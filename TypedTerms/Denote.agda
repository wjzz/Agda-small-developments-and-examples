{-
  @author: Wojciech Jedynak (wjedynak@gmail.com)
-}
module Denote where

open import Data.Nat
open import Data.Fin
open import Data.Fin.Props
open import Data.Bool
open import Data.Unit using (⊤; tt)
open import Data.Product
open import Data.Empty
open import Function

open import Data.Vec

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

private
  module V = Data.Vec

open import Terms

------------------
--  Denotation  --
------------------

⟦_⟧b : Base → Set
⟦ TBool ⟧b = Bool
⟦ TNat  ⟧b = ℕ

⟦_⟧t : Type → Set
⟦   B b   ⟧t = ⟦ b ⟧b
⟦ t₁ ⇒ t₂ ⟧t = ⟦ t₁ ⟧t → ⟦ t₂ ⟧t 

⟦_⟧c : {n : ℕ} → Ctx n → (Set → Set)
⟦_⟧c []      ret = ret
⟦_⟧c (t ∷ Γ) ret = ⟦ t ⟧t → ⟦ Γ ⟧c ret

⟦_⟧v : {n : ℕ} → Vec Set n → Set
⟦   []   ⟧v = ⊤
⟦ x ∷ xs ⟧v = x × ⟦ xs ⟧v

-- heterogenous vectors

data HetVec : {n : ℕ} → Vec Set n → Set₁ where
  []  : HetVec []
  _∷_ : ∀ {n t} {v : Vec Set n} 
      → (x : t) 
      → (h : HetVec v) 
      → HetVec (t ∷ v)

_!!_ : {n : ℕ} {v : Vec Set n} → HetVec v → (i : Fin n) → v ! i
[]      !! ()
(x ∷ h) !! zero = x
(x ∷ h) !! suc i = h !! i

-- a small lemma

map-lookup-commute2 : ∀ {n : ℕ} {l l'} {A : Set l}{B : Set l'} {x : A}
                    → (f : A → B)
                    → (v : Vec A n)
                    → (i : Fin n)
                    → (v ! i) ≡ x
                    → f x ≡ (V.map f v) ! i

map-lookup-commute2 f [] () _
map-lookup-commute2 f (x ∷ v) zero    refl = refl
map-lookup-commute2 f (x ∷ v) (suc i) prf  = map-lookup-commute2 f v i prf


{- Compilation into Agda terms. Equivalently: environment based term evaluation -}

denote : {n : ℕ} 
       → {t : Type}
       → {Γ : Ctx n}
       → (Δ : HetVec (V.map ⟦_⟧t Γ))
       → (M : Term Γ t)
       → ⟦ t ⟧t

denote {Γ = Γ} Δ (var i prf) rewrite map-lookup-commute2 ⟦_⟧t Γ i prf
  =  Δ !! i 
denote Δ (app t₁ M N) 
  = (denote Δ M) (denote Δ N) 
denote Δ (abs M) 
  = λ T1 → denote (T1 ∷ Δ) M
denote Δ true 
  = true
denote Δ false
  = false
denote Δ (cond C M N)
  = if (denote Δ C) then (denote Δ M) else (denote Δ N)


⟦_⟧ : ∀ {t} → Term ∅ t → ⟦ t ⟧t
⟦ t ⟧ = denote [] t



-------------------------------------
--  Some trivial program analysis  --
-------------------------------------

if-simpl : ∀ {t} (C : Term ∅ Boolean) (M : Term ∅ t) 
         → ⟦ cond C M M ⟧ ≡ ⟦ M ⟧

if-simpl C M with ⟦ C ⟧
... | true  = refl
... | false = refl

if-simpl2 : ∀ {t} (M N : Term ∅ t) 
         → ⟦ cond true M N ⟧ ≡ ⟦ M ⟧

if-simpl2 M N = refl 


---------------------
--  Optimizations  --
---------------------

optimize : ∀ {n t} {Γ : Ctx n} 
         → Term Γ t → Term Γ t

optimize (var i r)    = var i r
optimize (app t₁ M N) = app t₁ (optimize M) (optimize N)
optimize (abs M)      = abs (optimize M)
optimize true  = true
optimize false = false
optimize (cond C M N) with (optimize C) ≟t true
... | yes _ = optimize M
... | no _ with (optimize C) ≟t false
... | yes _ = optimize N
... | no _ with (optimize M) ≟t (optimize N)
... | yes _ = optimize M
... | no _ = cond (optimize C) (optimize M) (optimize N)

example : Term ∅ (Boolean ⇒ Boolean)
example = abs (cond (var (# 0) refl) true true)


postulate
  funcExt : {A B : Set} → {f g : A → B} → ((x : A) → f x ≡ g x) → f ≡ g

-- correctness of optimization

optimize-correct : ∀ {n t}{Γ : Ctx n}
                 → (t : Term Γ t)
                 → (Δ : HetVec (V.map ⟦_⟧t Γ))
                 → denote Δ t ≡ denote Δ (optimize t)

optimize-correct (var i ind) Δ = refl
optimize-correct (app t₁ t₂ t₃) Δ = cong₂ _$_ (optimize-correct t₂ Δ)(optimize-correct t₃ Δ)
optimize-correct (abs t) Δ = funcExt (λ x → optimize-correct t (x ∷ Δ))
optimize-correct true  Δ = refl
optimize-correct false Δ = refl
optimize-correct (cond t₁ t₂ t₃) Δ with optimize t₁ ≟t true
optimize-correct (cond t₁ t₂ t₃) Δ | yes p rewrite optimize-correct t₁ Δ | p = optimize-correct t₂ Δ
optimize-correct (cond t₁ t₂ t₃) Δ | no ¬p with optimize t₁ ≟t false
optimize-correct (cond t₁ t₂ t₃) Δ | no ¬p | yes q rewrite optimize-correct t₁ Δ | q = optimize-correct t₃ Δ
optimize-correct (cond t₁ t₂ t₃) Δ | no ¬p | no ¬q with optimize t₂ ≟t optimize t₃
optimize-correct (cond t₁ t₂ t₃) Δ | no ¬p | no ¬q | yes r with denote Δ t₁
optimize-correct (cond t₁ t₂ t₃) Δ | no ¬p | no ¬q | yes r | true  = optimize-correct t₂ Δ
optimize-correct (cond t₁ t₂ t₃) Δ | no ¬p | no ¬q | yes r | false rewrite r = optimize-correct t₃ Δ
optimize-correct (cond t₁ t₂ t₃) Δ | no ¬p | no ¬q | no ¬r 
  rewrite optimize-correct t₁ Δ | optimize-correct t₂ Δ | optimize-correct t₃ Δ  = refl
 
