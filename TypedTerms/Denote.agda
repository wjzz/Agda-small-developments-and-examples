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
open import Data.HetVec

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import Terms

--------------
--  Lemmas  --
--------------

-- functional extentionality

postulate
  funcExt : {A B : Set} → {f g : A → B} → ((x : A) → f x ≡ g x) → f ≡ g



map-lookup-commute2 : ∀ {n : ℕ} {l l'} {A : Set l}{B : Set l'} {x : A}
                    → (f : A → B)
                    → (v : Vec A n)
                    → (i : Fin n)
                    → (v ! i) ≡ x
                    → f x ≡ (V.map f v) ! i

map-lookup-commute2 f [] () _
map-lookup-commute2 f (x ∷ v) zero    refl = refl
map-lookup-commute2 f (x ∷ v) (suc i) prf  = map-lookup-commute2 f v i prf


------------------
--  Denotation  --
------------------

⟦_⟧b : Base → Set
⟦ TBool ⟧b = Bool
⟦ TNat  ⟧b = ℕ

⟦_⟧t : Type → Set
⟦   B b   ⟧t = ⟦ b ⟧b
⟦ t₁ ⇒ t₂ ⟧t = ⟦ t₁ ⟧t → ⟦ t₂ ⟧t 

⟦_⟧c : {n : ℕ} → Ctx n → Vec Set n
⟦_⟧c = V.map ⟦_⟧t

{-
⟦_⟧c : {n : ℕ} → Ctx n → (Set → Set)
⟦_⟧c []      ret = ret
⟦_⟧c (t ∷ Γ) ret = ⟦ t ⟧t → ⟦ Γ ⟧c ret

⟦_⟧v : {n : ℕ} → Vec Set n → Set
⟦   []   ⟧v = ⊤
⟦ x ∷ xs ⟧v = x × ⟦ xs ⟧v
-}

--------------------------------------
--  Term denotations as Agda terms  --
--------------------------------------

-- Compilation into Agda terms. Equivalently: environment based term evaluation

denote : {n : ℕ} 
       → {t : Type}
       → {Γ : Ctx n}
       → (Δ : HetVec ⟦ Γ ⟧c)
       → (M : Term Γ t)
       → ⟦ t ⟧t

-- we have inlined _!!_ from the commented out version to get rid of the rewrite

-- denote {Γ = []} _ (var () _)
-- denote {t = t} {Γ = .t ∷ Γ} (x₁ ∷ Δ) (var zero refl) = x₁
-- denote {t = t} {Γ = x ∷ Γ} (x₁ ∷ Δ) (var (suc i) prf) = denote Δ (var i prf) 

-- denote {Γ = Γ} Δ (var i prf) rewrite map-lookup-commute2 ⟦_⟧t Γ i prf
--   =  Δ !! i 

-- denote Δ (var i prf) rewrite sym prf 
--   = hlookup _ ⟦_⟧t Δ i

denote Δ (var i refl)
  = hlookup _ ⟦_⟧t Δ i

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


-- Denotations of closed terms

⟦_⟧ : ∀ {t} → Term ∅ t → ⟦ t ⟧t
⟦ t ⟧ = denote [] t
