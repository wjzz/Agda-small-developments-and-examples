{-
  @author: Wojciech Jedynak (wjedynak@gmail.com)

  TODO : 
    * extract the permutation code to my library
-}
module CPS where

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
open import Denote

----------------------------
--  Context permutations  --
----------------------------

infix 3 _≈_

data _≈_ : {n : ℕ} →  Ctx n → Ctx n → Set where
  nil : ∅ ≈ ∅
  swp : ∀ {a b n}{Γ : Ctx n} → a ∷ b ∷ Γ ≈ b ∷ a ∷ Γ
  cns : ∀ {a n}  {Γ Γ' : Ctx n} 
      → Γ ≈ Γ' 
      → a ∷ Γ ≈ a ∷ Γ'
  trn : ∀ {n}{Γ1 Γ2 Γ3 : Ctx n} 
      → Γ1 ≈ Γ2 
      → Γ2 ≈ Γ3
      → Γ1 ≈ Γ3

perm-reflexive : ∀ {n} (Γ : Ctx n) → Γ ≈ Γ
perm-reflexive []       = nil
perm-reflexive (x ∷ xs) = cns (perm-reflexive xs)

perm-symmetric : ∀ {n}{Γ Γ' : Ctx n} → Γ ≈ Γ' → Γ' ≈ Γ
perm-symmetric nil        = nil
perm-symmetric swp        = swp
perm-symmetric (cns x)    = cns (perm-symmetric x)
perm-symmetric (trn x x₁) = trn (perm-symmetric x₁) (perm-symmetric x)

perm-lookup : ∀ {n}
            → {Γ Γ' : Ctx n}
            → {x : Type}
            → (i : Fin n)
            → Γ ≈ Γ'
            → Γ ! i ≡ x
            → Σ[ j ∶ Fin n ](Γ' ! j ≡ x)

perm-lookup () nil eq
perm-lookup zero          swp eq = suc zero , eq
perm-lookup (suc zero)    swp eq = zero , eq
perm-lookup (suc (suc i)) swp eq = suc (suc i) , eq
perm-lookup zero (cns perm) eq = zero , eq
perm-lookup (suc i) (cns perm) eq with perm-lookup i perm eq
... | j , rec = suc j , rec
perm-lookup i (trn perm1 perm2) eq with perm-lookup i perm1 eq
... | j , rec = perm-lookup j perm2 rec

----------------------------------
--  Variable lifting in a term  --
----------------------------------

permutation : ∀ {n t} {Γ Γ' : Ctx n}
            → Γ ≈ Γ'
            → Term Γ  t 
            → Term Γ' t
permutation perm (var i ind) with perm-lookup i perm ind
... | j , eq = var j eq
permutation perm (app t₁ t₂ t₃)  = app t₁ (permutation perm t₂) (permutation perm t₃)
permutation perm (abs t)         = abs (permutation (cns perm) t)
permutation perm true            = true
permutation perm false           = true
permutation perm (cond t₁ t₂ t₃) = permutation perm t₃

tswap : ∀ {n t t1 t2} {Γ : Ctx n}
        → Term (t1 ∷ t2 ∷ Γ) t 
        → Term (t2 ∷ t1 ∷ Γ) t
tswap = permutation swp

-- ignoring the closest variable

tlift : ∀ {n t}{Γ : Ctx n}
      → {a : Type}
      → Term Γ       t 
      → Term (a ∷ Γ) t
      
tlift (var i ind)  = var (suc i) ind
tlift (app t₁ M N) = app t₁ (tlift M) (tlift N)
tlift (abs M)      = abs (tswap (tlift M))
tlift true         = true
tlift false        = false
tlift (cond C M N) = cond (tlift C) (tlift M) (tlift N)

---------------------------
--  Operations on types  --
---------------------------

[_%_] : Type → Type → Type
[ B b     % o ] = B b
[ t1 ⇒ t2 % o ] = [ t1 % o ] ⇒ ([ t2 % o ] ⇒ o) ⇒ o

[_%_]' : Type → Type → Type
[ t % o ]' = ([ t % o ] ⇒ o) ⇒ o

-- lifting for contexts

[_%_]c : {n : ℕ} → Ctx n → Type → Ctx n
[ []    % o ]c = ∅
[ t ∷ Γ % o ]c = [ t % o ] ∷ [ Γ % o ]c 

-------------------
-- lemmas

context-map : ∀ {n t o}{Γ : Ctx n}
            → (i : Fin n)
            → Γ ! i ≡ t
            → [ Γ % o ]c ! i ≡ [ t % o ]

context-map {Γ = []} () _
context-map {Γ = x ∷ Γ} zero  refl = refl
context-map {Γ = x ∷ Γ} (suc i) eq = context-map i eq

----------------------------
--  Typed CPS conversion  --
----------------------------

cps : ∀ {n t o}{Γ : Ctx n}
    → Term Γ t 
    → Term [ Γ % o ]c [ t % o ]'

cps {t = t}{o = o} 
  (var i ind) 
  = abs (app [ t % o ] (var (# 0) refl) (var (suc i) (context-map i ind)))

cps {t = t1 ⇒ t2} {o = o} {Γ = Γ}
  (abs M)      -- λ k . k (λ x . cps M)
  = abs (app [ t1 ⇒ t2 % o ] (var (# 0) refl) (abs (tswap (tlift M')))) 
  where
     M' : Term [ t1 ∷ Γ % o ]c [ t2 % o ]'
     M' = cps M

-- λ k. [M] (λ m. [N] (λ n. m n k))
cps {t = t} {o = o} 
  (app t₁ M N)
  = abs {- k -} (app _ (tlift (cps M)) 
                (abs {- m -} (app _ (tlift (tlift (cps N))) 
                             (abs {- n -} (app _ (app _ m n) k))))) 
  where
    m = var (# 1) refl
    n = var (# 0) refl
    k = var (# 2) refl

cps {o = o} true = abs (app Boolean k true) where
  k = var (# 0) refl

cps {o = o} false = abs (app Boolean k false) where
  k = var (# 0) refl

-- λ k. [C] (λ c → if c then [M] k else [N] k)
cps (cond C M N)    
  = abs (app _ (tlift (cps C) ) 
        (abs {- b -} (cond b 
                           (app _ (tlift (tlift (cps M))) k)
                           (app _ (tlift (tlift (cps N))) k))))
  where
    b = var (# 0) refl
    k = var (# 1) refl

-- ---------------------------------------------------------
-- -- K has to know how many binder levels it has went under
-- ----------------------------------------------------------

-- cps x = λ k → k x
-- cps (abs M) = λ k → k (abs (abs (cps M (abs (k (var (# 0) refl))))))
-- cps (app t0 M N) = λ k → cps M (λ m → ⟦ N ⟧ (λ n → (app (app m n) (abs (k (var (# 0) refl))))))

-- {-
-- ⟦ x ⟧ = λ k. k x

-- ⟦ λ x. M ⟧ = λ k. k (λ x. λ k'. ⟦ M ⟧ (λ a. k' a))

-- ⟦ M N ⟧ = λ k. ⟦ M ⟧ (λ m . ⟦ N ⟧ (λ n . m n (λ a . k a)))
-- -}

