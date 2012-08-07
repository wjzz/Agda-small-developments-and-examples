{-
  @author: Wojciech Jedynak (wjedynak@gmail.com)
-}
module CPS_Theory where

open import Data.Nat
open import Data.Fin
open import Data.Fin.Props
open import Data.Bool
open import Data.Unit using (⊤; tt)
open import Data.Product
open import Data.Empty
open import Function

open import Data.Vec
open import Data.Vec.Utils hiding (_!_)
open import Data.HetVec

open import Data.String hiding (_==_)

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import Terms
open import Denote
open import CPS

----------------------------------
--  Equivalence of denotations  --
----------------------------------

{- LEMMA:
denote (x₁ ∷ (x ∷ Δ)) (permutation swp (tlift M)) ≡
      denote (x₁ ∷ Δ) M
Have: denote (x ∷ (x₁ ∷ Δ)) (tlift M) ≡ denote (x₁ ∷ Δ) M
-}


{-

TODO: 
  this perm-read may not be accurate enough!

  a list of types is not enough

  (Nat, Nat) ≈ (Nat, Nat)  , but

  (1 , 2) ≈ (2, 1).

  This may be the reason our proof doesn't go well in the variable case!
-}

arg-stack-permutation : ∀ {n t}
                      → {Γ Γ' : Ctx n}
                      → (Δ  : HetVec ⟦ Γ  ⟧c)
                      → (Γ-perm : Γ ≈ Γ')
                      → (M : Term Γ t)
                      → let Δ' = proj₁ (perm-read ⟦_⟧t Γ-perm Δ) in
                      denote Δ M ≡ denote Δ' (permutation Γ-perm M)

arg-stack-permutation Δ Γ-perm (var i refl) with (perm-read ⟦_⟧t Γ-perm Δ) | perm-lookup i Γ-perm refl
... | Δ' , Δ-prf | j , j-prf = {!!}

arg-stack-permutation Δ Γ-perm (app t₁ M M₁) 
  = cong₂ (_$_) (arg-stack-permutation Δ Γ-perm M) 
                (arg-stack-permutation Δ Γ-perm M₁) 

arg-stack-permutation Δ Γ-perm (abs M) = funcExt (λ x → arg-stack-permutation (x ∷ Δ) (cns Γ-perm) M)

arg-stack-permutation Δ Γ-perm true = refl

arg-stack-permutation Δ Γ-perm false = refl

arg-stack-permutation Δ Γ-perm (cond M M₁ M₂) 
  = cong₃ if_then_else_ (arg-stack-permutation Δ Γ-perm M) 
                        (arg-stack-permutation Δ Γ-perm M₁) 
                        (arg-stack-permutation Δ Γ-perm M₂)

{- TODO: this needs to be generalized to permutations on heterogenous vectors -}

swap-lemma : ∀ {n t tx ty}
           → {Γ : Ctx n}
           → (x : ⟦ tx ⟧t)
           → (y : ⟦ ty ⟧t)
           → (Δ : HetVec (V.map ⟦_⟧t Γ))
           → (M : Term (tx ∷ ty ∷ Γ) t)
           → denote (y ∷ (x ∷ Δ)) (permutation swp M) ≡ denote (x ∷ y ∷ Δ) M

swap-lemma x y Δ M = {!!}

{-
lift-lemma0 : ∀ {n t} 
              → {Γ : Ctx n}
              → (Δ : HetVec (V.map ⟦_⟧t Γ))
              → (M : Term Γ t)
              → (t0 : Type)
              → (x : ⟦ t0 ⟧t)
              → let Δ' = x ∷ Δ in
              denote {Γ = t0 ∷ Γ} Δ' (tlift M) ≡ denote Δ M

lift-lemma0 {Γ = Γ} Δ (var i ind) t0 x = ? --rewrite map-lookup-commute2 ⟦_⟧t Γ i ind = refl
lift-lemma0 Δ (app t₁ M N) t0 x = cong₂ (_$_) (lift-lemma0 Δ M t0 x) (lift-lemma0 Δ N t0 x) 
lift-lemma0 Δ (abs M) t0 x = funcExt (λ x₁ → {!lift-lemma0 (x₁ ∷ Δ) M t0 x!})
lift-lemma0 Δ true t0 x = refl
lift-lemma0 Δ false t0 x = refl
lift-lemma0 Δ (cond C M N) t0 x 
  rewrite lift-lemma0 Δ C t0 x | lift-lemma0 Δ M t0 x | lift-lemma0 Δ N t0 x = refl
-}

lift-lemma : ∀ {n t} 
              → {Γ : Ctx n}
              → (Δ : HetVec (V.map ⟦_⟧t Γ))
              → (M N : Term Γ t)
              → denote Δ M ≡ denote Δ N
              → (t0 : Type)
              → (x : ⟦ t0 ⟧t)
              → let Δ' = x ∷ Δ in
              denote {Γ = t0 ∷ Γ} Δ' (tlift M) ≡ denote {Γ = t0 ∷ Γ} (x ∷ Δ) (tlift N)

lift-lemma Δ M N eq t0 x = {!!}

cps-equiv-gen : ∀ {n t o} 
              → {Γ : Ctx n}
              → let Γ' = [ Γ % o ]c in
              (Δ : HetVec (V.map ⟦_⟧t Γ'))
              → (M : Term Γ t)
              → denote Δ (cps M) ≡ denote Δ (opt-cps M)
cps-equiv-gen Δ (var i ind) = refl
cps-equiv-gen Δ (app t₁ M M₁) = {!!}
cps-equiv-gen Δ (abs M) = {!!}
cps-equiv-gen Δ true = refl
cps-equiv-gen Δ false = refl
cps-equiv-gen Δ (cond M M₁ M₂) = funcExt (λ T1 → {!!})

-- cps-equiv : ∀ {n t}{Γ : Ctx n}
--           → (M : Term ∅ t)
--           → ⟦ cps M ⟧ ≡ ⟦ opt-cps M ⟧

-- cps-equiv M = ?


cps-equiv : ∀ {t o}
          → (M : Term ∅ t)
          → ⟦ cps {o = o} M ⟧ ≡ ⟦ opt-cps M ⟧

cps-equiv (var i ind) = refl
cps-equiv (app t₁ M M₁) = {!!}
cps-equiv (abs M) = funcExt (λ x → cong (_$_ x) (funcExt (λ x₁ → funcExt (λ x₂ → {!!})))) -- generalization needed here
cps-equiv true = refl
cps-equiv false = refl
cps-equiv (cond M M₁ M₂) = funcExt (λ x → {!!}) --cong₂ (λ a → denote (x ∷ []) (tlift a)) {!!} {!!})

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

