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
open import Data.String

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import Terms
open import Denote
open import CPS

----------------------------------
--  Equivalence of denotations  --
----------------------------------


lift-lemma0 : ∀ {n t} 
              → {Γ : Ctx n}
              → (Δ : HetVec (V.map ⟦_⟧t Γ))
              → (M : Term Γ t)
              → (t0 : Type)
              → (x : ⟦ t0 ⟧t)
              → let Δ' = x ∷ Δ in
              denote {Γ = t0 ∷ Γ} Δ' (tlift M) ≡ denote Δ M

lift-lemma0 = {!!}


lift-lemma : ∀ {n t} 
              → {Γ : Ctx n}
              → (Δ : HetVec (V.map ⟦_⟧t Γ))
              → (M N : Term Γ t)
              → denote Δ M ≡ denote Δ N
              → (t0 : Type)
              → (x : ⟦ t0 ⟧t)
              → let Δ' = x ∷ Δ in
              denote {Γ = t0 ∷ Γ} Δ' (tlift M) ≡ denote {Γ = t0 ∷ Γ} (x ∷ Δ) (tlift N)

lift-lemma Δ (var i ind) N eq t0 x = {!!}
lift-lemma Δ (app t₁ M M₁) N eq t0 x = {!!}
lift-lemma Δ (abs M) N eq t0 x = {!!}
lift-lemma Δ true (var i ind) eq t0 x = {!!}
lift-lemma Δ true (app t₁ N N₁) eq t0 x = {!!}
lift-lemma Δ true true eq t0 x = refl
lift-lemma Δ true false eq t0 x = eq
lift-lemma Δ true (cond N N₁ N₂) eq t0 x = {!!}
lift-lemma Δ false N eq t0 x = {!!}
lift-lemma Δ (cond M M₁ M₂) N eq t0 x = {!!}


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

