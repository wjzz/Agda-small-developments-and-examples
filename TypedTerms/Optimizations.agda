{-
  @author: Wojciech Jedynak (wjedynak@gmail.com)
-}
module Optimizations where

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
open import Denote

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
