{-
  @author: Wojciech Jedynak (wjedynak@gmail.com)
-}
module LinearLogic where

open import Data.Bool
open import Data.Empty
open import Data.Nat renaming (_≟_ to _≟ℕ_)
open import Data.Nat.Theorems
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Binary hiding (_⇒_)
open import Relation.Nullary

-- formulas

Var : Set
Var = ℕ

data Formula : Set where
  #_  : (X : Var) → Formula 
  _⨂_ : (P Q : Formula) → Formula
  _&_ : (P Q : Formula) → Formula
  _⨁_ : (P Q : Formula) → Formula
  _⊸_ : (P Q : Formula) → Formula

-- equality on formulas

_==_ : Formula → Formula → Bool
(# X) == (# X') with X ≟ℕ X'
... | yes p = true
... | no ¬p = false
(P ⨂ Q) == (P' ⨂ Q')  = P == P' ∧ Q == Q'
(P & Q) == (P' & Q')  = P == P' ∧ Q == Q'
(P ⨁ Q) == (P' ⨁ Q')  = P == P' ∧ Q == Q'
(P ⊸ Q) == (P' ⊸ Q') = P == P' ∧ Q == Q'
(# X) == (P ⨂ Q) = false
(# X) == (P & Q) = false
(# X) == (P ⨁ Q) = false
(# X) == (P ⊸ Q) = false
(P ⨂ Q) == (# X) = false
(P ⨂ Q) == (P' & Q') = false
(P ⨂ Q) == (P' ⨁ Q') = false
(P ⨂ Q) == (P' ⊸ Q') = false
(P & Q) == (# X) = false
(P & Q) == (P' ⨂ Q') = false
(P & Q) == (P' ⨁ Q') = false
(P & Q) == (P' ⊸ Q') = false
(P ⨁ Q) == (# X) = false
(P ⨁ Q) == (P' ⨂ Q') = false
(P ⨁ Q) == (P' & Q') = false
(P ⨁ Q) == (P' ⊸ Q') = false
(P ⊸ Q) == (# X) = false
(P ⊸ Q) == (P' ⨂ Q') = false
(P ⊸ Q) == (P' & Q') = false
(P ⊸ Q) == (P' ⨁ Q') = false

-----------------------------------
-- contexts

data so : Bool → Set where
  oh : so true

Ctx : Set
Ctx = Formula → ℕ

_∈_ : Formula → Ctx → Set
P ∈ Δ = Δ P ≢ zero

-- empty context

∙ : Ctx
∙ X = 0

-- singleton context

[_] : Formula → Ctx
[ F ] G = if F == G then 1 else 0

-- context concatenation

_#_ : Ctx → Ctx → Ctx
Δ # Δ' = λ F → Δ F + Δ' F

-- context extension

_,_ : Ctx → Formula → Ctx
Δ , G = Δ # [ G ]

-- context equality

_≈_ : Ctx → Ctx → Set
Δ ≈ Δ' = (F : Formula) → Δ F ≡ Δ' F

infixl 5 _,_
infix  4 _⊢_
infix  4 _⇒_

-----------------------------------
-- typing judgements

data _⊢_ : Ctx → Formula → Set where

  -- structural rules

  id : ∀ {F}
     → [ F ] ⊢ F

  cut : ∀ {Δ Δ' F C}
      → Δ  ⊢ F
      → Δ' , F ⊢ C
      → Δ # Δ' ⊢ C

  reorder : ∀ {Δ Δ' F}
          → Δ ≈ Δ'
          → Δ' ⊢ F
          → Δ  ⊢ F

  -- lolli

  lolli-l : ∀ {Δ Δ' A B C}
          → Δ ⊢ A
          → Δ' , B ⊢ C
          → Δ # (Δ' , A ⊸ B) ⊢ C

  lolli-r : ∀ {Δ A B}
          → Δ , A ⊢ B
          → Δ ⊢ A ⊸ B


data _⇒_ : Ctx → Formula → Set where

  -- structural rules

  id : ∀ {F}
     → [ F ] ⇒ F

  reorder : ∀ {Δ Δ' F}
          → Δ ≈ Δ'
          → Δ' ⇒ F
          → Δ  ⇒ F

  -- lolli

  lolli-l : ∀ {Δ Δ' A B C}
          → Δ ⇒ A
          → Δ' , B ⇒ C
          → Δ # (Δ' , A ⊸ B) ⇒ C

  lolli-r : ∀ {Δ A B}
          → Δ , A ⇒ B
          → Δ ⇒ A ⊸ B

-------------------------------
--  Cut elimination theorem  --
-------------------------------

cut-lemma : ∀ Δ Δ' A C
          → Δ ⇒ A
          → Δ' , A ⇒ C
          → Δ # Δ' ⇒ C
cut-lemma .(λ G → if A == G then 1 else 0) Δ' A C id derAC = {!!}
cut-lemma Δ Δ' A C (reorder y y') derAC = {!!}
cut-lemma .(λ F → Δ F + (Δ0 F + (if (A' ⊸ B) == F then 1 else 0))) Δ' A C (lolli-l {Δ} {Δ0} {A'} {B} y y') derAC = {!!}
cut-lemma Δ Δ' .(A ⊸ B) C (lolli-r {.Δ} {A} {B} y) derAC = {!!}

cut-elimination : ∀ Δ F 
                → Δ ⊢ F → Δ ⇒ F
cut-elimination .(λ G → if F == G then 1 else 0) F id = id
cut-elimination .(λ F' → Δ F' + Δ' F') F (cut {Δ} {Δ'} y y') = {!!}
cut-elimination Δ F (reorder y y') = reorder y (cut-elimination _ F y')
cut-elimination .(λ F' → Δ F' + (Δ' F' + (if (A ⊸ B) == F' then 1 else 0))) F (lolli-l {Δ} {Δ'} {A} {B} y y')
  = lolli-l {Δ} {Δ'} {A} {B} (cut-elimination Δ A y) (cut-elimination (λ z → Δ' z + (if B == z then suc zero else zero))
                                                        F y')
cut-elimination Δ .(A ⊸ B) (lolli-r {.Δ} {A} {B} y) = lolli-r
                                                        (cut-elimination (λ z → Δ z + (if A == z then suc zero else zero))
                                                         B y)