-- @author : Wojciech Jedynak (wjedynak@gmail.com)
-- @date   : 2011-09-01
-- @tags   : Propositional logic ; agda ; semantics
-- @short  : Basic notions for propositional logic
-- @note   : Semantics of classical propositional logic

module PropLogic where

open import Data.Fin  public using (Fin; zero; suc; #_)
open import Data.Nat  public using (ℕ;   zero; suc)
open import Data.Vec  public

open import Relation.Binary hiding (_⇒_)
open import Relation.Binary.PropositionalEquality public using (_≡_; refl; sym)
open import Relation.Nullary

open import BoolUtils public

-- propositional formulas --

data F (n : ℕ) : Set where
  ff  : F n
  tt  : F n
  var : (v : Fin n) → F n
  neg : (f   : F n) → F n
  and : (p q : F n) → F n
  or  : (p q : F n) → F n
  imp : (p q : F n) → F n
  iff : (p q : F n) → F n

-- valuation function --

_!_ : {A : Set}{n : ℕ} → Vec A n → Fin n → A
v ! i = lookup i v

Val : ℕ → Set
Val n = Vec Bool n

-- denotation of a formula

⟦_⟧ : {n : ℕ} → F n → Val n → Bool
⟦ ff ⟧      σ = false
⟦ tt ⟧      σ = true
⟦ var v ⟧   σ = σ ! v
⟦ neg f ⟧   σ = not (⟦ f ⟧ σ)
⟦ and p q ⟧ σ = ⟦ p ⟧ σ ∧ ⟦ q ⟧ σ
⟦ or  p q ⟧ σ = ⟦ p ⟧ σ ∨ ⟦ q ⟧ σ
⟦ imp p q ⟧ σ = ⟦ p ⟧ σ ⇒ ⟦ q ⟧ σ
⟦ iff p q ⟧ σ = ⟦ p ⟧ σ ⇔ ⟦ q ⟧ σ

-- satisfies

satisfies : {n : ℕ} → F n → Val n → Set
satisfies f σ = ⟦ f ⟧ σ ≡ true

-- tautologies --

tautology : {n : ℕ} → F n → Set
tautology {n} f = ∀ (σ : Val n) → satisfies f σ

example : tautology {n = 1} (or (var (# 0)) (neg (var (# 0))))
example σ with σ ! (# 0)
... | true  = refl
... | false = refl

-- equivalence

_≈_ : {n : ℕ} → F n → F n → Set
p ≈ q = tautology (iff p q) 

-- some useful lemmas --

deMorgan : ∀ {n : ℕ} → (p q : F n) → (neg (and p q)) ≈ or (neg p) (neg q)
deMorgan p q σ = equalsEquiv (deMorganAndToOr (⟦ p ⟧ σ) (⟦ q ⟧ σ))

