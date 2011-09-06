-- @author : Wojciech Jedynak (wjedynak@gmail.com)
-- @date   : 2011-09-01
-- @tags   : Propositional logic ; Negation Normal Form ; NNF ; agda
-- @short  : Translation of prop. formulas to Negation Normal Form with proof of equivalence

module NNF where

open import Data.Product
open import Relation.Binary.PropositionalEquality

open import PropLogic

-- negation normal form

data NNF (n : ℕ) : Set where
  ff  : NNF n
  tt  : NNF n
  pos : (v : Fin n)   → NNF n    -- positive literal
  neg : (v : Fin n)   → NNF n    -- negative literal
  and : (p q : NNF n) → NNF n
  or  : (p q : NNF n) → NNF n

-- semantics

⟦_⟧N : {n : ℕ} → NNF n → Val n → Bool
⟦ ff ⟧N      σ = false
⟦ tt ⟧N      σ = true
⟦ pos v   ⟧N σ = σ ! v
⟦ neg v   ⟧N σ = not (σ ! v)
⟦ and p q ⟧N σ = ⟦ p ⟧N σ ∧ ⟦ q ⟧N σ
⟦ or  p q ⟧N σ = ⟦ p ⟧N σ ∨ ⟦ q ⟧N σ

-- translation to NNF

_==_ : {n : ℕ} → NNF n → F n → Set
p == q = ∀ (σ : Val _) → ⟦ p ⟧N σ ≡ ⟦ q ⟧ σ

_<>_ : {n : ℕ} → NNF n → F n → Set
p <> q = ∀ (σ : Val _) → ⟦ p ⟧N σ ≡ not (⟦ q ⟧ σ)


mutual
  positive : {n : ℕ} → (f : F n) → NNF n
  positive ff = ff
  positive tt = tt
  positive (var v)   = pos v
  positive (neg f)   = negative f
  positive (and p q) = and (positive p) (positive q)
  positive (or  p q) = or  (positive p) (positive q)
  positive (imp p q) = or  (negative p) (positive q) -- p => q ~ ¬ p ∨ q
  positive (iff p q) = and (or (negative p) (positive q)) 
                           (or (negative q) (positive p))

  negative : {n : ℕ} → (f : F n) → NNF n
  negative ff = tt
  negative tt = ff
  negative (var v)   = neg v
  negative (neg f)   = positive f
  negative (and p q) = or (negative p) (negative q)
  negative (or  p q) = and (negative p) (negative q)
  negative (imp p q) = and (positive p) (negative q)
  negative (iff p q) = or (and (negative p) (positive q)) 
                          (and (negative q) (positive p))

-- correctness lemma

mutual
  pos-cor : {n : ℕ} → (f : F n) → positive f == f
  pos-cor ff σ = refl
  pos-cor tt σ = refl
  pos-cor (var v)   σ = refl
  pos-cor (neg f)   σ = neg-cor f σ
  pos-cor (and p q) σ 
    rewrite pos-cor p σ | pos-cor q σ 
      = refl
  pos-cor (or  p q) σ 
    rewrite pos-cor p σ | pos-cor q σ 
      = refl
  pos-cor (imp p q) σ 
    rewrite pos-cor q σ | neg-cor p σ
      = sym (impl-pos (⟦ p ⟧ σ) (⟦ q ⟧ σ))
  pos-cor (iff p q) σ 
    rewrite pos-cor p σ | pos-cor q σ | neg-cor p σ | neg-cor q σ
      = sym (iff-pos (⟦ p ⟧ σ) (⟦ q ⟧ σ))

  neg-cor : {n : ℕ} → (f : F n) → negative f <> f
  neg-cor ff σ = refl
  neg-cor tt σ = refl
  neg-cor (var v) σ 
    rewrite nnpp (σ ! v) 
      = refl
  neg-cor (neg f) σ 
    rewrite pos-cor f σ | nnpp (⟦ f ⟧ σ) 
      = refl
  neg-cor (and p q) σ 
    rewrite neg-cor p σ | neg-cor q σ 
      = sym (deMorganAndToOr (⟦ p ⟧ σ) (⟦ q ⟧ σ))
  neg-cor (or p q) σ 
    rewrite neg-cor p σ | neg-cor q σ 
      = sym (deMorganOrToAnd (⟦ p ⟧ σ) (⟦ q ⟧ σ))
  neg-cor (imp p q) σ 
    rewrite pos-cor p σ | neg-cor q σ 
      = sym (impl-neg (⟦ p ⟧ σ) (⟦ q ⟧ σ))
  neg-cor (iff p q) σ 
    rewrite pos-cor p σ | pos-cor q σ | neg-cor p σ | neg-cor q σ
      = sym (iff-neg (⟦ p ⟧ σ) (⟦ q ⟧ σ))

-- the main result

toNNF : {n : ℕ} → (f : F n) → Σ[ f' ∶ NNF n ](f' == f)
toNNF f = positive f , pos-cor f
