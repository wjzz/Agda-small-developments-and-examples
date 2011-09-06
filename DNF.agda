-- @author : Wojciech Jedynak (wjedynak@gmail.com)
-- @date   : 2011-09-01
-- @tags   : Propositional logic ; DNF
-- @short  : A simple translation to DNF.

module DNF where

open import Data.Nat

-- ordinary formulas

data Formula : Set where
  #_    : ℕ → Formula
  True  : Formula
  False : Formula
  And   : Formula → Formula → Formula
  Or    : Formula → Formula → Formula

-- formulas in DNF

data Conj : Set where
  True : Conj
  _∧_  : (v : ℕ) → (c : Conj) → Conj

data Dysj : Set where
  False : Dysj
  _∨_   : (c : Conj) → (d : Dysj) → Dysj

-- appending operations

combineConj : Conj → Conj → Conj
combineConj True    c2 = c2
combineConj (v ∧ c) c2 = v ∧ combineConj c c2

combineDysj : Dysj → Dysj → Dysj
combineDysj False   d2 = d2
combineDysj (c ∨ d) d2 = c ∨ combineDysj d d2

-- conjuction of formulas in DNF

and2 : Conj → Dysj → Dysj
and2 c False    = False
and2 c (c' ∨ d) = combineConj c c' ∨ and2 c d

and : Dysj → Dysj → Dysj
and False   d2 = False
and (c ∨ d) d2 = combineDysj (and2 c d2) (and d d2)

-- conversion to DNF

toDNF : Formula → Dysj
toDNF (# v)     = (v ∧ True) ∨ False
toDNF True      = True ∨ False
toDNF False     = False
toDNF (And p q) = and (toDNF p) (toDNF q)
toDNF (Or  p q) = combineDysj (toDNF p) (toDNF q)

