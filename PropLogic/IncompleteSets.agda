-- @author : Wojciech Jedynak (wjedynak@gmail.com)
-- @date   : 2011-09-01
-- @tags   : Propositional logic ; agda ; incomplete sets 
-- @short  : Ex example of an incomplete set of logical operators.

module IncompleteSets where

open import PropLogic

-- formulas built only with tt, and, or, impl and if

data posFunctors {n : ℕ} : F n → Set where
  tt  : posFunctors tt
  var : (i : Fin n) → posFunctors (var i)
  and : {p q : F n} → posFunctors p → posFunctors q → posFunctors (and p q)
  or  : {p q : F n} → posFunctors p → posFunctors q → posFunctors (or  p q)
  imp : {p q : F n} → posFunctors p → posFunctors q → posFunctors (imp p q)
  iff : {p q : F n} → posFunctors p → posFunctors q → posFunctors (iff p q)

allTrue : {n : ℕ} → Val n
allTrue = replicate true

allTrueIsTrue : ∀ {n : ℕ}(i : Fin n) → (allTrue ! i ≡ true)
allTrueIsTrue {n = zero} ()
allTrueIsTrue {n = suc n} zero    = refl
allTrueIsTrue {n = suc n} (suc i) = allTrueIsTrue {n} i

-- under an evaluation function than maps all variable to true 
-- every formula built using only positive functors is true

evalTrue : ∀ {n : ℕ}{f : F n}(pos : posFunctors f) → ⟦ f ⟧ allTrue ≡ true
evalTrue tt      = refl
evalTrue (var i) = allTrueIsTrue i
evalTrue (and p q) rewrite evalTrue p | evalTrue q = refl
evalTrue (or  p q) rewrite evalTrue p | evalTrue q = refl
evalTrue (imp p q) rewrite evalTrue p | evalTrue q = refl
evalTrue (iff p q) rewrite evalTrue p | evalTrue q = refl

-- conclusion: we can't define negation, because it is not
-- true under the said eval. funct.
-- we omit this in the development.
