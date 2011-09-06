-- @author : Wojciech Jedynak (wjedynak@gmail.com)
-- @date   : 2011-09-01
-- @tags   : Propositional logic ; agda ; bool
-- @short  : Some additional operators on bools

module BoolUtils where

open import Data.Bool public using (Bool; true; false; not; _∧_; _∨_)

open import Relation.Binary hiding (_⇒_)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

-- auxilary boolean functions

_⇒_ : Bool → Bool → Bool
false ⇒ _ = true
true  ⇒ b = b

_⇔_ : Bool → Bool → Bool
true  ⇔ b = b
false ⇔ b = not b

-- properties needed to prove the correctness of the NNF translation

deMorganAndToOr : ∀ (b1 b2 : Bool) → not (b1 ∧ b2) ≡ not b1 ∨ not b2
deMorganAndToOr true b2 = refl
deMorganAndToOr false b2 = refl

deMorganOrToAnd : ∀ (b1 b2 : Bool) → not (b1 ∨ b2) ≡ not b1 ∧ not b2
deMorganOrToAnd true b2 = refl
deMorganOrToAnd false b2 = refl

equalsEquiv : ∀ {b1 b2 : Bool} → b1 ≡ b2 → b1 ⇔ b2 ≡ true
equalsEquiv {true} refl = refl
equalsEquiv {false} {true} eq = eq
equalsEquiv {false} {false} eq = refl

nnpp : ∀ (b : Bool) → not (not b) ≡ b
nnpp true = refl
nnpp false = refl

-- expressing ⇒ and ⇔ by means of {∧, ∨, not}

impl-pos : ∀ (b1 b2 : Bool) → b1 ⇒ b2 ≡ not b1 ∨ b2
impl-pos true b2 = refl
impl-pos false b2 = refl

impl-neg : ∀ (b1 b2 : Bool) → not (b1 ⇒ b2) ≡ b1 ∧ not b2
impl-neg true b2 = refl
impl-neg false b2 = refl

iff-pos : ∀ (b1 b2 : Bool) → b1 ⇔ b2 ≡ (not b1 ∨ b2) ∧ (not b2 ∨ b1)
iff-pos true true = refl
iff-pos true false = refl
iff-pos false true = refl
iff-pos false false = refl

iff-neg : ∀ (b1 b2 : Bool) → not (b1 ⇔ b2) ≡ (not b1 ∧ b2) ∨ (not b2 ∧ b1)
iff-neg true true = refl
iff-neg true false = refl
iff-neg false true = refl
iff-neg false false = refl
