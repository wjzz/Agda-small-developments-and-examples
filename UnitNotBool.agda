{-
@author : Wojciech Jedynak (wjedynak@gmail.com)
@date   : 2011-08-28
@tags   : agda ; different types ; type inequality ; nat <> bool ; open question
@short  : We prove that various inductive types are different using a simple counting technique.
@note   : We prove two types different by stating a theorem that is only true for one of them,
          and then we show that if the types were equal we could coerce the proof for one type
          into a proof for the other, which then would give us a contradiction.
-}

module UnitNotBool where

open import Data.Empty
open import Data.Unit
open import Data.Bool
open import Data.Nat
open import Data.Fin

open import Data.Product

open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

-------------------------------------------
--  The empty type is not equal to unit  --
-------------------------------------------

emptyNotUnit : ⊥ ≢ ⊤
emptyNotUnit ⊥≡⊤ rewrite ⊥≡⊤ = tt

---------------------------------
--  Unit is not equal to Bool  --
---------------------------------

-- bool has more than one inhabitant
boolMoreThanOne : ∃₂ (λ (b1 b2 : Bool) → b1 ≢ b2)
boolMoreThanOne = true , false , λ ()

-- unit has less than two inhabitants
unitOnlyOne : ¬ (∃₂ (λ (b1 b2 : ⊤) → b1 ≢ b2))
unitOnlyOne (tt , tt , y) = y refl      -- y : tt ≢ tt

unitNotBool : ⊤ ≢ Bool
unitNotBool ⊤≡Bool with boolMoreThanOne
... | lemma rewrite sym ⊤≡Bool = unitOnlyOne lemma

--------------------------------
--  Nat is not equal to Bool  --
--------------------------------

-- nat has more that two inhabitants

natMoreThanTwo : ∃ (λ (n1 : ℕ) → ∃₂ (λ n2 n3 → 
  n1 ≢ n2 × n1 ≢ n3 × n2 ≢ n3))
natMoreThanTwo = 0 , 1 , 2 , (λ ()) , (λ ()) , λ ()

-- it is not the case for Bool (proof by brute force)

boolNoMoreThanTwo : ¬ (∃ (λ (n1 : Bool) → ∃₂ (λ n2 n3 → 
  n1 ≢ n2 × n1 ≢ n3 × n2 ≢ n3)))
boolNoMoreThanTwo (true , true , n3 , proj₁1 , proj₁2 , y)     = proj₁1 refl
boolNoMoreThanTwo (true , false , true , proj₁1 , proj₁2 , y)  = proj₁2 refl
boolNoMoreThanTwo (true , false , false , proj₁1 , proj₁2 , y) = y refl
boolNoMoreThanTwo (false , true , true , proj₁1 , proj₁2 , y)  = y refl
boolNoMoreThanTwo (false , true , false , proj₁1 , proj₁2 , y) = proj₁2 refl
boolNoMoreThanTwo (false , false , n3 , proj₁1 , proj₁2 , y)   = proj₁1 refl

natNotBool : ℕ ≢ Bool
natNotBool ℕ≡Bool with natMoreThanTwo
... | lemma rewrite ℕ≡Bool = boolNoMoreThanTwo lemma

---------------------------------------------
--  Open question: can we proof this one?  --
---------------------------------------------

finsDifferent : ∀ (n m : ℕ) → n ≢ m → Fin n ≢ Fin m
finsDifferent n m n≢m Fin-n≢Fin-m = {!!}

-- it's easy to write a procedure (in LTac for Coq, in Lisp (:P) for Agda)
-- for given n and m, but I don't see a way to show it once and for all.
-- We would have to define some theory of finite ordinals perhaps?