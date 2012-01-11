{-
  @author: Wojciech Jedynak (wjedynak@gmail.com)
-}
module Even where

open import Data.Nat
open import Data.Maybe
-- open import Data.Bool


-- open import Data.List
-- open import Data.List.Theorems

-- open import Data.Nat
-- open import Data.Nat.Theorems

-- open import Data.Sum
-- open import Data.Product

-- open import Data.Empty
-- open import Data.Unit

-- open import Data.Fin
-- open import Data.Vec
-- --open import Data.Vec.Theorems

open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

data Even : ℕ → Set where
  ev-zero : Even zero
  ev-suc  : ∀ {n} → Even n → Even (suc (suc n))

-- examples

even-thirty : Even 30
even-thirty = ev-suc (ev-suc (ev-suc (ev-suc (ev-suc (ev-suc (ev-suc (ev-suc (ev-suc (ev-suc (ev-suc (ev-suc (ev-suc (ev-suc (ev-suc ev-zero))))))))))))))

-- even is decidable

even : (n : ℕ) → Maybe (Even n)
even 0 = just ev-zero
even 1 = nothing
even (suc (suc n)) with even n
... | just p  = just (ev-suc p)
... | nothing = nothing

even-type : (n : ℕ) → Set
even-type n with even n
... | just p  = Even n
... | nothing = ℕ                                 -- could be anything non-empty, ie ⊤

check-even : (n : ℕ) → even-type n
check-even n with even n
... | just p  = p
... | nothing = 0

