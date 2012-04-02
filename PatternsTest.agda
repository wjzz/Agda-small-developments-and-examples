{-
  @author: Wojciech Jedynak (wjedynak@gmail.com)
-}
module PatternsTest where

open import Data.Nat
open import Relation.Binary
open import Relation.Nullary


foo : ℕ → ℕ → ℕ
foo 0 n = 2
foo m 0 = 1
foo (suc m) (suc n) with n ≟ m | foo m 123 | foo (suc m) n
... | yes p | a | b = a
... | no ¬p | a | b = b

