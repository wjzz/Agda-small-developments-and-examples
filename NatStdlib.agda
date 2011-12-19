-- @author : Wojciech Jedynak (wjedynak@gmail.com)
-- @date   : 2011-09-14
-- @tags   : agda ; nats ; stdlib
-- @short  : Simple tests of the Standard library for nats

module NatStdlib where

open import Algebra
open import Data.Nat
open import Data.Nat.Properties as Nat
open import Relation.Binary.PropositionalEquality

open ≡-Reasoning

private
  module CS = CommutativeSemiring Nat.commutativeSemiring

plus-comm : (m n : ℕ) → m + n ≡ n + m
plus-comm m n = CS.+-comm m n

