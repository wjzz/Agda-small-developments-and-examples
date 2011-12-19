{-
  @author: Wojciech Jedynak (wjedynak@gmail.com)
-}
module JMeq where

open import Data.Nat
open import Relation.Binary.PropositionalEquality


-- based on Hardware modeling paper

data _==_ : {A B : Set} →  A → B → Set₁ where
  refl : {A : Set} → (a : A) → a == a

symm : {A B : Set} → {a : A} → {b : B} → a == b → b == a
symm {.B} {B} {.b} {b} (refl .b) = refl b

suc-cong : {n m : ℕ} → n == m → suc n == suc m
suc-cong {.m} {m} (refl .m) = refl (suc m)

==-to-≡ : {A : Set} → {a b : A} → a == b → a ≡ b
==-to-≡ {A} {.b} {b} (refl .b) = refl

repl : {A : Set} → {a b : A} → a == b → (P : A → Set) → P a → P b
repl {A} {.b} {b} (refl .b) P Pa = Pa

-- safe bits ;-)

data Bit : ℕ → Set where
  O : Bit 0
  I : Bit 1

data BitPair : ℕ → Set where
  bitpair : {n m : ℕ} → Bit n → Bit m → BitPair (2 * n + m)

addBit : ∀ {n m k} → Bit n → Bit m → Bit k → BitPair (n + m + k)
addBit O O O = bitpair O O
addBit O O I = bitpair O I
addBit O I O = bitpair O I
addBit O I I = bitpair I O
addBit I O O = bitpair O I
addBit I O I = bitpair I O
addBit I I O = bitpair I O
addBit I I I = bitpair I I

-- other take

and : ℕ → ℕ → ℕ
and zero    m = zero
and (suc n) m = m

or : ℕ → ℕ → ℕ
or zero    m = m
or (suc n) m = zero

xor : ℕ → ℕ → ℕ
xor zero    zero    = zero
xor zero    (suc m) = suc zero
xor (suc n) zero    = suc zero
xor (suc n) (suc m) = zero

AndGate : ∀ {n m} → Bit n → Bit m → Bit (and n m)
AndGate O b' = O
AndGate I b' = b'