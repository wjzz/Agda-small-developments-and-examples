{-# OPTIONS --universe-polymorphism #-}

module LevelPromotion where

open import Level
open import Relation.Binary.PropositionalEquality

t : Set ≡ Set₀
t = refl

t2 : Set ≡ Set zero
t2 = refl

promote : (a : Level) (A : Set) → Set a
promote a A = Lift A
