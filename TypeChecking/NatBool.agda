{-
  @author: Wojciech Jedynak (wjedynak@gmail.com)
-}
module NatBool where

open import Data.Nat  using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)

-- open import Data.Bool
-- open import Data.Maybe

-- open import Data.List
-- open import Data.List.Theorems

-- open import Data.Nat
-- open import Data.Nat.Theorems

-- open import Data.Sum
open import Data.Product

open import Data.Empty
-- open import Data.Unit

-- open import Data.Fin
-- open import Data.Vec
-- --open import Data.Vec.Theorems

open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary


infixl 5 _+_
infixl 5 _∧_
infix  4 _∶_

-- types

data Type : Set where
  nat bool : Type

-- expressions

data Expr : Set where
  N   : (n : ℕ) → Expr
  _+_ : (e1 e2 : Expr) → Expr
  B   : (b : Bool) → Expr
  _∧_ : (b1 b2 : Expr) → Expr

-- typings

data _∶_ : Expr → Type → Set where
  N : ∀ {n} 
    → N n ∶ nat
  
  P : ∀ {e1 e2}
    → e1 ∶ nat
    → e2 ∶ nat
    → e1 + e2 ∶ nat

  B : ∀ {b}
    → B b ∶ bool

  A : ∀ {b1 b2}
    → b1 ∶ bool
    → b2 ∶ bool
    → b1 ∧ b2 ∶ bool

-- some helpers

_==_ : Decidable {A = Type} _≡_
nat  == nat  = yes refl
nat  == bool = no (λ ())
bool == nat  = no (λ ())
bool == bool = yes refl


-- types are unique

type-unique : ∀ {e t1 t2} → e ∶ t1 → e ∶ t2 → t1 ≡ t2
type-unique {N n} N N                    = refl
type-unique {e1 + e2} (P y y') (P y0 y1) = refl
type-unique {B b} B B                    = refl
type-unique {b1 ∧ b2} (A y y') (A y0 y1) = refl

-- boring lemmas

nat-not-bool : nat ≢ bool
nat-not-bool ()

-- type checking is decidable

typeCheck : (e : Expr) → Dec (∃ (λ type → e ∶ type))
typeCheck (N n) = yes (nat , N)
typeCheck (B b) = yes (bool , B)
typeCheck (e1 + e2) with typeCheck e1
typeCheck (e1 + e2) | yes (nat , pr1) with typeCheck e2
typeCheck (e1 + e2) | yes (nat , pr1) | yes (nat  , pr2) = yes (nat , P pr1 pr2)
typeCheck (e1 + e2) | yes (nat , pr1) | yes (bool , pr2) = no (λ { (.nat , P y y') → nat-not-bool (type-unique y' pr2) })
typeCheck (e1 + e2) | yes (nat , pr1) | no ¬p            = no (λ { (.nat , P y y') → ¬p (nat , y') })
typeCheck (e1 + e2) | yes (bool , pr1)                   = no (λ { (.nat , P y y') → nat-not-bool (type-unique y pr1) })
typeCheck (e1 + e2) | no ¬p                              = no (λ { (.nat , P y y') → ¬p (nat , y) })
typeCheck (b1 ∧ b2) with typeCheck b1
typeCheck (b1 ∧ b2) | yes (bool , pr1) with typeCheck b2
typeCheck (b1 ∧ b2) | yes (bool , pr1) | yes (bool , proj₂) = yes (bool , A pr1 proj₂)
typeCheck (b1 ∧ b2) | yes (bool , pr1) | yes (nat , proj₂)  = no λ { (.bool , A y y') → nat-not-bool (type-unique proj₂ y' ) }
typeCheck (b1 ∧ b2) | yes (bool , pr1) | no ¬p              = no λ { (.bool , A y y') → ¬p (bool , y') }
typeCheck (b1 ∧ b2) | yes (nat , proj₂)                     = no λ { (.bool , A y y') → nat-not-bool (type-unique proj₂ y) }
typeCheck (b1 ∧ b2) | no ¬p                                 = no λ { (.bool , A y y') → ¬p (bool , y) }

open import Data.List

safeHead : {A : Set} → A → List A → A
safeHead a = λ { (x ∷ xs) → x
               ; []       → a
               }