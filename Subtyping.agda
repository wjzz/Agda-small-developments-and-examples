-- @author : Wojciech Jedynak (wjedynak@gmail.com)
-- @date   : 2011-09-18
-- @tags   : agda ; subtyping ; algorithmic subtyping 
-- @short  : Algorithm that decides subtyping of non-recursive types
-- @note   : We make the algorithm structurally recursive by annotating the types with sizes.
--           This makes the algorithm structurally recursive on the size!

module Subtyping where

open import Data.Bool

---------------------------
--  Type of annotations  --
---------------------------

data Size : Set where
  Atom : Size
  Comp : Size → Size → Size

----------------------------
--  Size annotated types  --
----------------------------

infixl 5 _+_ _×_ _⇒_

data Type : Size → Set where
  int float bool unit void : Type Atom
  _+_ _×_ _⇒_ : ∀ {n m} → (s : Type n) → (t : Type m) → Type (Comp n m)

-----------------------------------------
--  Size annotated subtyping relation  --
-----------------------------------------

infixl 4 _≤_

data _≤_ : ∀ {n} → Type n → Type n → Set where
  int-float : int ≤ float

  int-r   : int ≤ int
  float-r : float ≤ float
  bool-r  : bool ≤ bool
  unit-r  : unit ≤ unit
  void-r  : void ≤ void

  sum  : ∀ {n m} (s₁ t₁ : Type n)(s₂ t₂ : Type m)  → s₁ ≤ t₁  →  s₂ ≤ t₂  →  s₁ + s₂ ≤ t₁ + t₂
  prod : ∀ {n m} (s₁ t₁ : Type n)(s₂ t₂ : Type m)  → s₁ ≤ t₁  →  s₂ ≤ t₂  →  s₁ × s₂ ≤ t₁ × t₂
  fun  : ∀ {n m} (s₁ t₁ : Type n)(s₂ t₂ : Type m)  → t₁ ≤ s₁  →  s₂ ≤ t₂  →  s₁ ⇒ s₂ ≤ t₁ ⇒ t₂

-------------------------------------------------------------------------------
--  Function that decided the subtyping relation (weak specification style)  --
-------------------------------------------------------------------------------

_isSubtypeOf_ : ∀ {n} → Type n → Type n → Bool
int isSubtypeOf int = true
int isSubtypeOf float = true
int isSubtypeOf bool = false
int isSubtypeOf unit = false
int isSubtypeOf void = false
float isSubtypeOf int = false
float isSubtypeOf float = true
float isSubtypeOf bool = false
float isSubtypeOf unit = false
float isSubtypeOf void = false
bool isSubtypeOf t2 = {!!}
unit isSubtypeOf t2 = {!!}
void isSubtypeOf t2 = {!!}
(y + y') isSubtypeOf (s + t) = y isSubtypeOf s ∧ y' isSubtypeOf t
(y + y') isSubtypeOf (s × t) = false
(y + y') isSubtypeOf (s ⇒ t) = false
(y × y') isSubtypeOf t2 = {!!}
(y ⇒ y') isSubtypeOf (s + t) = false
(y ⇒ y') isSubtypeOf (s × t) = false
(y ⇒ y') isSubtypeOf (s ⇒ t) = s isSubtypeOf y ∧ y' isSubtypeOf t