-- @author : Wojciech Jedynak (wjedynak@gmail.com)
-- @date   : 2011-09-06
-- @tags   : combinatory logic ; agda
-- @short  : Definition of combinators and reduction. 
-- @note   : We define the syntax of combinatory logic and the weak reduction relation.

module Syntax where

open import Data.Nat
open import Data.Product
open import Relation.Binary hiding (_⇒_)
open import Relation.Binary.PropositionalEquality

------------------------------
--  The set of combinators  --
------------------------------

infixl 5 _∙_

data C : Set where
  #_  : ℕ → C                            -- variable
  S   : C                                -- S combinator
  K   : C                                -- K combinator
  _∙_ : C → C → C                        -- application

-- NOTE: in this development we don't really mention variables
--       anywhere, so they could be deleted.

-----------------------------------
--  The weak reduction relation  --
-----------------------------------

infix 4 _⟶_
infix 4 _⟶*_

data _⟶_ : C → C → Set where

  S : ∀ {F G H} → 
      S ∙ F ∙ G ∙ H ⟶ F ∙ H ∙ (G ∙ H)

  K : ∀ {F} (G : C)  →                  -- G needs to be explicit
      K ∙ F ∙ G     ⟶ F

  app-l : ∀ {F F' G} → 
        F ⟶ F' →
    F ∙ G ⟶ F' ∙ G

  app-r : ∀ {F F' G} → 
        F ⟶ F' →
    G ∙ F ⟶ G ∙ F'

------------------------------------
--  Weak reduction in many steps  --
------------------------------------

-- the least reflexive and transitive relation
-- containing _⟶_

data _⟶*_ : C → C → Set where
  base : (X : C) → 
         X ⟶* X 

  step : {X Y Z : C} → 
         X ⟶  Y →
         Y ⟶* Z → 
         X ⟶* Z

-- the weak reduction in many steps is a preorder

many-steps-reflective : Reflexive _⟶*_
many-steps-reflective = base _

many-steps-transitive : Transitive _⟶*_
many-steps-transitive (base _)    r2 = r2
many-steps-transitive (step r r1) r2 = step r (many-steps-transitive r1 r2)

-- a useful monotonicity lemma

many-steps-monotonous : ∀ {X X' Y Y'} → 
                        X ⟶* X'  →
                        Y ⟶* Y'  →
                        X ∙ Y ⟶* X' ∙ Y'
many-steps-monotonous {.X'} {X'} {.Y'} {Y'} (base .X') (base .Y') = base (X' ∙ Y')
many-steps-monotonous {.X'} {X'} (base .X') (step y y') = step (app-r y) (many-steps-monotonous (base X') y')
many-steps-monotonous (step y y') red2 = step (app-l y) (many-steps-monotonous y' red2)

--------------------------------------------
--  A nice notation for rewriting proofs  --
--------------------------------------------

infixr 4 _⟶⟨_⟩_

_∎ : (X : C) → X ⟶* X
X ∎ = base X

_⟶⟨_⟩_ : (X : C) {Y Z : C} → X ⟶ Y → Y ⟶* Z → X ⟶* Z
X ⟶⟨ prf ⟩ prf2 = step prf prf2

-------------------------------
--  Some example reductions  --
-------------------------------

k-rule-test : ∀ (X Y : C) → K ∙ X ∙ Y ⟶* X
k-rule-test X Y = 
  K ∙ X ∙ Y ⟶⟨ K _ ⟩ 
  X 
 ∎

identity-combinator : ∀ (X : C) → (S ∙ K ∙ K) ∙ X ⟶* X
identity-combinator X = 
 (S ∙ K ∙ K) ∙ X    ⟶⟨ S   ⟩
  K ∙ X ∙ (K ∙ X)   ⟶⟨ K _ ⟩
  X
 ∎
