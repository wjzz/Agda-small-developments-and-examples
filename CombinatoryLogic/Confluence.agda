-- @author : Wojciech Jedynak (wjedynak@gmail.com)
-- @date   : 2011-09-06
-- @tags   : combinatory logic ; agda
-- @short  : Proof of Church-Rosser.
-- @note   : We prove the Church-Rosser property using the Martin-Lôf--Tait
--           method of parallel reduction.

module Confluence where

open import Data.Nat
open import Data.Product
open import Relation.Binary hiding (_⇒_)
open import Relation.Binary.PropositionalEquality

open import Syntax

---------------------------------------
--  The parallel reduction relation  --
---------------------------------------

infix 5 _⇒_

data _⇒_ : C → C → Set where

  var : ∀ (n : ℕ) →
      # n ⇒ # n

  K   : ∀ {X X'} (Y : C) →
      X ⇒ X' →
      K ∙ X ∙ Y ⇒ X'

  S   : ∀ {X X' Y Y' Z Z'} →
      X ⇒ X' →
      Y ⇒ Y' →
      Z ⇒ Z' →
      S ∙ X ∙ Y ∙ Z ⇒ X' ∙ Z' ∙ (Y' ∙ Z')

  app : ∀ {X X' Y Y'} →
      X ⇒ X' →
      Y ⇒ Y' →
      X ∙ Y ⇒ X' ∙ Y'

  -- special cases to make the following proofs go through
  -- we need it to show that ⇒ is reflexive (see below)
  K₀  : K ⇒ K
  S₀  : S ⇒ S
  
--------------------------------------------
--  Properties of the parallel reduction  --
--------------------------------------------

parallel-refl : Reflexive _⇒_
parallel-refl {# y}   = var y
parallel-refl {S}     = S₀
parallel-refl {K}     = K₀
parallel-refl {X ∙ Y} = app parallel-refl parallel-refl


weak-to-par : ∀ {X Y} →   X ⟶ Y   →   X ⇒ Y
weak-to-par S           = S   parallel-refl parallel-refl parallel-refl
weak-to-par (K G)       = K G parallel-refl
weak-to-par (app-l red) = app (weak-to-par red) parallel-refl
weak-to-par (app-r red) = app parallel-refl (weak-to-par red)

par-to-many-weak : ∀ {X Y : C} →   X ⇒ Y   →   X ⟶* Y
par-to-many-weak (var n) = base (# n)
par-to-many-weak (K Y' red) = step (K Y') (par-to-many-weak red)
par-to-many-weak K₀ = base K
par-to-many-weak S₀ = base S
par-to-many-weak (app redX redY) = 
  many-steps-monotonous (par-to-many-weak redX) 
                        (par-to-many-weak redY)
par-to-many-weak (S redX redY redZ) = 
  step S (many-steps-monotonous (many-steps-monotonous (par-to-many-weak redX) 
                                                       (par-to-many-weak redZ)) 
         (many-steps-monotonous (par-to-many-weak redY) 
                                (par-to-many-weak redZ)))

--------------------------------------------
--  The full development of a combinator  --
--------------------------------------------

expand : C → C
expand (# x) = # x
expand S     = S
expand K     = K
expand (K ∙ X ∙ Y)     = expand X
expand (S ∙ X ∙ Y ∙ Z) = expand X ∙ expand Z ∙ (expand Y ∙ expand Z)
expand (X ∙ Y)         = expand X ∙ expand Y

-- NOTE: For clarity and brevity we use overlapping patterns here. 
--       This feature is somewhat shaky in Agda and the proof of par-red-expand
--       is very bloated -- we have to pay the price somewhere...

--       So far we avoided the issue, because we were defining relations -- not functions.

-----------------------------------------------------------
--  The key lemma for proving the Church-Rosser theorem  --
-----------------------------------------------------------

par-red-expand : ∀ {X Y} → X ⇒ Y   →  Y ⇒ expand X
par-red-expand (var n) = var n
par-red-expand (K Y' red) = par-red-expand red
par-red-expand (S y y' y0) = app (app (par-red-expand y) (par-red-expand y0))
                               (app (par-red-expand y') (par-red-expand y0))
par-red-expand K₀ = K₀
par-red-expand S₀ = S₀
par-red-expand {K ∙ Y ∙ Z} (app (app K₀ y') redY) = 
  K _ (par-red-expand y')
par-red-expand {S ∙ X ∙ Y ∙ Z} (app (app (app S₀ y') y0) red2) = 
  S (par-red-expand y') (par-red-expand y0) (par-red-expand red2)

-- other cases are just using app, but we have no choise, 
-- as this is what you get when you play with overlapping patterns

par-red-expand {# y ∙ Y} {X' ∙ Y'} (app redX redY) = app (par-red-expand redX) (par-red-expand redY)
par-red-expand {S ∙ Y} {X' ∙ Y'} (app redX redY) = app (par-red-expand redX) (par-red-expand redY)
par-red-expand {K ∙ Y} {X' ∙ Y'} (app redX redY) = app (par-red-expand redX) (par-red-expand redY)
par-red-expand {# y ∙ y' ∙ Y} {X' ∙ Y'} (app redX redY) = app (par-red-expand redX) (par-red-expand redY)
par-red-expand {S ∙ y' ∙ Y} {X' ∙ Y'} (app redX redY) = app (par-red-expand redX) (par-red-expand redY)
par-red-expand {# y ∙ y' ∙ y0 ∙ Y} {X' ∙ Y'} (app redX redY) = app (par-red-expand redX) (par-red-expand redY)
par-red-expand {K ∙ y' ∙ y0 ∙ Y} {X' ∙ Y'} (app redX redY) = app (par-red-expand redX) (par-red-expand redY)
par-red-expand {y ∙ y' ∙ y0 ∙ y1 ∙ Y} {X' ∙ Y'} (app redX redY) = app (par-red-expand redX) (par-red-expand redY)

-- now we can prove the confluence (the diamond property) of ⇒

diamond : ∀ {F X Y} → F ⇒ X → F ⇒ Y → Σ[ F' ∶ C ](X ⇒ F' × Y ⇒ F')
diamond {F} red1 red2 = expand F , par-red-expand red1 , par-red-expand red2

-----------------------------------------
--  The parallel reduction in n steps  --
-----------------------------------------

data _⇒[_]⇒_ : C → ℕ → C → Set where
  base : ∀ {X} → X ⇒[ 0 ]⇒ X
  step : ∀ {n X Y Z} →      
         X ⇒ Y           →
         Y ⇒[ n     ]⇒ Z →
         X ⇒[ suc n ]⇒ Z

--------------------------------------------
--  The proof of the diagram chase for ⇒  --
--------------------------------------------

mutual

  diagram-chase : ∀ {F X Y n m} → 
                     F ⇒[ n ]⇒ X →    F ⇒[ m ]⇒ Y → 
        Σ[ F' ∶ C ]( X ⇒[ m ]⇒ F'  ×  Y ⇒[ n ]⇒ F')

  diagram-chase (base {X}) base          = X , base , base
  diagram-chase base (step {Z = Y} y y') = Y , step y y' , base
  diagram-chase (step {Z = Y} y y') base = Y , base , step y y'
  diagram-chase (step {Y = A} F⇒A A⇒n⇒X) (step {Y = B} F⇒B B⇒m⇒Y) = 
    inductive-step F⇒A F⇒B A⇒n⇒X B⇒m⇒Y 
    (λ F' X⇒F'     → diagram-chase A⇒n⇒X (step X⇒F' base)) 
    (λ X' B⇒1+n⇒X' → diagram-chase B⇒1+n⇒X' B⇒m⇒Y)

  inductive-step : ∀ {n m F A B X Y}
                 → F ⇒ A 
                 → F ⇒ B 
                 → A ⇒[ n ]⇒ X
                 → B ⇒[ m ]⇒ Y
                 → ((F' : C) → (A ⇒ F') → Σ[ X' ∶ C ](X ⇒[ 1 ]⇒ X' × F' ⇒[ n ]⇒ X'))
                 → ((X' : C) → (B ⇒[ suc n ]⇒ X') → Σ[ G ∶ C ](X' ⇒[ m ]⇒ G × Y ⇒[ suc n ]⇒ G))
                 → Σ[ F⁰ ∶ C ]( X ⇒[ suc m ]⇒ F⁰ × Y ⇒[ suc n ]⇒ F⁰)
               
  inductive-step F⇒A F⇒B A⇒n⇒X B⇒m⇒Y f1 f2 with diamond F⇒A F⇒B
  ... | F' , A⇒F'           , B⇒F'    with f1 F' A⇒F'
  ... | X' , step X⇒X' base , F'⇒n⇒X' with f2 X' (step B⇒F' F'⇒n⇒X')
  ... | G ,  X'⇒m⇒G         , Y⇒1+n⇒G = G , step X⇒X' X'⇒m⇒G , Y⇒1+n⇒G
 

-- NOTE: We can get rid of the mutual block, if define inductive-step before diagram-chase,
--       but it seemed clearer to state the theorem before the lemma.

-- NOTE2: The inductive-step lemma is defined to work around the limitation of Agda's
--        termination checker. In the main theorem, we want to use lexicographic induction
--        on pairs: from <1+n,1+m> first use <n,1> and then <1+n,m>.

--        The problem is that we must add a with block BEFORE we recurse.
--        The with construct makes Agda forget the origin of the arguments,
--        so it no longer sees that the recursion actually terminates!

--        The trick we do here is that the we treat pack the recursive calls to
--        diagram-chase in anonymous functions and then we give all the information
--        to the inductive-step lemma/helper which does all the pattern matching
--        it needs and uses the functions when appropriate.

------------------------------------------
--  Conversions between ⟶* and ⇒[ n ]⇒ --
------------------------------------------

weak-many-to-par-many : ∀ {F G} → F ⟶* G → Σ[ n ∶ ℕ ](F ⇒[ n ]⇒ G)
weak-many-to-par-many {.G} {G} (base .G) = 0 , base
weak-many-to-par-many (step y y') with weak-many-to-par-many y'
... | n , r = suc n , step (weak-to-par y) r

par-many-to-weak-many : ∀ {n F G} → F ⇒[ n ]⇒ G → F ⟶* G
par-many-to-weak-many base = base _
par-many-to-weak-many (step y y') = 
  many-steps-transitive (par-to-many-weak y) (par-many-to-weak-many y')

--------------------------------------------------------------
--  The Church-Rosser property for the combinatorial logic  --
--------------------------------------------------------------

weak-church-rosser : ∀ {X F F'} → X ⟶ F → X ⟶ F' → Σ[ X' ∶ C ]( F ⟶* X' × F' ⟶* X' )
weak-church-rosser {X} red1 red2 = expand X , 
                       (par-to-many-weak (par-red-expand (weak-to-par red1))) ,
                       (par-to-many-weak (par-red-expand (weak-to-par red2))) 


church-rosser : ∀ {X F F'} → X ⟶* F → X ⟶* F' → Σ[ X' ∶ C ]( F ⟶* X' × F' ⟶* X' )
church-rosser red1 red2 with weak-many-to-par-many red1 | weak-many-to-par-many red2
... | n1 , r1 | n2 , r2 with diagram-chase r1 r2
... | X' , m1 , m2 = X' , par-many-to-weak-many m1 , par-many-to-weak-many m2
