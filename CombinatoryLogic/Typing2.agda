-- @author : Wojciech Jedynak (wjedynak@gmail.com)
-- @date   : 2012-03-02
-- @tags   : combinatory logic ; agda
-- @short  : Typed combinatory logic.
-- @note   : We define the typing judgements for combinatory logic.

module Typing2 where

open import Data.Nat
open import Data.Fin hiding (#_)
open import Data.Product
open import Relation.Binary hiding (_⇒_)
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Syntax

-- syntax fixity

infixl 5 _∙_
infixr 5 _⇒_
infix  3 _⟶w_

-------------
--  Types  --
-------------

Var = ℕ

data Type : Set where
  #_  : (p : Var) → Type
  _⇒_ : (τ σ : Type) → Type

-- example types

exType : Type
exType = α ⇒ β ⇒ α where
  α = # 0
  β = # 1

----------------
--  Contexts  --
----------------

Ctx : Set
Ctx = Var → Type

----------------------
--  Indexed syntax  --
----------------------

data Term (Γ : Ctx) : Type → Set where
  #_  : ∀ v
      → Term Γ (Γ v)

  K   : ∀ {α β}
      → Term Γ (α ⇒ β ⇒ α)

  S   : ∀ {α β γ}
      → Term Γ ((α ⇒ β ⇒ γ) ⇒ (α ⇒ β) ⇒ (α ⇒ γ))

  _∙_ : ∀ {α β}
      → (t : Term Γ (α ⇒ β))
      → (s : Term Γ α)
      → Term Γ β

----------------------
--  Weak reduction  --
----------------------

data _⟶w_ {Γ : Ctx} : ∀ {α} → Term Γ α → Term Γ α → Set where

  K : ∀ {α β}
    → (x : Term Γ α)
    → (y : Term Γ β)
    → K ∙ x ∙ y ⟶w x


  S : ∀ {α β γ}
    → (x : Term Γ (α ⇒ β ⇒ γ))
    → (y : Term Γ (α ⇒ β))
    → (z : Term Γ α)
    → S ∙ x ∙ y ∙ z   ⟶w   x ∙ z ∙ (y ∙ z)


  red-l : ∀ {α β}
        → (f f' : Term Γ (α ⇒ β))
        → (a    : Term Γ α)
        → f     ⟶w f'
        → f ∙ a ⟶w f' ∙ a


  red-r : ∀ {α β}
        → (f    : Term Γ (α ⇒ β))
        → (a a' : Term Γ α)
        → a     ⟶w a'
        → f ∙ a ⟶w f ∙ a'

{-
-- reflexive-transivite closure of ⟶w

module Star {A : ℕ → Set} (Rel : {n : ℕ} → A n → A n → Set) where
  data Star {n : ℕ} : A n → A n → Set where
    zero : ∀ {a} → Star a a

    suc  : ∀ {a b c}
         → Rel a b 
         → Star b c
         → Star a c

module ReflTrans = Star {Term} _⟶w_

open ReflTrans
-}

---------------------
--  Normalization  --
---------------------

------------------------------------------
--  The notion of strong normalization  --
------------------------------------------

-- inductive definition of strong normalization

data SN {Γ : Ctx} : ∀ {α} → Term Γ α → Set where
  sn : ∀ {α}
     → {t : Term Γ α}
     → (∀ t' 
        → t ⟶w t' 
        → SN t')
     → SN t

-- variables are SN

SN-var : ∀ x Γ
       → SN {Γ} (# x)

SN-var x Γ = sn (λ t' ())

-- 

SN-app-l : ∀ {Γ α β}
           → (t : Term Γ (α ⇒ β))
           → (s : Term Γ α)
           → SN (t ∙ s)
           → SN t

SN-app-l {Γ} {α} {β} t s (sn ft) = sn f where
  f : (t' : Term Γ (α ⇒ β)) → t ⟶w t' → SN t'
  f t' red = SN-app-l t' s (ft (t' ∙ s) (red-l t t' s red))

----------------------------------
--  The notion of reducibility  --
----------------------------------

Red : (α : Type) → (∀ {Γ} → Term Γ α → Set)
Red (# p)       t = SN t
Red (U ⇒ V) {Γ} t = (u : Term Γ U) 
                  → Red U u 
                  → Red V (t ∙ u)

-- crucial properties of Red

c2 : ∀ Γ α 
   → (t t' : Term Γ α)
   → t ⟶w t'
   → Red α t
   → Red α t'

c2 Γ (# p) t t' rd (sn ft') = ft' _ rd
c2 Γ (τ ⇒ σ) t t' rd red = λ u red-u → 
  c2 Γ σ (t ∙ u) (t' ∙ u) 
         (red-l t t' u rd) 
         (red u red-u)

mutual
  cr1 : ∀ Γ α
      → (t : Term Γ α)
      → Red α t 
      → SN t
  cr1 Γ (# p)   t red = red
  cr1 Γ (τ ⇒ σ) t red = {!!}

  


-------------------
--  Main result  --
-------------------

all-combinators-strongly-normalizing 
  : ∀ Γ α
  → (t : Term Γ α)
  → SN t

all-combinators-strongly-normalizing = {!!}
