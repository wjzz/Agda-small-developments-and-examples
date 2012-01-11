-- @author : Wojciech Jedynak (wjedynak@gmail.com)
-- @date   : 2012-01-03
-- @tags   : combinatory logic ; agda
-- @short  : Typed combinatory logic.
-- @note   : We define the typing judgements for combinatory logic.

module Typing where

open import Data.Nat
open import Data.Fin hiding (#_)
open import Data.Product
open import Relation.Binary hiding (_⇒_)
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Syntax

-- syntax fixity

infixl 4 _,_
infix  3 _∈_
infixl 5 _∙_
infixr 5 _⇒_
infix  2 _⊢_∶_
infix  3 _⟶w_
-------------
--  Types  --
-------------

TypVar = ℕ

data Type : Set where
  #_  : (p : TypVar) → Type
  _⇒_ : (τ σ : Type) → Type

-- example types

exType : Type
exType = α ⇒ β ⇒ α where
  α = # 0
  β = # 1

----------------
--  Contexts  --
----------------

data Ctx : ℕ → Set where
  ∅   : Ctx 0
  _,_ : ∀ {n} → (Γ : Ctx n) → (α : Type) → Ctx (suc n)

-- context membership

data _∈_ : ∀ {n} → Type → Ctx n → Set where
  here  : ∀ {n σ}{Γ : Ctx n}                      → σ ∈ Γ , σ
  there : ∀ {n σ}{Γ : Ctx n} → (α : Type) → σ ∈ Γ → σ ∈ Γ , α

-- a forgetful map from the position to the index

[_] : ∀ {n α}{Γ : Ctx n} → α ∈ Γ → Fin n
[ here ]      = zero
[ there α i ] = suc [ i ]

----------------------
--  Indexed syntax  --
----------------------

-- terms are indexed with the max. number of variables

data Term (n : ℕ) : Set where
  #_  : Fin n → Term n
  K   : Term n
  S   : Term n
  _∙_ : (f a : Term n) → Term n

-------------------------
--  Typing judgements  --
-------------------------

data _⊢_∶_ {n : ℕ} (Γ : Ctx n) : Term n → Type → Set where

  ass : ∀ {τ} → (i : τ ∈ Γ) → Γ ⊢ # [ i ] ∶ τ 

  app : ∀ {f a α β}
      → Γ ⊢ f ∶ α ⇒ β
      → Γ ⊢ a ∶ α
      → Γ ⊢ f ∙ a ∶ β

  K   : ∀ {α β}
      → Γ ⊢ K ∶ α ⇒ β ⇒ α

  S   : ∀ {α β γ}
      → Γ ⊢ S ∶ (α ⇒ β ⇒ γ) ⇒ (α ⇒ β) ⇒ (α ⇒ γ)

----------------------
--  Weak reduction  --
----------------------

data _⟶w_ {n : ℕ} : Term n → Term n → Set where

  K : ∀ {x} (y : Term n)
    → K ∙ x ∙ y ⟶w x

  S : ∀ {x y z}
    → S ∙ x ∙ y ∙ z   ⟶w   x ∙ z ∙ (y ∙ z)

  red-l : ∀ {f f' a}
        → f     ⟶w f'
        → f ∙ a ⟶w f' ∙ a

  red-r : ∀ {f a a'}
        → a     ⟶w a'
        → f ∙ a ⟶w f ∙ a'

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

----------------------------------------
--  Properties of the weak reduction  --
----------------------------------------

-- preservation under reduction

preservation : ∀ {n Γ α} {t t' : Term n} 
             → Γ ⊢ t ∶ α 
             → t ⟶w t' 
             → Γ ⊢ t' ∶ α
preservation (ass i) ()
preservation K ()
preservation S ()
preservation (app (app K y') y0) (K a)      = y'
preservation (app (app (app S y0) y1) y') S = app (app y0 y') (app y1 y')
preservation (app y y') (red-l y0)          = app (preservation y y0) y'
preservation (app y y') (red-r y0)          = app y (preservation y' y0)

-- i don't know how to state progress

----------------------------
--  A simple interpreter  --
----------------------------

interpType : Type → Set
interpType (# p)   = Fin p
interpType (τ ⇒ σ) = interpType τ → interpType σ

-- we only consider closed terms
-- we could extend this by introducing environments

{-
interpTerm : ∀ {τ} (t : Term 0)
           → ⦃ der : ∅ ⊢ t ∶ τ ⦄
           → interpType τ
interpTerm (# ())
interpTerm K       {{K}}             = λ x y   → x
interpTerm S       {{S}}             = λ x y z → x z (y z)
interpTerm (f ∙ a) {{app fder ader}} = (interpTerm f) (interpTerm a)
-}

interpTerm : ∀ {τ} (t : Term 0)
           → ∅ ⊢ t ∶ τ
           → interpType τ
interpTerm (# ()) der
interpTerm K       K               = λ x y   → x
interpTerm S       S               = λ x y z → x z (y z)
interpTerm (f ∙ a) (app fder ader) = (interpTerm f fder) (interpTerm a ader)

postulate
  lemma-der : ∀ {α n} {Γ : Ctx n} {t : Term n} → (der der' : Γ ⊢ t ∶ α) → der ≡ der'

correct : ∀ {α t t'} → Star t t' → (der : ∅ ⊢ t ∶ α) → (der' : ∅ ⊢ t' ∶ α) 
        → interpTerm t der ≡ interpTerm t' der'
correct ReflTrans.zero           der der' rewrite lemma-der der der' = refl
correct (ReflTrans.suc (K y) rest) (app (app K y0) y1) der' = correct rest y0 der'
correct (ReflTrans.suc S rest) (app y' y0) der' = {!!}
correct (ReflTrans.suc (red-l y) rest) (app y' y0) der' = {!!}
correct (ReflTrans.suc (red-r y) rest) der der' = {!!}

---------------------
--  Normalization  --
---------------------

