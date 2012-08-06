{-
  @author: Wojciech Jedynak (wjedynak@gmail.com)
-}
module Terms where

open import Data.Nat
open import Data.Fin
open import Data.Fin.Props
open import Data.Bool
open import Data.Unit using (⊤; tt)
open import Data.Product
open import Data.Empty

open import Data.Vec

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality


module V = Data.Vec

-------------
--  Types  --
-------------

infixr 5 _⇒_
--infix  7 _⟶_

-- base types

data Base : Set where
  TBool TNat : Base

data Type : Set where
  B   : (b : Base) → Type
  _⇒_ : (t₁ t₂ : Type) → Type

Boolean = B TBool
Natural = B TNat

----------------
--  Contexts  --
----------------

Ctx : ℕ → Set
Ctx = Vec Type

_!_ : ∀ {n : ℕ} {l} {A : Set l} → Vec A n → Fin n → A
Γ ! i = lookup i Γ

∅ : Ctx 0
∅ = []

-------------
--  Terms  --
-------------

data Term : {n : ℕ} → Ctx n → Type → Set where

  var : ∀ {n} 
      → {Γ : Ctx n}
      → {t : Type}
      → (i : Fin n)
      → (ind : Γ ! i ≡ t)
      → Term Γ t

  app : ∀ {n} t₁ {t₂}
      → {Γ : Ctx n}
      → (M : Term Γ (t₁ ⇒ t₂))
      → (N : Term Γ t₁)
      → Term Γ t₂

  abs : ∀ {n t₁ t₂}
      → {Γ : Ctx n}
      → (T : Term (t₁ ∷ Γ) t₂)
      → Term Γ (t₁ ⇒ t₂)

  true false : ∀ {n} {Γ : Ctx n} 
             → Term Γ Boolean

  cond : ∀ {n t} {Γ : Ctx n}
       → Term Γ Boolean
       → Term Γ t
       → Term Γ t
       → Term Γ t

-------------------------
--  Equality of terms  --
-------------------------

arr-inv : ∀ {t1 t2 t3 t4} 
        → t1 ⇒ t3 ≡ t2 ⇒ t4 
        → t1 ≡ t2 × t3 ≡ t4

arr-inv refl = refl , refl       


_≟tp_ : (t1 t2 : Type) → Dec (t1 ≡ t2)
B TBool ≟tp B TBool = yes refl
B TBool ≟tp B TNat = no (λ ())
B TBool ≟tp (t₁ ⇒ t₂) = no (λ ())
B TNat ≟tp B TBool = no (λ ())
B TNat ≟tp B TNat = yes refl
B TNat ≟tp (t₁ ⇒ t₂) = no (λ ())
(t1 ⇒ t2) ≟tp B b = no (λ ())
(t1 ⇒ t2) ≟tp (t3 ⇒ t4) with t1 ≟tp t3 | t2 ≟tp t4
(t1 ⇒ t2) ≟tp (t3 ⇒ t4) | yes p | yes p₁ rewrite p | p₁ = yes refl
(t1 ⇒ t2) ≟tp (t3 ⇒ t4) | yes p | no ¬p = no (λ z → ¬p (proj₂ (arr-inv z)))
(t1 ⇒ t2) ≟tp (t3 ⇒ t4) | no ¬p | r2 = no (λ z → ¬p (proj₁ (arr-inv z)))

----------------------

proof-irr-eq : {A : Set} → {a a' : A}
             → (p1 p2 : a ≡ a')
             → p1 ≡ p2
proof-irr-eq refl refl = refl


var-inv-1 : ∀ {n t}{Γ : Ctx n} → {i i' : Fin n}
          → (prf1 : Γ ! i  ≡ t) 
          → (prf2 : Γ ! i' ≡ t) 
          → var i prf1 ≡ var i' prf2 → i ≡ i'
var-inv-1 .b b refl = refl


abs-inv : ∀ {n t t'}{Γ : Ctx n}{M N : Term (t' ∷ Γ) t} 
         → abs M ≡ abs N → M ≡ N
abs-inv refl = refl


app-inv-1 : ∀ {n t t0 t1}{Γ : Ctx n}
          → {M  : Term Γ (t0 ⇒ t)}
          → {M' : Term Γ (t1 ⇒ t)}
          → {N  : Term Γ t0}
          → {N' : Term Γ t1}
          → app t0 M N ≡ app t1 M' N' → t0 ≡ t1
app-inv-1 refl = refl


app-inv-2 : ∀ {n t t'}{Γ : Ctx n}
          → {M M' : Term Γ (t' ⇒ t)} {N N' : Term Γ t'}
          → app t' M N ≡ app t' M' N' → M ≡ M' × N ≡ N'
app-inv-2 refl = refl , refl



cond-inv : ∀ {n t}{Γ : Ctx n}
         → {C C' : Term Γ Boolean} {M N M' N' : Term Γ t}
         → cond C M N ≡ cond C' M' N' → C ≡ C' × M ≡ M' × N ≡ N'
cond-inv refl = refl , refl , refl

------------------------------------------------

_≟t_ : ∀ {n t}{Γ : Ctx n} → (M N : Term Γ t) → Dec (M ≡ N)
var i prf ≟t var i' ind with i Data.Fin.Props.≟ i'
var i p1  ≟t var i' p2 | yes p rewrite p | proof-irr-eq p1 p2 = yes refl
var i prf ≟t var i' ind | no ¬p = no (λ z → ¬p (var-inv-1 prf ind z))
var i prf ≟t app t₁ N N₁ = no (λ ())
var i prf ≟t abs N = no (λ ())
var i prf ≟t true = no (λ ())
var i prf ≟t false = no (λ ())
var i prf ≟t cond N N₁ N₂ = no (λ ())
app t₁ M M₁ ≟t var i ind = no (λ ())
app t₁ M M₁ ≟t app t₂ N N₁ with t₁ ≟tp t₂ 
app t₁ M M₁ ≟t app t₂ N N₁ | yes p rewrite p with M ≟t N | M₁ ≟t N₁
... | yes P | yes Q rewrite P | Q = yes refl
... | yes P | no ¬Q = no (λ z → ¬Q (proj₂ (app-inv-2 z)))
... | no ¬P | r2 = no (λ z → ¬P (proj₁ (app-inv-2 z)))
app t₁ M M₁ ≟t app t₂ N N₁ | no ¬p = no (λ x → ¬p (app-inv-1 x))
app t₁ M M₁ ≟t abs N = no (λ ())
app t₁ M M₁ ≟t true = no (λ ())
app t₁ M M₁ ≟t false = no (λ ())
app t₁ M M₁ ≟t cond N N₁ N₂ = no (λ ())
abs M ≟t var i ind = no (λ ())
abs M ≟t app t₃ N N₁ = no (λ ())
abs M ≟t abs N with M ≟t N
abs M ≟t abs N | yes p = yes (cong abs p)
abs M ≟t abs N | no ¬p = no (λ { x → ¬p (abs-inv x)})
abs M ≟t cond N N₁ N₂ = no (λ ())
true ≟t var i ind = no (λ ())
true ≟t app t₁ M N = no (λ ())
true ≟t true = yes refl
true ≟t false = no (λ ())
true ≟t cond x x₁ x₂ = no (λ ())
false ≟t var i ind = no (λ ())
false ≟t app t₁ M N = no (λ ())
false ≟t true = no (λ ())
false ≟t false = yes refl
false ≟t cond x x₁ x₂ = no (λ ())
cond M M₁ M₂ ≟t var i ind = no (λ ())
cond M M₁ M₂ ≟t app t₁ N N₁ = no (λ ())
cond M M₁ M₂ ≟t abs N = no (λ ())
cond M M₁ M₂ ≟t true = no (λ ())
cond M M₁ M₂ ≟t false = no (λ ())
cond M M₁ M₂ ≟t cond N N₁ N₂ with M ≟t N | M₁ ≟t N₁ | M₂ ≟t N₂
cond M M₁ M₂ ≟t cond N N₁ N₂ | yes p | yes p₁ | yes p₂ rewrite p | p₁ | p₂ = yes refl
cond M M₁ M₂ ≟t cond N N₁ N₂ | yes p | yes p₁ | no ¬p = no (λ z → ¬p (proj₂ (proj₂ (cond-inv z))))
cond M M₁ M₂ ≟t cond N N₁ N₂ | yes p | no ¬p | r3 = no (λ z → ¬p (proj₁ (proj₂ (cond-inv z))))
cond M M₁ M₂ ≟t cond N N₁ N₂ | no ¬p | r2 | r3 = no (λ z → ¬p (proj₁ (cond-inv z)))

isTrue : ∀ {n}{Γ : Ctx n} → (M : Term Γ Boolean) → Dec (M ≡ true)
isTrue (var i _) = no (λ ())
isTrue (app t₁ M M₁) = no (λ ())
isTrue true = yes refl
isTrue false = no (λ ())
isTrue (cond M M₁ M₂) = no (λ ())

--------------------------------
--  Example well typed terms  --
--------------------------------

t-id : Term ∅ (Boolean ⇒ Boolean)
t-id = abs (var (# 0) refl)

t-K : (p q : Type) → Term ∅ (p ⇒ q ⇒ p)
t-K p q = abs (abs (var (# 1) refl))

t-comp : (p q r : Type) → Term ∅ ((p ⇒ q) ⇒ (q ⇒ r) ⇒ (p ⇒ r))
t-comp p q r = abs (abs (abs (app q (var (# 1) refl) (app p (var (# 2) refl) (var (# 0) refl)))))
