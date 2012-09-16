{-
  @author: Wojciech Jedynak (wjedynak@gmail.com)
-}
module STC where

open import Data.Nat
open import Data.Empty
open import Data.Product

--------------------
--  Atomic types  --
--------------------

Atom : Set
Atom = ℕ

-------------
--  Types  --
-------------

infixr 5 _⇒_

data Type : Set where
  A   : (a : Atom)   → Type
  _⇒_ : (α β : Type) → Type

-------------------
--  Typed terms  --
-------------------

infixl 5 _∙_

data Term : Type → Set where

  K : ∀ {α β} → Term (α ⇒ β ⇒ α)

  S : ∀ {α β γ} → Term ((α ⇒ β ⇒ γ) ⇒ (α ⇒ β) ⇒ α ⇒ γ)

  _∙_ : ∀ {α β} 
      → Term (α ⇒ β)
      → Term α
      → Term β

-- example terms
-- both I and K2 are found automatically by auto :-)

I : ∀ α → Term (α ⇒ α)
I α = S ∙ K ∙ K {β = α}

K2 : ∀ α β → Term (α ⇒ β ⇒ β)
K2 α β = K ∙ (S ∙ K ∙ K {β = α})

----------------------
--  Head reduction  --
----------------------

infix 1 _⟶_

data _⟶_ : ∀ {α} → Term α → Term α → Set where
  
  KR : ∀ {α β}
     → (M : Term α)
     → (N : Term β)
     → K ∙ M ∙ N ⟶ M

  SR : ∀ {α β γ}
     → (M : Term (α ⇒ β ⇒ γ))
     → (N : Term (α ⇒ β))
     → (O : Term α)
     → S ∙ M ∙ N ∙ O ⟶ (M ∙ O) ∙ (N ∙ O)

  AR : ∀ {α β}
     → (M N : Term (α ⇒ β))
     → (O   : Term α)
     → M     ⟶ N
     → M ∙ O ⟶ N ∙ O

-- reflexive and transitive closure of _⟶_

infix 1 _⟶*_

data _⟶*_ : ∀ {α} → Term α → Term α → Set where

  here : ∀ {α} 
       → (t : Term α)
       → t ⟶* t

  there : ∀ {α}
        → {t1 t2 t3 : Term α}
        → t1 ⟶  t2
        → t2 ⟶* t3
        → t1 ⟶* t3

-- example: behavior of I

reduction-example : ∀ {α} (M : Term α) → (I α) ∙ M ⟶* M
reduction-example M = there (SR K K M) (there (KR M (K ∙ M)) (here M))

--------------------------
--  Normalizable terms  --
--------------------------

data Normalizable : ∀ {α} → Term α → Set where
  
  KN : ∀ {α β} 
     → Normalizable (K {α} {β})

  SN : ∀ {α β γ} 
     → Normalizable (S {α} {β} {γ})

  K1N : ∀ {α β} 
      → {M : Term α}
      → Normalizable M
      → Normalizable (K {β = β} ∙ M)

  S1N : ∀ {α β γ} 
      → {M : Term (α ⇒ β ⇒ γ)}
      → Normalizable M
      → Normalizable (S ∙ M)

  S2N : ∀ {α β γ} 
      → {M : Term (α ⇒ β ⇒ γ)}
      → {N : Term (α ⇒ β)}
      → Normalizable M
      → Normalizable N
      → Normalizable (S ∙ M ∙ N)
  

  RN : ∀ {α}
     → {M N : Term α}
     → M ⟶ N
     → Normalizable N
     → Normalizable M

------------------------
--  Computable terms  --
------------------------

Computable : (α : Type) → (Term α → Set)
Computable (A a)   T = ⊥
Computable (α ⇒ β) M = Normalizable M 
                     × ((N : Term α) → Computable α N 
                                     → Computable β (M ∙ N))


comp2norm : ∀ {α} (t : Term α) 
          → Computable α t
          → Normalizable t

comp2norm {A a}   _ comp = ⊥-elim comp
comp2norm {α ⇒ β} M comp = proj₁ comp

-- main lemma 

red-comp : ∀ {α} {M N : Term α}
         → M ⟶ N
         → Computable α N
         → Computable α M

red-comp {A a}   red comp-N = comp-N
red-comp {α ⇒ β} {M} {N} red (norm-N , comp-app-N) = (RN red norm-N) , (λ O comp-O → red-comp {β} (AR M N O red) (comp-app-N O comp-O))

-- main theorem

all-terms-computable : ∀ {α} (t : Term α)
                     → Computable α t

all-terms-computable K = KN , (λ N comp-N → K1N (comp2norm N comp-N) , (λ N₁ comp-N1 → red-comp {_} {K ∙ N ∙ N₁} {N} (KR N N₁) comp-N))

all-terms-computable S = SN , (λ M comp-M → (S1N (proj₁ comp-M)) , (λ N comp-N → (S2N (proj₁ comp-M) (proj₁ comp-N)) , (λ O comp-O → 
  red-comp {_} {S ∙ M ∙ N ∙ O} {M ∙ O ∙ (N ∙ O)} (SR M N O) (proj₂ (proj₂ comp-M O comp-O) (N ∙ O) (proj₂ comp-N O comp-O)))))

-- an appeal to the induction hyp is enough
all-terms-computable (m ∙ n) with all-terms-computable m | all-terms-computable n
... | normalizable-m , all-n | comp-n = all-n n comp-n

-- main result

all-term-normalizable : ∀ {α} (t : Term α)
                      → Normalizable t
all-term-normalizable t 
  = comp2norm t (all-terms-computable t)

get-term : ∀ {α}{t : Term α} → Normalizable t → Term α
get-term KN = K
get-term SN = S
get-term (K1N norm) = K ∙ get-term norm
get-term (S1N norm) = S ∙ get-term norm
get-term (S2N norm norm₁) = S ∙ get-term norm ∙ get-term norm₁
get-term (RN x norm) = get-term norm              -- this step actually performs the reduction

example : Term (A 0 ⇒ A 0)
example = get-term (all-term-normalizable (I (A 0 ⇒ A 0) ∙ (I (A 0 ⇒ A 0) ∙ I (A 0))))
