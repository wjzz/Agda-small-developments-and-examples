{-
  @author: Wojciech Jedynak (wjedynak@gmail.com)

  2012-04-02

  Finding out the usage of monads in the stdlib.
-}
module Monads where

open import Data.Nat
open import Data.Product
open import Data.Unit
open import Relation.Binary.PropositionalEquality

--------------------
--  Binary trees  --
--------------------

data Tree (A : Set) : Set where
  leaf : Tree A
  node : (a : A) (l r : Tree A) → Tree A

-- the classic monad state example: tree node numbering

number : ∀ {A} → Tree A → ℕ → (Tree ℕ × ℕ)
number leaf         n = leaf , n
number (node a l r) n with number l n
... | l' , n' with number r (suc n')
... | r' , n'' = node n' l' r' , n''

num : ∀ {A} → Tree A → Tree ℕ
num t = proj₁ (number t 0)

-- example

ex : Tree ℕ
ex = node 20 (node 10 leaf leaf)
             (node 30 leaf leaf)

--------------------------------
--  Hand-written state monad  --
--------------------------------
module MyStateMonad where
  State : Set
  State = ℕ

  M : Set → Set
  M A = State → (A × State)

  runM : ∀ {A} → M A → State → A
  runM f n = proj₁ (f n)

  return : ∀ {A} → A → M A
  return a = λ s → (a , s)

  infixl 5 _>>=_
  infixl 5 _>>_ 

  _>>=_ : ∀ {A B} → M A → (A → M B) → M B
  f >>= g = λ st →
              let x = f st 
              in  g (proj₁ x) (proj₂ x)

  _>>_ : ∀ {A B} → M A → M B → M B
  f >> g = f >>= (λ _ → g)

  -- monadic laws

  return-l : ∀ {A}
           → (f : M A)
           → f >>= return ≡ f
  return-l f = refl


  return-r : ∀ {A B}
           → (x : A)
           → (f : A → M B)
           → return x >>= f ≡ f x

  return-r x f = refl


  bind-assoc : ∀ {A B C}
             → (f : M A)
             → (g : A → M B)
             → (h : B → M C)
             → f >>= (λ a → (g a >>= h)) ≡ (f >>= g) >>= h

  bind-assoc f g h = refl

  -- helpers
  
  get : M State
  get = λ st → st , st

  put : State → M ⊤
  put st' = λ st → tt , st'

  -- tree numbering the monadic way

  numberM : ∀ {A} → Tree A → M (Tree ℕ)
  numberM leaf         = return leaf
  numberM (node a l r) = 
    numberM l   >>= λ l' →
    get         >>= λ n  →
    put (suc n) >> 
    numberM r   >>= λ r' → 
    return (node n l' r')
 
  numM : ∀ {A} → Tree A → Tree ℕ
  numM t = runM (numberM t) 0

-------------------------------
--  Standard library monads  --
-------------------------------

open import Category.Monad
open import Category.Monad.State

St : Set
St = ℕ

M : Set → Set
M = State St

-- to get the monadict operations we need to open the RawMonadState module

open RawMonadState (StateMonadState St)           -- gives us put and get as well as return and _>>=_

-- dominuque devriese's notation with do and then replaced by ⟨ and ⟩ resp.
-- a trick needed because we can't use a mixfix inside a bind
bind : ∀ {A B} → M A → (A → M B) → M B
bind = _>>=_

syntax bind m (\ x → c) = ⟨ x ← m ⟩ c


numberM : ∀ {A} → Tree A → M (Tree ℕ)
numberM leaf = return leaf
numberM (node a l r) =
  ⟨  l' ← numberM l   ⟩
  ⟨  n  ← get         ⟩
  ⟨  _  ← put (suc n) ⟩
  ⟨  r' ← numberM r   ⟩
  return (node n l' r')
 
