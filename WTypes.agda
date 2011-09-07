-- @author : Wojciech Jedynak (wjedynak@gmail.com)
-- @date   : 2011-08-08
-- @tags   : agda ; ML ; W-types
-- @short  : Some experiments with the W-types from Maltin-Lôf's Type Theory.

module WTypes where

open import Data.Empty
open import Data.Nat
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Function
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

data W (A : Set) (B : A → Set) : Set where
  sup : (a : A) → (B a → W A B) → W A B

-----------------------
--  Natural numbers  --
-----------------------

data nat-cs : Set where
  Z S : nat-cs

nat-record : nat-cs → Set
nat-record Z = ⊥
nat-record S = ⊤

nat : Set
nat = W nat-cs nat-record

n-zero : nat
n-zero = sup Z ⊥-elim

n-suc : nat → nat
n-suc n = sup S (λ top → n)

-------------
--  Trees  --
-------------
  
data tree-cs : Set where
  leaf node : tree-cs

data tree-sel : Set where
  left right : tree-sel

tree-record : tree-cs → Set
tree-record leaf = ⊥
tree-record node = tree-sel

tree : Set
tree = W tree-cs tree-record

empty-tree : tree
empty-tree = sup leaf (λ ()) -- ⊥-elim

singleton-tree : tree
singleton-tree = sup node (const empty-tree) where
  sel : tree-sel → tree
  sel left  = empty-tree
  sel right = empty-tree

make-node : tree → tree → tree
make-node l r = sup node sel where
  sel : tree-sel → tree
  sel left  = l
  sel right = r

tryLeft : tree → ⊤ ⊎ tree -- ~ maybe tree
tryLeft (sup leaf sel) = inj₁ tt
tryLeft (sup node sel) = inj₂ (sel left)

---------------------------
--  Induction principle  --
---------------------------

wrec : {A : Set} 
     → {B : A → Set}
     → (C : W A B → Set)
     → (d : (x : A) → (y : B x → W A B) → ((z : B x) → C (y z)) → C (sup x y))
     → (w : W A B)
     → C w
wrec C d (sup a b) = d a b (λ z → wrec C d (b z))

-------------------------------
--  Convertions:  ℕ <-> nat  --
-------------------------------

toℕ : nat → ℕ
toℕ = wrec _ iter module TN where
  iter : (x : nat-cs) 
       → (nat-record x → nat)
       → (nat-record x → ℕ) 
       → ℕ
  iter Z _ rec = 0
  iter S _ rec = 1 + rec tt
                         
fromℕ : ℕ → nat
fromℕ zero    = n-zero
fromℕ (suc n) = n-suc (fromℕ n)
                             
toFrom : ∀ (n : ℕ) → toℕ (fromℕ n) ≡ n
toFrom zero    = refl
toFrom (suc n) = cong suc (toFrom n)

postulate
  funExt : {A : Set} → {B : A → Set} → (f g : (a : A) → B a) 
         → (∀ (x : A) → f x ≡ g x) → f ≡ g

fromTo : ∀ (n : nat) → fromℕ (toℕ n) ≡ n
fromTo (sup Z b) = cong (sup Z) proof where
  proof : ⊥-elim ≡ b
  proof = funExt ⊥-elim b (λ ())

fromTo (sup S b) = cong (sup S) proof where
  lem : (x : ⊤) → fromℕ (wrec (λ w → ℕ) TN.iter (b tt)) ≡ b x
  lem tt = fromTo (b tt)

  proof : (λ x → fromℕ (wrec (λ w → ℕ) TN.iter (b tt))) ≡ b
  proof = funExt (λ a → fromℕ (wrec (λ x → ℕ) TN.iter (b tt))) b lem

-- induction on nats

fromEmpty : (y : ⊥ → nat) → y ≡ ⊥-elim
fromEmpty y = funExt y ⊥-elim (λ ())

fromUnit : (f g : ⊤ → nat) → (f tt ≡ g tt) → f ≡ g
fromUnit f g p = funExt f g (λ tt → p)

natRec : (P : nat → Set)
       → P n-zero
       → ((n : nat) → P n → P (n-suc n))
       → (n : nat) → P n
natRec P zr sc = wrec P iter where
  iter : (x : nat-cs)
       → (y : nat-record x → nat)
       → ((z : nat-record x) → P (y z)) 
       → P (sup x y)
  iter Z y z rewrite fromEmpty y = zr
  iter S y z rewrite fromUnit  y (λ top → y tt) refl = sc (y tt) (z tt)

n-plus : nat → nat → nat
n-plus m n = natRec _ n (const n-suc) m

ex : ℕ
ex = toℕ (n-plus (fromℕ 0) (fromℕ 0))

n-plus2 : nat → nat → nat
n-plus2 n m = wrec (const nat) iter n where
  iter : (x : nat-cs) 
       → (nat-record x → nat) 
       → (nat-record x → nat) 
       → nat
  iter Z y z = m
  iter S y z = n-suc (z tt)

ex2 : ℕ
ex2 = toℕ (n-plus2 (fromℕ 10) (fromℕ 20))


------------------------------
--  Inhabitance of W types  --
------------------------------

inhab : ∀ {A : Set} {B : A → Set} → ∃ (λ (con : A) → ¬ (B con)) → W A B 
inhab {B = B} (con , prf) = sup con (λ (lbl : B con) → ⊥-elim (prf lbl))

not-inhab : ∀ {A : Set} {B : A → Set} → W A B → ¬ (∀ (con : A) → B con)
not-inhab (sup a b) all = not-inhab (b (all a)) all

module Improvements where
  open import Data.Fin
  
  onlyOneFin1 : (a b : Fin 1) -> a ≡ b
  onlyOneFin1 zero zero = refl
  onlyOneFin1 zero (suc ())
  onlyOneFin1 (suc ()) b

  oneEmptyFunc : {Y : Set} (f g : Fin 0 -> Y) -> f ≡ g
  oneEmptyFunc f g = funExt f g (λ ())

  fromEmpty' : (y : ⊥ → nat) → y ≡ ⊥-elim
  fromEmpty' y = funExt y ⊥-elim (λ ())

  altZeroAny' : {P : nat → Set} → P n-zero → (y : ⊥ → nat) → P (sup Z y)
  altZeroAny' a b rewrite fromEmpty b = a

-------------
--  Lists  --
-------------

list-cs : Set
list-cs = ⊤ ⊎ ℕ

list-record : list-cs → Set
list-record (inj₁ top) = ⊥
list-record (inj₂ n)   = ⊤

w-list : Set
w-list = W list-cs list-record

w-nil : w-list
w-nil = sup (inj₁ tt) ⊥-elim

w-cons : ℕ → w-list → w-list
w-cons n l = sup (inj₂ n) (λ x → l)

w-sum : w-list → ℕ
w-sum w = wrec (const ℕ) iter w where
  iter : (x : ⊤ ⊎ ℕ) → (y : list-record x → w-list) → ((z : list-record x) → ℕ) → ℕ
  iter (inj₁ x) y z = 0
  iter (inj₂ n) y z = n + z tt

example : w-list
example = w-cons 1 (w-cons 4 (w-cons 20 w-nil))

-------------
--  Trees  --
-------------

open import Data.Fin hiding (_+_)

w-tree-cs : Set
w-tree-cs = ℕ ⊎ ℕ

w-tree-record : w-tree-cs → Set
w-tree-record (inj₁ n) = ⊥
w-tree-record (inj₂ n) = Fin 2

w-tree : Set
w-tree = W w-tree-cs w-tree-record

w-leaf : ℕ → w-tree
w-leaf n = sup (inj₁ n) ⊥-elim

w-node : ℕ → w-tree → w-tree → w-tree
w-node n l r = sup (inj₂ n) sel module WN where
  sel : Fin 2 → w-tree
  sel zero       = l
  sel (suc zero) = r
  sel (suc (suc ()))

-- an example function using the general recursor

depth : w-tree → ℕ
depth w = wrec (const ℕ) iter w where
  iter : (x : w-tree-cs) 
       → (y : (w-tree-record x) → w-tree) 
       → (z : (a : w-tree-record x) → ℕ)
       → ℕ
  iter (inj₁ _) y z = 0
  iter (inj₂ _) y z = 1 + (z zero ⊔ z (suc zero))

ex-tree : w-tree
ex-tree = w-node 1 (w-node 4 (w-leaf 0) (w-leaf 1))
                   (w-leaf 4)

ex-tree-val : depth ex-tree ≡ 2
ex-tree-val = refl

w-tree-recursor : (C : w-tree → Set) 
                → ((n : ℕ) → C (w-leaf n))
                → ((n : ℕ) → {l r : w-tree}
                   → C l → C r
                   → C (w-node n l r))
                → (w : w-tree)
                → C w
w-tree-recursor C lf nd w = wrec C iter w where
  iter : (x : ℕ ⊎ ℕ) 
         (y : w-tree-record x → w-tree)
         (d : (z : w-tree-record x) → C (y z)) →
         C (sup x y)
  iter (inj₁ n) y d = subst (λ x → C (sup (inj₁ n) x)) 
                            (funExt ⊥-elim y (λ ())) 
                            (lf n)
  iter (inj₂ n) y d = subst (λ x → C (sup (inj₂ n) x)) 
                            (funExt (WN.sel n (y zero) (y (suc zero))) y fin2-eq) 
                            (nd n (d zero) (d (suc zero))) where
       fin2-eq : (x : Fin (suc (suc zero))) →
                   WN.sel n (y zero) (y (suc zero)) x ≡ y x
       fin2-eq zero = refl
       fin2-eq (suc zero) = refl
       fin2-eq (suc (suc ()))
  