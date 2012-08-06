{-
  @author: Wojciech Jedynak (wjedynak@gmail.com)
-}
module CPS where

open import Data.Nat
open import Data.Fin
open import Data.Fin.Props
open import Data.Bool
open import Data.Unit using (⊤; tt)
open import Data.Product
open import Data.Empty
open import Function

open import Data.Vec
open import Data.Vec.Utils hiding (_!_)

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import Data.String

open import Terms
open import Denote

----------------------------------
--  Variable lifting in a term  --
----------------------------------

-- renaming of variables according to the given permutation

permutation : ∀ {n t} {Γ Γ' : Ctx n}
            → Γ ≈ Γ'
            → Term Γ  t 
            → Term Γ' t

permutation perm (var i ind) with perm-lookup i perm ind
... | j , eq = var j eq
permutation perm (app t₁ M N) = app t₁ (permutation perm M) (permutation perm N)
permutation perm (abs M)      = abs (permutation (cns perm) M)
permutation perm true         = true
permutation perm false        = false
permutation perm (cond C M N) = cond (permutation perm C) (permutation perm M) (permutation perm N)


-- swapping of the two latest free variable

tswap : ∀ {n t t1 t2} {Γ : Ctx n}
        → Term (t1 ∷ t2 ∷ Γ) t 
        → Term (t2 ∷ t1 ∷ Γ) t
tswap = permutation swp


-- ignoring the closest variable

tlift : ∀ {n t}{Γ : Ctx n}
      → {a : Type}
      → Term Γ       t 
      → Term (a ∷ Γ) t
      
tlift (var i ind)  = var (suc i) ind
tlift (app t₁ M N) = app t₁ (tlift M) (tlift N)
tlift (abs M)      = abs (tswap (tlift M))
tlift true         = true
tlift false        = false
tlift (cond C M N) = cond (tlift C) (tlift M) (tlift N)

---------------------------
--  Operations on types  --
---------------------------

[_%_] : Type → Type → Type
[ B b     % o ] = B b
[ t1 ⇒ t2 % o ] = [ t1 % o ] ⇒ ([ t2 % o ] ⇒ o) ⇒ o

[_%_]' : Type → Type → Type
[ t % o ]' = ([ t % o ] ⇒ o) ⇒ o

-- lifting for contexts

[_%_]c : {n : ℕ} → Ctx n → Type → Ctx n
[ []    % o ]c = ∅
[ t ∷ Γ % o ]c = [ t % o ] ∷ [ Γ % o ]c 

--------------
--  Lemmas  --
--------------

context-map : ∀ {n t o}{Γ : Ctx n}
            → (i : Fin n)
            → Γ ! i ≡ t
            → [ Γ % o ]c ! i ≡ [ t % o ]

context-map {Γ = []} () _
context-map {Γ = x ∷ Γ} zero  refl = refl
context-map {Γ = x ∷ Γ} (suc i) eq = context-map i eq

---------------------------
--  Readability helpers  --
---------------------------

infixl 3 _$$_

_$$_ : ∀ {n t₁ t₂}
      → {Γ : Ctx n}
      → (M : Term Γ (t₁ ⇒ t₂))
      → (N : Term Γ t₁)
      → Term Γ t₂
M $$ N = app _ M N


-- The string is *only* for readability!

infix 2 ƛ_⟶_

ƛ_⟶_ : ∀ {n t₁ t₂}
      → {Γ : Ctx n}
      → String
      → (T : Term (t₁ ∷ Γ) t₂)
      → Term Γ (t₁ ⇒ t₂)

ƛ x ⟶ M = abs M

-- conditional 

infix 2 _??_::_ 

_??_::_  : ∀ {n t} {Γ : Ctx n}
        → Term Γ Boolean
        → Term Γ t
        → Term Γ t
        → Term Γ t

C ?? M :: N = cond C M N

----------------------------
--  Typed CPS conversion  --
----------------------------

cps : ∀ {n t o}{Γ : Ctx n}
    → Term Γ t 
    → Term [ Γ % o ]c [ t % o ]'

-- [ x ] = λ k. k x

cps (var i ind) 
  = ƛ "k" ⟶ k $$ x
  where
    k = var (# 0) refl
    x = var (suc i) (context-map i ind)


-- [ λ x. M ] = λ k. k (λ x. cps M)

cps (abs M)
  = ƛ "k" ⟶ (k $$ (ƛ "x" ⟶ M'))
  where
     k  = var (# 0) refl
     M' = tswap (tlift (cps M))


-- [ M N] = λ k. [M] (λ m. [N] (λ n. m n k))

cps (app t₁ M N)
  = ƛ "k" ⟶ M' $$ (ƛ "m" ⟶ (N' $$ (ƛ "n" ⟶ m $$ n $$ k)))
  -- = abs {- k -} (M' $$ 
  --               (abs {- m -} (N' $$ 
  --                            (abs {- n -} (m $$ n $$ k)))))
  where
    M' = tlift (cps M)
    N' = tlift (tlift (cps N))
    m = var (# 1) refl
    n = var (# 0) refl
    k = var (# 2) refl

cps true 
  = ƛ "k" ⟶ k $$ true 
  where
    k = var (# 0) refl

cps false 
  = ƛ "k" ⟶ k $$ false 
  where
    k = var (# 0) refl


-- [code C M N] = λ k. [C] (λ c → if c then [M] k else [N] k)

cps (cond C M N)    
  = ƛ "k" ⟶  (C'  $$  (ƛ "b" ⟶ (b ?? (M' $$ k) :: (N' $$ k))))
  where
    b = var (# 0) refl
    k = var (# 1) refl
    C' = tlift (cps C)
    M' = tlift (tlift (cps M))
    N' = tlift (tlift (cps N))

---------------------------------------
--  Optimized Typed CPS Converstion  --
---------------------------------------

opt-cps : ∀ {n t o}{Γ : Ctx n}
    → Term Γ t 
    → Term [ Γ % o ]c [ t % o ]'

-- [ x ] = λ k. k x

opt-cps (var i ind) 
  = ƛ "k" ⟶ k $$ x
  where
    k = var (# 0) refl
    x = var (suc i) (context-map i ind)


-- [ λ x. M ] = λ k. k (λ x. opt-cps M)
-- =>
-- [ λ x. M ] = λ k. k (λ x. λ k2. (opt-cps M) (λ a. k2 a))

opt-cps {o = o} (abs M) 
  = ƛ "k" ⟶ (k $$ (ƛ "x" ⟶ ƛ "k2" ⟶ (M' $$ (ƛ "a" ⟶ k2 $$ a))))
  where
     a  = var (# 0) refl
     k2 = var (# 1) refl
     k  = var (# 0) refl
     M' = tlift (tswap (tlift (opt-cps M)))


-- [ M N] = λ k. [M] (λ m. [N] (λ n. m n k))
-- =>
-- [ M N] = λ k. [M] (λ m. [N] (λ n. m n (λ a → k a)))

opt-cps (app t₁ M N)
  = ƛ "k" ⟶ M' $$ (ƛ "m" ⟶ (N' $$ (ƛ "n" ⟶ m $$ n $$ (ƛ "a" ⟶ k $$ a))))
  where
    M' = tlift (opt-cps M)
    N' = tlift (tlift (opt-cps N))
    m = var (# 1) refl
    n = var (# 0) refl
    k = var (# 3) refl
    a = var (# 0) refl

opt-cps true 
  = ƛ "k" ⟶ k $$ true 
  where
    k = var (# 0) refl

opt-cps false 
  = ƛ "k" ⟶ k $$ false 
  where
    k = var (# 0) refl

-- [code C M N] = λ k. [C] (λ c → if c then [M] k else [N] k)

opt-cps (cond C M N)    
  = ƛ "k" ⟶  (C'  $$  (ƛ "b" ⟶ (b ?? (M' $$ k) :: (N' $$ k))))
  where
    b = var (# 0) refl
    k = var (# 1) refl
    C' = tlift (opt-cps C)
    M' = tlift (tlift (opt-cps M))
    N' = tlift (tlift (opt-cps N))


----------------
--  Examples  --
----------------

ex-simple : ∀ o → Term ∅ [ (Boolean ⇒ Boolean) % o ]'
ex-simple o = cps {Γ = ∅} (abs (cond (var (# 0) refl) false true))

ex-simple2 : ∀ o → Term ∅ [ (Boolean ⇒ Boolean) % o ]'
ex-simple2 o = opt-cps {Γ = ∅} (abs (cond (var (# 0) refl) false true))

lemma : ∀ o → ⟦ ex-simple o ⟧ ≡ ⟦ ex-simple2 o ⟧
lemma o = refl
