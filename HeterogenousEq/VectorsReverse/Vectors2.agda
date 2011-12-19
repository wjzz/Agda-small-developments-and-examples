{-
  @author: Wojciech Jedynak (wjedynak@gmail.com)
-}
module Vectors2 where

open import Data.Nat
open import Data.Vec
open import Relation.Binary.PropositionalEquality

lemma : ∀ n → suc n ≡ n + 1
lemma zero = refl
lemma (suc n) rewrite lemma n = refl

-- the main function
-- The use of rewrite gives us a lot of pain...

rev : {A : Set}{n : ℕ} → Vec A n → Vec A n
rev [] = []
rev {n = suc n} (x ∷ xs) rewrite lemma n = rev xs ++ [ x ]

-- the notion of heterogeneous equality

coerce : {A : Set}{n m : ℕ} → n ≡ m → Vec A n → Vec A m
coerce refl a = a

infix 4 _≈_

data _≈_ {A : Set}{n : ℕ}(v : Vec A n) : {m : ℕ} → Vec A m → Set where
  refl : {m : ℕ} → (eq : n ≡ m) → v ≈ coerce eq v

-- properties of the equality

symm : ∀ {A n m} {v1 : Vec A n}{v2 : Vec A m} → v1 ≈ v2 → v2 ≈ v1
symm (refl refl) = refl refl

trns : ∀ {A n m k}{v1 : Vec A n}{v2 : Vec A m}{v3 : Vec A k} → v1 ≈ v2 → v2 ≈ v3 → v1 ≈ v3
trns (refl refl) (refl refl) = refl refl

elim : ∀ {A n} {v1 v2 : Vec A n} → v1 ≈ v2 → v1 ≡ v2
elim (refl refl) = refl

-- some helpers - specialized uses of cong

cong-cons : ∀ {A n m} x → {v1 : Vec A n}{v2 : Vec A m} → v1 ≈ v2 → x ∷ v1 ≈ x ∷ v2
cong-cons x (refl refl) = refl refl

cong-app : ∀ {A n m k}{v1 : Vec A n}{v2 : Vec A m}{v : Vec A k}
           → v1 ≈ v2 
           → v1 ++ v ≈ v2 ++ v
cong-app (refl refl) = refl refl

cong-rev : ∀ {A n m}{v1 : Vec A n}{v2 : Vec A m} → v1 ≈ v2 → rev v1 ≈ rev v2
cong-rev (refl refl) = refl refl

-- a few lemmas

lemma-nil : ∀ {A n} → (v : Vec A n) → v ≈ v ++ []
lemma-nil []       = refl refl
lemma-nil (x ∷ xs) = cong-cons x (lemma-nil xs)

app-assoc : ∀ {A n m k} (v1 : Vec A n)(v2 : Vec A m)(v3 : Vec A k) 
          → (v1 ++ v2) ++ v3 ≈ v1 ++ (v2 ++ v3) 
app-assoc []       v2 v3 = refl refl
app-assoc (x ∷ v1) v2 v3 = cong-cons x (app-assoc v1 v2 v3)

rev-app : ∀ {A n m} (v1 : Vec A n) (v2 : Vec A m) → rev (v1 ++ v2) ≈ rev v2 ++ rev v1
rev-app [] v2 = lemma-nil (rev v2)
rev-app {n = suc n}{m = m} (x ∷ v1) v2 rewrite lemma (n + m) | lemma n = 
  trns (cong-app (rev-app v1 v2)) (app-assoc (rev v2) (rev v1) (x ∷ []))

-- the main theorem 

rev-involutive-hlp : {A : Set} {n : ℕ} → (v : Vec A n) → rev (rev v) ≈ v
rev-involutive-hlp [] = refl refl
rev-involutive-hlp {n = suc n} (x ∷ xs) = 
  trns (cong-rev lemma2) 
 (trns (rev-app (rev xs) [ x ]) 
       (cong-cons x (rev-involutive-hlp xs)))
 where
  lemma2 : rev (x ∷ xs) ≈ rev xs ++ [ x ]
  lemma2 rewrite lemma n = refl refl

{- rev (rev (x ∷ xs))      ≈ definition + rewrite magic
   rev (rev (xs ++ [x]))   ≈ rev-app lemma
   rev [x] ++ rev (rev xs) ≈ definition
   x ∷ rev (rev xs)        ≈ cons congruence + ind. hyp.
   x ∷ xs
-}


rev-involutive : {A : Set} {n : ℕ} → (v : Vec A n) → rev (rev v) ≡ v
rev-involutive v = elim (rev-involutive-hlp v) 
