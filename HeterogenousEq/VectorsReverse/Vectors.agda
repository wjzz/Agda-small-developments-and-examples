{-# OPTIONS  --injective-type-constructors #-}

{-
  @author: Wojciech Jedynak (wjedynak@gmail.com)
-}
module Vectors where

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

coerce : {A B : Set} → A ≡ B → A → B
coerce refl a = a

infix 4 _≈_

data _≈_ {A B : Set} : A → B → Set₁ where
  refl : (eq : A ≡ B) → (a : A) → a ≈ coerce eq a

-- properties of equality

symm : ∀ {A} {B} {a : A}{b : B} → a ≈ b → b ≈ a
symm (refl refl a) = refl refl a

trns : ∀ {A} {B} {C} → {a : A}{b : B}{c : C} → a ≈ b → b ≈ c → a ≈ c
trns (refl refl a) (refl refl .a) = refl refl a

elim : ∀ {A}{a b : A} → a ≈ b → a ≡ b
elim {A} {a} (refl refl .a) = refl

-- congruences

vec-cong : {A : Set}{n m : ℕ}(x : A)(v1 : Vec A n)(v2 : Vec A m) → v1 ≈ v2 → x ∷ v1 ≈ x ∷ v2
vec-cong x v1 .v1 (refl refl .v1) = refl refl (x ∷ v1)

vec-cong-2 : {A : Set}{n m k : ℕ} (v1 : Vec A n)(v2 : Vec A m)(v : Vec A k) 
           → v1 ≈ v2 
           → v1 ++ v ≈ v2 ++ v
vec-cong-2 v1 .v1 v (refl refl .v1) = refl refl (v1 ++ v)

vec-cong-rev : {A : Set}{n m : ℕ}(v1 : Vec A n)(v2 : Vec A m) → v1 ≈ v2 → rev v1 ≈ rev v2
vec-cong-rev v1 .v1 (refl refl .v1) = refl refl (rev v1) 

-- main lemmas

lemma-nil : {A : Set}{n : ℕ} → (v : Vec A n) → v ≈ v ++ []
lemma-nil []       = refl refl []
lemma-nil (x ∷ xs) = vec-cong x xs (xs ++ []) (lemma-nil xs)

app-assoc : {A : Set}{n m k : ℕ} (v1 : Vec A n)(v2 : Vec A m)(v3 : Vec A k) → (v1 ++ v2) ++ v3 ≈ v1 ++ (v2 ++ v3) 
app-assoc []       v2 v3 = refl refl (v2 ++ v3)
app-assoc (x ∷ xs) v2 v3 = vec-cong x _ _ (app-assoc xs v2 v3)

rev-app : {A : Set}{n m : ℕ} (v1 : Vec A n) (v2 : Vec A m) → rev (v1 ++ v2) ≈ rev v2 ++ rev v1
rev-app [] v2 = lemma-nil (rev v2)
rev-app {n = suc n}{m = m} (x ∷ xs) v2 rewrite lemma (n + m) | lemma n with rev-app xs v2
... | rec = trns (vec-cong-2 (rev (xs ++ v2)) (rev v2 ++ rev xs) [ x ] rec) (app-assoc (rev v2) (rev xs) [ x ])

rev-involutive-hlp : {A : Set} {n : ℕ} → (v : Vec A n) → rev (rev v) ≈ v
rev-involutive-hlp [] = refl refl []
rev-involutive-hlp {n = suc n} (x ∷ xs) = 
  trns (vec-cong-rev _ _ lemma2) 
 (trns (rev-app (rev xs) [ x ]) 
       (vec-cong x (rev (rev xs)) xs (rev-involutive-hlp xs)))
 where
  lemma2 : rev (x ∷ xs) ≈ rev xs ++ [ x ]
  lemma2 rewrite lemma n = refl refl (rev xs ++ x ∷ [])

{- rev (rev (x ∷ xs))      ≈ definition + rewrite magic
   rev (rev (xs ++ [x]))   ≈ rev-app lemma
   rev [x] ++ rev (rev xs) ≈ definition
   x ∷ rev (rev xs)        ≈ cons congruence + ind. hyp.
   x ∷ xs
-}


rev-involutive : {A : Set} {n : ℕ} → (v : Vec A n) → rev (rev v) ≡ v
rev-involutive v = elim (rev-involutive-hlp v)
