{-
  @author: Wojciech Jedynak (wjedynak@gmail.com)
-}
module Stages where

open import Data.Nat
open import Data.Product
open import Data.String
open import Function hiding (_$_)

Var  = ℕ
Name = String

infixl 5 _$_

data Term : Set where
  #_  : (v : Name)   → Term
  _$_ : (f a : Term) → Term
  ƛ   : (v : Name)   → (t : Term) → Term

-- let x = t1 @ t2 in y

{-
  x z (y z)
  ==>
  let t1 = x $ z in
    let t2 = y $ z in
      let t3 = t1 @ t2 in 
         return t3
-}

s-body : Term
s-body = x $ z $ (y $ z) where
  x = # "x"
  y = # "y"
  z = # "z"

{-
let x = M $ N in x
==>
let-in M ;
let-in N ;
x ... 
-}

mutual
  data Trivial : Set where
    #_ : Name → Trivial
    ƛ  : Name → Term2 → Trivial
    L  : Var → Trivial                            -- variable bound by let
  
  data ANF : Set where
    Let_:=_$_In_ : Var → Trivial → Trivial → Term2 → ANF

  data Term2 : Set where
    T : Trivial → Term2
    S : ANF     → Term2

-- example

ex : Term2
ex = S (Let a1 := x $ z In (
       S (Let a2 := y $ z In (
         S (Let a3 := (L a1) $ (L a2) In (
           T (L a3))))))) where
   a1 = 1
   a2 = 2
   a3 = 3
   x  = # "x"
   y  = # "y"
   z  = # "z"


-- continuation-based translation algorithm
-- the continuation caries also the first free name
-- in a state monad

flatten : Term → ℕ → (Trivial → ℕ → Term2) → Term2
flatten (# v)   n k = k (# v) n
flatten (ƛ v t) n k = k (ƛ v (flatten t 0 (λ t n → T t))) n
flatten (f $ a) n k = flatten f n (λ t₁ n₁ → 
                        flatten a n₁ (λ t₂ n₂ → 
                          S (Let n₂ := t₁ $ t₂ In 
                            k (L n₂) (1 + n₂))))
                                        
flatten-top : Term → Term2
flatten-top t = flatten t 0 (λ t n → T t)
  

ex1 : Term
ex1 = # "x" $ (# "y" $ # "z")

ex2 : Term
ex2 = (ƛ "x" ((# "x1") $ (# "x2"))) $ (# "y" $ # "z")
