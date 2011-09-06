{-
  @author: Wojciech Jedynak (wjedynak@gmail.com)
-}
module AxiomOfChoice where

open import Data.Product
open import Function

choice : {A : Set} 
       → {B : A → Set}
       → {C : (a : A) → B a → Set}
       → (∀ (x : A) → Σ[ y ∶ B x ](C x y))
       → Σ[ f ∶ ((x : A) → B x)](∀ (x : A) → (C x (f x)))
choice g = proj₁ ∘ g , proj₂ ∘ g 

