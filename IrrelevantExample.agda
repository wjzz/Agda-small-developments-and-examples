{-
  @author: Wojciech Jedynak (wjedynak@gmail.com)
-}
module IrrelevantExample where

open import Data.List hiding (and)
open import Data.Product hiding (map)
open import Function
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

---------------------------------------
--  The notion of container monoids  --
---------------------------------------

record Monoid (Var : Set) : Set₁ where
--  constructor c-monoid
  field
    M   : Set → Set
    ε   : M Var
    _⊗_ : M Var → M Var → M Var

    -- monoidal laws

    zero-left  : (m : M Var)     → ε ⊗ m ≡ m
    zero-right : (m : M Var)     → m ⊗ ε ≡ m
    assoc      : (a b c : M Var) → (a ⊗ b) ⊗ c ≡ a ⊗ (b ⊗ c)

    -- an injection operation for variables

    ⌜_⌝        : Var → M Var

    -- a homomorphism into lists

    toList     : M Var → List Var
    toList-eps : toList ε ≡ []
    toList-var : (x : Var)     → toList ⌜ x ⌝   ≡ [ x ]
    toList-op  : (l r : M Var) → toList (l ⊗ r) ≡ toList l ++ toList r

-----------------------
--  Monoid examples  --
-----------------------

lem-app-l-nil : ∀ {A : Set}(l : List A) → l ++ [] ≡ l
lem-app-l-nil [] = refl
lem-app-l-nil (x ∷ xs) = cong (λ l → x ∷ l) (lem-app-l-nil xs)

lem-app-assoc : ∀ {A : Set}(l1 l2 l3 : List A) → l1 ++ (l2 ++ l3) ≡ (l1 ++ l2) ++ l3
lem-app-assoc [] l2 l3 = refl
lem-app-assoc (x ∷ xs) l2 l3 = cong (λ l → x ∷ l) (lem-app-assoc xs l2 l3)


listMonoid : (Var : Set) → Monoid Var
listMonoid Var = record { M          = List;
                          ε          = [];
                          _⊗_        = _++_;
                          zero-left  = λ m → refl;
                          zero-right = lem-app-l-nil;
                          assoc      = λ a b c → sym (lem-app-assoc a b c);
                          ⌜_⌝        = λ x → x ∷ [];
                          toList     = λ x → x;
                          toList-eps = refl;
                          toList-var = λ x → refl;
                          toList-op  = λ l r → refl 
                        }    

functionMonoid : (Var : Set) → Monoid Var
functionMonoid Var = record {
                       M          = λ V → List V → List V;
                       ε          = λ x → x;
                       _⊗_        = _∘′_;
                       zero-left  = λ m → refl;
                       zero-right = λ m → refl;
                       assoc      = λ a b c → refl;
                       ⌜_⌝        = λ x c → x ∷ c;
                       toList     = λ xs → xs [];
                       toList-eps = refl;
                       toList-var = λ x → refl;
                       toList-op  = {!!} } -- I don't see how to prove it. The assumptions are too weak.

module StrongFunctionMonoidBuilder (Var : Set) where

  -- sfMonoid : Set → Set
  -- sfMonoid V = Σ[ fl ∶ (List V → List V) ]((l : List V) → fl l ≡ fl [] ++ l) 
  
  record sfMonoid (V : Set) : Set where
    constructor _,_
    field
      fl : List V → List V
      .p : (l : List V) → fl l ≡ fl [] ++ l
      -- this proof is only required to limit possible fl's, 
      -- we don't want to reason about it, so we mark it as irrelevant

  identity : sfMonoid Var
  identity = id , (λ l → refl)

  compose : sfMonoid Var → sfMonoid Var → sfMonoid Var
  compose (l1 , p1) (l2 , p2) = (l1 ∘ l2) , (λ l → 
    begin
       l1 (l2 l)                ≡⟨ p1 (l2 l) ⟩
       l1 [] ++ (l2 l)          ≡⟨ cong (_++_ (l1 [])) (p2 l) ⟩
       l1 [] ++ (l2 [] ++ l)    ≡⟨ lem-app-assoc (l1 []) (l2 []) l ⟩
      (l1 [] ++ l2 []) ++ l     ≡⟨ sym (cong (λ x → x ++ l) (p1 (l2 []))) ⟩
      l1 (l2 []) ++ l
    ∎) where open ≡-Reasoning

  inject : Var → sfMonoid Var
  inject v = (λ l → v ∷ l) , λ l → refl

  toList : sfMonoid Var → List Var
  toList (l , p) = l []

  toListHomomorphic : (l r : sfMonoid Var) → toList (compose l r) ≡ toList l ++ toList r
  toListHomomorphic (l , pl) (r , pr) = pl (r [])

  strongFunctionMonoid : Monoid Var
  strongFunctionMonoid = 
    record { M          = sfMonoid
           ; ε          = identity
           ; _⊗_        = compose
           ; zero-left  = λ l → refl
           ; zero-right = λ l → refl
           ; assoc      = λ a b c → refl
           ; ⌜_⌝        = inject
           ; toList     = toList
           ; toList-eps = refl
           ; toList-var = λ x → refl
           ; toList-op  = toListHomomorphic 
           } 

