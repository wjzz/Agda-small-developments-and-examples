-- @author : Wojciech Jedynak (wjedynak@gmail.com)
-- @date   : 2011-08-31
-- @tags   : cps ; arith expr interpreter ; agda
-- @short  : Interpreter for arith exprs in cps and DS.
-- @note   : A trivial interpreter for arithmetical expression with a direct style and cps flavor with proof of equivalence.

module ArithExprEvaluator where

open import Data.Nat renaming (_+_ to _ℕ+_)
open import Function
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

data expr : Set where
  #_  : ℕ    -> expr
  _+_ : expr -> expr -> expr

-- direct style --

eval : expr -> ℕ
eval (# n)     = n
eval (e1 + e2) = eval e1 ℕ+ eval e2

-- cps transformed eval --

evalCPS : ∀ {a : Set} → expr -> (ℕ -> a) -> a
evalCPS (# n)     k = k n
evalCPS (e1 + e2) k = evalCPS e1 (λ n1 ->
                      evalCPS e2 (λ n2 -> 
                      k (n1 ℕ+ n2)))

-- the relationship between eval and evalCPS --

equivalence : ∀ {A : Set} (e : expr) (k : ℕ -> A) 
            → evalCPS e k ≡ k (eval e)
equivalence (# n)     k = 
  refl
equivalence (e1 + e2) k =
  begin 
    evalCPS (e1 + e2) k                                  ≡⟨ refl ⟩ 
    evalCPS e1 (λ x → evalCPS e2 (λ x' → k (x ℕ+ x')))   ≡⟨ equivalence e1 _ ⟩ 
    evalCPS e2 (λ x → k (eval e1 ℕ+ x))                  ≡⟨ equivalence e2 _ ⟩ 
    k (eval e1 ℕ+ eval e2)                               ≡⟨ refl ⟩
    k (eval (e1 + e2))
  ∎

corollary : ∀ {A : Set} (e : expr) 
            → evalCPS e id ≡ eval e
corollary e = equivalence e id
