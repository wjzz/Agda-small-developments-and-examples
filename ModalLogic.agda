module ModalLogic where

open import Data.Nat
open import Data.Fin

open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

----------------
--  Formulas  --
----------------

PropVar = ℕ

data Formula : Set where
  ⟨_⟩ : (A : PropVar) → Formula 
  ⊤   : Formula
  ⊥   : Formula
  _∧_ : (p q : Formula) → Formula
  _∨_ : (p q : Formula) → Formula
  _⇒_ : (p q : Formula) → Formula
  ◻_  : (f : Formula) → Formula
--  ◇_   : (f : Formula) → Formula

-- example variables

abstract
  A : Formula
  A = ⟨ 0 ⟩
  B : Formula
  B = ⟨ 1 ⟩
  C : Formula
  C = ⟨ 2 ⟩

------------------
--  Judgements  --
------------------

infixl 7 _∨_
infixl 7 _∧_
infixr 7 _⇒_
infixl 6 _,_
infix 5 _∈_
infix 3 _,,_⊢_
infix 3 ⊢_

-- contexts

data Ctx : Set where
  ∅ : Ctx
  _,_ : (Γ : Ctx) → (α : Formula) → Ctx

-- de Bruijin indices

data _∈_ : Formula → Ctx → Set where
  Z : ∀ {α Γ}   → α ∈ Γ , α
  S : ∀ {α β Γ} → α ∈ Γ      → α ∈ Γ , β


data _,,_⊢_ : Ctx → Ctx → Formula → Set where

  true-lookup : ∀ {Γ Δ φ}
              → φ ∈ Γ 
              → Δ ,, Γ ⊢ φ

  valid-lookup : ∀ {Γ Δ φ}
               → φ ∈ Δ 
               → Δ ,, Γ ⊢ φ

  -- modal operator ◻
  
  sq-intro : ∀ {Γ Δ φ}
           → Δ ,, ∅ ⊢ φ
           → Δ ,, Γ ⊢ ◻ φ

  sq-elim : ∀ {Γ Δ φ C}
          → Δ ,, Γ ⊢ ◻ φ
          → (Δ , φ) ,, Γ ⊢ C
          → Δ ,, Γ ⊢ C
  
  -- top ⊤

  top-intro : ∀ {Γ Δ}
            → Δ ,, Γ ⊢ ⊤

  -- bottom ⊥

  bot-elim : ∀ {Γ Δ C}
           → Δ ,, Γ ⊢ ⊥
           → Δ ,, Γ ⊢ C
 

  -- conjunction ∧

  and-intro : ∀ {Γ Δ P Q}
            → Δ ,, Γ ⊢ P
            → Δ ,, Γ ⊢ Q
            → Δ ,, Γ ⊢ P ∧ Q

  and-elim1 : ∀ {Γ Δ P Q}
            → Δ ,, Γ ⊢ P ∧ Q
            → Δ ,, Γ ⊢ P

  and-elim2 : ∀ {Γ Δ P Q}
            → Δ ,, Γ ⊢ P ∧ Q
            → Δ ,, Γ ⊢ Q

  -- implication ⇒

  imp-intro : ∀ {Γ Δ P Q} 
            → Δ ,, (Γ , P) ⊢ Q
            → Δ ,, Γ ⊢ P ⇒ Q

  imp-elim : ∀ {Γ Δ P Q} 
           → Δ ,, Γ ⊢ P ⇒ Q
           → Δ ,, Γ ⊢ P
           → Δ ,, Γ ⊢ Q

  -- disjunction ∨

  disj-intro1 : ∀ {Γ Δ P Q} 
              → Δ ,, Γ ⊢ P
              → Δ ,, Γ ⊢ P ∨ Q

  disj-intro2 : ∀ {Γ Δ P Q} 
              → Δ ,, Γ ⊢ Q
              → Δ ,, Γ ⊢ P ∨ Q

  disj-elim : ∀ {Γ Δ P Q C} 
            → Δ ,, Γ ⊢ P ∨ Q
            → Δ ,, (Γ , P) ⊢ C
            → Δ ,, (Γ , Q) ⊢ C
            → Δ ,, Γ ⊢ C


-- notation

⊢_ : Formula → Set
⊢ F = ∅ ,, ∅ ⊢ F

------------------------------
--  Substitution principle  --
------------------------------

substitution : ∀ {Δ Γ A C}
             → Δ ,, ∅ ⊢ A
             → (Δ , A) ,, Γ ⊢ C
             → Δ ,, Γ ⊢ C 

substitution derA derB = sq-elim (sq-intro derA) derB


---------------------------
--  Example derivations  --
---------------------------

-- this can't be inverted

unbox : ∀ A → ⊢ ◻ A ⇒ A
unbox A = imp-intro (sq-elim (true-lookup Z) 
                             (valid-lookup Z))

-- ◻ A ↔ ◻ ◻ A

double-box : ⊢ ◻ A ⇒ ◻ ◻ A
double-box = imp-intro (sq-elim (true-lookup Z) 
                                (sq-intro (sq-intro (valid-lookup Z))))

double-box-inv : ⊢ ◻ ◻ A ⇒ ◻ A
double-box-inv = unbox (◻ A)


-- ◻ and ⇒

fmap : ⊢ ◻ (A ⇒ B) ⇒ ◻ A ⇒ ◻ B
fmap = imp-intro (imp-intro (sq-elim (true-lookup Z) 
                            (sq-elim (true-lookup (S Z)) 
                            (sq-intro (imp-elim (valid-lookup Z) 
                                                (valid-lookup (S Z)))))))

fmap-inv : ⊢ (◻ A ⇒ ◻ B) ⇒ ◻ (A ⇒ B)
fmap-inv = imp-intro {!!}                         -- no way!

-- ◻ and ∧


equiv-and-l : ⊢ ◻ (A ∧ B) ⇒ (◻ A ∧ ◻ B)
equiv-and-l = imp-intro (and-intro (sq-elim (true-lookup Z) 
                                    (sq-intro (and-elim1 (valid-lookup Z))))            
                                   (sq-elim (true-lookup Z) 
                                    (sq-intro (and-elim2 (valid-lookup Z)))))

equiv-and-r-lemma : ⊢ ◻ (◻ A ∧ ◻ B) ⇒ ◻ (A ∧ B)
equiv-and-r-lemma = imp-intro (sq-elim (true-lookup Z) (sq-intro (and-intro
  (sq-elim (and-elim1 (valid-lookup Z)) (valid-lookup Z)) 
  (sq-elim (and-elim2 (valid-lookup Z)) (valid-lookup Z)))))

equiv-and-r-curried : ⊢ ◻ A ⇒ ◻ B ⇒ ◻ (A ∧ B)
equiv-and-r-curried = imp-intro (imp-intro (sq-elim (true-lookup Z) 
                                           (sq-elim (true-lookup (S Z)) 
                                            (sq-intro (and-intro (valid-lookup Z) 
                                                                 (valid-lookup (S Z)))))))

uncurry : ∀ F G H → ⊢ (F ⇒ G ⇒ H) ⇒ ((F ∧ G) ⇒ H)
uncurry F G H = imp-intro (imp-intro (imp-elim (imp-elim (true-lookup (S Z)) 
                          (and-elim1 (true-lookup Z))) (and-elim2 (true-lookup Z))))

equiv-and-r : ⊢ (◻ A ∧ ◻ B) ⇒ ◻ (A ∧ B)
equiv-and-r = imp-elim (uncurry _ _ _) equiv-and-r-curried

equiv-and-r-direct : ⊢ (◻ A ∧ ◻ B) ⇒ ◻ (A ∧ B)
equiv-and-r-direct = imp-intro (sq-elim (and-elim1 (true-lookup Z)) 
                                (sq-elim (and-elim2 (true-lookup Z)) 
                                 (sq-intro (and-intro (valid-lookup (S Z)) 
                                                      (valid-lookup Z)))))


-- ◻ and ∨

equiv-or-l : ⊢ ◻ (A ∨ B) ⇒ (◻ A ∨ ◻ B)
equiv-or-l = imp-intro (sq-elim (true-lookup Z) (disj-elim (valid-lookup Z) (disj-intro1 (sq-intro {!!})) {!!}))
-- we are stuck

equiv-or-r : ⊢ (◻ A ∨ ◻ B) ⇒ ◻ (A ∨ B)
equiv-or-r = imp-intro (disj-elim (true-lookup Z) 
                                  (sq-elim (true-lookup Z) (sq-intro (disj-intro1 (valid-lookup Z)))) 
                                  (sq-elim (true-lookup Z) (sq-intro (disj-intro2 (valid-lookup Z)))))

-- ◻ and ⊥

equiv-bot-l : ⊢ ◻ ⊥ ⇒ ⊥
equiv-bot-l = unbox ⊥

equiv-bot-r : ⊢ ⊥ ⇒ ◻ ⊥
equiv-bot-r = imp-intro (bot-elim (true-lookup Z))


-- other stuff

true : ⊢ ◻ (⊤ ∧ ⊤)
true = sq-intro (and-intro top-intro top-intro)

-- i don't see how to do this one

lemma : ∀ F G → ⊢ (F ⇒ G) ⇒ (◻ F ⇒ ◻ G)
lemma F G = imp-intro (imp-intro {!!})
