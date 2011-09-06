{-
  @author: Wojciech Jedynak (wjedynak@gmail.com)
-}

{-# OPTIONS --universe-polymorphism #-}

module Records where

-- symulacja (nie-zaleznego) rekordu za pomoca zaleznego produktu

open import Data.Nat hiding (_⊔_)
open import Data.Bool
open import Data.Unit
open import Data.Fin
open import Data.Vec
open import Function
open import Level

module First where

  data Label : Set where
    l-nat l-bool l-unit : Label

  B : Label -> Set
  B l-nat  = ℕ
  B l-bool = Bool
  B l-unit = ⊤

  Rec : Set
  Rec = (l : Label) → B l

  buildRecord : ℕ → Bool → ⊤ → Rec
  buildRecord n b t = rec where
    rec : Rec
    rec l-nat  = n
    rec l-bool = b
    rec l-unit = t
  
  -- przykladowy rekord

  ex : Rec
  ex = buildRecord 1 true tt

  ex2 : Rec
  ex2 = buildRecord (ex l-nat) (ex l-bool) (ex l-unit)
  

-- jeszcze raz to samo, ale na samych finach

module Second where

  Label : Set
  Label = Fin 3

  data U : Set where
    nat bool unit : U

  set : U → Set
  set nat  = ℕ
  set bool = Bool
  set unit = ⊤

  label-case : (C : Label → Set) → (C zero) → (C (suc zero)) → (C (suc (suc zero))) → (l : Label) → C l
  label-case C z s ss zero             = z
  label-case C z s ss (suc zero)       = s
  label-case C z s ss (suc (suc zero)) = ss
  label-case C z s ss (suc (suc (suc ())))

  B : Label → Set
  B l = set (label-case (λ x → U) nat bool unit l)

  Rec : Set 
  Rec = (l : Label) → B l

  buildRecord : ℕ → Bool → ⊤ → Rec
  buildRecord = label-case B
                -- λ n b t l → label-case (λ x → B x) n b t l

module Third where
  -- jeszcze bardziej konserwatywne

  Label : Set
  Label = Fin 3

  U : Set
  U = Fin 3   -- nat , bool , unit

  -- rekursor dla Fin 3

  fin3-rec : (C : Fin 3 → Set) → (C zero) → (C (suc zero)) → (C (suc (suc zero))) → (l : Fin 3) → C l
  fin3-rec C z s ss zero             = z
  fin3-rec C z s ss (suc zero)       = s
  fin3-rec C z s ss (suc (suc zero)) = ss
  fin3-rec C z s ss (suc (suc (suc ())))

  fin3-rec1 : (C : Fin 3 → Set₁) → (C zero) → (C (suc zero)) → (C (suc (suc zero))) → (l : Fin 3) → C l
  fin3-rec1 C z s ss zero             = z
  fin3-rec1 C z s ss (suc zero)       = s
  fin3-rec1 C z s ss (suc (suc zero)) = ss
  fin3-rec1 C z s ss (suc (suc (suc ())))

  set : U → Set
  set = fin3-rec1 (λ x → Set) ℕ Bool ⊤

  B : Label → Set
  B l = set (fin3-rec (λ x → U) zero (suc zero) (suc (suc zero)) l)

  Rec : Set
  Rec = (l : Label) → B l

  buildRecord : ℕ → Bool → ⊤ → Rec
  buildRecord = fin3-rec B

  ex : Rec
  ex = buildRecord 1 false tt

  n : ℕ
  n = ex zero

------------------------------------------------------
--  How can we build a general recursor for Fin n?  --
------------------------------------------------------

-- buildRecusor : (n : ℕ) → (C : Fin n → Set) → ...

at-all-values : {n : ℕ} → (C : Fin n → Set) → Vec Set n
at-all-values C = map C (tabulate id)

_^_⟶_ : ∀ {a} (A : Set a) → (n : ℕ) → (B : Set a) → Set a
A ^ zero  ⟶ B = B
A ^ suc n ⟶ B = A → (A ^ n ⟶ B) 

curry : ∀ {a} → {A : Set a} → (n : ℕ) → {B : Set a} → (Vec A n → B) → (A ^ n ⟶ B)
curry zero    f = f []
curry (suc n) f = λ a → curry n (λ v_n → f (a ∷ v_n))

recursor : {n : ℕ} → {C : Set} → (fin : Fin n) → (C ^ n ⟶ C)
recursor {n} f = curry n (lookup f)

{-

recursor : {n : ℕ} → (C : Fin n → Set) → (fin : Fin n) → (ℕ ^ n ⟶ C fin)
recursor {n} C = {!!}
-}