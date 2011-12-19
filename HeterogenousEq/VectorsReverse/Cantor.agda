{-# OPTIONS  --injective-type-constructors #-}

module Cantor where
 
  data Empty : Set where
 
  data One : Set where
    one : One
 
  data coprod (A : Set1) (B : Set1) : Set1 where
    inl : ∀ (a : A) -> coprod A B
    inr : ∀ (b : B) -> coprod A B 
 
  postulate exmid : ∀ (A : Set1) -> coprod A (A -> Empty)
 
  data Eq1 {A : Set1} (x : A) : A -> Set1 where
    refleq1 : Eq1 x x
 
  cast : ∀ { A B } -> Eq1 A B -> A -> B
  cast refleq1 a = a
 
  Eq1cong : ∀ {f g : Set -> Set} a -> Eq1 f g -> Eq1 (f a) (g a)
  Eq1cong a refleq1 = refleq1
 
  Eq1sym : ∀ {A : Set1} { x y : A } -> Eq1 x y -> Eq1 y x
  Eq1sym refleq1 = refleq1
 
  Eq1trans : ∀ {A : Set1} { x y z : A } -> Eq1 x y -> Eq1 y z -> Eq1 x z
  Eq1trans refleq1 refleq1 = refleq1
 
  data I : (Set -> Set) -> Set where
 
  Iinj : ∀ { x y : Set -> Set } -> Eq1 (I x) (I y) -> Eq1 x y 
  Iinj refleq1 = refleq1
 
  data invimageI (a : Set) : Set1 where
    invelmtI : forall x -> (Eq1 (I x) a) -> invimageI a
 
  J : Set -> (Set -> Set)
  J a with exmid (invimageI a)
  J a | inl (invelmtI x y) = x
  J a | inr b = λ x → Empty
 
  data invimageJ (x : Set -> Set) : Set1 where
    invelmtJ : forall a -> (Eq1 (J a) x) -> invimageJ x
 
  IJIeqI : ∀ x -> Eq1 (I (J (I x))) (I x)
  IJIeqI x with exmid (invimageI (I x))
  IJIeqI x | inl (invelmtI x' y) = y
  IJIeqI x | inr b with b (invelmtI x refleq1)
  IJIeqI x | inr b | ()
 
  J_srj : ∀ (x : Set -> Set) -> invimageJ x
  J_srj x = invelmtJ (I x) (Iinj (IJIeqI x))
 
  cantor : Set -> Set
  cantor a with exmid (Eq1 (J a a) Empty)
  cantor a | inl a' = One
  cantor a | inr b = Empty
 
  OneNeqEmpty : Eq1 One Empty -> Empty
  OneNeqEmpty p = cast p one
 
  cantorone : ∀ a -> Eq1 (J a a) Empty -> Eq1 (cantor a) One 
  cantorone a p with exmid (Eq1 (J a a) Empty)
  cantorone a p | inl a' = refleq1
  cantorone a p | inr b with b p
  cantorone a p | inr b | ()
 
  cantorempty : ∀ a -> (Eq1 (J a a) Empty -> Empty) -> Eq1 (cantor a) Empty
  cantorempty a p with exmid (Eq1 (J a a) Empty)
  cantorempty a p | inl a' with p a'
  cantorempty a p | inl a' | ()
  cantorempty a p | inr b = refleq1
 
  cantorcase : ∀ a -> Eq1 cantor (J a) -> Empty
  cantorcase a pf with exmid (Eq1 (J a a) Empty)
  cantorcase a pf | inl a' = OneNeqEmpty (Eq1trans (Eq1trans (Eq1sym (cantorone a a')) (Eq1cong a pf)) a')
  cantorcase a pf | inr b = b (Eq1trans (Eq1sym (Eq1cong a pf)) (cantorempty a b))
 
  absurd : Empty
  absurd with (J_srj cantor)
  absurd | invelmtJ a y = cantorcase a (Eq1sym y)
