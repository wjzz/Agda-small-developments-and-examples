Set Implicit Arguments.

Definition Atom := nat.

Inductive Typ : Set :=
| A : Atom -> Typ
| Arrow : Typ -> Typ -> Typ.

Notation "t1 ==> t2" := (Arrow t1 t2)(right associativity, at level 45).

(* terms *)

Inductive Term : Typ -> Set :=
| K : forall t1 t2, Term (t1 ==> t2 ==> t1)

| S : forall a b c, Term ((a ==> b ==> c) ==> (a ==> b) ==> (a ==> c))

| app : forall a b, Term (a ==> b) -> Term a -> Term b.

Notation "X @ Y" := (app X Y)(left associativity, at level 40).

(* Example *)

Definition I (a : Typ) : Term (a ==> a) :=
  S _ _ _  @ K _ _ @ K _ a.

Print I.

(* head reduction *)

Inductive head_red : forall a, Term a -> Term a -> Prop :=

| hr_K : forall a b, forall (M : Term a)(N : Term b),
         head_red (K _ _ @ M @ N) M

| hr_S : forall a b c, 
          forall (M : Term (a ==> b ==> c))
                 (N : Term (a ==> b))
                 (O : Term a),
                 head_red (S _ _ _ @ M @ N @ O) ((M @ O) @ (N @ O))

| hr_A : forall a b,
          forall (M N : Term (a ==> b))
                 (O   : Term a),
                 head_red M N ->
                 head_red (M @ O) (N @ O)
.

(* normalizable terms *)

Inductive normalizable : forall a, Term a -> Set :=
  
| n_K0 : forall a b,
             normalizable (K a b)

| n_S0 : forall a b c,
             normalizable (S a b c)

| n_K1 : forall a b (M : Term a),
           normalizable M ->
           normalizable (K _ b @ M)
           
| n_S1: forall a b c (M : Term (a ==> b ==> c)),
           normalizable M ->
           normalizable (S _ _ _ @ M)

| n_S2: forall a b c (M : Term (a ==> b ==> c)) (N : Term (a ==> b)),
           normalizable M ->
           normalizable N ->
           normalizable (S _ _ _ @ M @ N)

| n_app : forall a (M N : Term a),
             head_red M N ->
             normalizable N ->
             normalizable M
.

(* computable terms *)

Print Empty_set.

Open Scope type_scope.

Fixpoint computable (t : Typ) : Term t -> Set :=
  match t with
    | A _      => fun M => Empty_set
    | a ==> b  => fun M => normalizable M
                        * (forall (N : Term a), computable N -> computable (M @ N))
      
  end.

Lemma comp2norm : forall t (M : Term t), computable M -> normalizable M.
  intro. induction t; intros. simpl in *; inversion H. unfold computable in *; intuition.
Defined.

Hint Resolve comp2norm.

Print comp2norm.

Hint Constructors Term.
Hint Constructors head_red.
Hint Constructors normalizable.

Lemma red_comp : forall a (M N : Term a),
                   head_red M N ->
                   computable N ->
                   computable M.
  intro. induction a.
  intros; simpl in *; trivial.
  intros.
  unfold computable in *.
  split; intuition eauto.
  fold computable in *.
  eauto.
Defined.

Hint Resolve red_comp.

Print red_comp.

Lemma all_comp : forall a (M : Term a),
                   computable M.
  intros.
  induction M;
  try (simpl ; repeat (intuition eauto)).
  eapply red_comp; eauto. apply b0; auto. 
  unfold computable in IHM1. fold computable in *. intuition.
Defined.

Hint Resolve all_comp.

Theorem all_norm : forall a (M : Term a),
                   normalizable M.
  eauto.
Defined.

Recursive Extraction all_norm.
  

