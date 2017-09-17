Inductive nat : Type :=
| Z : nat
| S : nat -> nat.

Fixpoint add_nat (m n : nat): nat :=
  match m with
  | Z => n
  | S m => S (add_nat m n)
  end.


Lemma add_1 : forall m n : nat, S (add_nat n m) = add_nat n (S m).
Proof.
  intros.
  induction n.
  simpl.
  reflexivity.
  simpl.
  rewrite -> IHn.
  simpl.
  auto.
Qed.
  

Theorem add_commutes : forall m n : nat, add_nat m n = add_nat n m.
Proof.
  intros.
  induction m.
  simpl.
  induction n.
  simpl.
  reflexivity.
  simpl.
  rewrite <- IHn.
  reflexivity.
  simpl.
  rewrite -> IHm.
  apply add_1.
Qed.


Theorem reflex: forall A : Prop, A -> A.
Proof.
  intros.
  assumption.
Qed.


Theorem and_commutes: forall A B: Prop, A /\ B -> B /\ A.
Proof.
  intros.
  elim H.
  split.
  assumption.
  assumption.
Qed.

Theorem and_intro: forall A B: Prop, A -> B -> A /\ B.
Proof.
  intros.
  split; auto.
Qed.

Inductive List (A : Type): Type :=
| Nil : List A
| Cons : A -> List A -> List A.

(* Why is this prodicing a function type? *)
Inductive Vec (A : Type): nat -> Type :=
| VNil : Vec A Z
| VCons : forall n : nat, A -> Vec A n -> Vec A (S n).

Compute 1.

Lemma tt: forall a b: nat, add_nat a (S b) = S (add_nat a b).
Proof.
  intros a b.
  rewrite -> add_commutes.
  simpl.
  rewrite -> add_commutes.
  reflexivity.
Qed.  



Theorem add_assoc_1 : forall a b c: nat, S (add_nat b (add_nat a c)) = S (add_nat a (add_nat b c)).
Proof.
  intros a b c.
  induction b.
  simpl.
  reflexivity.
  simpl.
  rewrite -> IHb.
  symmetry.
  assert ( H : add_nat a (S (add_nat b c)) = S (add_nat a (add_nat b c)) ).
  apply tt.
  rewrite -> H.
  reflexivity.
Qed.
  


Theorem add_assoc : forall a b c: nat,  add_nat (add_nat a b) c = add_nat a (add_nat b c).
Proof.
  intros a b c.
  symmetry.
  induction a.
  simpl.
  reflexivity.
  simpl.
  rewrite -> IHa.
  reflexivity.
Qed.

Theorem demorgan1 : forall A B : Prop, (~ A) \/ (~ B) -> ~ (A /\ B).
Proof.
  intuition eauto.
Qed.

Axiom axiom_of_choice: forall P: Prop, P \/ (~ P) <-> True.
  

Axiom aa: forall x: Type, forall P : Type -> Prop, (P x) \/ (~ (P x)) <-> True.

Theorem absorption: forall P Q: Prop, (P \/ (P /\ Q)) <-> P.
Proof.
  intros P Q.
  split.
  intros H.
  elim H.
  intros H0.
  assumption.
  intros H0.
  elim H0.
  intros H1 H2.
  assumption.
  intros H.
  left.
  assumption.
Qed.

(* Multiplication *)
Fixpoint mult (m n: nat) :=
  match m with
  | Z => Z
  | (S m) => add_nat n (mult m n)
  end.


  
Lemma lem_mul1: forall a b: nat, add_nat b (mult b a) = mult b (S a).
Proof.
  intros a b.
  simpl.
  induction b.
  simpl.
  reflexivity.
  simpl.
  rewrite <- IHb.
  apply add_assoc_1.
Qed.
  
Theorem mult_comm: forall a b: nat, mult a b = mult b a.
Proof.
  intros a b.
  induction a.
  simpl.
  induction b; simpl; auto.
  simpl.
  rewrite -> IHa.
  apply lem_mul1.
Qed.


Lemma tt1: forall m n : nat, mult m (S n) = add_nat m (mult n m).
Proof.
  intros m n.
  simpl.
  induction m; simpl; auto.
  assert (Z = mult n Z).
  rewrite <- mult_comm; simpl; auto.
  assumption.
  rewrite -> IHm.
  symmetry.
  rewrite -> mult_comm.
  simpl.
  rewrite <- mult_comm.
  apply add_assoc_1.
Qed.


Lemma tty: forall a b m n:nat, add_nat (add_nat a m) (add_nat b n)
                        = add_nat (add_nat a b) (add_nat m n).
Proof.
  intros a b m n.
  rewrite -> add_assoc.
  assert (H : (add_nat m (add_nat b n)) = (add_nat (add_nat b n) m)).
  rewrite -> add_commutes.
  reflexivity.
  rewrite -> H.
  clear H.
  assert (H : (add_nat (add_nat b n) m) = (add_nat b (add_nat n m))).
  rewrite -> add_assoc.
  reflexivity.
  rewrite -> H.
  clear H.
  rewrite <- add_assoc.
  assert (H : (add_nat n m) = (add_nat m n)).
  rewrite <- add_commutes.
  reflexivity.
  rewrite -> H.
  reflexivity.
Qed.
  
Theorem mul_assoc: forall a b c:nat, mult a (add_nat b c) = add_nat (mult a b) (mult a c).
Proof.
  intros a b c.
  induction a; simpl; auto.
  rewrite -> IHa.
  symmetry.
  rewrite <- tt1; rewrite <- mult_comm.
  rewrite <- add_commutes.
  rewrite <- tt1; rewrite <- mult_comm.
  simpl.
  rewrite <- add_commutes.
  apply tty.
Qed.

Theorem nat_cong: forall x y: nat, forall (f : nat -> nat), (x = y) -> (f x) = (f y).
Proof.
  intros x y f H.
  rewrite H.
  reflexivity.
Qed.

Fixpoint geq (x y : nat) : Prop :=
                  match x with
                  | Z => True
                  | S x => geq x y
                  end.


Theorem geq_trans: forall x y z: nat, geq x y -> geq y z -> geq x z.
Proof.
  intros x y z H H0.
  induction x; simpl; auto.
Qed.
