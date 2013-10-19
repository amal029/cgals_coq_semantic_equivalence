Module naturals.
Inductive nat :Type :=
| O 
| S : nat -> nat.


Fixpoint mplus (v v1:nat) : nat :=
  match v with
    | O => v1
    | S x => S(mplus x v1)
  end.
    

Fixpoint neq (v v1:nat) : Prop :=
  match v,v1 with
    | S x , S y => neq x y
    | O, O => True
    | O, S _ => False
    | S _, O => False
  end.
    

Example neqs: forall (v1:nat), v1 = v1.
Proof.
  reflexivity.
Qed.

Notation "x + y" := (mplus x y)
                       (at level 50, left associativity)
                       : nat_scope.
(* Notation "x - y" := (mminus x y) *)
(*                        (at level 50, left associativity) *)
(*                        : nat_scope. *)
(* Notation "x * y" := (mmult x y) *)
(*                        (at level 40, left associativity) *)
(*                        : nat_scope. *)

Axiom paeno_add_axiom: forall (a b:nat), a + S b = S ( a+ b).

Lemma plus_id_O: forall (n:nat),  n = O + n.
Proof.
  intros n.
  reflexivity.
Qed.  

Lemma cmplus: forall (n :nat), n = n + O.
Proof.
  intros n.
  induction n.
  trivial.
  simpl.
  rewrite <- IHn.
  reflexivity.
 Qed.


Theorem associative_add: forall (n m:nat), n + m = m + n.
Proof.
  intros n m.
  induction m.
  induction n.
  reflexivity.
  rewrite <- plus_id_O.
  rewrite <- cmplus.
  reflexivity.
  simpl.
  rewrite <- IHm.
  rewrite -> paeno_add_axiom.
  reflexivity.
 Qed.

End naturals.
