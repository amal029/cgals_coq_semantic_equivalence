Module boolean.
Inductive bool : Type :=
| true
| false.

Definition not v :=
  match v with
    | true => false
    | false => true
  end.


Definition and (v:bool) (v1:bool) :=
  match (v,v1) with
    | (true,_ as s) | (_ as s ,true) => s
    | (_, false) => false
  end.

(* This is proof using a truth table! *)
Theorem assoc_and: forall (a b:bool), (and a b) = (and b a).
Proof.
  intros a b.
  elim a.
  elim b.
  reflexivity.
  reflexivity.
  reflexivity.
Qed.

(* This is proof using a truth table! *)
Definition or (v:bool) (v1:bool) :=
  match (v,v1) with
    | (false,false) => false
    | (false,_ as s ) | (_ as s, false) => s
    | (true,_)  => true
  end.

Theorem assoc_or: forall (a b:bool), (or a b) = (or b a).
Proof.
  intros a b.
  elim b.
  elim a.
  reflexivity.
  reflexivity.
  reflexivity.
Qed.


Lemma or_taut: forall b: bool, (or b (not b)) = true.
Proof.
  intros b.
  elim b.
  reflexivity.
  reflexivity.
Qed.

Theorem andb_true_elim1: forall (b c: bool), and b c = true -> b = true. 
Proof.
  intros b c H. destruct b.
  reflexivity. rewrite <- H.
  destruct c. reflexivity.
  reflexivity.
  Qed.
End boolean.
