Module list.

  Require Export naturals.
  Require Export option.

  Inductive list (A:Type) : Type :=
  | Nil : list A
  | Cons : A -> list A -> list A. 

  Fixpoint length (A:Type) (ll:list A) : nat :=
    match ll with
      | Nil => O
      | Cons x x0 => (S O) + length A x0
    end.

  Fixpoint append (A:Type) (l1 l2:list A) :=
    match l1 with
      | Nil => l2
      | Cons x x0 => Cons A x (append A x0 l2)
    end.

  Fixpoint tl (A:Type) (l: list A) :=
    match l with
      | Nil => Nil A
      | Cons x x0 => x0
    end.

  Fixpoint hd (A:Type) (l : list A) :=
    match l with
      | Nil => None
      | Cons x x0 => Some x
    end.

  Fixpoint map (A:Type) (f: A -> A) (l : list A) : list A:=
    match l with
      | Nil => Nil A
      | Cons x x0 => Cons A (f x) (map A f x0)
    end.
  
  Fixpoint rev (A:Type) (l : list A) : list A :=
    match l with
      | Nil => Nil A
      | Cons x x0 => append A (rev A x0) (Cons A x (Nil A))
    end.
  
  
  Theorem app_associative : 
    forall (A:Type) (l1 l2 l3: list A), append A (append A l1 l2) l3 = 
                                        append A l1 (append A l2 l3).

  Proof.
    intros A l1 l2 l3.
    induction l1.
    reflexivity.
    simpl.
    rewrite -> IHl1.
    reflexivity.
  Qed.

  Theorem app_length: 
    forall (A:Type) (l1 l2: list A), length A (append A l1 l2) = 
                                     (length A l1) + (length A l2).

  Proof.
    intros A l1 l2.
    induction l1.
    induction l2.
    reflexivity.
    simpl.
    reflexivity.
    simpl.
    rewrite -> IHl1.
    reflexivity.
  Qed.

  Lemma neutral_app1: forall (A:Type) (l : list A), append A (Nil A) l = l.
  Proof.
    intros A l.
    reflexivity.
  Qed.
  Lemma neutral_app: forall (A:Type) (l : list A), append A l (Nil A) = l.
  Proof.
    intros A l.
    induction l.
    reflexivity.
    simpl.
    rewrite -> IHl.
    reflexivity.
  Qed.

  Lemma nn: forall (A:Type) (a:A) (l: list A), Cons A a l = 
                                               append A (Cons A a (Nil A)) l.

  Proof.
    intros A a l.
    reflexivity.
  Qed.
  
  
  Lemma dist_rev: forall (A:Type) (l1 l2: list A), rev A (append A l1 l2) =
                                                   append A (rev A l2) (rev A l1).
  Proof.
    intros A l1 l2.
    induction l1.
    induction l2.
    reflexivity.
    simpl.
    rewrite -> neutral_app.
    reflexivity.
    simpl.
    rewrite -> IHl1.
    rewrite -> app_associative.
    reflexivity.
  Qed.

  Theorem rev_involution: forall (A:Type) (l:list A), rev A (rev A l) = l.
  Proof.
    intros A l.
    induction l.
    reflexivity.
    simpl.
    rewrite -> dist_rev.
    rewrite -> IHl.
    reflexivity.
  Qed.
End list.
