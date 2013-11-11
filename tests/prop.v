Module prop.

  Inductive isB : nat -> Prop :=
  | b_0 : isB 0
  | b_3 : isB 3
  | b_5 : isB 5
  | b_sum : forall n m:nat, isB n -> isB m -> isB (n+m).


  Lemma three_isB : isB 3.
  Proof.
    apply b_3.
  Qed.

  Lemma five_isB : isB 5.
  Proof.
    apply b_5.
  Qed.


  Theorem eight_isB : isB 8.
  Proof.
    apply b_sum with (n:=3) (m:=5).
    apply b_3. apply b_5.
  Qed.

  Theorem beautiful_plus_eight: forall n, isB n -> isB (8+n).
  Proof.
    intros n H.
    apply b_sum.
    apply eight_isB.
    apply H.
  Qed.

  Theorem b_timesm: forall n m: nat, isB n -> isB (m*n).
  Proof.
    intros n m H.
    induction m.
    simpl. apply b_0.
    simpl.
    apply b_sum.
    apply H.
    apply IHm.
  Qed.

  Inductive gor : nat -> Prop :=
  | g_0 : gor 0
  | g_3: forall n, gor n -> gor (3+n)
  | g_5: forall n, gor n -> gor (5+n).

  Lemma gb : forall n, gor n -> isB n.
  Proof.  
    intros n H.
    induction H.
    apply b_0. apply b_sum. apply b_3. apply IHgor.
    apply b_sum. apply b_5. apply IHgor.
  Qed.
  
  Lemma gs : forall n m:nat, gor n -> gor m -> gor (n+m).
  Proof.
    intros n m H H0.
    induction H.
    apply H0.
    apply g_3. apply IHgor.
    apply g_5. apply IHgor.
  Qed.    
  
  Theorem bg: forall n:nat, isB n -> gor n.
  Proof.
    intros n H.
    induction H.
    apply g_0. apply g_3. apply g_0. apply g_5. apply g_0.
    apply gs. apply IHisB1. apply IHisB2.
  Qed.        
  
  Theorem andb : forall n m, isB n -> isB m -> isB n /\ isB m.
  Proof.
    intros n m H H0.
    apply conj. apply H. apply H0. (* We can just use auto here! *)
  Qed.

  (* This theorem cannot be proven in Coq. I think! *)
  Theorem impor: forall P Q: Prop, P -> Q -> ~ P \/ Q.
    intros P Q H.
    apply or_intror with (A:=Q) in H.
    apply or_comm in H.
    admit.
  Qed.
  
  
End prop.
