(* These are the definitions from classical logic, which we cannot prove
in Coq, bit we addd these to Coq for later use in semantics!*) 



Module classical.



  (* Excluded middle *)
  Axiom exluded_middle: forall P:Prop, ~P \/ P.

  (* Implication to or like used in ocaml compiler! *)
  Axiom impl_or: forall P Q: Prop, (P -> Q) -> (~P \/ Q).

  
  Theorem eq : forall P Q:Prop, (P -> Q) -> (~P \/ Q) -> (~P \/ P).
  Proof.
    intros P Q H H0.
    apply exluded_middle.
  Qed. 
  
  Theorem eq2: forall P Q:Prop, (~P \/ P) -> (P -> Q) -> (~P \/ Q).
  Proof.
    intros P Q H H0.
    apply impl_or. apply H0.
  Qed.
End classical.
