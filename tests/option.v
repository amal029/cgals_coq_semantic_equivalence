Module option.


(* Define the option type, which will be used in the list hd! *)

Inductive option (X:Type) : Type :=
| Some: X -> option X
| None : option X.


End option.
