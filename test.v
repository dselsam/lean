Require Import mathlib.
Set Typeclasses Debug Verbosity 2.
Test Typeclasses Unique Instances.
(* Coq does not immediately infer the arguments of `algebra`, so force that with a dedicated instance. *)
Instance i (R : Set) (A : Set) `(_inst_1 : comm_ring R) `(_inst_2 : ring A) : @algebra R A _inst_1 _inst_2 := {}.
(*Definition test (R A : Set) `(field R) : has_scalar R A := _.*)
(*Definition test2 (R A : Set) `(field R) `(ring A) `(algebra R A) : has_scalar R A := _.*)
Definition test3 (R A : Set) `(discrete_linear_ordered_field R) : has_scalar R A := _.
