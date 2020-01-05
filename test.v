Require Import mathlib.
Set Typeclasses Debug Verbosity 100.
Test Typeclasses Unique Instances.
(* Set Typeclasses Dependency Order True. *)

Definition synth_mul_action_example (k a b : Set)
           (_inst_1 : normed_field k)
           (_mul_action_goal : mul_action k (a -> b) (@ring_to_monoid k (@normed_ring_to_ring k (@normed_field_to_normed_ring k _inst_1))))
  : unit := tt.

Definition try_synth_mul_action_example (k a b : Set)
           (_normed_field_k : normed_field k) : unit := synth_mul_action_example k a b _normed_field_k _.



(*


Definition synth_module (k a : Set) `(module k a) : unit := tt.

Check synth_module.

Check tangent_space_vector_space.

Definition tangent_space_vector_space (𝕜 : Set) `(_inst_1 : nondiscrete_normed_field 𝕜) (E : Set) `(_inst_2 : normed_group E) `(_inst_3 : @normed_space 𝕜 E (@nondiscrete_normed_field_to_normed_field 𝕜 _inst_1) _inst_2) (H : Set) `(_inst_4 : topological_space H) (I : Set) (M : Set) `(_inst_5 : topological_space M) `(_inst_6 : @manifold H _inst_4 M _inst_5) `(_inst_7 : @smooth_manifold_with_corners 𝕜 _inst_1 E _inst_2 _inst_3 H _inst_4 I M _inst_5 _inst_6) (x : Set) : @module 𝕜 E (@domain_to_ring 𝕜 (@division_ring_to_domain 𝕜 (@field_to_division_ring 𝕜 (@discrete_field_to_field 𝕜 (@normed_field_to_discrete_field 𝕜 (@nondiscrete_normed_field_to_normed_field 𝕜 _inst_1)))))) (@tangent_space_add_comm_group 𝕜 _inst_1 E _inst_2 _inst_3 H _inst_4 I M _inst_5 _inst_6 _inst_7 x) := {}.
*)




(*
Definition mul_action_example (k α β : Set) `(normed_field k) `(@mul_action k (α -> β) (@ring_to_monoid k (@normed_ring_to_ring k (@normed_field_to_normed_ring k _)))) : unit := tt.

Definition mul_action_example2 (k α β : Set) `(_inst_1 : normed_field k) : unit := mul_action_example k α β _inst_1 _.

(* Definition test (R A : Set) `(field R) : has_scalar R A := _.*)

Definition test2 (R A : Set) `(field R) `(ring A) `(algebra R A) : has_scalar R A := _.
Definition test3 (R A : Set) `(discrete_linear_ordered_field R) : has_scalar R A := _.
*)
