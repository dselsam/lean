Class decidable (p : Type).
Class has_zero (α : Type).
Class has_one (α : Type).
Class has_add (α : Type).
Class has_mul (α : Type).
Class has_inv (α : Type).
Class has_neg (α : Type).
Class has_sub (α : Type).
Class has_div (α : Type).
Class has_dvd (α : Type).
Class has_mod (α : Type).
Class has_le (α : Type).
Class has_lt (α : Type).
Class has_append (α : Type).
Class has_andthen (α : Type) (β : Type) (σ : Type).
Class has_union (α : Type).
Class has_inter (α : Type).
Class has_sdiff (α : Type).
Class has_equiv (α : Type).
Class has_subset (α : Type).
Class has_ssubset (α : Type).
Class has_emptyc (α : Type).
Class has_insert (α : Type) (γ : Type).
Class has_sep (α : Type) (γ : Type).
Class has_mem (α : Type) (γ : Type).
Class has_pow (α : Type) (β : Type).
Class has_sizeof (α : Type).
Class inhabited (α : Type).
Class nonempty (α : Type).
Instance nonempty_of_inhabited (α : Type) `(_inst_1 : inhabited α) : nonempty α := {}.
Class subsingleton (α : Type).
Instance subsingleton_prop (p : Type) : subsingleton p := {}.
Class setoid (α : Type).
Instance setoid_has_equiv (α : Type) `(_inst_1 : setoid α) : has_equiv α := {}.
Class has_well_founded (α : Type).
Instance has_well_founded_of_has_sizeof (α : Type) `(_inst_1 : has_sizeof α) : has_well_founded α := {}.
Class has_lift (a : Type) (b : Type).
Class has_lift_t (a : Type) (b : Type).
Class has_coe (a : Type) (b : Type).
Class has_coe_t (a : Type) (b : Type).
Class has_coe_to_fun (a : Type).
Class has_coe_to_sort (a : Type).
Instance lift_trans (a : Type) (b : Type) (c : Type) `(_inst_1 : has_lift a b) `(_inst_2 : has_lift_t b c) : has_lift_t a c := {}.
Instance lift_base (a : Type) (b : Type) `(_inst_1 : has_lift a b) : has_lift_t a b := {}.
Instance coe_trans (a : Type) (b : Type) (c : Type) `(_inst_1 : has_coe a b) `(_inst_2 : has_coe_t b c) : has_coe_t a c := {}.
Instance coe_base (a : Type) (b : Type) `(_inst_1 : has_coe a b) : has_coe_t a b := {}.
Class has_coe_t_aux (a : Type) (b : Type).
Instance coe_trans_aux (a : Type) (b : Type) (c : Type) `(_inst_1 : has_coe a b) `(_inst_2 : has_coe_t_aux b c) : has_coe_t_aux a c := {}.
Instance coe_base_aux (a : Type) (b : Type) `(_inst_1 : has_coe a b) : has_coe_t_aux a b := {}.
Instance coe_fn_trans (a : Type) (b : Type) `(_inst_1 : has_coe_t_aux a b) `(_inst_2 : has_coe_to_fun b) : has_coe_to_fun a := {}.
Instance coe_sort_trans (a : Type) (b : Type) `(_inst_1 : has_coe_t_aux a b) `(_inst_2 : has_coe_to_sort b) : has_coe_to_sort a := {}.
Instance coe_to_lift (a : Type) (b : Type) `(_inst_1 : has_coe_t a b) : has_lift_t a b := {}.
Class has_repr (α : Type).
Class has_to_string (α : Type).
Class is_symm_op (α : Type) (β : Type) (op : Type).
Class is_commutative (α : Type) (op : Type).
Instance is_symm_op_of_is_commutative (α : Type) (op : Type) `(_inst_1 : is_commutative α op) : is_symm_op α α op := {}.
Class is_associative (α : Type) (op : Type).
Class is_left_id (α : Type) (op : Type) (o : Type).
Class is_right_id (α : Type) (op : Type) (o : Type).
Class is_left_null (α : Type) (op : Type) (o : Type).
Class is_right_null (α : Type) (op : Type) (o : Type).
Class is_left_cancel (α : Type) (op : Type).
Class is_right_cancel (α : Type) (op : Type).
Class is_idempotent (α : Type) (op : Type).
Class is_left_distrib (α : Type) (op₁ : Type) (op₂ : Type).
Class is_right_distrib (α : Type) (op₁ : Type) (op₂ : Type).
Class is_left_inv (α : Type) (op : Type) (inv : Type) (o : Type).
Class is_right_inv (α : Type) (op : Type) (inv : Type) (o : Type).
Class is_cond_left_inv (α : Type) (op : Type) (inv : Type) (o : Type) (p : Type).
Class is_cond_right_inv (α : Type) (op : Type) (inv : Type) (o : Type) (p : Type).
Class is_distinct (α : Type) (a : Type) (b : Type).
Class is_irrefl (α : Type) (r : Type).
Class is_refl (α : Type) (r : Type).
Class is_symm (α : Type) (r : Type).
Class is_asymm (α : Type) (r : Type).
Class is_antisymm (α : Type) (r : Type).
Class is_trans (α : Type) (r : Type).
Class is_total (α : Type) (r : Type).
Class is_preorder (α : Type) (r : Type).
Instance is_preorder_to_is_refl (α : Type) (r : Type) `(c : is_preorder α r) : is_refl α r := {}.
Instance is_preorder_to_is_trans (α : Type) (r : Type) `(c : is_preorder α r) : is_trans α r := {}.
Class is_total_preorder (α : Type) (r : Type).
Instance is_total_preorder_to_is_trans (α : Type) (r : Type) `(c : is_total_preorder α r) : is_trans α r := {}.
Instance is_total_preorder_to_is_total (α : Type) (r : Type) `(c : is_total_preorder α r) : is_total α r := {}.
Instance is_total_preorder_is_preorder (α : Type) (r : Type) `(s : is_total_preorder α r) : is_preorder α r := {}.
Class is_partial_order (α : Type) (r : Type).
Instance is_partial_order_to_is_preorder (α : Type) (r : Type) `(c : is_partial_order α r) : is_preorder α r := {}.
Instance is_partial_order_to_is_antisymm (α : Type) (r : Type) `(c : is_partial_order α r) : is_antisymm α r := {}.
Class has_to_format (α : Type).
Class is_linear_order (α : Type) (r : Type).
Instance is_linear_order_to_is_partial_order (α : Type) (r : Type) `(c : is_linear_order α r) : is_partial_order α r := {}.
Instance is_linear_order_to_is_total (α : Type) (r : Type) `(c : is_linear_order α r) : is_total α r := {}.
Class is_equiv (α : Type) (r : Type).
Instance is_equiv_to_is_preorder (α : Type) (r : Type) `(c : is_equiv α r) : is_preorder α r := {}.
Instance is_equiv_to_is_symm (α : Type) (r : Type) `(c : is_equiv α r) : is_symm α r := {}.
Class is_per (α : Type) (r : Type).
Instance is_per_to_is_symm (α : Type) (r : Type) `(c : is_per α r) : is_symm α r := {}.
Instance is_per_to_is_trans (α : Type) (r : Type) `(c : is_per α r) : is_trans α r := {}.
Class is_strict_order (α : Type) (r : Type).
Instance is_strict_order_to_is_irrefl (α : Type) (r : Type) `(c : is_strict_order α r) : is_irrefl α r := {}.
Instance is_strict_order_to_is_trans (α : Type) (r : Type) `(c : is_strict_order α r) : is_trans α r := {}.
Class is_incomp_trans (α : Type) (lt : Type).
Class is_strict_weak_order (α : Type) (lt : Type).
Instance is_strict_weak_order_to_is_strict_order (α : Type) (lt : Type) `(c : is_strict_weak_order α lt) : is_strict_order α lt := {}.
Instance is_strict_weak_order_to_is_incomp_trans (α : Type) (lt : Type) `(c : is_strict_weak_order α lt) : is_incomp_trans α lt := {}.
Class is_trichotomous (α : Type) (lt : Type).
Class is_strict_total_order (α : Type) (lt : Type).
Instance is_strict_total_order_to_is_trichotomous (α : Type) (lt : Type) `(c : is_strict_total_order α lt) : is_trichotomous α lt := {}.
Instance is_strict_total_order_to_is_strict_weak_order (α : Type) (lt : Type) `(c : is_strict_total_order α lt) : is_strict_weak_order α lt := {}.
Instance is_asymm_of_is_trans_of_is_irrefl (α : Type) (r : Type) `(_inst_1 : is_trans α r) `(_inst_2 : is_irrefl α r) : is_asymm α r := {}.
Class functor (f : Type).
Class has_pure (f : Type).
Class has_seq (f : Type).
Class has_seq_left (f : Type).
Class has_seq_right (f : Type).
Class preorder (α : Type).
Instance preorder_to_has_le (α : Type) `(s : preorder α) : has_le α := {}.
Instance preorder_to_has_lt (α : Type) `(s : preorder α) : has_lt α := {}.
Class applicative (f : Type).
Instance applicative_to_functor (f : Type) `(c : applicative f) : functor f := {}.
Instance applicative_to_has_pure (f : Type) `(c : applicative f) : has_pure f := {}.
Instance applicative_to_has_seq (f : Type) `(c : applicative f) : has_seq f := {}.
Instance applicative_to_has_seq_left (f : Type) `(c : applicative f) : has_seq_left f := {}.
Instance applicative_to_has_seq_right (f : Type) `(c : applicative f) : has_seq_right f := {}.
Class has_bind (m : Type).
Class monad (m : Type).
Instance monad_to_applicative (m : Type) `(c : monad m) : applicative m := {}.
Instance monad_to_has_bind (m : Type) `(c : monad m) : has_bind m := {}.
Class partial_order (α : Type).
Instance partial_order_to_preorder (α : Type) `(s : partial_order α) : preorder α := {}.
Class linear_order (α : Type).
Instance linear_order_to_partial_order (α : Type) `(s : linear_order α) : partial_order α := {}.
Class has_orelse (f : Type).
Class has_monad_lift (m : Type) (n : Type).
Class has_monad_lift_t (m : Type) (n : Type).
Class alternative (f : Type).
Instance alternative_to_applicative (f : Type) `(c : alternative f) : applicative f := {}.
Instance alternative_to_has_orelse (f : Type) `(c : alternative f) : has_orelse f := {}.
Instance has_monad_lift_t_trans (m : Type) (n : Type) (o : Type) `(_inst_1 : has_monad_lift n o) `(_inst_2 : has_monad_lift_t m n) : has_monad_lift_t m o := {}.
Instance has_monad_lift_t_refl (m : Type) : has_monad_lift_t m m := {}.
Class monad_functor (m : Type) (m' : Type) (n : Type) (n' : Type).
Class monad_functor_t (m : Type) (m' : Type) (n : Type) (n' : Type).
Instance monad_functor_t_trans (m : Type) (m' : Type) (n : Type) (n' : Type) (o : Type) (o' : Type) `(_inst_1 : monad_functor n n' o o') `(_inst_2 : monad_functor_t m m' n n') : monad_functor_t m m' o o' := {}.
Instance monad_functor_t_refl (m : Type) (m' : Type) : monad_functor_t m m' m m' := {}.
Class monad_run (out : Type) (m : Type).
Class monad_fail (m : Type).
Instance monad_fail_lift (m : Type) (n : Type) `(_inst_1 : has_monad_lift m n) `(_inst_2 : monad_fail m) `(_inst_3 : monad n) : monad_fail n := {}.
Class decidable_linear_order (α : Type).
Instance decidable_linear_order_to_linear_order (α : Type) `(s : decidable_linear_order α) : linear_order α := {}.
Class monad_except (ε : Type) (m : Type).
Class reflected (α : Type) (a : Type).
Class monad_except_adapter (ε : Type) (ε' : Type) (m : Type) (m' : Type).
Instance monad_except_adapter_trans (ε : Type) (ε' : Type) (m : Type) (m' : Type) (n : Type) (n' : Type) `(_inst_1 : monad_functor m m' n n') `(_inst_2 : monad_except_adapter ε ε' m m') : monad_except_adapter ε ε' n n' := {}.
Class monad_reader (ρ : Type) (m : Type).
Instance monad_reader_trans (ρ : Type) (m : Type) (n : Type) `(_inst_1 : has_monad_lift m n) `(_inst_2 : monad_reader ρ m) : monad_reader ρ n := {}.
Class monad_reader_adapter (ρ : Type) (ρ' : Type) (m : Type) (m' : Type).
Instance monad_reader_adapter_trans (ρ : Type) (ρ' : Type) (m : Type) (m' : Type) (n : Type) (n' : Type) `(_inst_1 : monad_functor m m' n n') `(_inst_2 : monad_reader_adapter ρ ρ' m m') : monad_reader_adapter ρ ρ' n n' := {}.
Class monad_state (σ : Type) (m : Type).
Instance monad_state_trans (σ : Type) (m : Type) (n : Type) `(_inst_1 : has_monad_lift m n) `(_inst_2 : monad_state σ m) : monad_state σ n := {}.
Class monad_state_adapter (σ : Type) (σ' : Type) (m : Type) (m' : Type).
Instance monad_state_adapter_trans (σ : Type) (σ' : Type) (m : Type) (m' : Type) (n : Type) (n' : Type) `(_inst_1 : monad_functor m m' n n') `(_inst_2 : monad_state_adapter σ σ' m m') : monad_state_adapter σ σ' n n' := {}.
Class has_to_pexpr (α : Type).
Class has_to_tactic_format (α : Type).
Instance has_to_format_to_has_to_tactic_format (α : Type) `(_inst_1 : has_to_format α) : has_to_tactic_format α := {}.
Class is_lawful_functor (f : Type) `(_inst_1 : functor f).
Class is_lawful_applicative (f : Type) `(_inst_1 : applicative f).
Instance is_lawful_applicative_to_is_lawful_functor (f : Type) `(_inst_1 : applicative f) `(c : @is_lawful_applicative f _inst_1) : @is_lawful_functor f (@applicative_to_functor f _inst_1) := {}.
Class is_lawful_monad (m : Type) `(_inst_1 : monad m).
Instance is_lawful_monad_to_is_lawful_applicative (m : Type) `(_inst_1 : monad m) `(c : @is_lawful_monad m _inst_1) : @is_lawful_applicative m (@monad_to_applicative m _inst_1) := {}.
Class semigroup (α : Type).
Instance semigroup_to_has_mul (α : Type) `(s : semigroup α) : has_mul α := {}.
Class comm_semigroup (α : Type).
Instance comm_semigroup_to_semigroup (α : Type) `(s : comm_semigroup α) : semigroup α := {}.
Class left_cancel_semigroup (α : Type).
Instance left_cancel_semigroup_to_semigroup (α : Type) `(s : left_cancel_semigroup α) : semigroup α := {}.
Class right_cancel_semigroup (α : Type).
Instance right_cancel_semigroup_to_semigroup (α : Type) `(s : right_cancel_semigroup α) : semigroup α := {}.
Class monoid (α : Type).
Instance monoid_to_semigroup (α : Type) `(s : monoid α) : semigroup α := {}.
Instance monoid_to_has_one (α : Type) `(s : monoid α) : has_one α := {}.
Class comm_monoid (α : Type).
Instance comm_monoid_to_monoid (α : Type) `(s : comm_monoid α) : monoid α := {}.
Instance comm_monoid_to_comm_semigroup (α : Type) `(s : comm_monoid α) : comm_semigroup α := {}.
Class group (α : Type).
Instance group_to_monoid (α : Type) `(s : group α) : monoid α := {}.
Instance group_to_has_inv (α : Type) `(s : group α) : has_inv α := {}.
Class comm_group (α : Type).
Instance comm_group_to_group (α : Type) `(s : comm_group α) : group α := {}.
Instance comm_group_to_comm_monoid (α : Type) `(s : comm_group α) : comm_monoid α := {}.
Instance group_to_left_cancel_semigroup (α : Type) `(s : group α) : left_cancel_semigroup α := {}.
Instance group_to_right_cancel_semigroup (α : Type) `(s : group α) : right_cancel_semigroup α := {}.
Class add_semigroup (α : Type).
Instance add_semigroup_to_has_add (α : Type) `(s : add_semigroup α) : has_add α := {}.
Class add_comm_semigroup (α : Type).
Instance add_comm_semigroup_to_add_semigroup (α : Type) `(s : add_comm_semigroup α) : add_semigroup α := {}.
Class add_left_cancel_semigroup (α : Type).
Instance add_left_cancel_semigroup_to_add_semigroup (α : Type) `(s : add_left_cancel_semigroup α) : add_semigroup α := {}.
Class add_right_cancel_semigroup (α : Type).
Instance add_right_cancel_semigroup_to_add_semigroup (α : Type) `(s : add_right_cancel_semigroup α) : add_semigroup α := {}.
Class add_monoid (α : Type).
Instance add_monoid_to_add_semigroup (α : Type) `(s : add_monoid α) : add_semigroup α := {}.
Instance add_monoid_to_has_zero (α : Type) `(s : add_monoid α) : has_zero α := {}.
Class add_comm_monoid (α : Type).
Instance add_comm_monoid_to_add_monoid (α : Type) `(s : add_comm_monoid α) : add_monoid α := {}.
Instance add_comm_monoid_to_add_comm_semigroup (α : Type) `(s : add_comm_monoid α) : add_comm_semigroup α := {}.
Class add_group (α : Type).
Instance add_group_to_add_monoid (α : Type) `(s : add_group α) : add_monoid α := {}.
Instance add_group_to_has_neg (α : Type) `(s : add_group α) : has_neg α := {}.
Class add_comm_group (α : Type).
Instance add_comm_group_to_add_group (α : Type) `(s : add_comm_group α) : add_group α := {}.
Instance add_comm_group_to_add_comm_monoid (α : Type) `(s : add_comm_group α) : add_comm_monoid α := {}.
Instance add_group_to_left_cancel_add_semigroup (α : Type) `(s : add_group α) : add_left_cancel_semigroup α := {}.
Instance add_group_to_right_cancel_add_semigroup (α : Type) `(s : add_group α) : add_right_cancel_semigroup α := {}.
Instance add_group_has_sub (α : Type) `(_inst_1 : add_group α) : has_sub α := {}.
Class distrib (α : Type).
Instance distrib_to_has_mul (α : Type) `(s : distrib α) : has_mul α := {}.
Instance distrib_to_has_add (α : Type) `(s : distrib α) : has_add α := {}.
Class ordered_cancel_comm_monoid (α : Type).
Instance ordered_cancel_comm_monoid_to_add_comm_monoid (α : Type) `(s : ordered_cancel_comm_monoid α) : add_comm_monoid α := {}.
Instance ordered_cancel_comm_monoid_to_add_left_cancel_semigroup (α : Type) `(s : ordered_cancel_comm_monoid α) : add_left_cancel_semigroup α := {}.
Instance ordered_cancel_comm_monoid_to_add_right_cancel_semigroup (α : Type) `(s : ordered_cancel_comm_monoid α) : add_right_cancel_semigroup α := {}.
Instance ordered_cancel_comm_monoid_to_partial_order (α : Type) `(s : ordered_cancel_comm_monoid α) : partial_order α := {}.
Class mul_zero_class (α : Type).
Instance mul_zero_class_to_has_mul (α : Type) `(s : mul_zero_class α) : has_mul α := {}.
Instance mul_zero_class_to_has_zero (α : Type) `(s : mul_zero_class α) : has_zero α := {}.
Class zero_ne_one_class (α : Type).
Instance zero_ne_one_class_to_has_zero (α : Type) `(s : zero_ne_one_class α) : has_zero α := {}.
Instance zero_ne_one_class_to_has_one (α : Type) `(s : zero_ne_one_class α) : has_one α := {}.
Class semiring (α : Type).
Instance semiring_to_add_comm_monoid (α : Type) `(s : semiring α) : add_comm_monoid α := {}.
Instance semiring_to_monoid (α : Type) `(s : semiring α) : monoid α := {}.
Instance semiring_to_distrib (α : Type) `(s : semiring α) : distrib α := {}.
Instance semiring_to_mul_zero_class (α : Type) `(s : semiring α) : mul_zero_class α := {}.
Class ordered_comm_group (α : Type).
Instance ordered_comm_group_to_add_comm_group (α : Type) `(s : ordered_comm_group α) : add_comm_group α := {}.
Instance ordered_comm_group_to_partial_order (α : Type) `(s : ordered_comm_group α) : partial_order α := {}.
Instance ordered_comm_group_to_ordered_cancel_comm_monoid (α : Type) `(s : ordered_comm_group α) : ordered_cancel_comm_monoid α := {}.
Class comm_semiring (α : Type).
Instance comm_semiring_to_semiring (α : Type) `(s : comm_semiring α) : semiring α := {}.
Instance comm_semiring_to_comm_monoid (α : Type) `(s : comm_semiring α) : comm_monoid α := {}.
Instance comm_semiring_has_dvd (α : Type) `(_inst_1 : comm_semiring α) : has_dvd α := {}.
Class ring (α : Type).
Instance ring_to_add_comm_group (α : Type) `(s : ring α) : add_comm_group α := {}.
Instance ring_to_monoid (α : Type) `(s : ring α) : monoid α := {}.
Instance ring_to_distrib (α : Type) `(s : ring α) : distrib α := {}.
Instance ring_to_semiring (α : Type) `(s : ring α) : semiring α := {}.
Class comm_ring (α : Type).
Instance comm_ring_to_ring (α : Type) `(s : comm_ring α) : ring α := {}.
Instance comm_ring_to_comm_semigroup (α : Type) `(s : comm_ring α) : comm_semigroup α := {}.
Instance comm_ring_to_comm_semiring (α : Type) `(s : comm_ring α) : comm_semiring α := {}.
Class no_zero_divisors (α : Type).
Instance no_zero_divisors_to_has_mul (α : Type) `(s : no_zero_divisors α) : has_mul α := {}.
Instance no_zero_divisors_to_has_zero (α : Type) `(s : no_zero_divisors α) : has_zero α := {}.
Class integral_domain (α : Type).
Instance integral_domain_to_comm_ring (α : Type) `(s : integral_domain α) : comm_ring α := {}.
Instance integral_domain_to_no_zero_divisors (α : Type) `(s : integral_domain α) : no_zero_divisors α := {}.
Instance integral_domain_to_zero_ne_one_class (α : Type) `(s : integral_domain α) : zero_ne_one_class α := {}.
Class division_ring (α : Type).
Instance division_ring_to_ring (α : Type) `(s : division_ring α) : ring α := {}.
Instance division_ring_to_has_inv (α : Type) `(s : division_ring α) : has_inv α := {}.
Instance division_ring_to_zero_ne_one_class (α : Type) `(s : division_ring α) : zero_ne_one_class α := {}.
Instance division_ring_has_div (α : Type) `(_inst_1 : division_ring α) `(_inst_2 : division_ring α) : has_div α := {}.
Class decidable_linear_ordered_comm_group (α : Type).
Instance decidable_linear_ordered_comm_group_to_add_comm_group (α : Type) `(s : decidable_linear_ordered_comm_group α) : add_comm_group α := {}.
Instance decidable_linear_ordered_comm_group_to_decidable_linear_order (α : Type) `(s : decidable_linear_ordered_comm_group α) : decidable_linear_order α := {}.
Instance decidable_linear_ordered_comm_group_to_ordered_comm_group (α : Type) `(s : decidable_linear_ordered_comm_group α) : ordered_comm_group α := {}.
Class decidable_linear_ordered_cancel_comm_monoid (α : Type).
Instance decidable_linear_ordered_cancel_comm_monoid_to_ordered_cancel_comm_monoid (α : Type) `(s : decidable_linear_ordered_cancel_comm_monoid α) : ordered_cancel_comm_monoid α := {}.
Instance decidable_linear_ordered_cancel_comm_monoid_to_decidable_linear_order (α : Type) `(s : decidable_linear_ordered_cancel_comm_monoid α) : decidable_linear_order α := {}.
Class field (α : Type).
Instance field_to_division_ring (α : Type) `(s : field α) : division_ring α := {}.
Instance field_to_comm_ring (α : Type) `(s : field α) : comm_ring α := {}.
Class discrete_field (α : Type).
Instance discrete_field_to_field (α : Type) `(s : discrete_field α) : field α := {}.
Instance discrete_field_to_integral_domain (α : Type) `(_inst_1 : discrete_field α) `(s : discrete_field α) : integral_domain α := {}.
Class ordered_semiring (α : Type).
Instance ordered_semiring_to_semiring (α : Type) `(s : ordered_semiring α) : semiring α := {}.
Instance ordered_semiring_to_ordered_cancel_comm_monoid (α : Type) `(s : ordered_semiring α) : ordered_cancel_comm_monoid α := {}.
Class linear_ordered_semiring (α : Type).
Instance linear_ordered_semiring_to_ordered_semiring (α : Type) `(s : linear_ordered_semiring α) : ordered_semiring α := {}.
Instance linear_ordered_semiring_to_linear_order (α : Type) `(s : linear_ordered_semiring α) : linear_order α := {}.
Class decidable_linear_ordered_semiring (α : Type).
Instance decidable_linear_ordered_semiring_to_linear_ordered_semiring (α : Type) `(s : decidable_linear_ordered_semiring α) : linear_ordered_semiring α := {}.
Instance decidable_linear_ordered_semiring_to_decidable_linear_order (α : Type) `(s : decidable_linear_ordered_semiring α) : decidable_linear_order α := {}.
Class ordered_ring (α : Type).
Instance ordered_ring_to_ring (α : Type) `(s : ordered_ring α) : ring α := {}.
Instance ordered_ring_to_ordered_comm_group (α : Type) `(s : ordered_ring α) : ordered_comm_group α := {}.
Instance ordered_ring_to_zero_ne_one_class (α : Type) `(s : ordered_ring α) : zero_ne_one_class α := {}.
Instance ordered_ring_to_ordered_semiring (α : Type) `(s : ordered_ring α) : ordered_semiring α := {}.
Class linear_ordered_ring (α : Type).
Instance linear_ordered_ring_to_ordered_ring (α : Type) `(s : linear_ordered_ring α) : ordered_ring α := {}.
Instance linear_ordered_ring_to_linear_order (α : Type) `(s : linear_ordered_ring α) : linear_order α := {}.
Instance linear_ordered_ring_to_linear_ordered_semiring (α : Type) `(s : linear_ordered_ring α) : linear_ordered_semiring α := {}.
Class linear_ordered_comm_ring (α : Type).
Instance linear_ordered_comm_ring_to_linear_ordered_ring (α : Type) `(s : linear_ordered_comm_ring α) : linear_ordered_ring α := {}.
Instance linear_ordered_comm_ring_to_comm_monoid (α : Type) `(s : linear_ordered_comm_ring α) : comm_monoid α := {}.
Instance linear_ordered_comm_ring_to_integral_domain (α : Type) `(s : linear_ordered_comm_ring α) : integral_domain α := {}.
Class decidable_linear_ordered_comm_ring (α : Type).
Instance decidable_linear_ordered_comm_ring_to_linear_ordered_comm_ring (α : Type) `(s : decidable_linear_ordered_comm_ring α) : linear_ordered_comm_ring α := {}.
Instance decidable_linear_ordered_comm_ring_to_decidable_linear_ordered_comm_group (α : Type) `(s : decidable_linear_ordered_comm_ring α) : decidable_linear_ordered_comm_group α := {}.
Instance decidable_linear_ordered_comm_ring_to_decidable_linear_ordered_semiring (α : Type) `(d : decidable_linear_ordered_comm_ring α) : decidable_linear_ordered_semiring α := {}.
Class linear_ordered_field (α : Type).
Instance linear_ordered_field_to_linear_ordered_ring (α : Type) `(s : linear_ordered_field α) : linear_ordered_ring α := {}.
Instance linear_ordered_field_to_field (α : Type) `(s : linear_ordered_field α) : field α := {}.
Class discrete_linear_ordered_field (α : Type).
Instance discrete_linear_ordered_field_to_linear_ordered_field (α : Type) `(s : discrete_linear_ordered_field α) : linear_ordered_field α := {}.
Instance discrete_linear_ordered_field_to_decidable_linear_ordered_comm_ring (α : Type) `(s : discrete_linear_ordered_field α) : decidable_linear_ordered_comm_ring α := {}.
Instance discrete_linear_ordered_field_to_discrete_field (α : Type) `(s : discrete_linear_ordered_field α) : discrete_field α := {}.
Class unique (α : Type).
Class relator_right_total (α : Type) (β : Type) (R : Type).
Class relator_left_total (α : Type) (β : Type) (R : Type).
Class relator_bi_total (α : Type) (β : Type) (R : Type).
Instance unique_inhabited (α : Type) `(_inst_1 : unique α) : inhabited α := {}.
Instance unique_subsingleton (α : Type) `(_inst_1 : unique α) : subsingleton α := {}.
Class relator_left_unique (α : Type) (β : Type) (R : Type).
Class relator_right_unique (α : Type) (β : Type) (R : Type).
Class is_comm_applicative (m : Type) `(_inst_1 : applicative m).
Instance is_comm_applicative_to_is_lawful_applicative (m : Type) `(_inst_1 : applicative m) `(c : @is_comm_applicative m _inst_1) : @is_lawful_applicative m _inst_1 := {}.
Class can_lift (α : Type) (β : Type).
Class traversable (t : Type).
Instance traversable_to_functor (t : Type) `(c : traversable t) : functor t := {}.
Class is_lawful_traversable (t : Type) `(_inst_1 : traversable t).
Instance is_lawful_traversable_to_is_lawful_functor (t : Type) `(_inst_1 : traversable t) `(c : @is_lawful_traversable t _inst_1) : @is_lawful_functor t (@traversable_to_functor t _inst_1) := {}.
Class eckmann_hilton_is_unital (X : Type) (m : Type) (e : Type).
Class category_theory_has_hom (obj : Type).
Class category_theory_category_struct (obj : Type).
Instance category_theory_category_struct_to_has_hom (obj : Type) `(c : category_theory_category_struct obj) : category_theory_has_hom obj := {}.
Class category_theory_category (obj : Type).
Instance category_theory_category_to_category_struct (obj : Type) `(c : category_theory_category obj) : category_theory_category_struct obj := {}.
Class bifunctor (F : Type).
Class is_lawful_bifunctor (F : Type) `(_inst_1 : bifunctor F).
Class category_theory_epi (C : Type) `(𝒞 : category_theory_category C) (X : Type) (Y : Type) (f : Type).
Class category_theory_mono (C : Type) `(𝒞 : category_theory_category C) (X : Type) (Y : Type) (f : Type).
Instance preorder_small_category (α : Type) `(_inst_1 : preorder α) : category_theory_category α := {}.
Class computation_terminates (α : Type) (s : Type).
Class monad_writer (ω : Type) (m : Type).
Class bitraversable (t : Type).
Instance bitraversable_to_bifunctor (t : Type) `(c : bitraversable t) : bifunctor t := {}.
Class monad_writer_adapter (ω : Type) (ω' : Type) (m : Type) (m' : Type).
Class is_lawful_bitraversable (t : Type) `(_inst_1 : bitraversable t).
Instance is_lawful_bitraversable_to_is_lawful_bifunctor (t : Type) `(_inst_1 : bitraversable t) `(c : @is_lawful_bitraversable t _inst_1) : @is_lawful_bifunctor t (@bitraversable_to_bifunctor t _inst_1) := {}.
Instance monad_writer_adapter_trans (ω : Type) (ω' : Type) (m : Type) (m' : Type) (n : Type) (n' : Type) `(_inst_1 : monad_functor m m' n n') `(_inst_2 : monad_writer_adapter ω ω' m m') : monad_writer_adapter ω ω' n n' := {}.
Class monad_cont (m : Type).
Class is_lawful_monad_cont (m : Type) `(_inst_1 : monad m) `(_inst_2 : monad_cont m).
Instance is_lawful_monad_cont_to_is_lawful_monad (m : Type) `(_inst_1 : monad m) `(_inst_2 : monad_cont m) `(c : @is_lawful_monad_cont m _inst_1 _inst_2) : @is_lawful_monad m _inst_1 := {}.
Class category_theory_is_iso (C : Type) `(𝒞 : category_theory_category C) (X : Type) (Y : Type) (f : Type).
Instance category_theory_is_iso_epi_of_iso (C : Type) `(𝒞 : category_theory_category C) (X : Type) (Y : Type) (f : Type) `(_inst_1 : @category_theory_is_iso C 𝒞 X Y f) : @category_theory_epi C 𝒞 X Y f := {}.
Instance category_theory_is_iso_mono_of_iso (C : Type) `(𝒞 : category_theory_category C) (X : Type) (Y : Type) (f : Type) `(_inst_1 : @category_theory_is_iso C 𝒞 X Y f) : @category_theory_mono C 𝒞 X Y f := {}.
Class category_theory_groupoid (obj : Type).
Instance category_theory_groupoid_to_category (obj : Type) `(c : category_theory_groupoid obj) : category_theory_category obj := {}.
Class category_theory_full (C : Type) `(𝒞 : category_theory_category C) (D : Type) `(𝒟 : category_theory_category D) (F : Type).
Class category_theory_monad (C : Type) `(𝒞 : category_theory_category C) (T : Type).
Class category_theory_faithful (C : Type) `(𝒞 : category_theory_category C) (D : Type) `(𝒟 : category_theory_category D) (F : Type).
Instance category_theory_of_groupoid (C : Type) `(_inst_1 : category_theory_groupoid C) (X : Type) (Y : Type) (f : Type) : @category_theory_is_iso C (@category_theory_groupoid_to_category C _inst_1) X Y f := {}.
Class is_group_anti_hom (α : Type) (β : Type) `(_inst_1 : group α) `(_inst_2 : group β) (f : Type).
Class is_add_hom (α : Type) (β : Type) `(_inst_1 : has_add α) `(_inst_2 : has_add β) (f : Type).
Class is_mul_hom (α : Type) (β : Type) `(_inst_1 : has_mul α) `(_inst_2 : has_mul β) (f : Type).
Class pSet_definable (n : Type) (a : Type).
Class is_add_monoid_hom (α : Type) (β : Type) `(_inst_1 : add_monoid α) `(_inst_2 : add_monoid β) (f : Type).
Instance is_add_monoid_hom_to_is_add_hom (α : Type) (β : Type) `(_inst_1 : add_monoid α) `(_inst_2 : add_monoid β) (f : Type) `(c : @is_add_monoid_hom α β _inst_1 _inst_2 f) : @is_add_hom α β (@add_semigroup_to_has_add α (@add_monoid_to_add_semigroup α _inst_1)) (@add_semigroup_to_has_add β (@add_monoid_to_add_semigroup β _inst_2)) f := {}.
Class is_monoid_hom (α : Type) (β : Type) `(_inst_1 : monoid α) `(_inst_2 : monoid β) (f : Type).
Instance is_monoid_hom_to_is_mul_hom (α : Type) (β : Type) `(_inst_1 : monoid α) `(_inst_2 : monoid β) (f : Type) `(c : @is_monoid_hom α β _inst_1 _inst_2 f) : @is_mul_hom α β (@semigroup_to_has_mul α (@monoid_to_semigroup α _inst_1)) (@semigroup_to_has_mul β (@monoid_to_semigroup β _inst_2)) f := {}.
Class no_top_order (α : Type) `(_inst_1 : preorder α).
Class no_bot_order (α : Type) `(_inst_1 : preorder α).
Class densely_ordered (α : Type) `(_inst_1 : preorder α).
Class is_strict_total_order' (α : Type) (lt : Type).
Instance is_strict_total_order'_to_is_trichotomous (α : Type) (lt : Type) `(c : is_strict_total_order' α lt) : is_trichotomous α lt := {}.
Instance is_strict_total_order'_to_is_strict_order (α : Type) (lt : Type) `(c : is_strict_total_order' α lt) : is_strict_order α lt := {}.
Class is_order_connected (α : Type) (lt : Type).
Instance is_order_connected_of_is_strict_total_order' (α : Type) (r : Type) `(_inst_1 : is_strict_total_order' α r) : is_order_connected α r := {}.
Instance is_strict_total_order_of_is_strict_total_order' (α : Type) (r : Type) `(_inst_1 : is_strict_total_order' α r) : is_strict_total_order α r := {}.
Class is_extensional (α : Type) (r : Type).
Class is_add_group_hom (α : Type) (β : Type) `(_inst_1 : add_group α) `(_inst_2 : add_group β) (f : Type).
Instance is_add_group_hom_to_is_add_hom (α : Type) (β : Type) `(_inst_1 : add_group α) `(_inst_2 : add_group β) (f : Type) `(c : @is_add_group_hom α β _inst_1 _inst_2 f) : @is_add_hom α β (@add_semigroup_to_has_add α (@add_monoid_to_add_semigroup α (@add_group_to_add_monoid α _inst_1))) (@add_semigroup_to_has_add β (@add_monoid_to_add_semigroup β (@add_group_to_add_monoid β _inst_2))) f := {}.
Instance is_extensional_of_is_strict_total_order' (α : Type) (r : Type) `(_inst_1 : is_strict_total_order' α r) : is_extensional α r := {}.
Class is_well_order (α : Type) (r : Type).
Instance is_well_order_to_is_strict_total_order' (α : Type) (r : Type) `(c : is_well_order α r) : is_strict_total_order' α r := {}.
Instance is_well_order_is_strict_total_order (α : Type) (r : Type) `(_inst_1 : is_well_order α r) : is_strict_total_order α r := {}.
Instance is_well_order_is_extensional (α : Type) (r : Type) `(_inst_1 : is_well_order α r) : is_extensional α r := {}.
Class is_group_hom (α : Type) (β : Type) `(_inst_1 : group α) `(_inst_2 : group β) (f : Type).
Instance is_well_order_is_trichotomous (α : Type) (r : Type) `(_inst_1 : is_well_order α r) : is_trichotomous α r := {}.
Instance is_well_order_is_trans (α : Type) (r : Type) `(_inst_1 : is_well_order α r) : is_trans α r := {}.
Instance is_well_order_is_irrefl (α : Type) (r : Type) `(_inst_1 : is_well_order α r) : is_irrefl α r := {}.
Instance is_well_order_is_asymm (α : Type) (r : Type) `(_inst_1 : is_well_order α r) : is_asymm α r := {}.
Instance is_group_hom_to_is_mul_hom (α : Type) (β : Type) `(_inst_1 : group α) `(_inst_2 : group β) (f : Type) `(c : @is_group_hom α β _inst_1 _inst_2 f) : @is_mul_hom α β (@semigroup_to_has_mul α (@monoid_to_semigroup α (@group_to_monoid α _inst_1))) (@semigroup_to_has_mul β (@monoid_to_semigroup β (@group_to_monoid β _inst_2))) f := {}.
Instance is_group_hom_to_is_monoid_hom (α : Type) (β : Type) `(_inst_1 : group α) `(_inst_2 : group β) (f : Type) `(_inst_3 : @is_group_hom α β _inst_1 _inst_2 f) : @is_monoid_hom α β (@group_to_monoid α _inst_1) (@group_to_monoid β _inst_2) f := {}.
Instance is_add_group_hom_to_is_add_monoid_hom (α : Type) (β : Type) `(_inst_1 : add_group α) `(_inst_2 : add_group β) (f : Type) `(_inst_3 : @is_add_group_hom α β _inst_1 _inst_2 f) : @is_add_monoid_hom α β (@add_group_to_add_monoid α _inst_1) (@add_group_to_add_monoid β _inst_2) f := {}.
Class directed_order (α : Type).
Instance directed_order_to_preorder (α : Type) `(c : directed_order α) : preorder α := {}.
Class lattice_has_sup (α : Type).
Class lattice_has_inf (α : Type).
Class lattice_semilattice_sup (α : Type).
Instance lattice_semilattice_sup_to_has_sup (α : Type) `(s : lattice_semilattice_sup α) : lattice_has_sup α := {}.
Instance lattice_semilattice_sup_to_partial_order (α : Type) `(s : lattice_semilattice_sup α) : partial_order α := {}.
Class lattice_semilattice_inf (α : Type).
Instance lattice_semilattice_inf_to_has_inf (α : Type) `(s : lattice_semilattice_inf α) : lattice_has_inf α := {}.
Instance lattice_semilattice_inf_to_partial_order (α : Type) `(s : lattice_semilattice_inf α) : partial_order α := {}.
Class lattice_lattice (α : Type).
Instance lattice_lattice_to_semilattice_sup (α : Type) `(s : lattice_lattice α) : lattice_semilattice_sup α := {}.
Instance lattice_lattice_to_semilattice_inf (α : Type) `(s : lattice_lattice α) : lattice_semilattice_inf α := {}.
Class lattice_distrib_lattice (α : Type).
Instance lattice_distrib_lattice_to_lattice (α : Type) `(s : lattice_distrib_lattice α) : lattice_lattice α := {}.
Instance lattice_lattice_of_decidable_linear_order (α : Type) `(o : decidable_linear_order α) : lattice_lattice α := {}.
Instance lattice_distrib_lattice_of_decidable_linear_order (α : Type) `(o : decidable_linear_order α) : lattice_distrib_lattice α := {}.
Class lattice_has_top (α : Type).
Class lattice_has_bot (α : Type).
Class lattice_order_top (α : Type).
Instance lattice_order_top_to_has_top (α : Type) `(s : lattice_order_top α) : lattice_has_top α := {}.
Instance lattice_order_top_to_partial_order (α : Type) `(s : lattice_order_top α) : partial_order α := {}.
Class lattice_order_bot (α : Type).
Instance lattice_order_bot_to_has_bot (α : Type) `(s : lattice_order_bot α) : lattice_has_bot α := {}.
Instance lattice_order_bot_to_partial_order (α : Type) `(s : lattice_order_bot α) : partial_order α := {}.
Class lattice_semilattice_sup_top (α : Type).
Instance lattice_semilattice_sup_top_to_order_top (α : Type) `(s : lattice_semilattice_sup_top α) : lattice_order_top α := {}.
Instance lattice_semilattice_sup_top_to_semilattice_sup (α : Type) `(s : lattice_semilattice_sup_top α) : lattice_semilattice_sup α := {}.
Class lattice_semilattice_sup_bot (α : Type).
Instance lattice_semilattice_sup_bot_to_order_bot (α : Type) `(s : lattice_semilattice_sup_bot α) : lattice_order_bot α := {}.
Instance lattice_semilattice_sup_bot_to_semilattice_sup (α : Type) `(s : lattice_semilattice_sup_bot α) : lattice_semilattice_sup α := {}.
Class lattice_semilattice_inf_top (α : Type).
Instance lattice_semilattice_inf_top_to_order_top (α : Type) `(s : lattice_semilattice_inf_top α) : lattice_order_top α := {}.
Instance lattice_semilattice_inf_top_to_semilattice_inf (α : Type) `(s : lattice_semilattice_inf_top α) : lattice_semilattice_inf α := {}.
Class lattice_semilattice_inf_bot (α : Type).
Instance lattice_semilattice_inf_bot_to_order_bot (α : Type) `(s : lattice_semilattice_inf_bot α) : lattice_order_bot α := {}.
Instance lattice_semilattice_inf_bot_to_semilattice_inf (α : Type) `(s : lattice_semilattice_inf_bot α) : lattice_semilattice_inf α := {}.
Class lattice_bounded_lattice (α : Type).
Instance lattice_bounded_lattice_to_lattice (α : Type) `(s : lattice_bounded_lattice α) : lattice_lattice α := {}.
Instance lattice_bounded_lattice_to_order_top (α : Type) `(s : lattice_bounded_lattice α) : lattice_order_top α := {}.
Instance lattice_bounded_lattice_to_order_bot (α : Type) `(s : lattice_bounded_lattice α) : lattice_order_bot α := {}.
Instance lattice_semilattice_inf_top_of_bounded_lattice (α : Type) `(bl : lattice_bounded_lattice α) : lattice_semilattice_inf_top α := {}.
Instance lattice_semilattice_inf_bot_of_bounded_lattice (α : Type) `(bl : lattice_bounded_lattice α) : lattice_semilattice_inf_bot α := {}.
Instance lattice_semilattice_sup_top_of_bounded_lattice (α : Type) `(bl : lattice_bounded_lattice α) : lattice_semilattice_sup_top α := {}.
Instance lattice_semilattice_sup_bot_of_bounded_lattice (α : Type) `(bl : lattice_bounded_lattice α) : lattice_semilattice_sup_bot α := {}.
Class lattice_bounded_distrib_lattice (α : Type).
Instance lattice_bounded_distrib_lattice_to_distrib_lattice (α : Type) `(s : lattice_bounded_distrib_lattice α) : lattice_distrib_lattice α := {}.
Instance lattice_bounded_distrib_lattice_to_bounded_lattice (α : Type) `(s : lattice_bounded_distrib_lattice α) : lattice_bounded_lattice α := {}.
Class category_theory_concrete_category (C : Type).
Instance category_theory_concrete_category_to_category (C : Type) `(c : category_theory_concrete_category C) : category_theory_category C := {}.
Class category_theory_has_forget₂ (C : Type) (D : Type) `(_inst_1 : category_theory_concrete_category C) `(_inst_2 : category_theory_concrete_category D).
Class category_theory_bundled_hom (c : Type) (hom : Type).
Class category_theory_unbundled_hom (c : Type) (hom : Type).
Class lattice_has_Sup (α : Type).
Class lattice_has_Inf (α : Type).
Class lattice_boolean_algebra (α : Type).
Instance lattice_boolean_algebra_to_bounded_distrib_lattice (α : Type) `(s : lattice_boolean_algebra α) : lattice_bounded_distrib_lattice α := {}.
Instance lattice_boolean_algebra_to_has_neg (α : Type) `(s : lattice_boolean_algebra α) : has_neg α := {}.
Instance lattice_boolean_algebra_to_has_sub (α : Type) `(s : lattice_boolean_algebra α) : has_sub α := {}.
Class lattice_complete_lattice (α : Type).
Instance lattice_complete_lattice_to_bounded_lattice (α : Type) `(s : lattice_complete_lattice α) : lattice_bounded_lattice α := {}.
Instance lattice_complete_lattice_to_has_Sup (α : Type) `(s : lattice_complete_lattice α) : lattice_has_Sup α := {}.
Instance lattice_complete_lattice_to_has_Inf (α : Type) `(s : lattice_complete_lattice α) : lattice_has_Inf α := {}.
Class lattice_complete_linear_order (α : Type).
Instance lattice_complete_linear_order_to_complete_lattice (α : Type) `(s : lattice_complete_linear_order α) : lattice_complete_lattice α := {}.
Instance lattice_complete_linear_order_to_decidable_linear_order (α : Type) `(s : lattice_complete_linear_order α) : decidable_linear_order α := {}.
Class ordered_comm_monoid (α : Type).
Instance ordered_comm_monoid_to_add_comm_monoid (α : Type) `(s : ordered_comm_monoid α) : add_comm_monoid α := {}.
Instance ordered_comm_monoid_to_partial_order (α : Type) `(s : ordered_comm_monoid α) : partial_order α := {}.
Class canonically_ordered_monoid (α : Type).
Instance canonically_ordered_monoid_to_ordered_comm_monoid (α : Type) `(s : canonically_ordered_monoid α) : ordered_comm_monoid α := {}.
Instance canonically_ordered_monoid_to_order_bot (α : Type) `(s : canonically_ordered_monoid α) : lattice_order_bot α := {}.
Class category_theory_is_equivalence (C : Type) `(𝒞 : category_theory_category C) (D : Type) `(𝒟 : category_theory_category D) (F : Type).
Class is_semiring_hom (α : Type) (β : Type) `(_inst_1 : semiring α) `(_inst_2 : semiring β) (f : Type).
Class category_theory_ess_surj (C : Type) `(𝒞 : category_theory_category C) (D : Type) `(𝒟 : category_theory_category D) (F : Type).
Instance is_semiring_hom_is_add_monoid_hom (α : Type) (β : Type) `(_inst_1 : semiring α) `(_inst_2 : semiring β) (f : Type) `(_inst_3 : @is_semiring_hom α β _inst_1 _inst_2 f) : @is_add_monoid_hom α β (@add_comm_monoid_to_add_monoid α (@semiring_to_add_comm_monoid α _inst_1)) (@add_comm_monoid_to_add_monoid β (@semiring_to_add_comm_monoid β _inst_2)) f := {}.
Instance is_semiring_hom_is_monoid_hom (α : Type) (β : Type) `(_inst_1 : semiring α) `(_inst_2 : semiring β) (f : Type) `(_inst_3 : @is_semiring_hom α β _inst_1 _inst_2 f) : @is_monoid_hom α β (@semiring_to_monoid α _inst_1) (@semiring_to_monoid β _inst_2) f := {}.
Instance category_theory_equivalence_faithful_of_equivalence (C : Type) `(𝒞 : category_theory_category C) (D : Type) `(𝒟 : category_theory_category D) (F : Type) `(_inst_1 : @category_theory_is_equivalence C 𝒞 D 𝒟 F) : @category_theory_faithful C 𝒞 D 𝒟 F := {}.
Class is_ring_hom (α : Type) (β : Type) `(_inst_1 : ring α) `(_inst_2 : ring β) (f : Type).
Instance is_ring_hom_is_semiring_hom (α : Type) (β : Type) `(_inst_1 : ring α) `(_inst_2 : ring β) (f : Type) `(_inst_3 : @is_ring_hom α β _inst_1 _inst_2 f) : @is_semiring_hom α β (@ring_to_semiring α _inst_1) (@ring_to_semiring β _inst_2) f := {}.
Instance is_ring_hom_is_add_group_hom (α : Type) (β : Type) `(_inst_1 : ring α) `(_inst_2 : ring β) (f : Type) `(_inst_3 : @is_ring_hom α β _inst_1 _inst_2 f) : @is_add_group_hom α β (@add_comm_group_to_add_group α (@ring_to_add_comm_group α _inst_1)) (@add_comm_group_to_add_group β (@ring_to_add_comm_group β _inst_2)) f := {}.
Instance category_theory_equivalence_full_of_equivalence (C : Type) `(𝒞 : category_theory_category C) (D : Type) `(𝒟 : category_theory_category D) (F : Type) `(_inst_1 : @category_theory_is_equivalence C 𝒞 D 𝒟 F) : @category_theory_full C 𝒞 D 𝒟 F := {}.
Class nonzero_comm_semiring (α : Type).
Instance nonzero_comm_semiring_to_comm_semiring (α : Type) `(s : nonzero_comm_semiring α) : comm_semiring α := {}.
Instance nonzero_comm_semiring_to_zero_ne_one_class (α : Type) `(s : nonzero_comm_semiring α) : zero_ne_one_class α := {}.
Class nonzero_comm_ring (α : Type).
Instance nonzero_comm_ring_to_comm_ring (α : Type) `(s : nonzero_comm_ring α) : comm_ring α := {}.
Instance nonzero_comm_ring_to_zero_ne_one_class (α : Type) `(s : nonzero_comm_ring α) : zero_ne_one_class α := {}.
Instance nonzero_comm_ring_to_nonzero_comm_semiring (α : Type) `(I : nonzero_comm_ring α) : nonzero_comm_semiring α := {}.
Instance integral_domain_to_nonzero_comm_ring (α : Type) `(id : integral_domain α) : nonzero_comm_ring α := {}.
Class domain (α : Type).
Instance domain_to_ring (α : Type) `(s : domain α) : ring α := {}.
Instance domain_to_no_zero_divisors (α : Type) `(s : domain α) : no_zero_divisors α := {}.
Instance domain_to_zero_ne_one_class (α : Type) `(s : domain α) : zero_ne_one_class α := {}.
Class lattice_complete_distrib_lattice (α : Type).
Instance integral_domain_to_domain (α : Type) `(s : integral_domain α) : domain α := {}.
Instance lattice_complete_distrib_lattice_to_complete_lattice (α : Type) `(s : lattice_complete_distrib_lattice α) : lattice_complete_lattice α := {}.
Class category_theory_is_left_adjoint (C : Type) `(𝒞 : category_theory_category C) (D : Type) `(𝒟 : category_theory_category D) (left : Type).
Class category_theory_is_right_adjoint (C : Type) `(𝒞 : category_theory_category C) (D : Type) `(𝒟 : category_theory_category D) (right : Type).
Instance lattice_lattice_bounded_distrib_lattice (α : Type) `(d : lattice_complete_distrib_lattice α) : lattice_bounded_distrib_lattice α := {}.
Class lattice_complete_boolean_algebra (α : Type).
Instance lattice_complete_boolean_algebra_to_boolean_algebra (α : Type) `(s : lattice_complete_boolean_algebra α) : lattice_boolean_algebra α := {}.
Instance lattice_complete_boolean_algebra_to_complete_distrib_lattice (α : Type) `(s : lattice_complete_boolean_algebra α) : lattice_complete_distrib_lattice α := {}.
Instance division_ring_has_div' (α : Type) `(_inst_1 : division_ring α) : has_div α := {}.
Instance ordered_cancel_comm_monoid_to_ordered_comm_monoid (α : Type) `(H : ordered_cancel_comm_monoid α) : ordered_comm_monoid α := {}.
Instance division_ring_to_domain (α : Type) `(s : division_ring α) : domain α := {}.
Instance field_to_integral_domain (α : Type) `(F : field α) : integral_domain α := {}.
Instance decidable_linear_ordered_comm_group_decidable_linear_ordered_cancel_comm_monoid (α : Type) `(s : decidable_linear_ordered_comm_group α) : decidable_linear_ordered_cancel_comm_monoid α := {}.
Class nonneg_comm_group (α : Type).
Instance nonneg_comm_group_to_add_comm_group (α : Type) `(s : nonneg_comm_group α) : add_comm_group α := {}.
Instance nonneg_comm_group_to_ordered_comm_group (α : Type) `(s : nonneg_comm_group α) : ordered_comm_group α := {}.
Class char_zero (α : Type) `(_inst_1 : add_monoid α) `(_inst_2 : has_one α).
Instance linear_ordered_semiring_to_char_zero (α : Type) `(_inst_1 : linear_ordered_semiring α) : @char_zero α (@add_comm_monoid_to_add_monoid α (@ordered_comm_monoid_to_add_comm_monoid α (@ordered_cancel_comm_monoid_to_ordered_comm_monoid α (@ordered_semiring_to_ordered_cancel_comm_monoid α (@linear_ordered_semiring_to_ordered_semiring α _inst_1))))) (@monoid_to_has_one α (@semiring_to_monoid α (@ordered_semiring_to_semiring α (@linear_ordered_semiring_to_ordered_semiring α _inst_1)))) := {}.
Instance linear_ordered_semiring_to_no_top_order (α : Type) `(_inst_1 : linear_ordered_semiring α) : @no_top_order α (@partial_order_to_preorder α (@ordered_comm_monoid_to_partial_order α (@ordered_cancel_comm_monoid_to_ordered_comm_monoid α (@ordered_semiring_to_ordered_cancel_comm_monoid α (@linear_ordered_semiring_to_ordered_semiring α _inst_1))))) := {}.
Instance linear_ordered_semiring_to_no_bot_order (α : Type) `(_inst_1 : linear_ordered_ring α) : @no_bot_order α (@partial_order_to_preorder α (@ordered_comm_monoid_to_partial_order α (@ordered_cancel_comm_monoid_to_ordered_comm_monoid α (@ordered_semiring_to_ordered_cancel_comm_monoid α (@ordered_ring_to_ordered_semiring α (@linear_ordered_ring_to_ordered_ring α _inst_1)))))) := {}.
Instance to_domain (α : Type) `(s : linear_ordered_ring α) : domain α := {}.
Class nonneg_ring (α : Type).
Instance nonneg_ring_to_ring (α : Type) `(s : nonneg_ring α) : ring α := {}.
Instance nonneg_ring_to_zero_ne_one_class (α : Type) `(s : nonneg_ring α) : zero_ne_one_class α := {}.
Instance nonneg_ring_to_nonneg_comm_group (α : Type) `(s : nonneg_ring α) : nonneg_comm_group α := {}.
Class category_theory_monoidal_category (C : Type) `(𝒞 : category_theory_category C).
Class linear_nonneg_ring (α : Type).
Instance linear_nonneg_ring_to_domain (α : Type) `(s : linear_nonneg_ring α) : domain α := {}.
Instance linear_nonneg_ring_to_nonneg_comm_group (α : Type) `(s : linear_nonneg_ring α) : nonneg_comm_group α := {}.
Instance nonneg_ring_to_ordered_ring (α : Type) `(s : nonneg_ring α) : ordered_ring α := {}.
Instance linear_nonneg_ring_to_nonneg_ring (α : Type) `(s : linear_nonneg_ring α) : nonneg_ring α := {}.
Instance linear_nonneg_ring_to_linear_order (α : Type) `(s : linear_nonneg_ring α) : linear_order α := {}.
Instance linear_nonneg_ring_to_linear_ordered_ring (α : Type) `(s : linear_nonneg_ring α) : linear_ordered_ring α := {}.
Class canonically_ordered_comm_semiring (α : Type).
Instance canonically_ordered_comm_semiring_to_canonically_ordered_monoid (α : Type) `(s : canonically_ordered_comm_semiring α) : canonically_ordered_monoid α := {}.
Instance canonically_ordered_comm_semiring_to_comm_semiring (α : Type) `(s : canonically_ordered_comm_semiring α) : comm_semiring α := {}.
Instance canonically_ordered_comm_semiring_to_zero_ne_one_class (α : Type) `(s : canonically_ordered_comm_semiring α) : zero_ne_one_class α := {}.
Instance linear_ordered_field_to_densely_ordered (α : Type) `(_inst_1 : linear_ordered_field α) : @densely_ordered α (@partial_order_to_preorder α (@ordered_comm_monoid_to_partial_order α (@ordered_cancel_comm_monoid_to_ordered_comm_monoid α (@ordered_semiring_to_ordered_cancel_comm_monoid α (@ordered_ring_to_ordered_semiring α (@linear_ordered_ring_to_ordered_ring α (@linear_ordered_field_to_linear_ordered_ring α _inst_1))))))) := {}.
Instance linear_ordered_field_to_no_top_order (α : Type) `(_inst_1 : linear_ordered_field α) : @no_top_order α (@partial_order_to_preorder α (@ordered_comm_monoid_to_partial_order α (@ordered_cancel_comm_monoid_to_ordered_comm_monoid α (@ordered_semiring_to_ordered_cancel_comm_monoid α (@ordered_ring_to_ordered_semiring α (@linear_ordered_ring_to_ordered_ring α (@linear_ordered_field_to_linear_ordered_ring α _inst_1))))))) := {}.
Instance linear_ordered_field_to_no_bot_order (α : Type) `(_inst_1 : linear_ordered_field α) : @no_bot_order α (@partial_order_to_preorder α (@ordered_comm_monoid_to_partial_order α (@ordered_cancel_comm_monoid_to_ordered_comm_monoid α (@ordered_semiring_to_ordered_cancel_comm_monoid α (@ordered_ring_to_ordered_semiring α (@linear_ordered_ring_to_ordered_ring α (@linear_ordered_field_to_linear_ordered_ring α _inst_1))))))) := {}.
Class category_theory_representable (C : Type) `(𝒞 : category_theory_category C) (F : Type).
Class is_ring_anti_hom (R : Type) (F : Type) `(_inst_1 : ring R) `(_inst_2 : ring F) (f : Type).
Instance is_ring_anti_hom_is_add_group_hom (R : Type) (F : Type) `(_inst_1 : ring R) `(_inst_2 : ring F) (f : Type) `(_inst_3 : @is_ring_anti_hom R F _inst_1 _inst_2 f) : @is_add_group_hom R F (@add_comm_group_to_add_group R (@ring_to_add_comm_group R _inst_1)) (@add_comm_group_to_add_group F (@ring_to_add_comm_group F _inst_2)) f := {}.
Class category_theory_reflective (C : Type) `(𝒞 : category_theory_category C) (D : Type) `(𝒟 : category_theory_category D) (R : Type).
Instance category_theory_reflective_to_is_right_adjoint (C : Type) `(𝒞 : category_theory_category C) (D : Type) `(𝒟 : category_theory_category D) (R : Type) `(c : @category_theory_reflective C 𝒞 D 𝒟 R) : @category_theory_is_right_adjoint C 𝒞 D 𝒟 R := {}.
Instance category_theory_reflective_to_full (C : Type) `(𝒞 : category_theory_category C) (D : Type) `(𝒟 : category_theory_category D) (R : Type) `(c : @category_theory_reflective C 𝒞 D 𝒟 R) : @category_theory_full D 𝒟 C 𝒞 R := {}.
Instance category_theory_reflective_to_faithful (C : Type) `(𝒞 : category_theory_category C) (D : Type) `(𝒟 : category_theory_category D) (R : Type) `(c : @category_theory_reflective C 𝒞 D 𝒟 R) : @category_theory_faithful D 𝒟 C 𝒞 R := {}.
Class category_theory_monadic_right_adjoint (C : Type) `(𝒞 : category_theory_category C) (D : Type) `(𝒟 : category_theory_category D) (R : Type).
Instance category_theory_monadic_right_adjoint_to_is_right_adjoint (C : Type) `(𝒞 : category_theory_category C) (D : Type) `(𝒟 : category_theory_category D) (R : Type) `(c : @category_theory_monadic_right_adjoint C 𝒞 D 𝒟 R) : @category_theory_is_right_adjoint C 𝒞 D 𝒟 R := {}.
Instance category_theory_monadic_of_reflective (C : Type) `(𝒞 : category_theory_category C) (D : Type) `(𝒟 : category_theory_category D) (R : Type) `(_inst_1 : @category_theory_reflective C 𝒞 D 𝒟 R) : @category_theory_monadic_right_adjoint C 𝒞 D 𝒟 R := {}.
Class wseq_is_finite (α : Type) (s : Type).
Class wseq_productive (α : Type) (s : Type).
Class euclidean_domain (α : Type).
Instance euclidean_domain_to_nonzero_comm_ring (α : Type) `(c : euclidean_domain α) : nonzero_comm_ring α := {}.
Instance euclidean_domain_has_div (α : Type) `(_inst_1 : euclidean_domain α) : has_div α := {}.
Instance euclidean_domain_has_mod (α : Type) `(_inst_1 : euclidean_domain α) : has_mod α := {}.
Class category_theory_limits_has_limit (J : Type) `(_inst_1 : category_theory_category J) (C : Type) `(𝒞 : category_theory_category C) (F : Type).
Class category_theory_limits_has_limits_of_shape (J : Type) `(_inst_1 : category_theory_category J) (C : Type) `(𝒞 : category_theory_category C).
Class category_theory_limits_has_limits (C : Type) `(𝒞 : category_theory_category C).
Instance category_theory_limits_has_limit_of_has_limits_of_shape (C : Type) `(𝒞 : category_theory_category C) (J : Type) `(_inst_3 : category_theory_category J) `(H : @category_theory_limits_has_limits_of_shape J _inst_3 C 𝒞) (F : Type) : @category_theory_limits_has_limit J _inst_3 C 𝒞 F := {}.
Instance category_theory_limits_has_limits_of_shape_of_has_limits (C : Type) `(𝒞 : category_theory_category C) (J : Type) `(_inst_3 : category_theory_category J) `(H : @category_theory_limits_has_limits C 𝒞) : @category_theory_limits_has_limits_of_shape J _inst_3 C 𝒞 := {}.
Instance euclidean_domain_integral_domain (α : Type) `(e : euclidean_domain α) : integral_domain α := {}.
Instance discrete_field_to_euclidean_domain (K : Type) `(_inst_1 : discrete_field K) : euclidean_domain K := {}.
Class category_theory_limits_has_colimit (J : Type) `(_inst_1 : category_theory_category J) (C : Type) `(𝒞 : category_theory_category C) (F : Type).
Class category_theory_limits_has_colimits_of_shape (J : Type) `(_inst_1 : category_theory_category J) (C : Type) `(𝒞 : category_theory_category C).
Class category_theory_limits_has_colimits (C : Type) `(𝒞 : category_theory_category C).
Instance category_theory_limits_has_colimit_of_has_colimits_of_shape (C : Type) `(𝒞 : category_theory_category C) (J : Type) `(_inst_3 : category_theory_category J) `(H : @category_theory_limits_has_colimits_of_shape J _inst_3 C 𝒞) (F : Type) : @category_theory_limits_has_colimit J _inst_3 C 𝒞 F := {}.
Instance category_theory_limits_has_colimits_of_shape_of_has_colimits (C : Type) `(𝒞 : category_theory_category C) (J : Type) `(_inst_3 : category_theory_category J) `(H : @category_theory_limits_has_colimits C 𝒞) : @category_theory_limits_has_colimits_of_shape J _inst_3 C 𝒞 := {}.
Class encodable (α : Type).
Class category_theory_limits_preserves_limit (C : Type) `(𝒞 : category_theory_category C) (D : Type) `(𝒟 : category_theory_category D) (J : Type) `(_inst_1 : category_theory_category J) (K : Type) (F : Type).
Class category_theory_limits_preserves_colimit (C : Type) `(𝒞 : category_theory_category C) (D : Type) `(𝒟 : category_theory_category D) (J : Type) `(_inst_1 : category_theory_category J) (K : Type) (F : Type).
Class category_theory_limits_preserves_limits_of_shape (C : Type) `(𝒞 : category_theory_category C) (D : Type) `(𝒟 : category_theory_category D) (J : Type) `(_inst_2 : category_theory_category J) (F : Type).
Class category_theory_limits_preserves_colimits_of_shape (C : Type) `(𝒞 : category_theory_category C) (D : Type) `(𝒟 : category_theory_category D) (J : Type) `(_inst_2 : category_theory_category J) (F : Type).
Class category_theory_limits_preserves_limits (C : Type) `(𝒞 : category_theory_category C) (D : Type) `(𝒟 : category_theory_category D) (F : Type).
Instance category_theory_limits_has_limits_of_complete_lattice (α : Type) `(_inst_1 : lattice_complete_lattice α) : @category_theory_limits_has_limits α (@preorder_small_category α (@partial_order_to_preorder α (@lattice_order_bot_to_partial_order α (@lattice_bounded_lattice_to_order_bot α (@lattice_complete_lattice_to_bounded_lattice α _inst_1))))) := {}.
Class category_theory_limits_preserves_colimits (C : Type) `(𝒞 : category_theory_category C) (D : Type) `(𝒟 : category_theory_category D) (F : Type).
Instance category_theory_limits_preserves_limits_of_shape_preserves_limit (C : Type) `(𝒞 : category_theory_category C) (D : Type) `(𝒟 : category_theory_category D) (J : Type) `(_inst_2 : category_theory_category J) (F : Type) `(c : @category_theory_limits_preserves_limits_of_shape C 𝒞 D 𝒟 J _inst_2 F) (K : Type) : @category_theory_limits_preserves_limit C 𝒞 D 𝒟 J _inst_2 K F := {}.
Instance category_theory_limits_preserves_limits_preserves_limits_of_shape (C : Type) `(𝒞 : category_theory_category C) (D : Type) `(𝒟 : category_theory_category D) (F : Type) `(c : @category_theory_limits_preserves_limits C 𝒞 D 𝒟 F) (J : Type) `(𝒥 : category_theory_category J) : @category_theory_limits_preserves_limits_of_shape C 𝒞 D 𝒟 J 𝒥 F := {}.
Instance category_theory_limits_preserves_colimits_of_shape_preserves_colimit (C : Type) `(𝒞 : category_theory_category C) (D : Type) `(𝒟 : category_theory_category D) (J : Type) `(_inst_2 : category_theory_category J) (F : Type) `(c : @category_theory_limits_preserves_colimits_of_shape C 𝒞 D 𝒟 J _inst_2 F) (K : Type) : @category_theory_limits_preserves_colimit C 𝒞 D 𝒟 J _inst_2 K F := {}.
Instance category_theory_limits_preserves_colimits_preserves_colimits_of_shape (C : Type) `(𝒞 : category_theory_category C) (D : Type) `(𝒟 : category_theory_category D) (F : Type) `(c : @category_theory_limits_preserves_colimits C 𝒞 D 𝒟 F) (J : Type) `(𝒥 : category_theory_category J) : @category_theory_limits_preserves_colimits_of_shape C 𝒞 D 𝒟 J 𝒥 F := {}.
Instance category_theory_limits_has_colimits_of_complete_lattice (α : Type) `(_inst_1 : lattice_complete_lattice α) : @category_theory_limits_has_colimits α (@preorder_small_category α (@partial_order_to_preorder α (@lattice_order_bot_to_partial_order α (@lattice_bounded_lattice_to_order_bot α (@lattice_complete_lattice_to_bounded_lattice α _inst_1))))) := {}.
Class category_theory_limits_reflects_limit (C : Type) `(𝒞 : category_theory_category C) (D : Type) `(𝒟 : category_theory_category D) (J : Type) `(_inst_1 : category_theory_category J) (K : Type) (F : Type).
Class category_theory_limits_reflects_colimit (C : Type) `(𝒞 : category_theory_category C) (D : Type) `(𝒟 : category_theory_category D) (J : Type) `(_inst_1 : category_theory_category J) (K : Type) (F : Type).
Class category_theory_limits_reflects_limits_of_shape (C : Type) `(𝒞 : category_theory_category C) (D : Type) `(𝒟 : category_theory_category D) (J : Type) `(_inst_2 : category_theory_category J) (F : Type).
Class category_theory_limits_reflects_colimits_of_shape (C : Type) `(𝒞 : category_theory_category C) (D : Type) `(𝒟 : category_theory_category D) (J : Type) `(_inst_2 : category_theory_category J) (F : Type).
Class category_theory_limits_reflects_limits (C : Type) `(𝒞 : category_theory_category C) (D : Type) `(𝒟 : category_theory_category D) (F : Type).
Class category_theory_limits_reflects_colimits (C : Type) `(𝒞 : category_theory_category C) (D : Type) `(𝒟 : category_theory_category D) (F : Type).
Instance category_theory_limits_reflects_limit_of_reflects_limits_of_shape (C : Type) `(𝒞 : category_theory_category C) (D : Type) `(𝒟 : category_theory_category D) (J : Type) `(_inst_1 : category_theory_category J) (K : Type) (F : Type) `(H : @category_theory_limits_reflects_limits_of_shape C 𝒞 D 𝒟 J _inst_1 F) : @category_theory_limits_reflects_limit C 𝒞 D 𝒟 J _inst_1 K F := {}.
Instance category_theory_limits_reflects_colimit_of_reflects_colimits_of_shape (C : Type) `(𝒞 : category_theory_category C) (D : Type) `(𝒟 : category_theory_category D) (J : Type) `(_inst_1 : category_theory_category J) (K : Type) (F : Type) `(H : @category_theory_limits_reflects_colimits_of_shape C 𝒞 D 𝒟 J _inst_1 F) : @category_theory_limits_reflects_colimit C 𝒞 D 𝒟 J _inst_1 K F := {}.
Instance category_theory_limits_reflects_limits_of_shape_of_reflects_limits (C : Type) `(𝒞 : category_theory_category C) (D : Type) `(𝒟 : category_theory_category D) (J : Type) `(_inst_1 : category_theory_category J) (F : Type) `(H : @category_theory_limits_reflects_limits C 𝒞 D 𝒟 F) : @category_theory_limits_reflects_limits_of_shape C 𝒞 D 𝒟 J _inst_1 F := {}.
Instance category_theory_limits_reflects_colimits_of_shape_of_reflects_colimits (C : Type) `(𝒞 : category_theory_category C) (D : Type) `(𝒟 : category_theory_category D) (J : Type) `(_inst_1 : category_theory_category J) (F : Type) `(H : @category_theory_limits_reflects_colimits C 𝒞 D 𝒟 F) : @category_theory_limits_reflects_colimits_of_shape C 𝒞 D 𝒟 J _inst_1 F := {}.
Instance category_theory_adjunction_left_adjoint_preserves_colimits (C : Type) `(𝒞 : category_theory_category C) (D : Type) `(𝒟 : category_theory_category D) (F : Type) (G : Type) (adj : Type) : @category_theory_limits_preserves_colimits C 𝒞 D 𝒟 F := {}.
Instance category_theory_adjunction_is_equivalence_preserves_colimits (C : Type) `(𝒞 : category_theory_category C) (D : Type) `(𝒟 : category_theory_category D) (E : Type) `(_inst_2 : @category_theory_is_equivalence C 𝒞 D 𝒟 E) : @category_theory_limits_preserves_colimits C 𝒞 D 𝒟 E := {}.
Class irreducible (α : Type) `(_inst_1 : monoid α) (p : Type).
Class floor_ring (α : Type) `(_inst_1 : linear_ordered_ring α).
Class archimedean (α : Type) `(_inst_1 : ordered_comm_monoid α).
Class normalization_domain (α : Type).
Instance normalization_domain_to_integral_domain (α : Type) `(s : normalization_domain α) : integral_domain α := {}.
Class gcd_domain (α : Type).
Instance gcd_domain_to_normalization_domain (α : Type) `(s : gcd_domain α) : normalization_domain α := {}.
Instance category_theory_adjunction_right_adjoint_preserves_limits (C : Type) `(𝒞 : category_theory_category C) (D : Type) `(𝒟 : category_theory_category D) (F : Type) (G : Type) (adj : Type) : @category_theory_limits_preserves_limits D 𝒟 C 𝒞 G := {}.
Instance category_theory_adjunction_is_equivalence_preserves_limits (C : Type) `(𝒞 : category_theory_category C) (D : Type) `(𝒟 : category_theory_category D) (E : Type) `(_inst_2 : @category_theory_is_equivalence D 𝒟 C 𝒞 E) : @category_theory_limits_preserves_limits D 𝒟 C 𝒞 E := {}.
Class unique_factorization_domain (α : Type) `(_inst_1 : integral_domain α).
Class zsqrtd_nonsquare (x : Type).
Class fin2_is_lt (m : Type) (n : Type).
Class is_add_submonoid (β : Type) `(_inst_2 : add_monoid β) (s : Type).
Class is_submonoid (α : Type) `(_inst_1 : monoid α) (s : Type).
Class is_absolute_value (α : Type) `(_inst_1 : discrete_linear_ordered_field α) (β : Type) `(_inst_2 : ring β) (f : Type).
Class fintype (α : Type).
Instance unique_fintype (α : Type) `(_inst_1 : unique α) : fintype α := {}.
Class nat_prime (p : Type).
Class cau_seq_is_complete (α : Type) `(_inst_1 : discrete_linear_ordered_field α) (β : Type) `(_inst_2 : ring β) (abv : Type) `(_inst_3 : is_absolute_value abv).
Class is_add_subgroup (β : Type) `(_inst_2 : add_group β) (s : Type).
Instance is_add_subgroup_to_is_add_submonoid (β : Type) `(_inst_2 : add_group β) (s : Type) `(c : @is_add_subgroup β _inst_2 s) : @is_add_submonoid β (@add_group_to_add_monoid β _inst_2) s := {}.
Class is_subgroup (α : Type) `(_inst_1 : group α) (s : Type).
Instance is_subgroup_to_is_submonoid (α : Type) `(_inst_1 : group α) (s : Type) `(c : @is_subgroup α _inst_1 s) : @is_submonoid α (@group_to_monoid α _inst_1) s := {}.
Class infinite (α : Type).
Instance infinite_nonempty (α : Type) `(_inst_1 : infinite α) : nonempty α := {}.
Class denumerable (α : Type).
Instance denumerable_to_encodable (α : Type) `(c : denumerable α) : encodable α := {}.
Class turing_pointed_map (Γ : Type) (Γ' : Type) `(_inst_1 : inhabited Γ) `(_inst_2 : inhabited Γ') (f : Type).
Class normal_add_subgroup (α : Type) `(_inst_1 : add_group α) (s : Type).
Instance normal_add_subgroup_to_is_add_subgroup (α : Type) `(_inst_1 : add_group α) (s : Type) `(c : @normal_add_subgroup α _inst_1 s) : @is_add_subgroup α _inst_1 s := {}.
Class normal_subgroup (α : Type) `(_inst_1 : group α) (s : Type).
Instance normal_subgroup_to_is_subgroup (α : Type) `(_inst_1 : group α) (s : Type) `(c : @normal_subgroup α _inst_1 s) : @is_subgroup α _inst_1 s := {}.
Class category_theory_limits_has_products (C : Type) `(𝒞 : category_theory_category C).
Class category_theory_limits_has_coproducts (C : Type) `(𝒞 : category_theory_category C).
Class category_theory_limits_fin_category (J : Type) `(_inst_1 : category_theory_category J).
Instance category_theory_limits_fin_category_fintype_obj (J : Type) `(_inst_1 : category_theory_category J) `(c : @category_theory_limits_fin_category J _inst_1) : fintype J := {}.
Class category_theory_limits_has_finite_limits (C : Type) `(𝒞 : category_theory_category C).
Class category_theory_limits_has_finite_colimits (C : Type) `(𝒞 : category_theory_category C).
Instance category_theory_limits_has_finite_limits_has_limits_of_shape (C : Type) `(𝒞 : category_theory_category C) `(c : @category_theory_limits_has_finite_limits C 𝒞) (J : Type) `(_inst_1 : category_theory_category J) `(_inst_2 : @category_theory_limits_fin_category J _inst_1) : @category_theory_limits_has_limits_of_shape J _inst_1 C 𝒞 := {}.
Instance category_theory_limits_has_finite_colimits_has_colimits_of_shape (C : Type) `(𝒞 : category_theory_category C) `(c : @category_theory_limits_has_finite_colimits C 𝒞) (J : Type) `(_inst_1 : category_theory_category J) `(_inst_2 : @category_theory_limits_fin_category J _inst_1) : @category_theory_limits_has_colimits_of_shape J _inst_1 C 𝒞 := {}.
Instance category_theory_limits_category_theory_limits_has_finite_limits (C : Type) `(𝒞 : category_theory_category C) `(_inst_1 : @category_theory_limits_has_limits C 𝒞) : @category_theory_limits_has_finite_limits C 𝒞 := {}.
Instance category_theory_limits_category_theory_limits_has_finite_colimits (C : Type) `(𝒞 : category_theory_category C) `(_inst_1 : @category_theory_limits_has_colimits C 𝒞) : @category_theory_limits_has_finite_colimits C 𝒞 := {}.
Class category_theory_limits_has_finite_products (C : Type) `(𝒞 : category_theory_category C).
Class category_theory_limits_has_finite_coproducts (C : Type) `(𝒞 : category_theory_category C).
Instance category_theory_limits_has_finite_products_of_has_products (C : Type) `(𝒞 : category_theory_category C) `(_inst_1 : @category_theory_limits_has_products C 𝒞) : @category_theory_limits_has_finite_products C 𝒞 := {}.
Instance category_theory_limits_has_finite_coproducts_of_has_coproducts (C : Type) `(𝒞 : category_theory_category C) `(_inst_1 : @category_theory_limits_has_coproducts C 𝒞) : @category_theory_limits_has_finite_coproducts C 𝒞 := {}.
Instance category_theory_limits_has_finite_products_of_has_finite_limits (C : Type) `(𝒞 : category_theory_category C) `(_inst_1 : @category_theory_limits_has_finite_limits C 𝒞) : @category_theory_limits_has_finite_products C 𝒞 := {}.
Instance category_theory_limits_has_finite_coproducts_of_has_finite_colimits (C : Type) `(𝒞 : category_theory_category C) `(_inst_1 : @category_theory_limits_has_finite_colimits C 𝒞) : @category_theory_limits_has_finite_coproducts C 𝒞 := {}.
Class category_theory_limits_has_terminal (C : Type) `(𝒞 : category_theory_category C).
Class category_theory_limits_has_initial (C : Type) `(𝒞 : category_theory_category C).
Instance category_theory_limits_category_theory_limits_has_terminal (C : Type) `(𝒞 : category_theory_category C) `(_inst_1 : @category_theory_limits_has_finite_products C 𝒞) : @category_theory_limits_has_terminal C 𝒞 := {}.
Instance category_theory_limits_category_theory_limits_has_initial (C : Type) `(𝒞 : category_theory_category C) `(_inst_1 : @category_theory_limits_has_finite_coproducts C 𝒞) : @category_theory_limits_has_initial C 𝒞 := {}.
Class lattice_conditionally_complete_lattice (α : Type).
Instance lattice_conditionally_complete_lattice_to_lattice (α : Type) `(s : lattice_conditionally_complete_lattice α) : lattice_lattice α := {}.
Instance lattice_conditionally_complete_lattice_to_has_Sup (α : Type) `(s : lattice_conditionally_complete_lattice α) : lattice_has_Sup α := {}.
Instance lattice_conditionally_complete_lattice_to_has_Inf (α : Type) `(s : lattice_conditionally_complete_lattice α) : lattice_has_Inf α := {}.
Class lattice_conditionally_complete_linear_order (α : Type).
Instance lattice_conditionally_complete_linear_order_to_conditionally_complete_lattice (α : Type) `(s : lattice_conditionally_complete_linear_order α) : lattice_conditionally_complete_lattice α := {}.
Instance lattice_conditionally_complete_linear_order_to_decidable_linear_order (α : Type) `(s : lattice_conditionally_complete_linear_order α) : decidable_linear_order α := {}.
Class lattice_conditionally_complete_linear_order_bot (α : Type).
Instance lattice_conditionally_complete_linear_order_bot_to_conditionally_complete_lattice (α : Type) `(s : lattice_conditionally_complete_linear_order_bot α) : lattice_conditionally_complete_lattice α := {}.
Instance lattice_conditionally_complete_linear_order_bot_to_decidable_linear_order (α : Type) `(s : lattice_conditionally_complete_linear_order_bot α) : decidable_linear_order α := {}.
Instance lattice_conditionally_complete_linear_order_bot_to_order_bot (α : Type) `(s : lattice_conditionally_complete_linear_order_bot α) : lattice_order_bot α := {}.
Instance lattice_conditionally_complete_lattice_of_complete_lattice (α : Type) `(_inst_1 : lattice_complete_lattice α) : lattice_conditionally_complete_lattice α := {}.
Instance lattice_conditionally_complete_linear_order_of_complete_linear_order (α : Type) `(_inst_1 : lattice_complete_linear_order α) : lattice_conditionally_complete_linear_order α := {}.
Class category_theory_limits_has_equalizers (C : Type) `(𝒞 : category_theory_category C).
Class category_theory_limits_has_coequalizers (C : Type) `(𝒞 : category_theory_category C).
Class primcodable (α : Type).
Instance primcodable_to_encodable (α : Type) `(c : primcodable α) : encodable α := {}.
Instance primcodable_of_denumerable (α : Type) `(_inst_1 : denumerable α) : primcodable α := {}.
Class measurable_space (α : Type).
Class category_theory_limits_has_pullbacks (C : Type) `(𝒞 : category_theory_category C).
Class category_theory_limits_has_pushouts (C : Type) `(𝒞 : category_theory_category C).
Class category_theory_limits_has_binary_products (C : Type) `(𝒞 : category_theory_category C).
Class category_theory_limits_has_binary_coproducts (C : Type) `(𝒞 : category_theory_category C).
Instance category_theory_limits_category_theory_limits_has_binary_products (C : Type) `(𝒞 : category_theory_category C) `(_inst_1 : @category_theory_limits_has_finite_products C 𝒞) : @category_theory_limits_has_binary_products C 𝒞 := {}.
Instance category_theory_limits_category_theory_limits_has_binary_coproducts (C : Type) `(𝒞 : category_theory_category C) `(_inst_1 : @category_theory_limits_has_finite_coproducts C 𝒞) : @category_theory_limits_has_binary_coproducts C 𝒞 := {}.
Class topological_space (α : Type).
Class simple_group (α : Type) `(_inst_1 : group α).
Class simple_add_group (α : Type) `(_inst_1 : add_group α).
Class is_subring (R : Type) `(_inst_1 : ring R) (S : Type).
Instance is_subring_to_is_add_subgroup (R : Type) `(_inst_1 : ring R) (S : Type) `(c : @is_subring R _inst_1 S) : @is_add_subgroup R (@add_comm_group_to_add_group R (@ring_to_add_comm_group R _inst_1)) S := {}.
Instance is_subring_to_is_submonoid (R : Type) `(_inst_1 : ring R) (S : Type) `(c : @is_subring R _inst_1 S) : @is_submonoid R (@ring_to_monoid R _inst_1) S := {}.
Class discrete_topology (α : Type) `(t : topological_space α).
Class compact_space (α : Type) `(_inst_2 : topological_space α).
Class locally_compact_space (α : Type) `(_inst_2 : topological_space α).
Class irreducible_space (α : Type) `(_inst_2 : topological_space α).
Class connected_space (α : Type) `(_inst_2 : topological_space α).
Instance irreducible_space_connected_space (α : Type) `(_inst_2 : topological_space α) `(_inst_3 : @irreducible_space α _inst_2) : @connected_space α _inst_2 := {}.
Class is_subfield (F : Type) `(_inst_1 : discrete_field F) (S : Type).
Instance is_subfield_to_is_subring (F : Type) `(_inst_1 : discrete_field F) (S : Type) `(c : @is_subfield F _inst_1 S) : @is_subring F (@domain_to_ring F (@division_ring_to_domain F (@field_to_division_ring F (@discrete_field_to_field F _inst_1)))) S := {}.
Class totally_disconnected_space (α : Type) `(_inst_2 : topological_space α).
Class totally_separated_space (α : Type) `(_inst_2 : topological_space α).
Instance totally_separated_space_totally_disconnected_space (α : Type) `(_inst_2 : topological_space α) `(_inst_3 : @totally_separated_space α _inst_2) : @totally_disconnected_space α _inst_2 := {}.
Class t0_space (α : Type) `(_inst_2 : topological_space α).
Class t1_space (α : Type) `(_inst_2 : topological_space α).
Instance t1_space_t0_space (α : Type) `(_inst_1 : topological_space α) `(_inst_2 : @t1_space α _inst_1) : @t0_space α _inst_1 := {}.
Class topological_space_separable_space (α : Type) `(t : topological_space α).
Class t2_space (α : Type) `(_inst_2 : topological_space α).
Class topological_space_first_countable_topology (α : Type) `(t : topological_space α).
Class topological_space_second_countable_topology (α : Type) `(t : topological_space α).
Instance t2_space_t1_space (α : Type) `(_inst_1 : topological_space α) `(_inst_2 : @t2_space α _inst_1) : @t1_space α _inst_1 := {}.
Instance topological_space_second_countable_topology_to_first_countable_topology (α : Type) `(t : topological_space α) `(_inst_1 : @topological_space_second_countable_topology α t) : @topological_space_first_countable_topology α t := {}.
Instance t2_space_discrete (α : Type) `(_inst_2 : topological_space α) `(_inst_3 : @discrete_topology α _inst_2) : @t2_space α _inst_2 := {}.
Instance topological_space_second_countable_topology_to_separable_space (α : Type) `(t : topological_space α) `(_inst_1 : @topological_space_second_countable_topology α t) : @topological_space_separable_space α t := {}.
Class regular_space (α : Type) `(_inst_2 : topological_space α).
Instance regular_space_to_t1_space (α : Type) `(_inst_2 : topological_space α) `(c : @regular_space α _inst_2) : @t1_space α _inst_2 := {}.
Instance regular_space_t2_space (α : Type) `(_inst_1 : topological_space α) `(_inst_2 : @regular_space α _inst_1) : @t2_space α _inst_1 := {}.
Class normal_space (α : Type) `(_inst_2 : topological_space α).
Instance normal_space_to_t1_space (α : Type) `(_inst_2 : topological_space α) `(c : @normal_space α _inst_2) : @t1_space α _inst_2 := {}.
Instance normal_space_regular_space (α : Type) `(_inst_1 : topological_space α) `(_inst_2 : @normal_space α _inst_1) : @regular_space α _inst_1 := {}.
Instance ctop_to_topsp (α : Type) (σ : Type) (F : Type) : topological_space α := {}.
Class onote_NF (o : Type).
Instance locally_compact_of_compact (α : Type) `(_inst_1 : topological_space α) `(_inst_5 : @t2_space α _inst_1) `(_inst_6 : @compact_space α _inst_1) : @locally_compact_space α _inst_1 := {}.
Class has_scalar (α : Type) (γ : Type).
Class mul_action (α : Type) (β : Type) `(_inst_1 : monoid α).
Instance mul_action_to_has_scalar (α : Type) (β : Type) `(_inst_1 : monoid α) `(c : @mul_action α β _inst_1) : has_scalar α β := {}.
Class is_cyclic (α : Type) `(_inst_1 : group α).
Class distrib_mul_action (α : Type) (β : Type) `(_inst_1 : monoid α) `(_inst_2 : add_monoid β).
Instance distrib_mul_action_to_mul_action (α : Type) (β : Type) `(_inst_1 : monoid α) `(_inst_2 : add_monoid β) `(c : @distrib_mul_action α β _inst_1 _inst_2) : @mul_action α β _inst_1 := {}.
Class uniform_space (α : Type).
Instance uniform_space_to_topological_space (α : Type) `(c : uniform_space α) : topological_space α := {}.
Class semimodule (α : Type) (β : Type) `(_inst_1 : semiring α) `(_inst_2 : add_comm_monoid β).
Instance semimodule_to_distrib_mul_action (α : Type) (β : Type) `(_inst_1 : semiring α) `(_inst_2 : add_comm_monoid β) `(c : @semimodule α β _inst_1 _inst_2) : @distrib_mul_action α β (@semiring_to_monoid α _inst_1) (@add_comm_monoid_to_add_monoid β _inst_2) := {}.
Class module (α : Type) (β : Type) `(_inst_1 : ring α) `(_inst_2 : add_comm_group β).
Instance module_to_semimodule (α : Type) (β : Type) `(_inst_1 : ring α) `(_inst_2 : add_comm_group β) `(c : @module α β _inst_1 _inst_2) : @semimodule α β (@ring_to_semiring α _inst_1) (@add_comm_group_to_add_comm_monoid β _inst_2) := {}.
Instance semiring_to_semimodule (α : Type) `(r : semiring α) : @semimodule α α r (@semiring_to_add_comm_monoid α r) := {}.
Instance ring_to_module (α : Type) `(r : ring α) : @module α α r (@ring_to_add_comm_group α r) := {}.
Class is_linear_map (α : Type) (β : Type) (γ : Type) `(_inst_1 : ring α) `(_inst_2 : add_comm_group β) `(_inst_3 : add_comm_group γ) `(_inst_4 : module α β) `(_inst_5 : module α γ) (f : Type).
Class manifold (H : Type) `(_inst_1 : topological_space H) (M : Type) `(_inst_2 : topological_space M).
Class separated (α : Type) `(_inst_4 : uniform_space α).
Instance manifold_model_space (H : Type) `(_inst_1 : topological_space H) : @manifold H _inst_1 H _inst_1 := {}.
Instance separated_t2 (α : Type) `(_inst_1 : uniform_space α) `(s : @separated α _inst_1) : @t2_space α (@uniform_space_to_topological_space α _inst_1) := {}.
Instance separated_regular (α : Type) `(_inst_1 : uniform_space α) `(_inst_4 : @separated α _inst_1) : @regular_space α (@uniform_space_to_topological_space α _inst_1) := {}.
Class complete_space (α : Type) `(_inst_2 : uniform_space α).
Class has_groupoid (H : Type) `(_inst_4 : topological_space H) (M : Type) `(_inst_5 : topological_space M) `(_inst_6 : manifold H M) (G : Type).
Instance has_groupoid_model_space (H : Type) `(_inst_4 : topological_space H) (G : Type) : @has_groupoid H _inst_4 H _inst_4 (@manifold_model_space H _inst_4) G := {}.
Instance complete_of_compact (α : Type) `(_inst_2 : uniform_space α) `(_inst_3 : @compact_space α (@uniform_space_to_topological_space α _inst_2)) : @complete_space α _inst_2 := {}.
Class vector_space (α : Type) (β : Type) `(_inst_1 : discrete_field α) `(_inst_2 : add_comm_group β).
Instance vector_space_to_module (α : Type) (β : Type) `(_inst_1 : discrete_field α) `(_inst_2 : add_comm_group β) `(c : @vector_space α β _inst_1 _inst_2) : @module α β (@domain_to_ring α (@division_ring_to_domain α (@field_to_division_ring α (@discrete_field_to_field α _inst_1)))) _inst_2 := {}.
Instance discrete_field_to_vector_space (α : Type) `(_inst_1 : discrete_field α) : @vector_space α α _inst_1 (@ring_to_add_comm_group α (@domain_to_ring α (@division_ring_to_domain α (@field_to_division_ring α (@discrete_field_to_field α _inst_1))))) := {}.
Class has_edist (α : Type).
Class emetric_space (α : Type).
Instance emetric_space_to_has_edist (α : Type) `(c : emetric_space α) : has_edist α := {}.
Instance emetric_space_to_uniform_space' (α : Type) `(_inst_1 : emetric_space α) : uniform_space α := {}.
Instance to_separated (α : Type) `(_inst_1 : emetric_space α) : @separated α (@emetric_space_to_uniform_space' α _inst_1) := {}.
Class char_p (α : Type) `(_inst_1 : semiring α) (p : Type).
Class perfect_field (α : Type) `(_inst_1 : field α) (p : Type) `(_inst_2 : char_p α p).
Instance emetric_topological_space_first_countable_topology (α : Type) `(_inst_2 : emetric_space α) : @topological_space_first_countable_topology α (@uniform_space_to_topological_space α (@emetric_space_to_uniform_space' α _inst_2)) := {}.
Class topological_monoid (α : Type) `(_inst_1 : topological_space α) `(_inst_2 : monoid α).
Class topological_add_monoid (α : Type) `(_inst_1 : topological_space α) `(_inst_2 : add_monoid α).
Class topological_add_group (α : Type) `(_inst_1 : topological_space α) `(_inst_2 : add_group α).
Instance topological_add_group_to_topological_add_monoid (α : Type) `(_inst_1 : topological_space α) `(_inst_2 : add_group α) `(c : @topological_add_group α _inst_1 _inst_2) : @topological_add_monoid α _inst_1 (@add_group_to_add_monoid α _inst_2) := {}.
Class topological_group (α : Type) `(_inst_1 : topological_space α) `(_inst_2 : group α).
Instance topological_group_to_topological_monoid (α : Type) `(_inst_1 : topological_space α) `(_inst_2 : group α) `(c : @topological_group α _inst_1 _inst_2) : @topological_monoid α _inst_1 (@group_to_monoid α _inst_2) := {}.
Class add_group_with_zero_nhd (α : Type).
Instance add_group_with_zero_nhd_to_add_comm_group (α : Type) `(c : add_group_with_zero_nhd α) : add_comm_group α := {}.
Instance add_group_with_zero_nhd_topological_space (α : Type) `(_inst_1 : add_group_with_zero_nhd α) : topological_space α := {}.
Instance add_group_with_zero_nhd_topological_add_monoid (α : Type) `(_inst_1 : add_group_with_zero_nhd α) : @topological_add_monoid α (@add_group_with_zero_nhd_topological_space α _inst_1) (@add_group_to_add_monoid α (@add_comm_group_to_add_group α (@add_group_with_zero_nhd_to_add_comm_group α _inst_1))) := {}.
Instance add_group_with_zero_nhd_topological_add_group (α : Type) `(_inst_1 : add_group_with_zero_nhd α) : @topological_add_group α (@add_group_with_zero_nhd_topological_space α _inst_1) (@add_comm_group_to_add_group α (@add_group_with_zero_nhd_to_add_comm_group α _inst_1)) := {}.
Class uniform_add_group (α : Type) `(_inst_1 : uniform_space α) `(_inst_2 : add_group α).
Class ordered_topology (α : Type) `(t : topological_space α) `(_inst_1 : preorder α).
Instance uniform_add_group_to_topological_add_group (α : Type) `(_inst_1 : uniform_space α) `(_inst_2 : add_group α) `(_inst_3 : @uniform_add_group α _inst_1 _inst_2) : @topological_add_group α (@uniform_space_to_topological_space α _inst_1) _inst_2 := {}.
Instance ordered_topology_to_t2_space (α : Type) `(_inst_1 : topological_space α) `(_inst_2 : partial_order α) `(t : @ordered_topology α _inst_1 (@partial_order_to_preorder α _inst_2)) : @t2_space α _inst_1 := {}.
Class orderable_topology (α : Type) `(t : topological_space α) `(_inst_1 : partial_order α).
Class add_comm_group_is_Z_bilin (α : Type) (β : Type) (γ : Type) `(_inst_1 : add_comm_group α) `(_inst_2 : add_comm_group β) `(_inst_3 : add_comm_group γ) (f : Type).
Instance orderable_topology_to_ordered_topology (α : Type) `(_inst_1 : topological_space α) `(_inst_2 : linear_order α) `(t : @orderable_topology α _inst_1 (@linear_order_to_partial_order α _inst_2)) : @ordered_topology α _inst_1 (@partial_order_to_preorder α (@linear_order_to_partial_order α _inst_2)) := {}.
Instance orderable_topology_t2_space (α : Type) `(_inst_1 : topological_space α) `(_inst_2 : linear_order α) `(t : @orderable_topology α _inst_1 (@linear_order_to_partial_order α _inst_2)) : @t2_space α _inst_1 := {}.
Instance orderable_topology_regular_space (α : Type) `(_inst_1 : topological_space α) `(_inst_2 : linear_order α) `(t : @orderable_topology α _inst_1 (@linear_order_to_partial_order α _inst_2)) : @regular_space α _inst_1 := {}.
Class has_dist (α : Type).
Class metric_space (α : Type).
Instance metric_space_to_has_dist (α : Type) `(c : metric_space α) : has_dist α := {}.
Instance metric_space_to_uniform_space' (α : Type) `(_inst_1 : metric_space α) : uniform_space α := {}.
Instance metric_space_to_has_edist (α : Type) `(_inst_1 : metric_space α) : has_edist α := {}.
Instance metric_space_to_separated (α : Type) `(_inst_1 : metric_space α) : @separated α (@metric_space_to_uniform_space' α _inst_1) := {}.
Instance metric_space_to_emetric_space (α : Type) `(_inst_1 : metric_space α) : emetric_space α := {}.
Class proper_space (α : Type) `(_inst_2 : metric_space α).
Instance proper_of_compact (α : Type) `(_inst_1 : metric_space α) `(_inst_2 : @compact_space α (@uniform_space_to_topological_space α (@metric_space_to_uniform_space' α _inst_1))) : @proper_space α _inst_1 := {}.
Instance locally_compact_of_proper (α : Type) `(_inst_1 : metric_space α) `(_inst_2 : @proper_space α _inst_1) : @locally_compact_space α (@uniform_space_to_topological_space α (@metric_space_to_uniform_space' α _inst_1)) := {}.
Instance complete_of_proper (α : Type) `(_inst_1 : metric_space α) `(_inst_2 : @proper_space α _inst_1) : @complete_space α (@metric_space_to_uniform_space' α _inst_1) := {}.
Instance second_countable_of_proper (α : Type) `(_inst_1 : metric_space α) `(_inst_2 : @proper_space α _inst_1) : @topological_space_second_countable_topology α (@uniform_space_to_topological_space α (@metric_space_to_uniform_space' α _inst_1)) := {}.
Class ideal_is_prime (α : Type) `(_inst_1 : comm_ring α) (I : Type).
Class ideal_is_maximal (α : Type) `(_inst_1 : comm_ring α) (I : Type).
Instance ideal_is_maximal_is_prime' (α : Type) `(_inst_1 : comm_ring α) (I : Type) `(H : @ideal_is_maximal α _inst_1 I) : @ideal_is_prime α _inst_1 I := {}.
Class premetric_space (α : Type).
Instance premetric_space_to_has_dist (α : Type) `(c : premetric_space α) : has_dist α := {}.
Class local_ring (α : Type).
Instance local_ring_to_nonzero_comm_ring (α : Type) `(c : local_ring α) : nonzero_comm_ring α := {}.
Instance local_ring_comm_ring (α : Type) `(_inst_1 : local_ring α) : comm_ring α := {}.
Class is_local_ring_hom (α : Type) (β : Type) `(_inst_1 : comm_ring α) `(_inst_2 : comm_ring β) (f : Type).
Instance is_local_ring_hom_to_is_ring_hom (α : Type) (β : Type) `(_inst_1 : comm_ring α) `(_inst_2 : comm_ring β) (f : Type) `(c : @is_local_ring_hom α β _inst_1 _inst_2 f) : @is_ring_hom α β (@comm_ring_to_ring α _inst_1) (@comm_ring_to_ring β _inst_2) f := {}.
Instance discrete_field_local_ring (α : Type) `(_inst_1 : discrete_field α) : local_ring α := {}.
Class topological_semiring (α : Type) `(_inst_1 : topological_space α) `(_inst_2 : semiring α).
Instance topological_semiring_to_topological_add_monoid (α : Type) `(_inst_1 : topological_space α) `(_inst_2 : semiring α) `(c : @topological_semiring α _inst_1 _inst_2) : @topological_add_monoid α _inst_1 (@add_comm_monoid_to_add_monoid α (@semiring_to_add_comm_monoid α _inst_2)) := {}.
Instance topological_semiring_to_topological_monoid (α : Type) `(_inst_1 : topological_space α) `(_inst_2 : semiring α) `(c : @topological_semiring α _inst_1 _inst_2) : @topological_monoid α _inst_1 (@semiring_to_monoid α _inst_2) := {}.
Class topological_ring (α : Type) `(_inst_1 : topological_space α) `(_inst_2 : ring α).
Instance topological_ring_to_topological_add_monoid (α : Type) `(_inst_1 : topological_space α) `(_inst_2 : ring α) `(c : @topological_ring α _inst_1 _inst_2) : @topological_add_monoid α _inst_1 (@add_group_to_add_monoid α (@add_comm_group_to_add_group α (@ring_to_add_comm_group α _inst_2))) := {}.
Instance topological_ring_to_topological_monoid (α : Type) `(_inst_1 : topological_space α) `(_inst_2 : ring α) `(c : @topological_ring α _inst_1 _inst_2) : @topological_monoid α _inst_1 (@ring_to_monoid α _inst_2) := {}.
Instance topological_ring_to_topological_semiring (α : Type) `(_inst_1 : topological_space α) `(_inst_2 : ring α) `(t : @topological_ring α _inst_1 _inst_2) : @topological_semiring α _inst_1 (@ring_to_semiring α _inst_2) := {}.
Instance topological_ring_to_topological_add_group (α : Type) `(_inst_1 : topological_space α) `(_inst_2 : ring α) `(t : @topological_ring α _inst_1 _inst_2) : @topological_add_group α _inst_1 (@add_comm_group_to_add_group α (@ring_to_add_comm_group α _inst_2)) := {}.
Class algebra (R : Type) (A : Type) `(_inst_1 : comm_ring R) `(_inst_2 : ring A).
Instance algebra_to_module (R : Type) (A : Type) `(_inst_1 : comm_ring R) `(_inst_2 : ring A) `(c : @algebra R A _inst_1 _inst_2) : @module R A (@comm_ring_to_ring R _inst_1) (@ring_to_add_comm_group A _inst_2) := {}.
Instance algebra_module (R : Type) (A : Type) `(_inst_1 : comm_ring R) `(_inst_3 : ring A) `(_inst_4 : @algebra R A _inst_1 _inst_3) : @module R A (@comm_ring_to_ring R _inst_1) (@ring_to_add_comm_group A _inst_3) := {}.
Instance algebra_has_scalar (R : Type) (A : Type) `(_inst_1 : comm_ring R) `(_inst_3 : ring A) `(_inst_4 : @algebra R A _inst_1 _inst_3) : has_scalar R A := {}.
Instance algebra_vector_space (F : Type) (K : Type) `(_inst_5 : discrete_field F) `(_inst_6 : ring K) `(_inst_7 : @algebra F K (@local_ring_comm_ring F (@discrete_field_local_ring F _inst_5)) _inst_6) : @vector_space F K _inst_5 (@ring_to_add_comm_group K _inst_6) := {}.
Instance algebra_id (R : Type) `(_inst_1 : comm_ring R) : @algebra R R _inst_1 (@comm_ring_to_ring R _inst_1) := {}.
Class topological_semimodule (α : Type) (β : Type) `(_inst_1 : semiring α) `(_inst_2 : topological_space α) `(_inst_3 : topological_space β) `(_inst_4 : add_comm_monoid β) `(_inst_5 : semimodule α β).
Class topological_module (α : Type) (β : Type) `(_inst_1 : ring α) `(_inst_2 : topological_space α) `(_inst_3 : topological_space β) `(_inst_4 : add_comm_group β) `(_inst_5 : module α β).
Instance topological_module_to_topological_semimodule (α : Type) (β : Type) `(_inst_1 : ring α) `(_inst_2 : topological_space α) `(_inst_3 : topological_space β) `(_inst_4 : add_comm_group β) `(_inst_5 : @module α β _inst_1 _inst_4) `(c : @topological_module α β _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) : @topological_semimodule α β (@ring_to_semiring α _inst_1) _inst_2 _inst_3 (@add_comm_group_to_add_comm_monoid β _inst_4) (@module_to_semimodule α β _inst_1 _inst_4 _inst_5) := {}.
Class topological_vector_space (α : Type) (β : Type) `(_inst_1 : discrete_field α) `(_inst_2 : topological_space α) `(_inst_3 : topological_space β) `(_inst_4 : add_comm_group β) `(_inst_5 : vector_space α β).
Instance topological_vector_space_to_topological_module (α : Type) (β : Type) `(_inst_1 : discrete_field α) `(_inst_2 : topological_space α) `(_inst_3 : topological_space β) `(_inst_4 : add_comm_group β) `(_inst_5 : @vector_space α β _inst_1 _inst_4) `(c : @topological_vector_space α β _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) : @topological_module α β (@domain_to_ring α (@division_ring_to_domain α (@field_to_division_ring α (@discrete_field_to_field α _inst_1)))) _inst_2 _inst_3 _inst_4 (@vector_space_to_module α β _inst_1 _inst_4 _inst_5) := {}.
Class has_norm (α : Type).
Class normed_group (α : Type).
Instance normed_group_to_has_norm (α : Type) `(c : normed_group α) : has_norm α := {}.
Instance normed_group_to_add_comm_group (α : Type) `(c : normed_group α) : add_comm_group α := {}.
Instance normed_group_to_metric_space (α : Type) `(c : normed_group α) : metric_space α := {}.
Instance normed_uniform_group (α : Type) `(_inst_1 : normed_group α) : @uniform_add_group α (@metric_space_to_uniform_space' α (@normed_group_to_metric_space α _inst_1)) (@add_comm_group_to_add_group α (@normed_group_to_add_comm_group α _inst_1)) := {}.
Instance normed_top_monoid (α : Type) `(_inst_1 : normed_group α) : @topological_add_monoid α (@uniform_space_to_topological_space α (@metric_space_to_uniform_space' α (@normed_group_to_metric_space α _inst_1))) (@add_group_to_add_monoid α (@add_comm_group_to_add_group α (@normed_group_to_add_comm_group α _inst_1))) := {}.
Instance normed_top_group (α : Type) `(_inst_1 : normed_group α) : @topological_add_group α (@uniform_space_to_topological_space α (@metric_space_to_uniform_space' α (@normed_group_to_metric_space α _inst_1))) (@add_comm_group_to_add_group α (@normed_group_to_add_comm_group α _inst_1)) := {}.
Class normed_ring (α : Type).
Instance normed_ring_to_has_norm (α : Type) `(c : normed_ring α) : has_norm α := {}.
Instance normed_ring_to_ring (α : Type) `(c : normed_ring α) : ring α := {}.
Instance normed_ring_to_metric_space (α : Type) `(c : normed_ring α) : metric_space α := {}.
Instance normed_ring_to_normed_group (α : Type) `(β : normed_ring α) : normed_group α := {}.
Instance normed_ring_top_monoid (α : Type) `(_inst_1 : normed_ring α) : @topological_monoid α (@uniform_space_to_topological_space α (@metric_space_to_uniform_space' α (@normed_ring_to_metric_space α _inst_1))) (@ring_to_monoid α (@normed_ring_to_ring α _inst_1)) := {}.
Instance normed_top_ring (α : Type) `(_inst_1 : normed_ring α) : @topological_ring α (@uniform_space_to_topological_space α (@metric_space_to_uniform_space' α (@normed_ring_to_metric_space α _inst_1))) (@normed_ring_to_ring α _inst_1) := {}.
Class normed_field (α : Type).
Instance normed_field_to_has_norm (α : Type) `(c : normed_field α) : has_norm α := {}.
Instance normed_field_to_discrete_field (α : Type) `(c : normed_field α) : discrete_field α := {}.
Instance normed_field_to_metric_space (α : Type) `(c : normed_field α) : metric_space α := {}.
Class nondiscrete_normed_field (α : Type).
Instance nondiscrete_normed_field_to_normed_field (α : Type) `(c : nondiscrete_normed_field α) : normed_field α := {}.
Instance normed_field_to_normed_ring (α : Type) `(i : normed_field α) : normed_ring α := {}.
Class is_noetherian (α : Type) (β : Type) `(_inst_1 : ring α) `(_inst_2 : add_comm_group β) `(_inst_3 : module α β).
Class normed_space (α : Type) (β : Type) `(_inst_1 : normed_field α) `(_inst_2 : normed_group β).
Instance normed_space_to_vector_space (α : Type) (β : Type) `(_inst_1 : normed_field α) `(_inst_2 : normed_group β) `(c : @normed_space α β _inst_1 _inst_2) : @vector_space α β (@normed_field_to_discrete_field α _inst_1) (@normed_group_to_add_comm_group β _inst_2) := {}.
Instance normed_field_to_normed_space (α : Type) `(_inst_1 : normed_field α) : @normed_space α α _inst_1 (@normed_ring_to_normed_group α (@normed_field_to_normed_ring α _inst_1)) := {}.
Instance normed_space_topological_vector_space (α : Type) `(_inst_1 : normed_field α) (E : Type) `(_inst_3 : normed_group E) `(_inst_4 : @normed_space α E _inst_1 _inst_3) : @topological_vector_space α E (@normed_field_to_discrete_field α _inst_1) (@uniform_space_to_topological_space α (@metric_space_to_uniform_space' α (@normed_field_to_metric_space α _inst_1))) (@uniform_space_to_topological_space E (@metric_space_to_uniform_space' E (@normed_group_to_metric_space E _inst_3))) (@normed_group_to_add_comm_group E _inst_3) (@normed_space_to_vector_space α E _inst_1 _inst_3 _inst_4) := {}.
Class is_noetherian_ring (α : Type) `(_inst_1 : ring α).
Instance is_noetherian_ring_to_is_noetherian (α : Type) `(_inst_1 : ring α) `(_inst_2 : @is_noetherian_ring α _inst_1) : @is_noetherian α α _inst_1 (@ring_to_add_comm_group α _inst_1) (@ring_to_module α _inst_1) := {}.
Instance ring_is_noetherian_of_fintype (R : Type) (M : Type) `(_inst_1 : fintype M) `(_inst_2 : ring R) `(_inst_3 : add_comm_group M) `(_inst_4 : @module R M _inst_2 _inst_3) : @is_noetherian R M _inst_2 _inst_3 _inst_4 := {}.
Instance measure_theory_borel (α : Type) `(_inst_1 : topological_space α) : measurable_space α := {}.
Class ideal_is_principal (α : Type) `(_inst_1 : comm_ring α) (S : Type).
Class principal_ideal_domain (α : Type).
Instance principal_ideal_domain_to_integral_domain (α : Type) `(c : principal_ideal_domain α) : integral_domain α := {}.
Instance principal_ideal_domain_principal (α : Type) `(c : principal_ideal_domain α) (S : Type) : @ideal_is_principal α (@nonzero_comm_ring_to_comm_ring α (@integral_domain_to_nonzero_comm_ring α (@principal_ideal_domain_to_integral_domain α c))) S := {}.
Class directed_system (ι : Type) `(_inst_2 : nonempty ι) `(_inst_3 : directed_order ι) `(_inst_4 : Π (a b : ι), decidable (a = b)) (G : Type) `(_inst_5 : Π (i : ι) (a b : G i), decidable (a = b)) (f : Type).
Class module_directed_system (R : Type) `(_inst_1 : ring R) (ι : Type) `(_inst_2 : nonempty ι) `(_inst_3 : directed_order ι) `(_inst_4 : Π (a b : ι), decidable (a = b)) (G : Type) `(_inst_5 : Π (i : ι) (a b : G i), decidable (a = b)) `(_inst_6 : Π (i : ι), add_comm_group (G i)) `(_inst_7 : Π (i : ι), module R (G i)) (f : Type).
Instance euclidean_domain_to_principal_ideal_domain (α : Type) `(_inst_1 : euclidean_domain α) : principal_ideal_domain α := {}.
Instance principal_ideal_domain_is_noetherian_ring (α : Type) `(_inst_1 : principal_ideal_domain α) : @is_noetherian_ring α (@domain_to_ring α (@integral_domain_to_domain α (@principal_ideal_domain_to_integral_domain α _inst_1))) := {}.
Class sequential_space (α : Type) `(_inst_3 : topological_space α).
Instance metric_sequential_space (α : Type) `(_inst_1 : metric_space α) : @sequential_space α (@uniform_space_to_topological_space α (@metric_space_to_uniform_space' α _inst_1)) := {}.
Class has_inner (α : Type).
Class inner_product_space (α : Type).
Instance inner_product_space_to_add_comm_group (α : Type) `(c : inner_product_space α) : add_comm_group α := {}.
Instance inner_product_space_to_has_inner (α : Type) `(c : inner_product_space α) : has_inner α := {}.
Instance inner_product_space_has_norm (α : Type) `(_inst_1 : inner_product_space α) : has_norm α := {}.
Instance inner_product_space_is_normed_group (α : Type) `(_inst_1 : inner_product_space α) : normed_group α := {}.
Class measure_theory_measure_is_complete (α : Type) (_x : Type) (μ : Type).
Class measure_theory_measure_space (α : Type).
Instance measure_theory_measure_space_to_measurable_space (α : Type) `(c : measure_theory_measure_space α) : measurable_space α := {}.
