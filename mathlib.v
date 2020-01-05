Class decidable (p : Set) : Set.
Class has_zero (α : Set) : Set.
Class has_one (α : Set) : Set.
Class has_add (α : Set) : Set.
Class has_mul (α : Set) : Set.
Class has_inv (α : Set) : Set.
Class has_neg (α : Set) : Set.
Class has_sub (α : Set) : Set.
Class has_div (α : Set) : Set.
Class has_dvd (α : Set) : Set.
Class has_mod (α : Set) : Set.
Class has_le (α : Set) : Set.
Class has_lt (α : Set) : Set.
Class has_append (α : Set) : Set.
Class has_andthen (α : Set) (β : Set) (σ : Set) : Set.
Class has_union (α : Set) : Set.
Class has_inter (α : Set) : Set.
Class has_sdiff (α : Set) : Set.
Class has_equiv (α : Set) : Set.
Class has_subset (α : Set) : Set.
Class has_ssubset (α : Set) : Set.
Class has_emptyc (α : Set) : Set.
Class has_insert (α : Set) (γ : Set) : Set.
Class has_sep (α : Set) (γ : Set) : Set.
Class has_mem (α : Set) (γ : Set) : Set.
Class has_pow (α : Set) (β : Set) : Set.
Class has_sizeof (α : Set) : Set.
Class inhabited (α : Set) : Set.
Class nonempty (α : Set) : Set.
Instance nonempty_of_inhabited (α : Set) `(_inst_1 : inhabited α) : nonempty α := {}.
Class subsingleton (α : Set) : Set.
Instance subsingleton_prop (p : Set) : subsingleton p := {}.
Class setoid (α : Set) : Set.
Instance setoid_has_equiv (α : Set) `(_inst_1 : setoid α) : has_equiv α := {}.
Class has_well_founded (α : Set) : Set.
Instance has_well_founded_of_has_sizeof (α : Set) `(_inst_1 : has_sizeof α) : has_well_founded α := {}.
Class has_lift (a : Set) (b : Set) : Set.
Class has_lift_t (a : Set) (b : Set) : Set.
Class has_coe (a : Set) (b : Set) : Set.
Class has_coe_t (a : Set) (b : Set) : Set.
Class has_coe_to_fun (a : Set) : Set.
Class has_coe_to_sort (a : Set) : Set.
Instance lift_trans (a : Set) (b : Set) (c : Set) `(_inst_1 : has_lift a b) `(_inst_2 : has_lift_t b c) : has_lift_t a c := {}.
Instance lift_base (a : Set) (b : Set) `(_inst_1 : has_lift a b) : has_lift_t a b := {}.
Instance coe_trans (a : Set) (b : Set) (c : Set) `(_inst_1 : has_coe a b) `(_inst_2 : has_coe_t b c) : has_coe_t a c := {}.
Instance coe_base (a : Set) (b : Set) `(_inst_1 : has_coe a b) : has_coe_t a b := {}.
Class has_coe_t_aux (a : Set) (b : Set) : Set.
Instance coe_trans_aux (a : Set) (b : Set) (c : Set) `(_inst_1 : has_coe a b) `(_inst_2 : has_coe_t_aux b c) : has_coe_t_aux a c := {}.
Instance coe_base_aux (a : Set) (b : Set) `(_inst_1 : has_coe a b) : has_coe_t_aux a b := {}.
Instance coe_fn_trans (a : Set) (b : Set) `(_inst_1 : has_coe_t_aux a b) `(_inst_2 : has_coe_to_fun b) : has_coe_to_fun a := {}.
Instance coe_sort_trans (a : Set) (b : Set) `(_inst_1 : has_coe_t_aux a b) `(_inst_2 : has_coe_to_sort b) : has_coe_to_sort a := {}.
Instance coe_to_lift (a : Set) (b : Set) `(_inst_1 : has_coe_t a b) : has_lift_t a b := {}.
Class has_repr (α : Set) : Set.
Class has_to_string (α : Set) : Set.
Class is_symm_op (α : Set) (β : Set) (op : Set) : Set.
Class is_commutative (α : Set) (op : Set) : Set.
Instance is_symm_op_of_is_commutative (α : Set) (op : Set) `(_inst_1 : is_commutative α op) : is_symm_op α α op := {}.
Class is_associative (α : Set) (op : Set) : Set.
Class is_left_id (α : Set) (op : Set) (o : Set) : Set.
Class is_right_id (α : Set) (op : Set) (o : Set) : Set.
Class is_left_null (α : Set) (op : Set) (o : Set) : Set.
Class is_right_null (α : Set) (op : Set) (o : Set) : Set.
Class is_left_cancel (α : Set) (op : Set) : Set.
Class is_right_cancel (α : Set) (op : Set) : Set.
Class is_idempotent (α : Set) (op : Set) : Set.
Class is_left_distrib (α : Set) (op₁ : Set) (op₂ : Set) : Set.
Class is_right_distrib (α : Set) (op₁ : Set) (op₂ : Set) : Set.
Class is_left_inv (α : Set) (op : Set) (inv : Set) (o : Set) : Set.
Class is_right_inv (α : Set) (op : Set) (inv : Set) (o : Set) : Set.
Class is_cond_left_inv (α : Set) (op : Set) (inv : Set) (o : Set) (p : Set) : Set.
Class is_cond_right_inv (α : Set) (op : Set) (inv : Set) (o : Set) (p : Set) : Set.
Class is_distinct (α : Set) (a : Set) (b : Set) : Set.
Class is_irrefl (α : Set) (r : Set) : Set.
Class is_refl (α : Set) (r : Set) : Set.
Class is_symm (α : Set) (r : Set) : Set.
Class is_asymm (α : Set) (r : Set) : Set.
Class is_antisymm (α : Set) (r : Set) : Set.
Class is_trans (α : Set) (r : Set) : Set.
Class is_total (α : Set) (r : Set) : Set.
Class is_preorder (α : Set) (r : Set) : Set.
Instance is_preorder_to_is_refl (α : Set) (r : Set) `(c : is_preorder α r) : is_refl α r := {}.
Instance is_preorder_to_is_trans (α : Set) (r : Set) `(c : is_preorder α r) : is_trans α r := {}.
Class is_total_preorder (α : Set) (r : Set) : Set.
Instance is_total_preorder_to_is_trans (α : Set) (r : Set) `(c : is_total_preorder α r) : is_trans α r := {}.
Instance is_total_preorder_to_is_total (α : Set) (r : Set) `(c : is_total_preorder α r) : is_total α r := {}.
Instance is_total_preorder_is_preorder (α : Set) (r : Set) `(s : is_total_preorder α r) : is_preorder α r := {}.
Class is_partial_order (α : Set) (r : Set) : Set.
Instance is_partial_order_to_is_preorder (α : Set) (r : Set) `(c : is_partial_order α r) : is_preorder α r := {}.
Instance is_partial_order_to_is_antisymm (α : Set) (r : Set) `(c : is_partial_order α r) : is_antisymm α r := {}.
Class has_to_format (α : Set) : Set.
Class is_linear_order (α : Set) (r : Set) : Set.
Instance is_linear_order_to_is_partial_order (α : Set) (r : Set) `(c : is_linear_order α r) : is_partial_order α r := {}.
Instance is_linear_order_to_is_total (α : Set) (r : Set) `(c : is_linear_order α r) : is_total α r := {}.
Class is_equiv (α : Set) (r : Set) : Set.
Instance is_equiv_to_is_preorder (α : Set) (r : Set) `(c : is_equiv α r) : is_preorder α r := {}.
Instance is_equiv_to_is_symm (α : Set) (r : Set) `(c : is_equiv α r) : is_symm α r := {}.
Class is_per (α : Set) (r : Set) : Set.
Instance is_per_to_is_symm (α : Set) (r : Set) `(c : is_per α r) : is_symm α r := {}.
Instance is_per_to_is_trans (α : Set) (r : Set) `(c : is_per α r) : is_trans α r := {}.
Class is_strict_order (α : Set) (r : Set) : Set.
Instance is_strict_order_to_is_irrefl (α : Set) (r : Set) `(c : is_strict_order α r) : is_irrefl α r := {}.
Instance is_strict_order_to_is_trans (α : Set) (r : Set) `(c : is_strict_order α r) : is_trans α r := {}.
Class is_incomp_trans (α : Set) (lt : Set) : Set.
Class is_strict_weak_order (α : Set) (lt : Set) : Set.
Instance is_strict_weak_order_to_is_strict_order (α : Set) (lt : Set) `(c : is_strict_weak_order α lt) : is_strict_order α lt := {}.
Instance is_strict_weak_order_to_is_incomp_trans (α : Set) (lt : Set) `(c : is_strict_weak_order α lt) : is_incomp_trans α lt := {}.
Class is_trichotomous (α : Set) (lt : Set) : Set.
Class functor (f : Set) : Set.
Class is_strict_total_order (α : Set) (lt : Set) : Set.
Instance is_strict_total_order_to_is_trichotomous (α : Set) (lt : Set) `(c : is_strict_total_order α lt) : is_trichotomous α lt := {}.
Instance is_strict_total_order_to_is_strict_weak_order (α : Set) (lt : Set) `(c : is_strict_total_order α lt) : is_strict_weak_order α lt := {}.
Instance is_asymm_of_is_trans_of_is_irrefl (α : Set) (r : Set) `(_inst_1 : is_trans α r) `(_inst_2 : is_irrefl α r) : is_asymm α r := {}.
Class has_pure (f : Set) : Set.
Class has_seq (f : Set) : Set.
Class has_seq_left (f : Set) : Set.
Class has_seq_right (f : Set) : Set.
Class applicative (f : Set) : Set.
Instance applicative_to_functor (f : Set) `(c : applicative f) : functor f := {}.
Instance applicative_to_has_pure (f : Set) `(c : applicative f) : has_pure f := {}.
Instance applicative_to_has_seq (f : Set) `(c : applicative f) : has_seq f := {}.
Instance applicative_to_has_seq_left (f : Set) `(c : applicative f) : has_seq_left f := {}.
Instance applicative_to_has_seq_right (f : Set) `(c : applicative f) : has_seq_right f := {}.
Class preorder (α : Set) : Set.
Instance preorder_to_has_le (α : Set) `(s : preorder α) : has_le α := {}.
Instance preorder_to_has_lt (α : Set) `(s : preorder α) : has_lt α := {}.
Class has_bind (m : Set) : Set.
Class monad (m : Set) : Set.
Instance monad_to_applicative (m : Set) `(c : monad m) : applicative m := {}.
Instance monad_to_has_bind (m : Set) `(c : monad m) : has_bind m := {}.
Class partial_order (α : Set) : Set.
Instance partial_order_to_preorder (α : Set) `(s : partial_order α) : preorder α := {}.
Class has_orelse (f : Set) : Set.
Class alternative (f : Set) : Set.
Instance alternative_to_applicative (f : Set) `(c : alternative f) : applicative f := {}.
Instance alternative_to_has_orelse (f : Set) `(c : alternative f) : has_orelse f := {}.
Class has_monad_lift (m : Set) (n : Set) : Set.
Class linear_order (α : Set) : Set.
Instance linear_order_to_partial_order (α : Set) `(s : linear_order α) : partial_order α := {}.
Class has_monad_lift_t (m : Set) (n : Set) : Set.
Instance has_monad_lift_t_trans (m : Set) (n : Set) (o : Set) `(_inst_1 : has_monad_lift n o) `(_inst_2 : has_monad_lift_t m n) : has_monad_lift_t m o := {}.
Instance has_monad_lift_t_refl (m : Set) : has_monad_lift_t m m := {}.
Class monad_functor (m : Set) (m' : Set) (n : Set) (n' : Set) : Set.
Class monad_functor_t (m : Set) (m' : Set) (n : Set) (n' : Set) : Set.
Instance monad_functor_t_trans (m : Set) (m' : Set) (n : Set) (n' : Set) (o : Set) (o' : Set) `(_inst_1 : monad_functor n n' o o') `(_inst_2 : monad_functor_t m m' n n') : monad_functor_t m m' o o' := {}.
Instance monad_functor_t_refl (m : Set) (m' : Set) : monad_functor_t m m' m m' := {}.
Class monad_run (out : Set) (m : Set) : Set.
Class monad_fail (m : Set) : Set.
Instance monad_fail_lift (m : Set) (n : Set) `(_inst_1 : has_monad_lift m n) `(_inst_2 : monad_fail m) `(_inst_3 : monad n) : monad_fail n := {}.
Class decidable_linear_order (α : Set) : Set.
Instance decidable_linear_order_to_linear_order (α : Set) `(s : decidable_linear_order α) : linear_order α := {}.
Class monad_except (ε : Set) (m : Set) : Set.
Class monad_except_adapter (ε : Set) (ε' : Set) (m : Set) (m' : Set) : Set.
Instance monad_except_adapter_trans (ε : Set) (ε' : Set) (m : Set) (m' : Set) (n : Set) (n' : Set) `(_inst_1 : monad_functor m m' n n') `(_inst_2 : monad_except_adapter ε ε' m m') : monad_except_adapter ε ε' n n' := {}.
Class monad_reader (ρ : Set) (m : Set) : Set.
Instance monad_reader_trans (ρ : Set) (m : Set) (n : Set) `(_inst_1 : has_monad_lift m n) `(_inst_2 : monad_reader ρ m) : monad_reader ρ n := {}.
Class monad_reader_adapter (ρ : Set) (ρ' : Set) (m : Set) (m' : Set) : Set.
Instance monad_reader_adapter_trans (ρ : Set) (ρ' : Set) (m : Set) (m' : Set) (n : Set) (n' : Set) `(_inst_1 : monad_functor m m' n n') `(_inst_2 : monad_reader_adapter ρ ρ' m m') : monad_reader_adapter ρ ρ' n n' := {}.
Class monad_state (σ : Set) (m : Set) : Set.
Instance monad_state_trans (σ : Set) (m : Set) (n : Set) `(_inst_1 : has_monad_lift m n) `(_inst_2 : monad_state σ m) : monad_state σ n := {}.
Class monad_state_adapter (σ : Set) (σ' : Set) (m : Set) (m' : Set) : Set.
Instance monad_state_adapter_trans (σ : Set) (σ' : Set) (m : Set) (m' : Set) (n : Set) (n' : Set) `(_inst_1 : monad_functor m m' n n') `(_inst_2 : monad_state_adapter σ σ' m m') : monad_state_adapter σ σ' n n' := {}.
Class has_to_pexpr (α : Set) : Set.
Class has_to_tactic_format (α : Set) : Set.
Instance has_to_format_to_has_to_tactic_format (α : Set) `(_inst_1 : has_to_format α) : has_to_tactic_format α := {}.
Class is_lawful_functor (f : Set) `(_inst_1 : functor f) : Set.
Class is_lawful_applicative (f : Set) `(_inst_1 : applicative f) : Set.
Instance is_lawful_applicative_to_is_lawful_functor (f : Set) `(_inst_1 : applicative f) `(c : @is_lawful_applicative f _inst_1) : @is_lawful_functor f (@applicative_to_functor f _inst_1) := {}.
Class is_lawful_monad (m : Set) `(_inst_1 : monad m) : Set.
Instance is_lawful_monad_to_is_lawful_applicative (m : Set) `(_inst_1 : monad m) `(c : @is_lawful_monad m _inst_1) : @is_lawful_applicative m (@monad_to_applicative m _inst_1) := {}.
Class semigroup (α : Set) : Set.
Instance semigroup_to_has_mul (α : Set) `(s : semigroup α) : has_mul α := {}.
Class comm_semigroup (α : Set) : Set.
Instance comm_semigroup_to_semigroup (α : Set) `(s : comm_semigroup α) : semigroup α := {}.
Class left_cancel_semigroup (α : Set) : Set.
Instance left_cancel_semigroup_to_semigroup (α : Set) `(s : left_cancel_semigroup α) : semigroup α := {}.
Class right_cancel_semigroup (α : Set) : Set.
Instance right_cancel_semigroup_to_semigroup (α : Set) `(s : right_cancel_semigroup α) : semigroup α := {}.
Class monoid (α : Set) : Set.
Instance monoid_to_semigroup (α : Set) `(s : monoid α) : semigroup α := {}.
Instance monoid_to_has_one (α : Set) `(s : monoid α) : has_one α := {}.
Class comm_monoid (α : Set) : Set.
Instance comm_monoid_to_monoid (α : Set) `(s : comm_monoid α) : monoid α := {}.
Instance comm_monoid_to_comm_semigroup (α : Set) `(s : comm_monoid α) : comm_semigroup α := {}.
Class group (α : Set) : Set.
Instance group_to_monoid (α : Set) `(s : group α) : monoid α := {}.
Instance group_to_has_inv (α : Set) `(s : group α) : has_inv α := {}.
Class comm_group (α : Set) : Set.
Instance comm_group_to_group (α : Set) `(s : comm_group α) : group α := {}.
Instance comm_group_to_comm_monoid (α : Set) `(s : comm_group α) : comm_monoid α := {}.
Instance group_to_left_cancel_semigroup (α : Set) `(s : group α) : left_cancel_semigroup α := {}.
Instance group_to_right_cancel_semigroup (α : Set) `(s : group α) : right_cancel_semigroup α := {}.
Class add_semigroup (α : Set) : Set.
Instance add_semigroup_to_has_add (α : Set) `(s : add_semigroup α) : has_add α := {}.
Class add_comm_semigroup (α : Set) : Set.
Instance add_comm_semigroup_to_add_semigroup (α : Set) `(s : add_comm_semigroup α) : add_semigroup α := {}.
Class add_left_cancel_semigroup (α : Set) : Set.
Instance add_left_cancel_semigroup_to_add_semigroup (α : Set) `(s : add_left_cancel_semigroup α) : add_semigroup α := {}.
Class add_right_cancel_semigroup (α : Set) : Set.
Instance add_right_cancel_semigroup_to_add_semigroup (α : Set) `(s : add_right_cancel_semigroup α) : add_semigroup α := {}.
Class add_monoid (α : Set) : Set.
Instance add_monoid_to_add_semigroup (α : Set) `(s : add_monoid α) : add_semigroup α := {}.
Instance add_monoid_to_has_zero (α : Set) `(s : add_monoid α) : has_zero α := {}.
Class add_comm_monoid (α : Set) : Set.
Instance add_comm_monoid_to_add_monoid (α : Set) `(s : add_comm_monoid α) : add_monoid α := {}.
Instance add_comm_monoid_to_add_comm_semigroup (α : Set) `(s : add_comm_monoid α) : add_comm_semigroup α := {}.
Class add_group (α : Set) : Set.
Instance add_group_to_add_monoid (α : Set) `(s : add_group α) : add_monoid α := {}.
Instance add_group_to_has_neg (α : Set) `(s : add_group α) : has_neg α := {}.
Class add_comm_group (α : Set) : Set.
Instance add_comm_group_to_add_group (α : Set) `(s : add_comm_group α) : add_group α := {}.
Instance add_comm_group_to_add_comm_monoid (α : Set) `(s : add_comm_group α) : add_comm_monoid α := {}.
Instance add_group_to_left_cancel_add_semigroup (α : Set) `(s : add_group α) : add_left_cancel_semigroup α := {}.
Instance add_group_to_right_cancel_add_semigroup (α : Set) `(s : add_group α) : add_right_cancel_semigroup α := {}.
Instance add_group_has_sub (α : Set) `(_inst_1 : add_group α) : has_sub α := {}.
Class distrib (α : Set) : Set.
Instance distrib_to_has_mul (α : Set) `(s : distrib α) : has_mul α := {}.
Instance distrib_to_has_add (α : Set) `(s : distrib α) : has_add α := {}.
Class mul_zero_class (α : Set) : Set.
Instance mul_zero_class_to_has_mul (α : Set) `(s : mul_zero_class α) : has_mul α := {}.
Instance mul_zero_class_to_has_zero (α : Set) `(s : mul_zero_class α) : has_zero α := {}.
Class zero_ne_one_class (α : Set) : Set.
Instance zero_ne_one_class_to_has_zero (α : Set) `(s : zero_ne_one_class α) : has_zero α := {}.
Instance zero_ne_one_class_to_has_one (α : Set) `(s : zero_ne_one_class α) : has_one α := {}.
Class ordered_cancel_comm_monoid (α : Set) : Set.
Instance ordered_cancel_comm_monoid_to_add_comm_monoid (α : Set) `(s : ordered_cancel_comm_monoid α) : add_comm_monoid α := {}.
Instance ordered_cancel_comm_monoid_to_add_left_cancel_semigroup (α : Set) `(s : ordered_cancel_comm_monoid α) : add_left_cancel_semigroup α := {}.
Instance ordered_cancel_comm_monoid_to_add_right_cancel_semigroup (α : Set) `(s : ordered_cancel_comm_monoid α) : add_right_cancel_semigroup α := {}.
Instance ordered_cancel_comm_monoid_to_partial_order (α : Set) `(s : ordered_cancel_comm_monoid α) : partial_order α := {}.
Class semiring (α : Set) : Set.
Instance semiring_to_add_comm_monoid (α : Set) `(s : semiring α) : add_comm_monoid α := {}.
Instance semiring_to_monoid (α : Set) `(s : semiring α) : monoid α := {}.
Instance semiring_to_distrib (α : Set) `(s : semiring α) : distrib α := {}.
Instance semiring_to_mul_zero_class (α : Set) `(s : semiring α) : mul_zero_class α := {}.
Class comm_semiring (α : Set) : Set.
Instance comm_semiring_to_semiring (α : Set) `(s : comm_semiring α) : semiring α := {}.
Instance comm_semiring_to_comm_monoid (α : Set) `(s : comm_semiring α) : comm_monoid α := {}.
Instance comm_semiring_has_dvd (α : Set) `(_inst_1 : comm_semiring α) : has_dvd α := {}.
Class ordered_comm_group (α : Set) : Set.
Instance ordered_comm_group_to_add_comm_group (α : Set) `(s : ordered_comm_group α) : add_comm_group α := {}.
Instance ordered_comm_group_to_partial_order (α : Set) `(s : ordered_comm_group α) : partial_order α := {}.
Instance ordered_comm_group_to_ordered_cancel_comm_monoid (α : Set) `(s : ordered_comm_group α) : ordered_cancel_comm_monoid α := {}.
Class ring (α : Set) : Set.
Instance ring_to_add_comm_group (α : Set) `(s : ring α) : add_comm_group α := {}.
Instance ring_to_monoid (α : Set) `(s : ring α) : monoid α := {}.
Instance ring_to_distrib (α : Set) `(s : ring α) : distrib α := {}.
Instance ring_to_semiring (α : Set) `(s : ring α) : semiring α := {}.
Class comm_ring (α : Set) : Set.
Instance comm_ring_to_ring (α : Set) `(s : comm_ring α) : ring α := {}.
Instance comm_ring_to_comm_semigroup (α : Set) `(s : comm_ring α) : comm_semigroup α := {}.
Instance comm_ring_to_comm_semiring (α : Set) `(s : comm_ring α) : comm_semiring α := {}.
Class no_zero_divisors (α : Set) : Set.
Instance no_zero_divisors_to_has_mul (α : Set) `(s : no_zero_divisors α) : has_mul α := {}.
Instance no_zero_divisors_to_has_zero (α : Set) `(s : no_zero_divisors α) : has_zero α := {}.
Class integral_domain (α : Set) : Set.
Instance integral_domain_to_comm_ring (α : Set) `(s : integral_domain α) : comm_ring α := {}.
Instance integral_domain_to_no_zero_divisors (α : Set) `(s : integral_domain α) : no_zero_divisors α := {}.
Instance integral_domain_to_zero_ne_one_class (α : Set) `(s : integral_domain α) : zero_ne_one_class α := {}.
Class division_ring (α : Set) : Set.
Instance division_ring_to_ring (α : Set) `(s : division_ring α) : ring α := {}.
Instance division_ring_to_has_inv (α : Set) `(s : division_ring α) : has_inv α := {}.
Instance division_ring_to_zero_ne_one_class (α : Set) `(s : division_ring α) : zero_ne_one_class α := {}.
Instance division_ring_has_div (α : Set) `(_inst_1 : division_ring α) `(_inst_2 : division_ring α) : has_div α := {}.
Class decidable_linear_ordered_comm_group (α : Set) : Set.
Instance decidable_linear_ordered_comm_group_to_add_comm_group (α : Set) `(s : decidable_linear_ordered_comm_group α) : add_comm_group α := {}.
Instance decidable_linear_ordered_comm_group_to_decidable_linear_order (α : Set) `(s : decidable_linear_ordered_comm_group α) : decidable_linear_order α := {}.
Instance decidable_linear_ordered_comm_group_to_ordered_comm_group (α : Set) `(s : decidable_linear_ordered_comm_group α) : ordered_comm_group α := {}.
Class decidable_linear_ordered_cancel_comm_monoid (α : Set) : Set.
Instance decidable_linear_ordered_cancel_comm_monoid_to_ordered_cancel_comm_monoid (α : Set) `(s : decidable_linear_ordered_cancel_comm_monoid α) : ordered_cancel_comm_monoid α := {}.
Instance decidable_linear_ordered_cancel_comm_monoid_to_decidable_linear_order (α : Set) `(s : decidable_linear_ordered_cancel_comm_monoid α) : decidable_linear_order α := {}.
Class field (α : Set) : Set.
Instance field_to_division_ring (α : Set) `(s : field α) : division_ring α := {}.
Instance field_to_comm_ring (α : Set) `(s : field α) : comm_ring α := {}.
Class discrete_field (α : Set) : Set.
Instance discrete_field_to_field (α : Set) `(s : discrete_field α) : field α := {}.
Instance discrete_field_to_integral_domain (α : Set) `(_inst_1 : discrete_field α) `(s : discrete_field α) : integral_domain α := {}.
Class ordered_semiring (α : Set) : Set.
Instance ordered_semiring_to_semiring (α : Set) `(s : ordered_semiring α) : semiring α := {}.
Instance ordered_semiring_to_ordered_cancel_comm_monoid (α : Set) `(s : ordered_semiring α) : ordered_cancel_comm_monoid α := {}.
Class linear_ordered_semiring (α : Set) : Set.
Instance linear_ordered_semiring_to_ordered_semiring (α : Set) `(s : linear_ordered_semiring α) : ordered_semiring α := {}.
Instance linear_ordered_semiring_to_linear_order (α : Set) `(s : linear_ordered_semiring α) : linear_order α := {}.
Class decidable_linear_ordered_semiring (α : Set) : Set.
Instance decidable_linear_ordered_semiring_to_linear_ordered_semiring (α : Set) `(s : decidable_linear_ordered_semiring α) : linear_ordered_semiring α := {}.
Instance decidable_linear_ordered_semiring_to_decidable_linear_order (α : Set) `(s : decidable_linear_ordered_semiring α) : decidable_linear_order α := {}.
Class ordered_ring (α : Set) : Set.
Instance ordered_ring_to_ring (α : Set) `(s : ordered_ring α) : ring α := {}.
Instance ordered_ring_to_ordered_comm_group (α : Set) `(s : ordered_ring α) : ordered_comm_group α := {}.
Instance ordered_ring_to_zero_ne_one_class (α : Set) `(s : ordered_ring α) : zero_ne_one_class α := {}.
Instance ordered_ring_to_ordered_semiring (α : Set) `(s : ordered_ring α) : ordered_semiring α := {}.
Class linear_ordered_ring (α : Set) : Set.
Instance linear_ordered_ring_to_ordered_ring (α : Set) `(s : linear_ordered_ring α) : ordered_ring α := {}.
Instance linear_ordered_ring_to_linear_order (α : Set) `(s : linear_ordered_ring α) : linear_order α := {}.
Instance linear_ordered_ring_to_linear_ordered_semiring (α : Set) `(s : linear_ordered_ring α) : linear_ordered_semiring α := {}.
Class linear_ordered_comm_ring (α : Set) : Set.
Instance linear_ordered_comm_ring_to_linear_ordered_ring (α : Set) `(s : linear_ordered_comm_ring α) : linear_ordered_ring α := {}.
Instance linear_ordered_comm_ring_to_comm_monoid (α : Set) `(s : linear_ordered_comm_ring α) : comm_monoid α := {}.
Instance linear_ordered_comm_ring_to_integral_domain (α : Set) `(s : linear_ordered_comm_ring α) : integral_domain α := {}.
Class decidable_linear_ordered_comm_ring (α : Set) : Set.
Instance decidable_linear_ordered_comm_ring_to_linear_ordered_comm_ring (α : Set) `(s : decidable_linear_ordered_comm_ring α) : linear_ordered_comm_ring α := {}.
Instance decidable_linear_ordered_comm_ring_to_decidable_linear_ordered_comm_group (α : Set) `(s : decidable_linear_ordered_comm_ring α) : decidable_linear_ordered_comm_group α := {}.
Instance decidable_linear_ordered_comm_ring_to_decidable_linear_ordered_semiring (α : Set) `(d : decidable_linear_ordered_comm_ring α) : decidable_linear_ordered_semiring α := {}.
Class linear_ordered_field (α : Set) : Set.
Instance linear_ordered_field_to_linear_ordered_ring (α : Set) `(s : linear_ordered_field α) : linear_ordered_ring α := {}.
Instance linear_ordered_field_to_field (α : Set) `(s : linear_ordered_field α) : field α := {}.
Class discrete_linear_ordered_field (α : Set) : Set.
Instance discrete_linear_ordered_field_to_linear_ordered_field (α : Set) `(s : discrete_linear_ordered_field α) : linear_ordered_field α := {}.
Instance discrete_linear_ordered_field_to_decidable_linear_ordered_comm_ring (α : Set) `(s : discrete_linear_ordered_field α) : decidable_linear_ordered_comm_ring α := {}.
Instance discrete_linear_ordered_field_to_discrete_field (α : Set) `(s : discrete_linear_ordered_field α) : discrete_field α := {}.
Class unique (α : Set) : Set.
Class relator_right_total (α : Set) (β : Set) (R : Set) : Set.
Class relator_left_total (α : Set) (β : Set) (R : Set) : Set.
Class relator_bi_total (α : Set) (β : Set) (R : Set) : Set.
Instance unique_inhabited (α : Set) `(_inst_1 : unique α) : inhabited α := {}.
Instance unique_subsingleton (α : Set) `(_inst_1 : unique α) : subsingleton α := {}.
Class relator_left_unique (α : Set) (β : Set) (R : Set) : Set.
Class relator_right_unique (α : Set) (β : Set) (R : Set) : Set.
Class is_comm_applicative (m : Set) `(_inst_1 : applicative m) : Set.
Instance is_comm_applicative_to_is_lawful_applicative (m : Set) `(_inst_1 : applicative m) `(c : @is_comm_applicative m _inst_1) : @is_lawful_applicative m _inst_1 := {}.
Class can_lift (α : Set) (β : Set) : Set.
Class traversable (t : Set) : Set.
Instance traversable_to_functor (t : Set) `(c : traversable t) : functor t := {}.
Class is_lawful_traversable (t : Set) `(_inst_1 : traversable t) : Set.
Instance is_lawful_traversable_to_is_lawful_functor (t : Set) `(_inst_1 : traversable t) `(c : @is_lawful_traversable t _inst_1) : @is_lawful_functor t (@traversable_to_functor t _inst_1) := {}.
Class category_theory_has_hom (obj : Set) : Set.
Class eckmann_hilton_is_unital (X : Set) (m : Set) (e : Set) : Set.
Class category_theory_category_struct (obj : Set) : Set.
Instance category_theory_category_struct_to_has_hom (obj : Set) `(c : category_theory_category_struct obj) : category_theory_has_hom obj := {}.
Class bifunctor (F : Set) : Set.
Class is_lawful_bifunctor (F : Set) `(_inst_1 : bifunctor F) : Set.
Class category_theory_category (obj : Set) : Set.
Instance category_theory_category_to_category_struct (obj : Set) `(c : category_theory_category obj) : category_theory_category_struct obj := {}.
Class category_theory_epi (C : Set) `(𝒞 : category_theory_category C) (X : Set) (Y : Set) (f : Set) : Set.
Class category_theory_mono (C : Set) `(𝒞 : category_theory_category C) (X : Set) (Y : Set) (f : Set) : Set.
Instance preorder_small_category (α : Set) `(_inst_1 : preorder α) : category_theory_category α := {}.
Class computation_terminates (α : Set) (s : Set) : Set.
Class monad_writer (ω : Set) (m : Set) : Set.
Class monad_writer_adapter (ω : Set) (ω' : Set) (m : Set) (m' : Set) : Set.
Class bitraversable (t : Set) : Set.
Instance bitraversable_to_bifunctor (t : Set) `(c : bitraversable t) : bifunctor t := {}.
Instance monad_writer_adapter_trans (ω : Set) (ω' : Set) (m : Set) (m' : Set) (n : Set) (n' : Set) `(_inst_1 : monad_functor m m' n n') `(_inst_2 : monad_writer_adapter ω ω' m m') : monad_writer_adapter ω ω' n n' := {}.
Class is_lawful_bitraversable (t : Set) `(_inst_1 : bitraversable t) : Set.
Instance is_lawful_bitraversable_to_is_lawful_bifunctor (t : Set) `(_inst_1 : bitraversable t) `(c : @is_lawful_bitraversable t _inst_1) : @is_lawful_bifunctor t (@bitraversable_to_bifunctor t _inst_1) := {}.
Class monad_cont (m : Set) : Set.
Class is_lawful_monad_cont (m : Set) `(_inst_1 : monad m) `(_inst_2 : monad_cont m) : Set.
Instance is_lawful_monad_cont_to_is_lawful_monad (m : Set) `(_inst_1 : monad m) `(_inst_2 : monad_cont m) `(c : @is_lawful_monad_cont m _inst_1 _inst_2) : @is_lawful_monad m _inst_1 := {}.
Class category_theory_is_iso (C : Set) `(𝒞 : category_theory_category C) (X : Set) (Y : Set) (f : Set) : Set.
Instance category_theory_is_iso_epi_of_iso (C : Set) `(𝒞 : category_theory_category C) (X : Set) (Y : Set) (f : Set) `(_inst_1 : @category_theory_is_iso C 𝒞 X Y f) : @category_theory_epi C 𝒞 X Y f := {}.
Instance category_theory_is_iso_mono_of_iso (C : Set) `(𝒞 : category_theory_category C) (X : Set) (Y : Set) (f : Set) `(_inst_1 : @category_theory_is_iso C 𝒞 X Y f) : @category_theory_mono C 𝒞 X Y f := {}.
Class category_theory_full (C : Set) `(𝒞 : category_theory_category C) (D : Set) `(𝒟 : category_theory_category D) (F : Set) : Set.
Class category_theory_faithful (C : Set) `(𝒞 : category_theory_category C) (D : Set) `(𝒟 : category_theory_category D) (F : Set) : Set.
Class category_theory_monad (C : Set) `(𝒞 : category_theory_category C) (T : Set) : Set.
Class pSet_definable (n : Set) (a : Set) : Set.
Class is_group_anti_hom (α : Set) (β : Set) `(_inst_1 : group α) `(_inst_2 : group β) (f : Set) : Set.
Class is_add_hom (α : Set) (β : Set) `(_inst_1 : has_add α) `(_inst_2 : has_add β) (f : Set) : Set.
Class is_mul_hom (α : Set) (β : Set) `(_inst_1 : has_mul α) `(_inst_2 : has_mul β) (f : Set) : Set.
Class no_top_order (α : Set) `(_inst_1 : preorder α) : Set.
Class no_bot_order (α : Set) `(_inst_1 : preorder α) : Set.
Class densely_ordered (α : Set) `(_inst_1 : preorder α) : Set.
Class is_add_monoid_hom (α : Set) (β : Set) `(_inst_1 : add_monoid α) `(_inst_2 : add_monoid β) (f : Set) : Set.
Instance is_add_monoid_hom_to_is_add_hom (α : Set) (β : Set) `(_inst_1 : add_monoid α) `(_inst_2 : add_monoid β) (f : Set) `(c : @is_add_monoid_hom α β _inst_1 _inst_2 f) : @is_add_hom α β (@add_semigroup_to_has_add α (@add_monoid_to_add_semigroup α _inst_1)) (@add_semigroup_to_has_add β (@add_monoid_to_add_semigroup β _inst_2)) f := {}.
Class is_monoid_hom (α : Set) (β : Set) `(_inst_1 : monoid α) `(_inst_2 : monoid β) (f : Set) : Set.
Class is_strict_total_order' (α : Set) (lt : Set) : Set.
Instance is_strict_total_order'_to_is_trichotomous (α : Set) (lt : Set) `(c : is_strict_total_order' α lt) : is_trichotomous α lt := {}.
Instance is_strict_total_order'_to_is_strict_order (α : Set) (lt : Set) `(c : is_strict_total_order' α lt) : is_strict_order α lt := {}.
Instance is_monoid_hom_to_is_mul_hom (α : Set) (β : Set) `(_inst_1 : monoid α) `(_inst_2 : monoid β) (f : Set) `(c : @is_monoid_hom α β _inst_1 _inst_2 f) : @is_mul_hom α β (@semigroup_to_has_mul α (@monoid_to_semigroup α _inst_1)) (@semigroup_to_has_mul β (@monoid_to_semigroup β _inst_2)) f := {}.
Class is_order_connected (α : Set) (lt : Set) : Set.
Instance is_order_connected_of_is_strict_total_order' (α : Set) (r : Set) `(_inst_1 : is_strict_total_order' α r) : is_order_connected α r := {}.
Instance is_strict_total_order_of_is_strict_total_order' (α : Set) (r : Set) `(_inst_1 : is_strict_total_order' α r) : is_strict_total_order α r := {}.
Class is_extensional (α : Set) (r : Set) : Set.
Instance is_extensional_of_is_strict_total_order' (α : Set) (r : Set) `(_inst_1 : is_strict_total_order' α r) : is_extensional α r := {}.
Class is_well_order (α : Set) (r : Set) : Set.
Instance is_well_order_to_is_strict_total_order' (α : Set) (r : Set) `(c : is_well_order α r) : is_strict_total_order' α r := {}.
Instance is_well_order_is_strict_total_order (α : Set) (r : Set) `(_inst_1 : is_well_order α r) : is_strict_total_order α r := {}.
Instance is_well_order_is_extensional (α : Set) (r : Set) `(_inst_1 : is_well_order α r) : is_extensional α r := {}.
Instance is_well_order_is_trichotomous (α : Set) (r : Set) `(_inst_1 : is_well_order α r) : is_trichotomous α r := {}.
Instance is_well_order_is_trans (α : Set) (r : Set) `(_inst_1 : is_well_order α r) : is_trans α r := {}.
Instance is_well_order_is_irrefl (α : Set) (r : Set) `(_inst_1 : is_well_order α r) : is_irrefl α r := {}.
Instance is_well_order_is_asymm (α : Set) (r : Set) `(_inst_1 : is_well_order α r) : is_asymm α r := {}.
Class is_add_group_hom (α : Set) (β : Set) `(_inst_1 : add_group α) `(_inst_2 : add_group β) (f : Set) : Set.
Instance is_add_group_hom_to_is_add_hom (α : Set) (β : Set) `(_inst_1 : add_group α) `(_inst_2 : add_group β) (f : Set) `(c : @is_add_group_hom α β _inst_1 _inst_2 f) : @is_add_hom α β (@add_semigroup_to_has_add α (@add_monoid_to_add_semigroup α (@add_group_to_add_monoid α _inst_1))) (@add_semigroup_to_has_add β (@add_monoid_to_add_semigroup β (@add_group_to_add_monoid β _inst_2))) f := {}.
Class is_group_hom (α : Set) (β : Set) `(_inst_1 : group α) `(_inst_2 : group β) (f : Set) : Set.
Instance is_group_hom_to_is_mul_hom (α : Set) (β : Set) `(_inst_1 : group α) `(_inst_2 : group β) (f : Set) `(c : @is_group_hom α β _inst_1 _inst_2 f) : @is_mul_hom α β (@semigroup_to_has_mul α (@monoid_to_semigroup α (@group_to_monoid α _inst_1))) (@semigroup_to_has_mul β (@monoid_to_semigroup β (@group_to_monoid β _inst_2))) f := {}.
Instance is_group_hom_to_is_monoid_hom (α : Set) (β : Set) `(_inst_1 : group α) `(_inst_2 : group β) (f : Set) `(_inst_3 : @is_group_hom α β _inst_1 _inst_2 f) : @is_monoid_hom α β (@group_to_monoid α _inst_1) (@group_to_monoid β _inst_2) f := {}.
Instance is_add_group_hom_to_is_add_monoid_hom (α : Set) (β : Set) `(_inst_1 : add_group α) `(_inst_2 : add_group β) (f : Set) `(_inst_3 : @is_add_group_hom α β _inst_1 _inst_2 f) : @is_add_monoid_hom α β (@add_group_to_add_monoid α _inst_1) (@add_group_to_add_monoid β _inst_2) f := {}.
Class directed_order (α : Set) : Set.
Instance directed_order_to_preorder (α : Set) `(c : directed_order α) : preorder α := {}.
Class lattice_has_sup (α : Set) : Set.
Class lattice_has_inf (α : Set) : Set.
Class lattice_semilattice_sup (α : Set) : Set.
Instance lattice_semilattice_sup_to_has_sup (α : Set) `(s : lattice_semilattice_sup α) : lattice_has_sup α := {}.
Instance lattice_semilattice_sup_to_partial_order (α : Set) `(s : lattice_semilattice_sup α) : partial_order α := {}.
Class lattice_semilattice_inf (α : Set) : Set.
Instance lattice_semilattice_inf_to_has_inf (α : Set) `(s : lattice_semilattice_inf α) : lattice_has_inf α := {}.
Instance lattice_semilattice_inf_to_partial_order (α : Set) `(s : lattice_semilattice_inf α) : partial_order α := {}.
Class lattice_lattice (α : Set) : Set.
Instance lattice_lattice_to_semilattice_sup (α : Set) `(s : lattice_lattice α) : lattice_semilattice_sup α := {}.
Instance lattice_lattice_to_semilattice_inf (α : Set) `(s : lattice_lattice α) : lattice_semilattice_inf α := {}.
Class lattice_distrib_lattice (α : Set) : Set.
Instance lattice_distrib_lattice_to_lattice (α : Set) `(s : lattice_distrib_lattice α) : lattice_lattice α := {}.
Instance lattice_lattice_of_decidable_linear_order (α : Set) `(o : decidable_linear_order α) : lattice_lattice α := {}.
Instance lattice_distrib_lattice_of_decidable_linear_order (α : Set) `(o : decidable_linear_order α) : lattice_distrib_lattice α := {}.
Class lattice_has_top (α : Set) : Set.
Class lattice_has_bot (α : Set) : Set.
Class lattice_order_top (α : Set) : Set.
Instance lattice_order_top_to_has_top (α : Set) `(s : lattice_order_top α) : lattice_has_top α := {}.
Instance lattice_order_top_to_partial_order (α : Set) `(s : lattice_order_top α) : partial_order α := {}.
Class lattice_order_bot (α : Set) : Set.
Instance lattice_order_bot_to_has_bot (α : Set) `(s : lattice_order_bot α) : lattice_has_bot α := {}.
Instance lattice_order_bot_to_partial_order (α : Set) `(s : lattice_order_bot α) : partial_order α := {}.
Class lattice_semilattice_sup_top (α : Set) : Set.
Instance lattice_semilattice_sup_top_to_order_top (α : Set) `(s : lattice_semilattice_sup_top α) : lattice_order_top α := {}.
Instance lattice_semilattice_sup_top_to_semilattice_sup (α : Set) `(s : lattice_semilattice_sup_top α) : lattice_semilattice_sup α := {}.
Class lattice_semilattice_sup_bot (α : Set) : Set.
Instance lattice_semilattice_sup_bot_to_order_bot (α : Set) `(s : lattice_semilattice_sup_bot α) : lattice_order_bot α := {}.
Instance lattice_semilattice_sup_bot_to_semilattice_sup (α : Set) `(s : lattice_semilattice_sup_bot α) : lattice_semilattice_sup α := {}.
Class lattice_semilattice_inf_top (α : Set) : Set.
Instance lattice_semilattice_inf_top_to_order_top (α : Set) `(s : lattice_semilattice_inf_top α) : lattice_order_top α := {}.
Instance lattice_semilattice_inf_top_to_semilattice_inf (α : Set) `(s : lattice_semilattice_inf_top α) : lattice_semilattice_inf α := {}.
Class lattice_semilattice_inf_bot (α : Set) : Set.
Instance lattice_semilattice_inf_bot_to_order_bot (α : Set) `(s : lattice_semilattice_inf_bot α) : lattice_order_bot α := {}.
Instance lattice_semilattice_inf_bot_to_semilattice_inf (α : Set) `(s : lattice_semilattice_inf_bot α) : lattice_semilattice_inf α := {}.
Class lattice_bounded_lattice (α : Set) : Set.
Instance lattice_bounded_lattice_to_lattice (α : Set) `(s : lattice_bounded_lattice α) : lattice_lattice α := {}.
Instance lattice_bounded_lattice_to_order_top (α : Set) `(s : lattice_bounded_lattice α) : lattice_order_top α := {}.
Instance lattice_bounded_lattice_to_order_bot (α : Set) `(s : lattice_bounded_lattice α) : lattice_order_bot α := {}.
Instance lattice_semilattice_inf_top_of_bounded_lattice (α : Set) `(bl : lattice_bounded_lattice α) : lattice_semilattice_inf_top α := {}.
Instance lattice_semilattice_inf_bot_of_bounded_lattice (α : Set) `(bl : lattice_bounded_lattice α) : lattice_semilattice_inf_bot α := {}.
Instance lattice_semilattice_sup_top_of_bounded_lattice (α : Set) `(bl : lattice_bounded_lattice α) : lattice_semilattice_sup_top α := {}.
Instance lattice_semilattice_sup_bot_of_bounded_lattice (α : Set) `(bl : lattice_bounded_lattice α) : lattice_semilattice_sup_bot α := {}.
Class category_theory_groupoid (obj : Set) : Set.
Instance category_theory_groupoid_to_category (obj : Set) `(c : category_theory_groupoid obj) : category_theory_category obj := {}.
Class lattice_bounded_distrib_lattice (α : Set) : Set.
Instance lattice_bounded_distrib_lattice_to_distrib_lattice (α : Set) `(s : lattice_bounded_distrib_lattice α) : lattice_distrib_lattice α := {}.
Instance lattice_bounded_distrib_lattice_to_bounded_lattice (α : Set) `(s : lattice_bounded_distrib_lattice α) : lattice_bounded_lattice α := {}.
Instance category_theory_is_iso_of_groupoid (C : Set) `(𝒞 : category_theory_groupoid C) (X : Set) (Y : Set) (f : Set) : @category_theory_is_iso C (@category_theory_groupoid_to_category C 𝒞) X Y f := {}.
Class category_theory_concrete_category (C : Set) : Set.
Instance category_theory_concrete_category_to_category (C : Set) `(c : category_theory_concrete_category C) : category_theory_category C := {}.
Class category_theory_has_forget₂ (C : Set) (D : Set) `(_inst_1 : category_theory_concrete_category C) `(_inst_2 : category_theory_concrete_category D) : Set.
Class category_theory_is_equivalence (C : Set) `(𝒞 : category_theory_category C) (D : Set) `(𝒟 : category_theory_category D) (F : Set) : Set.
Class category_theory_ess_surj (C : Set) `(𝒞 : category_theory_category C) (D : Set) `(𝒟 : category_theory_category D) (F : Set) : Set.
Instance category_theory_equivalence_faithful_of_equivalence (C : Set) `(𝒞 : category_theory_category C) (D : Set) `(𝒟 : category_theory_category D) (F : Set) `(_inst_1 : @category_theory_is_equivalence C 𝒞 D 𝒟 F) : @category_theory_faithful C 𝒞 D 𝒟 F := {}.
Class category_theory_bundled_hom (c : Set) (hom : Set) : Set.
Class category_theory_unbundled_hom (c : Set) (hom : Set) : Set.
Instance category_theory_equivalence_full_of_equivalence (C : Set) `(𝒞 : category_theory_category C) (D : Set) `(𝒟 : category_theory_category D) (F : Set) `(_inst_1 : @category_theory_is_equivalence C 𝒞 D 𝒟 F) : @category_theory_full C 𝒞 D 𝒟 F := {}.
Class lattice_boolean_algebra (α : Set) : Set.
Instance lattice_boolean_algebra_to_bounded_distrib_lattice (α : Set) `(s : lattice_boolean_algebra α) : lattice_bounded_distrib_lattice α := {}.
Instance lattice_boolean_algebra_to_has_neg (α : Set) `(s : lattice_boolean_algebra α) : has_neg α := {}.
Instance lattice_boolean_algebra_to_has_sub (α : Set) `(s : lattice_boolean_algebra α) : has_sub α := {}.
Class category_theory_is_left_adjoint (C : Set) `(𝒞 : category_theory_category C) (D : Set) `(𝒟 : category_theory_category D) (left : Set) : Set.
Class category_theory_is_right_adjoint (C : Set) `(𝒞 : category_theory_category C) (D : Set) `(𝒟 : category_theory_category D) (right : Set) : Set.
Class ordered_comm_monoid (α : Set) : Set.
Instance ordered_comm_monoid_to_add_comm_monoid (α : Set) `(s : ordered_comm_monoid α) : add_comm_monoid α := {}.
Instance ordered_comm_monoid_to_partial_order (α : Set) `(s : ordered_comm_monoid α) : partial_order α := {}.
Class canonically_ordered_monoid (α : Set) : Set.
Instance canonically_ordered_monoid_to_ordered_comm_monoid (α : Set) `(s : canonically_ordered_monoid α) : ordered_comm_monoid α := {}.
Instance canonically_ordered_monoid_to_order_bot (α : Set) `(s : canonically_ordered_monoid α) : lattice_order_bot α := {}.
Class is_semiring_hom (α : Set) (β : Set) `(_inst_1 : semiring α) `(_inst_2 : semiring β) (f : Set) : Set.
Instance is_semiring_hom_is_add_monoid_hom (α : Set) (β : Set) `(_inst_1 : semiring α) `(_inst_2 : semiring β) (f : Set) `(_inst_3 : @is_semiring_hom α β _inst_1 _inst_2 f) : @is_add_monoid_hom α β (@add_comm_monoid_to_add_monoid α (@semiring_to_add_comm_monoid α _inst_1)) (@add_comm_monoid_to_add_monoid β (@semiring_to_add_comm_monoid β _inst_2)) f := {}.
Instance is_semiring_hom_is_monoid_hom (α : Set) (β : Set) `(_inst_1 : semiring α) `(_inst_2 : semiring β) (f : Set) `(_inst_3 : @is_semiring_hom α β _inst_1 _inst_2 f) : @is_monoid_hom α β (@semiring_to_monoid α _inst_1) (@semiring_to_monoid β _inst_2) f := {}.
Class is_ring_hom (α : Set) (β : Set) `(_inst_1 : ring α) `(_inst_2 : ring β) (f : Set) : Set.
Instance is_ring_hom_is_semiring_hom (α : Set) (β : Set) `(_inst_1 : ring α) `(_inst_2 : ring β) (f : Set) `(_inst_3 : @is_ring_hom α β _inst_1 _inst_2 f) : @is_semiring_hom α β (@ring_to_semiring α _inst_1) (@ring_to_semiring β _inst_2) f := {}.
Instance is_ring_hom_is_add_group_hom (α : Set) (β : Set) `(_inst_1 : ring α) `(_inst_2 : ring β) (f : Set) `(_inst_3 : @is_ring_hom α β _inst_1 _inst_2 f) : @is_add_group_hom α β (@add_comm_group_to_add_group α (@ring_to_add_comm_group α _inst_1)) (@add_comm_group_to_add_group β (@ring_to_add_comm_group β _inst_2)) f := {}.
Class nonzero_comm_semiring (α : Set) : Set.
Instance nonzero_comm_semiring_to_comm_semiring (α : Set) `(s : nonzero_comm_semiring α) : comm_semiring α := {}.
Instance nonzero_comm_semiring_to_zero_ne_one_class (α : Set) `(s : nonzero_comm_semiring α) : zero_ne_one_class α := {}.
Class nonzero_comm_ring (α : Set) : Set.
Instance nonzero_comm_ring_to_comm_ring (α : Set) `(s : nonzero_comm_ring α) : comm_ring α := {}.
Instance nonzero_comm_ring_to_zero_ne_one_class (α : Set) `(s : nonzero_comm_ring α) : zero_ne_one_class α := {}.
Instance nonzero_comm_ring_to_nonzero_comm_semiring (α : Set) `(I : nonzero_comm_ring α) : nonzero_comm_semiring α := {}.
Instance integral_domain_to_nonzero_comm_ring (α : Set) `(id : integral_domain α) : nonzero_comm_ring α := {}.
Class domain (α : Set) : Set.
Instance domain_to_ring (α : Set) `(s : domain α) : ring α := {}.
Instance domain_to_no_zero_divisors (α : Set) `(s : domain α) : no_zero_divisors α := {}.
Instance domain_to_zero_ne_one_class (α : Set) `(s : domain α) : zero_ne_one_class α := {}.
Instance integral_domain_to_domain (α : Set) `(s : integral_domain α) : domain α := {}.
Instance division_ring_has_div' (α : Set) `(_inst_1 : division_ring α) : has_div α := {}.
Instance division_ring_to_domain (α : Set) `(s : division_ring α) : domain α := {}.
Instance field_to_integral_domain (α : Set) `(F : field α) : integral_domain α := {}.
Instance ordered_cancel_comm_monoid_to_ordered_comm_monoid (α : Set) `(H : ordered_cancel_comm_monoid α) : ordered_comm_monoid α := {}.
Instance decidable_linear_ordered_comm_group_decidable_linear_ordered_cancel_comm_monoid (α : Set) `(s : decidable_linear_ordered_comm_group α) : decidable_linear_ordered_cancel_comm_monoid α := {}.
Class nonneg_comm_group (α : Set) : Set.
Instance nonneg_comm_group_to_add_comm_group (α : Set) `(s : nonneg_comm_group α) : add_comm_group α := {}.
Instance nonneg_comm_group_to_ordered_comm_group (α : Set) `(s : nonneg_comm_group α) : ordered_comm_group α := {}.
Class char_zero (α : Set) `(_inst_1 : add_monoid α) `(_inst_2 : has_one α) : Set.
Instance linear_ordered_semiring_to_char_zero (α : Set) `(_inst_1 : linear_ordered_semiring α) : @char_zero α (@add_comm_monoid_to_add_monoid α (@ordered_comm_monoid_to_add_comm_monoid α (@ordered_cancel_comm_monoid_to_ordered_comm_monoid α (@ordered_semiring_to_ordered_cancel_comm_monoid α (@linear_ordered_semiring_to_ordered_semiring α _inst_1))))) (@monoid_to_has_one α (@semiring_to_monoid α (@ordered_semiring_to_semiring α (@linear_ordered_semiring_to_ordered_semiring α _inst_1)))) := {}.
Class category_theory_monoidal_category (C : Set) `(𝒞 : category_theory_category C) : Set.
Instance linear_ordered_semiring_to_no_top_order (α : Set) `(_inst_1 : linear_ordered_semiring α) : @no_top_order α (@partial_order_to_preorder α (@ordered_comm_monoid_to_partial_order α (@ordered_cancel_comm_monoid_to_ordered_comm_monoid α (@ordered_semiring_to_ordered_cancel_comm_monoid α (@linear_ordered_semiring_to_ordered_semiring α _inst_1))))) := {}.
Instance linear_ordered_semiring_to_no_bot_order (α : Set) `(_inst_1 : linear_ordered_ring α) : @no_bot_order α (@partial_order_to_preorder α (@ordered_comm_monoid_to_partial_order α (@ordered_cancel_comm_monoid_to_ordered_comm_monoid α (@ordered_semiring_to_ordered_cancel_comm_monoid α (@ordered_ring_to_ordered_semiring α (@linear_ordered_ring_to_ordered_ring α _inst_1)))))) := {}.
Instance linear_ordered_ring_to_domain (α : Set) `(s : linear_ordered_ring α) : domain α := {}.
Class nonneg_ring (α : Set) : Set.
Instance nonneg_ring_to_ring (α : Set) `(s : nonneg_ring α) : ring α := {}.
Instance nonneg_ring_to_zero_ne_one_class (α : Set) `(s : nonneg_ring α) : zero_ne_one_class α := {}.
Instance nonneg_ring_to_nonneg_comm_group (α : Set) `(s : nonneg_ring α) : nonneg_comm_group α := {}.
Class linear_nonneg_ring (α : Set) : Set.
Instance linear_nonneg_ring_to_domain (α : Set) `(s : linear_nonneg_ring α) : domain α := {}.
Instance linear_nonneg_ring_to_nonneg_comm_group (α : Set) `(s : linear_nonneg_ring α) : nonneg_comm_group α := {}.
Instance nonneg_ring_to_ordered_ring (α : Set) `(s : nonneg_ring α) : ordered_ring α := {}.
Instance linear_nonneg_ring_to_nonneg_ring (α : Set) `(s : linear_nonneg_ring α) : nonneg_ring α := {}.
Instance linear_nonneg_ring_to_linear_order (α : Set) `(s : linear_nonneg_ring α) : linear_order α := {}.
Instance linear_nonneg_ring_to_linear_ordered_ring (α : Set) `(s : linear_nonneg_ring α) : linear_ordered_ring α := {}.
Class canonically_ordered_comm_semiring (α : Set) : Set.
Instance canonically_ordered_comm_semiring_to_canonically_ordered_monoid (α : Set) `(s : canonically_ordered_comm_semiring α) : canonically_ordered_monoid α := {}.
Instance canonically_ordered_comm_semiring_to_comm_semiring (α : Set) `(s : canonically_ordered_comm_semiring α) : comm_semiring α := {}.
Instance canonically_ordered_comm_semiring_to_zero_ne_one_class (α : Set) `(s : canonically_ordered_comm_semiring α) : zero_ne_one_class α := {}.
Instance linear_ordered_field_to_densely_ordered (α : Set) `(_inst_1 : linear_ordered_field α) : @densely_ordered α (@partial_order_to_preorder α (@ordered_comm_monoid_to_partial_order α (@ordered_cancel_comm_monoid_to_ordered_comm_monoid α (@ordered_semiring_to_ordered_cancel_comm_monoid α (@ordered_ring_to_ordered_semiring α (@linear_ordered_ring_to_ordered_ring α (@linear_ordered_field_to_linear_ordered_ring α _inst_1))))))) := {}.
Instance linear_ordered_field_to_no_top_order (α : Set) `(_inst_1 : linear_ordered_field α) : @no_top_order α (@partial_order_to_preorder α (@ordered_comm_monoid_to_partial_order α (@ordered_cancel_comm_monoid_to_ordered_comm_monoid α (@ordered_semiring_to_ordered_cancel_comm_monoid α (@ordered_ring_to_ordered_semiring α (@linear_ordered_ring_to_ordered_ring α (@linear_ordered_field_to_linear_ordered_ring α _inst_1))))))) := {}.
Class category_theory_representable (C : Set) `(𝒞 : category_theory_category C) (F : Set) : Set.
Instance linear_ordered_field_to_no_bot_order (α : Set) `(_inst_1 : linear_ordered_field α) : @no_bot_order α (@partial_order_to_preorder α (@ordered_comm_monoid_to_partial_order α (@ordered_cancel_comm_monoid_to_ordered_comm_monoid α (@ordered_semiring_to_ordered_cancel_comm_monoid α (@ordered_ring_to_ordered_semiring α (@linear_ordered_ring_to_ordered_ring α (@linear_ordered_field_to_linear_ordered_ring α _inst_1))))))) := {}.
Class is_ring_anti_hom (R : Set) (F : Set) `(_inst_1 : ring R) `(_inst_2 : ring F) (f : Set) : Set.
Instance is_ring_anti_hom_is_add_group_hom (R : Set) (F : Set) `(_inst_1 : ring R) `(_inst_2 : ring F) (f : Set) `(_inst_3 : @is_ring_anti_hom R F _inst_1 _inst_2 f) : @is_add_group_hom R F (@add_comm_group_to_add_group R (@ring_to_add_comm_group R _inst_1)) (@add_comm_group_to_add_group F (@ring_to_add_comm_group F _inst_2)) f := {}.
Class lattice_has_Sup (α : Set) : Set.
Class lattice_has_Inf (α : Set) : Set.
Class lattice_complete_lattice (α : Set) : Set.
Instance lattice_complete_lattice_to_bounded_lattice (α : Set) `(s : lattice_complete_lattice α) : lattice_bounded_lattice α := {}.
Instance lattice_complete_lattice_to_has_Sup (α : Set) `(s : lattice_complete_lattice α) : lattice_has_Sup α := {}.
Instance lattice_complete_lattice_to_has_Inf (α : Set) `(s : lattice_complete_lattice α) : lattice_has_Inf α := {}.
Class lattice_complete_linear_order (α : Set) : Set.
Instance lattice_complete_linear_order_to_complete_lattice (α : Set) `(s : lattice_complete_linear_order α) : lattice_complete_lattice α := {}.
Instance lattice_complete_linear_order_to_decidable_linear_order (α : Set) `(s : lattice_complete_linear_order α) : decidable_linear_order α := {}.
Class category_theory_reflective (C : Set) `(𝒞 : category_theory_category C) (D : Set) `(𝒟 : category_theory_category D) (R : Set) : Set.
Instance category_theory_reflective_to_is_right_adjoint (C : Set) `(𝒞 : category_theory_category C) (D : Set) `(𝒟 : category_theory_category D) (R : Set) `(c : @category_theory_reflective C 𝒞 D 𝒟 R) : @category_theory_is_right_adjoint C 𝒞 D 𝒟 R := {}.
Instance category_theory_reflective_to_full (C : Set) `(𝒞 : category_theory_category C) (D : Set) `(𝒟 : category_theory_category D) (R : Set) `(c : @category_theory_reflective C 𝒞 D 𝒟 R) : @category_theory_full D 𝒟 C 𝒞 R := {}.
Instance category_theory_reflective_to_faithful (C : Set) `(𝒞 : category_theory_category C) (D : Set) `(𝒟 : category_theory_category D) (R : Set) `(c : @category_theory_reflective C 𝒞 D 𝒟 R) : @category_theory_faithful D 𝒟 C 𝒞 R := {}.
Class category_theory_monadic_right_adjoint (C : Set) `(𝒞 : category_theory_category C) (D : Set) `(𝒟 : category_theory_category D) (R : Set) : Set.
Instance category_theory_monadic_right_adjoint_to_is_right_adjoint (C : Set) `(𝒞 : category_theory_category C) (D : Set) `(𝒟 : category_theory_category D) (R : Set) `(c : @category_theory_monadic_right_adjoint C 𝒞 D 𝒟 R) : @category_theory_is_right_adjoint C 𝒞 D 𝒟 R := {}.
Instance category_theory_monadic_of_reflective (C : Set) `(𝒞 : category_theory_category C) (D : Set) `(𝒟 : category_theory_category D) (R : Set) `(_inst_1 : @category_theory_reflective C 𝒞 D 𝒟 R) : @category_theory_monadic_right_adjoint C 𝒞 D 𝒟 R := {}.
Class lattice_complete_distrib_lattice (α : Set) : Set.
Instance lattice_complete_distrib_lattice_to_complete_lattice (α : Set) `(s : lattice_complete_distrib_lattice α) : lattice_complete_lattice α := {}.
Instance lattice_lattice_bounded_distrib_lattice (α : Set) `(d : lattice_complete_distrib_lattice α) : lattice_bounded_distrib_lattice α := {}.
Class lattice_complete_boolean_algebra (α : Set) : Set.
Instance lattice_complete_boolean_algebra_to_boolean_algebra (α : Set) `(s : lattice_complete_boolean_algebra α) : lattice_boolean_algebra α := {}.
Instance lattice_complete_boolean_algebra_to_complete_distrib_lattice (α : Set) `(s : lattice_complete_boolean_algebra α) : lattice_complete_distrib_lattice α := {}.
Class category_theory_limits_has_limit (J : Set) `(_inst_1 : category_theory_category J) (C : Set) `(𝒞 : category_theory_category C) (F : Set) : Set.
Class category_theory_limits_has_limits_of_shape (J : Set) `(_inst_1 : category_theory_category J) (C : Set) `(𝒞 : category_theory_category C) : Set.
Class category_theory_limits_has_limits (C : Set) `(𝒞 : category_theory_category C) : Set.
Instance category_theory_limits_has_limit_of_has_limits_of_shape (C : Set) `(𝒞 : category_theory_category C) (J : Set) `(_inst_3 : category_theory_category J) `(H : @category_theory_limits_has_limits_of_shape J _inst_3 C 𝒞) (F : Set) : @category_theory_limits_has_limit J _inst_3 C 𝒞 F := {}.
Instance category_theory_limits_has_limits_of_shape_of_has_limits (C : Set) `(𝒞 : category_theory_category C) (J : Set) `(_inst_3 : category_theory_category J) `(H : @category_theory_limits_has_limits C 𝒞) : @category_theory_limits_has_limits_of_shape J _inst_3 C 𝒞 := {}.
Class wseq_is_finite (α : Set) (s : Set) : Set.
Class wseq_productive (α : Set) (s : Set) : Set.
Class euclidean_domain (α : Set) : Set.
Instance euclidean_domain_to_nonzero_comm_ring (α : Set) `(c : euclidean_domain α) : nonzero_comm_ring α := {}.
Instance euclidean_domain_has_div (α : Set) `(_inst_1 : euclidean_domain α) : has_div α := {}.
Instance euclidean_domain_has_mod (α : Set) `(_inst_1 : euclidean_domain α) : has_mod α := {}.
Class category_theory_limits_has_colimit (J : Set) `(_inst_1 : category_theory_category J) (C : Set) `(𝒞 : category_theory_category C) (F : Set) : Set.
Class category_theory_limits_has_colimits_of_shape (J : Set) `(_inst_1 : category_theory_category J) (C : Set) `(𝒞 : category_theory_category C) : Set.
Class category_theory_limits_has_colimits (C : Set) `(𝒞 : category_theory_category C) : Set.
Instance euclidean_domain_integral_domain (α : Set) `(e : euclidean_domain α) : integral_domain α := {}.
Instance category_theory_limits_has_colimit_of_has_colimits_of_shape (C : Set) `(𝒞 : category_theory_category C) (J : Set) `(_inst_3 : category_theory_category J) `(H : @category_theory_limits_has_colimits_of_shape J _inst_3 C 𝒞) (F : Set) : @category_theory_limits_has_colimit J _inst_3 C 𝒞 F := {}.
Instance category_theory_limits_has_colimits_of_shape_of_has_colimits (C : Set) `(𝒞 : category_theory_category C) (J : Set) `(_inst_3 : category_theory_category J) `(H : @category_theory_limits_has_colimits C 𝒞) : @category_theory_limits_has_colimits_of_shape J _inst_3 C 𝒞 := {}.
Instance discrete_field_to_euclidean_domain (K : Set) `(_inst_1 : discrete_field K) : euclidean_domain K := {}.
Class category_theory_limits_preserves_limit (C : Set) `(𝒞 : category_theory_category C) (D : Set) `(𝒟 : category_theory_category D) (J : Set) `(_inst_1 : category_theory_category J) (K : Set) (F : Set) : Set.
Class category_theory_limits_preserves_colimit (C : Set) `(𝒞 : category_theory_category C) (D : Set) `(𝒟 : category_theory_category D) (J : Set) `(_inst_1 : category_theory_category J) (K : Set) (F : Set) : Set.
Class category_theory_limits_preserves_limits_of_shape (C : Set) `(𝒞 : category_theory_category C) (D : Set) `(𝒟 : category_theory_category D) (J : Set) `(_inst_2 : category_theory_category J) (F : Set) : Set.
Class category_theory_limits_preserves_colimits_of_shape (C : Set) `(𝒞 : category_theory_category C) (D : Set) `(𝒟 : category_theory_category D) (J : Set) `(_inst_2 : category_theory_category J) (F : Set) : Set.
Class category_theory_limits_preserves_limits (C : Set) `(𝒞 : category_theory_category C) (D : Set) `(𝒟 : category_theory_category D) (F : Set) : Set.
Class category_theory_limits_preserves_colimits (C : Set) `(𝒞 : category_theory_category C) (D : Set) `(𝒟 : category_theory_category D) (F : Set) : Set.
Instance category_theory_limits_preserves_limits_of_shape_preserves_limit (C : Set) `(𝒞 : category_theory_category C) (D : Set) `(𝒟 : category_theory_category D) (J : Set) `(_inst_2 : category_theory_category J) (F : Set) `(c : @category_theory_limits_preserves_limits_of_shape C 𝒞 D 𝒟 J _inst_2 F) (K : Set) : @category_theory_limits_preserves_limit C 𝒞 D 𝒟 J _inst_2 K F := {}.
Instance category_theory_limits_preserves_limits_preserves_limits_of_shape (C : Set) `(𝒞 : category_theory_category C) (D : Set) `(𝒟 : category_theory_category D) (F : Set) `(c : @category_theory_limits_preserves_limits C 𝒞 D 𝒟 F) (J : Set) `(𝒥 : category_theory_category J) : @category_theory_limits_preserves_limits_of_shape C 𝒞 D 𝒟 J 𝒥 F := {}.
Instance category_theory_limits_preserves_colimits_of_shape_preserves_colimit (C : Set) `(𝒞 : category_theory_category C) (D : Set) `(𝒟 : category_theory_category D) (J : Set) `(_inst_2 : category_theory_category J) (F : Set) `(c : @category_theory_limits_preserves_colimits_of_shape C 𝒞 D 𝒟 J _inst_2 F) (K : Set) : @category_theory_limits_preserves_colimit C 𝒞 D 𝒟 J _inst_2 K F := {}.
Instance category_theory_limits_preserves_colimits_preserves_colimits_of_shape (C : Set) `(𝒞 : category_theory_category C) (D : Set) `(𝒟 : category_theory_category D) (F : Set) `(c : @category_theory_limits_preserves_colimits C 𝒞 D 𝒟 F) (J : Set) `(𝒥 : category_theory_category J) : @category_theory_limits_preserves_colimits_of_shape C 𝒞 D 𝒟 J 𝒥 F := {}.
Instance category_theory_limits_has_limits_of_complete_lattice (α : Set) `(_inst_1 : lattice_complete_lattice α) : @category_theory_limits_has_limits α (@preorder_small_category α (@partial_order_to_preorder α (@lattice_order_bot_to_partial_order α (@lattice_bounded_lattice_to_order_bot α (@lattice_complete_lattice_to_bounded_lattice α _inst_1))))) := {}.
Instance category_theory_limits_has_colimits_of_complete_lattice (α : Set) `(_inst_1 : lattice_complete_lattice α) : @category_theory_limits_has_colimits α (@preorder_small_category α (@partial_order_to_preorder α (@lattice_order_bot_to_partial_order α (@lattice_bounded_lattice_to_order_bot α (@lattice_complete_lattice_to_bounded_lattice α _inst_1))))) := {}.
Class category_theory_limits_reflects_limit (C : Set) `(𝒞 : category_theory_category C) (D : Set) `(𝒟 : category_theory_category D) (J : Set) `(_inst_1 : category_theory_category J) (K : Set) (F : Set) : Set.
Class encodable (α : Set) : Set.
Class category_theory_limits_reflects_colimit (C : Set) `(𝒞 : category_theory_category C) (D : Set) `(𝒟 : category_theory_category D) (J : Set) `(_inst_1 : category_theory_category J) (K : Set) (F : Set) : Set.
Class category_theory_limits_reflects_limits_of_shape (C : Set) `(𝒞 : category_theory_category C) (D : Set) `(𝒟 : category_theory_category D) (J : Set) `(_inst_2 : category_theory_category J) (F : Set) : Set.
Class category_theory_limits_reflects_colimits_of_shape (C : Set) `(𝒞 : category_theory_category C) (D : Set) `(𝒟 : category_theory_category D) (J : Set) `(_inst_2 : category_theory_category J) (F : Set) : Set.
Class category_theory_limits_reflects_limits (C : Set) `(𝒞 : category_theory_category C) (D : Set) `(𝒟 : category_theory_category D) (F : Set) : Set.
Class category_theory_limits_reflects_colimits (C : Set) `(𝒞 : category_theory_category C) (D : Set) `(𝒟 : category_theory_category D) (F : Set) : Set.
Instance category_theory_limits_reflects_limit_of_reflects_limits_of_shape (C : Set) `(𝒞 : category_theory_category C) (D : Set) `(𝒟 : category_theory_category D) (J : Set) `(_inst_1 : category_theory_category J) (K : Set) (F : Set) `(H : @category_theory_limits_reflects_limits_of_shape C 𝒞 D 𝒟 J _inst_1 F) : @category_theory_limits_reflects_limit C 𝒞 D 𝒟 J _inst_1 K F := {}.
Instance category_theory_limits_reflects_colimit_of_reflects_colimits_of_shape (C : Set) `(𝒞 : category_theory_category C) (D : Set) `(𝒟 : category_theory_category D) (J : Set) `(_inst_1 : category_theory_category J) (K : Set) (F : Set) `(H : @category_theory_limits_reflects_colimits_of_shape C 𝒞 D 𝒟 J _inst_1 F) : @category_theory_limits_reflects_colimit C 𝒞 D 𝒟 J _inst_1 K F := {}.
Instance category_theory_limits_reflects_limits_of_shape_of_reflects_limits (C : Set) `(𝒞 : category_theory_category C) (D : Set) `(𝒟 : category_theory_category D) (J : Set) `(_inst_1 : category_theory_category J) (F : Set) `(H : @category_theory_limits_reflects_limits C 𝒞 D 𝒟 F) : @category_theory_limits_reflects_limits_of_shape C 𝒞 D 𝒟 J _inst_1 F := {}.
Instance category_theory_limits_reflects_colimits_of_shape_of_reflects_colimits (C : Set) `(𝒞 : category_theory_category C) (D : Set) `(𝒟 : category_theory_category D) (J : Set) `(_inst_1 : category_theory_category J) (F : Set) `(H : @category_theory_limits_reflects_colimits C 𝒞 D 𝒟 F) : @category_theory_limits_reflects_colimits_of_shape C 𝒞 D 𝒟 J _inst_1 F := {}.
Instance category_theory_adjunction_left_adjoint_preserves_colimits (C : Set) `(𝒞 : category_theory_category C) (D : Set) `(𝒟 : category_theory_category D) (F : Set) (G : Set) (adj : Set) : @category_theory_limits_preserves_colimits C 𝒞 D 𝒟 F := {}.
Instance category_theory_adjunction_is_equivalence_preserves_colimits (C : Set) `(𝒞 : category_theory_category C) (D : Set) `(𝒟 : category_theory_category D) (E : Set) `(_inst_2 : @category_theory_is_equivalence C 𝒞 D 𝒟 E) : @category_theory_limits_preserves_colimits C 𝒞 D 𝒟 E := {}.
Instance category_theory_adjunction_right_adjoint_preserves_limits (C : Set) `(𝒞 : category_theory_category C) (D : Set) `(𝒟 : category_theory_category D) (F : Set) (G : Set) (adj : Set) : @category_theory_limits_preserves_limits D 𝒟 C 𝒞 G := {}.
Instance category_theory_adjunction_is_equivalence_preserves_limits (C : Set) `(𝒞 : category_theory_category C) (D : Set) `(𝒟 : category_theory_category D) (E : Set) `(_inst_2 : @category_theory_is_equivalence D 𝒟 C 𝒞 E) : @category_theory_limits_preserves_limits D 𝒟 C 𝒞 E := {}.
Class irreducible (α : Set) `(_inst_1 : monoid α) (p : Set) : Set.
Class floor_ring (α : Set) `(_inst_1 : linear_ordered_ring α) : Set.
Class archimedean (α : Set) `(_inst_1 : ordered_comm_monoid α) : Set.
Class normalization_domain (α : Set) : Set.
Instance normalization_domain_to_integral_domain (α : Set) `(s : normalization_domain α) : integral_domain α := {}.
Class gcd_domain (α : Set) : Set.
Instance gcd_domain_to_normalization_domain (α : Set) `(s : gcd_domain α) : normalization_domain α := {}.
Class unique_factorization_domain (α : Set) `(_inst_1 : integral_domain α) : Set.
Class zsqrtd_nonsquare (x : Set) : Set.
Class fin2_is_lt (m : Set) (n : Set) : Set.
Class is_absolute_value (α : Set) `(_inst_1 : discrete_linear_ordered_field α) (β : Set) `(_inst_2 : ring β) (f : Set) : Set.
Class is_add_submonoid (β : Set) `(_inst_2 : add_monoid β) (s : Set) : Set.
Class is_submonoid (α : Set) `(_inst_1 : monoid α) (s : Set) : Set.
Class fintype (α : Set) : Set.
Instance unique_fintype (α : Set) `(_inst_1 : unique α) : fintype α := {}.
Class nat_prime (p : Set) : Set.
Class infinite (α : Set) : Set.
Instance infinite_nonempty (α : Set) `(_inst_1 : infinite α) : nonempty α := {}.
Class denumerable (α : Set) : Set.
Instance denumerable_to_encodable (α : Set) `(c : denumerable α) : encodable α := {}.
Class turing_pointed_map (Γ : Set) (Γ' : Set) `(_inst_1 : inhabited Γ) `(_inst_2 : inhabited Γ') (f : Set) : Set.
Class category_theory_limits_has_products (C : Set) `(𝒞 : category_theory_category C) : Set.
Class category_theory_limits_has_coproducts (C : Set) `(𝒞 : category_theory_category C) : Set.
Class category_theory_limits_fin_category (J : Set) `(_inst_1 : category_theory_category J) : Set.
Instance category_theory_limits_fin_category_fintype_obj (J : Set) `(_inst_1 : category_theory_category J) `(c : @category_theory_limits_fin_category J _inst_1) : fintype J := {}.
Class category_theory_limits_has_finite_limits (C : Set) `(𝒞 : category_theory_category C) : Set.
Class category_theory_limits_has_finite_colimits (C : Set) `(𝒞 : category_theory_category C) : Set.
Instance category_theory_limits_has_finite_limits_has_limits_of_shape (C : Set) `(𝒞 : category_theory_category C) `(c : @category_theory_limits_has_finite_limits C 𝒞) (J : Set) `(_inst_1 : category_theory_category J) `(_inst_2 : @category_theory_limits_fin_category J _inst_1) : @category_theory_limits_has_limits_of_shape J _inst_1 C 𝒞 := {}.
Instance category_theory_limits_has_finite_colimits_has_colimits_of_shape (C : Set) `(𝒞 : category_theory_category C) `(c : @category_theory_limits_has_finite_colimits C 𝒞) (J : Set) `(_inst_1 : category_theory_category J) `(_inst_2 : @category_theory_limits_fin_category J _inst_1) : @category_theory_limits_has_colimits_of_shape J _inst_1 C 𝒞 := {}.
Instance category_theory_limits_category_theory_limits_has_finite_limits (C : Set) `(𝒞 : category_theory_category C) `(_inst_1 : @category_theory_limits_has_limits C 𝒞) : @category_theory_limits_has_finite_limits C 𝒞 := {}.
Instance category_theory_limits_category_theory_limits_has_finite_colimits (C : Set) `(𝒞 : category_theory_category C) `(_inst_1 : @category_theory_limits_has_colimits C 𝒞) : @category_theory_limits_has_finite_colimits C 𝒞 := {}.
Class category_theory_limits_has_finite_products (C : Set) `(𝒞 : category_theory_category C) : Set.
Class category_theory_limits_has_finite_coproducts (C : Set) `(𝒞 : category_theory_category C) : Set.
Instance category_theory_limits_has_finite_products_of_has_products (C : Set) `(𝒞 : category_theory_category C) `(_inst_1 : @category_theory_limits_has_products C 𝒞) : @category_theory_limits_has_finite_products C 𝒞 := {}.
Instance category_theory_limits_has_finite_coproducts_of_has_coproducts (C : Set) `(𝒞 : category_theory_category C) `(_inst_1 : @category_theory_limits_has_coproducts C 𝒞) : @category_theory_limits_has_finite_coproducts C 𝒞 := {}.
Instance category_theory_limits_has_finite_products_of_has_finite_limits (C : Set) `(𝒞 : category_theory_category C) `(_inst_1 : @category_theory_limits_has_finite_limits C 𝒞) : @category_theory_limits_has_finite_products C 𝒞 := {}.
Instance category_theory_limits_has_finite_coproducts_of_has_finite_colimits (C : Set) `(𝒞 : category_theory_category C) `(_inst_1 : @category_theory_limits_has_finite_colimits C 𝒞) : @category_theory_limits_has_finite_coproducts C 𝒞 := {}.
Class category_theory_limits_has_terminal (C : Set) `(𝒞 : category_theory_category C) : Set.
Class category_theory_limits_has_initial (C : Set) `(𝒞 : category_theory_category C) : Set.
Instance category_theory_limits_category_theory_limits_has_terminal (C : Set) `(𝒞 : category_theory_category C) `(_inst_1 : @category_theory_limits_has_finite_products C 𝒞) : @category_theory_limits_has_terminal C 𝒞 := {}.
Instance category_theory_limits_category_theory_limits_has_initial (C : Set) `(𝒞 : category_theory_category C) `(_inst_1 : @category_theory_limits_has_finite_coproducts C 𝒞) : @category_theory_limits_has_initial C 𝒞 := {}.
Class lattice_conditionally_complete_lattice (α : Set) : Set.
Instance lattice_conditionally_complete_lattice_to_lattice (α : Set) `(s : lattice_conditionally_complete_lattice α) : lattice_lattice α := {}.
Instance lattice_conditionally_complete_lattice_to_has_Sup (α : Set) `(s : lattice_conditionally_complete_lattice α) : lattice_has_Sup α := {}.
Instance lattice_conditionally_complete_lattice_to_has_Inf (α : Set) `(s : lattice_conditionally_complete_lattice α) : lattice_has_Inf α := {}.
Class lattice_conditionally_complete_linear_order (α : Set) : Set.
Instance lattice_conditionally_complete_linear_order_to_conditionally_complete_lattice (α : Set) `(s : lattice_conditionally_complete_linear_order α) : lattice_conditionally_complete_lattice α := {}.
Instance lattice_conditionally_complete_linear_order_to_decidable_linear_order (α : Set) `(s : lattice_conditionally_complete_linear_order α) : decidable_linear_order α := {}.
Class lattice_conditionally_complete_linear_order_bot (α : Set) : Set.
Instance lattice_conditionally_complete_linear_order_bot_to_conditionally_complete_lattice (α : Set) `(s : lattice_conditionally_complete_linear_order_bot α) : lattice_conditionally_complete_lattice α := {}.
Instance lattice_conditionally_complete_linear_order_bot_to_decidable_linear_order (α : Set) `(s : lattice_conditionally_complete_linear_order_bot α) : decidable_linear_order α := {}.
Instance lattice_conditionally_complete_linear_order_bot_to_order_bot (α : Set) `(s : lattice_conditionally_complete_linear_order_bot α) : lattice_order_bot α := {}.
Instance lattice_conditionally_complete_lattice_of_complete_lattice (α : Set) `(_inst_1 : lattice_complete_lattice α) : lattice_conditionally_complete_lattice α := {}.
Instance lattice_conditionally_complete_linear_order_of_complete_linear_order (α : Set) `(_inst_1 : lattice_complete_linear_order α) : lattice_conditionally_complete_linear_order α := {}.
Class primcodable (α : Set) : Set.
Instance primcodable_to_encodable (α : Set) `(c : primcodable α) : encodable α := {}.
Instance primcodable_of_denumerable (α : Set) `(_inst_1 : denumerable α) : primcodable α := {}.
Class category_theory_limits_has_equalizers (C : Set) `(𝒞 : category_theory_category C) : Set.
Class category_theory_limits_has_coequalizers (C : Set) `(𝒞 : category_theory_category C) : Set.
Class measurable_space (α : Set) : Set.
Class category_theory_limits_has_pullbacks (C : Set) `(𝒞 : category_theory_category C) : Set.
Class category_theory_limits_has_pushouts (C : Set) `(𝒞 : category_theory_category C) : Set.
Class category_theory_limits_has_binary_products (C : Set) `(𝒞 : category_theory_category C) : Set.
Class category_theory_limits_has_binary_coproducts (C : Set) `(𝒞 : category_theory_category C) : Set.
Instance category_theory_limits_category_theory_limits_has_binary_products (C : Set) `(𝒞 : category_theory_category C) `(_inst_1 : @category_theory_limits_has_finite_products C 𝒞) : @category_theory_limits_has_binary_products C 𝒞 := {}.
Instance category_theory_limits_category_theory_limits_has_binary_coproducts (C : Set) `(𝒞 : category_theory_category C) `(_inst_1 : @category_theory_limits_has_finite_coproducts C 𝒞) : @category_theory_limits_has_binary_coproducts C 𝒞 := {}.
Class topological_space (α : Set) : Set.
Class discrete_topology (α : Set) `(t : topological_space α) : Set.
Class is_add_subgroup (β : Set) `(_inst_2 : add_group β) (s : Set) : Set.
Instance is_add_subgroup_to_is_add_submonoid (β : Set) `(_inst_2 : add_group β) (s : Set) `(c : @is_add_subgroup β _inst_2 s) : @is_add_submonoid β (@add_group_to_add_monoid β _inst_2) s := {}.
Class is_subgroup (α : Set) `(_inst_1 : group α) (s : Set) : Set.
Instance is_subgroup_to_is_submonoid (α : Set) `(_inst_1 : group α) (s : Set) `(c : @is_subgroup α _inst_1 s) : @is_submonoid α (@group_to_monoid α _inst_1) s := {}.
Class onote_NF (o : Set) : Set.
Class topological_space_separable_space (α : Set) `(t : topological_space α) : Set.
Class topological_space_first_countable_topology (α : Set) `(t : topological_space α) : Set.
Class topological_space_second_countable_topology (α : Set) `(t : topological_space α) : Set.
Instance topological_space_second_countable_topology_to_first_countable_topology (α : Set) `(t : topological_space α) `(_inst_1 : @topological_space_second_countable_topology α t) : @topological_space_first_countable_topology α t := {}.
Class normal_add_subgroup (α : Set) `(_inst_1 : add_group α) (s : Set) : Set.
Instance normal_add_subgroup_to_is_add_subgroup (α : Set) `(_inst_1 : add_group α) (s : Set) `(c : @normal_add_subgroup α _inst_1 s) : @is_add_subgroup α _inst_1 s := {}.
Class normal_subgroup (α : Set) `(_inst_1 : group α) (s : Set) : Set.
Instance topological_space_second_countable_topology_to_separable_space (α : Set) `(t : topological_space α) `(_inst_1 : @topological_space_second_countable_topology α t) : @topological_space_separable_space α t := {}.
Class compact_space (α : Set) `(_inst_2 : topological_space α) : Set.
Instance normal_subgroup_to_is_subgroup (α : Set) `(_inst_1 : group α) (s : Set) `(c : @normal_subgroup α _inst_1 s) : @is_subgroup α _inst_1 s := {}.
Instance fintype_compact_space (α : Set) `(_inst_1 : topological_space α) `(_inst_3 : fintype α) : @compact_space α _inst_1 := {}.
Class sequential_space (α : Set) `(_inst_3 : topological_space α) : Set.
Class locally_compact_space (α : Set) `(_inst_3 : topological_space α) : Set.
Class irreducible_space (α : Set) `(_inst_2 : topological_space α) : Set.
Class connected_space (α : Set) `(_inst_2 : topological_space α) : Set.
Instance irreducible_space_connected_space (α : Set) `(_inst_2 : topological_space α) `(_inst_3 : @irreducible_space α _inst_2) : @connected_space α _inst_2 := {}.
Class totally_disconnected_space (α : Set) `(_inst_2 : topological_space α) : Set.
Class totally_separated_space (α : Set) `(_inst_2 : topological_space α) : Set.
Instance totally_separated_space_totally_disconnected_space (α : Set) `(_inst_2 : topological_space α) `(_inst_3 : @totally_separated_space α _inst_2) : @totally_disconnected_space α _inst_2 := {}.
Instance topological_space_first_countable_topology_sequential_space (α : Set) `(_inst_1 : topological_space α) `(_inst_2 : @topological_space_first_countable_topology α _inst_1) : @sequential_space α _inst_1 := {}.
Class t0_space (α : Set) `(_inst_2 : topological_space α) : Set.
Class t1_space (α : Set) `(_inst_2 : topological_space α) : Set.
Instance t1_space_t0_space (α : Set) `(_inst_1 : topological_space α) `(_inst_2 : @t1_space α _inst_1) : @t0_space α _inst_1 := {}.
Class t2_space (α : Set) `(_inst_2 : topological_space α) : Set.
Instance t2_space_t1_space (α : Set) `(_inst_1 : topological_space α) `(_inst_2 : @t2_space α _inst_1) : @t1_space α _inst_1 := {}.
Instance t2_space_discrete (α : Set) `(_inst_2 : topological_space α) `(_inst_3 : @discrete_topology α _inst_2) : @t2_space α _inst_2 := {}.
Instance locally_compact_of_compact (α : Set) `(_inst_1 : topological_space α) `(_inst_3 : @t2_space α _inst_1) `(_inst_4 : @compact_space α _inst_1) : @locally_compact_space α _inst_1 := {}.
Class regular_space (α : Set) `(_inst_2 : topological_space α) : Set.
Instance regular_space_to_t1_space (α : Set) `(_inst_2 : topological_space α) `(c : @regular_space α _inst_2) : @t1_space α _inst_2 := {}.
Instance regular_space_t2_space (α : Set) `(_inst_1 : topological_space α) `(_inst_2 : @regular_space α _inst_1) : @t2_space α _inst_1 := {}.
Class normal_space (α : Set) `(_inst_2 : topological_space α) : Set.
Instance normal_space_to_t1_space (α : Set) `(_inst_2 : topological_space α) `(c : @normal_space α _inst_2) : @t1_space α _inst_2 := {}.
Instance normal_space_regular_space (α : Set) `(_inst_1 : topological_space α) `(_inst_2 : @normal_space α _inst_1) : @regular_space α _inst_1 := {}.
Class uniform_space (α : Set) : Set.
Instance uniform_space_to_topological_space (α : Set) `(c : uniform_space α) : topological_space α := {}.
Class separated (α : Set) `(_inst_4 : uniform_space α) : Set.
Instance separated_t2 (α : Set) `(_inst_1 : uniform_space α) `(s : @separated α _inst_1) : @t2_space α (@uniform_space_to_topological_space α _inst_1) := {}.
Instance separated_regular (α : Set) `(_inst_1 : uniform_space α) `(_inst_4 : @separated α _inst_1) : @regular_space α (@uniform_space_to_topological_space α _inst_1) := {}.
Class complete_space (α : Set) `(_inst_2 : uniform_space α) : Set.
Instance complete_of_compact (α : Set) `(_inst_2 : uniform_space α) `(_inst_3 : @compact_space α (@uniform_space_to_topological_space α _inst_2)) : @complete_space α _inst_2 := {}.
Class manifold (H : Set) `(_inst_1 : topological_space H) (M : Set) `(_inst_2 : topological_space M) : Set.
Instance manifold_model_space (H : Set) `(_inst_1 : topological_space H) : @manifold H _inst_1 H _inst_1 := {}.
Class has_groupoid (H : Set) `(_inst_4 : topological_space H) (M : Set) `(_inst_5 : topological_space M) `(_inst_6 : @manifold H _inst_4 M _inst_5) (G : Set) : Set.
Class has_edist (α : Set) : Set.
Instance has_groupoid_model_space (H : Set) `(_inst_4 : topological_space H) (G : Set) : @has_groupoid H _inst_4 H _inst_4 (@manifold_model_space H _inst_4) G := {}.
Class emetric_space (α : Set) : Set.
Instance emetric_space_to_has_edist (α : Set) `(c : emetric_space α) : has_edist α := {}.
Instance emetric_space_to_uniform_space' (α : Set) `(_inst_1 : emetric_space α) : uniform_space α := {}.
Instance to_separated (α : Set) `(_inst_1 : emetric_space α) : @separated α (@emetric_space_to_uniform_space' α _inst_1) := {}.
Instance emetric_topological_space_first_countable_topology (α : Set) `(_inst_2 : emetric_space α) : @topological_space_first_countable_topology α (@uniform_space_to_topological_space α (@emetric_space_to_uniform_space' α _inst_2)) := {}.
Class simple_group (α : Set) `(_inst_1 : group α) : Set.
Class simple_add_group (α : Set) `(_inst_1 : add_group α) : Set.
Class is_subring (R : Set) `(_inst_1 : ring R) (S : Set) : Set.
Instance is_subring_to_is_add_subgroup (R : Set) `(_inst_1 : ring R) (S : Set) `(c : @is_subring R _inst_1 S) : @is_add_subgroup R (@add_comm_group_to_add_group R (@ring_to_add_comm_group R _inst_1)) S := {}.
Instance is_subring_to_is_submonoid (R : Set) `(_inst_1 : ring R) (S : Set) `(c : @is_subring R _inst_1 S) : @is_submonoid R (@ring_to_monoid R _inst_1) S := {}.
Class is_subfield (F : Set) `(_inst_1 : discrete_field F) (S : Set) : Set.
Instance is_subfield_to_is_subring (F : Set) `(_inst_1 : discrete_field F) (S : Set) `(c : @is_subfield F _inst_1 S) : @is_subring F (@domain_to_ring F (@division_ring_to_domain F (@field_to_division_ring F (@discrete_field_to_field F _inst_1)))) S := {}.
Class has_scalar (α : Set) (γ : Set) : Set.
Class mul_action (α : Set) (β : Set) `(_inst_1 : monoid α) : Set.
Instance mul_action_to_has_scalar (α : Set) (β : Set) `(_inst_1 : monoid α) `(c : @mul_action α β _inst_1) : has_scalar α β := {}.
Class is_cyclic (α : Set) `(_inst_1 : group α) : Set.
Class distrib_mul_action (α : Set) (β : Set) `(_inst_1 : monoid α) `(_inst_2 : add_monoid β) : Set.
Instance distrib_mul_action_to_mul_action (α : Set) (β : Set) `(_inst_1 : monoid α) `(_inst_2 : add_monoid β) `(c : @distrib_mul_action α β _inst_1 _inst_2) : @mul_action α β _inst_1 := {}.
Class semimodule (α : Set) (β : Set) `(_inst_1 : semiring α) `(_inst_2 : add_comm_monoid β) : Set.
Instance semimodule_to_distrib_mul_action_old (α : Set) (β : Set) `(_inst_1 : semiring α) `(_inst_2 : add_comm_monoid β) `(c : @semimodule α β _inst_1 _inst_2) : @distrib_mul_action α β (@semiring_to_monoid α _inst_1) (@add_comm_monoid_to_add_monoid β _inst_2) := {}.
Instance semimodule_to_distrib_mul_action (α : Set) (β : Set) `(c : semimodule α β) : @distrib_mul_action α β (semiring_to_monoid α _) (add_comm_monoid_to_add_monoid β _) := {}.
Check semimodule_to_distrib_mul_action.
Check semimodule_to_distrib_mul_action_old.
Class module (α : Set) (β : Set) `(_inst_1 : ring α) `(_inst_2 : add_comm_group β) : Set.
Instance module_to_semimodule (α : Set) (β : Set) `(_inst_1 : ring α) `(_inst_2 : add_comm_group β) `(c : @module α β _inst_1 _inst_2) : @semimodule α β (@ring_to_semiring α _inst_1) (@add_comm_group_to_add_comm_monoid β _inst_2) := {}.
Instance semiring_to_semimodule (α : Set) `(r : semiring α) : @semimodule α α r (@semiring_to_add_comm_monoid α r) := {}.
Instance ring_to_module (α : Set) `(r : ring α) : @module α α r (@ring_to_add_comm_group α r) := {}.
Class is_linear_map (α : Set) (β : Set) (γ : Set) `(_inst_1 : ring α) `(_inst_2 : add_comm_group β) `(_inst_3 : add_comm_group γ) `(_inst_4 : @module α β _inst_1 _inst_2) `(_inst_5 : @module α γ _inst_1 _inst_3) (f : Set) : Set.
Instance discrete_field_to_vector_space (α : Set) `(_inst_1 : discrete_field α) : @module α α (@domain_to_ring α (@division_ring_to_domain α (@field_to_division_ring α (@discrete_field_to_field α _inst_1)))) (@ring_to_add_comm_group α (@domain_to_ring α (@division_ring_to_domain α (@field_to_division_ring α (@discrete_field_to_field α _inst_1))))) := {}.
Class char_p (α : Set) `(_inst_1 : semiring α) (p : Set) : Set.
Class perfect_field (α : Set) `(_inst_1 : field α) (p : Set) `(_inst_2 : @char_p α (@ring_to_semiring α (@domain_to_ring α (@division_ring_to_domain α (@field_to_division_ring α _inst_1)))) p) : Set.
Class topological_monoid (α : Set) `(_inst_1 : topological_space α) `(_inst_2 : monoid α) : Set.
Class topological_add_monoid (α : Set) `(_inst_1 : topological_space α) `(_inst_2 : add_monoid α) : Set.
Class topological_add_group (α : Set) `(_inst_1 : topological_space α) `(_inst_2 : add_group α) : Set.
Instance topological_add_group_to_topological_add_monoid (α : Set) `(_inst_1 : topological_space α) `(_inst_2 : add_group α) `(c : @topological_add_group α _inst_1 _inst_2) : @topological_add_monoid α _inst_1 (@add_group_to_add_monoid α _inst_2) := {}.
Class topological_group (α : Set) `(_inst_1 : topological_space α) `(_inst_2 : group α) : Set.
Instance topological_group_to_topological_monoid (α : Set) `(_inst_1 : topological_space α) `(_inst_2 : group α) `(c : @topological_group α _inst_1 _inst_2) : @topological_monoid α _inst_1 (@group_to_monoid α _inst_2) := {}.
Class add_group_with_zero_nhd (α : Set) : Set.
Instance add_group_with_zero_nhd_to_add_comm_group (α : Set) `(c : add_group_with_zero_nhd α) : add_comm_group α := {}.
Instance add_group_with_zero_nhd_topological_space (α : Set) `(_inst_1 : add_group_with_zero_nhd α) : topological_space α := {}.
Instance add_group_with_zero_nhd_topological_add_monoid (α : Set) `(_inst_1 : add_group_with_zero_nhd α) : @topological_add_monoid α (@add_group_with_zero_nhd_topological_space α _inst_1) (@add_group_to_add_monoid α (@add_comm_group_to_add_group α (@add_group_with_zero_nhd_to_add_comm_group α _inst_1))) := {}.
Instance add_group_with_zero_nhd_topological_add_group (α : Set) `(_inst_1 : add_group_with_zero_nhd α) : @topological_add_group α (@add_group_with_zero_nhd_topological_space α _inst_1) (@add_comm_group_to_add_group α (@add_group_with_zero_nhd_to_add_comm_group α _inst_1)) := {}.
Class ordered_topology (α : Set) `(t : topological_space α) `(_inst_1 : preorder α) : Set.
Class uniform_add_group (α : Set) `(_inst_1 : uniform_space α) `(_inst_2 : add_group α) : Set.
Instance ordered_topology_to_t2_space (α : Set) `(_inst_1 : topological_space α) `(_inst_2 : partial_order α) `(t : @ordered_topology α _inst_1 (@partial_order_to_preorder α _inst_2)) : @t2_space α _inst_1 := {}.
Instance uniform_add_group_to_topological_add_group (α : Set) `(_inst_1 : uniform_space α) `(_inst_2 : add_group α) `(_inst_3 : @uniform_add_group α _inst_1 _inst_2) : @topological_add_group α (@uniform_space_to_topological_space α _inst_1) _inst_2 := {}.
Class orderable_topology (α : Set) `(t : topological_space α) `(_inst_1 : partial_order α) : Set.
Class add_comm_group_is_Z_bilin (α : Set) (β : Set) (γ : Set) `(_inst_1 : add_comm_group α) `(_inst_2 : add_comm_group β) `(_inst_3 : add_comm_group γ) (f : Set) : Set.
Instance orderable_topology_to_ordered_topology (α : Set) `(_inst_1 : topological_space α) `(_inst_2 : linear_order α) `(t : @orderable_topology α _inst_1 (@linear_order_to_partial_order α _inst_2)) : @ordered_topology α _inst_1 (@partial_order_to_preorder α (@linear_order_to_partial_order α _inst_2)) := {}.
Instance orderable_topology_regular_space (α : Set) `(_inst_1 : topological_space α) `(_inst_2 : linear_order α) `(t : @orderable_topology α _inst_1 (@linear_order_to_partial_order α _inst_2)) : @regular_space α _inst_1 := {}.
Instance ordered_connected_space (α : Set) `(_inst_1 : lattice_conditionally_complete_linear_order α) `(_inst_2 : topological_space α) `(_inst_3 : @orderable_topology α _inst_2 (@lattice_semilattice_inf_to_partial_order α (@lattice_lattice_to_semilattice_inf α (@lattice_conditionally_complete_lattice_to_lattice α (@lattice_conditionally_complete_linear_order_to_conditionally_complete_lattice α _inst_1))))) `(_inst_8 : @densely_ordered α (@partial_order_to_preorder α (@lattice_semilattice_inf_to_partial_order α (@lattice_lattice_to_semilattice_inf α (@lattice_conditionally_complete_lattice_to_lattice α (@lattice_conditionally_complete_linear_order_to_conditionally_complete_lattice α _inst_1)))))) : @connected_space α _inst_2 := {}.
Class ideal_is_prime (α : Set) `(_inst_1 : comm_ring α) (I : Set) : Set.
Class ideal_is_maximal (α : Set) `(_inst_1 : comm_ring α) (I : Set) : Set.
Instance ideal_is_maximal_is_prime' (α : Set) `(_inst_1 : comm_ring α) (I : Set) `(H : @ideal_is_maximal α _inst_1 I) : @ideal_is_prime α _inst_1 I := {}.
Class has_dist (α : Set) : Set.
Class metric_space (α : Set) : Set.
Instance metric_space_to_has_dist (α : Set) `(c : metric_space α) : has_dist α := {}.
Instance metric_space_to_uniform_space' (α : Set) `(_inst_1 : metric_space α) : uniform_space α := {}.
Instance metric_space_to_has_edist (α : Set) `(_inst_1 : metric_space α) : has_edist α := {}.
Class local_ring (α : Set) : Set.
Instance local_ring_to_nonzero_comm_ring (α : Set) `(c : local_ring α) : nonzero_comm_ring α := {}.
Instance metric_space_to_separated (α : Set) `(_inst_1 : metric_space α) : @separated α (@metric_space_to_uniform_space' α _inst_1) := {}.
Instance metric_space_to_emetric_space (α : Set) `(_inst_1 : metric_space α) : emetric_space α := {}.
Class is_local_ring_hom (α : Set) (β : Set) `(_inst_1 : comm_ring α) `(_inst_2 : comm_ring β) (f : Set) : Set.
Instance is_local_ring_hom_to_is_ring_hom (α : Set) (β : Set) `(_inst_1 : comm_ring α) `(_inst_2 : comm_ring β) (f : Set) `(c : @is_local_ring_hom α β _inst_1 _inst_2 f) : @is_ring_hom α β (@comm_ring_to_ring α _inst_1) (@comm_ring_to_ring β _inst_2) f := {}.
Instance discrete_field_local_ring (α : Set) `(_inst_1 : discrete_field α) : local_ring α := {}.
Class topological_semiring (α : Set) `(_inst_1 : topological_space α) `(_inst_2 : semiring α) : Set.
Instance topological_semiring_to_topological_add_monoid (α : Set) `(_inst_1 : topological_space α) `(_inst_2 : semiring α) `(c : @topological_semiring α _inst_1 _inst_2) : @topological_add_monoid α _inst_1 (@add_comm_monoid_to_add_monoid α (@semiring_to_add_comm_monoid α _inst_2)) := {}.
Instance topological_semiring_to_topological_monoid (α : Set) `(_inst_1 : topological_space α) `(_inst_2 : semiring α) `(c : @topological_semiring α _inst_1 _inst_2) : @topological_monoid α _inst_1 (@semiring_to_monoid α _inst_2) := {}.
Class topological_ring (α : Set) `(_inst_1 : topological_space α) `(_inst_2 : ring α) : Set.
Instance topological_ring_to_topological_add_monoid (α : Set) `(_inst_1 : topological_space α) `(_inst_2 : ring α) `(c : @topological_ring α _inst_1 _inst_2) : @topological_add_monoid α _inst_1 (@add_group_to_add_monoid α (@add_comm_group_to_add_group α (@ring_to_add_comm_group α _inst_2))) := {}.
Instance topological_ring_to_topological_monoid (α : Set) `(_inst_1 : topological_space α) `(_inst_2 : ring α) `(c : @topological_ring α _inst_1 _inst_2) : @topological_monoid α _inst_1 (@ring_to_monoid α _inst_2) := {}.
Instance topological_ring_to_topological_semiring (α : Set) `(_inst_1 : topological_space α) `(_inst_2 : ring α) `(t : @topological_ring α _inst_1 _inst_2) : @topological_semiring α _inst_1 (@ring_to_semiring α _inst_2) := {}.
Instance topological_ring_to_topological_add_group (α : Set) `(_inst_1 : topological_space α) `(_inst_2 : ring α) `(t : @topological_ring α _inst_1 _inst_2) : @topological_add_group α _inst_1 (@add_comm_group_to_add_group α (@ring_to_add_comm_group α _inst_2)) := {}.
Class proper_space (α : Set) `(_inst_2 : metric_space α) : Set.
Instance proper_of_compact (α : Set) `(_inst_1 : metric_space α) `(_inst_2 : @compact_space α (@uniform_space_to_topological_space α (@metric_space_to_uniform_space' α _inst_1))) : @proper_space α _inst_1 := {}.
Instance locally_compact_of_proper (α : Set) `(_inst_1 : metric_space α) `(_inst_2 : @proper_space α _inst_1) : @locally_compact_space α (@uniform_space_to_topological_space α (@metric_space_to_uniform_space' α _inst_1)) := {}.
Instance complete_of_proper (α : Set) `(_inst_1 : metric_space α) `(_inst_2 : @proper_space α _inst_1) : @complete_space α (@metric_space_to_uniform_space' α _inst_1) := {}.
Instance second_countable_of_proper (α : Set) `(_inst_1 : metric_space α) `(_inst_2 : @proper_space α _inst_1) : @topological_space_second_countable_topology α (@uniform_space_to_topological_space α (@metric_space_to_uniform_space' α _inst_1)) := {}.
Class premetric_space (α : Set) : Set.
Instance premetric_space_to_has_dist (α : Set) `(c : premetric_space α) : has_dist α := {}.
Class algebra (R : Set) (A : Set) `(_inst_1 : comm_ring R) `(_inst_2 : ring A) : Set.
Instance algebra_to_has_scalar (R : Set) (A : Set) `(_inst_1 : comm_ring R) `(_inst_2 : ring A) `(c : @algebra R A _inst_1 _inst_2) : has_scalar R A := {}.
Instance algebra_to_module (R : Set) (A : Set) `(_inst_1 : comm_ring R) `(_inst_3 : ring A) `(_inst_4 : @algebra R A _inst_1 _inst_3) : @module R A (@comm_ring_to_ring R _inst_1) (@ring_to_add_comm_group A _inst_3) := {}.
Instance algebra_id (R : Set) `(_inst_1 : comm_ring R) : @algebra R R _inst_1 (@comm_ring_to_ring R _inst_1) := {}.
Class has_bracket (L : Set) : Set.
Class topological_semimodule (α : Set) (β : Set) `(_inst_1 : semiring α) `(_inst_2 : topological_space α) `(_inst_3 : topological_space β) `(_inst_4 : add_comm_monoid β) `(_inst_5 : @semimodule α β _inst_1 _inst_4) : Set.
Class topological_module (α : Set) (β : Set) `(_inst_1 : ring α) `(_inst_2 : topological_space α) `(_inst_3 : topological_space β) `(_inst_4 : add_comm_group β) `(_inst_5 : @module α β _inst_1 _inst_4) : Set.
Instance topological_module_to_topological_semimodule (α : Set) (β : Set) `(_inst_1 : ring α) `(_inst_2 : topological_space α) `(_inst_3 : topological_space β) `(_inst_4 : add_comm_group β) `(_inst_5 : @module α β _inst_1 _inst_4) `(c : @topological_module α β _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) : @topological_semimodule α β (@ring_to_semiring α _inst_1) _inst_2 _inst_3 (@add_comm_group_to_add_comm_monoid β _inst_4) (@module_to_semimodule α β _inst_1 _inst_4 _inst_5) := {}.
Class lie_ring (L : Set) `(_inst_1 : add_comm_group L) : Set.
Instance lie_ring_to_has_bracket (L : Set) `(_inst_1 : add_comm_group L) `(c : @lie_ring L _inst_1) : has_bracket L := {}.
Class lie_algebra (R : Set) (L : Set) `(_inst_1 : comm_ring R) `(_inst_2 : add_comm_group L) : Set.
Instance lie_algebra_to_module (R : Set) (L : Set) `(_inst_1 : comm_ring R) `(_inst_2 : add_comm_group L) `(c : @lie_algebra R L _inst_1 _inst_2) : @module R L (@comm_ring_to_ring R _inst_1) _inst_2 := {}.
Instance lie_algebra_to_lie_ring (R : Set) (L : Set) `(_inst_1 : comm_ring R) `(_inst_2 : add_comm_group L) `(c : @lie_algebra R L _inst_1 _inst_2) : @lie_ring L _inst_2 := {}.
Class has_norm (α : Set) : Set.
Class normed_group (α : Set) : Set.
Instance normed_group_to_has_norm (α : Set) `(c : normed_group α) : has_norm α := {}.
Instance normed_group_to_add_comm_group (α : Set) `(c : normed_group α) : add_comm_group α := {}.
Instance normed_group_to_metric_space (α : Set) `(c : normed_group α) : metric_space α := {}.
Class is_noetherian (α : Set) (β : Set) `(_inst_1 : ring α) `(_inst_2 : add_comm_group β) `(_inst_3 : @module α β _inst_1 _inst_2) : Set.
Instance normed_uniform_group (α : Set) `(_inst_1 : normed_group α) : @uniform_add_group α (@metric_space_to_uniform_space' α (@normed_group_to_metric_space α _inst_1)) (@add_comm_group_to_add_group α (@normed_group_to_add_comm_group α _inst_1)) := {}.
Instance normed_top_monoid (α : Set) `(_inst_1 : normed_group α) : @topological_add_monoid α (@uniform_space_to_topological_space α (@metric_space_to_uniform_space' α (@normed_group_to_metric_space α _inst_1))) (@add_group_to_add_monoid α (@add_comm_group_to_add_group α (@normed_group_to_add_comm_group α _inst_1))) := {}.
Instance normed_top_group (α : Set) `(_inst_1 : normed_group α) : @topological_add_group α (@uniform_space_to_topological_space α (@metric_space_to_uniform_space' α (@normed_group_to_metric_space α _inst_1))) (@add_comm_group_to_add_group α (@normed_group_to_add_comm_group α _inst_1)) := {}.
Class normed_ring (α : Set) : Set.
Instance normed_ring_to_has_norm (α : Set) `(c : normed_ring α) : has_norm α := {}.
Instance normed_ring_to_ring (α : Set) `(c : normed_ring α) : ring α := {}.
Instance normed_ring_to_metric_space (α : Set) `(c : normed_ring α) : metric_space α := {}.
Instance normed_ring_to_normed_group (α : Set) `(β : normed_ring α) : normed_group α := {}.
Instance normed_ring_top_monoid (α : Set) `(_inst_1 : normed_ring α) : @topological_monoid α (@uniform_space_to_topological_space α (@metric_space_to_uniform_space' α (@normed_ring_to_metric_space α _inst_1))) (@ring_to_monoid α (@normed_ring_to_ring α _inst_1)) := {}.
Class is_noetherian_ring (α : Set) `(_inst_1 : ring α) : Set.
Instance is_noetherian_ring_to_is_noetherian (α : Set) `(_inst_1 : ring α) `(_inst_2 : @is_noetherian_ring α _inst_1) : @is_noetherian α α _inst_1 (@ring_to_add_comm_group α _inst_1) (@ring_to_module α _inst_1) := {}.
Instance ring_is_noetherian_of_fintype (R : Set) (M : Set) `(_inst_1 : fintype M) `(_inst_2 : ring R) `(_inst_3 : add_comm_group M) `(_inst_4 : @module R M _inst_2 _inst_3) : @is_noetherian R M _inst_2 _inst_3 _inst_4 := {}.
Instance normed_top_ring (α : Set) `(_inst_1 : normed_ring α) : @topological_ring α (@uniform_space_to_topological_space α (@metric_space_to_uniform_space' α (@normed_ring_to_metric_space α _inst_1))) (@normed_ring_to_ring α _inst_1) := {}.
Class normed_field (α : Set) : Set.
Instance normed_field_to_has_norm (α : Set) `(c : normed_field α) : has_norm α := {}.
Instance normed_field_to_discrete_field (α : Set) `(c : normed_field α) : discrete_field α := {}.
Instance normed_field_to_metric_space (α : Set) `(c : normed_field α) : metric_space α := {}.
Class nondiscrete_normed_field (α : Set) : Set.
Instance nondiscrete_normed_field_to_normed_field (α : Set) `(c : nondiscrete_normed_field α) : normed_field α := {}.
Instance normed_field_to_normed_ring (α : Set) `(i : normed_field α) : normed_ring α := {}.
Class ideal_is_principal (α : Set) `(_inst_1 : comm_ring α) (S : Set) : Set.
Class principal_ideal_domain (α : Set) : Set.
Instance principal_ideal_domain_to_integral_domain (α : Set) `(c : principal_ideal_domain α) : integral_domain α := {}.
Instance principal_ideal_domain_principal (α : Set) `(c : principal_ideal_domain α) (S : Set) : @ideal_is_principal α (@nonzero_comm_ring_to_comm_ring α (@integral_domain_to_nonzero_comm_ring α (@principal_ideal_domain_to_integral_domain α c))) S := {}.
Class normed_space (α : Set) (β : Set) `(_inst_1 : normed_field α) `(_inst_2 : normed_group β) : Set.
Instance normed_space_to_module (α : Set) (β : Set) `(_inst_1 : normed_field α) `(_inst_2 : normed_group β) `(c : @normed_space α β _inst_1 _inst_2) : @module α β (@normed_ring_to_ring α (@normed_field_to_normed_ring α _inst_1)) (@normed_group_to_add_comm_group β _inst_2) := {}.
Instance normed_field_to_normed_space (α : Set) `(_inst_1 : normed_field α) : @normed_space α α _inst_1 (@normed_ring_to_normed_group α (@normed_field_to_normed_ring α _inst_1)) := {}.
Instance euclidean_domain_to_principal_ideal_domain (α : Set) `(_inst_1 : euclidean_domain α) : principal_ideal_domain α := {}.
Instance principal_ideal_domain_is_noetherian_ring (α : Set) `(_inst_1 : principal_ideal_domain α) : @is_noetherian_ring α (@domain_to_ring α (@integral_domain_to_domain α (@principal_ideal_domain_to_integral_domain α _inst_1))) := {}.
Instance normed_space_topological_vector_space (α : Set) `(_inst_1 : normed_field α) (E : Set) `(_inst_3 : normed_group E) `(_inst_4 : @normed_space α E _inst_1 _inst_3) : @topological_module α E (@domain_to_ring α (@division_ring_to_domain α (@field_to_division_ring α (@discrete_field_to_field α (@normed_field_to_discrete_field α _inst_1))))) (@uniform_space_to_topological_space α (@metric_space_to_uniform_space' α (@normed_field_to_metric_space α _inst_1))) (@uniform_space_to_topological_space E (@metric_space_to_uniform_space' E (@normed_group_to_metric_space E _inst_3))) (@normed_group_to_add_comm_group E _inst_3) (@normed_space_to_module α E _inst_1 _inst_3 _inst_4) := {}.
Class normed_algebra (𝕜 : Set) (𝕜' : Set) `(_inst_1 : normed_field 𝕜) `(_inst_2 : normed_ring 𝕜') : Set.
Instance normed_algebra_to_algebra (𝕜 : Set) (𝕜' : Set) `(_inst_1 : normed_field 𝕜) `(_inst_2 : normed_ring 𝕜') `(c : @normed_algebra 𝕜 𝕜' _inst_1 _inst_2) : @algebra 𝕜 𝕜' (@nonzero_comm_ring_to_comm_ring 𝕜 (@euclidean_domain_to_nonzero_comm_ring 𝕜 (@discrete_field_to_euclidean_domain 𝕜 (@normed_field_to_discrete_field 𝕜 _inst_1)))) (@normed_ring_to_ring 𝕜' _inst_2) := {}.
Instance borel (α : Set) `(_inst_1 : topological_space α) : measurable_space α := {}.
Class measure_theory_measure_is_complete (α : Set) (_x : Set) (μ : Set) : Set.
Class measure_theory_measure_space (α : Set) : Set.
Instance measure_theory_measure_space_to_measurable_space (α : Set) `(c : measure_theory_measure_space α) : measurable_space α := {}.
Class model_with_corners_boundaryless (𝕜 : Set) `(_inst_1 : nondiscrete_normed_field 𝕜) (E : Set) `(_inst_2 : normed_group E) `(_inst_3 : @normed_space 𝕜 E (@nondiscrete_normed_field_to_normed_field 𝕜 _inst_1) _inst_2) (H : Set) `(_inst_4 : topological_space H) (I : Set) : Set.
Class smooth_manifold_with_corners (𝕜 : Set) `(_inst_1 : nondiscrete_normed_field 𝕜) (E : Set) `(_inst_2 : normed_group E) `(_inst_3 : @normed_space 𝕜 E (@nondiscrete_normed_field_to_normed_field 𝕜 _inst_1) _inst_2) (H : Set) `(_inst_4 : topological_space H) (I : Set) (M : Set) `(_inst_5 : topological_space M) `(_inst_6 : @manifold H _inst_4 M _inst_5) : Set.
Instance model_space_smooth (𝕜 : Set) `(_inst_1 : nondiscrete_normed_field 𝕜) (E : Set) `(_inst_2 : normed_group E) `(_inst_3 : @normed_space 𝕜 E (@nondiscrete_normed_field_to_normed_field 𝕜 _inst_1) _inst_2) (H : Set) `(_inst_4 : topological_space H) (I : Set) : @smooth_manifold_with_corners 𝕜 _inst_1 E _inst_2 _inst_3 H _inst_4 I H _inst_4 (@manifold_model_space H _inst_4) := {}.
Class lt_class (α : Set) `(_inst_1 : has_lt α) (x : Set) (y : Set) : Set.
Instance tangent_space_topological_module (𝕜 : Set) `(_inst_1 : nondiscrete_normed_field 𝕜) (E : Set) `(_inst_2 : normed_group E) `(_inst_3 : @normed_space 𝕜 E (@nondiscrete_normed_field_to_normed_field 𝕜 _inst_1) _inst_2) (H : Set) `(_inst_4 : topological_space H) (I : Set) (M : Set) `(_inst_5 : topological_space M) `(_inst_6 : @manifold H _inst_4 M _inst_5) `(_inst_7 : @smooth_manifold_with_corners 𝕜 _inst_1 E _inst_2 _inst_3 H _inst_4 I M _inst_5 _inst_6) (x : Set) : @topological_module 𝕜 E (@normed_ring_to_ring 𝕜 (@normed_field_to_normed_ring 𝕜 (@nondiscrete_normed_field_to_normed_field 𝕜 _inst_1))) (@uniform_space_to_topological_space 𝕜 (@metric_space_to_uniform_space' 𝕜 (@normed_field_to_metric_space 𝕜 (@nondiscrete_normed_field_to_normed_field 𝕜 _inst_1)))) (@uniform_space_to_topological_space E (@metric_space_to_uniform_space' E (@normed_group_to_metric_space E _inst_2))) (@normed_group_to_add_comm_group E _inst_2) (@normed_space_to_module 𝕜 E (@nondiscrete_normed_field_to_normed_field 𝕜 _inst_1) _inst_2 _inst_3) := {}.
Instance tangent_space_topological_space (𝕜 : Set) `(_inst_1 : nondiscrete_normed_field 𝕜) (E : Set) `(_inst_2 : normed_group E) `(_inst_3 : @normed_space 𝕜 E (@nondiscrete_normed_field_to_normed_field 𝕜 _inst_1) _inst_2) (H : Set) `(_inst_4 : topological_space H) (I : Set) (M : Set) `(_inst_5 : topological_space M) `(_inst_6 : @manifold H _inst_4 M _inst_5) `(_inst_7 : @smooth_manifold_with_corners 𝕜 _inst_1 E _inst_2 _inst_3 H _inst_4 I M _inst_5 _inst_6) (x : Set) : topological_space E := {}.
Instance tangent_space_add_comm_group (𝕜 : Set) `(_inst_1 : nondiscrete_normed_field 𝕜) (E : Set) `(_inst_2 : normed_group E) `(_inst_3 : @normed_space 𝕜 E (@nondiscrete_normed_field_to_normed_field 𝕜 _inst_1) _inst_2) (H : Set) `(_inst_4 : topological_space H) (I : Set) (M : Set) `(_inst_5 : topological_space M) `(_inst_6 : @manifold H _inst_4 M _inst_5) `(_inst_7 : @smooth_manifold_with_corners 𝕜 _inst_1 E _inst_2 _inst_3 H _inst_4 I M _inst_5 _inst_6) (x : Set) : add_comm_group E := {}.
Instance tangent_space_topological_add_group (𝕜 : Set) `(_inst_1 : nondiscrete_normed_field 𝕜) (E : Set) `(_inst_2 : normed_group E) `(_inst_3 : @normed_space 𝕜 E (@nondiscrete_normed_field_to_normed_field 𝕜 _inst_1) _inst_2) (H : Set) `(_inst_4 : topological_space H) (I : Set) (M : Set) `(_inst_5 : topological_space M) `(_inst_6 : @manifold H _inst_4 M _inst_5) `(_inst_7 : @smooth_manifold_with_corners 𝕜 _inst_1 E _inst_2 _inst_3 H _inst_4 I M _inst_5 _inst_6) (x : Set) : @topological_add_group E (@tangent_space_topological_space 𝕜 _inst_1 E _inst_2 _inst_3 H _inst_4 I M _inst_5 _inst_6 _inst_7 x) (@add_comm_group_to_add_group E (@tangent_space_add_comm_group 𝕜 _inst_1 E _inst_2 _inst_3 H _inst_4 I M _inst_5 _inst_6 _inst_7 x)) := {}.
Instance tangent_space_vector_space (𝕜 : Set) `(_inst_1 : nondiscrete_normed_field 𝕜) (E : Set) `(_inst_2 : normed_group E) `(_inst_3 : @normed_space 𝕜 E (@nondiscrete_normed_field_to_normed_field 𝕜 _inst_1) _inst_2) (H : Set) `(_inst_4 : topological_space H) (I : Set) (M : Set) `(_inst_5 : topological_space M) `(_inst_6 : @manifold H _inst_4 M _inst_5) `(_inst_7 : @smooth_manifold_with_corners 𝕜 _inst_1 E _inst_2 _inst_3 H _inst_4 I M _inst_5 _inst_6) (x : Set) : @module 𝕜 E (@domain_to_ring 𝕜 (@division_ring_to_domain 𝕜 (@field_to_division_ring 𝕜 (@discrete_field_to_field 𝕜 (@normed_field_to_discrete_field 𝕜 (@nondiscrete_normed_field_to_normed_field 𝕜 _inst_1)))))) (@tangent_space_add_comm_group 𝕜 _inst_1 E _inst_2 _inst_3 H _inst_4 I M _inst_5 _inst_6 _inst_7 x) := {}.
Class has_inner (α : Set) : Set.
Class inner_product_space (α : Set) : Set.
Instance inner_product_space_to_add_comm_group (α : Set) `(c : inner_product_space α) : add_comm_group α := {}.
Instance inner_product_space_to_has_inner (α : Set) `(c : inner_product_space α) : has_inner α := {}.
Instance inner_product_space_has_norm (α : Set) `(_inst_1 : inner_product_space α) : has_norm α := {}.
Instance inner_product_space_is_normed_group (α : Set) `(_inst_1 : inner_product_space α) : normed_group α := {}.
