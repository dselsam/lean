namespace test
class decidable (p : Type)
class has_zero (α : Type)
class has_one (α : Type)
class has_add (α : Type)
class has_mul (α : Type)
class has_inv (α : Type)
class has_neg (α : Type)
class has_sub (α : Type)
class has_div (α : Type)
class has_dvd (α : Type)
class has_mod (α : Type)
class has_le (α : Type)
class has_lt (α : Type)
class has_append (α : Type)
class has_andthen (α : Type) (β : Type) (σ : Type)
class has_union (α : Type)
class has_inter (α : Type)
class has_sdiff (α : Type)
class has_equiv (α : Type)
class has_subset (α : Type)
class has_ssubset (α : Type)
class has_emptyc (α : Type)
class has_insert (α : Type) (γ : Type)
class has_sep (α : Type) (γ : Type)
class has_mem (α : Type) (γ : Type)
class has_pow (α : Type) (β : Type)
class has_sizeof (α : Type)
class inhabited (α : Type)
class nonempty (α : Type)
@[instance] axiom nonempty_of_inhabited (α : Type) [_inst_1 : inhabited α] : nonempty α
class subsingleton (α : Type)
@[instance] axiom subsingleton_prop (p : Type) : subsingleton p
class setoid (α : Type)
@[instance] axiom setoid_has_equiv (α : Type) [_inst_1 : setoid α] : has_equiv α
class has_well_founded (α : Type)
@[instance] axiom has_well_founded_of_has_sizeof (α : Type) [_inst_1 : has_sizeof α] : has_well_founded α
class has_lift (a : Type) (b : Type)
class has_lift_t (a : Type) (b : Type)
class has_coe (a : Type) (b : Type)
class has_coe_t (a : Type) (b : Type)
class has_coe_to_fun (a : Type)
class has_coe_to_sort (a : Type)
@[instance] axiom lift_trans (a : Type) (b : Type) (c : Type) [_inst_1 : has_lift a b] [_inst_2 : has_lift_t b c] : has_lift_t a c
@[instance] axiom lift_base (a : Type) (b : Type) [_inst_1 : has_lift a b] : has_lift_t a b
@[instance] axiom coe_trans (a : Type) (b : Type) (c : Type) [_inst_1 : has_coe a b] [_inst_2 : has_coe_t b c] : has_coe_t a c
@[instance] axiom coe_base (a : Type) (b : Type) [_inst_1 : has_coe a b] : has_coe_t a b
class has_coe_t_aux (a : Type) (b : Type)
@[instance] axiom coe_trans_aux (a : Type) (b : Type) (c : Type) [_inst_1 : has_coe a b] [_inst_2 : has_coe_t_aux b c] : has_coe_t_aux a c
@[instance] axiom coe_base_aux (a : Type) (b : Type) [_inst_1 : has_coe a b] : has_coe_t_aux a b
@[instance] axiom coe_fn_trans (a : Type) (b : Type) [_inst_1 : has_coe_t_aux a b] [_inst_2 : has_coe_to_fun b] : has_coe_to_fun a
@[instance] axiom coe_sort_trans (a : Type) (b : Type) [_inst_1 : has_coe_t_aux a b] [_inst_2 : has_coe_to_sort b] : has_coe_to_sort a
@[instance] axiom coe_to_lift (a : Type) (b : Type) [_inst_1 : has_coe_t a b] : has_lift_t a b
class has_repr (α : Type)
class has_to_string (α : Type)
class is_symm_op (α : Type) (β : Type) (op : Type)
class is_commutative (α : Type) (op : Type)
@[instance] axiom is_symm_op_of_is_commutative (α : Type) (op : Type) [_inst_1 : is_commutative α op] : is_symm_op α α op
class is_associative (α : Type) (op : Type)
class is_left_id (α : Type) (op : Type) (o : Type)
class is_right_id (α : Type) (op : Type) (o : Type)
class is_left_null (α : Type) (op : Type) (o : Type)
class is_right_null (α : Type) (op : Type) (o : Type)
class is_left_cancel (α : Type) (op : Type)
class is_right_cancel (α : Type) (op : Type)
class is_idempotent (α : Type) (op : Type)
class is_left_distrib (α : Type) (op₁ : Type) (op₂ : Type)
class is_right_distrib (α : Type) (op₁ : Type) (op₂ : Type)
class is_left_inv (α : Type) (op : Type) (inv : Type) (o : Type)
class is_right_inv (α : Type) (op : Type) (inv : Type) (o : Type)
class is_cond_left_inv (α : Type) (op : Type) (inv : Type) (o : Type) (p : Type)
class is_cond_right_inv (α : Type) (op : Type) (inv : Type) (o : Type) (p : Type)
class is_distinct (α : Type) (a : Type) (b : Type)
class is_irrefl (α : Type) (r : Type)
class is_refl (α : Type) (r : Type)
class is_symm (α : Type) (r : Type)
class is_asymm (α : Type) (r : Type)
class is_antisymm (α : Type) (r : Type)
class is_trans (α : Type) (r : Type)
class is_total (α : Type) (r : Type)
class is_preorder (α : Type) (r : Type)
@[instance] axiom is_preorder.to_is_refl (α : Type) (r : Type) [c : is_preorder α r] : is_refl α r
@[instance] axiom is_preorder.to_is_trans (α : Type) (r : Type) [c : is_preorder α r] : is_trans α r
class is_total_preorder (α : Type) (r : Type)
@[instance] axiom is_total_preorder.to_is_trans (α : Type) (r : Type) [c : is_total_preorder α r] : is_trans α r
@[instance] axiom is_total_preorder.to_is_total (α : Type) (r : Type) [c : is_total_preorder α r] : is_total α r
@[instance] axiom is_total_preorder_is_preorder (α : Type) (r : Type) [s : is_total_preorder α r] : is_preorder α r
class is_partial_order (α : Type) (r : Type)
@[instance] axiom is_partial_order.to_is_preorder (α : Type) (r : Type) [c : is_partial_order α r] : is_preorder α r
@[instance] axiom is_partial_order.to_is_antisymm (α : Type) (r : Type) [c : is_partial_order α r] : is_antisymm α r
class is_linear_order (α : Type) (r : Type)
@[instance] axiom is_linear_order.to_is_partial_order (α : Type) (r : Type) [c : is_linear_order α r] : is_partial_order α r
@[instance] axiom is_linear_order.to_is_total (α : Type) (r : Type) [c : is_linear_order α r] : is_total α r
class has_to_format (α : Type)
class is_equiv (α : Type) (r : Type)
@[instance] axiom is_equiv.to_is_preorder (α : Type) (r : Type) [c : is_equiv α r] : is_preorder α r
@[instance] axiom is_equiv.to_is_symm (α : Type) (r : Type) [c : is_equiv α r] : is_symm α r
class is_per (α : Type) (r : Type)
@[instance] axiom is_per.to_is_symm (α : Type) (r : Type) [c : is_per α r] : is_symm α r
@[instance] axiom is_per.to_is_trans (α : Type) (r : Type) [c : is_per α r] : is_trans α r
class is_strict_order (α : Type) (r : Type)
@[instance] axiom is_strict_order.to_is_irrefl (α : Type) (r : Type) [c : is_strict_order α r] : is_irrefl α r
@[instance] axiom is_strict_order.to_is_trans (α : Type) (r : Type) [c : is_strict_order α r] : is_trans α r
class is_incomp_trans (α : Type) (lt : Type)
class is_strict_weak_order (α : Type) (lt : Type)
@[instance] axiom is_strict_weak_order.to_is_strict_order (α : Type) (lt : Type) [c : is_strict_weak_order α lt] : is_strict_order α lt
@[instance] axiom is_strict_weak_order.to_is_incomp_trans (α : Type) (lt : Type) [c : is_strict_weak_order α lt] : is_incomp_trans α lt
class is_trichotomous (α : Type) (lt : Type)
class is_strict_total_order (α : Type) (lt : Type)
@[instance] axiom is_strict_total_order.to_is_trichotomous (α : Type) (lt : Type) [c : is_strict_total_order α lt] : is_trichotomous α lt
@[instance] axiom is_strict_total_order.to_is_strict_weak_order (α : Type) (lt : Type) [c : is_strict_total_order α lt] : is_strict_weak_order α lt
@[instance] axiom is_asymm_of_is_trans_of_is_irrefl (α : Type) (r : Type) [_inst_1 : is_trans α r] [_inst_2 : is_irrefl α r] : is_asymm α r
class functor (f : Type)
class has_pure (f : Type)
class has_seq (f : Type)
class has_seq_left (f : Type)
class has_seq_right (f : Type)
class preorder (α : Type)
@[instance] axiom preorder.to_has_le (α : Type) [s : preorder α] : has_le α
@[instance] axiom preorder.to_has_lt (α : Type) [s : preorder α] : has_lt α
class applicative (f : Type)
@[instance] axiom applicative.to_functor (f : Type) [c : applicative f] : functor f
@[instance] axiom applicative.to_has_pure (f : Type) [c : applicative f] : has_pure f
@[instance] axiom applicative.to_has_seq (f : Type) [c : applicative f] : has_seq f
@[instance] axiom applicative.to_has_seq_left (f : Type) [c : applicative f] : has_seq_left f
@[instance] axiom applicative.to_has_seq_right (f : Type) [c : applicative f] : has_seq_right f
class has_bind (m : Type)
class partial_order (α : Type)
@[instance] axiom partial_order.to_preorder (α : Type) [s : partial_order α] : preorder α
class monad (m : Type)
@[instance] axiom monad.to_applicative (m : Type) [c : monad m] : applicative m
@[instance] axiom monad.to_has_bind (m : Type) [c : monad m] : has_bind m
class linear_order (α : Type)
@[instance] axiom linear_order.to_partial_order (α : Type) [s : linear_order α] : partial_order α
class has_orelse (f : Type)
class alternative (f : Type)
@[instance] axiom alternative.to_applicative (f : Type) [c : alternative f] : applicative f
@[instance] axiom alternative.to_has_orelse (f : Type) [c : alternative f] : has_orelse f
class has_monad_lift (m : Type) (n : Type)
class has_monad_lift_t (m : Type) (n : Type)
@[instance] axiom has_monad_lift_t_trans (m : Type) (n : Type) (o : Type) [_inst_1 : has_monad_lift n o] [_inst_2 : has_monad_lift_t m n] : has_monad_lift_t m o
@[instance] axiom has_monad_lift_t_refl (m : Type) : has_monad_lift_t m m
class monad_functor (m : Type) (m' : Type) (n : Type) (n' : Type)
class monad_functor_t (m : Type) (m' : Type) (n : Type) (n' : Type)
@[instance] axiom monad_functor_t_trans (m : Type) (m' : Type) (n : Type) (n' : Type) (o : Type) (o' : Type) [_inst_1 : monad_functor n n' o o'] [_inst_2 : monad_functor_t m m' n n'] : monad_functor_t m m' o o'
@[instance] axiom monad_functor_t_refl (m : Type) (m' : Type) : monad_functor_t m m' m m'
class monad_run (out : Type) (m : Type)
class decidable_linear_order (α : Type)
@[instance] axiom decidable_linear_order.to_linear_order (α : Type) [s : decidable_linear_order α] : linear_order α
class monad_fail (m : Type)
@[instance] axiom monad_fail_lift (m : Type) (n : Type) [_inst_1 : has_monad_lift m n] [_inst_2 : monad_fail m] [_inst_3 : monad n] : monad_fail n
class monad_except (ε : Type) (m : Type)
class monad_except_adapter (ε : Type) (ε' : Type) (m : Type) (m' : Type)
@[instance] axiom monad_except_adapter_trans (ε : Type) (ε' : Type) (m : Type) (m' : Type) (n : Type) (n' : Type) [_inst_1 : monad_functor m m' n n'] [_inst_2 : monad_except_adapter ε ε' m m'] : monad_except_adapter ε ε' n n'
class monad_reader (ρ : Type) (m : Type)
@[instance] axiom monad_reader_trans (ρ : Type) (m : Type) (n : Type) [_inst_1 : has_monad_lift m n] [_inst_2 : monad_reader ρ m] : monad_reader ρ n
class monad_reader_adapter (ρ : Type) (ρ' : Type) (m : Type) (m' : Type)
@[instance] axiom monad_reader_adapter_trans (ρ : Type) (ρ' : Type) (m : Type) (m' : Type) (n : Type) (n' : Type) [_inst_1 : monad_functor m m' n n'] [_inst_2 : monad_reader_adapter ρ ρ' m m'] : monad_reader_adapter ρ ρ' n n'
class monad_state (σ : Type) (m : Type)
@[instance] axiom monad_state_trans (σ : Type) (m : Type) (n : Type) [_inst_1 : has_monad_lift m n] [_inst_2 : monad_state σ m] : monad_state σ n
class monad_state_adapter (σ : Type) (σ' : Type) (m : Type) (m' : Type)
@[instance] axiom monad_state_adapter_trans (σ : Type) (σ' : Type) (m : Type) (m' : Type) (n : Type) (n' : Type) [_inst_1 : monad_functor m m' n n'] [_inst_2 : monad_state_adapter σ σ' m m'] : monad_state_adapter σ σ' n n'
class has_to_pexpr (α : Type)
class has_to_tactic_format (α : Type)
@[instance] axiom has_to_format_to_has_to_tactic_format (α : Type) [_inst_1 : has_to_format α] : has_to_tactic_format α
class is_lawful_functor (f : Type) [_inst_1 : functor f]
class is_lawful_applicative (f : Type) [_inst_1 : applicative f]
@[instance] axiom is_lawful_applicative.to_is_lawful_functor (f : Type) [_inst_1 : applicative f] [c : @is_lawful_applicative f _inst_1] : @is_lawful_functor f (@applicative.to_functor f _inst_1)
class is_lawful_monad (m : Type) [_inst_1 : monad m]
@[instance] axiom is_lawful_monad.to_is_lawful_applicative (m : Type) [_inst_1 : monad m] [c : @is_lawful_monad m _inst_1] : @is_lawful_applicative m (@monad.to_applicative m _inst_1)
class semigroup (α : Type)
@[instance] axiom semigroup.to_has_mul (α : Type) [s : semigroup α] : has_mul α
class comm_semigroup (α : Type)
@[instance] axiom comm_semigroup.to_semigroup (α : Type) [s : comm_semigroup α] : semigroup α
class left_cancel_semigroup (α : Type)
@[instance] axiom left_cancel_semigroup.to_semigroup (α : Type) [s : left_cancel_semigroup α] : semigroup α
class right_cancel_semigroup (α : Type)
@[instance] axiom right_cancel_semigroup.to_semigroup (α : Type) [s : right_cancel_semigroup α] : semigroup α
class monoid (α : Type)
@[instance] axiom monoid.to_semigroup (α : Type) [s : monoid α] : semigroup α
@[instance] axiom monoid.to_has_one (α : Type) [s : monoid α] : has_one α
class comm_monoid (α : Type)
@[instance] axiom comm_monoid.to_monoid (α : Type) [s : comm_monoid α] : monoid α
@[instance] axiom comm_monoid.to_comm_semigroup (α : Type) [s : comm_monoid α] : comm_semigroup α
class group (α : Type)
@[instance] axiom group.to_monoid (α : Type) [s : group α] : monoid α
@[instance] axiom group.to_has_inv (α : Type) [s : group α] : has_inv α
class comm_group (α : Type)
@[instance] axiom comm_group.to_group (α : Type) [s : comm_group α] : group α
@[instance] axiom comm_group.to_comm_monoid (α : Type) [s : comm_group α] : comm_monoid α
@[instance] axiom group.to_left_cancel_semigroup (α : Type) [s : group α] : left_cancel_semigroup α
@[instance] axiom group.to_right_cancel_semigroup (α : Type) [s : group α] : right_cancel_semigroup α
class add_semigroup (α : Type)
@[instance] axiom add_semigroup.to_has_add (α : Type) [s : add_semigroup α] : has_add α
class add_comm_semigroup (α : Type)
@[instance] axiom add_comm_semigroup.to_add_semigroup (α : Type) [s : add_comm_semigroup α] : add_semigroup α
class add_left_cancel_semigroup (α : Type)
@[instance] axiom add_left_cancel_semigroup.to_add_semigroup (α : Type) [s : add_left_cancel_semigroup α] : add_semigroup α
class add_right_cancel_semigroup (α : Type)
@[instance] axiom add_right_cancel_semigroup.to_add_semigroup (α : Type) [s : add_right_cancel_semigroup α] : add_semigroup α
class add_monoid (α : Type)
@[instance] axiom add_monoid.to_add_semigroup (α : Type) [s : add_monoid α] : add_semigroup α
@[instance] axiom add_monoid.to_has_zero (α : Type) [s : add_monoid α] : has_zero α
class add_comm_monoid (α : Type)
@[instance] axiom add_comm_monoid.to_add_monoid (α : Type) [s : add_comm_monoid α] : add_monoid α
@[instance] axiom add_comm_monoid.to_add_comm_semigroup (α : Type) [s : add_comm_monoid α] : add_comm_semigroup α
class add_group (α : Type)
@[instance] axiom add_group.to_add_monoid (α : Type) [s : add_group α] : add_monoid α
@[instance] axiom add_group.to_has_neg (α : Type) [s : add_group α] : has_neg α
class add_comm_group (α : Type)
@[instance] axiom add_comm_group.to_add_group (α : Type) [s : add_comm_group α] : add_group α
@[instance] axiom add_comm_group.to_add_comm_monoid (α : Type) [s : add_comm_group α] : add_comm_monoid α
@[instance] axiom add_group.to_left_cancel_add_semigroup (α : Type) [s : add_group α] : add_left_cancel_semigroup α
@[instance] axiom add_group.to_right_cancel_add_semigroup (α : Type) [s : add_group α] : add_right_cancel_semigroup α
@[instance] axiom add_group_has_sub (α : Type) [_inst_1 : add_group α] : has_sub α
class distrib (α : Type)
@[instance] axiom distrib.to_has_mul (α : Type) [s : distrib α] : has_mul α
@[instance] axiom distrib.to_has_add (α : Type) [s : distrib α] : has_add α
class mul_zero_class (α : Type)
@[instance] axiom mul_zero_class.to_has_mul (α : Type) [s : mul_zero_class α] : has_mul α
@[instance] axiom mul_zero_class.to_has_zero (α : Type) [s : mul_zero_class α] : has_zero α
class ordered_cancel_comm_monoid (α : Type)
@[instance] axiom ordered_cancel_comm_monoid.to_add_comm_monoid (α : Type) [s : ordered_cancel_comm_monoid α] : add_comm_monoid α
@[instance] axiom ordered_cancel_comm_monoid.to_add_left_cancel_semigroup (α : Type) [s : ordered_cancel_comm_monoid α] : add_left_cancel_semigroup α
@[instance] axiom ordered_cancel_comm_monoid.to_add_right_cancel_semigroup (α : Type) [s : ordered_cancel_comm_monoid α] : add_right_cancel_semigroup α
@[instance] axiom ordered_cancel_comm_monoid.to_partial_order (α : Type) [s : ordered_cancel_comm_monoid α] : partial_order α
class zero_ne_one_class (α : Type)
@[instance] axiom zero_ne_one_class.to_has_zero (α : Type) [s : zero_ne_one_class α] : has_zero α
@[instance] axiom zero_ne_one_class.to_has_one (α : Type) [s : zero_ne_one_class α] : has_one α
class semiring (α : Type)
@[instance] axiom semiring.to_add_comm_monoid (α : Type) [s : semiring α] : add_comm_monoid α
@[instance] axiom semiring.to_monoid (α : Type) [s : semiring α] : monoid α
@[instance] axiom semiring.to_distrib (α : Type) [s : semiring α] : distrib α
@[instance] axiom semiring.to_mul_zero_class (α : Type) [s : semiring α] : mul_zero_class α
class comm_semiring (α : Type)
@[instance] axiom comm_semiring.to_semiring (α : Type) [s : comm_semiring α] : semiring α
@[instance] axiom comm_semiring.to_comm_monoid (α : Type) [s : comm_semiring α] : comm_monoid α
@[instance] axiom comm_semiring_has_dvd (α : Type) [_inst_1 : comm_semiring α] : has_dvd α
class ordered_comm_group (α : Type)
@[instance] axiom ordered_comm_group.to_add_comm_group (α : Type) [s : ordered_comm_group α] : add_comm_group α
@[instance] axiom ordered_comm_group.to_partial_order (α : Type) [s : ordered_comm_group α] : partial_order α
@[instance] axiom ordered_comm_group.to_ordered_cancel_comm_monoid (α : Type) [s : ordered_comm_group α] : ordered_cancel_comm_monoid α
class ring (α : Type)
@[instance] axiom ring.to_add_comm_group (α : Type) [s : ring α] : add_comm_group α
@[instance] axiom ring.to_monoid (α : Type) [s : ring α] : monoid α
@[instance] axiom ring.to_distrib (α : Type) [s : ring α] : distrib α
@[instance] axiom ring.to_semiring (α : Type) [s : ring α] : semiring α
class comm_ring (α : Type)
@[instance] axiom comm_ring.to_ring (α : Type) [s : comm_ring α] : ring α
@[instance] axiom comm_ring.to_comm_semigroup (α : Type) [s : comm_ring α] : comm_semigroup α
@[instance] axiom comm_ring.to_comm_semiring (α : Type) [s : comm_ring α] : comm_semiring α
class no_zero_divisors (α : Type)
@[instance] axiom no_zero_divisors.to_has_mul (α : Type) [s : no_zero_divisors α] : has_mul α
@[instance] axiom no_zero_divisors.to_has_zero (α : Type) [s : no_zero_divisors α] : has_zero α
class integral_domain (α : Type)
@[instance] axiom integral_domain.to_comm_ring (α : Type) [s : integral_domain α] : comm_ring α
@[instance] axiom integral_domain.to_no_zero_divisors (α : Type) [s : integral_domain α] : no_zero_divisors α
@[instance] axiom integral_domain.to_zero_ne_one_class (α : Type) [s : integral_domain α] : zero_ne_one_class α
class division_ring (α : Type)
@[instance] axiom division_ring.to_ring (α : Type) [s : division_ring α] : ring α
@[instance] axiom division_ring.to_has_inv (α : Type) [s : division_ring α] : has_inv α
@[instance] axiom division_ring.to_zero_ne_one_class (α : Type) [s : division_ring α] : zero_ne_one_class α
@[instance] axiom division_ring_has_div (α : Type) [_inst_1 : division_ring α] [_inst_2 : division_ring α] : has_div α
class decidable_linear_ordered_comm_group (α : Type)
@[instance] axiom decidable_linear_ordered_comm_group.to_add_comm_group (α : Type) [s : decidable_linear_ordered_comm_group α] : add_comm_group α
@[instance] axiom decidable_linear_ordered_comm_group.to_decidable_linear_order (α : Type) [s : decidable_linear_ordered_comm_group α] : decidable_linear_order α
@[instance] axiom decidable_linear_ordered_comm_group.to_ordered_comm_group (α : Type) [s : decidable_linear_ordered_comm_group α] : ordered_comm_group α
class decidable_linear_ordered_cancel_comm_monoid (α : Type)
@[instance] axiom decidable_linear_ordered_cancel_comm_monoid.to_ordered_cancel_comm_monoid (α : Type) [s : decidable_linear_ordered_cancel_comm_monoid α] : ordered_cancel_comm_monoid α
@[instance] axiom decidable_linear_ordered_cancel_comm_monoid.to_decidable_linear_order (α : Type) [s : decidable_linear_ordered_cancel_comm_monoid α] : decidable_linear_order α
class field (α : Type)
@[instance] axiom field.to_division_ring (α : Type) [s : field α] : division_ring α
@[instance] axiom field.to_comm_ring (α : Type) [s : field α] : comm_ring α
class discrete_field (α : Type)
@[instance] axiom discrete_field.to_field (α : Type) [s : discrete_field α] : field α
@[instance] axiom discrete_field.to_integral_domain (α : Type) [_inst_1 : discrete_field α] [s : discrete_field α] : integral_domain α
class ordered_semiring (α : Type)
@[instance] axiom ordered_semiring.to_semiring (α : Type) [s : ordered_semiring α] : semiring α
@[instance] axiom ordered_semiring.to_ordered_cancel_comm_monoid (α : Type) [s : ordered_semiring α] : ordered_cancel_comm_monoid α
class linear_ordered_semiring (α : Type)
@[instance] axiom linear_ordered_semiring.to_ordered_semiring (α : Type) [s : linear_ordered_semiring α] : ordered_semiring α
@[instance] axiom linear_ordered_semiring.to_linear_order (α : Type) [s : linear_ordered_semiring α] : linear_order α
class decidable_linear_ordered_semiring (α : Type)
@[instance] axiom decidable_linear_ordered_semiring.to_linear_ordered_semiring (α : Type) [s : decidable_linear_ordered_semiring α] : linear_ordered_semiring α
@[instance] axiom decidable_linear_ordered_semiring.to_decidable_linear_order (α : Type) [s : decidable_linear_ordered_semiring α] : decidable_linear_order α
class ordered_ring (α : Type)
@[instance] axiom ordered_ring.to_ring (α : Type) [s : ordered_ring α] : ring α
@[instance] axiom ordered_ring.to_ordered_comm_group (α : Type) [s : ordered_ring α] : ordered_comm_group α
@[instance] axiom ordered_ring.to_zero_ne_one_class (α : Type) [s : ordered_ring α] : zero_ne_one_class α
@[instance] axiom ordered_ring.to_ordered_semiring (α : Type) [s : ordered_ring α] : ordered_semiring α
class linear_ordered_ring (α : Type)
@[instance] axiom linear_ordered_ring.to_ordered_ring (α : Type) [s : linear_ordered_ring α] : ordered_ring α
@[instance] axiom linear_ordered_ring.to_linear_order (α : Type) [s : linear_ordered_ring α] : linear_order α
@[instance] axiom linear_ordered_ring.to_linear_ordered_semiring (α : Type) [s : linear_ordered_ring α] : linear_ordered_semiring α
class linear_ordered_comm_ring (α : Type)
@[instance] axiom linear_ordered_comm_ring.to_linear_ordered_ring (α : Type) [s : linear_ordered_comm_ring α] : linear_ordered_ring α
@[instance] axiom linear_ordered_comm_ring.to_comm_monoid (α : Type) [s : linear_ordered_comm_ring α] : comm_monoid α
@[instance] axiom linear_ordered_comm_ring.to_integral_domain (α : Type) [s : linear_ordered_comm_ring α] : integral_domain α
class decidable_linear_ordered_comm_ring (α : Type)
@[instance] axiom decidable_linear_ordered_comm_ring.to_linear_ordered_comm_ring (α : Type) [s : decidable_linear_ordered_comm_ring α] : linear_ordered_comm_ring α
@[instance] axiom decidable_linear_ordered_comm_ring.to_decidable_linear_ordered_comm_group (α : Type) [s : decidable_linear_ordered_comm_ring α] : decidable_linear_ordered_comm_group α
@[instance] axiom decidable_linear_ordered_comm_ring.to_decidable_linear_ordered_semiring (α : Type) [d : decidable_linear_ordered_comm_ring α] : decidable_linear_ordered_semiring α
class linear_ordered_field (α : Type)
@[instance] axiom linear_ordered_field.to_linear_ordered_ring (α : Type) [s : linear_ordered_field α] : linear_ordered_ring α
@[instance] axiom linear_ordered_field.to_field (α : Type) [s : linear_ordered_field α] : field α
class discrete_linear_ordered_field (α : Type)
@[instance] axiom discrete_linear_ordered_field.to_linear_ordered_field (α : Type) [s : discrete_linear_ordered_field α] : linear_ordered_field α
@[instance] axiom discrete_linear_ordered_field.to_decidable_linear_ordered_comm_ring (α : Type) [s : discrete_linear_ordered_field α] : decidable_linear_ordered_comm_ring α
@[instance] axiom discrete_linear_ordered_field.to_discrete_field (α : Type) [s : discrete_linear_ordered_field α] : discrete_field α
class unique (α : Type)
class relator.right_total (α : Type) (β : Type) (R : Type)
class relator.left_total (α : Type) (β : Type) (R : Type)
@[instance] axiom unique.inhabited (α : Type) [_inst_1 : unique α] : inhabited α
class relator.bi_total (α : Type) (β : Type) (R : Type)
@[instance] axiom unique.subsingleton (α : Type) [_inst_1 : unique α] : subsingleton α
class relator.left_unique (α : Type) (β : Type) (R : Type)
class relator.right_unique (α : Type) (β : Type) (R : Type)
class is_comm_applicative (m : Type) [_inst_1 : applicative m]
@[instance] axiom is_comm_applicative.to_is_lawful_applicative (m : Type) [_inst_1 : applicative m] [c : @is_comm_applicative m _inst_1] : @is_lawful_applicative m _inst_1
class can_lift (α : Type) (β : Type)
class traversable (t : Type)
@[instance] axiom traversable.to_functor (t : Type) [c : traversable t] : functor t
class is_lawful_traversable (t : Type) [_inst_1 : traversable t]
@[instance] axiom is_lawful_traversable.to_is_lawful_functor (t : Type) [_inst_1 : traversable t] [c : @is_lawful_traversable t _inst_1] : @is_lawful_functor t (@traversable.to_functor t _inst_1)
class eckmann_hilton.is_unital (X : Type) (m : Type) (e : Type)
class category_theory.has_hom (obj : Type)
class category_theory.category_struct (obj : Type)
@[instance] axiom category_theory.category_struct.to_has_hom (obj : Type) [c : category_theory.category_struct obj] : category_theory.has_hom obj
class category_theory.category (obj : Type)
@[instance] axiom category_theory.category.to_category_struct (obj : Type) [c : category_theory.category obj] : category_theory.category_struct obj
class bifunctor (F : Type)
class is_lawful_bifunctor (F : Type) [_inst_1 : bifunctor F]
class category_theory.epi (C : Type) [𝒞 : category_theory.category C] (X : Type) (Y : Type) (f : Type)
class category_theory.mono (C : Type) [𝒞 : category_theory.category C] (X : Type) (Y : Type) (f : Type)
@[instance] axiom preorder.small_category (α : Type) [_inst_1 : preorder α] : category_theory.category α
class computation.terminates (α : Type) (s : Type)
class monad_writer (ω : Type) (m : Type)
class bitraversable (t : Type)
@[instance] axiom bitraversable.to_bifunctor (t : Type) [c : bitraversable t] : bifunctor t
class is_lawful_bitraversable (t : Type) [_inst_1 : bitraversable t]
@[instance] axiom is_lawful_bitraversable.to_is_lawful_bifunctor (t : Type) [_inst_1 : bitraversable t] [c : @is_lawful_bitraversable t _inst_1] : @is_lawful_bifunctor t (@bitraversable.to_bifunctor t _inst_1)
class monad_writer_adapter (ω : Type) (ω' : Type) (m : Type) (m' : Type)
@[instance] axiom monad_writer_adapter_trans (ω : Type) (ω' : Type) (m : Type) (m' : Type) (n : Type) (n' : Type) [_inst_1 : monad_functor m m' n n'] [_inst_2 : monad_writer_adapter ω ω' m m'] : monad_writer_adapter ω ω' n n'
class monad_cont (m : Type)
class is_lawful_monad_cont (m : Type) [_inst_1 : monad m] [_inst_2 : monad_cont m]
@[instance] axiom is_lawful_monad_cont.to_is_lawful_monad (m : Type) [_inst_1 : monad m] [_inst_2 : monad_cont m] [c : @is_lawful_monad_cont m _inst_1 _inst_2] : @is_lawful_monad m _inst_1
class category_theory.is_iso (C : Type) [𝒞 : category_theory.category C] (X : Type) (Y : Type) (f : Type)
@[instance] axiom category_theory.is_iso.epi_of_iso (C : Type) [𝒞 : category_theory.category C] (X : Type) (Y : Type) (f : Type) [_inst_1 : @category_theory.is_iso C 𝒞 X Y f] : @category_theory.epi C 𝒞 X Y f
@[instance] axiom category_theory.is_iso.mono_of_iso (C : Type) [𝒞 : category_theory.category C] (X : Type) (Y : Type) (f : Type) [_inst_1 : @category_theory.is_iso C 𝒞 X Y f] : @category_theory.mono C 𝒞 X Y f
class category_theory.groupoid (obj : Type)
@[instance] axiom category_theory.groupoid.to_category (obj : Type) [c : category_theory.groupoid obj] : category_theory.category obj
class category_theory.full (C : Type) [𝒞 : category_theory.category C] (D : Type) [𝒟 : category_theory.category D] (F : Type)
class category_theory.monad (C : Type) [𝒞 : category_theory.category C] (T : Type)
class category_theory.faithful (C : Type) [𝒞 : category_theory.category C] (D : Type) [𝒟 : category_theory.category D] (F : Type)
@[instance] axiom category_theory.of_groupoid (C : Type) [_inst_1 : category_theory.groupoid C] (X : Type) (Y : Type) (f : Type) : @category_theory.is_iso C (@category_theory.groupoid.to_category C _inst_1) X Y f
class is_add_hom (α : Type) (β : Type) [_inst_1 : has_add α] [_inst_2 : has_add β] (f : Type)
class is_mul_hom (α : Type) (β : Type) [_inst_1 : has_mul α] [_inst_2 : has_mul β] (f : Type)
class is_group_anti_hom (α : Type) (β : Type) [_inst_1 : group α] [_inst_2 : group β] (f : Type)
class pSet.definable (n : Type) (a : Type)
class is_add_monoid_hom (α : Type) (β : Type) [_inst_1 : add_monoid α] [_inst_2 : add_monoid β] (f : Type)
@[instance] axiom is_add_monoid_hom.to_is_add_hom (α : Type) (β : Type) [_inst_1 : add_monoid α] [_inst_2 : add_monoid β] (f : Type) [c : @is_add_monoid_hom α β _inst_1 _inst_2 f] : @is_add_hom α β (@add_semigroup.to_has_add α (@add_monoid.to_add_semigroup α _inst_1)) (@add_semigroup.to_has_add β (@add_monoid.to_add_semigroup β _inst_2)) f
class is_monoid_hom (α : Type) (β : Type) [_inst_1 : monoid α] [_inst_2 : monoid β] (f : Type)
@[instance] axiom is_monoid_hom.to_is_mul_hom (α : Type) (β : Type) [_inst_1 : monoid α] [_inst_2 : monoid β] (f : Type) [c : @is_monoid_hom α β _inst_1 _inst_2 f] : @is_mul_hom α β (@semigroup.to_has_mul α (@monoid.to_semigroup α _inst_1)) (@semigroup.to_has_mul β (@monoid.to_semigroup β _inst_2)) f
class no_top_order (α : Type) [_inst_1 : preorder α]
class no_bot_order (α : Type) [_inst_1 : preorder α]
class densely_ordered (α : Type) [_inst_1 : preorder α]
class is_strict_total_order' (α : Type) (lt : Type)
@[instance] axiom is_strict_total_order'.to_is_trichotomous (α : Type) (lt : Type) [c : is_strict_total_order' α lt] : is_trichotomous α lt
@[instance] axiom is_strict_total_order'.to_is_strict_order (α : Type) (lt : Type) [c : is_strict_total_order' α lt] : is_strict_order α lt
class is_order_connected (α : Type) (lt : Type)
@[instance] axiom is_order_connected_of_is_strict_total_order' (α : Type) (r : Type) [_inst_1 : is_strict_total_order' α r] : is_order_connected α r
@[instance] axiom is_strict_total_order_of_is_strict_total_order' (α : Type) (r : Type) [_inst_1 : is_strict_total_order' α r] : is_strict_total_order α r
class is_extensional (α : Type) (r : Type)
@[instance] axiom is_extensional_of_is_strict_total_order' (α : Type) (r : Type) [_inst_1 : is_strict_total_order' α r] : is_extensional α r
class is_well_order (α : Type) (r : Type)
@[instance] axiom is_well_order.to_is_strict_total_order' (α : Type) (r : Type) [c : is_well_order α r] : is_strict_total_order' α r
@[instance] axiom is_well_order.is_strict_total_order (α : Type) (r : Type) [_inst_1 : is_well_order α r] : is_strict_total_order α r
@[instance] axiom is_well_order.is_extensional (α : Type) (r : Type) [_inst_1 : is_well_order α r] : is_extensional α r
@[instance] axiom is_well_order.is_trichotomous (α : Type) (r : Type) [_inst_1 : is_well_order α r] : is_trichotomous α r
class is_add_group_hom (α : Type) (β : Type) [_inst_1 : add_group α] [_inst_2 : add_group β] (f : Type)
@[instance] axiom is_add_group_hom.to_is_add_hom (α : Type) (β : Type) [_inst_1 : add_group α] [_inst_2 : add_group β] (f : Type) [c : @is_add_group_hom α β _inst_1 _inst_2 f] : @is_add_hom α β (@add_semigroup.to_has_add α (@add_monoid.to_add_semigroup α (@add_group.to_add_monoid α _inst_1))) (@add_semigroup.to_has_add β (@add_monoid.to_add_semigroup β (@add_group.to_add_monoid β _inst_2))) f
@[instance] axiom is_well_order.is_trans (α : Type) (r : Type) [_inst_1 : is_well_order α r] : is_trans α r
@[instance] axiom is_well_order.is_irrefl (α : Type) (r : Type) [_inst_1 : is_well_order α r] : is_irrefl α r
class is_group_hom (α : Type) (β : Type) [_inst_1 : group α] [_inst_2 : group β] (f : Type)
@[instance] axiom is_well_order.is_asymm (α : Type) (r : Type) [_inst_1 : is_well_order α r] : is_asymm α r
@[instance] axiom is_group_hom.to_is_mul_hom (α : Type) (β : Type) [_inst_1 : group α] [_inst_2 : group β] (f : Type) [c : @is_group_hom α β _inst_1 _inst_2 f] : @is_mul_hom α β (@semigroup.to_has_mul α (@monoid.to_semigroup α (@group.to_monoid α _inst_1))) (@semigroup.to_has_mul β (@monoid.to_semigroup β (@group.to_monoid β _inst_2))) f
@[instance] axiom is_group_hom.to_is_monoid_hom (α : Type) (β : Type) [_inst_1 : group α] [_inst_2 : group β] (f : Type) [_inst_3 : @is_group_hom α β _inst_1 _inst_2 f] : @is_monoid_hom α β (@group.to_monoid α _inst_1) (@group.to_monoid β _inst_2) f
@[instance] axiom is_add_group_hom.to_is_add_monoid_hom (α : Type) (β : Type) [_inst_1 : add_group α] [_inst_2 : add_group β] (f : Type) [_inst_3 : @is_add_group_hom α β _inst_1 _inst_2 f] : @is_add_monoid_hom α β (@add_group.to_add_monoid α _inst_1) (@add_group.to_add_monoid β _inst_2) f
class directed_order (α : Type)
@[instance] axiom directed_order.to_preorder (α : Type) [c : directed_order α] : preorder α
class lattice.has_sup (α : Type)
class lattice.has_inf (α : Type)
class lattice.semilattice_sup (α : Type)
@[instance] axiom lattice.semilattice_sup.to_has_sup (α : Type) [s : lattice.semilattice_sup α] : lattice.has_sup α
@[instance] axiom lattice.semilattice_sup.to_partial_order (α : Type) [s : lattice.semilattice_sup α] : partial_order α
class lattice.semilattice_inf (α : Type)
@[instance] axiom lattice.semilattice_inf.to_has_inf (α : Type) [s : lattice.semilattice_inf α] : lattice.has_inf α
@[instance] axiom lattice.semilattice_inf.to_partial_order (α : Type) [s : lattice.semilattice_inf α] : partial_order α
class lattice.lattice (α : Type)
@[instance] axiom lattice.lattice.to_semilattice_sup (α : Type) [s : lattice.lattice α] : lattice.semilattice_sup α
@[instance] axiom lattice.lattice.to_semilattice_inf (α : Type) [s : lattice.lattice α] : lattice.semilattice_inf α
class lattice.distrib_lattice (α : Type)
@[instance] axiom lattice.distrib_lattice.to_lattice (α : Type) [s : lattice.distrib_lattice α] : lattice.lattice α
@[instance] axiom lattice.lattice_of_decidable_linear_order (α : Type) [o : decidable_linear_order α] : lattice.lattice α
@[instance] axiom lattice.distrib_lattice_of_decidable_linear_order (α : Type) [o : decidable_linear_order α] : lattice.distrib_lattice α
class lattice.has_top (α : Type)
class lattice.has_bot (α : Type)
class lattice.order_top (α : Type)
@[instance] axiom lattice.order_top.to_has_top (α : Type) [s : lattice.order_top α] : lattice.has_top α
@[instance] axiom lattice.order_top.to_partial_order (α : Type) [s : lattice.order_top α] : partial_order α
class lattice.order_bot (α : Type)
@[instance] axiom lattice.order_bot.to_has_bot (α : Type) [s : lattice.order_bot α] : lattice.has_bot α
@[instance] axiom lattice.order_bot.to_partial_order (α : Type) [s : lattice.order_bot α] : partial_order α
class lattice.semilattice_sup_top (α : Type)
@[instance] axiom lattice.semilattice_sup_top.to_order_top (α : Type) [s : lattice.semilattice_sup_top α] : lattice.order_top α
@[instance] axiom lattice.semilattice_sup_top.to_semilattice_sup (α : Type) [s : lattice.semilattice_sup_top α] : lattice.semilattice_sup α
class lattice.semilattice_sup_bot (α : Type)
@[instance] axiom lattice.semilattice_sup_bot.to_order_bot (α : Type) [s : lattice.semilattice_sup_bot α] : lattice.order_bot α
@[instance] axiom lattice.semilattice_sup_bot.to_semilattice_sup (α : Type) [s : lattice.semilattice_sup_bot α] : lattice.semilattice_sup α
class lattice.semilattice_inf_top (α : Type)
@[instance] axiom lattice.semilattice_inf_top.to_order_top (α : Type) [s : lattice.semilattice_inf_top α] : lattice.order_top α
@[instance] axiom lattice.semilattice_inf_top.to_semilattice_inf (α : Type) [s : lattice.semilattice_inf_top α] : lattice.semilattice_inf α
class lattice.semilattice_inf_bot (α : Type)
@[instance] axiom lattice.semilattice_inf_bot.to_order_bot (α : Type) [s : lattice.semilattice_inf_bot α] : lattice.order_bot α
@[instance] axiom lattice.semilattice_inf_bot.to_semilattice_inf (α : Type) [s : lattice.semilattice_inf_bot α] : lattice.semilattice_inf α
class lattice.bounded_lattice (α : Type)
@[instance] axiom lattice.bounded_lattice.to_lattice (α : Type) [s : lattice.bounded_lattice α] : lattice.lattice α
@[instance] axiom lattice.bounded_lattice.to_order_top (α : Type) [s : lattice.bounded_lattice α] : lattice.order_top α
@[instance] axiom lattice.bounded_lattice.to_order_bot (α : Type) [s : lattice.bounded_lattice α] : lattice.order_bot α
@[instance] axiom lattice.semilattice_inf_top_of_bounded_lattice (α : Type) [bl : lattice.bounded_lattice α] : lattice.semilattice_inf_top α
@[instance] axiom lattice.semilattice_inf_bot_of_bounded_lattice (α : Type) [bl : lattice.bounded_lattice α] : lattice.semilattice_inf_bot α
@[instance] axiom lattice.semilattice_sup_top_of_bounded_lattice (α : Type) [bl : lattice.bounded_lattice α] : lattice.semilattice_sup_top α
@[instance] axiom lattice.semilattice_sup_bot_of_bounded_lattice (α : Type) [bl : lattice.bounded_lattice α] : lattice.semilattice_sup_bot α
class lattice.bounded_distrib_lattice (α : Type)
@[instance] axiom lattice.bounded_distrib_lattice.to_distrib_lattice (α : Type) [s : lattice.bounded_distrib_lattice α] : lattice.distrib_lattice α
@[instance] axiom lattice.bounded_distrib_lattice.to_bounded_lattice (α : Type) [s : lattice.bounded_distrib_lattice α] : lattice.bounded_lattice α
class category_theory.concrete_category (C : Type)
@[instance] axiom category_theory.concrete_category.to_category (C : Type) [c : category_theory.concrete_category C] : category_theory.category C
class category_theory.has_forget₂ (C : Type) (D : Type) [_inst_1 : category_theory.concrete_category C] [_inst_2 : category_theory.concrete_category D]
class category_theory.bundled_hom (c : Type) (hom : Type)
class category_theory.unbundled_hom (c : Type) (hom : Type)
class lattice.has_Sup (α : Type)
class lattice.has_Inf (α : Type)
class lattice.boolean_algebra (α : Type)
@[instance] axiom lattice.boolean_algebra.to_bounded_distrib_lattice (α : Type) [s : lattice.boolean_algebra α] : lattice.bounded_distrib_lattice α
@[instance] axiom lattice.boolean_algebra.to_has_neg (α : Type) [s : lattice.boolean_algebra α] : has_neg α
@[instance] axiom lattice.boolean_algebra.to_has_sub (α : Type) [s : lattice.boolean_algebra α] : has_sub α
class lattice.complete_lattice (α : Type)
@[instance] axiom lattice.complete_lattice.to_bounded_lattice (α : Type) [s : lattice.complete_lattice α] : lattice.bounded_lattice α
@[instance] axiom lattice.complete_lattice.to_has_Sup (α : Type) [s : lattice.complete_lattice α] : lattice.has_Sup α
@[instance] axiom lattice.complete_lattice.to_has_Inf (α : Type) [s : lattice.complete_lattice α] : lattice.has_Inf α
class category_theory.is_equivalence (C : Type) [𝒞 : category_theory.category C] (D : Type) [𝒟 : category_theory.category D] (F : Type)
class ordered_comm_monoid (α : Type)
@[instance] axiom ordered_comm_monoid.to_add_comm_monoid (α : Type) [s : ordered_comm_monoid α] : add_comm_monoid α
@[instance] axiom ordered_comm_monoid.to_partial_order (α : Type) [s : ordered_comm_monoid α] : partial_order α
class canonically_ordered_monoid (α : Type)
@[instance] axiom canonically_ordered_monoid.to_ordered_comm_monoid (α : Type) [s : canonically_ordered_monoid α] : ordered_comm_monoid α
@[instance] axiom canonically_ordered_monoid.to_order_bot (α : Type) [s : canonically_ordered_monoid α] : lattice.order_bot α
class lattice.complete_linear_order (α : Type)
@[instance] axiom lattice.complete_linear_order.to_complete_lattice (α : Type) [s : lattice.complete_linear_order α] : lattice.complete_lattice α
@[instance] axiom lattice.complete_linear_order.to_decidable_linear_order (α : Type) [s : lattice.complete_linear_order α] : decidable_linear_order α
class category_theory.ess_surj (C : Type) [𝒞 : category_theory.category C] (D : Type) [𝒟 : category_theory.category D] (F : Type)
class is_semiring_hom (α : Type) (β : Type) [_inst_1 : semiring α] [_inst_2 : semiring β] (f : Type)
@[instance] axiom category_theory.equivalence.faithful_of_equivalence (C : Type) [𝒞 : category_theory.category C] (D : Type) [𝒟 : category_theory.category D] (F : Type) [_inst_1 : @category_theory.is_equivalence C 𝒞 D 𝒟 F] : @category_theory.faithful C 𝒞 D 𝒟 F
@[instance] axiom is_semiring_hom.is_add_monoid_hom (α : Type) (β : Type) [_inst_1 : semiring α] [_inst_2 : semiring β] (f : Type) [_inst_3 : @is_semiring_hom α β _inst_1 _inst_2 f] : @is_add_monoid_hom α β (@add_comm_monoid.to_add_monoid α (@semiring.to_add_comm_monoid α _inst_1)) (@add_comm_monoid.to_add_monoid β (@semiring.to_add_comm_monoid β _inst_2)) f
@[instance] axiom is_semiring_hom.is_monoid_hom (α : Type) (β : Type) [_inst_1 : semiring α] [_inst_2 : semiring β] (f : Type) [_inst_3 : @is_semiring_hom α β _inst_1 _inst_2 f] : @is_monoid_hom α β (@semiring.to_monoid α _inst_1) (@semiring.to_monoid β _inst_2) f
class is_ring_hom (α : Type) (β : Type) [_inst_1 : ring α] [_inst_2 : ring β] (f : Type)
@[instance] axiom category_theory.equivalence.full_of_equivalence (C : Type) [𝒞 : category_theory.category C] (D : Type) [𝒟 : category_theory.category D] (F : Type) [_inst_1 : @category_theory.is_equivalence C 𝒞 D 𝒟 F] : @category_theory.full C 𝒞 D 𝒟 F
@[instance] axiom is_ring_hom.is_semiring_hom (α : Type) (β : Type) [_inst_1 : ring α] [_inst_2 : ring β] (f : Type) [_inst_3 : @is_ring_hom α β _inst_1 _inst_2 f] : @is_semiring_hom α β (@ring.to_semiring α _inst_1) (@ring.to_semiring β _inst_2) f
@[instance] axiom is_ring_hom.is_add_group_hom (α : Type) (β : Type) [_inst_1 : ring α] [_inst_2 : ring β] (f : Type) [_inst_3 : @is_ring_hom α β _inst_1 _inst_2 f] : @is_add_group_hom α β (@add_comm_group.to_add_group α (@ring.to_add_comm_group α _inst_1)) (@add_comm_group.to_add_group β (@ring.to_add_comm_group β _inst_2)) f
class nonzero_comm_semiring (α : Type)
@[instance] axiom nonzero_comm_semiring.to_comm_semiring (α : Type) [s : nonzero_comm_semiring α] : comm_semiring α
@[instance] axiom nonzero_comm_semiring.to_zero_ne_one_class (α : Type) [s : nonzero_comm_semiring α] : zero_ne_one_class α
class nonzero_comm_ring (α : Type)
@[instance] axiom nonzero_comm_ring.to_comm_ring (α : Type) [s : nonzero_comm_ring α] : comm_ring α
@[instance] axiom nonzero_comm_ring.to_zero_ne_one_class (α : Type) [s : nonzero_comm_ring α] : zero_ne_one_class α
@[instance] axiom nonzero_comm_ring.to_nonzero_comm_semiring (α : Type) [I : nonzero_comm_ring α] : nonzero_comm_semiring α
@[instance] axiom integral_domain.to_nonzero_comm_ring (α : Type) [id : integral_domain α] : nonzero_comm_ring α
class category_theory.is_left_adjoint (C : Type) [𝒞 : category_theory.category C] (D : Type) [𝒟 : category_theory.category D] (left : Type)
class domain (α : Type)
@[instance] axiom domain.to_ring (α : Type) [s : domain α] : ring α
@[instance] axiom domain.to_no_zero_divisors (α : Type) [s : domain α] : no_zero_divisors α
@[instance] axiom domain.to_zero_ne_one_class (α : Type) [s : domain α] : zero_ne_one_class α
class category_theory.is_right_adjoint (C : Type) [𝒞 : category_theory.category C] (D : Type) [𝒟 : category_theory.category D] (right : Type)
@[instance] axiom integral_domain.to_domain (α : Type) [s : integral_domain α] : domain α
@[instance] axiom ordered_cancel_comm_monoid.to_ordered_comm_monoid (α : Type) [H : ordered_cancel_comm_monoid α] : ordered_comm_monoid α
@[instance] axiom division_ring_has_div' (α : Type) [_inst_1 : division_ring α] : has_div α
@[instance] axiom division_ring.to_domain (α : Type) [s : division_ring α] : domain α
class lattice.complete_distrib_lattice (α : Type)
@[instance] axiom lattice.complete_distrib_lattice.to_complete_lattice (α : Type) [s : lattice.complete_distrib_lattice α] : lattice.complete_lattice α
@[instance] axiom field.to_integral_domain (α : Type) [F : field α] : integral_domain α
@[instance] axiom lattice.lattice.bounded_distrib_lattice (α : Type) [d : lattice.complete_distrib_lattice α] : lattice.bounded_distrib_lattice α
class lattice.complete_boolean_algebra (α : Type)
@[instance] axiom lattice.complete_boolean_algebra.to_boolean_algebra (α : Type) [s : lattice.complete_boolean_algebra α] : lattice.boolean_algebra α
@[instance] axiom lattice.complete_boolean_algebra.to_complete_distrib_lattice (α : Type) [s : lattice.complete_boolean_algebra α] : lattice.complete_distrib_lattice α
@[instance] axiom decidable_linear_ordered_comm_group.decidable_linear_ordered_cancel_comm_monoid (α : Type) [s : decidable_linear_ordered_comm_group α] : decidable_linear_ordered_cancel_comm_monoid α
class nonneg_comm_group (α : Type)
@[instance] axiom nonneg_comm_group.to_add_comm_group (α : Type) [s : nonneg_comm_group α] : add_comm_group α
@[instance] axiom nonneg_comm_group.to_ordered_comm_group (α : Type) [s : nonneg_comm_group α] : ordered_comm_group α
class char_zero (α : Type) [_inst_1 : add_monoid α] [_inst_2 : has_one α]
@[instance] axiom linear_ordered_semiring.to_char_zero (α : Type) [_inst_1 : linear_ordered_semiring α] : @char_zero α (@add_comm_monoid.to_add_monoid α (@ordered_comm_monoid.to_add_comm_monoid α (@ordered_cancel_comm_monoid.to_ordered_comm_monoid α (@ordered_semiring.to_ordered_cancel_comm_monoid α (@linear_ordered_semiring.to_ordered_semiring α _inst_1))))) (@monoid.to_has_one α (@semiring.to_monoid α (@ordered_semiring.to_semiring α (@linear_ordered_semiring.to_ordered_semiring α _inst_1))))
class category_theory.monoidal_category (C : Type) [𝒞 : category_theory.category C]
@[instance] axiom linear_ordered_semiring.to_no_top_order (α : Type) [_inst_1 : linear_ordered_semiring α] : @no_top_order α (@partial_order.to_preorder α (@ordered_comm_monoid.to_partial_order α (@ordered_cancel_comm_monoid.to_ordered_comm_monoid α (@ordered_semiring.to_ordered_cancel_comm_monoid α (@linear_ordered_semiring.to_ordered_semiring α _inst_1)))))
@[instance] axiom linear_ordered_semiring.to_no_bot_order (α : Type) [_inst_1 : linear_ordered_ring α] : @no_bot_order α (@partial_order.to_preorder α (@ordered_comm_monoid.to_partial_order α (@ordered_cancel_comm_monoid.to_ordered_comm_monoid α (@ordered_semiring.to_ordered_cancel_comm_monoid α (@ordered_ring.to_ordered_semiring α (@linear_ordered_ring.to_ordered_ring α _inst_1))))))
@[instance] axiom to_domain (α : Type) [s : linear_ordered_ring α] : domain α
class nonneg_ring (α : Type)
@[instance] axiom nonneg_ring.to_ring (α : Type) [s : nonneg_ring α] : ring α
@[instance] axiom nonneg_ring.to_zero_ne_one_class (α : Type) [s : nonneg_ring α] : zero_ne_one_class α
@[instance] axiom nonneg_ring.to_nonneg_comm_group (α : Type) [s : nonneg_ring α] : nonneg_comm_group α
class linear_nonneg_ring (α : Type)
@[instance] axiom linear_nonneg_ring.to_domain (α : Type) [s : linear_nonneg_ring α] : domain α
@[instance] axiom linear_nonneg_ring.to_nonneg_comm_group (α : Type) [s : linear_nonneg_ring α] : nonneg_comm_group α
@[instance] axiom nonneg_ring.to_ordered_ring (α : Type) [s : nonneg_ring α] : ordered_ring α
@[instance] axiom linear_nonneg_ring.to_nonneg_ring (α : Type) [s : linear_nonneg_ring α] : nonneg_ring α
@[instance] axiom linear_nonneg_ring.to_linear_order (α : Type) [s : linear_nonneg_ring α] : linear_order α
@[instance] axiom linear_nonneg_ring.to_linear_ordered_ring (α : Type) [s : linear_nonneg_ring α] : linear_ordered_ring α
class canonically_ordered_comm_semiring (α : Type)
@[instance] axiom canonically_ordered_comm_semiring.to_canonically_ordered_monoid (α : Type) [s : canonically_ordered_comm_semiring α] : canonically_ordered_monoid α
@[instance] axiom canonically_ordered_comm_semiring.to_comm_semiring (α : Type) [s : canonically_ordered_comm_semiring α] : comm_semiring α
@[instance] axiom canonically_ordered_comm_semiring.to_zero_ne_one_class (α : Type) [s : canonically_ordered_comm_semiring α] : zero_ne_one_class α
class category_theory.representable (C : Type) [𝒞 : category_theory.category C] (F : Type)
@[instance] axiom linear_ordered_field.to_densely_ordered (α : Type) [_inst_1 : linear_ordered_field α] : @densely_ordered α (@partial_order.to_preorder α (@ordered_comm_monoid.to_partial_order α (@ordered_cancel_comm_monoid.to_ordered_comm_monoid α (@ordered_semiring.to_ordered_cancel_comm_monoid α (@ordered_ring.to_ordered_semiring α (@linear_ordered_ring.to_ordered_ring α (@linear_ordered_field.to_linear_ordered_ring α _inst_1)))))))
@[instance] axiom linear_ordered_field.to_no_top_order (α : Type) [_inst_1 : linear_ordered_field α] : @no_top_order α (@partial_order.to_preorder α (@ordered_comm_monoid.to_partial_order α (@ordered_cancel_comm_monoid.to_ordered_comm_monoid α (@ordered_semiring.to_ordered_cancel_comm_monoid α (@ordered_ring.to_ordered_semiring α (@linear_ordered_ring.to_ordered_ring α (@linear_ordered_field.to_linear_ordered_ring α _inst_1)))))))
@[instance] axiom linear_ordered_field.to_no_bot_order (α : Type) [_inst_1 : linear_ordered_field α] : @no_bot_order α (@partial_order.to_preorder α (@ordered_comm_monoid.to_partial_order α (@ordered_cancel_comm_monoid.to_ordered_comm_monoid α (@ordered_semiring.to_ordered_cancel_comm_monoid α (@ordered_ring.to_ordered_semiring α (@linear_ordered_ring.to_ordered_ring α (@linear_ordered_field.to_linear_ordered_ring α _inst_1)))))))
class is_ring_anti_hom (R : Type) (F : Type) [_inst_1 : ring R] [_inst_2 : ring F] (f : Type)
@[instance] axiom is_ring_anti_hom.is_add_group_hom (R : Type) (F : Type) [_inst_1 : ring R] [_inst_2 : ring F] (f : Type) [_inst_3 : @is_ring_anti_hom R F _inst_1 _inst_2 f] : @is_add_group_hom R F (@add_comm_group.to_add_group R (@ring.to_add_comm_group R _inst_1)) (@add_comm_group.to_add_group F (@ring.to_add_comm_group F _inst_2)) f
class category_theory.reflective (C : Type) [𝒞 : category_theory.category C] (D : Type) [𝒟 : category_theory.category D] (R : Type)
@[instance] axiom category_theory.reflective.to_is_right_adjoint (C : Type) [𝒞 : category_theory.category C] (D : Type) [𝒟 : category_theory.category D] (R : Type) [c : @category_theory.reflective C 𝒞 D 𝒟 R] : @category_theory.is_right_adjoint C 𝒞 D 𝒟 R
@[instance] axiom category_theory.reflective.to_full (C : Type) [𝒞 : category_theory.category C] (D : Type) [𝒟 : category_theory.category D] (R : Type) [c : @category_theory.reflective C 𝒞 D 𝒟 R] : @category_theory.full D 𝒟 C 𝒞 R
@[instance] axiom category_theory.reflective.to_faithful (C : Type) [𝒞 : category_theory.category C] (D : Type) [𝒟 : category_theory.category D] (R : Type) [c : @category_theory.reflective C 𝒞 D 𝒟 R] : @category_theory.faithful D 𝒟 C 𝒞 R
class category_theory.monadic_right_adjoint (C : Type) [𝒞 : category_theory.category C] (D : Type) [𝒟 : category_theory.category D] (R : Type)
@[instance] axiom category_theory.monadic_right_adjoint.to_is_right_adjoint (C : Type) [𝒞 : category_theory.category C] (D : Type) [𝒟 : category_theory.category D] (R : Type) [c : @category_theory.monadic_right_adjoint C 𝒞 D 𝒟 R] : @category_theory.is_right_adjoint C 𝒞 D 𝒟 R
@[instance] axiom category_theory.monadic_of_reflective (C : Type) [𝒞 : category_theory.category C] (D : Type) [𝒟 : category_theory.category D] (R : Type) [_inst_1 : @category_theory.reflective C 𝒞 D 𝒟 R] : @category_theory.monadic_right_adjoint C 𝒞 D 𝒟 R
class wseq.is_finite (α : Type) (s : Type)
class wseq.productive (α : Type) (s : Type)
class euclidean_domain (α : Type)
@[instance] axiom euclidean_domain.to_nonzero_comm_ring (α : Type) [c : euclidean_domain α] : nonzero_comm_ring α
@[instance] axiom euclidean_domain.has_div (α : Type) [_inst_1 : euclidean_domain α] : has_div α
@[instance] axiom euclidean_domain.has_mod (α : Type) [_inst_1 : euclidean_domain α] : has_mod α
class category_theory.limits.has_limit (J : Type) [_inst_1 : category_theory.category J] (C : Type) [𝒞 : category_theory.category C] (F : Type)
class category_theory.limits.has_limits_of_shape (J : Type) [_inst_1 : category_theory.category J] (C : Type) [𝒞 : category_theory.category C]
class category_theory.limits.has_limits (C : Type) [𝒞 : category_theory.category C]
@[instance] axiom category_theory.limits.has_limit_of_has_limits_of_shape (C : Type) [𝒞 : category_theory.category C] (J : Type) [_inst_3 : category_theory.category J] [H : @category_theory.limits.has_limits_of_shape J _inst_3 C 𝒞] (F : Type) : @category_theory.limits.has_limit J _inst_3 C 𝒞 F
@[instance] axiom category_theory.limits.has_limits_of_shape_of_has_limits (C : Type) [𝒞 : category_theory.category C] (J : Type) [_inst_3 : category_theory.category J] [H : @category_theory.limits.has_limits C 𝒞] : @category_theory.limits.has_limits_of_shape J _inst_3 C 𝒞
@[instance] axiom euclidean_domain.integral_domain (α : Type) [e : euclidean_domain α] : integral_domain α
@[instance] axiom discrete_field.to_euclidean_domain (K : Type) [_inst_1 : discrete_field K] : euclidean_domain K
class category_theory.limits.has_colimit (J : Type) [_inst_1 : category_theory.category J] (C : Type) [𝒞 : category_theory.category C] (F : Type)
class category_theory.limits.has_colimits_of_shape (J : Type) [_inst_1 : category_theory.category J] (C : Type) [𝒞 : category_theory.category C]
class category_theory.limits.has_colimits (C : Type) [𝒞 : category_theory.category C]
@[instance] axiom category_theory.limits.has_colimit_of_has_colimits_of_shape (C : Type) [𝒞 : category_theory.category C] (J : Type) [_inst_3 : category_theory.category J] [H : @category_theory.limits.has_colimits_of_shape J _inst_3 C 𝒞] (F : Type) : @category_theory.limits.has_colimit J _inst_3 C 𝒞 F
@[instance] axiom category_theory.limits.has_colimits_of_shape_of_has_colimits (C : Type) [𝒞 : category_theory.category C] (J : Type) [_inst_3 : category_theory.category J] [H : @category_theory.limits.has_colimits C 𝒞] : @category_theory.limits.has_colimits_of_shape J _inst_3 C 𝒞
class encodable (α : Type)
class category_theory.limits.preserves_limit (C : Type) [𝒞 : category_theory.category C] (D : Type) [𝒟 : category_theory.category D] (J : Type) [_inst_1 : category_theory.category J] (K : Type) (F : Type)
class category_theory.limits.preserves_colimit (C : Type) [𝒞 : category_theory.category C] (D : Type) [𝒟 : category_theory.category D] (J : Type) [_inst_1 : category_theory.category J] (K : Type) (F : Type)
class category_theory.limits.preserves_limits_of_shape (C : Type) [𝒞 : category_theory.category C] (D : Type) [𝒟 : category_theory.category D] (J : Type) [_inst_2 : category_theory.category J] (F : Type)
class category_theory.limits.preserves_colimits_of_shape (C : Type) [𝒞 : category_theory.category C] (D : Type) [𝒟 : category_theory.category D] (J : Type) [_inst_2 : category_theory.category J] (F : Type)
class category_theory.limits.preserves_limits (C : Type) [𝒞 : category_theory.category C] (D : Type) [𝒟 : category_theory.category D] (F : Type)
@[instance] axiom category_theory.limits.has_limits_of_complete_lattice (α : Type) [_inst_1 : lattice.complete_lattice α] : @category_theory.limits.has_limits α (@preorder.small_category α (@partial_order.to_preorder α (@lattice.order_bot.to_partial_order α (@lattice.bounded_lattice.to_order_bot α (@lattice.complete_lattice.to_bounded_lattice α _inst_1)))))
class category_theory.limits.preserves_colimits (C : Type) [𝒞 : category_theory.category C] (D : Type) [𝒟 : category_theory.category D] (F : Type)
@[instance] axiom category_theory.limits.preserves_limits_of_shape.preserves_limit (C : Type) [𝒞 : category_theory.category C] (D : Type) [𝒟 : category_theory.category D] (J : Type) [_inst_2 : category_theory.category J] (F : Type) [c : @category_theory.limits.preserves_limits_of_shape C 𝒞 D 𝒟 J _inst_2 F] (K : Type) : @category_theory.limits.preserves_limit C 𝒞 D 𝒟 J _inst_2 K F
@[instance] axiom category_theory.limits.preserves_limits.preserves_limits_of_shape (C : Type) [𝒞 : category_theory.category C] (D : Type) [𝒟 : category_theory.category D] (F : Type) [c : @category_theory.limits.preserves_limits C 𝒞 D 𝒟 F] (J : Type) [𝒥 : category_theory.category J] : @category_theory.limits.preserves_limits_of_shape C 𝒞 D 𝒟 J 𝒥 F
@[instance] axiom category_theory.limits.preserves_colimits_of_shape.preserves_colimit (C : Type) [𝒞 : category_theory.category C] (D : Type) [𝒟 : category_theory.category D] (J : Type) [_inst_2 : category_theory.category J] (F : Type) [c : @category_theory.limits.preserves_colimits_of_shape C 𝒞 D 𝒟 J _inst_2 F] (K : Type) : @category_theory.limits.preserves_colimit C 𝒞 D 𝒟 J _inst_2 K F
@[instance] axiom category_theory.limits.preserves_colimits.preserves_colimits_of_shape (C : Type) [𝒞 : category_theory.category C] (D : Type) [𝒟 : category_theory.category D] (F : Type) [c : @category_theory.limits.preserves_colimits C 𝒞 D 𝒟 F] (J : Type) [𝒥 : category_theory.category J] : @category_theory.limits.preserves_colimits_of_shape C 𝒞 D 𝒟 J 𝒥 F
@[instance] axiom category_theory.limits.has_colimits_of_complete_lattice (α : Type) [_inst_1 : lattice.complete_lattice α] : @category_theory.limits.has_colimits α (@preorder.small_category α (@partial_order.to_preorder α (@lattice.order_bot.to_partial_order α (@lattice.bounded_lattice.to_order_bot α (@lattice.complete_lattice.to_bounded_lattice α _inst_1)))))
class category_theory.limits.reflects_limit (C : Type) [𝒞 : category_theory.category C] (D : Type) [𝒟 : category_theory.category D] (J : Type) [_inst_1 : category_theory.category J] (K : Type) (F : Type)
class category_theory.limits.reflects_colimit (C : Type) [𝒞 : category_theory.category C] (D : Type) [𝒟 : category_theory.category D] (J : Type) [_inst_1 : category_theory.category J] (K : Type) (F : Type)
class category_theory.limits.reflects_limits_of_shape (C : Type) [𝒞 : category_theory.category C] (D : Type) [𝒟 : category_theory.category D] (J : Type) [_inst_2 : category_theory.category J] (F : Type)
class category_theory.limits.reflects_colimits_of_shape (C : Type) [𝒞 : category_theory.category C] (D : Type) [𝒟 : category_theory.category D] (J : Type) [_inst_2 : category_theory.category J] (F : Type)
class category_theory.limits.reflects_limits (C : Type) [𝒞 : category_theory.category C] (D : Type) [𝒟 : category_theory.category D] (F : Type)
class category_theory.limits.reflects_colimits (C : Type) [𝒞 : category_theory.category C] (D : Type) [𝒟 : category_theory.category D] (F : Type)
@[instance] axiom category_theory.limits.reflects_limit_of_reflects_limits_of_shape (C : Type) [𝒞 : category_theory.category C] (D : Type) [𝒟 : category_theory.category D] (J : Type) [_inst_1 : category_theory.category J] (K : Type) (F : Type) [H : @category_theory.limits.reflects_limits_of_shape C 𝒞 D 𝒟 J _inst_1 F] : @category_theory.limits.reflects_limit C 𝒞 D 𝒟 J _inst_1 K F
@[instance] axiom category_theory.limits.reflects_colimit_of_reflects_colimits_of_shape (C : Type) [𝒞 : category_theory.category C] (D : Type) [𝒟 : category_theory.category D] (J : Type) [_inst_1 : category_theory.category J] (K : Type) (F : Type) [H : @category_theory.limits.reflects_colimits_of_shape C 𝒞 D 𝒟 J _inst_1 F] : @category_theory.limits.reflects_colimit C 𝒞 D 𝒟 J _inst_1 K F
@[instance] axiom category_theory.limits.reflects_limits_of_shape_of_reflects_limits (C : Type) [𝒞 : category_theory.category C] (D : Type) [𝒟 : category_theory.category D] (J : Type) [_inst_1 : category_theory.category J] (F : Type) [H : @category_theory.limits.reflects_limits C 𝒞 D 𝒟 F] : @category_theory.limits.reflects_limits_of_shape C 𝒞 D 𝒟 J _inst_1 F
@[instance] axiom category_theory.limits.reflects_colimits_of_shape_of_reflects_colimits (C : Type) [𝒞 : category_theory.category C] (D : Type) [𝒟 : category_theory.category D] (J : Type) [_inst_1 : category_theory.category J] (F : Type) [H : @category_theory.limits.reflects_colimits C 𝒞 D 𝒟 F] : @category_theory.limits.reflects_colimits_of_shape C 𝒞 D 𝒟 J _inst_1 F
@[instance] axiom category_theory.adjunction.left_adjoint_preserves_colimits (C : Type) [𝒞 : category_theory.category C] (D : Type) [𝒟 : category_theory.category D] (F : Type) (G : Type) (adj : Type) : @category_theory.limits.preserves_colimits C 𝒞 D 𝒟 F
@[instance] axiom category_theory.adjunction.is_equivalence_preserves_colimits (C : Type) [𝒞 : category_theory.category C] (D : Type) [𝒟 : category_theory.category D] (E : Type) [_inst_2 : @category_theory.is_equivalence C 𝒞 D 𝒟 E] : @category_theory.limits.preserves_colimits C 𝒞 D 𝒟 E
class irreducible (α : Type) [_inst_1 : monoid α] (p : Type)
class floor_ring (α : Type) [_inst_1 : linear_ordered_ring α]
class normalization_domain (α : Type)
@[instance] axiom normalization_domain.to_integral_domain (α : Type) [s : normalization_domain α] : integral_domain α
class archimedean (α : Type) [_inst_1 : ordered_comm_monoid α]
class gcd_domain (α : Type)
@[instance] axiom gcd_domain.to_normalization_domain (α : Type) [s : gcd_domain α] : normalization_domain α
@[instance] axiom category_theory.adjunction.right_adjoint_preserves_limits (C : Type) [𝒞 : category_theory.category C] (D : Type) [𝒟 : category_theory.category D] (F : Type) (G : Type) (adj : Type) : @category_theory.limits.preserves_limits D 𝒟 C 𝒞 G
@[instance] axiom category_theory.adjunction.is_equivalence_preserves_limits (C : Type) [𝒞 : category_theory.category C] (D : Type) [𝒟 : category_theory.category D] (E : Type) [_inst_2 : @category_theory.is_equivalence D 𝒟 C 𝒞 E] : @category_theory.limits.preserves_limits D 𝒟 C 𝒞 E
class zsqrtd.nonsquare (x : Type)
class unique_factorization_domain (α : Type) [_inst_1 : integral_domain α]
class fin2.is_lt (m : Type) (n : Type)
class is_absolute_value (α : Type) [_inst_1 : discrete_linear_ordered_field α] (β : Type) [_inst_2 : ring β] (f : Type)
class fintype (α : Type)
class is_add_submonoid (β : Type) [_inst_2 : add_monoid β] (s : Type)
class is_submonoid (α : Type) [_inst_1 : monoid α] (s : Type)
@[instance] axiom unique.fintype (α : Type) [_inst_1 : unique α] : fintype α
class nat.prime (p : Type)
class is_add_subgroup (β : Type) [_inst_2 : add_group β] (s : Type)
@[instance] axiom is_add_subgroup.to_is_add_submonoid (β : Type) [_inst_2 : add_group β] (s : Type) [c : @is_add_subgroup β _inst_2 s] : @is_add_submonoid β (@add_group.to_add_monoid β _inst_2) s
class is_subgroup (α : Type) [_inst_1 : group α] (s : Type)
@[instance] axiom is_subgroup.to_is_submonoid (α : Type) [_inst_1 : group α] (s : Type) [c : @is_subgroup α _inst_1 s] : @is_submonoid α (@group.to_monoid α _inst_1) s
class infinite (α : Type)
@[instance] axiom infinite.nonempty (α : Type) [_inst_1 : infinite α] : nonempty α
class denumerable (α : Type)
@[instance] axiom denumerable.to_encodable (α : Type) [c : denumerable α] : encodable α
class turing.pointed_map (Γ : Type) (Γ' : Type) [_inst_1 : inhabited Γ] [_inst_2 : inhabited Γ'] (f : Type)
class normal_add_subgroup (α : Type) [_inst_1 : add_group α] (s : Type)
@[instance] axiom normal_add_subgroup.to_is_add_subgroup (α : Type) [_inst_1 : add_group α] (s : Type) [c : @normal_add_subgroup α _inst_1 s] : @is_add_subgroup α _inst_1 s
class normal_subgroup (α : Type) [_inst_1 : group α] (s : Type)
@[instance] axiom normal_subgroup.to_is_subgroup (α : Type) [_inst_1 : group α] (s : Type) [c : @normal_subgroup α _inst_1 s] : @is_subgroup α _inst_1 s
class category_theory.limits.has_products (C : Type) [𝒞 : category_theory.category C]
class category_theory.limits.has_coproducts (C : Type) [𝒞 : category_theory.category C]
class category_theory.limits.fin_category (J : Type) [_inst_1 : category_theory.category J]
@[instance] axiom category_theory.limits.fin_category.fintype_obj (J : Type) [_inst_1 : category_theory.category J] [c : @category_theory.limits.fin_category J _inst_1] : fintype J
class category_theory.limits.has_finite_limits (C : Type) [𝒞 : category_theory.category C]
class category_theory.limits.has_finite_colimits (C : Type) [𝒞 : category_theory.category C]
@[instance] axiom category_theory.limits.has_finite_limits.has_limits_of_shape (C : Type) [𝒞 : category_theory.category C] [c : @category_theory.limits.has_finite_limits C 𝒞] (J : Type) [_inst_1 : category_theory.category J] [_inst_2 : @category_theory.limits.fin_category J _inst_1] : @category_theory.limits.has_limits_of_shape J _inst_1 C 𝒞
@[instance] axiom category_theory.limits.has_finite_colimits.has_colimits_of_shape (C : Type) [𝒞 : category_theory.category C] [c : @category_theory.limits.has_finite_colimits C 𝒞] (J : Type) [_inst_1 : category_theory.category J] [_inst_2 : @category_theory.limits.fin_category J _inst_1] : @category_theory.limits.has_colimits_of_shape J _inst_1 C 𝒞
@[instance] axiom category_theory.limits.category_theory.limits.has_finite_limits (C : Type) [𝒞 : category_theory.category C] [_inst_1 : @category_theory.limits.has_limits C 𝒞] : @category_theory.limits.has_finite_limits C 𝒞
@[instance] axiom category_theory.limits.category_theory.limits.has_finite_colimits (C : Type) [𝒞 : category_theory.category C] [_inst_1 : @category_theory.limits.has_colimits C 𝒞] : @category_theory.limits.has_finite_colimits C 𝒞
class category_theory.limits.has_finite_products (C : Type) [𝒞 : category_theory.category C]
class category_theory.limits.has_finite_coproducts (C : Type) [𝒞 : category_theory.category C]
@[instance] axiom category_theory.limits.has_finite_products_of_has_products (C : Type) [𝒞 : category_theory.category C] [_inst_1 : @category_theory.limits.has_products C 𝒞] : @category_theory.limits.has_finite_products C 𝒞
@[instance] axiom category_theory.limits.has_finite_coproducts_of_has_coproducts (C : Type) [𝒞 : category_theory.category C] [_inst_1 : @category_theory.limits.has_coproducts C 𝒞] : @category_theory.limits.has_finite_coproducts C 𝒞
@[instance] axiom category_theory.limits.has_finite_products_of_has_finite_limits (C : Type) [𝒞 : category_theory.category C] [_inst_1 : @category_theory.limits.has_finite_limits C 𝒞] : @category_theory.limits.has_finite_products C 𝒞
@[instance] axiom category_theory.limits.has_finite_coproducts_of_has_finite_colimits (C : Type) [𝒞 : category_theory.category C] [_inst_1 : @category_theory.limits.has_finite_colimits C 𝒞] : @category_theory.limits.has_finite_coproducts C 𝒞
class category_theory.limits.has_terminal (C : Type) [𝒞 : category_theory.category C]
class category_theory.limits.has_initial (C : Type) [𝒞 : category_theory.category C]
@[instance] axiom category_theory.limits.category_theory.limits.has_terminal (C : Type) [𝒞 : category_theory.category C] [_inst_1 : @category_theory.limits.has_finite_products C 𝒞] : @category_theory.limits.has_terminal C 𝒞
@[instance] axiom category_theory.limits.category_theory.limits.has_initial (C : Type) [𝒞 : category_theory.category C] [_inst_1 : @category_theory.limits.has_finite_coproducts C 𝒞] : @category_theory.limits.has_initial C 𝒞
class lattice.conditionally_complete_lattice (α : Type)
@[instance] axiom lattice.conditionally_complete_lattice.to_lattice (α : Type) [s : lattice.conditionally_complete_lattice α] : lattice.lattice α
@[instance] axiom lattice.conditionally_complete_lattice.to_has_Sup (α : Type) [s : lattice.conditionally_complete_lattice α] : lattice.has_Sup α
@[instance] axiom lattice.conditionally_complete_lattice.to_has_Inf (α : Type) [s : lattice.conditionally_complete_lattice α] : lattice.has_Inf α
class lattice.conditionally_complete_linear_order (α : Type)
@[instance] axiom lattice.conditionally_complete_linear_order.to_conditionally_complete_lattice (α : Type) [s : lattice.conditionally_complete_linear_order α] : lattice.conditionally_complete_lattice α
@[instance] axiom lattice.conditionally_complete_linear_order.to_decidable_linear_order (α : Type) [s : lattice.conditionally_complete_linear_order α] : decidable_linear_order α
class lattice.conditionally_complete_linear_order_bot (α : Type)
@[instance] axiom lattice.conditionally_complete_linear_order_bot.to_conditionally_complete_lattice (α : Type) [s : lattice.conditionally_complete_linear_order_bot α] : lattice.conditionally_complete_lattice α
@[instance] axiom lattice.conditionally_complete_linear_order_bot.to_decidable_linear_order (α : Type) [s : lattice.conditionally_complete_linear_order_bot α] : decidable_linear_order α
@[instance] axiom lattice.conditionally_complete_linear_order_bot.to_order_bot (α : Type) [s : lattice.conditionally_complete_linear_order_bot α] : lattice.order_bot α
class primcodable (α : Type)
@[instance] axiom primcodable.to_encodable (α : Type) [c : primcodable α] : encodable α
@[instance] axiom lattice.conditionally_complete_lattice_of_complete_lattice (α : Type) [_inst_1 : lattice.complete_lattice α] : lattice.conditionally_complete_lattice α
@[instance] axiom lattice.conditionally_complete_linear_order_of_complete_linear_order (α : Type) [_inst_1 : lattice.complete_linear_order α] : lattice.conditionally_complete_linear_order α
@[instance] axiom primcodable.of_denumerable (α : Type) [_inst_1 : denumerable α] : primcodable α
class measurable_space (α : Type)
class category_theory.limits.has_equalizers (C : Type) [𝒞 : category_theory.category C]
class category_theory.limits.has_coequalizers (C : Type) [𝒞 : category_theory.category C]
class category_theory.limits.has_pullbacks (C : Type) [𝒞 : category_theory.category C]
class category_theory.limits.has_pushouts (C : Type) [𝒞 : category_theory.category C]
class category_theory.limits.has_binary_products (C : Type) [𝒞 : category_theory.category C]
class category_theory.limits.has_binary_coproducts (C : Type) [𝒞 : category_theory.category C]
@[instance] axiom category_theory.limits.category_theory.limits.has_binary_products (C : Type) [𝒞 : category_theory.category C] [_inst_1 : @category_theory.limits.has_finite_products C 𝒞] : @category_theory.limits.has_binary_products C 𝒞
@[instance] axiom category_theory.limits.category_theory.limits.has_binary_coproducts (C : Type) [𝒞 : category_theory.category C] [_inst_1 : @category_theory.limits.has_finite_coproducts C 𝒞] : @category_theory.limits.has_binary_coproducts C 𝒞
class topological_space (α : Type)
class simple_group (α : Type) [_inst_1 : group α]
class simple_add_group (α : Type) [_inst_1 : add_group α]
class is_subring (R : Type) [_inst_1 : ring R] (S : Type)
@[instance] axiom is_subring.to_is_add_subgroup (R : Type) [_inst_1 : ring R] (S : Type) [c : @is_subring R _inst_1 S] : @is_add_subgroup R (@add_comm_group.to_add_group R (@ring.to_add_comm_group R _inst_1)) S
@[instance] axiom is_subring.to_is_submonoid (R : Type) [_inst_1 : ring R] (S : Type) [c : @is_subring R _inst_1 S] : @is_submonoid R (@ring.to_monoid R _inst_1) S
class compact_space (α : Type) [_inst_2 : topological_space α]
class discrete_topology (α : Type) [t : topological_space α]
class locally_compact_space (α : Type) [_inst_2 : topological_space α]
class irreducible_space (α : Type) [_inst_2 : topological_space α]
class is_subfield (F : Type) [_inst_1 : discrete_field F] (S : Type)
@[instance] axiom is_subfield.to_is_subring (F : Type) [_inst_1 : discrete_field F] (S : Type) [c : @is_subfield F _inst_1 S] : @is_subring F (@domain.to_ring F (@division_ring.to_domain F (@field.to_division_ring F (@discrete_field.to_field F _inst_1)))) S
class connected_space (α : Type) [_inst_2 : topological_space α]
@[instance] axiom irreducible_space.connected_space (α : Type) [_inst_2 : topological_space α] [_inst_3 : @irreducible_space α _inst_2] : @connected_space α _inst_2
class totally_disconnected_space (α : Type) [_inst_2 : topological_space α]
class totally_separated_space (α : Type) [_inst_2 : topological_space α]
@[instance] axiom totally_separated_space.totally_disconnected_space (α : Type) [_inst_2 : topological_space α] [_inst_3 : @totally_separated_space α _inst_2] : @totally_disconnected_space α _inst_2
class t0_space (α : Type) [_inst_2 : topological_space α]
class t1_space (α : Type) [_inst_2 : topological_space α]
@[instance] axiom t1_space.t0_space (α : Type) [_inst_1 : topological_space α] [_inst_2 : @t1_space α _inst_1] : @t0_space α _inst_1
class t2_space (α : Type) [_inst_2 : topological_space α]
class topological_space.separable_space (α : Type) [t : topological_space α]
@[instance] axiom t2_space.t1_space (α : Type) [_inst_1 : topological_space α] [_inst_2 : @t2_space α _inst_1] : @t1_space α _inst_1
class topological_space.first_countable_topology (α : Type) [t : topological_space α]
class topological_space.second_countable_topology (α : Type) [t : topological_space α]
@[instance] axiom topological_space.second_countable_topology.to_first_countable_topology (α : Type) [t : topological_space α] [_inst_1 : @topological_space.second_countable_topology α t] : @topological_space.first_countable_topology α t
@[instance] axiom t2_space_discrete (α : Type) [_inst_2 : topological_space α] [_inst_3 : @discrete_topology α _inst_2] : @t2_space α _inst_2
@[instance] axiom topological_space.second_countable_topology.to_separable_space (α : Type) [t : topological_space α] [_inst_1 : @topological_space.second_countable_topology α t] : @topological_space.separable_space α t
class regular_space (α : Type) [_inst_2 : topological_space α]
@[instance] axiom regular_space.to_t1_space (α : Type) [_inst_2 : topological_space α] [c : @regular_space α _inst_2] : @t1_space α _inst_2
@[instance] axiom regular_space.t2_space (α : Type) [_inst_1 : topological_space α] [_inst_2 : @regular_space α _inst_1] : @t2_space α _inst_1
class normal_space (α : Type) [_inst_2 : topological_space α]
@[instance] axiom normal_space.to_t1_space (α : Type) [_inst_2 : topological_space α] [c : @normal_space α _inst_2] : @t1_space α _inst_2
@[instance] axiom normal_space.regular_space (α : Type) [_inst_1 : topological_space α] [_inst_2 : @normal_space α _inst_1] : @regular_space α _inst_1
@[instance] axiom ctop.to_topsp (α : Type) (σ : Type) (F : Type) : topological_space α
class onote.NF (o : Type)
@[instance] axiom locally_compact_of_compact (α : Type) [_inst_1 : topological_space α] [_inst_5 : @t2_space α _inst_1] [_inst_6 : @compact_space α _inst_1] : @locally_compact_space α _inst_1
class has_scalar (α : Type) (γ : Type)
class mul_action (α : Type) (β : Type) [_inst_1 : monoid α]
@[instance] axiom mul_action.to_has_scalar (α : Type) (β : Type) [_inst_1 : monoid α] [c : @mul_action α β _inst_1] : has_scalar α β
class is_cyclic (α : Type) [_inst_1 : group α]
class distrib_mul_action (α : Type) (β : Type) [_inst_1 : monoid α] [_inst_2 : add_monoid β]
@[instance] axiom distrib_mul_action.to_mul_action (α : Type) (β : Type) [_inst_1 : monoid α] [_inst_2 : add_monoid β] [c : @distrib_mul_action α β _inst_1 _inst_2] : @mul_action α β _inst_1
class semimodule (α : Type) (β : Type) [_inst_1 : semiring α] [_inst_2 : add_comm_monoid β]
@[instance] axiom semimodule.to_distrib_mul_action (α : Type) (β : Type) [_inst_1 : semiring α] [_inst_2 : add_comm_monoid β] [c : @semimodule α β _inst_1 _inst_2] : @distrib_mul_action α β (@semiring.to_monoid α _inst_1) (@add_comm_monoid.to_add_monoid β _inst_2)
class uniform_space (α : Type)
@[instance] axiom uniform_space.to_topological_space (α : Type) [c : uniform_space α] : topological_space α
class module (α : Type) (β : Type) [_inst_1 : ring α] [_inst_2 : add_comm_group β]
@[instance] axiom module.to_semimodule (α : Type) (β : Type) [_inst_1 : ring α] [_inst_2 : add_comm_group β] [c : @module α β _inst_1 _inst_2] : @semimodule α β (@ring.to_semiring α _inst_1) (@add_comm_group.to_add_comm_monoid β _inst_2)
@[instance] axiom semiring.to_semimodule (α : Type) [r : semiring α] : @semimodule α α r (@semiring.to_add_comm_monoid α r)
@[instance] axiom ring.to_module (α : Type) [r : ring α] : @module α α r (@ring.to_add_comm_group α r)
class is_linear_map (α : Type) (β : Type) (γ : Type) [_inst_1 : ring α] [_inst_2 : add_comm_group β] [_inst_3 : add_comm_group γ] [_inst_4 : @module α β _inst_1 _inst_2] [_inst_5 : @module α γ _inst_1 _inst_3] (f : Type)
class separated (α : Type) [_inst_4 : uniform_space α]
@[instance] axiom separated_t2 (α : Type) [_inst_1 : uniform_space α] [s : @separated α _inst_1] : @t2_space α (@uniform_space.to_topological_space α _inst_1)
class manifold (H : Type) [_inst_1 : topological_space H] (M : Type) [_inst_2 : topological_space M]
@[instance] axiom manifold_model_space (H : Type) [_inst_1 : topological_space H] : @manifold H _inst_1 H _inst_1
@[instance] axiom separated_regular (α : Type) [_inst_1 : uniform_space α] [_inst_4 : @separated α _inst_1] : @regular_space α (@uniform_space.to_topological_space α _inst_1)
class complete_space (α : Type) [_inst_2 : uniform_space α]
class has_groupoid (H : Type) [_inst_4 : topological_space H] (M : Type) [_inst_5 : topological_space M] [_inst_6 : @manifold H _inst_4 M _inst_5] (G : Type)
@[instance] axiom complete_of_compact (α : Type) [_inst_2 : uniform_space α] [_inst_3 : @compact_space α (@uniform_space.to_topological_space α _inst_2)] : @complete_space α _inst_2
class vector_space (α : Type) (β : Type) [_inst_1 : discrete_field α] [_inst_2 : add_comm_group β]
@[instance] axiom vector_space.to_module (α : Type) (β : Type) [_inst_1 : discrete_field α] [_inst_2 : add_comm_group β] [c : @vector_space α β _inst_1 _inst_2] : @module α β (@domain.to_ring α (@division_ring.to_domain α (@field.to_division_ring α (@discrete_field.to_field α _inst_1)))) _inst_2
@[instance] axiom discrete_field.to_vector_space (α : Type) [_inst_1 : discrete_field α] : @vector_space α α _inst_1 (@ring.to_add_comm_group α (@domain.to_ring α (@division_ring.to_domain α (@field.to_division_ring α (@discrete_field.to_field α _inst_1)))))
@[instance] axiom has_groupoid_model_space (H : Type) [_inst_4 : topological_space H] (G : Type) : @has_groupoid H _inst_4 H _inst_4 (@manifold_model_space H _inst_4) G
class char_p (α : Type) [_inst_1 : semiring α] (p : Type)
class has_edist (α : Type)
class emetric_space (α : Type)
@[instance] axiom emetric_space.to_has_edist (α : Type) [c : emetric_space α] : has_edist α
@[instance] axiom emetric_space.to_uniform_space' (α : Type) [_inst_1 : emetric_space α] : uniform_space α
class perfect_field (α : Type) [_inst_1 : field α] (p : Type) [_inst_2 : @char_p α (@ring.to_semiring α (@domain.to_ring α (@division_ring.to_domain α (@field.to_division_ring α _inst_1)))) p]
@[instance] axiom to_separated (α : Type) [_inst_1 : emetric_space α] : @separated α (@emetric_space.to_uniform_space' α _inst_1)
@[instance] axiom emetric.topological_space.first_countable_topology (α : Type) [_inst_2 : emetric_space α] : @topological_space.first_countable_topology α (@uniform_space.to_topological_space α (@emetric_space.to_uniform_space' α _inst_2))
class topological_monoid (α : Type) [_inst_1 : topological_space α] [_inst_2 : monoid α]
class topological_add_monoid (α : Type) [_inst_1 : topological_space α] [_inst_2 : add_monoid α]
class topological_add_group (α : Type) [_inst_1 : topological_space α] [_inst_2 : add_group α]
@[instance] axiom topological_add_group.to_topological_add_monoid (α : Type) [_inst_1 : topological_space α] [_inst_2 : add_group α] [c : @topological_add_group α _inst_1 _inst_2] : @topological_add_monoid α _inst_1 (@add_group.to_add_monoid α _inst_2)
class topological_group (α : Type) [_inst_1 : topological_space α] [_inst_2 : group α]
@[instance] axiom topological_group.to_topological_monoid (α : Type) [_inst_1 : topological_space α] [_inst_2 : group α] [c : @topological_group α _inst_1 _inst_2] : @topological_monoid α _inst_1 (@group.to_monoid α _inst_2)
class add_group_with_zero_nhd (α : Type)
@[instance] axiom add_group_with_zero_nhd.to_add_comm_group (α : Type) [c : add_group_with_zero_nhd α] : add_comm_group α
@[instance] axiom add_group_with_zero_nhd.topological_space (α : Type) [_inst_1 : add_group_with_zero_nhd α] : topological_space α
@[instance] axiom add_group_with_zero_nhd.topological_add_monoid (α : Type) [_inst_1 : add_group_with_zero_nhd α] : @topological_add_monoid α (@add_group_with_zero_nhd.topological_space α _inst_1) (@add_group.to_add_monoid α (@add_comm_group.to_add_group α (@add_group_with_zero_nhd.to_add_comm_group α _inst_1)))
@[instance] axiom add_group_with_zero_nhd.topological_add_group (α : Type) [_inst_1 : add_group_with_zero_nhd α] : @topological_add_group α (@add_group_with_zero_nhd.topological_space α _inst_1) (@add_comm_group.to_add_group α (@add_group_with_zero_nhd.to_add_comm_group α _inst_1))
class uniform_add_group (α : Type) [_inst_1 : uniform_space α] [_inst_2 : add_group α]
class ordered_topology (α : Type) [t : topological_space α] [_inst_1 : preorder α]
@[instance] axiom uniform_add_group.to_topological_add_group (α : Type) [_inst_1 : uniform_space α] [_inst_2 : add_group α] [_inst_3 : @uniform_add_group α _inst_1 _inst_2] : @topological_add_group α (@uniform_space.to_topological_space α _inst_1) _inst_2
@[instance] axiom ordered_topology.to_t2_space (α : Type) [_inst_1 : topological_space α] [_inst_2 : partial_order α] [t : @ordered_topology α _inst_1 (@partial_order.to_preorder α _inst_2)] : @t2_space α _inst_1
class orderable_topology (α : Type) [t : topological_space α] [_inst_1 : partial_order α]
@[instance] axiom orderable_topology.to_ordered_topology (α : Type) [_inst_1 : topological_space α] [_inst_2 : linear_order α] [t : @orderable_topology α _inst_1 (@linear_order.to_partial_order α _inst_2)] : @ordered_topology α _inst_1 (@partial_order.to_preorder α (@linear_order.to_partial_order α _inst_2))
@[instance] axiom orderable_topology.t2_space (α : Type) [_inst_1 : topological_space α] [_inst_2 : linear_order α] [t : @orderable_topology α _inst_1 (@linear_order.to_partial_order α _inst_2)] : @t2_space α _inst_1
class add_comm_group.is_Z_bilin (α : Type) (β : Type) (γ : Type) [_inst_1 : add_comm_group α] [_inst_2 : add_comm_group β] [_inst_3 : add_comm_group γ] (f : Type)
@[instance] axiom orderable_topology.regular_space (α : Type) [_inst_1 : topological_space α] [_inst_2 : linear_order α] [t : @orderable_topology α _inst_1 (@linear_order.to_partial_order α _inst_2)] : @regular_space α _inst_1
class has_dist (α : Type)
class metric_space (α : Type)
@[instance] axiom metric_space.to_has_dist (α : Type) [c : metric_space α] : has_dist α
@[instance] axiom metric_space.to_uniform_space' (α : Type) [_inst_1 : metric_space α] : uniform_space α
@[instance] axiom metric_space.to_has_edist (α : Type) [_inst_1 : metric_space α] : has_edist α
@[instance] axiom metric_space.to_separated (α : Type) [_inst_1 : metric_space α] : @separated α (@metric_space.to_uniform_space' α _inst_1)
@[instance] axiom metric_space.to_emetric_space (α : Type) [_inst_1 : metric_space α] : emetric_space α
class proper_space (α : Type) [_inst_2 : metric_space α]
@[instance] axiom proper_of_compact (α : Type) [_inst_1 : metric_space α] [_inst_2 : @compact_space α (@uniform_space.to_topological_space α (@metric_space.to_uniform_space' α _inst_1))] : @proper_space α _inst_1
@[instance] axiom locally_compact_of_proper (α : Type) [_inst_1 : metric_space α] [_inst_2 : @proper_space α _inst_1] : @locally_compact_space α (@uniform_space.to_topological_space α (@metric_space.to_uniform_space' α _inst_1))
@[instance] axiom complete_of_proper (α : Type) [_inst_1 : metric_space α] [_inst_2 : @proper_space α _inst_1] : @complete_space α (@metric_space.to_uniform_space' α _inst_1)
@[instance] axiom second_countable_of_proper (α : Type) [_inst_1 : metric_space α] [_inst_2 : @proper_space α _inst_1] : @topological_space.second_countable_topology α (@uniform_space.to_topological_space α (@metric_space.to_uniform_space' α _inst_1))
class premetric_space (α : Type)
@[instance] axiom premetric_space.to_has_dist (α : Type) [c : premetric_space α] : has_dist α
class ideal.is_prime (α : Type) [_inst_1 : comm_ring α] (I : Type)
class ideal.is_maximal (α : Type) [_inst_1 : comm_ring α] (I : Type)
@[instance] axiom ideal.is_maximal.is_prime' (α : Type) [_inst_1 : comm_ring α] (I : Type) [H : @ideal.is_maximal α _inst_1 I] : @ideal.is_prime α _inst_1 I
class local_ring (α : Type)
@[instance] axiom local_ring.to_nonzero_comm_ring (α : Type) [c : local_ring α] : nonzero_comm_ring α
@[instance] axiom local_ring.comm_ring (α : Type) [_inst_1 : local_ring α] : comm_ring α
class is_local_ring_hom (α : Type) (β : Type) [_inst_1 : comm_ring α] [_inst_2 : comm_ring β] (f : Type)
@[instance] axiom is_local_ring_hom.to_is_ring_hom (α : Type) (β : Type) [_inst_1 : comm_ring α] [_inst_2 : comm_ring β] (f : Type) [c : @is_local_ring_hom α β _inst_1 _inst_2 f] : @is_ring_hom α β (@comm_ring.to_ring α _inst_1) (@comm_ring.to_ring β _inst_2) f
@[instance] axiom discrete_field.local_ring (α : Type) [_inst_1 : discrete_field α] : local_ring α
class topological_semiring (α : Type) [_inst_1 : topological_space α] [_inst_2 : semiring α]
@[instance] axiom topological_semiring.to_topological_add_monoid (α : Type) [_inst_1 : topological_space α] [_inst_2 : semiring α] [c : @topological_semiring α _inst_1 _inst_2] : @topological_add_monoid α _inst_1 (@add_comm_monoid.to_add_monoid α (@semiring.to_add_comm_monoid α _inst_2))
@[instance] axiom topological_semiring.to_topological_monoid (α : Type) [_inst_1 : topological_space α] [_inst_2 : semiring α] [c : @topological_semiring α _inst_1 _inst_2] : @topological_monoid α _inst_1 (@semiring.to_monoid α _inst_2)
class topological_ring (α : Type) [_inst_1 : topological_space α] [_inst_2 : ring α]
@[instance] axiom topological_ring.to_topological_add_monoid (α : Type) [_inst_1 : topological_space α] [_inst_2 : ring α] [c : @topological_ring α _inst_1 _inst_2] : @topological_add_monoid α _inst_1 (@add_group.to_add_monoid α (@add_comm_group.to_add_group α (@ring.to_add_comm_group α _inst_2)))
@[instance] axiom topological_ring.to_topological_monoid (α : Type) [_inst_1 : topological_space α] [_inst_2 : ring α] [c : @topological_ring α _inst_1 _inst_2] : @topological_monoid α _inst_1 (@ring.to_monoid α _inst_2)
@[instance] axiom topological_ring.to_topological_semiring (α : Type) [_inst_1 : topological_space α] [_inst_2 : ring α] [t : @topological_ring α _inst_1 _inst_2] : @topological_semiring α _inst_1 (@ring.to_semiring α _inst_2)
@[instance] axiom topological_ring.to_topological_add_group (α : Type) [_inst_1 : topological_space α] [_inst_2 : ring α] [t : @topological_ring α _inst_1 _inst_2] : @topological_add_group α _inst_1 (@add_comm_group.to_add_group α (@ring.to_add_comm_group α _inst_2))
class algebra (R : Type) (A : Type) [_inst_1 : comm_ring R] [_inst_2 : ring A]
@[instance] axiom algebra.to_module (R : Type) (A : Type) [_inst_1 : comm_ring R] [_inst_2 : ring A] [c : @algebra R A _inst_1 _inst_2] : @module R A (@comm_ring.to_ring R _inst_1) (@ring.to_add_comm_group A _inst_2)
@[instance] axiom algebra.module (R : Type) (A : Type) [_inst_1 : comm_ring R] [_inst_3 : ring A] [_inst_4 : @algebra R A _inst_1 _inst_3] : @module R A (@comm_ring.to_ring R _inst_1) (@ring.to_add_comm_group A _inst_3)
@[instance] axiom algebra.has_scalar (R : Type) (A : Type) [_inst_1 : comm_ring R] [_inst_3 : ring A] [_inst_4 : @algebra R A _inst_1 _inst_3] : has_scalar R A
@[instance] axiom algebra.vector_space (F : Type) (K : Type) [_inst_5 : discrete_field F] [_inst_6 : ring K] [_inst_7 : @algebra F K (@local_ring.comm_ring F (@discrete_field.local_ring F _inst_5)) _inst_6] : @vector_space F K _inst_5 (@ring.to_add_comm_group K _inst_6)
@[instance] axiom algebra.id (R : Type) [_inst_1 : comm_ring R] : @algebra R R _inst_1 (@comm_ring.to_ring R _inst_1)
class topological_semimodule (α : Type) (β : Type) [_inst_1 : semiring α] [_inst_2 : topological_space α] [_inst_3 : topological_space β] [_inst_4 : add_comm_monoid β] [_inst_5 : @semimodule α β _inst_1 _inst_4]
class topological_module (α : Type) (β : Type) [_inst_1 : ring α] [_inst_2 : topological_space α] [_inst_3 : topological_space β] [_inst_4 : add_comm_group β] [_inst_5 : @module α β _inst_1 _inst_4]
@[instance] axiom topological_module.to_topological_semimodule (α : Type) (β : Type) [_inst_1 : ring α] [_inst_2 : topological_space α] [_inst_3 : topological_space β] [_inst_4 : add_comm_group β] [_inst_5 : @module α β _inst_1 _inst_4] [c : @topological_module α β _inst_1 _inst_2 _inst_3 _inst_4 _inst_5] : @topological_semimodule α β (@ring.to_semiring α _inst_1) _inst_2 _inst_3 (@add_comm_group.to_add_comm_monoid β _inst_4) (@module.to_semimodule α β _inst_1 _inst_4 _inst_5)
class topological_vector_space (α : Type) (β : Type) [_inst_1 : discrete_field α] [_inst_2 : topological_space α] [_inst_3 : topological_space β] [_inst_4 : add_comm_group β] [_inst_5 : @vector_space α β _inst_1 _inst_4]
@[instance] axiom topological_vector_space.to_topological_module (α : Type) (β : Type) [_inst_1 : discrete_field α] [_inst_2 : topological_space α] [_inst_3 : topological_space β] [_inst_4 : add_comm_group β] [_inst_5 : @vector_space α β _inst_1 _inst_4] [c : @topological_vector_space α β _inst_1 _inst_2 _inst_3 _inst_4 _inst_5] : @topological_module α β (@domain.to_ring α (@division_ring.to_domain α (@field.to_division_ring α (@discrete_field.to_field α _inst_1)))) _inst_2 _inst_3 _inst_4 (@vector_space.to_module α β _inst_1 _inst_4 _inst_5)
class has_norm (α : Type)
class normed_group (α : Type)
@[instance] axiom normed_group.to_has_norm (α : Type) [c : normed_group α] : has_norm α
@[instance] axiom normed_group.to_add_comm_group (α : Type) [c : normed_group α] : add_comm_group α
@[instance] axiom normed_group.to_metric_space (α : Type) [c : normed_group α] : metric_space α
@[instance] axiom normed_uniform_group (α : Type) [_inst_1 : normed_group α] : @uniform_add_group α (@metric_space.to_uniform_space' α (@normed_group.to_metric_space α _inst_1)) (@add_comm_group.to_add_group α (@normed_group.to_add_comm_group α _inst_1))
@[instance] axiom normed_top_monoid (α : Type) [_inst_1 : normed_group α] : @topological_add_monoid α (@uniform_space.to_topological_space α (@metric_space.to_uniform_space' α (@normed_group.to_metric_space α _inst_1))) (@add_group.to_add_monoid α (@add_comm_group.to_add_group α (@normed_group.to_add_comm_group α _inst_1)))
@[instance] axiom normed_top_group (α : Type) [_inst_1 : normed_group α] : @topological_add_group α (@uniform_space.to_topological_space α (@metric_space.to_uniform_space' α (@normed_group.to_metric_space α _inst_1))) (@add_comm_group.to_add_group α (@normed_group.to_add_comm_group α _inst_1))
class normed_ring (α : Type)
@[instance] axiom normed_ring.to_has_norm (α : Type) [c : normed_ring α] : has_norm α
@[instance] axiom normed_ring.to_ring (α : Type) [c : normed_ring α] : ring α
@[instance] axiom normed_ring.to_metric_space (α : Type) [c : normed_ring α] : metric_space α
@[instance] axiom normed_ring.to_normed_group (α : Type) [β : normed_ring α] : normed_group α
@[instance] axiom normed_ring_top_monoid (α : Type) [_inst_1 : normed_ring α] : @topological_monoid α (@uniform_space.to_topological_space α (@metric_space.to_uniform_space' α (@normed_ring.to_metric_space α _inst_1))) (@ring.to_monoid α (@normed_ring.to_ring α _inst_1))
@[instance] axiom normed_top_ring (α : Type) [_inst_1 : normed_ring α] : @topological_ring α (@uniform_space.to_topological_space α (@metric_space.to_uniform_space' α (@normed_ring.to_metric_space α _inst_1))) (@normed_ring.to_ring α _inst_1)
class normed_field (α : Type)
@[instance] axiom normed_field.to_has_norm (α : Type) [c : normed_field α] : has_norm α
@[instance] axiom normed_field.to_discrete_field (α : Type) [c : normed_field α] : discrete_field α
@[instance] axiom normed_field.to_metric_space (α : Type) [c : normed_field α] : metric_space α
class nondiscrete_normed_field (α : Type)
@[instance] axiom nondiscrete_normed_field.to_normed_field (α : Type) [c : nondiscrete_normed_field α] : normed_field α
@[instance] axiom normed_field.to_normed_ring (α : Type) [i : normed_field α] : normed_ring α
class normed_space (α : Type) (β : Type) [_inst_1 : normed_field α] [_inst_2 : normed_group β]
@[instance] axiom normed_space.to_vector_space (α : Type) (β : Type) [_inst_1 : normed_field α] [_inst_2 : normed_group β] [c : @normed_space α β _inst_1 _inst_2] : @vector_space α β (@normed_field.to_discrete_field α _inst_1) (@normed_group.to_add_comm_group β _inst_2)
@[instance] axiom normed_field.to_normed_space (α : Type) [_inst_1 : normed_field α] : @normed_space α α _inst_1 (@normed_ring.to_normed_group α (@normed_field.to_normed_ring α _inst_1))
class is_noetherian (α : Type) (β : Type) [_inst_1 : ring α] [_inst_2 : add_comm_group β] [_inst_3 : @module α β _inst_1 _inst_2]
@[instance] axiom normed_space.topological_vector_space (α : Type) [_inst_1 : normed_field α] (E : Type) [_inst_3 : normed_group E] [_inst_4 : @normed_space α E _inst_1 _inst_3] : @topological_vector_space α E (@normed_field.to_discrete_field α _inst_1) (@uniform_space.to_topological_space α (@metric_space.to_uniform_space' α (@normed_field.to_metric_space α _inst_1))) (@uniform_space.to_topological_space E (@metric_space.to_uniform_space' E (@normed_group.to_metric_space E _inst_3))) (@normed_group.to_add_comm_group E _inst_3) (@normed_space.to_vector_space α E _inst_1 _inst_3 _inst_4)
class is_noetherian_ring (α : Type) [_inst_1 : ring α]
@[instance] axiom is_noetherian_ring.to_is_noetherian (α : Type) [_inst_1 : ring α] [_inst_2 : @is_noetherian_ring α _inst_1] : @is_noetherian α α _inst_1 (@ring.to_add_comm_group α _inst_1) (@ring.to_module α _inst_1)
@[instance] axiom ring.is_noetherian_of_fintype (R : Type) (M : Type) [_inst_1 : fintype M] [_inst_2 : ring R] [_inst_3 : add_comm_group M] [_inst_4 : @module R M _inst_2 _inst_3] : @is_noetherian R M _inst_2 _inst_3 _inst_4
@[instance] axiom measure_theory.borel (α : Type) [_inst_1 : topological_space α] : measurable_space α
class ideal.is_principal (α : Type) [_inst_1 : comm_ring α] (S : Type)
class principal_ideal_domain (α : Type)
@[instance] axiom principal_ideal_domain.to_integral_domain (α : Type) [c : principal_ideal_domain α] : integral_domain α
@[instance] axiom principal_ideal_domain.principal (α : Type) [c : principal_ideal_domain α] (S : Type) : @ideal.is_principal α (@nonzero_comm_ring.to_comm_ring α (@integral_domain.to_nonzero_comm_ring α (@principal_ideal_domain.to_integral_domain α c))) S
@[instance] axiom euclidean_domain.to_principal_ideal_domain (α : Type) [_inst_1 : euclidean_domain α] : principal_ideal_domain α
@[instance] axiom principal_ideal_domain.is_noetherian_ring (α : Type) [_inst_1 : principal_ideal_domain α] : @is_noetherian_ring α (@domain.to_ring α (@integral_domain.to_domain α (@principal_ideal_domain.to_integral_domain α _inst_1)))
class sequential_space (α : Type) [_inst_3 : topological_space α]
@[instance] axiom metric.sequential_space (α : Type) [_inst_1 : metric_space α] : @sequential_space α (@uniform_space.to_topological_space α (@metric_space.to_uniform_space' α _inst_1))
class has_inner (α : Type)
class inner_product_space (α : Type)
@[instance] axiom inner_product_space.to_add_comm_group (α : Type) [c : inner_product_space α] : add_comm_group α
@[instance] axiom inner_product_space.to_has_inner (α : Type) [c : inner_product_space α] : has_inner α
@[instance] axiom inner_product_space_has_norm (α : Type) [_inst_1 : inner_product_space α] : has_norm α
@[instance] axiom inner_product_space_is_normed_group (α : Type) [_inst_1 : inner_product_space α] : normed_group α
class measure_theory.measure.is_complete (α : Type) (_x : Type) (μ : Type)
class measure_theory.measure_space (α : Type)
@[instance] axiom measure_theory.measure_space.to_measurable_space (α : Type) [c : measure_theory.measure_space α] : measurable_space α
end test
