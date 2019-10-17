noncomputable theory
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
@[instance] constant nonempty_of_inhabited (α : Type) [inhabited α] : nonempty α
class subsingleton (α : Type)
@[instance] constant subsingleton_prop (p : Type) : subsingleton p
class setoid (α : Type)
@[instance] constant setoid_has_equiv (α : Type) [setoid α] : has_equiv α
class has_well_founded (α : Type)
@[instance] constant has_well_founded_of_has_sizeof (α : Type) [has_sizeof α] : has_well_founded α
class has_lift (a : Type) (b : Type)
class has_lift_t (a : Type) (b : Type)
class has_coe (a : Type) (b : Type)
class has_coe_t (a : Type) (b : Type)
class has_coe_to_fun (a : Type)
class has_coe_to_sort (a : Type)
@[instance] constant lift_trans (a : Type) (b : Type) (c : Type) [has_lift a b] [has_lift_t b c] : has_lift_t a c
@[instance] constant lift_base (a : Type) (b : Type) [has_lift a b] : has_lift_t a b
@[instance] constant coe_trans (a : Type) (b : Type) (c : Type) [has_coe a b] [has_coe_t b c] : has_coe_t a c
@[instance] constant coe_base (a : Type) (b : Type) [has_coe a b] : has_coe_t a b
class has_coe_t_aux (a : Type) (b : Type)
@[instance] constant coe_trans_aux (a : Type) (b : Type) (c : Type) [has_coe a b] [has_coe_t_aux b c] : has_coe_t_aux a c
@[instance] constant coe_base_aux (a : Type) (b : Type) [has_coe a b] : has_coe_t_aux a b
@[instance] constant coe_fn_trans (a : Type) (b : Type) [has_coe_t_aux a b] [has_coe_to_fun b] : has_coe_to_fun a
@[instance] constant coe_sort_trans (a : Type) (b : Type) [has_coe_t_aux a b] [has_coe_to_sort b] : has_coe_to_sort a
@[instance] constant coe_to_lift (a : Type) (b : Type) [has_coe_t a b] : has_lift_t a b
class has_repr (α : Type)
class has_to_string (α : Type)
class is_symm_op (α : Type) (β : Type) (op : Type)
class is_commutative (α : Type) (op : Type)
@[instance] constant is_symm_op_of_is_commutative (α : Type) (op : Type) [is_commutative α op] : is_symm_op α α op
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
@[instance] constant is_preorder.to_is_refl (α : Type) (r : Type) [is_preorder α r] : is_refl α r
@[instance] constant is_preorder.to_is_trans (α : Type) (r : Type) [is_preorder α r] : is_trans α r
class is_total_preorder (α : Type) (r : Type)
@[instance] constant is_total_preorder.to_is_trans (α : Type) (r : Type) [is_total_preorder α r] : is_trans α r
@[instance] constant is_total_preorder.to_is_total (α : Type) (r : Type) [is_total_preorder α r] : is_total α r
@[instance] constant is_total_preorder_is_preorder (α : Type) (r : Type) [is_total_preorder α r] : is_preorder α r
class has_to_format (α : Type)
class is_partial_order (α : Type) (r : Type)
@[instance] constant is_partial_order.to_is_preorder (α : Type) (r : Type) [is_partial_order α r] : is_preorder α r
@[instance] constant is_partial_order.to_is_antisymm (α : Type) (r : Type) [is_partial_order α r] : is_antisymm α r
class is_linear_order (α : Type) (r : Type)
@[instance] constant is_linear_order.to_is_partial_order (α : Type) (r : Type) [is_linear_order α r] : is_partial_order α r
@[instance] constant is_linear_order.to_is_total (α : Type) (r : Type) [is_linear_order α r] : is_total α r
class is_equiv (α : Type) (r : Type)
@[instance] constant is_equiv.to_is_preorder (α : Type) (r : Type) [is_equiv α r] : is_preorder α r
@[instance] constant is_equiv.to_is_symm (α : Type) (r : Type) [is_equiv α r] : is_symm α r
class is_per (α : Type) (r : Type)
@[instance] constant is_per.to_is_symm (α : Type) (r : Type) [is_per α r] : is_symm α r
@[instance] constant is_per.to_is_trans (α : Type) (r : Type) [is_per α r] : is_trans α r
class is_strict_order (α : Type) (r : Type)
@[instance] constant is_strict_order.to_is_irrefl (α : Type) (r : Type) [is_strict_order α r] : is_irrefl α r
@[instance] constant is_strict_order.to_is_trans (α : Type) (r : Type) [is_strict_order α r] : is_trans α r
class is_incomp_trans (α : Type) (lt : Type)
class is_strict_weak_order (α : Type) (lt : Type)
@[instance] constant is_strict_weak_order.to_is_strict_order (α : Type) (lt : Type) [is_strict_weak_order α lt] : is_strict_order α lt
@[instance] constant is_strict_weak_order.to_is_incomp_trans (α : Type) (lt : Type) [is_strict_weak_order α lt] : is_incomp_trans α lt
class is_trichotomous (α : Type) (lt : Type)
class is_strict_total_order (α : Type) (lt : Type)
@[instance] constant is_strict_total_order.to_is_trichotomous (α : Type) (lt : Type) [is_strict_total_order α lt] : is_trichotomous α lt
@[instance] constant is_strict_total_order.to_is_strict_weak_order (α : Type) (lt : Type) [is_strict_total_order α lt] : is_strict_weak_order α lt
@[instance] constant is_asymm_of_is_trans_of_is_irrefl (α : Type) (r : Type) [is_trans α r] [is_irrefl α r] : is_asymm α r
class functor (f : Type)
class has_pure (f : Type)
class has_seq (f : Type)
class has_seq_left (f : Type)
class has_seq_right (f : Type)
class preorder (α : Type)
@[instance] constant preorder.to_has_le (α : Type) [preorder α] : has_le α
@[instance] constant preorder.to_has_lt (α : Type) [preorder α] : has_lt α
class applicative (f : Type)
@[instance] constant applicative.to_functor (f : Type) [applicative f] : functor f
@[instance] constant applicative.to_has_pure (f : Type) [applicative f] : has_pure f
@[instance] constant applicative.to_has_seq (f : Type) [applicative f] : has_seq f
@[instance] constant applicative.to_has_seq_left (f : Type) [applicative f] : has_seq_left f
@[instance] constant applicative.to_has_seq_right (f : Type) [applicative f] : has_seq_right f
class has_bind (m : Type)
class partial_order (α : Type)
@[instance] constant partial_order.to_preorder (α : Type) [partial_order α] : preorder α
class monad (m : Type)
@[instance] constant monad.to_applicative (m : Type) [monad m] : applicative m
@[instance] constant monad.to_has_bind (m : Type) [monad m] : has_bind m
class linear_order (α : Type)
@[instance] constant linear_order.to_partial_order (α : Type) [linear_order α] : partial_order α
class has_orelse (f : Type)
class alternative (f : Type)
@[instance] constant alternative.to_applicative (f : Type) [alternative f] : applicative f
@[instance] constant alternative.to_has_orelse (f : Type) [alternative f] : has_orelse f
class has_monad_lift (m : Type) (n : Type)
class has_monad_lift_t (m : Type) (n : Type)
@[instance] constant has_monad_lift_t_trans (m : Type) (n : Type) (o : Type) [has_monad_lift n o] [has_monad_lift_t m n] : has_monad_lift_t m o
@[instance] constant has_monad_lift_t_refl (m : Type) : has_monad_lift_t m m
class monad_functor (m : Type) (m' : Type) (n : Type) (n' : Type)
class monad_functor_t (m : Type) (m' : Type) (n : Type) (n' : Type)
@[instance] constant monad_functor_t_trans (m : Type) (m' : Type) (n : Type) (n' : Type) (o : Type) (o' : Type) [monad_functor n n' o o'] [monad_functor_t m m' n n'] : monad_functor_t m m' o o'
@[instance] constant monad_functor_t_refl (m : Type) (m' : Type) : monad_functor_t m m' m m'
class monad_run (out : Type) (m : Type)
class monad_fail (m : Type)
class decidable_linear_order (α : Type)
@[instance] constant monad_fail_lift (m : Type) (n : Type) [has_monad_lift m n] [monad_fail m] [monad n] : monad_fail n
@[instance] constant decidable_linear_order.to_linear_order (α : Type) [decidable_linear_order α] : linear_order α
class reflected (α : Type) (a : Type)
class monad_except (ε : Type) (m : Type)
class monad_except_adapter (ε : Type) (ε' : Type) (m : Type) (m' : Type)
@[instance] constant monad_except_adapter_trans (ε : Type) (ε' : Type) (m : Type) (m' : Type) (n : Type) (n' : Type) [monad_functor m m' n n'] [monad_except_adapter ε ε' m m'] : monad_except_adapter ε ε' n n'
class monad_reader (ρ : Type) (m : Type)
@[instance] constant monad_reader_trans (ρ : Type) (m : Type) (n : Type) [has_monad_lift m n] [monad_reader ρ m] : monad_reader ρ n
class monad_reader_adapter (ρ : Type) (ρ' : Type) (m : Type) (m' : Type)
@[instance] constant monad_reader_adapter_trans (ρ : Type) (ρ' : Type) (m : Type) (m' : Type) (n : Type) (n' : Type) [monad_functor m m' n n'] [monad_reader_adapter ρ ρ' m m'] : monad_reader_adapter ρ ρ' n n'
class monad_state (σ : Type) (m : Type)
@[instance] constant monad_state_trans (σ : Type) (m : Type) (n : Type) [has_monad_lift m n] [monad_state σ m] : monad_state σ n
class monad_state_adapter (σ : Type) (σ' : Type) (m : Type) (m' : Type)
@[instance] constant monad_state_adapter_trans (σ : Type) (σ' : Type) (m : Type) (m' : Type) (n : Type) (n' : Type) [monad_functor m m' n n'] [monad_state_adapter σ σ' m m'] : monad_state_adapter σ σ' n n'
class has_to_pexpr (α : Type)
class has_to_tactic_format (α : Type)
@[instance] constant has_to_format_to_has_to_tactic_format (α : Type) [has_to_format α] : has_to_tactic_format α
class is_lawful_functor (f : Type) [functor f]
class is_lawful_applicative (f : Type) [applicative f]
@[instance] constant is_lawful_applicative.to_is_lawful_functor (f : Type) [applicative f] [@is_lawful_applicative f _inst_1] : @is_lawful_functor f (@applicative.to_functor f _inst_1)
class is_lawful_monad (m : Type) [monad m]
@[instance] constant is_lawful_monad.to_is_lawful_applicative (m : Type) [monad m] [@is_lawful_monad m _inst_1] : @is_lawful_applicative m (@monad.to_applicative m _inst_1)
class semigroup (α : Type)
@[instance] constant semigroup.to_has_mul (α : Type) [semigroup α] : has_mul α
class comm_semigroup (α : Type)
@[instance] constant comm_semigroup.to_semigroup (α : Type) [comm_semigroup α] : semigroup α
class left_cancel_semigroup (α : Type)
@[instance] constant left_cancel_semigroup.to_semigroup (α : Type) [left_cancel_semigroup α] : semigroup α
class right_cancel_semigroup (α : Type)
@[instance] constant right_cancel_semigroup.to_semigroup (α : Type) [right_cancel_semigroup α] : semigroup α
class monoid (α : Type)
@[instance] constant monoid.to_semigroup (α : Type) [monoid α] : semigroup α
@[instance] constant monoid.to_has_one (α : Type) [monoid α] : has_one α
class comm_monoid (α : Type)
@[instance] constant comm_monoid.to_monoid (α : Type) [comm_monoid α] : monoid α
@[instance] constant comm_monoid.to_comm_semigroup (α : Type) [comm_monoid α] : comm_semigroup α
class group (α : Type)
@[instance] constant group.to_monoid (α : Type) [group α] : monoid α
@[instance] constant group.to_has_inv (α : Type) [group α] : has_inv α
class comm_group (α : Type)
@[instance] constant comm_group.to_group (α : Type) [comm_group α] : group α
@[instance] constant comm_group.to_comm_monoid (α : Type) [comm_group α] : comm_monoid α
@[instance] constant group.to_left_cancel_semigroup (α : Type) [group α] : left_cancel_semigroup α
@[instance] constant group.to_right_cancel_semigroup (α : Type) [group α] : right_cancel_semigroup α
class add_semigroup (α : Type)
@[instance] constant add_semigroup.to_has_add (α : Type) [add_semigroup α] : has_add α
class add_comm_semigroup (α : Type)
@[instance] constant add_comm_semigroup.to_add_semigroup (α : Type) [add_comm_semigroup α] : add_semigroup α
class add_left_cancel_semigroup (α : Type)
@[instance] constant add_left_cancel_semigroup.to_add_semigroup (α : Type) [add_left_cancel_semigroup α] : add_semigroup α
class add_right_cancel_semigroup (α : Type)
@[instance] constant add_right_cancel_semigroup.to_add_semigroup (α : Type) [add_right_cancel_semigroup α] : add_semigroup α
class add_monoid (α : Type)
@[instance] constant add_monoid.to_add_semigroup (α : Type) [add_monoid α] : add_semigroup α
@[instance] constant add_monoid.to_has_zero (α : Type) [add_monoid α] : has_zero α
class add_comm_monoid (α : Type)
@[instance] constant add_comm_monoid.to_add_monoid (α : Type) [add_comm_monoid α] : add_monoid α
@[instance] constant add_comm_monoid.to_add_comm_semigroup (α : Type) [add_comm_monoid α] : add_comm_semigroup α
class add_group (α : Type)
@[instance] constant add_group.to_add_monoid (α : Type) [add_group α] : add_monoid α
@[instance] constant add_group.to_has_neg (α : Type) [add_group α] : has_neg α
class add_comm_group (α : Type)
@[instance] constant add_comm_group.to_add_group (α : Type) [add_comm_group α] : add_group α
@[instance] constant add_comm_group.to_add_comm_monoid (α : Type) [add_comm_group α] : add_comm_monoid α
@[instance] constant add_group.to_left_cancel_add_semigroup (α : Type) [add_group α] : add_left_cancel_semigroup α
@[instance] constant add_group.to_right_cancel_add_semigroup (α : Type) [add_group α] : add_right_cancel_semigroup α
@[instance] constant add_group_has_sub (α : Type) [add_group α] : has_sub α
class distrib (α : Type)
@[instance] constant distrib.to_has_mul (α : Type) [distrib α] : has_mul α
@[instance] constant distrib.to_has_add (α : Type) [distrib α] : has_add α
class ordered_cancel_comm_monoid (α : Type)
@[instance] constant ordered_cancel_comm_monoid.to_add_comm_monoid (α : Type) [ordered_cancel_comm_monoid α] : add_comm_monoid α
@[instance] constant ordered_cancel_comm_monoid.to_add_left_cancel_semigroup (α : Type) [ordered_cancel_comm_monoid α] : add_left_cancel_semigroup α
@[instance] constant ordered_cancel_comm_monoid.to_add_right_cancel_semigroup (α : Type) [ordered_cancel_comm_monoid α] : add_right_cancel_semigroup α
@[instance] constant ordered_cancel_comm_monoid.to_partial_order (α : Type) [ordered_cancel_comm_monoid α] : partial_order α
class mul_zero_class (α : Type)
@[instance] constant mul_zero_class.to_has_mul (α : Type) [mul_zero_class α] : has_mul α
@[instance] constant mul_zero_class.to_has_zero (α : Type) [mul_zero_class α] : has_zero α
class zero_ne_one_class (α : Type)
@[instance] constant zero_ne_one_class.to_has_zero (α : Type) [zero_ne_one_class α] : has_zero α
@[instance] constant zero_ne_one_class.to_has_one (α : Type) [zero_ne_one_class α] : has_one α
class semiring (α : Type)
@[instance] constant semiring.to_add_comm_monoid (α : Type) [semiring α] : add_comm_monoid α
@[instance] constant semiring.to_monoid (α : Type) [semiring α] : monoid α
@[instance] constant semiring.to_distrib (α : Type) [semiring α] : distrib α
@[instance] constant semiring.to_mul_zero_class (α : Type) [semiring α] : mul_zero_class α
class ordered_comm_group (α : Type)
@[instance] constant ordered_comm_group.to_add_comm_group (α : Type) [ordered_comm_group α] : add_comm_group α
@[instance] constant ordered_comm_group.to_partial_order (α : Type) [ordered_comm_group α] : partial_order α
class comm_semiring (α : Type)
@[instance] constant comm_semiring.to_semiring (α : Type) [comm_semiring α] : semiring α
@[instance] constant comm_semiring.to_comm_monoid (α : Type) [comm_semiring α] : comm_monoid α
@[instance] constant comm_semiring_has_dvd (α : Type) [comm_semiring α] : has_dvd α
@[instance] constant ordered_comm_group.to_ordered_cancel_comm_monoid (α : Type) [ordered_comm_group α] : ordered_cancel_comm_monoid α
class ring (α : Type)
@[instance] constant ring.to_add_comm_group (α : Type) [ring α] : add_comm_group α
@[instance] constant ring.to_monoid (α : Type) [ring α] : monoid α
@[instance] constant ring.to_distrib (α : Type) [ring α] : distrib α
@[instance] constant ring.to_semiring (α : Type) [ring α] : semiring α
class comm_ring (α : Type)
@[instance] constant comm_ring.to_ring (α : Type) [comm_ring α] : ring α
@[instance] constant comm_ring.to_comm_semigroup (α : Type) [comm_ring α] : comm_semigroup α
@[instance] constant comm_ring.to_comm_semiring (α : Type) [comm_ring α] : comm_semiring α
class no_zero_divisors (α : Type)
@[instance] constant no_zero_divisors.to_has_mul (α : Type) [no_zero_divisors α] : has_mul α
@[instance] constant no_zero_divisors.to_has_zero (α : Type) [no_zero_divisors α] : has_zero α
class integral_domain (α : Type)
@[instance] constant integral_domain.to_comm_ring (α : Type) [integral_domain α] : comm_ring α
@[instance] constant integral_domain.to_no_zero_divisors (α : Type) [integral_domain α] : no_zero_divisors α
@[instance] constant integral_domain.to_zero_ne_one_class (α : Type) [integral_domain α] : zero_ne_one_class α
class division_ring (α : Type)
@[instance] constant division_ring.to_ring (α : Type) [division_ring α] : ring α
@[instance] constant division_ring.to_has_inv (α : Type) [division_ring α] : has_inv α
@[instance] constant division_ring.to_zero_ne_one_class (α : Type) [division_ring α] : zero_ne_one_class α
@[instance] constant division_ring_has_div (α : Type) [division_ring α] [division_ring α] : has_div α
class decidable_linear_ordered_comm_group (α : Type)
@[instance] constant decidable_linear_ordered_comm_group.to_add_comm_group (α : Type) [decidable_linear_ordered_comm_group α] : add_comm_group α
@[instance] constant decidable_linear_ordered_comm_group.to_decidable_linear_order (α : Type) [decidable_linear_ordered_comm_group α] : decidable_linear_order α
@[instance] constant decidable_linear_ordered_comm_group.to_ordered_comm_group (α : Type) [decidable_linear_ordered_comm_group α] : ordered_comm_group α
class decidable_linear_ordered_cancel_comm_monoid (α : Type)
@[instance] constant decidable_linear_ordered_cancel_comm_monoid.to_ordered_cancel_comm_monoid (α : Type) [decidable_linear_ordered_cancel_comm_monoid α] : ordered_cancel_comm_monoid α
@[instance] constant decidable_linear_ordered_cancel_comm_monoid.to_decidable_linear_order (α : Type) [decidable_linear_ordered_cancel_comm_monoid α] : decidable_linear_order α
class field (α : Type)
@[instance] constant field.to_division_ring (α : Type) [field α] : division_ring α
@[instance] constant field.to_comm_ring (α : Type) [field α] : comm_ring α
class discrete_field (α : Type)
@[instance] constant discrete_field.to_field (α : Type) [discrete_field α] : field α
@[instance] constant discrete_field.to_integral_domain (α : Type) [discrete_field α] [discrete_field α] : integral_domain α
class ordered_semiring (α : Type)
@[instance] constant ordered_semiring.to_semiring (α : Type) [ordered_semiring α] : semiring α
@[instance] constant ordered_semiring.to_ordered_cancel_comm_monoid (α : Type) [ordered_semiring α] : ordered_cancel_comm_monoid α
class linear_ordered_semiring (α : Type)
@[instance] constant linear_ordered_semiring.to_ordered_semiring (α : Type) [linear_ordered_semiring α] : ordered_semiring α
@[instance] constant linear_ordered_semiring.to_linear_order (α : Type) [linear_ordered_semiring α] : linear_order α
class decidable_linear_ordered_semiring (α : Type)
@[instance] constant decidable_linear_ordered_semiring.to_linear_ordered_semiring (α : Type) [decidable_linear_ordered_semiring α] : linear_ordered_semiring α
@[instance] constant decidable_linear_ordered_semiring.to_decidable_linear_order (α : Type) [decidable_linear_ordered_semiring α] : decidable_linear_order α
class ordered_ring (α : Type)
@[instance] constant ordered_ring.to_ring (α : Type) [ordered_ring α] : ring α
@[instance] constant ordered_ring.to_ordered_comm_group (α : Type) [ordered_ring α] : ordered_comm_group α
@[instance] constant ordered_ring.to_zero_ne_one_class (α : Type) [ordered_ring α] : zero_ne_one_class α
@[instance] constant ordered_ring.to_ordered_semiring (α : Type) [ordered_ring α] : ordered_semiring α
class linear_ordered_ring (α : Type)
@[instance] constant linear_ordered_ring.to_ordered_ring (α : Type) [linear_ordered_ring α] : ordered_ring α
@[instance] constant linear_ordered_ring.to_linear_order (α : Type) [linear_ordered_ring α] : linear_order α
@[instance] constant linear_ordered_ring.to_linear_ordered_semiring (α : Type) [linear_ordered_ring α] : linear_ordered_semiring α
class linear_ordered_comm_ring (α : Type)
@[instance] constant linear_ordered_comm_ring.to_linear_ordered_ring (α : Type) [linear_ordered_comm_ring α] : linear_ordered_ring α
@[instance] constant linear_ordered_comm_ring.to_comm_monoid (α : Type) [linear_ordered_comm_ring α] : comm_monoid α
@[instance] constant linear_ordered_comm_ring.to_integral_domain (α : Type) [linear_ordered_comm_ring α] : integral_domain α
class decidable_linear_ordered_comm_ring (α : Type)
@[instance] constant decidable_linear_ordered_comm_ring.to_linear_ordered_comm_ring (α : Type) [decidable_linear_ordered_comm_ring α] : linear_ordered_comm_ring α
@[instance] constant decidable_linear_ordered_comm_ring.to_decidable_linear_ordered_comm_group (α : Type) [decidable_linear_ordered_comm_ring α] : decidable_linear_ordered_comm_group α
@[instance] constant decidable_linear_ordered_comm_ring.to_decidable_linear_ordered_semiring (α : Type) [decidable_linear_ordered_comm_ring α] : decidable_linear_ordered_semiring α
class linear_ordered_field (α : Type)
@[instance] constant linear_ordered_field.to_linear_ordered_ring (α : Type) [linear_ordered_field α] : linear_ordered_ring α
@[instance] constant linear_ordered_field.to_field (α : Type) [linear_ordered_field α] : field α
class discrete_linear_ordered_field (α : Type)
@[instance] constant discrete_linear_ordered_field.to_linear_ordered_field (α : Type) [discrete_linear_ordered_field α] : linear_ordered_field α
@[instance] constant discrete_linear_ordered_field.to_decidable_linear_ordered_comm_ring (α : Type) [discrete_linear_ordered_field α] : decidable_linear_ordered_comm_ring α
@[instance] constant discrete_linear_ordered_field.to_discrete_field (α : Type) [discrete_linear_ordered_field α] : discrete_field α
end test
