namespace test
class decidable (p : Type) := (u:Unit:=())
class has_zero (α : Type) := (u:Unit:=())
class has_one (α : Type) := (u:Unit:=())
class has_add (α : Type) := (u:Unit:=())
class has_mul (α : Type) := (u:Unit:=())
class has_inv (α : Type) := (u:Unit:=())
class has_neg (α : Type) := (u:Unit:=())
class has_sub (α : Type) := (u:Unit:=())
class has_div (α : Type) := (u:Unit:=())
class has_dvd (α : Type) := (u:Unit:=())
class has_mod (α : Type) := (u:Unit:=())
class has_le (α : Type) := (u:Unit:=())
class has_lt (α : Type) := (u:Unit:=())
class has_append (α : Type) := (u:Unit:=())
class has_andthen (α : Type) (β : Type) (σ : Type) := (u:Unit:=())
class has_union (α : Type) := (u:Unit:=())
class has_inter (α : Type) := (u:Unit:=())
class has_sdiff (α : Type) := (u:Unit:=())
class has_equiv (α : Type) := (u:Unit:=())
class has_subset (α : Type) := (u:Unit:=())
class has_ssubset (α : Type) := (u:Unit:=())
class has_emptyc (α : Type) := (u:Unit:=())
class has_insert (α : Type) (γ : Type) := (u:Unit:=())
class has_sep (α : Type) (γ : Type) := (u:Unit:=())
class has_mem (α : Type) (γ : Type) := (u:Unit:=())
class has_pow (α : Type) (β : Type) := (u:Unit:=())
class has_sizeof (α : Type) := (u:Unit:=())
class inhabited (α : Type) := (u:Unit:=())
class nonempty (α : Type) := (u:Unit:=())
@[instance] def nonempty_of_inhabited (α : Type) [_inst_1 : inhabited α] : nonempty α := {}
class subsingleton (α : Type) := (u:Unit:=())
@[instance] def subsingleton_prop (p : Type) : subsingleton p := {}
class setoid (α : Type) := (u:Unit:=())
@[instance] def setoid_has_equiv (α : Type) [_inst_1 : setoid α] : has_equiv α := {}
class has_well_founded (α : Type) := (u:Unit:=())
@[instance] def has_well_founded_of_has_sizeof (α : Type) [_inst_1 : has_sizeof α] : has_well_founded α := {}
class has_lift (a : Type) (b : Type) := (u:Unit:=())
class has_lift_t (a : Type) (b : Type) := (u:Unit:=())
class has_coe (a : Type) (b : Type) := (u:Unit:=())
class has_coe_t (a : Type) (b : Type) := (u:Unit:=())
class has_coe_to_fun (a : Type) := (u:Unit:=())
class has_coe_to_sort (a : Type) := (u:Unit:=())
@[instance] def lift_trans (a : Type) (b : Type) (c : Type) [_inst_1 : has_lift a b] [_inst_2 : has_lift_t b c] : has_lift_t a c := {}
@[instance] def lift_base (a : Type) (b : Type) [_inst_1 : has_lift a b] : has_lift_t a b := {}
@[instance] def coe_trans (a : Type) (b : Type) (c : Type) [_inst_1 : has_coe a b] [_inst_2 : has_coe_t b c] : has_coe_t a c := {}
@[instance] def coe_base (a : Type) (b : Type) [_inst_1 : has_coe a b] : has_coe_t a b := {}
class has_coe_t_aux (a : Type) (b : Type) := (u:Unit:=())
@[instance] def coe_trans_aux (a : Type) (b : Type) (c : Type) [_inst_1 : has_coe a b] [_inst_2 : has_coe_t_aux b c] : has_coe_t_aux a c := {}
@[instance] def coe_base_aux (a : Type) (b : Type) [_inst_1 : has_coe a b] : has_coe_t_aux a b := {}
@[instance] def coe_fn_trans (a : Type) (b : Type) [_inst_1 : has_coe_t_aux a b] [_inst_2 : has_coe_to_fun b] : has_coe_to_fun a := {}
@[instance] def coe_sort_trans (a : Type) (b : Type) [_inst_1 : has_coe_t_aux a b] [_inst_2 : has_coe_to_sort b] : has_coe_to_sort a := {}
@[instance] def coe_to_lift (a : Type) (b : Type) [_inst_1 : has_coe_t a b] : has_lift_t a b := {}
class has_repr (α : Type) := (u:Unit:=())
class has_to_string (α : Type) := (u:Unit:=())
class is_symm_op (α : Type) (β : Type) (op : Type) := (u:Unit:=())
class is_commutative (α : Type) (op : Type) := (u:Unit:=())
@[instance] def is_symm_op_of_is_commutative (α : Type) (op : Type) [_inst_1 : is_commutative α op] : is_symm_op α α op := {}
class is_associative (α : Type) (op : Type) := (u:Unit:=())
class is_left_id (α : Type) (op : Type) (o : Type) := (u:Unit:=())
class is_right_id (α : Type) (op : Type) (o : Type) := (u:Unit:=())
class is_left_null (α : Type) (op : Type) (o : Type) := (u:Unit:=())
class is_right_null (α : Type) (op : Type) (o : Type) := (u:Unit:=())
class is_left_cancel (α : Type) (op : Type) := (u:Unit:=())
class is_right_cancel (α : Type) (op : Type) := (u:Unit:=())
class is_idempotent (α : Type) (op : Type) := (u:Unit:=())
class is_left_distrib (α : Type) (op₁ : Type) (op₂ : Type) := (u:Unit:=())
class is_right_distrib (α : Type) (op₁ : Type) (op₂ : Type) := (u:Unit:=())
class is_left_inv (α : Type) (op : Type) (inv : Type) (o : Type) := (u:Unit:=())
class is_right_inv (α : Type) (op : Type) (inv : Type) (o : Type) := (u:Unit:=())
class is_cond_left_inv (α : Type) (op : Type) (inv : Type) (o : Type) (p : Type) := (u:Unit:=())
class is_cond_right_inv (α : Type) (op : Type) (inv : Type) (o : Type) (p : Type) := (u:Unit:=())
class is_distinct (α : Type) (a : Type) (b : Type) := (u:Unit:=())
class is_irrefl (α : Type) (r : Type) := (u:Unit:=())
class is_refl (α : Type) (r : Type) := (u:Unit:=())
class is_symm (α : Type) (r : Type) := (u:Unit:=())
class is_asymm (α : Type) (r : Type) := (u:Unit:=())
class is_antisymm (α : Type) (r : Type) := (u:Unit:=())
class is_trans (α : Type) (r : Type) := (u:Unit:=())
class is_total (α : Type) (r : Type) := (u:Unit:=())
class is_preorder (α : Type) (r : Type) := (u:Unit:=())
@[instance] def is_preorder.to_is_refl (α : Type) (r : Type) [c : is_preorder α r] : is_refl α r := {}
@[instance] def is_preorder.to_is_trans (α : Type) (r : Type) [c : is_preorder α r] : is_trans α r := {}
class is_total_preorder (α : Type) (r : Type) := (u:Unit:=())
@[instance] def is_total_preorder.to_is_trans (α : Type) (r : Type) [c : is_total_preorder α r] : is_trans α r := {}
@[instance] def is_total_preorder.to_is_total (α : Type) (r : Type) [c : is_total_preorder α r] : is_total α r := {}
@[instance] def is_total_preorder_is_preorder (α : Type) (r : Type) [s : is_total_preorder α r] : is_preorder α r := {}
class is_partial_order (α : Type) (r : Type) := (u:Unit:=())
@[instance] def is_partial_order.to_is_preorder (α : Type) (r : Type) [c : is_partial_order α r] : is_preorder α r := {}
@[instance] def is_partial_order.to_is_antisymm (α : Type) (r : Type) [c : is_partial_order α r] : is_antisymm α r := {}
class has_to_format (α : Type) := (u:Unit:=())
class is_linear_order (α : Type) (r : Type) := (u:Unit:=())
@[instance] def is_linear_order.to_is_partial_order (α : Type) (r : Type) [c : is_linear_order α r] : is_partial_order α r := {}
@[instance] def is_linear_order.to_is_total (α : Type) (r : Type) [c : is_linear_order α r] : is_total α r := {}
class is_equiv (α : Type) (r : Type) := (u:Unit:=())
@[instance] def is_equiv.to_is_preorder (α : Type) (r : Type) [c : is_equiv α r] : is_preorder α r := {}
@[instance] def is_equiv.to_is_symm (α : Type) (r : Type) [c : is_equiv α r] : is_symm α r := {}
class is_per (α : Type) (r : Type) := (u:Unit:=())
@[instance] def is_per.to_is_symm (α : Type) (r : Type) [c : is_per α r] : is_symm α r := {}
@[instance] def is_per.to_is_trans (α : Type) (r : Type) [c : is_per α r] : is_trans α r := {}
class is_strict_order (α : Type) (r : Type) := (u:Unit:=())
@[instance] def is_strict_order.to_is_irrefl (α : Type) (r : Type) [c : is_strict_order α r] : is_irrefl α r := {}
@[instance] def is_strict_order.to_is_trans (α : Type) (r : Type) [c : is_strict_order α r] : is_trans α r := {}
class is_incomp_trans (α : Type) (lt : Type) := (u:Unit:=())
class is_strict_weak_order (α : Type) (lt : Type) := (u:Unit:=())
@[instance] def is_strict_weak_order.to_is_strict_order (α : Type) (lt : Type) [c : is_strict_weak_order α lt] : is_strict_order α lt := {}
@[instance] def is_strict_weak_order.to_is_incomp_trans (α : Type) (lt : Type) [c : is_strict_weak_order α lt] : is_incomp_trans α lt := {}
class is_trichotomous (α : Type) (lt : Type) := (u:Unit:=())
class functor (f : Type) := (u:Unit:=())
class is_strict_total_order (α : Type) (lt : Type) := (u:Unit:=())
@[instance] def is_strict_total_order.to_is_trichotomous (α : Type) (lt : Type) [c : is_strict_total_order α lt] : is_trichotomous α lt := {}
@[instance] def is_strict_total_order.to_is_strict_weak_order (α : Type) (lt : Type) [c : is_strict_total_order α lt] : is_strict_weak_order α lt := {}
@[instance] def is_asymm_of_is_trans_of_is_irrefl (α : Type) (r : Type) [_inst_1 : is_trans α r] [_inst_2 : is_irrefl α r] : is_asymm α r := {}
class has_pure (f : Type) := (u:Unit:=())
class has_seq (f : Type) := (u:Unit:=())
class has_seq_left (f : Type) := (u:Unit:=())
class has_seq_right (f : Type) := (u:Unit:=())
class applicative (f : Type) := (u:Unit:=())
@[instance] def applicative.to_functor (f : Type) [c : applicative f] : functor f := {}
@[instance] def applicative.to_has_pure (f : Type) [c : applicative f] : has_pure f := {}
@[instance] def applicative.to_has_seq (f : Type) [c : applicative f] : has_seq f := {}
@[instance] def applicative.to_has_seq_left (f : Type) [c : applicative f] : has_seq_left f := {}
@[instance] def applicative.to_has_seq_right (f : Type) [c : applicative f] : has_seq_right f := {}
class preorder (α : Type) := (u:Unit:=())
@[instance] def preorder.to_has_le (α : Type) [s : preorder α] : has_le α := {}
@[instance] def preorder.to_has_lt (α : Type) [s : preorder α] : has_lt α := {}
class has_bind (m : Type) := (u:Unit:=())
class monad (m : Type) := (u:Unit:=())
@[instance] def monad.to_applicative (m : Type) [c : monad m] : applicative m := {}
@[instance] def monad.to_has_bind (m : Type) [c : monad m] : has_bind m := {}
class partial_order (α : Type) := (u:Unit:=())
@[instance] def partial_order.to_preorder (α : Type) [s : partial_order α] : preorder α := {}
class has_orelse (f : Type) := (u:Unit:=())
class alternative (f : Type) := (u:Unit:=())
@[instance] def alternative.to_applicative (f : Type) [c : alternative f] : applicative f := {}
@[instance] def alternative.to_has_orelse (f : Type) [c : alternative f] : has_orelse f := {}
class has_monad_lift (m : Type) (n : Type) := (u:Unit:=())
class linear_order (α : Type) := (u:Unit:=())
@[instance] def linear_order.to_partial_order (α : Type) [s : linear_order α] : partial_order α := {}
class has_monad_lift_t (m : Type) (n : Type) := (u:Unit:=())
@[instance] def has_monad_lift_t_trans (m : Type) (n : Type) (o : Type) [_inst_1 : has_monad_lift n o] [_inst_2 : has_monad_lift_t m n] : has_monad_lift_t m o := {}
@[instance] def has_monad_lift_t_refl (m : Type) : has_monad_lift_t m m := {}
class monad_functor (m : Type) (m' : Type) (n : Type) (n' : Type) := (u:Unit:=())
class monad_functor_t (m : Type) (m' : Type) (n : Type) (n' : Type) := (u:Unit:=())
@[instance] def monad_functor_t_trans (m : Type) (m' : Type) (n : Type) (n' : Type) (o : Type) (o' : Type) [_inst_1 : monad_functor n n' o o'] [_inst_2 : monad_functor_t m m' n n'] : monad_functor_t m m' o o' := {}
@[instance] def monad_functor_t_refl (m : Type) (m' : Type) : monad_functor_t m m' m m' := {}
class monad_run (out : Type) (m : Type) := (u:Unit:=())
class monad_fail (m : Type) := (u:Unit:=())
@[instance] def monad_fail_lift (m : Type) (n : Type) [_inst_1 : has_monad_lift m n] [_inst_2 : monad_fail m] [_inst_3 : monad n] : monad_fail n := {}
class decidable_linear_order (α : Type) := (u:Unit:=())
@[instance] def decidable_linear_order.to_linear_order (α : Type) [s : decidable_linear_order α] : linear_order α := {}
class monad_except (ε : Type) (m : Type) := (u:Unit:=())
class monad_except_adapter (ε : Type) (ε' : Type) (m : Type) (m' : Type) := (u:Unit:=())
@[instance] def monad_except_adapter_trans (ε : Type) (ε' : Type) (m : Type) (m' : Type) (n : Type) (n' : Type) [_inst_1 : monad_functor m m' n n'] [_inst_2 : monad_except_adapter ε ε' m m'] : monad_except_adapter ε ε' n n' := {}
class monad_reader (ρ : Type) (m : Type) := (u:Unit:=())
@[instance] def monad_reader_trans (ρ : Type) (m : Type) (n : Type) [_inst_1 : has_monad_lift m n] [_inst_2 : monad_reader ρ m] : monad_reader ρ n := {}
class monad_reader_adapter (ρ : Type) (ρ' : Type) (m : Type) (m' : Type) := (u:Unit:=())
@[instance] def monad_reader_adapter_trans (ρ : Type) (ρ' : Type) (m : Type) (m' : Type) (n : Type) (n' : Type) [_inst_1 : monad_functor m m' n n'] [_inst_2 : monad_reader_adapter ρ ρ' m m'] : monad_reader_adapter ρ ρ' n n' := {}
class monad_state (σ : Type) (m : Type) := (u:Unit:=())
@[instance] def monad_state_trans (σ : Type) (m : Type) (n : Type) [_inst_1 : has_monad_lift m n] [_inst_2 : monad_state σ m] : monad_state σ n := {}
class monad_state_adapter (σ : Type) (σ' : Type) (m : Type) (m' : Type) := (u:Unit:=())
@[instance] def monad_state_adapter_trans (σ : Type) (σ' : Type) (m : Type) (m' : Type) (n : Type) (n' : Type) [_inst_1 : monad_functor m m' n n'] [_inst_2 : monad_state_adapter σ σ' m m'] : monad_state_adapter σ σ' n n' := {}
class has_to_pexpr (α : Type) := (u:Unit:=())
class has_to_tactic_format (α : Type) := (u:Unit:=())
@[instance] def has_to_format_to_has_to_tactic_format (α : Type) [_inst_1 : has_to_format α] : has_to_tactic_format α := {}
class is_lawful_functor (f : Type) [_inst_1 : functor f] := (u:Unit:=())
class is_lawful_applicative (f : Type) [_inst_1 : applicative f] := (u:Unit:=())
@[instance] def is_lawful_applicative.to_is_lawful_functor (f : Type) [_inst_1 : applicative f] [c : @is_lawful_applicative f _inst_1] : @is_lawful_functor f (@applicative.to_functor f _inst_1) := {}
class is_lawful_monad (m : Type) [_inst_1 : monad m] := (u:Unit:=())
@[instance] def is_lawful_monad.to_is_lawful_applicative (m : Type) [_inst_1 : monad m] [c : @is_lawful_monad m _inst_1] : @is_lawful_applicative m (@monad.to_applicative m _inst_1) := {}
class semigroup (α : Type) := (u:Unit:=())
@[instance] def semigroup.to_has_mul (α : Type) [s : semigroup α] : has_mul α := {}
class comm_semigroup (α : Type) := (u:Unit:=())
@[instance] def comm_semigroup.to_semigroup (α : Type) [s : comm_semigroup α] : semigroup α := {}
class left_cancel_semigroup (α : Type) := (u:Unit:=())
@[instance] def left_cancel_semigroup.to_semigroup (α : Type) [s : left_cancel_semigroup α] : semigroup α := {}
class right_cancel_semigroup (α : Type) := (u:Unit:=())
@[instance] def right_cancel_semigroup.to_semigroup (α : Type) [s : right_cancel_semigroup α] : semigroup α := {}
class monoid (α : Type) := (u:Unit:=())
@[instance] def monoid.to_semigroup (α : Type) [s : monoid α] : semigroup α := {}
@[instance] def monoid.to_has_one (α : Type) [s : monoid α] : has_one α := {}
class comm_monoid (α : Type) := (u:Unit:=())
@[instance] def comm_monoid.to_monoid (α : Type) [s : comm_monoid α] : monoid α := {}
@[instance] def comm_monoid.to_comm_semigroup (α : Type) [s : comm_monoid α] : comm_semigroup α := {}
class group (α : Type) := (u:Unit:=())
@[instance] def group.to_monoid (α : Type) [s : group α] : monoid α := {}
@[instance] def group.to_has_inv (α : Type) [s : group α] : has_inv α := {}
class comm_group (α : Type) := (u:Unit:=())
@[instance] def comm_group.to_group (α : Type) [s : comm_group α] : group α := {}
@[instance] def comm_group.to_comm_monoid (α : Type) [s : comm_group α] : comm_monoid α := {}
@[instance] def group.to_left_cancel_semigroup (α : Type) [s : group α] : left_cancel_semigroup α := {}
@[instance] def group.to_right_cancel_semigroup (α : Type) [s : group α] : right_cancel_semigroup α := {}
class add_semigroup (α : Type) := (u:Unit:=())
@[instance] def add_semigroup.to_has_add (α : Type) [s : add_semigroup α] : has_add α := {}
class add_comm_semigroup (α : Type) := (u:Unit:=())
@[instance] def add_comm_semigroup.to_add_semigroup (α : Type) [s : add_comm_semigroup α] : add_semigroup α := {}
class add_left_cancel_semigroup (α : Type) := (u:Unit:=())
@[instance] def add_left_cancel_semigroup.to_add_semigroup (α : Type) [s : add_left_cancel_semigroup α] : add_semigroup α := {}
class add_right_cancel_semigroup (α : Type) := (u:Unit:=())
@[instance] def add_right_cancel_semigroup.to_add_semigroup (α : Type) [s : add_right_cancel_semigroup α] : add_semigroup α := {}
class add_monoid (α : Type) := (u:Unit:=())
@[instance] def add_monoid.to_add_semigroup (α : Type) [s : add_monoid α] : add_semigroup α := {}
@[instance] def add_monoid.to_has_zero (α : Type) [s : add_monoid α] : has_zero α := {}
class add_comm_monoid (α : Type) := (u:Unit:=())
@[instance] def add_comm_monoid.to_add_monoid (α : Type) [s : add_comm_monoid α] : add_monoid α := {}
@[instance] def add_comm_monoid.to_add_comm_semigroup (α : Type) [s : add_comm_monoid α] : add_comm_semigroup α := {}
class add_group (α : Type) := (u:Unit:=())
@[instance] def add_group.to_add_monoid (α : Type) [s : add_group α] : add_monoid α := {}
@[instance] def add_group.to_has_neg (α : Type) [s : add_group α] : has_neg α := {}
class add_comm_group (α : Type) := (u:Unit:=())
@[instance] def add_comm_group.to_add_group (α : Type) [s : add_comm_group α] : add_group α := {}
@[instance] def add_comm_group.to_add_comm_monoid (α : Type) [s : add_comm_group α] : add_comm_monoid α := {}
@[instance] def add_group.to_left_cancel_add_semigroup (α : Type) [s : add_group α] : add_left_cancel_semigroup α := {}
@[instance] def add_group.to_right_cancel_add_semigroup (α : Type) [s : add_group α] : add_right_cancel_semigroup α := {}
@[instance] def add_group_has_sub (α : Type) [_inst_1 : add_group α] : has_sub α := {}
class distrib (α : Type) := (u:Unit:=())
@[instance] def distrib.to_has_mul (α : Type) [s : distrib α] : has_mul α := {}
@[instance] def distrib.to_has_add (α : Type) [s : distrib α] : has_add α := {}
class mul_zero_class (α : Type) := (u:Unit:=())
@[instance] def mul_zero_class.to_has_mul (α : Type) [s : mul_zero_class α] : has_mul α := {}
@[instance] def mul_zero_class.to_has_zero (α : Type) [s : mul_zero_class α] : has_zero α := {}
class zero_ne_one_class (α : Type) := (u:Unit:=())
@[instance] def zero_ne_one_class.to_has_zero (α : Type) [s : zero_ne_one_class α] : has_zero α := {}
@[instance] def zero_ne_one_class.to_has_one (α : Type) [s : zero_ne_one_class α] : has_one α := {}
class ordered_cancel_comm_monoid (α : Type) := (u:Unit:=())
@[instance] def ordered_cancel_comm_monoid.to_add_comm_monoid (α : Type) [s : ordered_cancel_comm_monoid α] : add_comm_monoid α := {}
@[instance] def ordered_cancel_comm_monoid.to_add_left_cancel_semigroup (α : Type) [s : ordered_cancel_comm_monoid α] : add_left_cancel_semigroup α := {}
@[instance] def ordered_cancel_comm_monoid.to_add_right_cancel_semigroup (α : Type) [s : ordered_cancel_comm_monoid α] : add_right_cancel_semigroup α := {}
@[instance] def ordered_cancel_comm_monoid.to_partial_order (α : Type) [s : ordered_cancel_comm_monoid α] : partial_order α := {}
class semiring (α : Type) := (u:Unit:=())
@[instance] def semiring.to_add_comm_monoid (α : Type) [s : semiring α] : add_comm_monoid α := {}
@[instance] def semiring.to_monoid (α : Type) [s : semiring α] : monoid α := {}
@[instance] def semiring.to_distrib (α : Type) [s : semiring α] : distrib α := {}
@[instance] def semiring.to_mul_zero_class (α : Type) [s : semiring α] : mul_zero_class α := {}
class comm_semiring (α : Type) := (u:Unit:=())
@[instance] def comm_semiring.to_semiring (α : Type) [s : comm_semiring α] : semiring α := {}
@[instance] def comm_semiring.to_comm_monoid (α : Type) [s : comm_semiring α] : comm_monoid α := {}
@[instance] def comm_semiring_has_dvd (α : Type) [_inst_1 : comm_semiring α] : has_dvd α := {}
class ordered_comm_group (α : Type) := (u:Unit:=())
@[instance] def ordered_comm_group.to_add_comm_group (α : Type) [s : ordered_comm_group α] : add_comm_group α := {}
@[instance] def ordered_comm_group.to_partial_order (α : Type) [s : ordered_comm_group α] : partial_order α := {}
@[instance] def ordered_comm_group.to_ordered_cancel_comm_monoid (α : Type) [s : ordered_comm_group α] : ordered_cancel_comm_monoid α := {}
class ring (α : Type) := (u:Unit:=())
@[instance] def ring.to_add_comm_group (α : Type) [s : ring α] : add_comm_group α := {}
@[instance] def ring.to_monoid (α : Type) [s : ring α] : monoid α := {}
@[instance] def ring.to_distrib (α : Type) [s : ring α] : distrib α := {}
@[instance] def ring.to_semiring (α : Type) [s : ring α] : semiring α := {}
class comm_ring (α : Type) := (u:Unit:=())
@[instance] def comm_ring.to_ring (α : Type) [s : comm_ring α] : ring α := {}
@[instance] def comm_ring.to_comm_semigroup (α : Type) [s : comm_ring α] : comm_semigroup α := {}
@[instance] def comm_ring.to_comm_semiring (α : Type) [s : comm_ring α] : comm_semiring α := {}
class no_zero_divisors (α : Type) := (u:Unit:=())
@[instance] def no_zero_divisors.to_has_mul (α : Type) [s : no_zero_divisors α] : has_mul α := {}
@[instance] def no_zero_divisors.to_has_zero (α : Type) [s : no_zero_divisors α] : has_zero α := {}
class integral_domain (α : Type) := (u:Unit:=())
@[instance] def integral_domain.to_comm_ring (α : Type) [s : integral_domain α] : comm_ring α := {}
@[instance] def integral_domain.to_no_zero_divisors (α : Type) [s : integral_domain α] : no_zero_divisors α := {}
@[instance] def integral_domain.to_zero_ne_one_class (α : Type) [s : integral_domain α] : zero_ne_one_class α := {}
class division_ring (α : Type) := (u:Unit:=())
@[instance] def division_ring.to_ring (α : Type) [s : division_ring α] : ring α := {}
@[instance] def division_ring.to_has_inv (α : Type) [s : division_ring α] : has_inv α := {}
@[instance] def division_ring.to_zero_ne_one_class (α : Type) [s : division_ring α] : zero_ne_one_class α := {}
@[instance] def division_ring_has_div (α : Type) [_inst_1 : division_ring α] [_inst_2 : division_ring α] : has_div α := {}
class decidable_linear_ordered_comm_group (α : Type) := (u:Unit:=())
@[instance] def decidable_linear_ordered_comm_group.to_add_comm_group (α : Type) [s : decidable_linear_ordered_comm_group α] : add_comm_group α := {}
@[instance] def decidable_linear_ordered_comm_group.to_decidable_linear_order (α : Type) [s : decidable_linear_ordered_comm_group α] : decidable_linear_order α := {}
@[instance] def decidable_linear_ordered_comm_group.to_ordered_comm_group (α : Type) [s : decidable_linear_ordered_comm_group α] : ordered_comm_group α := {}
class decidable_linear_ordered_cancel_comm_monoid (α : Type) := (u:Unit:=())
@[instance] def decidable_linear_ordered_cancel_comm_monoid.to_ordered_cancel_comm_monoid (α : Type) [s : decidable_linear_ordered_cancel_comm_monoid α] : ordered_cancel_comm_monoid α := {}
@[instance] def decidable_linear_ordered_cancel_comm_monoid.to_decidable_linear_order (α : Type) [s : decidable_linear_ordered_cancel_comm_monoid α] : decidable_linear_order α := {}
class field (α : Type) := (u:Unit:=())
@[instance] def field.to_division_ring (α : Type) [s : field α] : division_ring α := {}
@[instance] def field.to_comm_ring (α : Type) [s : field α] : comm_ring α := {}
class discrete_field (α : Type) := (u:Unit:=())
@[instance] def discrete_field.to_field (α : Type) [s : discrete_field α] : field α := {}
@[instance] def discrete_field.to_integral_domain (α : Type) [_inst_1 : discrete_field α] [s : discrete_field α] : integral_domain α := {}
class ordered_semiring (α : Type) := (u:Unit:=())
@[instance] def ordered_semiring.to_semiring (α : Type) [s : ordered_semiring α] : semiring α := {}
@[instance] def ordered_semiring.to_ordered_cancel_comm_monoid (α : Type) [s : ordered_semiring α] : ordered_cancel_comm_monoid α := {}
class linear_ordered_semiring (α : Type) := (u:Unit:=())
@[instance] def linear_ordered_semiring.to_ordered_semiring (α : Type) [s : linear_ordered_semiring α] : ordered_semiring α := {}
@[instance] def linear_ordered_semiring.to_linear_order (α : Type) [s : linear_ordered_semiring α] : linear_order α := {}
class decidable_linear_ordered_semiring (α : Type) := (u:Unit:=())
@[instance] def decidable_linear_ordered_semiring.to_linear_ordered_semiring (α : Type) [s : decidable_linear_ordered_semiring α] : linear_ordered_semiring α := {}
@[instance] def decidable_linear_ordered_semiring.to_decidable_linear_order (α : Type) [s : decidable_linear_ordered_semiring α] : decidable_linear_order α := {}
class ordered_ring (α : Type) := (u:Unit:=())
@[instance] def ordered_ring.to_ring (α : Type) [s : ordered_ring α] : ring α := {}
@[instance] def ordered_ring.to_ordered_comm_group (α : Type) [s : ordered_ring α] : ordered_comm_group α := {}
@[instance] def ordered_ring.to_zero_ne_one_class (α : Type) [s : ordered_ring α] : zero_ne_one_class α := {}
@[instance] def ordered_ring.to_ordered_semiring (α : Type) [s : ordered_ring α] : ordered_semiring α := {}
class linear_ordered_ring (α : Type) := (u:Unit:=())
@[instance] def linear_ordered_ring.to_ordered_ring (α : Type) [s : linear_ordered_ring α] : ordered_ring α := {}
@[instance] def linear_ordered_ring.to_linear_order (α : Type) [s : linear_ordered_ring α] : linear_order α := {}
@[instance] def linear_ordered_ring.to_linear_ordered_semiring (α : Type) [s : linear_ordered_ring α] : linear_ordered_semiring α := {}
class linear_ordered_comm_ring (α : Type) := (u:Unit:=())
@[instance] def linear_ordered_comm_ring.to_linear_ordered_ring (α : Type) [s : linear_ordered_comm_ring α] : linear_ordered_ring α := {}
@[instance] def linear_ordered_comm_ring.to_comm_monoid (α : Type) [s : linear_ordered_comm_ring α] : comm_monoid α := {}
@[instance] def linear_ordered_comm_ring.to_integral_domain (α : Type) [s : linear_ordered_comm_ring α] : integral_domain α := {}
class decidable_linear_ordered_comm_ring (α : Type) := (u:Unit:=())
@[instance] def decidable_linear_ordered_comm_ring.to_linear_ordered_comm_ring (α : Type) [s : decidable_linear_ordered_comm_ring α] : linear_ordered_comm_ring α := {}
@[instance] def decidable_linear_ordered_comm_ring.to_decidable_linear_ordered_comm_group (α : Type) [s : decidable_linear_ordered_comm_ring α] : decidable_linear_ordered_comm_group α := {}
@[instance] def decidable_linear_ordered_comm_ring.to_decidable_linear_ordered_semiring (α : Type) [d : decidable_linear_ordered_comm_ring α] : decidable_linear_ordered_semiring α := {}
class linear_ordered_field (α : Type) := (u:Unit:=())
@[instance] def linear_ordered_field.to_linear_ordered_ring (α : Type) [s : linear_ordered_field α] : linear_ordered_ring α := {}
@[instance] def linear_ordered_field.to_field (α : Type) [s : linear_ordered_field α] : field α := {}
class discrete_linear_ordered_field (α : Type) := (u:Unit:=())
@[instance] def discrete_linear_ordered_field.to_linear_ordered_field (α : Type) [s : discrete_linear_ordered_field α] : linear_ordered_field α := {}
@[instance] def discrete_linear_ordered_field.to_decidable_linear_ordered_comm_ring (α : Type) [s : discrete_linear_ordered_field α] : decidable_linear_ordered_comm_ring α := {}
@[instance] def discrete_linear_ordered_field.to_discrete_field (α : Type) [s : discrete_linear_ordered_field α] : discrete_field α := {}
class unique (α : Type) := (u:Unit:=())
class relator.right_total (α : Type) (β : Type) (R : Type) := (u:Unit:=())
class relator.left_total (α : Type) (β : Type) (R : Type) := (u:Unit:=())
class relator.bi_total (α : Type) (β : Type) (R : Type) := (u:Unit:=())
@[instance] def unique.inhabited (α : Type) [_inst_1 : unique α] : inhabited α := {}
@[instance] def unique.subsingleton (α : Type) [_inst_1 : unique α] : subsingleton α := {}
class relator.left_unique (α : Type) (β : Type) (R : Type) := (u:Unit:=())
class relator.right_unique (α : Type) (β : Type) (R : Type) := (u:Unit:=())
class is_comm_applicative (m : Type) [_inst_1 : applicative m] := (u:Unit:=())
@[instance] def is_comm_applicative.to_is_lawful_applicative (m : Type) [_inst_1 : applicative m] [c : @is_comm_applicative m _inst_1] : @is_lawful_applicative m _inst_1 := {}
class can_lift (α : Type) (β : Type) := (u:Unit:=())
class traversable (t : Type) := (u:Unit:=())
@[instance] def traversable.to_functor (t : Type) [c : traversable t] : functor t := {}
class is_lawful_traversable (t : Type) [_inst_1 : traversable t] := (u:Unit:=())
@[instance] def is_lawful_traversable.to_is_lawful_functor (t : Type) [_inst_1 : traversable t] [c : @is_lawful_traversable t _inst_1] : @is_lawful_functor t (@traversable.to_functor t _inst_1) := {}
class category_theory.has_hom (obj : Type) := (u:Unit:=())
class eckmann_hilton.is_unital (X : Type) (m : Type) (e : Type) := (u:Unit:=())
class category_theory.category_struct (obj : Type) := (u:Unit:=())
@[instance] def category_theory.category_struct.to_has_hom (obj : Type) [c : category_theory.category_struct obj] : category_theory.has_hom obj := {}
class bifunctor (F : Type) := (u:Unit:=())
class is_lawful_bifunctor (F : Type) [_inst_1 : bifunctor F] := (u:Unit:=())
class category_theory.category (obj : Type) := (u:Unit:=())
@[instance] def category_theory.category.to_category_struct (obj : Type) [c : category_theory.category obj] : category_theory.category_struct obj := {}
class category_theory.epi (C : Type) [𝒞 : category_theory.category C] (X : Type) (Y : Type) (f : Type) := (u:Unit:=())
class category_theory.mono (C : Type) [𝒞 : category_theory.category C] (X : Type) (Y : Type) (f : Type) := (u:Unit:=())
@[instance] def preorder.small_category (α : Type) [_inst_1 : preorder α] : category_theory.category α := {}
class computation.terminates (α : Type) (s : Type) := (u:Unit:=())
class monad_writer (ω : Type) (m : Type) := (u:Unit:=())
class monad_writer_adapter (ω : Type) (ω' : Type) (m : Type) (m' : Type) := (u:Unit:=())
class bitraversable (t : Type) := (u:Unit:=())
@[instance] def bitraversable.to_bifunctor (t : Type) [c : bitraversable t] : bifunctor t := {}
@[instance] def monad_writer_adapter_trans (ω : Type) (ω' : Type) (m : Type) (m' : Type) (n : Type) (n' : Type) [_inst_1 : monad_functor m m' n n'] [_inst_2 : monad_writer_adapter ω ω' m m'] : monad_writer_adapter ω ω' n n' := {}
class is_lawful_bitraversable (t : Type) [_inst_1 : bitraversable t] := (u:Unit:=())
@[instance] def is_lawful_bitraversable.to_is_lawful_bifunctor (t : Type) [_inst_1 : bitraversable t] [c : @is_lawful_bitraversable t _inst_1] : @is_lawful_bifunctor t (@bitraversable.to_bifunctor t _inst_1) := {}
class monad_cont (m : Type) := (u:Unit:=())
class is_lawful_monad_cont (m : Type) [_inst_1 : monad m] [_inst_2 : monad_cont m] := (u:Unit:=())
@[instance] def is_lawful_monad_cont.to_is_lawful_monad (m : Type) [_inst_1 : monad m] [_inst_2 : monad_cont m] [c : @is_lawful_monad_cont m _inst_1 _inst_2] : @is_lawful_monad m _inst_1 := {}
class category_theory.is_iso (C : Type) [𝒞 : category_theory.category C] (X : Type) (Y : Type) (f : Type) := (u:Unit:=())
@[instance] def category_theory.is_iso.epi_of_iso (C : Type) [𝒞 : category_theory.category C] (X : Type) (Y : Type) (f : Type) [_inst_1 : @category_theory.is_iso C 𝒞 X Y f] : @category_theory.epi C 𝒞 X Y f := {}
@[instance] def category_theory.is_iso.mono_of_iso (C : Type) [𝒞 : category_theory.category C] (X : Type) (Y : Type) (f : Type) [_inst_1 : @category_theory.is_iso C 𝒞 X Y f] : @category_theory.mono C 𝒞 X Y f := {}
class category_theory.full (C : Type) [𝒞 : category_theory.category C] (D : Type) [𝒟 : category_theory.category D] (F : Type) := (u:Unit:=())
class category_theory.faithful (C : Type) [𝒞 : category_theory.category C] (D : Type) [𝒟 : category_theory.category D] (F : Type) := (u:Unit:=())
class category_theory.monad (C : Type) [𝒞 : category_theory.category C] (T : Type) := (u:Unit:=())
class pSet.definable (n : Type) (a : Type) := (u:Unit:=())
class is_group_anti_hom (α : Type) (β : Type) [_inst_1 : group α] [_inst_2 : group β] (f : Type) := (u:Unit:=())
class is_add_hom (α : Type) (β : Type) [_inst_1 : has_add α] [_inst_2 : has_add β] (f : Type) := (u:Unit:=())
class is_mul_hom (α : Type) (β : Type) [_inst_1 : has_mul α] [_inst_2 : has_mul β] (f : Type) := (u:Unit:=())
class no_top_order (α : Type) [_inst_1 : preorder α] := (u:Unit:=())
class no_bot_order (α : Type) [_inst_1 : preorder α] := (u:Unit:=())
class densely_ordered (α : Type) [_inst_1 : preorder α] := (u:Unit:=())
class is_add_monoid_hom (α : Type) (β : Type) [_inst_1 : add_monoid α] [_inst_2 : add_monoid β] (f : Type) := (u:Unit:=())
@[instance] def is_add_monoid_hom.to_is_add_hom (α : Type) (β : Type) [_inst_1 : add_monoid α] [_inst_2 : add_monoid β] (f : Type) [c : @is_add_monoid_hom α β _inst_1 _inst_2 f] : @is_add_hom α β (@add_semigroup.to_has_add α (@add_monoid.to_add_semigroup α _inst_1)) (@add_semigroup.to_has_add β (@add_monoid.to_add_semigroup β _inst_2)) f := {}
class is_monoid_hom (α : Type) (β : Type) [_inst_1 : monoid α] [_inst_2 : monoid β] (f : Type) := (u:Unit:=())
class is_strict_total_order' (α : Type) (lt : Type) := (u:Unit:=())
@[instance] def is_strict_total_order'.to_is_trichotomous (α : Type) (lt : Type) [c : is_strict_total_order' α lt] : is_trichotomous α lt := {}
@[instance] def is_strict_total_order'.to_is_strict_order (α : Type) (lt : Type) [c : is_strict_total_order' α lt] : is_strict_order α lt := {}
@[instance] def is_monoid_hom.to_is_mul_hom (α : Type) (β : Type) [_inst_1 : monoid α] [_inst_2 : monoid β] (f : Type) [c : @is_monoid_hom α β _inst_1 _inst_2 f] : @is_mul_hom α β (@semigroup.to_has_mul α (@monoid.to_semigroup α _inst_1)) (@semigroup.to_has_mul β (@monoid.to_semigroup β _inst_2)) f := {}
class is_order_connected (α : Type) (lt : Type) := (u:Unit:=())
@[instance] def is_order_connected_of_is_strict_total_order' (α : Type) (r : Type) [_inst_1 : is_strict_total_order' α r] : is_order_connected α r := {}
@[instance] def is_strict_total_order_of_is_strict_total_order' (α : Type) (r : Type) [_inst_1 : is_strict_total_order' α r] : is_strict_total_order α r := {}
class is_extensional (α : Type) (r : Type) := (u:Unit:=())
@[instance] def is_extensional_of_is_strict_total_order' (α : Type) (r : Type) [_inst_1 : is_strict_total_order' α r] : is_extensional α r := {}
class is_well_order (α : Type) (r : Type) := (u:Unit:=())
@[instance] def is_well_order.to_is_strict_total_order' (α : Type) (r : Type) [c : is_well_order α r] : is_strict_total_order' α r := {}
@[instance] def is_well_order.is_strict_total_order (α : Type) (r : Type) [_inst_1 : is_well_order α r] : is_strict_total_order α r := {}
@[instance] def is_well_order.is_extensional (α : Type) (r : Type) [_inst_1 : is_well_order α r] : is_extensional α r := {}
@[instance] def is_well_order.is_trichotomous (α : Type) (r : Type) [_inst_1 : is_well_order α r] : is_trichotomous α r := {}
@[instance] def is_well_order.is_trans (α : Type) (r : Type) [_inst_1 : is_well_order α r] : is_trans α r := {}
@[instance] def is_well_order.is_irrefl (α : Type) (r : Type) [_inst_1 : is_well_order α r] : is_irrefl α r := {}
@[instance] def is_well_order.is_asymm (α : Type) (r : Type) [_inst_1 : is_well_order α r] : is_asymm α r := {}
class is_add_group_hom (α : Type) (β : Type) [_inst_1 : add_group α] [_inst_2 : add_group β] (f : Type) := (u:Unit:=())
@[instance] def is_add_group_hom.to_is_add_hom (α : Type) (β : Type) [_inst_1 : add_group α] [_inst_2 : add_group β] (f : Type) [c : @is_add_group_hom α β _inst_1 _inst_2 f] : @is_add_hom α β (@add_semigroup.to_has_add α (@add_monoid.to_add_semigroup α (@add_group.to_add_monoid α _inst_1))) (@add_semigroup.to_has_add β (@add_monoid.to_add_semigroup β (@add_group.to_add_monoid β _inst_2))) f := {}
class is_group_hom (α : Type) (β : Type) [_inst_1 : group α] [_inst_2 : group β] (f : Type) := (u:Unit:=())
@[instance] def is_group_hom.to_is_mul_hom (α : Type) (β : Type) [_inst_1 : group α] [_inst_2 : group β] (f : Type) [c : @is_group_hom α β _inst_1 _inst_2 f] : @is_mul_hom α β (@semigroup.to_has_mul α (@monoid.to_semigroup α (@group.to_monoid α _inst_1))) (@semigroup.to_has_mul β (@monoid.to_semigroup β (@group.to_monoid β _inst_2))) f := {}
@[instance] def is_group_hom.to_is_monoid_hom (α : Type) (β : Type) [_inst_1 : group α] [_inst_2 : group β] (f : Type) [_inst_3 : @is_group_hom α β _inst_1 _inst_2 f] : @is_monoid_hom α β (@group.to_monoid α _inst_1) (@group.to_monoid β _inst_2) f := {}
@[instance] def is_add_group_hom.to_is_add_monoid_hom (α : Type) (β : Type) [_inst_1 : add_group α] [_inst_2 : add_group β] (f : Type) [_inst_3 : @is_add_group_hom α β _inst_1 _inst_2 f] : @is_add_monoid_hom α β (@add_group.to_add_monoid α _inst_1) (@add_group.to_add_monoid β _inst_2) f := {}
class directed_order (α : Type) := (u:Unit:=())
@[instance] def directed_order.to_preorder (α : Type) [c : directed_order α] : preorder α := {}
class lattice.has_sup (α : Type) := (u:Unit:=())
class lattice.has_inf (α : Type) := (u:Unit:=())
class lattice.semilattice_sup (α : Type) := (u:Unit:=())
@[instance] def lattice.semilattice_sup.to_has_sup (α : Type) [s : lattice.semilattice_sup α] : lattice.has_sup α := {}
@[instance] def lattice.semilattice_sup.to_partial_order (α : Type) [s : lattice.semilattice_sup α] : partial_order α := {}
class lattice.semilattice_inf (α : Type) := (u:Unit:=())
@[instance] def lattice.semilattice_inf.to_has_inf (α : Type) [s : lattice.semilattice_inf α] : lattice.has_inf α := {}
@[instance] def lattice.semilattice_inf.to_partial_order (α : Type) [s : lattice.semilattice_inf α] : partial_order α := {}
class lattice.lattice (α : Type) := (u:Unit:=())
@[instance] def lattice.lattice.to_semilattice_sup (α : Type) [s : lattice.lattice α] : lattice.semilattice_sup α := {}
@[instance] def lattice.lattice.to_semilattice_inf (α : Type) [s : lattice.lattice α] : lattice.semilattice_inf α := {}
class lattice.distrib_lattice (α : Type) := (u:Unit:=())
@[instance] def lattice.distrib_lattice.to_lattice (α : Type) [s : lattice.distrib_lattice α] : lattice.lattice α := {}
@[instance] def lattice.lattice_of_decidable_linear_order (α : Type) [o : decidable_linear_order α] : lattice.lattice α := {}
@[instance] def lattice.distrib_lattice_of_decidable_linear_order (α : Type) [o : decidable_linear_order α] : lattice.distrib_lattice α := {}
class lattice.has_top (α : Type) := (u:Unit:=())
class lattice.has_bot (α : Type) := (u:Unit:=())
class lattice.order_top (α : Type) := (u:Unit:=())
@[instance] def lattice.order_top.to_has_top (α : Type) [s : lattice.order_top α] : lattice.has_top α := {}
@[instance] def lattice.order_top.to_partial_order (α : Type) [s : lattice.order_top α] : partial_order α := {}
class lattice.order_bot (α : Type) := (u:Unit:=())
@[instance] def lattice.order_bot.to_has_bot (α : Type) [s : lattice.order_bot α] : lattice.has_bot α := {}
@[instance] def lattice.order_bot.to_partial_order (α : Type) [s : lattice.order_bot α] : partial_order α := {}
class lattice.semilattice_sup_top (α : Type) := (u:Unit:=())
@[instance] def lattice.semilattice_sup_top.to_order_top (α : Type) [s : lattice.semilattice_sup_top α] : lattice.order_top α := {}
@[instance] def lattice.semilattice_sup_top.to_semilattice_sup (α : Type) [s : lattice.semilattice_sup_top α] : lattice.semilattice_sup α := {}
class lattice.semilattice_sup_bot (α : Type) := (u:Unit:=())
@[instance] def lattice.semilattice_sup_bot.to_order_bot (α : Type) [s : lattice.semilattice_sup_bot α] : lattice.order_bot α := {}
@[instance] def lattice.semilattice_sup_bot.to_semilattice_sup (α : Type) [s : lattice.semilattice_sup_bot α] : lattice.semilattice_sup α := {}
class lattice.semilattice_inf_top (α : Type) := (u:Unit:=())
@[instance] def lattice.semilattice_inf_top.to_order_top (α : Type) [s : lattice.semilattice_inf_top α] : lattice.order_top α := {}
@[instance] def lattice.semilattice_inf_top.to_semilattice_inf (α : Type) [s : lattice.semilattice_inf_top α] : lattice.semilattice_inf α := {}
class lattice.semilattice_inf_bot (α : Type) := (u:Unit:=())
@[instance] def lattice.semilattice_inf_bot.to_order_bot (α : Type) [s : lattice.semilattice_inf_bot α] : lattice.order_bot α := {}
@[instance] def lattice.semilattice_inf_bot.to_semilattice_inf (α : Type) [s : lattice.semilattice_inf_bot α] : lattice.semilattice_inf α := {}
class lattice.bounded_lattice (α : Type) := (u:Unit:=())
@[instance] def lattice.bounded_lattice.to_lattice (α : Type) [s : lattice.bounded_lattice α] : lattice.lattice α := {}
@[instance] def lattice.bounded_lattice.to_order_top (α : Type) [s : lattice.bounded_lattice α] : lattice.order_top α := {}
@[instance] def lattice.bounded_lattice.to_order_bot (α : Type) [s : lattice.bounded_lattice α] : lattice.order_bot α := {}
@[instance] def lattice.semilattice_inf_top_of_bounded_lattice (α : Type) [bl : lattice.bounded_lattice α] : lattice.semilattice_inf_top α := {}
@[instance] def lattice.semilattice_inf_bot_of_bounded_lattice (α : Type) [bl : lattice.bounded_lattice α] : lattice.semilattice_inf_bot α := {}
@[instance] def lattice.semilattice_sup_top_of_bounded_lattice (α : Type) [bl : lattice.bounded_lattice α] : lattice.semilattice_sup_top α := {}
@[instance] def lattice.semilattice_sup_bot_of_bounded_lattice (α : Type) [bl : lattice.bounded_lattice α] : lattice.semilattice_sup_bot α := {}
class category_theory.groupoid (obj : Type) := (u:Unit:=())
@[instance] def category_theory.groupoid.to_category (obj : Type) [c : category_theory.groupoid obj] : category_theory.category obj := {}
class lattice.bounded_distrib_lattice (α : Type) := (u:Unit:=())
@[instance] def lattice.bounded_distrib_lattice.to_distrib_lattice (α : Type) [s : lattice.bounded_distrib_lattice α] : lattice.distrib_lattice α := {}
@[instance] def lattice.bounded_distrib_lattice.to_bounded_lattice (α : Type) [s : lattice.bounded_distrib_lattice α] : lattice.bounded_lattice α := {}
@[instance] def category_theory.is_iso.of_groupoid (C : Type) [𝒞 : category_theory.groupoid C] (X : Type) (Y : Type) (f : Type) : @category_theory.is_iso C (@category_theory.groupoid.to_category C 𝒞) X Y f := {}
class category_theory.concrete_category (C : Type) := (u:Unit:=())
@[instance] def category_theory.concrete_category.to_category (C : Type) [c : category_theory.concrete_category C] : category_theory.category C := {}
class category_theory.has_forget₂ (C : Type) (D : Type) [_inst_1 : category_theory.concrete_category C] [_inst_2 : category_theory.concrete_category D] := (u:Unit:=())
class category_theory.is_equivalence (C : Type) [𝒞 : category_theory.category C] (D : Type) [𝒟 : category_theory.category D] (F : Type) := (u:Unit:=())
class category_theory.ess_surj (C : Type) [𝒞 : category_theory.category C] (D : Type) [𝒟 : category_theory.category D] (F : Type) := (u:Unit:=())
@[instance] def category_theory.equivalence.faithful_of_equivalence (C : Type) [𝒞 : category_theory.category C] (D : Type) [𝒟 : category_theory.category D] (F : Type) [_inst_1 : @category_theory.is_equivalence C 𝒞 D 𝒟 F] : @category_theory.faithful C 𝒞 D 𝒟 F := {}
class category_theory.bundled_hom (c : Type) (hom : Type) := (u:Unit:=())
class category_theory.unbundled_hom (c : Type) (hom : Type) := (u:Unit:=())
@[instance] def category_theory.equivalence.full_of_equivalence (C : Type) [𝒞 : category_theory.category C] (D : Type) [𝒟 : category_theory.category D] (F : Type) [_inst_1 : @category_theory.is_equivalence C 𝒞 D 𝒟 F] : @category_theory.full C 𝒞 D 𝒟 F := {}
class lattice.boolean_algebra (α : Type) := (u:Unit:=())
@[instance] def lattice.boolean_algebra.to_bounded_distrib_lattice (α : Type) [s : lattice.boolean_algebra α] : lattice.bounded_distrib_lattice α := {}
@[instance] def lattice.boolean_algebra.to_has_neg (α : Type) [s : lattice.boolean_algebra α] : has_neg α := {}
@[instance] def lattice.boolean_algebra.to_has_sub (α : Type) [s : lattice.boolean_algebra α] : has_sub α := {}
class category_theory.is_left_adjoint (C : Type) [𝒞 : category_theory.category C] (D : Type) [𝒟 : category_theory.category D] (left : Type) := (u:Unit:=())
class category_theory.is_right_adjoint (C : Type) [𝒞 : category_theory.category C] (D : Type) [𝒟 : category_theory.category D] (right : Type) := (u:Unit:=())
class ordered_comm_monoid (α : Type) := (u:Unit:=())
@[instance] def ordered_comm_monoid.to_add_comm_monoid (α : Type) [s : ordered_comm_monoid α] : add_comm_monoid α := {}
@[instance] def ordered_comm_monoid.to_partial_order (α : Type) [s : ordered_comm_monoid α] : partial_order α := {}
class canonically_ordered_monoid (α : Type) := (u:Unit:=())
@[instance] def canonically_ordered_monoid.to_ordered_comm_monoid (α : Type) [s : canonically_ordered_monoid α] : ordered_comm_monoid α := {}
@[instance] def canonically_ordered_monoid.to_order_bot (α : Type) [s : canonically_ordered_monoid α] : lattice.order_bot α := {}
class is_semiring_hom (α : Type) (β : Type) [_inst_1 : semiring α] [_inst_2 : semiring β] (f : Type) := (u:Unit:=())
@[instance] def is_semiring_hom.is_add_monoid_hom (α : Type) (β : Type) [_inst_1 : semiring α] [_inst_2 : semiring β] (f : Type) [_inst_3 : @is_semiring_hom α β _inst_1 _inst_2 f] : @is_add_monoid_hom α β (@add_comm_monoid.to_add_monoid α (@semiring.to_add_comm_monoid α _inst_1)) (@add_comm_monoid.to_add_monoid β (@semiring.to_add_comm_monoid β _inst_2)) f := {}
@[instance] def is_semiring_hom.is_monoid_hom (α : Type) (β : Type) [_inst_1 : semiring α] [_inst_2 : semiring β] (f : Type) [_inst_3 : @is_semiring_hom α β _inst_1 _inst_2 f] : @is_monoid_hom α β (@semiring.to_monoid α _inst_1) (@semiring.to_monoid β _inst_2) f := {}
class is_ring_hom (α : Type) (β : Type) [_inst_1 : ring α] [_inst_2 : ring β] (f : Type) := (u:Unit:=())
@[instance] def is_ring_hom.is_semiring_hom (α : Type) (β : Type) [_inst_1 : ring α] [_inst_2 : ring β] (f : Type) [_inst_3 : @is_ring_hom α β _inst_1 _inst_2 f] : @is_semiring_hom α β (@ring.to_semiring α _inst_1) (@ring.to_semiring β _inst_2) f := {}
@[instance] def is_ring_hom.is_add_group_hom (α : Type) (β : Type) [_inst_1 : ring α] [_inst_2 : ring β] (f : Type) [_inst_3 : @is_ring_hom α β _inst_1 _inst_2 f] : @is_add_group_hom α β (@add_comm_group.to_add_group α (@ring.to_add_comm_group α _inst_1)) (@add_comm_group.to_add_group β (@ring.to_add_comm_group β _inst_2)) f := {}
class nonzero_comm_semiring (α : Type) := (u:Unit:=())
@[instance] def nonzero_comm_semiring.to_comm_semiring (α : Type) [s : nonzero_comm_semiring α] : comm_semiring α := {}
@[instance] def nonzero_comm_semiring.to_zero_ne_one_class (α : Type) [s : nonzero_comm_semiring α] : zero_ne_one_class α := {}
class nonzero_comm_ring (α : Type) := (u:Unit:=())
@[instance] def nonzero_comm_ring.to_comm_ring (α : Type) [s : nonzero_comm_ring α] : comm_ring α := {}
@[instance] def nonzero_comm_ring.to_zero_ne_one_class (α : Type) [s : nonzero_comm_ring α] : zero_ne_one_class α := {}
@[instance] def nonzero_comm_ring.to_nonzero_comm_semiring (α : Type) [I : nonzero_comm_ring α] : nonzero_comm_semiring α := {}
@[instance] def integral_domain.to_nonzero_comm_ring (α : Type) [id : integral_domain α] : nonzero_comm_ring α := {}
class domain (α : Type) := (u:Unit:=())
@[instance] def domain.to_ring (α : Type) [s : domain α] : ring α := {}
@[instance] def domain.to_no_zero_divisors (α : Type) [s : domain α] : no_zero_divisors α := {}
@[instance] def domain.to_zero_ne_one_class (α : Type) [s : domain α] : zero_ne_one_class α := {}
@[instance] def integral_domain.to_domain (α : Type) [s : integral_domain α] : domain α := {}
@[instance] def division_ring_has_div' (α : Type) [_inst_1 : division_ring α] : has_div α := {}
@[instance] def division_ring.to_domain (α : Type) [s : division_ring α] : domain α := {}
@[instance] def field.to_integral_domain (α : Type) [F : field α] : integral_domain α := {}
@[instance] def ordered_cancel_comm_monoid.to_ordered_comm_monoid (α : Type) [H : ordered_cancel_comm_monoid α] : ordered_comm_monoid α := {}
@[instance] def decidable_linear_ordered_comm_group.decidable_linear_ordered_cancel_comm_monoid (α : Type) [s : decidable_linear_ordered_comm_group α] : decidable_linear_ordered_cancel_comm_monoid α := {}
class nonneg_comm_group (α : Type) := (u:Unit:=())
@[instance] def nonneg_comm_group.to_add_comm_group (α : Type) [s : nonneg_comm_group α] : add_comm_group α := {}
@[instance] def nonneg_comm_group.to_ordered_comm_group (α : Type) [s : nonneg_comm_group α] : ordered_comm_group α := {}
class char_zero (α : Type) [_inst_1 : add_monoid α] [_inst_2 : has_one α] := (u:Unit:=())
@[instance] def linear_ordered_semiring.to_char_zero (α : Type) [_inst_1 : linear_ordered_semiring α] : @char_zero α (@add_comm_monoid.to_add_monoid α (@ordered_comm_monoid.to_add_comm_monoid α (@ordered_cancel_comm_monoid.to_ordered_comm_monoid α (@ordered_semiring.to_ordered_cancel_comm_monoid α (@linear_ordered_semiring.to_ordered_semiring α _inst_1))))) (@monoid.to_has_one α (@semiring.to_monoid α (@ordered_semiring.to_semiring α (@linear_ordered_semiring.to_ordered_semiring α _inst_1)))) := {}
class category_theory.monoidal_category (C : Type) [𝒞 : category_theory.category C] := (u:Unit:=())
@[instance] def linear_ordered_semiring.to_no_top_order (α : Type) [_inst_1 : linear_ordered_semiring α] : @no_top_order α (@partial_order.to_preorder α (@ordered_comm_monoid.to_partial_order α (@ordered_cancel_comm_monoid.to_ordered_comm_monoid α (@ordered_semiring.to_ordered_cancel_comm_monoid α (@linear_ordered_semiring.to_ordered_semiring α _inst_1))))) := {}
@[instance] def linear_ordered_semiring.to_no_bot_order (α : Type) [_inst_1 : linear_ordered_ring α] : @no_bot_order α (@partial_order.to_preorder α (@ordered_comm_monoid.to_partial_order α (@ordered_cancel_comm_monoid.to_ordered_comm_monoid α (@ordered_semiring.to_ordered_cancel_comm_monoid α (@ordered_ring.to_ordered_semiring α (@linear_ordered_ring.to_ordered_ring α _inst_1)))))) := {}
@[instance] def linear_ordered_ring.to_domain (α : Type) [s : linear_ordered_ring α] : domain α := {}
class nonneg_ring (α : Type) := (u:Unit:=())
@[instance] def nonneg_ring.to_ring (α : Type) [s : nonneg_ring α] : ring α := {}
@[instance] def nonneg_ring.to_zero_ne_one_class (α : Type) [s : nonneg_ring α] : zero_ne_one_class α := {}
@[instance] def nonneg_ring.to_nonneg_comm_group (α : Type) [s : nonneg_ring α] : nonneg_comm_group α := {}
class linear_nonneg_ring (α : Type) := (u:Unit:=())
@[instance] def linear_nonneg_ring.to_domain (α : Type) [s : linear_nonneg_ring α] : domain α := {}
@[instance] def linear_nonneg_ring.to_nonneg_comm_group (α : Type) [s : linear_nonneg_ring α] : nonneg_comm_group α := {}
@[instance] def nonneg_ring.to_ordered_ring (α : Type) [s : nonneg_ring α] : ordered_ring α := {}
@[instance] def linear_nonneg_ring.to_nonneg_ring (α : Type) [s : linear_nonneg_ring α] : nonneg_ring α := {}
@[instance] def linear_nonneg_ring.to_linear_order (α : Type) [s : linear_nonneg_ring α] : linear_order α := {}
@[instance] def linear_nonneg_ring.to_linear_ordered_ring (α : Type) [s : linear_nonneg_ring α] : linear_ordered_ring α := {}
class canonically_ordered_comm_semiring (α : Type) := (u:Unit:=())
@[instance] def canonically_ordered_comm_semiring.to_canonically_ordered_monoid (α : Type) [s : canonically_ordered_comm_semiring α] : canonically_ordered_monoid α := {}
@[instance] def canonically_ordered_comm_semiring.to_comm_semiring (α : Type) [s : canonically_ordered_comm_semiring α] : comm_semiring α := {}
@[instance] def canonically_ordered_comm_semiring.to_zero_ne_one_class (α : Type) [s : canonically_ordered_comm_semiring α] : zero_ne_one_class α := {}
@[instance] def linear_ordered_field.to_densely_ordered (α : Type) [_inst_1 : linear_ordered_field α] : @densely_ordered α (@partial_order.to_preorder α (@ordered_comm_monoid.to_partial_order α (@ordered_cancel_comm_monoid.to_ordered_comm_monoid α (@ordered_semiring.to_ordered_cancel_comm_monoid α (@ordered_ring.to_ordered_semiring α (@linear_ordered_ring.to_ordered_ring α (@linear_ordered_field.to_linear_ordered_ring α _inst_1))))))) := {}
@[instance] def linear_ordered_field.to_no_top_order (α : Type) [_inst_1 : linear_ordered_field α] : @no_top_order α (@partial_order.to_preorder α (@ordered_comm_monoid.to_partial_order α (@ordered_cancel_comm_monoid.to_ordered_comm_monoid α (@ordered_semiring.to_ordered_cancel_comm_monoid α (@ordered_ring.to_ordered_semiring α (@linear_ordered_ring.to_ordered_ring α (@linear_ordered_field.to_linear_ordered_ring α _inst_1))))))) := {}
class category_theory.representable (C : Type) [𝒞 : category_theory.category C] (F : Type) := (u:Unit:=())
@[instance] def linear_ordered_field.to_no_bot_order (α : Type) [_inst_1 : linear_ordered_field α] : @no_bot_order α (@partial_order.to_preorder α (@ordered_comm_monoid.to_partial_order α (@ordered_cancel_comm_monoid.to_ordered_comm_monoid α (@ordered_semiring.to_ordered_cancel_comm_monoid α (@ordered_ring.to_ordered_semiring α (@linear_ordered_ring.to_ordered_ring α (@linear_ordered_field.to_linear_ordered_ring α _inst_1))))))) := {}
class is_ring_anti_hom (R : Type) (F : Type) [_inst_1 : ring R] [_inst_2 : ring F] (f : Type) := (u:Unit:=())
@[instance] def is_ring_anti_hom.is_add_group_hom (R : Type) (F : Type) [_inst_1 : ring R] [_inst_2 : ring F] (f : Type) [_inst_3 : @is_ring_anti_hom R F _inst_1 _inst_2 f] : @is_add_group_hom R F (@add_comm_group.to_add_group R (@ring.to_add_comm_group R _inst_1)) (@add_comm_group.to_add_group F (@ring.to_add_comm_group F _inst_2)) f := {}
class lattice.has_Sup (α : Type) := (u:Unit:=())
class lattice.has_Inf (α : Type) := (u:Unit:=())
class lattice.complete_lattice (α : Type) := (u:Unit:=())
@[instance] def lattice.complete_lattice.to_bounded_lattice (α : Type) [s : lattice.complete_lattice α] : lattice.bounded_lattice α := {}
@[instance] def lattice.complete_lattice.to_has_Sup (α : Type) [s : lattice.complete_lattice α] : lattice.has_Sup α := {}
@[instance] def lattice.complete_lattice.to_has_Inf (α : Type) [s : lattice.complete_lattice α] : lattice.has_Inf α := {}
class lattice.complete_linear_order (α : Type) := (u:Unit:=())
@[instance] def lattice.complete_linear_order.to_complete_lattice (α : Type) [s : lattice.complete_linear_order α] : lattice.complete_lattice α := {}
@[instance] def lattice.complete_linear_order.to_decidable_linear_order (α : Type) [s : lattice.complete_linear_order α] : decidable_linear_order α := {}
class category_theory.reflective (C : Type) [𝒞 : category_theory.category C] (D : Type) [𝒟 : category_theory.category D] (R : Type) := (u:Unit:=())
@[instance] def category_theory.reflective.to_is_right_adjoint (C : Type) [𝒞 : category_theory.category C] (D : Type) [𝒟 : category_theory.category D] (R : Type) [c : @category_theory.reflective C 𝒞 D 𝒟 R] : @category_theory.is_right_adjoint C 𝒞 D 𝒟 R := {}
@[instance] def category_theory.reflective.to_full (C : Type) [𝒞 : category_theory.category C] (D : Type) [𝒟 : category_theory.category D] (R : Type) [c : @category_theory.reflective C 𝒞 D 𝒟 R] : @category_theory.full D 𝒟 C 𝒞 R := {}
@[instance] def category_theory.reflective.to_faithful (C : Type) [𝒞 : category_theory.category C] (D : Type) [𝒟 : category_theory.category D] (R : Type) [c : @category_theory.reflective C 𝒞 D 𝒟 R] : @category_theory.faithful D 𝒟 C 𝒞 R := {}
class category_theory.monadic_right_adjoint (C : Type) [𝒞 : category_theory.category C] (D : Type) [𝒟 : category_theory.category D] (R : Type) := (u:Unit:=())
@[instance] def category_theory.monadic_right_adjoint.to_is_right_adjoint (C : Type) [𝒞 : category_theory.category C] (D : Type) [𝒟 : category_theory.category D] (R : Type) [c : @category_theory.monadic_right_adjoint C 𝒞 D 𝒟 R] : @category_theory.is_right_adjoint C 𝒞 D 𝒟 R := {}
@[instance] def category_theory.monadic_of_reflective (C : Type) [𝒞 : category_theory.category C] (D : Type) [𝒟 : category_theory.category D] (R : Type) [_inst_1 : @category_theory.reflective C 𝒞 D 𝒟 R] : @category_theory.monadic_right_adjoint C 𝒞 D 𝒟 R := {}
class lattice.complete_distrib_lattice (α : Type) := (u:Unit:=())
@[instance] def lattice.complete_distrib_lattice.to_complete_lattice (α : Type) [s : lattice.complete_distrib_lattice α] : lattice.complete_lattice α := {}
@[instance] def lattice.lattice.bounded_distrib_lattice (α : Type) [d : lattice.complete_distrib_lattice α] : lattice.bounded_distrib_lattice α := {}
class lattice.complete_boolean_algebra (α : Type) := (u:Unit:=())
@[instance] def lattice.complete_boolean_algebra.to_boolean_algebra (α : Type) [s : lattice.complete_boolean_algebra α] : lattice.boolean_algebra α := {}
@[instance] def lattice.complete_boolean_algebra.to_complete_distrib_lattice (α : Type) [s : lattice.complete_boolean_algebra α] : lattice.complete_distrib_lattice α := {}
class category_theory.limits.has_limit (J : Type) [_inst_1 : category_theory.category J] (C : Type) [𝒞 : category_theory.category C] (F : Type) := (u:Unit:=())
class category_theory.limits.has_limits_of_shape (J : Type) [_inst_1 : category_theory.category J] (C : Type) [𝒞 : category_theory.category C] := (u:Unit:=())
class category_theory.limits.has_limits (C : Type) [𝒞 : category_theory.category C] := (u:Unit:=())
@[instance] def category_theory.limits.has_limit_of_has_limits_of_shape (C : Type) [𝒞 : category_theory.category C] (J : Type) [_inst_3 : category_theory.category J] [H : @category_theory.limits.has_limits_of_shape J _inst_3 C 𝒞] (F : Type) : @category_theory.limits.has_limit J _inst_3 C 𝒞 F := {}
@[instance] def category_theory.limits.has_limits_of_shape_of_has_limits (C : Type) [𝒞 : category_theory.category C] (J : Type) [_inst_3 : category_theory.category J] [H : @category_theory.limits.has_limits C 𝒞] : @category_theory.limits.has_limits_of_shape J _inst_3 C 𝒞 := {}
class wseq.is_finite (α : Type) (s : Type) := (u:Unit:=())
class wseq.productive (α : Type) (s : Type) := (u:Unit:=())
class euclidean_domain (α : Type) := (u:Unit:=())
@[instance] def euclidean_domain.to_nonzero_comm_ring (α : Type) [c : euclidean_domain α] : nonzero_comm_ring α := {}
@[instance] def euclidean_domain.has_div (α : Type) [_inst_1 : euclidean_domain α] : has_div α := {}
@[instance] def euclidean_domain.has_mod (α : Type) [_inst_1 : euclidean_domain α] : has_mod α := {}
class category_theory.limits.has_colimit (J : Type) [_inst_1 : category_theory.category J] (C : Type) [𝒞 : category_theory.category C] (F : Type) := (u:Unit:=())
class category_theory.limits.has_colimits_of_shape (J : Type) [_inst_1 : category_theory.category J] (C : Type) [𝒞 : category_theory.category C] := (u:Unit:=())
class category_theory.limits.has_colimits (C : Type) [𝒞 : category_theory.category C] := (u:Unit:=())
@[instance] def euclidean_domain.integral_domain (α : Type) [e : euclidean_domain α] : integral_domain α := {}
@[instance] def category_theory.limits.has_colimit_of_has_colimits_of_shape (C : Type) [𝒞 : category_theory.category C] (J : Type) [_inst_3 : category_theory.category J] [H : @category_theory.limits.has_colimits_of_shape J _inst_3 C 𝒞] (F : Type) : @category_theory.limits.has_colimit J _inst_3 C 𝒞 F := {}
@[instance] def category_theory.limits.has_colimits_of_shape_of_has_colimits (C : Type) [𝒞 : category_theory.category C] (J : Type) [_inst_3 : category_theory.category J] [H : @category_theory.limits.has_colimits C 𝒞] : @category_theory.limits.has_colimits_of_shape J _inst_3 C 𝒞 := {}
@[instance] def discrete_field.to_euclidean_domain (K : Type) [_inst_1 : discrete_field K] : euclidean_domain K := {}
class category_theory.limits.preserves_limit (C : Type) [𝒞 : category_theory.category C] (D : Type) [𝒟 : category_theory.category D] (J : Type) [_inst_1 : category_theory.category J] (K : Type) (F : Type) := (u:Unit:=())
class category_theory.limits.preserves_colimit (C : Type) [𝒞 : category_theory.category C] (D : Type) [𝒟 : category_theory.category D] (J : Type) [_inst_1 : category_theory.category J] (K : Type) (F : Type) := (u:Unit:=())
class category_theory.limits.preserves_limits_of_shape (C : Type) [𝒞 : category_theory.category C] (D : Type) [𝒟 : category_theory.category D] (J : Type) [_inst_2 : category_theory.category J] (F : Type) := (u:Unit:=())
class category_theory.limits.preserves_colimits_of_shape (C : Type) [𝒞 : category_theory.category C] (D : Type) [𝒟 : category_theory.category D] (J : Type) [_inst_2 : category_theory.category J] (F : Type) := (u:Unit:=())
class category_theory.limits.preserves_limits (C : Type) [𝒞 : category_theory.category C] (D : Type) [𝒟 : category_theory.category D] (F : Type) := (u:Unit:=())
class category_theory.limits.preserves_colimits (C : Type) [𝒞 : category_theory.category C] (D : Type) [𝒟 : category_theory.category D] (F : Type) := (u:Unit:=())
@[instance] def category_theory.limits.preserves_limits_of_shape.preserves_limit (C : Type) [𝒞 : category_theory.category C] (D : Type) [𝒟 : category_theory.category D] (J : Type) [_inst_2 : category_theory.category J] (F : Type) [c : @category_theory.limits.preserves_limits_of_shape C 𝒞 D 𝒟 J _inst_2 F] (K : Type) : @category_theory.limits.preserves_limit C 𝒞 D 𝒟 J _inst_2 K F := {}
@[instance] def category_theory.limits.preserves_limits.preserves_limits_of_shape (C : Type) [𝒞 : category_theory.category C] (D : Type) [𝒟 : category_theory.category D] (F : Type) [c : @category_theory.limits.preserves_limits C 𝒞 D 𝒟 F] (J : Type) [𝒥 : category_theory.category J] : @category_theory.limits.preserves_limits_of_shape C 𝒞 D 𝒟 J 𝒥 F := {}
@[instance] def category_theory.limits.preserves_colimits_of_shape.preserves_colimit (C : Type) [𝒞 : category_theory.category C] (D : Type) [𝒟 : category_theory.category D] (J : Type) [_inst_2 : category_theory.category J] (F : Type) [c : @category_theory.limits.preserves_colimits_of_shape C 𝒞 D 𝒟 J _inst_2 F] (K : Type) : @category_theory.limits.preserves_colimit C 𝒞 D 𝒟 J _inst_2 K F := {}
@[instance] def category_theory.limits.preserves_colimits.preserves_colimits_of_shape (C : Type) [𝒞 : category_theory.category C] (D : Type) [𝒟 : category_theory.category D] (F : Type) [c : @category_theory.limits.preserves_colimits C 𝒞 D 𝒟 F] (J : Type) [𝒥 : category_theory.category J] : @category_theory.limits.preserves_colimits_of_shape C 𝒞 D 𝒟 J 𝒥 F := {}
@[instance] def category_theory.limits.has_limits_of_complete_lattice (α : Type) [_inst_1 : lattice.complete_lattice α] : @category_theory.limits.has_limits α (@preorder.small_category α (@partial_order.to_preorder α (@lattice.order_bot.to_partial_order α (@lattice.bounded_lattice.to_order_bot α (@lattice.complete_lattice.to_bounded_lattice α _inst_1))))) := {}
@[instance] def category_theory.limits.has_colimits_of_complete_lattice (α : Type) [_inst_1 : lattice.complete_lattice α] : @category_theory.limits.has_colimits α (@preorder.small_category α (@partial_order.to_preorder α (@lattice.order_bot.to_partial_order α (@lattice.bounded_lattice.to_order_bot α (@lattice.complete_lattice.to_bounded_lattice α _inst_1))))) := {}
class category_theory.limits.reflects_limit (C : Type) [𝒞 : category_theory.category C] (D : Type) [𝒟 : category_theory.category D] (J : Type) [_inst_1 : category_theory.category J] (K : Type) (F : Type) := (u:Unit:=())
class encodable (α : Type) := (u:Unit:=())
class category_theory.limits.reflects_colimit (C : Type) [𝒞 : category_theory.category C] (D : Type) [𝒟 : category_theory.category D] (J : Type) [_inst_1 : category_theory.category J] (K : Type) (F : Type) := (u:Unit:=())
class category_theory.limits.reflects_limits_of_shape (C : Type) [𝒞 : category_theory.category C] (D : Type) [𝒟 : category_theory.category D] (J : Type) [_inst_2 : category_theory.category J] (F : Type) := (u:Unit:=())
class category_theory.limits.reflects_colimits_of_shape (C : Type) [𝒞 : category_theory.category C] (D : Type) [𝒟 : category_theory.category D] (J : Type) [_inst_2 : category_theory.category J] (F : Type) := (u:Unit:=())
class category_theory.limits.reflects_limits (C : Type) [𝒞 : category_theory.category C] (D : Type) [𝒟 : category_theory.category D] (F : Type) := (u:Unit:=())
class category_theory.limits.reflects_colimits (C : Type) [𝒞 : category_theory.category C] (D : Type) [𝒟 : category_theory.category D] (F : Type) := (u:Unit:=())
@[instance] def category_theory.limits.reflects_limit_of_reflects_limits_of_shape (C : Type) [𝒞 : category_theory.category C] (D : Type) [𝒟 : category_theory.category D] (J : Type) [_inst_1 : category_theory.category J] (K : Type) (F : Type) [H : @category_theory.limits.reflects_limits_of_shape C 𝒞 D 𝒟 J _inst_1 F] : @category_theory.limits.reflects_limit C 𝒞 D 𝒟 J _inst_1 K F := {}
@[instance] def category_theory.limits.reflects_colimit_of_reflects_colimits_of_shape (C : Type) [𝒞 : category_theory.category C] (D : Type) [𝒟 : category_theory.category D] (J : Type) [_inst_1 : category_theory.category J] (K : Type) (F : Type) [H : @category_theory.limits.reflects_colimits_of_shape C 𝒞 D 𝒟 J _inst_1 F] : @category_theory.limits.reflects_colimit C 𝒞 D 𝒟 J _inst_1 K F := {}
@[instance] def category_theory.limits.reflects_limits_of_shape_of_reflects_limits (C : Type) [𝒞 : category_theory.category C] (D : Type) [𝒟 : category_theory.category D] (J : Type) [_inst_1 : category_theory.category J] (F : Type) [H : @category_theory.limits.reflects_limits C 𝒞 D 𝒟 F] : @category_theory.limits.reflects_limits_of_shape C 𝒞 D 𝒟 J _inst_1 F := {}
@[instance] def category_theory.limits.reflects_colimits_of_shape_of_reflects_colimits (C : Type) [𝒞 : category_theory.category C] (D : Type) [𝒟 : category_theory.category D] (J : Type) [_inst_1 : category_theory.category J] (F : Type) [H : @category_theory.limits.reflects_colimits C 𝒞 D 𝒟 F] : @category_theory.limits.reflects_colimits_of_shape C 𝒞 D 𝒟 J _inst_1 F := {}
@[instance] def category_theory.adjunction.left_adjoint_preserves_colimits (C : Type) [𝒞 : category_theory.category C] (D : Type) [𝒟 : category_theory.category D] (F : Type) (G : Type) (adj : Type) : @category_theory.limits.preserves_colimits C 𝒞 D 𝒟 F := {}
@[instance] def category_theory.adjunction.is_equivalence_preserves_colimits (C : Type) [𝒞 : category_theory.category C] (D : Type) [𝒟 : category_theory.category D] (E : Type) [_inst_2 : @category_theory.is_equivalence C 𝒞 D 𝒟 E] : @category_theory.limits.preserves_colimits C 𝒞 D 𝒟 E := {}
@[instance] def category_theory.adjunction.right_adjoint_preserves_limits (C : Type) [𝒞 : category_theory.category C] (D : Type) [𝒟 : category_theory.category D] (F : Type) (G : Type) (adj : Type) : @category_theory.limits.preserves_limits D 𝒟 C 𝒞 G := {}
@[instance] def category_theory.adjunction.is_equivalence_preserves_limits (C : Type) [𝒞 : category_theory.category C] (D : Type) [𝒟 : category_theory.category D] (E : Type) [_inst_2 : @category_theory.is_equivalence D 𝒟 C 𝒞 E] : @category_theory.limits.preserves_limits D 𝒟 C 𝒞 E := {}
class irreducible (α : Type) [_inst_1 : monoid α] (p : Type) := (u:Unit:=())
class floor_ring (α : Type) [_inst_1 : linear_ordered_ring α] := (u:Unit:=())
class archimedean (α : Type) [_inst_1 : ordered_comm_monoid α] := (u:Unit:=())
class normalization_domain (α : Type) := (u:Unit:=())
@[instance] def normalization_domain.to_integral_domain (α : Type) [s : normalization_domain α] : integral_domain α := {}
class gcd_domain (α : Type) := (u:Unit:=())
@[instance] def gcd_domain.to_normalization_domain (α : Type) [s : gcd_domain α] : normalization_domain α := {}
class unique_factorization_domain (α : Type) [_inst_1 : integral_domain α] := (u:Unit:=())
class zsqrtd.nonsquare (x : Type) := (u:Unit:=())
class fin2.is_lt (m : Type) (n : Type) := (u:Unit:=())
class is_absolute_value (α : Type) [_inst_1 : discrete_linear_ordered_field α] (β : Type) [_inst_2 : ring β] (f : Type) := (u:Unit:=())
class is_add_submonoid (β : Type) [_inst_2 : add_monoid β] (s : Type) := (u:Unit:=())
class is_submonoid (α : Type) [_inst_1 : monoid α] (s : Type) := (u:Unit:=())
class fintype (α : Type) := (u:Unit:=())
@[instance] def unique.fintype (α : Type) [_inst_1 : unique α] : fintype α := {}
class nat.prime (p : Type) := (u:Unit:=())
class infinite (α : Type) := (u:Unit:=())
@[instance] def infinite.nonempty (α : Type) [_inst_1 : infinite α] : nonempty α := {}
class denumerable (α : Type) := (u:Unit:=())
@[instance] def denumerable.to_encodable (α : Type) [c : denumerable α] : encodable α := {}
class turing.pointed_map (Γ : Type) (Γ' : Type) [_inst_1 : inhabited Γ] [_inst_2 : inhabited Γ'] (f : Type) := (u:Unit:=())
class category_theory.limits.has_products (C : Type) [𝒞 : category_theory.category C] := (u:Unit:=())
class category_theory.limits.has_coproducts (C : Type) [𝒞 : category_theory.category C] := (u:Unit:=())
class category_theory.limits.fin_category (J : Type) [_inst_1 : category_theory.category J] := (u:Unit:=())
@[instance] def category_theory.limits.fin_category.fintype_obj (J : Type) [_inst_1 : category_theory.category J] [c : @category_theory.limits.fin_category J _inst_1] : fintype J := {}
class category_theory.limits.has_finite_limits (C : Type) [𝒞 : category_theory.category C] := (u:Unit:=())
class category_theory.limits.has_finite_colimits (C : Type) [𝒞 : category_theory.category C] := (u:Unit:=())
@[instance] def category_theory.limits.has_finite_limits.has_limits_of_shape (C : Type) [𝒞 : category_theory.category C] [c : @category_theory.limits.has_finite_limits C 𝒞] (J : Type) [_inst_1 : category_theory.category J] [_inst_2 : @category_theory.limits.fin_category J _inst_1] : @category_theory.limits.has_limits_of_shape J _inst_1 C 𝒞 := {}
@[instance] def category_theory.limits.has_finite_colimits.has_colimits_of_shape (C : Type) [𝒞 : category_theory.category C] [c : @category_theory.limits.has_finite_colimits C 𝒞] (J : Type) [_inst_1 : category_theory.category J] [_inst_2 : @category_theory.limits.fin_category J _inst_1] : @category_theory.limits.has_colimits_of_shape J _inst_1 C 𝒞 := {}
@[instance] def category_theory.limits.category_theory.limits.has_finite_limits (C : Type) [𝒞 : category_theory.category C] [_inst_1 : @category_theory.limits.has_limits C 𝒞] : @category_theory.limits.has_finite_limits C 𝒞 := {}
@[instance] def category_theory.limits.category_theory.limits.has_finite_colimits (C : Type) [𝒞 : category_theory.category C] [_inst_1 : @category_theory.limits.has_colimits C 𝒞] : @category_theory.limits.has_finite_colimits C 𝒞 := {}
class category_theory.limits.has_finite_products (C : Type) [𝒞 : category_theory.category C] := (u:Unit:=())
class category_theory.limits.has_finite_coproducts (C : Type) [𝒞 : category_theory.category C] := (u:Unit:=())
@[instance] def category_theory.limits.has_finite_products_of_has_products (C : Type) [𝒞 : category_theory.category C] [_inst_1 : @category_theory.limits.has_products C 𝒞] : @category_theory.limits.has_finite_products C 𝒞 := {}
@[instance] def category_theory.limits.has_finite_coproducts_of_has_coproducts (C : Type) [𝒞 : category_theory.category C] [_inst_1 : @category_theory.limits.has_coproducts C 𝒞] : @category_theory.limits.has_finite_coproducts C 𝒞 := {}
@[instance] def category_theory.limits.has_finite_products_of_has_finite_limits (C : Type) [𝒞 : category_theory.category C] [_inst_1 : @category_theory.limits.has_finite_limits C 𝒞] : @category_theory.limits.has_finite_products C 𝒞 := {}
@[instance] def category_theory.limits.has_finite_coproducts_of_has_finite_colimits (C : Type) [𝒞 : category_theory.category C] [_inst_1 : @category_theory.limits.has_finite_colimits C 𝒞] : @category_theory.limits.has_finite_coproducts C 𝒞 := {}
class category_theory.limits.has_terminal (C : Type) [𝒞 : category_theory.category C] := (u:Unit:=())
class category_theory.limits.has_initial (C : Type) [𝒞 : category_theory.category C] := (u:Unit:=())
@[instance] def category_theory.limits.category_theory.limits.has_terminal (C : Type) [𝒞 : category_theory.category C] [_inst_1 : @category_theory.limits.has_finite_products C 𝒞] : @category_theory.limits.has_terminal C 𝒞 := {}
@[instance] def category_theory.limits.category_theory.limits.has_initial (C : Type) [𝒞 : category_theory.category C] [_inst_1 : @category_theory.limits.has_finite_coproducts C 𝒞] : @category_theory.limits.has_initial C 𝒞 := {}
class lattice.conditionally_complete_lattice (α : Type) := (u:Unit:=())
@[instance] def lattice.conditionally_complete_lattice.to_lattice (α : Type) [s : lattice.conditionally_complete_lattice α] : lattice.lattice α := {}
@[instance] def lattice.conditionally_complete_lattice.to_has_Sup (α : Type) [s : lattice.conditionally_complete_lattice α] : lattice.has_Sup α := {}
@[instance] def lattice.conditionally_complete_lattice.to_has_Inf (α : Type) [s : lattice.conditionally_complete_lattice α] : lattice.has_Inf α := {}
class lattice.conditionally_complete_linear_order (α : Type) := (u:Unit:=())
@[instance] def lattice.conditionally_complete_linear_order.to_conditionally_complete_lattice (α : Type) [s : lattice.conditionally_complete_linear_order α] : lattice.conditionally_complete_lattice α := {}
@[instance] def lattice.conditionally_complete_linear_order.to_decidable_linear_order (α : Type) [s : lattice.conditionally_complete_linear_order α] : decidable_linear_order α := {}
class lattice.conditionally_complete_linear_order_bot (α : Type) := (u:Unit:=())
@[instance] def lattice.conditionally_complete_linear_order_bot.to_conditionally_complete_lattice (α : Type) [s : lattice.conditionally_complete_linear_order_bot α] : lattice.conditionally_complete_lattice α := {}
@[instance] def lattice.conditionally_complete_linear_order_bot.to_decidable_linear_order (α : Type) [s : lattice.conditionally_complete_linear_order_bot α] : decidable_linear_order α := {}
@[instance] def lattice.conditionally_complete_linear_order_bot.to_order_bot (α : Type) [s : lattice.conditionally_complete_linear_order_bot α] : lattice.order_bot α := {}
@[instance] def lattice.conditionally_complete_lattice_of_complete_lattice (α : Type) [_inst_1 : lattice.complete_lattice α] : lattice.conditionally_complete_lattice α := {}
@[instance] def lattice.conditionally_complete_linear_order_of_complete_linear_order (α : Type) [_inst_1 : lattice.complete_linear_order α] : lattice.conditionally_complete_linear_order α := {}
class primcodable (α : Type) := (u:Unit:=())
@[instance] def primcodable.to_encodable (α : Type) [c : primcodable α] : encodable α := {}
@[instance] def primcodable.of_denumerable (α : Type) [_inst_1 : denumerable α] : primcodable α := {}
class category_theory.limits.has_equalizers (C : Type) [𝒞 : category_theory.category C] := (u:Unit:=())
class category_theory.limits.has_coequalizers (C : Type) [𝒞 : category_theory.category C] := (u:Unit:=())
class measurable_space (α : Type) := (u:Unit:=())
class category_theory.limits.has_pullbacks (C : Type) [𝒞 : category_theory.category C] := (u:Unit:=())
class category_theory.limits.has_pushouts (C : Type) [𝒞 : category_theory.category C] := (u:Unit:=())
class category_theory.limits.has_binary_products (C : Type) [𝒞 : category_theory.category C] := (u:Unit:=())
class category_theory.limits.has_binary_coproducts (C : Type) [𝒞 : category_theory.category C] := (u:Unit:=())
@[instance] def category_theory.limits.category_theory.limits.has_binary_products (C : Type) [𝒞 : category_theory.category C] [_inst_1 : @category_theory.limits.has_finite_products C 𝒞] : @category_theory.limits.has_binary_products C 𝒞 := {}
@[instance] def category_theory.limits.category_theory.limits.has_binary_coproducts (C : Type) [𝒞 : category_theory.category C] [_inst_1 : @category_theory.limits.has_finite_coproducts C 𝒞] : @category_theory.limits.has_binary_coproducts C 𝒞 := {}
class topological_space (α : Type) := (u:Unit:=())
class discrete_topology (α : Type) [t : topological_space α] := (u:Unit:=())
class is_add_subgroup (β : Type) [_inst_2 : add_group β] (s : Type) := (u:Unit:=())
@[instance] def is_add_subgroup.to_is_add_submonoid (β : Type) [_inst_2 : add_group β] (s : Type) [c : @is_add_subgroup β _inst_2 s] : @is_add_submonoid β (@add_group.to_add_monoid β _inst_2) s := {}
class is_subgroup (α : Type) [_inst_1 : group α] (s : Type) := (u:Unit:=())
@[instance] def is_subgroup.to_is_submonoid (α : Type) [_inst_1 : group α] (s : Type) [c : @is_subgroup α _inst_1 s] : @is_submonoid α (@group.to_monoid α _inst_1) s := {}
class onote.NF (o : Type) := (u:Unit:=())
class topological_space.separable_space (α : Type) [t : topological_space α] := (u:Unit:=())
class topological_space.first_countable_topology (α : Type) [t : topological_space α] := (u:Unit:=())
class topological_space.second_countable_topology (α : Type) [t : topological_space α] := (u:Unit:=())
@[instance] def topological_space.second_countable_topology.to_first_countable_topology (α : Type) [t : topological_space α] [_inst_1 : @topological_space.second_countable_topology α t] : @topological_space.first_countable_topology α t := {}
class normal_add_subgroup (α : Type) [_inst_1 : add_group α] (s : Type) := (u:Unit:=())
@[instance] def normal_add_subgroup.to_is_add_subgroup (α : Type) [_inst_1 : add_group α] (s : Type) [c : @normal_add_subgroup α _inst_1 s] : @is_add_subgroup α _inst_1 s := {}
class normal_subgroup (α : Type) [_inst_1 : group α] (s : Type) := (u:Unit:=())
@[instance] def topological_space.second_countable_topology.to_separable_space (α : Type) [t : topological_space α] [_inst_1 : @topological_space.second_countable_topology α t] : @topological_space.separable_space α t := {}
class compact_space (α : Type) [_inst_2 : topological_space α] := (u:Unit:=())
@[instance] def normal_subgroup.to_is_subgroup (α : Type) [_inst_1 : group α] (s : Type) [c : @normal_subgroup α _inst_1 s] : @is_subgroup α _inst_1 s := {}
@[instance] def fintype.compact_space (α : Type) [_inst_1 : topological_space α] [_inst_3 : fintype α] : @compact_space α _inst_1 := {}
class sequential_space (α : Type) [_inst_3 : topological_space α] := (u:Unit:=())
class locally_compact_space (α : Type) [_inst_3 : topological_space α] := (u:Unit:=())
class irreducible_space (α : Type) [_inst_2 : topological_space α] := (u:Unit:=())
class connected_space (α : Type) [_inst_2 : topological_space α] := (u:Unit:=())
@[instance] def irreducible_space.connected_space (α : Type) [_inst_2 : topological_space α] [_inst_3 : @irreducible_space α _inst_2] : @connected_space α _inst_2 := {}
class totally_disconnected_space (α : Type) [_inst_2 : topological_space α] := (u:Unit:=())
class totally_separated_space (α : Type) [_inst_2 : topological_space α] := (u:Unit:=())
@[instance] def totally_separated_space.totally_disconnected_space (α : Type) [_inst_2 : topological_space α] [_inst_3 : @totally_separated_space α _inst_2] : @totally_disconnected_space α _inst_2 := {}
@[instance] def topological_space.first_countable_topology.sequential_space (α : Type) [_inst_1 : topological_space α] [_inst_2 : @topological_space.first_countable_topology α _inst_1] : @sequential_space α _inst_1 := {}
class t0_space (α : Type) [_inst_2 : topological_space α] := (u:Unit:=())
class t1_space (α : Type) [_inst_2 : topological_space α] := (u:Unit:=())
@[instance] def t1_space.t0_space (α : Type) [_inst_1 : topological_space α] [_inst_2 : @t1_space α _inst_1] : @t0_space α _inst_1 := {}
class t2_space (α : Type) [_inst_2 : topological_space α] := (u:Unit:=())
@[instance] def t2_space.t1_space (α : Type) [_inst_1 : topological_space α] [_inst_2 : @t2_space α _inst_1] : @t1_space α _inst_1 := {}
@[instance] def t2_space_discrete (α : Type) [_inst_2 : topological_space α] [_inst_3 : @discrete_topology α _inst_2] : @t2_space α _inst_2 := {}
@[instance] def locally_compact_of_compact (α : Type) [_inst_1 : topological_space α] [_inst_3 : @t2_space α _inst_1] [_inst_4 : @compact_space α _inst_1] : @locally_compact_space α _inst_1 := {}
class regular_space (α : Type) [_inst_2 : topological_space α] := (u:Unit:=())
@[instance] def regular_space.to_t1_space (α : Type) [_inst_2 : topological_space α] [c : @regular_space α _inst_2] : @t1_space α _inst_2 := {}
@[instance] def regular_space.t2_space (α : Type) [_inst_1 : topological_space α] [_inst_2 : @regular_space α _inst_1] : @t2_space α _inst_1 := {}
class normal_space (α : Type) [_inst_2 : topological_space α] := (u:Unit:=())
@[instance] def normal_space.to_t1_space (α : Type) [_inst_2 : topological_space α] [c : @normal_space α _inst_2] : @t1_space α _inst_2 := {}
@[instance] def normal_space.regular_space (α : Type) [_inst_1 : topological_space α] [_inst_2 : @normal_space α _inst_1] : @regular_space α _inst_1 := {}
class uniform_space (α : Type) := (u:Unit:=())
@[instance] def uniform_space.to_topological_space (α : Type) [c : uniform_space α] : topological_space α := {}
class separated (α : Type) [_inst_4 : uniform_space α] := (u:Unit:=())
@[instance] def separated_t2 (α : Type) [_inst_1 : uniform_space α] [s : @separated α _inst_1] : @t2_space α (@uniform_space.to_topological_space α _inst_1) := {}
@[instance] def separated_regular (α : Type) [_inst_1 : uniform_space α] [_inst_4 : @separated α _inst_1] : @regular_space α (@uniform_space.to_topological_space α _inst_1) := {}
class complete_space (α : Type) [_inst_2 : uniform_space α] := (u:Unit:=())
@[instance] def complete_of_compact (α : Type) [_inst_2 : uniform_space α] [_inst_3 : @compact_space α (@uniform_space.to_topological_space α _inst_2)] : @complete_space α _inst_2 := {}
class manifold (H : Type) [_inst_1 : topological_space H] (M : Type) [_inst_2 : topological_space M] := (u:Unit:=())
@[instance] def manifold_model_space (H : Type) [_inst_1 : topological_space H] : @manifold H _inst_1 H _inst_1 := {}
class has_groupoid (H : Type) [_inst_4 : topological_space H] (M : Type) [_inst_5 : topological_space M] [_inst_6 : @manifold H _inst_4 M _inst_5] (G : Type) := (u:Unit:=())
class has_edist (α : Type) := (u:Unit:=())
@[instance] def has_groupoid_model_space (H : Type) [_inst_4 : topological_space H] (G : Type) : @has_groupoid H _inst_4 H _inst_4 (@manifold_model_space H _inst_4) G := {}
class emetric_space (α : Type) := (u:Unit:=())
@[instance] def emetric_space.to_has_edist (α : Type) [c : emetric_space α] : has_edist α := {}
@[instance] def emetric_space.to_uniform_space' (α : Type) [_inst_1 : emetric_space α] : uniform_space α := {}
@[instance] def to_separated (α : Type) [_inst_1 : emetric_space α] : @separated α (@emetric_space.to_uniform_space' α _inst_1) := {}
@[instance] def emetric.topological_space.first_countable_topology (α : Type) [_inst_2 : emetric_space α] : @topological_space.first_countable_topology α (@uniform_space.to_topological_space α (@emetric_space.to_uniform_space' α _inst_2)) := {}
class simple_group (α : Type) [_inst_1 : group α] := (u:Unit:=())
class simple_add_group (α : Type) [_inst_1 : add_group α] := (u:Unit:=())
class is_subring (R : Type) [_inst_1 : ring R] (S : Type) := (u:Unit:=())
@[instance] def is_subring.to_is_add_subgroup (R : Type) [_inst_1 : ring R] (S : Type) [c : @is_subring R _inst_1 S] : @is_add_subgroup R (@add_comm_group.to_add_group R (@ring.to_add_comm_group R _inst_1)) S := {}
@[instance] def is_subring.to_is_submonoid (R : Type) [_inst_1 : ring R] (S : Type) [c : @is_subring R _inst_1 S] : @is_submonoid R (@ring.to_monoid R _inst_1) S := {}
class is_subfield (F : Type) [_inst_1 : discrete_field F] (S : Type) := (u:Unit:=())
@[instance] def is_subfield.to_is_subring (F : Type) [_inst_1 : discrete_field F] (S : Type) [c : @is_subfield F _inst_1 S] : @is_subring F (@domain.to_ring F (@division_ring.to_domain F (@field.to_division_ring F (@discrete_field.to_field F _inst_1)))) S := {}
class has_scalar (α : Type) (γ : Type) := (u:Unit:=())
class mul_action (α : Type) (β : Type) [_inst_1 : monoid α] := (u:Unit:=())
@[instance] def mul_action.to_has_scalar (α : Type) (β : Type) [_inst_1 : monoid α] [c : @mul_action α β _inst_1] : has_scalar α β := {}
class is_cyclic (α : Type) [_inst_1 : group α] := (u:Unit:=())
class distrib_mul_action (α : Type) (β : Type) [_inst_1 : monoid α] [_inst_2 : add_monoid β] := (u:Unit:=())
@[instance] def distrib_mul_action.to_mul_action (α : Type) (β : Type) [_inst_1 : monoid α] [_inst_2 : add_monoid β] [c : @distrib_mul_action α β _inst_1 _inst_2] : @mul_action α β _inst_1 := {}
class semimodule (α : Type) (β : Type) [_inst_1 : semiring α] [_inst_2 : add_comm_monoid β] := (u:Unit:=())
@[instance] def semimodule.to_distrib_mul_action (α : Type) (β : Type) [_inst_1 : semiring α] [_inst_2 : add_comm_monoid β] [c : @semimodule α β _inst_1 _inst_2] : @distrib_mul_action α β (@semiring.to_monoid α _inst_1) (@add_comm_monoid.to_add_monoid β _inst_2) := {}
class module (α : Type) (β : Type) [_inst_1 : ring α] [_inst_2 : add_comm_group β] := (u:Unit:=())
@[instance] def module.to_semimodule (α : Type) (β : Type) [_inst_1 : ring α] [_inst_2 : add_comm_group β] [c : @module α β _inst_1 _inst_2] : @semimodule α β (@ring.to_semiring α _inst_1) (@add_comm_group.to_add_comm_monoid β _inst_2) := {}
@[instance] def semiring.to_semimodule (α : Type) [r : semiring α] : @semimodule α α r (@semiring.to_add_comm_monoid α r) := {}
@[instance] def ring.to_module (α : Type) [r : ring α] : @module α α r (@ring.to_add_comm_group α r) := {}
class is_linear_map (α : Type) (β : Type) (γ : Type) [_inst_1 : ring α] [_inst_2 : add_comm_group β] [_inst_3 : add_comm_group γ] [_inst_4 : @module α β _inst_1 _inst_2] [_inst_5 : @module α γ _inst_1 _inst_3] (f : Type) := (u:Unit:=())
@[instance] def discrete_field.to_vector_space (α : Type) [_inst_1 : discrete_field α] : @module α α (@domain.to_ring α (@division_ring.to_domain α (@field.to_division_ring α (@discrete_field.to_field α _inst_1)))) (@ring.to_add_comm_group α (@domain.to_ring α (@division_ring.to_domain α (@field.to_division_ring α (@discrete_field.to_field α _inst_1))))) := {}
class char_p (α : Type) [_inst_1 : semiring α] (p : Type) := (u:Unit:=())
class perfect_field (α : Type) [_inst_1 : field α] (p : Type) [_inst_2 : @char_p α (@ring.to_semiring α (@domain.to_ring α (@division_ring.to_domain α (@field.to_division_ring α _inst_1)))) p] := (u:Unit:=())
class topological_monoid (α : Type) [_inst_1 : topological_space α] [_inst_2 : monoid α] := (u:Unit:=())
class topological_add_monoid (α : Type) [_inst_1 : topological_space α] [_inst_2 : add_monoid α] := (u:Unit:=())
class topological_add_group (α : Type) [_inst_1 : topological_space α] [_inst_2 : add_group α] := (u:Unit:=())
@[instance] def topological_add_group.to_topological_add_monoid (α : Type) [_inst_1 : topological_space α] [_inst_2 : add_group α] [c : @topological_add_group α _inst_1 _inst_2] : @topological_add_monoid α _inst_1 (@add_group.to_add_monoid α _inst_2) := {}
class topological_group (α : Type) [_inst_1 : topological_space α] [_inst_2 : group α] := (u:Unit:=())
@[instance] def topological_group.to_topological_monoid (α : Type) [_inst_1 : topological_space α] [_inst_2 : group α] [c : @topological_group α _inst_1 _inst_2] : @topological_monoid α _inst_1 (@group.to_monoid α _inst_2) := {}
class add_group_with_zero_nhd (α : Type) := (u:Unit:=())
@[instance] def add_group_with_zero_nhd.to_add_comm_group (α : Type) [c : add_group_with_zero_nhd α] : add_comm_group α := {}
@[instance] def add_group_with_zero_nhd.topological_space (α : Type) [_inst_1 : add_group_with_zero_nhd α] : topological_space α := {}
@[instance] def add_group_with_zero_nhd.topological_add_monoid (α : Type) [_inst_1 : add_group_with_zero_nhd α] : @topological_add_monoid α (@add_group_with_zero_nhd.topological_space α _inst_1) (@add_group.to_add_monoid α (@add_comm_group.to_add_group α (@add_group_with_zero_nhd.to_add_comm_group α _inst_1))) := {}
@[instance] def add_group_with_zero_nhd.topological_add_group (α : Type) [_inst_1 : add_group_with_zero_nhd α] : @topological_add_group α (@add_group_with_zero_nhd.topological_space α _inst_1) (@add_comm_group.to_add_group α (@add_group_with_zero_nhd.to_add_comm_group α _inst_1)) := {}
class ordered_topology (α : Type) [t : topological_space α] [_inst_1 : preorder α] := (u:Unit:=())
class uniform_add_group (α : Type) [_inst_1 : uniform_space α] [_inst_2 : add_group α] := (u:Unit:=())
@[instance] def ordered_topology.to_t2_space (α : Type) [_inst_1 : topological_space α] [_inst_2 : partial_order α] [t : @ordered_topology α _inst_1 (@partial_order.to_preorder α _inst_2)] : @t2_space α _inst_1 := {}
@[instance] def uniform_add_group.to_topological_add_group (α : Type) [_inst_1 : uniform_space α] [_inst_2 : add_group α] [_inst_3 : @uniform_add_group α _inst_1 _inst_2] : @topological_add_group α (@uniform_space.to_topological_space α _inst_1) _inst_2 := {}
class orderable_topology (α : Type) [t : topological_space α] [_inst_1 : partial_order α] := (u:Unit:=())
class add_comm_group.is_Z_bilin (α : Type) (β : Type) (γ : Type) [_inst_1 : add_comm_group α] [_inst_2 : add_comm_group β] [_inst_3 : add_comm_group γ] (f : Type) := (u:Unit:=())
@[instance] def orderable_topology.to_ordered_topology (α : Type) [_inst_1 : topological_space α] [_inst_2 : linear_order α] [t : @orderable_topology α _inst_1 (@linear_order.to_partial_order α _inst_2)] : @ordered_topology α _inst_1 (@partial_order.to_preorder α (@linear_order.to_partial_order α _inst_2)) := {}
@[instance] def orderable_topology.regular_space (α : Type) [_inst_1 : topological_space α] [_inst_2 : linear_order α] [t : @orderable_topology α _inst_1 (@linear_order.to_partial_order α _inst_2)] : @regular_space α _inst_1 := {}
@[instance] def ordered_connected_space (α : Type) [_inst_1 : lattice.conditionally_complete_linear_order α] [_inst_2 : topological_space α] [_inst_3 : @orderable_topology α _inst_2 (@lattice.semilattice_inf.to_partial_order α (@lattice.lattice.to_semilattice_inf α (@lattice.conditionally_complete_lattice.to_lattice α (@lattice.conditionally_complete_linear_order.to_conditionally_complete_lattice α _inst_1))))] [_inst_8 : @densely_ordered α (@partial_order.to_preorder α (@lattice.semilattice_inf.to_partial_order α (@lattice.lattice.to_semilattice_inf α (@lattice.conditionally_complete_lattice.to_lattice α (@lattice.conditionally_complete_linear_order.to_conditionally_complete_lattice α _inst_1)))))] : @connected_space α _inst_2 := {}
class ideal.is_prime (α : Type) [_inst_1 : comm_ring α] (I : Type) := (u:Unit:=())
class ideal.is_maximal (α : Type) [_inst_1 : comm_ring α] (I : Type) := (u:Unit:=())
@[instance] def ideal.is_maximal.is_prime' (α : Type) [_inst_1 : comm_ring α] (I : Type) [H : @ideal.is_maximal α _inst_1 I] : @ideal.is_prime α _inst_1 I := {}
class has_dist (α : Type) := (u:Unit:=())
class metric_space (α : Type) := (u:Unit:=())
@[instance] def metric_space.to_has_dist (α : Type) [c : metric_space α] : has_dist α := {}
@[instance] def metric_space.to_uniform_space' (α : Type) [_inst_1 : metric_space α] : uniform_space α := {}
@[instance] def metric_space.to_has_edist (α : Type) [_inst_1 : metric_space α] : has_edist α := {}
class local_ring (α : Type) := (u:Unit:=())
@[instance] def local_ring.to_nonzero_comm_ring (α : Type) [c : local_ring α] : nonzero_comm_ring α := {}
@[instance] def metric_space.to_separated (α : Type) [_inst_1 : metric_space α] : @separated α (@metric_space.to_uniform_space' α _inst_1) := {}
@[instance] def metric_space.to_emetric_space (α : Type) [_inst_1 : metric_space α] : emetric_space α := {}
class is_local_ring_hom (α : Type) (β : Type) [_inst_1 : comm_ring α] [_inst_2 : comm_ring β] (f : Type) := (u:Unit:=())
@[instance] def is_local_ring_hom.to_is_ring_hom (α : Type) (β : Type) [_inst_1 : comm_ring α] [_inst_2 : comm_ring β] (f : Type) [c : @is_local_ring_hom α β _inst_1 _inst_2 f] : @is_ring_hom α β (@comm_ring.to_ring α _inst_1) (@comm_ring.to_ring β _inst_2) f := {}
@[instance] def discrete_field.local_ring (α : Type) [_inst_1 : discrete_field α] : local_ring α := {}
class topological_semiring (α : Type) [_inst_1 : topological_space α] [_inst_2 : semiring α] := (u:Unit:=())
@[instance] def topological_semiring.to_topological_add_monoid (α : Type) [_inst_1 : topological_space α] [_inst_2 : semiring α] [c : @topological_semiring α _inst_1 _inst_2] : @topological_add_monoid α _inst_1 (@add_comm_monoid.to_add_monoid α (@semiring.to_add_comm_monoid α _inst_2)) := {}
@[instance] def topological_semiring.to_topological_monoid (α : Type) [_inst_1 : topological_space α] [_inst_2 : semiring α] [c : @topological_semiring α _inst_1 _inst_2] : @topological_monoid α _inst_1 (@semiring.to_monoid α _inst_2) := {}
class topological_ring (α : Type) [_inst_1 : topological_space α] [_inst_2 : ring α] := (u:Unit:=())
@[instance] def topological_ring.to_topological_add_monoid (α : Type) [_inst_1 : topological_space α] [_inst_2 : ring α] [c : @topological_ring α _inst_1 _inst_2] : @topological_add_monoid α _inst_1 (@add_group.to_add_monoid α (@add_comm_group.to_add_group α (@ring.to_add_comm_group α _inst_2))) := {}
@[instance] def topological_ring.to_topological_monoid (α : Type) [_inst_1 : topological_space α] [_inst_2 : ring α] [c : @topological_ring α _inst_1 _inst_2] : @topological_monoid α _inst_1 (@ring.to_monoid α _inst_2) := {}
@[instance] def topological_ring.to_topological_semiring (α : Type) [_inst_1 : topological_space α] [_inst_2 : ring α] [t : @topological_ring α _inst_1 _inst_2] : @topological_semiring α _inst_1 (@ring.to_semiring α _inst_2) := {}
@[instance] def topological_ring.to_topological_add_group (α : Type) [_inst_1 : topological_space α] [_inst_2 : ring α] [t : @topological_ring α _inst_1 _inst_2] : @topological_add_group α _inst_1 (@add_comm_group.to_add_group α (@ring.to_add_comm_group α _inst_2)) := {}
class proper_space (α : Type) [_inst_2 : metric_space α] := (u:Unit:=())
@[instance] def proper_of_compact (α : Type) [_inst_1 : metric_space α] [_inst_2 : @compact_space α (@uniform_space.to_topological_space α (@metric_space.to_uniform_space' α _inst_1))] : @proper_space α _inst_1 := {}
@[instance] def locally_compact_of_proper (α : Type) [_inst_1 : metric_space α] [_inst_2 : @proper_space α _inst_1] : @locally_compact_space α (@uniform_space.to_topological_space α (@metric_space.to_uniform_space' α _inst_1)) := {}
@[instance] def complete_of_proper (α : Type) [_inst_1 : metric_space α] [_inst_2 : @proper_space α _inst_1] : @complete_space α (@metric_space.to_uniform_space' α _inst_1) := {}
@[instance] def second_countable_of_proper (α : Type) [_inst_1 : metric_space α] [_inst_2 : @proper_space α _inst_1] : @topological_space.second_countable_topology α (@uniform_space.to_topological_space α (@metric_space.to_uniform_space' α _inst_1)) := {}
class premetric_space (α : Type) := (u:Unit:=())
@[instance] def premetric_space.to_has_dist (α : Type) [c : premetric_space α] : has_dist α := {}
class algebra (R : Type) (A : Type) [_inst_1 : comm_ring R] [_inst_2 : ring A] := (u:Unit:=())
@[instance] def algebra.to_has_scalar (R : Type) (A : Type) [_inst_1 : comm_ring R] [_inst_2 : ring A] [c : @algebra R A _inst_1 _inst_2] : has_scalar R A := {}
@[instance] def algebra.to_module (R : Type) (A : Type) [_inst_1 : comm_ring R] [_inst_3 : ring A] [_inst_4 : @algebra R A _inst_1 _inst_3] : @module R A (@comm_ring.to_ring R _inst_1) (@ring.to_add_comm_group A _inst_3) := {}
@[instance] def algebra.id (R : Type) [_inst_1 : comm_ring R] : @algebra R R _inst_1 (@comm_ring.to_ring R _inst_1) := {}
class has_bracket (L : Type) := (u:Unit:=())
class topological_semimodule (α : Type) (β : Type) [_inst_1 : semiring α] [_inst_2 : topological_space α] [_inst_3 : topological_space β] [_inst_4 : add_comm_monoid β] [_inst_5 : @semimodule α β _inst_1 _inst_4] := (u:Unit:=())
class topological_module (α : Type) (β : Type) [_inst_1 : ring α] [_inst_2 : topological_space α] [_inst_3 : topological_space β] [_inst_4 : add_comm_group β] [_inst_5 : @module α β _inst_1 _inst_4] := (u:Unit:=())
@[instance] def topological_module.to_topological_semimodule (α : Type) (β : Type) [_inst_1 : ring α] [_inst_2 : topological_space α] [_inst_3 : topological_space β] [_inst_4 : add_comm_group β] [_inst_5 : @module α β _inst_1 _inst_4] [c : @topological_module α β _inst_1 _inst_2 _inst_3 _inst_4 _inst_5] : @topological_semimodule α β (@ring.to_semiring α _inst_1) _inst_2 _inst_3 (@add_comm_group.to_add_comm_monoid β _inst_4) (@module.to_semimodule α β _inst_1 _inst_4 _inst_5) := {}
class lie_ring (L : Type) [_inst_1 : add_comm_group L] := (u:Unit:=())
@[instance] def lie_ring.to_has_bracket (L : Type) [_inst_1 : add_comm_group L] [c : @lie_ring L _inst_1] : has_bracket L := {}
class lie_algebra (R : Type) (L : Type) [_inst_1 : comm_ring R] [_inst_2 : add_comm_group L] := (u:Unit:=())
@[instance] def lie_algebra.to_module (R : Type) (L : Type) [_inst_1 : comm_ring R] [_inst_2 : add_comm_group L] [c : @lie_algebra R L _inst_1 _inst_2] : @module R L (@comm_ring.to_ring R _inst_1) _inst_2 := {}
@[instance] def lie_algebra.to_lie_ring (R : Type) (L : Type) [_inst_1 : comm_ring R] [_inst_2 : add_comm_group L] [c : @lie_algebra R L _inst_1 _inst_2] : @lie_ring L _inst_2 := {}
class has_norm (α : Type) := (u:Unit:=())
class normed_group (α : Type) := (u:Unit:=())
@[instance] def normed_group.to_has_norm (α : Type) [c : normed_group α] : has_norm α := {}
@[instance] def normed_group.to_add_comm_group (α : Type) [c : normed_group α] : add_comm_group α := {}
@[instance] def normed_group.to_metric_space (α : Type) [c : normed_group α] : metric_space α := {}
class is_noetherian (α : Type) (β : Type) [_inst_1 : ring α] [_inst_2 : add_comm_group β] [_inst_3 : @module α β _inst_1 _inst_2] := (u:Unit:=())
@[instance] def normed_uniform_group (α : Type) [_inst_1 : normed_group α] : @uniform_add_group α (@metric_space.to_uniform_space' α (@normed_group.to_metric_space α _inst_1)) (@add_comm_group.to_add_group α (@normed_group.to_add_comm_group α _inst_1)) := {}
@[instance] def normed_top_monoid (α : Type) [_inst_1 : normed_group α] : @topological_add_monoid α (@uniform_space.to_topological_space α (@metric_space.to_uniform_space' α (@normed_group.to_metric_space α _inst_1))) (@add_group.to_add_monoid α (@add_comm_group.to_add_group α (@normed_group.to_add_comm_group α _inst_1))) := {}
@[instance] def normed_top_group (α : Type) [_inst_1 : normed_group α] : @topological_add_group α (@uniform_space.to_topological_space α (@metric_space.to_uniform_space' α (@normed_group.to_metric_space α _inst_1))) (@add_comm_group.to_add_group α (@normed_group.to_add_comm_group α _inst_1)) := {}
class normed_ring (α : Type) := (u:Unit:=())
@[instance] def normed_ring.to_has_norm (α : Type) [c : normed_ring α] : has_norm α := {}
@[instance] def normed_ring.to_ring (α : Type) [c : normed_ring α] : ring α := {}
@[instance] def normed_ring.to_metric_space (α : Type) [c : normed_ring α] : metric_space α := {}
@[instance] def normed_ring.to_normed_group (α : Type) [β : normed_ring α] : normed_group α := {}
@[instance] def normed_ring_top_monoid (α : Type) [_inst_1 : normed_ring α] : @topological_monoid α (@uniform_space.to_topological_space α (@metric_space.to_uniform_space' α (@normed_ring.to_metric_space α _inst_1))) (@ring.to_monoid α (@normed_ring.to_ring α _inst_1)) := {}
class is_noetherian_ring (α : Type) [_inst_1 : ring α] := (u:Unit:=())
@[instance] def is_noetherian_ring.to_is_noetherian (α : Type) [_inst_1 : ring α] [_inst_2 : @is_noetherian_ring α _inst_1] : @is_noetherian α α _inst_1 (@ring.to_add_comm_group α _inst_1) (@ring.to_module α _inst_1) := {}
@[instance] def ring.is_noetherian_of_fintype (R : Type) (M : Type) [_inst_1 : fintype M] [_inst_2 : ring R] [_inst_3 : add_comm_group M] [_inst_4 : @module R M _inst_2 _inst_3] : @is_noetherian R M _inst_2 _inst_3 _inst_4 := {}
@[instance] def normed_top_ring (α : Type) [_inst_1 : normed_ring α] : @topological_ring α (@uniform_space.to_topological_space α (@metric_space.to_uniform_space' α (@normed_ring.to_metric_space α _inst_1))) (@normed_ring.to_ring α _inst_1) := {}
class normed_field (α : Type) := (u:Unit:=())
@[instance] def normed_field.to_has_norm (α : Type) [c : normed_field α] : has_norm α := {}
@[instance] def normed_field.to_discrete_field (α : Type) [c : normed_field α] : discrete_field α := {}
@[instance] def normed_field.to_metric_space (α : Type) [c : normed_field α] : metric_space α := {}
class nondiscrete_normed_field (α : Type) := (u:Unit:=())
@[instance] def nondiscrete_normed_field.to_normed_field (α : Type) [c : nondiscrete_normed_field α] : normed_field α := {}
@[instance] def normed_field.to_normed_ring (α : Type) [i : normed_field α] : normed_ring α := {}
class ideal.is_principal (α : Type) [_inst_1 : comm_ring α] (S : Type) := (u:Unit:=())
class principal_ideal_domain (α : Type) := (u:Unit:=())
@[instance] def principal_ideal_domain.to_integral_domain (α : Type) [c : principal_ideal_domain α] : integral_domain α := {}
@[instance] def principal_ideal_domain.principal (α : Type) [c : principal_ideal_domain α] (S : Type) : @ideal.is_principal α (@nonzero_comm_ring.to_comm_ring α (@integral_domain.to_nonzero_comm_ring α (@principal_ideal_domain.to_integral_domain α c))) S := {}
class normed_space (α : Type) (β : Type) [_inst_1 : normed_field α] [_inst_2 : normed_group β] := (u:Unit:=())
@[instance] def normed_space.to_module (α : Type) (β : Type) [_inst_1 : normed_field α] [_inst_2 : normed_group β] [c : @normed_space α β _inst_1 _inst_2] : @module α β (@normed_ring.to_ring α (@normed_field.to_normed_ring α _inst_1)) (@normed_group.to_add_comm_group β _inst_2) := {}
@[instance] def normed_field.to_normed_space (α : Type) [_inst_1 : normed_field α] : @normed_space α α _inst_1 (@normed_ring.to_normed_group α (@normed_field.to_normed_ring α _inst_1)) := {}
@[instance] def euclidean_domain.to_principal_ideal_domain (α : Type) [_inst_1 : euclidean_domain α] : principal_ideal_domain α := {}
@[instance] def principal_ideal_domain.is_noetherian_ring (α : Type) [_inst_1 : principal_ideal_domain α] : @is_noetherian_ring α (@domain.to_ring α (@integral_domain.to_domain α (@principal_ideal_domain.to_integral_domain α _inst_1))) := {}
@[instance] def normed_space.topological_vector_space (α : Type) [_inst_1 : normed_field α] (E : Type) [_inst_3 : normed_group E] [_inst_4 : @normed_space α E _inst_1 _inst_3] : @topological_module α E (@domain.to_ring α (@division_ring.to_domain α (@field.to_division_ring α (@discrete_field.to_field α (@normed_field.to_discrete_field α _inst_1))))) (@uniform_space.to_topological_space α (@metric_space.to_uniform_space' α (@normed_field.to_metric_space α _inst_1))) (@uniform_space.to_topological_space E (@metric_space.to_uniform_space' E (@normed_group.to_metric_space E _inst_3))) (@normed_group.to_add_comm_group E _inst_3) (@normed_space.to_module α E _inst_1 _inst_3 _inst_4) := {}
class normed_algebra (𝕜 : Type) (𝕜' : Type) [_inst_1 : normed_field 𝕜] [_inst_2 : normed_ring 𝕜'] := (u:Unit:=())
@[instance] def normed_algebra.to_algebra (𝕜 : Type) (𝕜' : Type) [_inst_1 : normed_field 𝕜] [_inst_2 : normed_ring 𝕜'] [c : @normed_algebra 𝕜 𝕜' _inst_1 _inst_2] : @algebra 𝕜 𝕜' (@nonzero_comm_ring.to_comm_ring 𝕜 (@euclidean_domain.to_nonzero_comm_ring 𝕜 (@discrete_field.to_euclidean_domain 𝕜 (@normed_field.to_discrete_field 𝕜 _inst_1)))) (@normed_ring.to_ring 𝕜' _inst_2) := {}
@[instance] def borel (α : Type) [_inst_1 : topological_space α] : measurable_space α := {}
class measure_theory.measure.is_complete (α : Type) (_x : Type) (μ : Type) := (u:Unit:=())
class measure_theory.measure_space (α : Type) := (u:Unit:=())
@[instance] def measure_theory.measure_space.to_measurable_space (α : Type) [c : measure_theory.measure_space α] : measurable_space α := {}
class model_with_corners.boundaryless (𝕜 : Type) [_inst_1 : nondiscrete_normed_field 𝕜] (E : Type) [_inst_2 : normed_group E] [_inst_3 : @normed_space 𝕜 E (@nondiscrete_normed_field.to_normed_field 𝕜 _inst_1) _inst_2] (H : Type) [_inst_4 : topological_space H] (I : Type) := (u:Unit:=())
class smooth_manifold_with_corners (𝕜 : Type) [_inst_1 : nondiscrete_normed_field 𝕜] (E : Type) [_inst_2 : normed_group E] [_inst_3 : @normed_space 𝕜 E (@nondiscrete_normed_field.to_normed_field 𝕜 _inst_1) _inst_2] (H : Type) [_inst_4 : topological_space H] (I : Type) (M : Type) [_inst_5 : topological_space M] [_inst_6 : @manifold H _inst_4 M _inst_5] := (u:Unit:=())
@[instance] def model_space_smooth (𝕜 : Type) [_inst_1 : nondiscrete_normed_field 𝕜] (E : Type) [_inst_2 : normed_group E] [_inst_3 : @normed_space 𝕜 E (@nondiscrete_normed_field.to_normed_field 𝕜 _inst_1) _inst_2] (H : Type) [_inst_4 : topological_space H] (I : Type) : @smooth_manifold_with_corners 𝕜 _inst_1 E _inst_2 _inst_3 H _inst_4 I H _inst_4 (@manifold_model_space H _inst_4) := {}
class lt_class (α : Type) [_inst_1 : has_lt α] (x : Type) (y : Type) := (u:Unit:=())
@[instance] def tangent_space.topological_module (𝕜 : Type) [_inst_1 : nondiscrete_normed_field 𝕜] (E : Type) [_inst_2 : normed_group E] [_inst_3 : @normed_space 𝕜 E (@nondiscrete_normed_field.to_normed_field 𝕜 _inst_1) _inst_2] (H : Type) [_inst_4 : topological_space H] (I : Type) (M : Type) [_inst_5 : topological_space M] [_inst_6 : @manifold H _inst_4 M _inst_5] [_inst_7 : @smooth_manifold_with_corners 𝕜 _inst_1 E _inst_2 _inst_3 H _inst_4 I M _inst_5 _inst_6] (x : Type) : @topological_module 𝕜 E (@normed_ring.to_ring 𝕜 (@normed_field.to_normed_ring 𝕜 (@nondiscrete_normed_field.to_normed_field 𝕜 _inst_1))) (@uniform_space.to_topological_space 𝕜 (@metric_space.to_uniform_space' 𝕜 (@normed_field.to_metric_space 𝕜 (@nondiscrete_normed_field.to_normed_field 𝕜 _inst_1)))) (@uniform_space.to_topological_space E (@metric_space.to_uniform_space' E (@normed_group.to_metric_space E _inst_2))) (@normed_group.to_add_comm_group E _inst_2) (@normed_space.to_module 𝕜 E (@nondiscrete_normed_field.to_normed_field 𝕜 _inst_1) _inst_2 _inst_3) := {}
@[instance] def tangent_space.topological_space (𝕜 : Type) [_inst_1 : nondiscrete_normed_field 𝕜] (E : Type) [_inst_2 : normed_group E] [_inst_3 : @normed_space 𝕜 E (@nondiscrete_normed_field.to_normed_field 𝕜 _inst_1) _inst_2] (H : Type) [_inst_4 : topological_space H] (I : Type) (M : Type) [_inst_5 : topological_space M] [_inst_6 : @manifold H _inst_4 M _inst_5] [_inst_7 : @smooth_manifold_with_corners 𝕜 _inst_1 E _inst_2 _inst_3 H _inst_4 I M _inst_5 _inst_6] (x : Type) : topological_space E := {}
@[instance] def tangent_space.add_comm_group (𝕜 : Type) [_inst_1 : nondiscrete_normed_field 𝕜] (E : Type) [_inst_2 : normed_group E] [_inst_3 : @normed_space 𝕜 E (@nondiscrete_normed_field.to_normed_field 𝕜 _inst_1) _inst_2] (H : Type) [_inst_4 : topological_space H] (I : Type) (M : Type) [_inst_5 : topological_space M] [_inst_6 : @manifold H _inst_4 M _inst_5] [_inst_7 : @smooth_manifold_with_corners 𝕜 _inst_1 E _inst_2 _inst_3 H _inst_4 I M _inst_5 _inst_6] (x : Type) : add_comm_group E := {}
@[instance] def tangent_space.topological_add_group (𝕜 : Type) [_inst_1 : nondiscrete_normed_field 𝕜] (E : Type) [_inst_2 : normed_group E] [_inst_3 : @normed_space 𝕜 E (@nondiscrete_normed_field.to_normed_field 𝕜 _inst_1) _inst_2] (H : Type) [_inst_4 : topological_space H] (I : Type) (M : Type) [_inst_5 : topological_space M] [_inst_6 : @manifold H _inst_4 M _inst_5] [_inst_7 : @smooth_manifold_with_corners 𝕜 _inst_1 E _inst_2 _inst_3 H _inst_4 I M _inst_5 _inst_6] (x : Type) : @topological_add_group E (@tangent_space.topological_space 𝕜 _inst_1 E _inst_2 _inst_3 H _inst_4 I M _inst_5 _inst_6 _inst_7 x) (@add_comm_group.to_add_group E (@tangent_space.add_comm_group 𝕜 _inst_1 E _inst_2 _inst_3 H _inst_4 I M _inst_5 _inst_6 _inst_7 x)) := {}
@[instance] def tangent_space.vector_space (𝕜 : Type) [_inst_1 : nondiscrete_normed_field 𝕜] (E : Type) [_inst_2 : normed_group E] [_inst_3 : @normed_space 𝕜 E (@nondiscrete_normed_field.to_normed_field 𝕜 _inst_1) _inst_2] (H : Type) [_inst_4 : topological_space H] (I : Type) (M : Type) [_inst_5 : topological_space M] [_inst_6 : @manifold H _inst_4 M _inst_5] [_inst_7 : @smooth_manifold_with_corners 𝕜 _inst_1 E _inst_2 _inst_3 H _inst_4 I M _inst_5 _inst_6] (x : Type) : @module 𝕜 E (@domain.to_ring 𝕜 (@division_ring.to_domain 𝕜 (@field.to_division_ring 𝕜 (@discrete_field.to_field 𝕜 (@normed_field.to_discrete_field 𝕜 (@nondiscrete_normed_field.to_normed_field 𝕜 _inst_1)))))) (@tangent_space.add_comm_group 𝕜 _inst_1 E _inst_2 _inst_3 H _inst_4 I M _inst_5 _inst_6 _inst_7 x) := {}
class has_inner (α : Type) := (u:Unit:=())
class inner_product_space (α : Type) := (u:Unit:=())
@[instance] def inner_product_space.to_add_comm_group (α : Type) [c : inner_product_space α] : add_comm_group α := {}
@[instance] def inner_product_space.to_has_inner (α : Type) [c : inner_product_space α] : has_inner α := {}
@[instance] def inner_product_space_has_norm (α : Type) [_inst_1 : inner_product_space α] : has_norm α := {}
@[instance] def inner_product_space_is_normed_group (α : Type) [_inst_1 : inner_product_space α] : normed_group α := {}
end test
