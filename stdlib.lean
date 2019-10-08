noncomputable theory
namespace test
class {} decidable (p : Prop)
class {u} has_zero (α : Type.{u})
class {u} has_one (α : Type.{u})
class {u} has_add (α : Type.{u})
class {u} has_mul (α : Type.{u})
class {u} has_inv (α : Type.{u})
class {u} has_neg (α : Type.{u})
class {u} has_sub (α : Type.{u})
class {u} has_div (α : Type.{u})
class {u} has_dvd (α : Type.{u})
class {u} has_mod (α : Type.{u})
class {u} has_le (α : Type.{u})
class {u} has_lt (α : Type.{u})
class {u} has_append (α : Type.{u})
class {u v w} has_andthen (α : Type.{u}) (β : Type.{v}) (σ : Type.{w})
class {u} has_union (α : Type.{u})
class {u} has_inter (α : Type.{u})
class {u} has_sdiff (α : Type.{u})
class {u} has_equiv (α : Sort.{u})
class {u} has_subset (α : Type.{u})
class {u} has_ssubset (α : Type.{u})
class {u} has_emptyc (α : Type.{u})
class {u v} has_insert (α : Type.{u}) (γ : Type.{v})
class {u v} has_sep (α : Type.{u}) (γ : Type.{v})
class {u v} has_mem (α : Type.{u}) (γ : Type.{v})
class {u v} has_pow (α : Type.{u}) (β : Type.{v})
constant {} nat : Type
@[instance] constant {} nat.has_zero  : has_zero.{0} nat
@[instance] constant {} nat.has_one  : has_one.{0} nat
@[instance] constant {} nat.has_add  : has_add.{0} nat
def {} p1 : has_one.{0} nat := infer_instance
def {} p2 : has_add.{0} nat := infer_instance
class {u} has_sizeof (α : Sort.{u})
def {} p3 : has_zero.{0} nat := infer_instance
constant {} true : Prop
@[instance] constant {} decidable.true  : decidable true
constant {} false : Prop
@[instance] constant {} decidable.false  : decidable false
constant {} and : Prop -> Prop -> Prop
@[instance] constant {} and.decidable (p : Prop) (q : Prop) [_inst_1 : decidable p] [_inst_2 : decidable q] : decidable (and p q)
constant {} or : Prop -> Prop -> Prop
@[instance] constant {} or.decidable (p : Prop) (q : Prop) [_inst_1 : decidable p] [_inst_2 : decidable q] : decidable (or p q)
constant {} not : Prop -> Prop
@[instance] constant {} not.decidable (p : Prop) [_inst_1 : decidable p] : decidable (not p)
@[instance] constant {} implies.decidable (p : Prop) (q : Prop) [_inst_1 : decidable p] [_inst_2 : decidable q] : decidable (p -> q)
constant {} iff : Prop -> Prop -> Prop
@[instance] constant {} iff.decidable (p : Prop) (q : Prop) [_inst_1 : decidable p] [_inst_2 : decidable q] : decidable (iff p q)
constant {} xor : Prop -> Prop -> Prop
@[instance] constant {} xor.decidable (p : Prop) (q : Prop) [_inst_1 : decidable p] [_inst_2 : decidable q] : decidable (xor p q)
constant {u} Exists : Pi (α : Sort.{u}) (p : α -> Prop), Prop
@[instance] constant {} exists_prop_decidable (p : Prop) (P : p -> Prop) [Dp : decidable p] [DP : Pi (h : p), (decidable (P h))] : decidable (Exists.{0} p P)
@[instance] constant {} forall_prop_decidable (p : Prop) (P : p -> Prop) [Dp : decidable p] [DP : Pi (h : p), (decidable (P h))] : decidable (Pi (h : p), (P h))
def {} p4 : decidable false := infer_instance
constant {u} eq : Pi (α : Sort.{u}) (a : α) (a : α), Prop
@[instance] constant {u} ne.decidable (α : Sort.{u}) [_inst_1 : Pi (a : α) (b : α), (decidable (eq.{u} α a b))] (a : α) (b : α) : decidable (not (eq.{u} α a b))
constant {} bool : Type
@[instance] constant {} bool.decidable_eq (a : bool) (b : bool) : decidable (eq.{1} bool a b)
class {u} inhabited (α : Sort.{u})
@[instance] constant {} prop.inhabited  : inhabited.{1} Prop
@[instance] constant {u v} fun.inhabited (α : Sort.{u}) (β : Sort.{v}) [h : inhabited.{v} β] : inhabited.{(imax u v)} (α -> β)
@[instance] constant {u v} pi.inhabited (α : Sort.{u}) (β : α -> Sort.{v}) [_inst_1 : Pi (x : α), (inhabited.{v} (β x))] : inhabited.{(imax u v)} (Pi (x : α), (β x))
@[instance] constant {} bool.inhabited  : inhabited.{1} bool
@[instance] constant {} true.inhabited  : inhabited.{0} true
class {u} nonempty (α : Sort.{u})
@[instance] constant {u} nonempty_of_inhabited (α : Sort.{u}) [_inst_1 : inhabited.{u} α] : nonempty.{u} α
class {u} subsingleton (α : Sort.{u})
@[instance] constant {} subsingleton_prop (p : Prop) : subsingleton.{0} p
@[instance] constant {} decidable.subsingleton (p : Prop) : subsingleton.{1} (decidable p)
constant {u} ite : Pi (c : Prop) (h : decidable c) (α : Sort.{u}) (t : α) (e : α), α
@[instance] constant {} ite.decidable (c : Prop) (t : Prop) (e : Prop) [d_c : decidable c] [d_t : decidable t] [d_e : decidable e] : decidable (ite.{1} c d_c Prop t e)
constant {u} dite : Pi (c : Prop) (h : decidable c) (α : Sort.{u}) (a : c -> α) (a : (not c) -> α), α
@[instance] constant {} dite.decidable (c : Prop) (t : c -> Prop) (e : (not c) -> Prop) [d_c : decidable c] [d_t : Pi (h : c), (decidable (t h))] [d_e : Pi (h : not c), (decidable (e h))] : decidable (dite.{1} c d_c Prop t e)
constant {u v} prod : Type.{u} -> Type.{v} -> Sort.{max (u+1) (v+1)}
@[instance] constant {u v} prod.inhabited (α : Type.{u}) (β : Type.{v}) [_inst_1 : inhabited.{u+1} α] [_inst_2 : inhabited.{v+1} β] : inhabited.{(max (u+1) (v+1))} (prod.{u v} α β)
@[instance] constant {u v} prod.decidable_eq (α : Type.{u}) (β : Type.{v}) [h₁ : Pi (a : α) (b : α), (decidable (eq.{u+1} α a b))] [h₂ : Pi (a : β) (b : β), (decidable (eq.{v+1} β a b))] (a : prod.{u v} α β) (b : prod.{u v} α β) : decidable (eq.{(max (u+1) (v+1))} (prod.{u v} α β) a b)
@[instance] constant {u v} prod.has_lt (α : Type.{u}) (β : Type.{v}) [_inst_1 : has_lt.{u} α] [_inst_2 : has_lt.{v} β] : has_lt.{(max u v)} (prod.{u v} α β)
constant {u} has_lt.lt : Pi (α : Type.{u}) (c : has_lt.{u} α) (a : α) (a : α), Prop
@[instance] constant {u v} prod_has_decidable_lt (α : Type.{u}) (β : Type.{v}) [_inst_1 : has_lt.{u} α] [_inst_2 : has_lt.{v} β] [_inst_3 : Pi (a : α) (b : α), (decidable (eq.{u+1} α a b))] [_inst_4 : Pi (a : β) (b : β), (decidable (eq.{v+1} β a b))] [_inst_5 : Pi (a : α) (b : α), (decidable (has_lt.lt.{u} α _inst_1 a b))] [_inst_6 : Pi (a : β) (b : β), (decidable (has_lt.lt.{v} β _inst_2 a b))] (s : prod.{u v} α β) (t : prod.{u v} α β) : decidable (has_lt.lt.{(max u v)} (prod.{u v} α β) (prod.has_lt.{u v} α β _inst_1 _inst_2) s t)
@[instance] constant {} nat.has_le  : has_le.{0} nat
@[instance] constant {} nat.has_lt  : has_lt.{0} nat
@[instance] constant {} nat.has_sub  : has_sub.{0} nat
@[instance] constant {} nat.has_mul  : has_mul.{0} nat
@[instance] constant {} nat.decidable_eq (a : nat) (b : nat) : decidable (eq.{1} nat a b)
@[instance] constant {} nat.inhabited  : inhabited.{1} nat
def {} p5 : has_le.{0} nat := infer_instance
def {} p6 : has_lt.{0} nat := infer_instance
constant {u} has_le.le : Pi (α : Type.{u}) (c : has_le.{u} α) (a : α) (a : α), Prop
@[instance] constant {} nat.decidable_le (a : nat) (b : nat) : decidable (has_le.le.{0} nat nat.has_le a b)
@[instance] constant {} nat.decidable_lt (a : nat) (b : nat) : decidable (has_lt.lt.{0} nat nat.has_lt a b)
def {} p7 : has_sub.{0} nat := infer_instance
def {} p8 : has_mul.{0} nat := infer_instance
@[instance] constant {} nat.has_pow  : has_pow.{0 0} nat nat
def {} p9 : has_pow.{0 0} nat nat := infer_instance
class {u} has_well_founded (α : Sort.{u})
@[instance] constant {u} has_well_founded_of_has_sizeof (α : Sort.{u}) [_inst_1 : has_sizeof.{u} α] : has_well_founded.{u} α
@[instance] constant {u v} prod.has_well_founded (α : Type.{u}) (β : Type.{v}) [s₁ : has_well_founded.{u+1} α] [s₂ : has_well_founded.{v+1} β] : has_well_founded.{(max (u+1) (v+1))} (prod.{u v} α β)
class {u} setoid (α : Sort.{u})
@[instance] constant {u} setoid_has_equiv (α : Sort.{u}) [_inst_1 : setoid.{u} α] : has_equiv.{u} α
constant {u} has_equiv.equiv : Pi (α : Sort.{u}) (c : has_equiv.{u} α) (a : α) (a : α), Prop
constant {u} quotient : Pi (α : Sort.{u}) (s : setoid.{u} α), Sort.{u}
@[instance] constant {u} quotient.decidable_eq (α : Sort.{u}) (s : setoid.{u} α) [d : Pi (a : α) (b : α), (decidable (has_equiv.equiv.{u} α (setoid_has_equiv.{u} α s) a b))] (a : quotient.{u} α s) (b : quotient.{u} α s) : decidable (eq.{u} (quotient.{u} α s) a b)
@[instance] constant {u v} pi.subsingleton (α : Sort.{u}) (β : α -> Sort.{v}) [_inst_1 : Pi (a : α), (subsingleton.{v} (β a))] : subsingleton.{(imax u v)} (Pi (a : α), (β a))
constant {u} list : Type.{u} -> Type.{u}
@[instance] constant {u} list.inhabited (α : Type.{u}) : inhabited.{u+1} (list.{u} α)
@[instance] constant {u} list.decidable_eq (α : Type.{u}) [_inst_1 : Pi (a : α) (b : α), (decidable (eq.{u+1} α a b))] (a : list.{u} α) (b : list.{u} α) : decidable (eq.{u+1} (list.{u} α) a b)
@[instance] constant {u} list.has_append (α : Type.{u}) : has_append.{u} (list.{u} α)
@[instance] constant {u} list.has_mem (α : Type.{u}) : has_mem.{u u} α (list.{u} α)
constant {u v} has_mem.mem : Pi (α : Type.{u}) (γ : Type.{v}) (c : has_mem.{u v} α γ) (a : α) (a : γ), Prop
@[instance] constant {u} list.decidable_mem (α : Type.{u}) [_inst_1 : Pi (a : α) (b : α), (decidable (eq.{u+1} α a b))] (a : α) (l : list.{u} α) : decidable (has_mem.mem.{u u} α (list.{u} α) (list.has_mem.{u} α) a l)
@[instance] constant {u} list.has_emptyc (α : Type.{u}) : has_emptyc.{u} (list.{u} α)
@[instance] constant {u} list.has_insert (α : Type.{u}) [_inst_1 : Pi (a : α) (b : α), (decidable (eq.{u+1} α a b))] : has_insert.{u u} α (list.{u} α)
@[instance] constant {u} list.has_union (α : Type.{u}) [_inst_1 : Pi (a : α) (b : α), (decidable (eq.{u+1} α a b))] : has_union.{u} (list.{u} α)
@[instance] constant {u} list.has_inter (α : Type.{u}) [_inst_1 : Pi (a : α) (b : α), (decidable (eq.{u+1} α a b))] : has_inter.{u} (list.{u} α)
@[instance] constant {u} list.has_lt (α : Type.{u}) [_inst_1 : has_lt.{u} α] : has_lt.{u} (list.{u} α)
@[instance] constant {u} list.has_decidable_lt (α : Type.{u}) [_inst_1 : has_lt.{u} α] [h : Pi (a : α) (b : α), (decidable (has_lt.lt.{u} α _inst_1 a b))] (l₁ : list.{u} α) (l₂ : list.{u} α) : decidable (has_lt.lt.{u} (list.{u} α) (list.has_lt.{u} α _inst_1) l₁ l₂)
@[instance] constant {u} list.has_le (α : Type.{u}) [_inst_1 : has_lt.{u} α] : has_le.{u} (list.{u} α)
@[instance] constant {u} list.has_decidable_le (α : Type.{u}) [_inst_1 : has_lt.{u} α] [h : Pi (a : α) (b : α), (decidable (has_lt.lt.{u} α _inst_1 a b))] (l₁ : list.{u} α) (l₂ : list.{u} α) : decidable (has_le.le.{u} (list.{u} α) (list.has_le.{u} α _inst_1) l₁ l₂)
constant {} char : Type
@[instance] constant {} char.has_lt  : has_lt.{0} char
@[instance] constant {} char.has_le  : has_le.{0} char
def {} p10 : has_lt.{0} char := infer_instance
@[instance] constant {} char.decidable_lt (a : char) (b : char) : decidable (has_lt.lt.{0} char char.has_lt a b)
def {} p11 : has_le.{0} char := infer_instance
@[instance] constant {} char.decidable_le (a : char) (b : char) : decidable (has_le.le.{0} char char.has_le a b)
@[instance] constant {} char.decidable_eq (a : char) (b : char) : decidable (eq.{1} char a b)
@[instance] constant {} char.inhabited  : inhabited.{1} char
def {} p12 : has_lt.{0} (list.{0} char) := infer_instance
constant {} string : Type
@[instance] constant {} string.has_lt  : has_lt.{0} string
def {} p13 : has_lt.{0} string := infer_instance
def {} p14 : Pi (a : char) (b : char), (decidable (has_lt.lt.{0} char char.has_lt a b)) := infer_instance
@[instance] constant {} string.has_decidable_lt (s₁ : string) (s₂ : string) : decidable (has_lt.lt.{0} string string.has_lt s₁ s₂)
def {} p15 : has_append.{0} (list.{0} char) := infer_instance
def {} p16 : inhabited.{1} char := infer_instance
@[instance] constant {} string.inhabited  : inhabited.{1} string
@[instance] constant {} string.has_append  : has_append.{0} string
def {} p17 : has_append.{0} string := infer_instance
constant {u} subtype : Pi (α : Sort.{u}) (p : α -> Prop), Sort.{max 1 u}
@[instance] constant {u} subtype.inhabited (α : Type.{u}) (p : α -> Prop) (a : α) (h : p a) : inhabited.{(max 1 (u+1))} (subtype.{u+1} α p)
constant {} fin : nat -> Type
@[instance] constant {} fin.has_lt (n : nat) : has_lt.{0} (fin n)
@[instance] constant {} fin.has_le (n : nat) : has_le.{0} (fin n)
@[instance] constant {} fin.decidable_lt (n : nat) (a : fin n) (b : fin n) : decidable (has_lt.lt.{0} (fin n) (fin.has_lt n) a b)
@[instance] constant {} fin.decidable_le (n : nat) (a : fin n) (b : fin n) : decidable (has_le.le.{0} (fin n) (fin.has_le n) a b)
@[instance] constant {} fin.decidable_eq (n : nat) (a : fin n) (b : fin n) : decidable (eq.{1} (fin n) a b)
constant {} unsigned : Type
@[instance] constant {} unsigned.decidable_eq (a : unsigned) (b : unsigned) : decidable (eq.{1} unsigned a b)
constant {u v} sum : Type.{u} -> Type.{v} -> Sort.{max (u+1) (v+1)}
@[instance] constant {u v} sum.inhabited_left (α : Type.{u}) (β : Type.{v}) [h : inhabited.{u+1} α] : inhabited.{(max (u+1) (v+1))} (sum.{u v} α β)
@[instance] constant {u v} sum.inhabited_right (α : Type.{u}) (β : Type.{v}) [h : inhabited.{v+1} β] : inhabited.{(max (u+1) (v+1))} (sum.{u v} α β)
@[instance] constant {} nat.has_div  : has_div.{0} nat
def {} p18 : has_div.{0} nat := infer_instance
@[instance] constant {} nat.has_mod  : has_mod.{0} nat
def {} p19 : has_mod.{0} nat := infer_instance
class {u} has_repr (α : Type.{u})
@[instance] constant {} bool.has_repr  : has_repr.{0} bool
@[instance] constant {} decidable.has_repr (p : Prop) : has_repr.{0} (decidable p)
@[instance] constant {u} list.has_repr (α : Type.{u}) [_inst_1 : has_repr.{u} α] : has_repr.{u} (list.{u} α)
constant {u} punit : Sort.{u}
@[instance] constant {} unit.has_repr  : has_repr.{0} punit.{1}
constant {u} option : Type.{u} -> Type.{u}
@[instance] constant {u} option.has_repr (α : Type.{u}) [_inst_1 : has_repr.{u} α] : has_repr.{u} (option.{u} α)
@[instance] constant {u v} sum.has_repr (α : Type.{u}) (β : Type.{v}) [_inst_1 : has_repr.{u} α] [_inst_2 : has_repr.{v} β] : has_repr.{(max u v)} (sum.{u v} α β)
@[instance] constant {u v} prod.has_repr (α : Type.{u}) (β : Type.{v}) [_inst_1 : has_repr.{u} α] [_inst_2 : has_repr.{v} β] : has_repr.{(max u v)} (prod.{u v} α β)
constant {u v} sigma : Pi (α : Type.{u}) (β : α -> Type.{v}), Sort.{max (u+1) (v+1)}
@[instance] constant {u v} sigma.has_repr (α : Type.{u}) (β : α -> Type.{v}) [_inst_1 : has_repr.{u} α] [s : Pi (x : α), (has_repr.{v} (β x))] : has_repr.{(max u v)} (sigma.{u v} α β)
@[instance] constant {u} subtype.has_repr (α : Type.{u}) (p : α -> Prop) [_inst_1 : has_repr.{u} α] : has_repr.{u} (subtype.{u+1} α p)
@[instance] constant {} nat.has_repr  : has_repr.{0} nat
@[instance] constant {} char.has_repr  : has_repr.{0} char
@[instance] constant {} string.has_repr  : has_repr.{0} string
def {} p20 : has_repr.{0} nat := infer_instance
@[instance] constant {} fin.has_repr (n : nat) : has_repr.{0} (fin n)
@[instance] constant {} unsigned.has_repr  : has_repr.{0} unsigned
def {} p21 : has_repr.{0} char := infer_instance
constant {} ordering : Type
@[instance] constant {} ordering.has_repr  : has_repr.{0} ordering
@[instance] constant {} ordering.decidable_eq (a : ordering) (b : ordering) : decidable (eq.{1} ordering a b)
class {u v} has_lift (a : Sort.{u}) (b : Sort.{v})
class {u v} has_lift_t (a : Sort.{u}) (b : Sort.{v})
class {u v} has_coe (a : Sort.{u}) (b : Sort.{v})
class {u v} has_coe_t (a : Sort.{u}) (b : Sort.{v})
class {u v} has_coe_to_fun (a : Sort.{u})
class {u v} has_coe_to_sort (a : Sort.{u})
@[instance] constant {u₁ u₂ u₃} lift_trans (a : Sort.{u₁}) (b : Sort.{u₂}) (c : Sort.{u₃}) [_inst_1 : has_lift.{u₁ u₂} a b] [_inst_2 : has_lift_t.{u₂ u₃} b c] : has_lift_t.{u₁ u₃} a c
@[instance] constant {u v} lift_base (a : Sort.{u}) (b : Sort.{v}) [_inst_1 : has_lift.{u v} a b] : has_lift_t.{u v} a b
@[instance] constant {u₁ u₂ u₃} coe_trans (a : Sort.{u₁}) (b : Sort.{u₂}) (c : Sort.{u₃}) [_inst_1 : has_coe.{u₁ u₂} a b] [_inst_2 : has_coe_t.{u₂ u₃} b c] : has_coe_t.{u₁ u₃} a c
@[instance] constant {u v} coe_base (a : Sort.{u}) (b : Sort.{v}) [_inst_1 : has_coe.{u v} a b] : has_coe_t.{u v} a b
@[instance] constant {u} coe_option (a : Type.{u}) : has_coe_t.{u+1 u+1} a (option.{u} a)
class {u v} has_coe_t_aux (a : Sort.{u}) (b : Sort.{v})
@[instance] constant {u₁ u₂ u₃} coe_trans_aux (a : Sort.{u₁}) (b : Sort.{u₂}) (c : Sort.{u₃}) [_inst_1 : has_coe.{u₁ u₂} a b] [_inst_2 : has_coe_t_aux.{u₂ u₃} b c] : has_coe_t_aux.{u₁ u₃} a c
@[instance] constant {u v} coe_base_aux (a : Sort.{u}) (b : Sort.{v}) [_inst_1 : has_coe.{u v} a b] : has_coe_t_aux.{u v} a b
@[instance] constant {u₁ u₂ u₃} coe_fn_trans (a : Sort.{u₁}) (b : Sort.{u₂}) [_inst_1 : has_coe_t_aux.{u₁ u₂} a b] [_inst_2 : has_coe_to_fun.{u₂ u₃} b] : has_coe_to_fun.{u₁ u₃} a
@[instance] constant {u₁ u₂ u₃} coe_sort_trans (a : Sort.{u₁}) (b : Sort.{u₂}) [_inst_1 : has_coe_t_aux.{u₁ u₂} a b] [_inst_2 : has_coe_to_sort.{u₂ u₃} b] : has_coe_to_sort.{u₁ u₃} a
@[instance] constant {u v} coe_to_lift (a : Sort.{u}) (b : Sort.{v}) [_inst_1 : has_coe_t.{u v} a b] : has_lift_t.{u v} a b
@[instance] constant {} coe_bool_to_Prop  : has_coe.{1 1} bool Prop
@[instance] constant {} coe_sort_bool  : has_coe_to_sort.{1 1} bool
def {} p22 : has_lift_t.{1 1} bool Prop := infer_instance
constant {u v} lift_t : Pi (a : Sort.{u}) (b : Sort.{v}) (_inst_1 : has_lift_t.{u v} a b) (a : a), b
@[instance] constant {} coe_decidable_eq (x : bool) : decidable (lift_t.{1 1} bool Prop (coe_to_lift.{1 1} bool Prop (coe_base.{1 1} bool Prop coe_bool_to_Prop)) x)
@[instance] constant {u} coe_subtype (a : Sort.{u}) (p : a -> Prop) : has_coe.{(max 1 u) u} (subtype.{u} a p) a
@[instance] constant {ua₁ ua₂ ub₁ ub₂} lift_fn (a₁ : Sort.{ua₁}) (a₂ : Sort.{ua₂}) (b₁ : Sort.{ub₁}) (b₂ : Sort.{ub₂}) [_inst_1 : has_lift.{ua₂ ua₁} a₂ a₁] [_inst_2 : has_lift_t.{ub₁ ub₂} b₁ b₂] : has_lift.{(imax ua₁ ub₁) (imax ua₂ ub₂)} (a₁ -> b₁) (a₂ -> b₂)
@[instance] constant {ua ub₁ ub₂} lift_fn_range (a : Sort.{ua}) (b₁ : Sort.{ub₁}) (b₂ : Sort.{ub₂}) [_inst_1 : has_lift_t.{ub₁ ub₂} b₁ b₂] : has_lift.{(imax ua ub₁) (imax ua ub₂)} (a -> b₁) (a -> b₂)
@[instance] constant {ua₁ ua₂ ub} lift_fn_dom (a₁ : Sort.{ua₁}) (a₂ : Sort.{ua₂}) (b : Sort.{ub}) [_inst_1 : has_lift.{ua₂ ua₁} a₂ a₁] : has_lift.{(imax ua₁ ub) (imax ua₂ ub)} (a₁ -> b) (a₂ -> b)
@[instance] constant {ua₁ ub₁ ub₂} lift_pair (a₁ : Type.{ua₁}) (a₂ : Type.{ub₂}) (b₁ : Type.{ub₁}) (b₂ : Type.{ub₂}) [_inst_1 : has_lift_t.{ua₁+1 ub₂+1} a₁ a₂] [_inst_2 : has_lift_t.{ub₁+1 ub₂+1} b₁ b₂] : has_lift.{(max (ua₁+1) (ub₁+1)) ub₂+1} (prod.{ua₁ ub₁} a₁ b₁) (prod.{ub₂ ub₂} a₂ b₂)
@[instance] constant {ua₁ ua₂ ub} lift_pair₁ (a₁ : Type.{ua₁}) (a₂ : Type.{ua₂}) (b : Type.{ub}) [_inst_1 : has_lift_t.{ua₁+1 ua₂+1} a₁ a₂] : has_lift.{(max (ua₁+1) (ub+1)) (max (ua₂+1) (ub+1))} (prod.{ua₁ ub} a₁ b) (prod.{ua₂ ub} a₂ b)
@[instance] constant {ua ub₁ ub₂} lift_pair₂ (a : Type.{ua}) (b₁ : Type.{ub₁}) (b₂ : Type.{ub₂}) [_inst_1 : has_lift_t.{ub₁+1 ub₂+1} b₁ b₂] : has_lift.{(max (ua+1) (ub₁+1)) (max (ua+1) (ub₂+1))} (prod.{ua ub₁} a b₁) (prod.{ua ub₂} a b₂)
@[instance] constant {u v} lift_list (a : Type.{u}) (b : Type.{v}) [_inst_1 : has_lift_t.{u+1 v+1} a b] : has_lift.{u+1 v+1} (list.{u} a) (list.{v} b)
class {u} has_to_string (α : Type.{u})
@[instance] constant {} string.has_to_string  : has_to_string.{0} string
@[instance] constant {} bool.has_to_string  : has_to_string.{0} bool
@[instance] constant {} decidable.has_to_string (p : Prop) : has_to_string.{0} (decidable p)
@[instance] constant {u} list.has_to_string (α : Type.{u}) [_inst_1 : has_to_string.{u} α] : has_to_string.{u} (list.{u} α)
@[instance] constant {} unit.has_to_string  : has_to_string.{0} punit.{1}
@[instance] constant {} nat.has_to_string  : has_to_string.{0} nat
@[instance] constant {} char.has_to_string  : has_to_string.{0} char
def {} p23 : has_to_string.{0} nat := infer_instance
@[instance] constant {} fin.has_to_string (n : nat) : has_to_string.{0} (fin n)
@[instance] constant {} unsigned.has_to_string  : has_to_string.{0} unsigned
@[instance] constant {u} option.has_to_string (α : Type.{u}) [_inst_1 : has_to_string.{u} α] : has_to_string.{u} (option.{u} α)
@[instance] constant {u v} sum.has_to_string (α : Type.{u}) (β : Type.{v}) [_inst_1 : has_to_string.{u} α] [_inst_2 : has_to_string.{v} β] : has_to_string.{(max u v)} (sum.{u v} α β)
@[instance] constant {u v} prod.has_to_string (α : Type.{u}) (β : Type.{v}) [_inst_1 : has_to_string.{u} α] [_inst_2 : has_to_string.{v} β] : has_to_string.{(max u v)} (prod.{u v} α β)
@[instance] constant {u v} sigma.has_to_string (α : Type.{u}) (β : α -> Type.{v}) [_inst_1 : has_to_string.{u} α] [s : Pi (x : α), (has_to_string.{v} (β x))] : has_to_string.{(max u v)} (sigma.{u v} α β)
@[instance] constant {u} subtype.has_to_string (α : Type.{u}) (p : α -> Prop) [_inst_1 : has_to_string.{u} α] : has_to_string.{u} (subtype.{u+1} α p)
constant {} name : Type
@[instance] constant {} name.inhabited  : inhabited.{1} name
@[instance] constant {} string_to_name  : has_coe.{1 1} string name
def {} p24 : has_repr.{0} unsigned := infer_instance
@[instance] constant {} name.has_to_string  : has_to_string.{0} name
constant {} name.lt : name -> name -> Prop
@[instance] constant {} name.lt.decidable_rel (a : name) (b : name) : decidable (name.lt a b)
@[instance] constant {} name.has_lt  : has_lt.{0} name
@[instance] constant {} name.has_decidable_eq (a : name) (b : name) : decidable (eq.{1} name a b)
@[instance] constant {} name.has_append  : has_append.{0} name
class {u v} functor (f : Type.{u} -> Type.{v})
class {u v} has_pure (f : Type.{u} -> Type.{v})
class {u v} has_seq (f : Type.{u} -> Type.{v})
class {u v} has_seq_left (f : Type.{u} -> Type.{v})
class {u v} has_seq_right (f : Type.{u} -> Type.{v})
class {u v} applicative (f : Type.{u} -> Type.{v})
@[instance] constant {u v} applicative.to_functor (f : Type.{u} -> Type.{v}) [c : applicative.{u v} f] : functor.{u v} f
@[instance] constant {u v} applicative.to_has_pure (f : Type.{u} -> Type.{v}) [c : applicative.{u v} f] : has_pure.{u v} f
@[instance] constant {u v} applicative.to_has_seq (f : Type.{u} -> Type.{v}) [c : applicative.{u v} f] : has_seq.{u v} f
@[instance] constant {u v} applicative.to_has_seq_left (f : Type.{u} -> Type.{v}) [c : applicative.{u v} f] : has_seq_left.{u v} f
@[instance] constant {u v} applicative.to_has_seq_right (f : Type.{u} -> Type.{v}) [c : applicative.{u v} f] : has_seq_right.{u v} f
class {u v} has_orelse (f : Type.{u} -> Type.{v})
class {u v} alternative (f : Type.{u} -> Type.{v})
@[instance] constant {u v} alternative.to_applicative (f : Type.{u} -> Type.{v}) [c : alternative.{u v} f] : applicative.{u v} f
@[instance] constant {u v} alternative.to_has_orelse (f : Type.{u} -> Type.{v}) [c : alternative.{u v} f] : has_orelse.{u v} f
class {u v} has_bind (m : Type.{u} -> Type.{v})
class {u v} monad (m : Type.{u} -> Type.{v})
@[instance] constant {u v} monad.to_applicative (m : Type.{u} -> Type.{v}) [c : monad.{u v} m] : applicative.{u v} m
@[instance] constant {u v} monad.to_has_bind (m : Type.{u} -> Type.{v}) [c : monad.{u v} m] : has_bind.{u v} m
class {u v w} has_monad_lift (m : Type.{u} -> Type.{v}) (n : Type.{u} -> Type.{w})
class {u v w} has_monad_lift_t (m : Type.{u} -> Type.{v}) (n : Type.{u} -> Type.{w})
@[instance] constant {u_1 u_2 u_3 u_4} has_monad_lift_t_trans (m : Type.{u_1} -> Type.{u_2}) (n : Type.{u_1} -> Type.{u_3}) (o : Type.{u_1} -> Type.{u_4}) [_inst_1 : has_monad_lift.{u_1 u_3 u_4} n o] [_inst_2 : has_monad_lift_t.{u_1 u_2 u_3} m n] : has_monad_lift_t.{u_1 u_2 u_4} m o
@[instance] constant {u_1 u_2} has_monad_lift_t_refl (m : Type.{u_1} -> Type.{u_2}) : has_monad_lift_t.{u_1 u_2 u_2} m m
class {u v w} monad_functor (m : Type.{u} -> Type.{v}) (m' : Type.{u} -> Type.{v}) (n : Type.{u} -> Type.{w}) (n' : Type.{u} -> Type.{w})
class {u v w} monad_functor_t (m : Type.{u} -> Type.{v}) (m' : Type.{u} -> Type.{v}) (n : Type.{u} -> Type.{w}) (n' : Type.{u} -> Type.{w})
@[instance] constant {u_1 u_2 u_3 u_4} monad_functor_t_trans (m : Type.{u_1} -> Type.{u_2}) (m' : Type.{u_1} -> Type.{u_2}) (n : Type.{u_1} -> Type.{u_3}) (n' : Type.{u_1} -> Type.{u_3}) (o : Type.{u_1} -> Type.{u_4}) (o' : Type.{u_1} -> Type.{u_4}) [_inst_1 : monad_functor.{u_1 u_3 u_4} n n' o o'] [_inst_2 : monad_functor_t.{u_1 u_2 u_3} m m' n n'] : monad_functor_t.{u_1 u_2 u_4} m m' o o'
@[instance] constant {u_1 u_2} monad_functor_t_refl (m : Type.{u_1} -> Type.{u_2}) (m' : Type.{u_1} -> Type.{u_2}) : monad_functor_t.{u_1 u_2 u_2} m m' m m'
class {u v} monad_run (out : Type.{u} -> Type.{v}) (m : Type.{u} -> Type.{v})
def {} p25 : has_coe_to_sort.{1 1} bool := infer_instance
@[instance] constant {u_1} option.monad  : monad.{u_1 u_1} option.{u_1}
def {u_1} p26 : has_pure.{u_1 u_1} option.{u_1} := infer_instance
def {u_1} p27 : has_seq.{u_1 u_1} option.{u_1} := infer_instance
@[instance] constant {u_1} option.alternative  : alternative.{u_1 u_1} option.{u_1}
@[instance] constant {u} option.inhabited (α : Type.{u}) : inhabited.{u+1} (option.{u} α)
@[instance] constant {u} option.decidable_eq (α : Type.{u}) [d : Pi (a : α) (b : α), (decidable (eq.{u+1} α a b))] (a : option.{u} α) (b : option.{u} α) : decidable (eq.{u+1} (option.{u} α) a b)
constant {} options : Type
@[instance] constant {} options.has_decidable_eq (a : options) (b : options) : decidable (eq.{1} options a b)
@[instance] constant {} options.has_add  : has_add.{0} options
@[instance] constant {} options.inhabited  : inhabited.{1} options
constant {} format : Type
@[instance] constant {} format.inhabited  : inhabited.{1} format
@[instance] constant {} format.has_append  : has_append.{0} format
@[instance] constant {} format.has_to_string  : has_to_string.{0} format
class {u} has_to_format (α : Type.{u})
@[instance] constant {} format.has_to_format  : has_to_format.{0} format
@[instance] constant {} nat_to_format  : has_coe.{1 1} nat format
@[instance] constant {} string_to_format  : has_coe.{1 1} string format
def {} p28 : has_append.{0} format := infer_instance
@[instance] constant {} options.has_to_format  : has_to_format.{0} options
@[instance] constant {} bool.has_to_format  : has_to_format.{0} bool
@[instance] constant {} decidable.has_to_format (p : Prop) : has_to_format.{0} (decidable p)
@[instance] constant {} string.has_to_format  : has_to_format.{0} string
@[instance] constant {} nat.has_to_format  : has_to_format.{0} nat
def {} p29 : has_to_format.{0} nat := infer_instance
@[instance] constant {} unsigned.has_to_format  : has_to_format.{0} unsigned
@[instance] constant {} char.has_to_format  : has_to_format.{0} char
def {} p30 : has_to_format.{0} string := infer_instance
def {} p31 : has_coe_t.{1 1} string format := infer_instance
@[instance] constant {u} list.has_to_format (α : Type.{u}) [_inst_1 : has_to_format.{u} α] : has_to_format.{u} (list.{u} α)
@[instance] constant {} string.has_to_format  : has_to_format.{0} string
@[instance] constant {} name.has_to_format  : has_to_format.{0} name
@[instance] constant {} unit.has_to_format  : has_to_format.{0} punit.{1}
@[instance] constant {u} option.has_to_format (α : Type.{u}) [_inst_1 : has_to_format.{u} α] : has_to_format.{u} (option.{u} α)
@[instance] constant {u v} sum_has_to_format (α : Type.{u}) (β : Type.{v}) [_inst_1 : has_to_format.{u} α] [_inst_2 : has_to_format.{v} β] : has_to_format.{(max u v)} (sum.{u v} α β)
@[instance] constant {u v} prod.has_to_format (α : Type.{u}) (β : Type.{v}) [_inst_1 : has_to_format.{u} α] [_inst_2 : has_to_format.{v} β] : has_to_format.{(max u v)} (prod.{u v} α β)
@[instance] constant {u v} sigma.has_to_format (α : Type.{u}) (β : α -> Type.{v}) [_inst_1 : has_to_format.{u} α] [s : Pi (x : α), (has_to_format.{v} (β x))] : has_to_format.{(max u v)} (sigma.{u v} α β)
@[instance] constant {u} subtype.has_to_format (α : Type.{u}) (p : α -> Prop) [_inst_1 : has_to_format.{u} α] : has_to_format.{u} (subtype.{u+1} α p)
class {u v} monad_fail (m : Type.{u} -> Type.{v})
@[instance] constant {u v} monad_fail_lift (m : Type.{u} -> Type.{v}) (n : Type.{u} -> Type.{v}) [_inst_1 : has_monad_lift.{u v v} m n] [_inst_2 : monad_fail.{u v} m] [_inst_3 : monad.{u v} n] : monad_fail.{u v} n
def {} p32 : has_to_string.{0} format := infer_instance
constant {} exceptional : Type -> Type
@[instance] constant {} exceptional.has_to_string (α : Type) [_inst_1 : has_to_string.{0} α] : has_to_string.{0} (exceptional α)
@[instance] constant {} exceptional.monad  : monad.{0 0} exceptional
constant {} level : Type
@[instance] constant {} level.inhabited  : inhabited.{1} level
@[instance] constant {} level.has_decidable_eq (a : level) (b : level) : decidable (eq.{1} level a b)
@[instance] constant {} level.has_to_string  : has_to_string.{0} level
@[instance] constant {} level.has_to_format  : has_to_format.{0} level
def {} p33 : Pi (a : nat) (b : nat), (decidable (has_lt.lt.{0} nat nat.has_lt a b)) := infer_instance
constant {u₁ u₂} native.rb_map : Type.{u₁} -> Type.{u₂} -> Type.{max u₁ u₂}
@[instance] constant {} native.has_to_format (key : Type) (data : Type) [_inst_1 : has_to_format.{0} key] [_inst_2 : has_to_format.{0} data] : has_to_format.{0} (native.rb_map.{0 0} key data)
@[instance] constant {} native.has_to_string (key : Type) (data : Type) [_inst_1 : has_to_string.{0} key] [_inst_2 : has_to_string.{0} data] : has_to_string.{0} (native.rb_map.{0 0} key data)
constant {u_1} native.rb_set : Type.{u_1} -> Type.{u_1}
@[instance] constant {} native.rb_set.has_to_format (key : Type) [_inst_1 : has_to_format.{0} key] : has_to_format.{0} (native.rb_set.{0} key)
def {} p34 : has_to_format.{0} name := infer_instance
constant {} name_set : Type
@[instance] constant {} name_set.has_to_format  : has_to_format.{0} name_set
constant {} pos : Type
@[instance] constant {} pos.decidable_eq (a : pos) (b : pos) : decidable (eq.{1} pos a b)
def {} p35 : has_coe_t.{1 1} nat format := infer_instance
@[instance] constant {} pos.has_to_format  : has_to_format.{0} pos
constant {} binder_info : Type
@[instance] constant {} binder_info.has_repr  : has_repr.{0} binder_info
constant {} expr : bool -> Type
constant {} bool.tt : bool
@[instance] constant {} expr.inhabited  : inhabited.{1} (expr bool.tt)
@[instance] constant {} expr.has_decidable_eq (a : expr bool.tt) (b : expr bool.tt) : decidable (eq.{1} (expr bool.tt) a b)
@[instance] constant {} expr.has_to_string (elab : bool) : has_to_string.{0} (expr elab)
@[instance] constant {} expr.has_to_format (elab : bool) : has_to_format.{0} (expr elab)
@[instance] constant {} expr.has_coe_to_fun (elab : bool) : has_coe_to_fun.{1 1} (expr elab)
class {u} reflected (α : Sort.{u}) (a : α)
@[instance] constant {} expr.reflect (elab : bool) (e : expr elab) : reflected.{1} (expr elab) e
@[instance] constant {} string.reflect (s : string) : reflected.{1} string s
@[instance] constant {u} expr.has_coe (α : Sort.{u}) (a : α) : has_coe.{1 1} (reflected.{u} α a) (expr bool.tt)
def {} p36 : has_to_format.{0} (expr bool.tt) := infer_instance
@[instance] constant {u_1} reflected.has_to_format (α : Sort.{u_1}) (a : α) : has_to_format.{0} (reflected.{u_1} α a)
constant {} expr.expr.lt_prop : (expr bool.tt) -> (expr bool.tt) -> Prop
@[instance] constant {} expr.decidable_rel (a : expr bool.tt) (b : expr bool.tt) : decidable (expr.expr.lt_prop a b)
@[instance] constant {} expr.has_lt  : has_lt.{0} (expr bool.tt)
def {} p37 : has_coe_to_fun.{1 1} (expr bool.tt) := infer_instance
def {} p38 : has_to_format.{0} level := infer_instance
def {} p39 : has_to_format.{0} (list.{0} level) := infer_instance
def {} p40 : has_repr.{0} binder_info := infer_instance
def {} p41 : has_lt.{0} (expr bool.tt) := infer_instance
def {} p42 : Pi (a : expr bool.tt) (b : expr bool.tt), (decidable (has_lt.lt.{0} (expr bool.tt) expr.has_lt a b)) := infer_instance
def {} p43 : inhabited.{1} (expr bool.tt) := infer_instance
constant {} environment : Type
@[instance] constant {} environment.has_repr  : has_repr.{0} environment
@[instance] constant {} environment.inhabited  : inhabited.{1} environment
class {u} has_to_pexpr (α : Sort.{u})
constant {} bool.ff : bool
@[instance] constant {} pexpr.has_to_pexpr  : has_to_pexpr.{1} (expr bool.ff)
@[instance] constant {} expr.has_to_pexpr  : has_to_pexpr.{1} (expr bool.tt)
@[instance] constant {u} reflected.has_to_pexpr (α : Sort.{u}) (a : α) : has_to_pexpr.{1} (reflected.{u} α a)
constant {u} interaction_monad.result : Type -> Type.{u} -> Type.{u}
@[instance] constant {u} interaction_monad.result_has_string (state : Type) (α : Type.{u}) [_inst_1 : has_to_string.{u} α] : has_to_string.{u} (interaction_monad.result.{u} state α)
@[instance] constant {u_1} interaction_monad.monad (state : Type) : monad.{u_1 u_1} (fun (α : Type.{u_1}), (state -> (interaction_monad.result.{u_1} state α)))
def {} p44 : has_to_format.{0} format := infer_instance
@[instance] constant {u_1} interaction_monad.monad_fail (state : Type) : monad_fail.{u_1 u_1} (fun (α : Type.{u_1}), (state -> (interaction_monad.result.{u_1} state α)))
constant {} tactic_state : Type
@[instance] constant {} tactic_state.has_to_format  : has_to_format.{0} tactic_state
def {} p45 : has_to_format.{0} tactic_state := infer_instance
@[instance] constant {} tactic_state.has_to_string  : has_to_string.{0} tactic_state
@[instance] constant {u_1} tactic.alternative  : alternative.{u_1 u_1} (fun (α : Type.{u_1}), (tactic_state -> (interaction_monad.result.{u_1} tactic_state α)))
def {} p46 : has_orelse.{0 0} (fun (α : Type), (tactic_state -> (interaction_monad.result.{0} tactic_state α))) := infer_instance
def {} p47 : has_bind.{0 0} (fun (α : Type), (tactic_state -> (interaction_monad.result.{0} tactic_state α))) := infer_instance
@[instance] constant {u} tactic.opt_to_tac (α : Type.{u}) : has_coe.{u+1 (max 1 (u+1))} (option.{u} α) (tactic_state -> (interaction_monad.result.{u} tactic_state α))
def {} p48 : monad.{0 0} (fun (α : Type), (tactic_state -> (interaction_monad.result.{0} tactic_state α))) := infer_instance
@[instance] constant {} tactic.ex_to_tac (α : Type) : has_coe.{1 1} (exceptional α) (tactic_state -> (interaction_monad.result.{0} tactic_state α))
class {u} has_to_tactic_format (α : Type.{u})
@[instance] constant {} expr.has_to_tactic_format  : has_to_tactic_format.{0} (expr bool.tt)
def {} p49 : functor.{0 0} (fun (α : Type), (tactic_state -> (interaction_monad.result.{0} tactic_state α))) := infer_instance
def {} p50 : has_to_format.{0} (list.{0} format) := infer_instance
@[instance] constant {u} list.has_to_tactic_format (α : Type.{u}) [_inst_1 : has_to_tactic_format.{u} α] : has_to_tactic_format.{u} (list.{u} α)
def {} p51 : has_seq.{0 0} (fun (α : Type), (tactic_state -> (interaction_monad.result.{0} tactic_state α))) := infer_instance
def {} p52 : has_to_format.{0} (prod.{0 0} format format) := infer_instance
@[instance] constant {u v} prod.has_to_tactic_format (α : Type.{u}) (β : Type.{v}) [_inst_1 : has_to_tactic_format.{u} α] [_inst_2 : has_to_tactic_format.{v} β] : has_to_tactic_format.{(max u v)} (prod.{u v} α β)
@[instance] constant {u} option.has_to_tactic_format (α : Type.{u}) [_inst_1 : has_to_tactic_format.{u} α] : has_to_tactic_format.{u} (option.{u} α)
def {} p53 : has_to_tactic_format.{0} (expr bool.tt) := infer_instance
@[instance] constant {u_1} reflected.has_to_tactic_format (α : Sort.{u_1}) (a : α) : has_to_tactic_format.{0} (reflected.{u_1} α a)
@[instance] constant {} has_to_format_to_has_to_tactic_format (α : Type) [_inst_1 : has_to_format.{0} α] : has_to_tactic_format.{0} α
constant {} declaration : Type
def {} p54 : has_coe_t.{1 1} (exceptional declaration) (tactic_state -> (interaction_monad.result.{0} tactic_state declaration)) := infer_instance
def {} p55 : has_to_tactic_format.{0} format := infer_instance
constant {} tactic.transparency : Type
constant {} tactic.new_goals : Type
def {u_1} p56 : has_bind.{u_1 u_1} (fun (α : Type.{u_1}), (tactic_state -> (interaction_monad.result.{u_1} tactic_state α))) := infer_instance
def {} p57 : has_coe_t.{1 1} (reflected.{2} Type Prop) (expr bool.tt) := infer_instance
def {} p58 : monad.{0 0} exceptional := infer_instance
def {} p59 : has_append.{0} (list.{0} (expr bool.tt)) := infer_instance
def {} p60 : has_pure.{0 0} (fun (α : Type), (tactic_state -> (interaction_monad.result.{0} tactic_state α))) := infer_instance
def {} p61 : monad_fail.{0 0} (fun (α : Type), (tactic_state -> (interaction_monad.result.{0} tactic_state α))) := infer_instance
def {} p62 : alternative.{0 0} (fun (α : Type), (tactic_state -> (interaction_monad.result.{0} tactic_state α))) := infer_instance
def {u} p63 : has_orelse.{u u} (fun (α : Type.{u}), (tactic_state -> (interaction_monad.result.{u} tactic_state α))) := infer_instance
@[instance] constant {} tactic.andthen_seq  : has_andthen.{0 0 0} (tactic_state -> (interaction_monad.result.{0} tactic_state punit.{1})) (tactic_state -> (interaction_monad.result.{0} tactic_state punit.{1})) (tactic_state -> (interaction_monad.result.{0} tactic_state punit.{1}))
@[instance] constant {} tactic.andthen_seq_focus  : has_andthen.{0 0 0} (tactic_state -> (interaction_monad.result.{0} tactic_state punit.{1})) (list.{0} (tactic_state -> (interaction_monad.result.{0} tactic_state punit.{1}))) (tactic_state -> (interaction_monad.result.{0} tactic_state punit.{1}))
def {} p64 : has_to_pexpr.{1} (expr bool.ff) := infer_instance
def {} p65 : has_to_pexpr.{1} (expr bool.tt) := infer_instance
def {u_1} p66 : functor.{u_1 u_1} (fun (α : Type.{u_1}), (tactic_state -> (interaction_monad.result.{u_1} tactic_state α))) := infer_instance
def {} p67 : inhabited.{1} name := infer_instance
def {} p68 : has_append.{0} name := infer_instance
constant {u} task : Type.{u} -> Type.{u}
@[instance] constant {u_1} task.monad  : monad.{u_1 u_1} task.{u_1}
def {} p69 : has_mem.{0 0} nat (list.{0} nat) := infer_instance
constant {} occurrences : Type
@[instance] constant {} occurrences.inhabited  : inhabited.{1} occurrences
def {} p70 : has_repr.{0} (list.{0} nat) := infer_instance
@[instance] constant {} occurrences.has_repr  : has_repr.{0} occurrences
def {} p71 : has_to_format.{0} (list.{0} nat) := infer_instance
@[instance] constant {} occurrences.has_to_format  : has_to_format.{0} occurrences
constant {} tactic.apply_cfg : Type
constant {u} has_zero.zero : Pi (α : Type.{u}) (c : has_zero.{u} α), α
constant {u} has_one.one : Pi (α : Type.{u}) (c : has_one.{u} α), α
@[instance] constant {} nat.reflect (a : nat) : reflected.{1} nat a
@[instance] constant {} unsigned.reflect (a : unsigned) : reflected.{1} unsigned a
constant {} name.anonymous : name
@[instance] constant {} name.reflect (a : name) : reflected.{1} name a
@[instance] constant {} list.reflect (α : Type) [_inst_1 : Pi (a : α), (reflected.{1} α a)] [_inst_2 : reflected.{2} Type α] (a : list.{0} α) : reflected.{1} (list.{0} α) a
constant {u} punit.star : punit.{u}
@[instance] constant {} punit.reflect (a : punit.{1}) : reflected.{1} punit.{1} a
constant {} lean.parser_state : Type
@[instance] constant {} lean.parser.alternative  : alternative.{0 0} (fun (α : Type), (lean.parser_state -> (interaction_monad.result.{0} lean.parser_state α)))
def {} p72 : has_orelse.{0 0} (fun (α : Type), (lean.parser_state -> (interaction_monad.result.{0} lean.parser_state α))) := infer_instance
def {} p73 : has_seq.{0 0} (fun (α : Type), (lean.parser_state -> (interaction_monad.result.{0} lean.parser_state α))) := infer_instance
def {} p74 : functor.{0 0} (fun (α : Type), (lean.parser_state -> (interaction_monad.result.{0} lean.parser_state α))) := infer_instance
def {} p75 : monad.{0 0} (fun (α : Type), (lean.parser_state -> (interaction_monad.result.{0} lean.parser_state α))) := infer_instance
def {} p76 : alternative.{0 0} (fun (α : Type), (lean.parser_state -> (interaction_monad.result.{0} lean.parser_state α))) := infer_instance
def {} p77 : has_seq_right.{0 0} (fun (α : Type), (lean.parser_state -> (interaction_monad.result.{0} lean.parser_state α))) := infer_instance
@[instance] constant {} lean.parser.has_coe (α : Type) : has_coe.{1 1} (tactic_state -> (interaction_monad.result.{0} tactic_state α)) (lean.parser_state -> (interaction_monad.result.{0} lean.parser_state α))
constant {} user_attribute_cache_cfg : Type -> Type
constant {} user_attribute_cache_cfg.mk : Pi (cache_ty : Type) (mk_cache : (list.{0} name) -> tactic_state -> (interaction_monad.result.{0} tactic_state cache_ty)) (dependencies : list.{0} name), (user_attribute_cache_cfg cache_ty)
constant {u v} has_pure.pure : Pi (f : Type.{u} -> Type.{v}) (c : has_pure.{u v} f) (α : Type.{u}) (a : α), (f α)
constant {u} list.nil : Pi (T : Type.{u}), (list.{u} T)
def {} p78 : has_coe_t.{1 1} (reflected.{1} (user_attribute_cache_cfg punit.{1}) (user_attribute_cache_cfg.mk punit.{1} (fun (_x : list.{0} name), (has_pure.pure.{0 0} (fun (α : Type), (tactic_state -> (interaction_monad.result.{0} tactic_state α))) (applicative.to_has_pure.{0 0} (fun (α : Type), (tactic_state -> (interaction_monad.result.{0} tactic_state α))) (alternative.to_applicative.{0 0} (fun (α : Type), (tactic_state -> (interaction_monad.result.{0} tactic_state α))) tactic.alternative.{0})) punit.{1} punit.star.{1})) (list.nil.{0} name))) (expr bool.tt) := infer_instance
def {} p79 : has_pure.{0 0} (fun (α : Type), (lean.parser_state -> (interaction_monad.result.{0} lean.parser_state α))) := infer_instance
def {} p80 : has_coe_t.{1 1} (reflected.{1} (lean.parser_state -> (interaction_monad.result.{0} lean.parser_state punit.{1})) (has_pure.pure.{0 0} (fun (α : Type), (lean.parser_state -> (interaction_monad.result.{0} lean.parser_state α))) (applicative.to_has_pure.{0 0} (fun (α : Type), (lean.parser_state -> (interaction_monad.result.{0} lean.parser_state α))) (alternative.to_applicative.{0 0} (fun (α : Type), (lean.parser_state -> (interaction_monad.result.{0} lean.parser_state α))) lean.parser.alternative)) punit.{1} punit.star.{1})) (expr bool.tt) := infer_instance
constant {} user_attribute : Type -> Type -> Type
def {} p81 : has_coe_t.{1 1} (reflected.{2} Type (user_attribute name_set punit.{1})) (expr bool.tt) := infer_instance
constant {} simp_lemmas : Type
@[instance] constant {} simp_lemmas.has_to_tactic_format  : has_to_tactic_format.{0} simp_lemmas
constant {} tactic.dsimp_config : Type
def {} p82 : monad.{0 0} option.{0} := infer_instance
def {} p83 : has_coe_t.{1 1} (option.{0} (expr bool.tt)) (tactic_state -> (interaction_monad.result.{0} tactic_state (expr bool.tt))) := infer_instance
constant {} tactic.simp_config : Type
def {} p84 : has_coe_t.{1 1} (reflected.{2} Type (user_attribute simp_lemmas punit.{1})) (expr bool.tt) := infer_instance
def {} p85 : has_coe_t.{1 1} (reflected.{1} Prop false) (expr bool.tt) := infer_instance
def {} p86 : has_coe_t.{1 1} (expr bool.tt) (option.{0} (expr bool.tt)) := infer_instance
def {} p87 : has_append.{0} (list.{0} (tactic_state -> (interaction_monad.result.{0} tactic_state punit.{1}))) := infer_instance
def {} p88 : has_seq_left.{0 0} (fun (α : Type), (lean.parser_state -> (interaction_monad.result.{0} lean.parser_state α))) := infer_instance
def {} p89 : has_append.{0} (list.{0} format) := infer_instance
def {} p90 : has_bind.{0 0} (fun (α : Type), (lean.parser_state -> (interaction_monad.result.{0} lean.parser_state α))) := infer_instance
def {} p91 : monad_fail.{0 0} (fun (α : Type), (lean.parser_state -> (interaction_monad.result.{0} lean.parser_state α))) := infer_instance
constant {} cc_state : Type
@[instance] constant {} cc_state.has_to_tactic_format  : has_to_tactic_format.{0} cc_state
def {} p92 : has_to_tactic_format.{0} cc_state := infer_instance
def {} p93 : has_coe_t.{1 1} (option.{0} name) (tactic_state -> (interaction_monad.result.{0} tactic_state name)) := infer_instance
def {} p94 : has_append.{0} (list.{0} name) := infer_instance
def {} p95 : has_to_format.{0} (expr bool.ff) := infer_instance
constant {} derive_handler : Type
@[instance] constant {} bool.has_reflect (a : bool) : reflected.{1} bool a
@[instance] constant {} prod.has_reflect (α : Type) [a : Pi (a : α), (reflected.{1} α a)] (β : Type) [a : Pi (a : β), (reflected.{1} β a)] [a : reflected.{2} Type α] [a : reflected.{2} Type β] (a : prod.{0 0} α β) : reflected.{1} (prod.{0 0} α β) a
@[instance] constant {} sum.has_reflect (α : Type) [a : Pi (a : α), (reflected.{1} α a)] (β : Type) [a : Pi (a : β), (reflected.{1} β a)] [a : reflected.{2} Type α] [a : reflected.{2} Type β] (a : sum.{0 0} α β) : reflected.{1} (sum.{0 0} α β) a
@[instance] constant {} option.has_reflect (α : Type) [a : Pi (a : α), (reflected.{1} α a)] [a : reflected.{2} Type α] (a : option.{0} α) : reflected.{1} (option.{0} α) a
constant {} interactive.loc : Type
constant {} interactive.loc.wildcard : interactive.loc
constant {} interactive.loc.ns : (list.{0} (option.{0} name)) -> interactive.loc
@[instance] constant {} interactive.loc.has_reflect (a : interactive.loc) : reflected.{1} interactive.loc a
constant {} pos.mk : nat -> nat -> pos
@[instance] constant {} pos.has_reflect (a : pos) : reflected.{1} pos a
def {} p96 : has_to_tactic_format.{0} nat := infer_instance
def {} p97 : has_to_tactic_format.{0} (list.{0} level) := infer_instance
def {} p98 : has_to_tactic_format.{0} (list.{0} (expr bool.tt)) := infer_instance
constant {} tactic.pattern : Type
@[instance] constant {} tactic.has_to_tactic_format  : has_to_tactic_format.{0} tactic.pattern
def {} p99 : has_coe_t.{1 1} nat (option.{0} nat) := infer_instance
constant {} tactic.interactive.rw_rule : Type
constant {} tactic.interactive.rw_rule.mk : pos -> bool -> (expr bool.ff) -> tactic.interactive.rw_rule
@[instance] constant {} tactic.interactive.rw_rule.has_reflect (a : tactic.interactive.rw_rule) : reflected.{1} tactic.interactive.rw_rule a
constant {} tactic.interactive.rw_rules_t : Type
constant {} tactic.interactive.rw_rules_t.mk : (list.{0} tactic.interactive.rw_rule) -> (option.{0} pos) -> tactic.interactive.rw_rules_t
@[instance] constant {} tactic.interactive.rw_rules_t.has_reflect (a : tactic.interactive.rw_rules_t) : reflected.{1} tactic.interactive.rw_rules_t a
def {u_1} p100 : monad.{u_1 u_1} (fun (α : Type.{u_1}), (tactic_state -> (interaction_monad.result.{u_1} tactic_state α))) := infer_instance
def {} p101 : has_coe_t.{1 1} (tactic_state -> (interaction_monad.result.{0} tactic_state (prod.{0 0} (expr bool.ff) name))) (lean.parser_state -> (interaction_monad.result.{0} lean.parser_state (prod.{0 0} (expr bool.ff) name))) := infer_instance
def {} p102 : has_coe_t.{1 1} name (option.{0} name) := infer_instance
constant {} expr.is_local_constant : (expr bool.tt) -> bool
def {} p103 : Pi (a : expr bool.tt), (decidable (eq.{1} bool (expr.is_local_constant a) bool.tt)) := infer_instance
def {} p104 : Pi (a : name) (b : name), (decidable (eq.{1} name a b)) := infer_instance
def {} p105 : has_to_string.{0} (list.{0} name) := infer_instance
def {} p106 : has_to_string.{0} (list.{0} (list.{0} name)) := infer_instance
def {} p107 : has_bind.{0 0} option.{0} := infer_instance
def {} p108 : alternative.{0 0} option.{0} := infer_instance
def {} p109 : has_pure.{0 0} option.{0} := infer_instance
def {} p110 : has_mem.{0 0} (expr bool.tt) (list.{0} (expr bool.tt)) := infer_instance
def {} p111 : has_orelse.{0 0} option.{0} := infer_instance
def {} p112 : has_to_string.{0} name := infer_instance
def {} p113 : has_mem.{0 0} name (list.{0} name) := infer_instance
constant {} tactic.simp_arg_type : Type
constant {} tactic.simp_arg_type.all_hyps : tactic.simp_arg_type
constant {} tactic.simp_arg_type.except : name -> tactic.simp_arg_type
constant {} tactic.simp_arg_type.expr : (expr bool.ff) -> tactic.simp_arg_type
@[instance] constant {} tactic.simp_arg_type.has_reflect (a : tactic.simp_arg_type) : reflected.{1} tactic.simp_arg_type a
def {} p114 : has_coe_t.{1 1} simp_lemmas (option.{0} simp_lemmas) := infer_instance
def {} p115 : has_coe_t.{1 1} string name := infer_instance
def {} p116 : has_andthen.{0 0 0} (tactic_state -> (interaction_monad.result.{0} tactic_state punit.{1})) (tactic_state -> (interaction_monad.result.{0} tactic_state punit.{1})) (tactic_state -> (interaction_monad.result.{0} tactic_state punit.{1})) := infer_instance
constant {u} id : Pi (α : Sort.{u}) (a : α), α
@[instance] constant {u} id.monad  : monad.{u u} (id.{(u+1)+1} Type.{u})
@[instance] constant {u_1} id.monad_run  : monad_run.{u_1 u_1} (id.{(u_1+1)+1} Type.{u_1}) (id.{(u_1+1)+1} Type.{u_1})
constant {u v} except : Type.{u} -> Type.{v} -> Sort.{max (u+1) (v+1)}
@[instance] constant {u u_1} except.monad (ε : Type.{u}) : monad.{u_1 (max u u_1)} (except.{u u_1} ε)
constant {u v} except_t : Type.{u} -> (Type.{u} -> Type.{v}) -> Type.{u} -> Type.{v}
@[instance] constant {u v} except_t.has_monad_lift (ε : Type.{u}) (m : Type.{u} -> Type.{v}) [_inst_1 : monad.{u v} m] : has_monad_lift.{u v v} m (except_t.{u v} ε m)
@[instance] constant {u v} except_t.monad_functor (ε : Type.{u}) (m : Type.{u} -> Type.{v}) [_inst_1 : monad.{u v} m] (m' : Type.{u} -> Type.{v}) [_inst_2 : monad.{u v} m'] : monad_functor.{u v v} m m' (except_t.{u v} ε m) (except_t.{u v} ε m')
@[instance] constant {u v} except_t.monad (ε : Type.{u}) (m : Type.{u} -> Type.{v}) [_inst_1 : monad.{u v} m] : monad.{u v} (except_t.{u v} ε m)
class {u v w} monad_except (ε : Type.{u}) (m : Type.{v} -> Type.{w})
@[instance] constant {u_1 u_2} except_t.monad_except (m : Type.{u_1} -> Type.{u_2}) (ε : Type.{u_1}) [_inst_1 : monad.{u_1 u_2} m] : monad_except.{u_1 u_1 u_2} ε (except_t.{u_1 u_2} ε m)
class {u v} monad_except_adapter (ε : Type.{u}) (ε' : Type.{u}) (m : Type.{u} -> Type.{v}) (m' : Type.{u} -> Type.{v})
@[instance] constant {u v} monad_except_adapter_trans (ε : Type.{u}) (ε' : Type.{u}) (m : Type.{u} -> Type.{v}) (m' : Type.{u} -> Type.{v}) (n : Type.{u} -> Type.{v}) (n' : Type.{u} -> Type.{v}) [_inst_1 : monad_functor.{u v v} m m' n n'] [_inst_2 : monad_except_adapter.{u v} ε ε' m m'] : monad_except_adapter.{u v} ε ε' n n'
@[instance] constant {u v} except_t.monad_except_adapter (ε : Type.{u}) (ε' : Type.{u}) (m : Type.{u} -> Type.{v}) [_inst_1 : monad.{u v} m] : monad_except_adapter.{u v} ε ε' (except_t.{u v} ε m) (except_t.{u v} ε' m)
@[instance] constant {u_1 u_2} except_t.monad_run (ε : Type.{u_1}) (m : Type.{u_1} -> Type.{u_2}) (out : Type.{u_1} -> Type.{u_2}) [_inst_1 : monad_run.{u_1 u_2} out m] : monad_run.{u_1 u_2} (fun (α : Type.{u_1}), (out (except.{u_1 u_1} ε α))) (except_t.{u_1 u_2} ε m)
constant {u v} state_t : Type.{u} -> (Type.{u} -> Type.{v}) -> Type.{u} -> Type.{max u v}
@[instance] constant {u v} state_t.monad (σ : Type.{u}) (m : Type.{u} -> Type.{v}) [_inst_1 : monad.{u v} m] : monad.{u (max u v)} (state_t.{u v} σ m)
@[instance] constant {u v} state_t.alternative (σ : Type.{u}) (m : Type.{u} -> Type.{v}) [_inst_1 : monad.{u v} m] [_inst_2 : alternative.{u v} m] : alternative.{u (max u v)} (state_t.{u v} σ m)
@[instance] constant {u v} state_t.has_monad_lift (σ : Type.{u}) (m : Type.{u} -> Type.{v}) [_inst_1 : monad.{u v} m] : has_monad_lift.{u v (max u v)} m (state_t.{u v} σ m)
@[instance] constant {u_1 u_2} state_t.monad_functor (σ : Type.{u_1}) (m : Type.{u_1} -> Type.{u_2}) (m' : Type.{u_1} -> Type.{u_2}) [_inst_2 : monad.{u_1 u_2} m] [_inst_3 : monad.{u_1 u_2} m'] : monad_functor.{u_1 u_2 (max u_1 u_2)} m m' (state_t.{u_1 u_2} σ m) (state_t.{u_1 u_2} σ m')
@[instance] constant {u v u_1} state_t.monad_except (σ : Type.{u}) (m : Type.{u} -> Type.{v}) [_inst_1 : monad.{u v} m] (ε : Type.{u_1}) [_inst_2 : monad_except.{u_1 u v} ε m] : monad_except.{u_1 u (max u v)} ε (state_t.{u v} σ m)
class {u v} monad_state (σ : Type.{u}) (m : Type.{u} -> Type.{v})
@[instance] constant {u v w} monad_state_trans (σ : Type.{u}) (m : Type.{u} -> Type.{v}) (n : Type.{u} -> Type.{w}) [_inst_1 : has_monad_lift.{u v w} m n] [_inst_2 : monad_state.{u v} σ m] : monad_state.{u w} σ n
@[instance] constant {u v} state_t.monad_state (σ : Type.{u}) (m : Type.{u} -> Type.{v}) [_inst_1 : monad.{u v} m] : monad_state.{u (max u v)} σ (state_t.{u v} σ m)
def {u} p117 : monad.{u u} (id.{(u+1)+1} Type.{u}) := infer_instance
class {u v} monad_state_adapter (σ : Type.{u}) (σ' : Type.{u}) (m : Type.{u} -> Type.{v}) (m' : Type.{u} -> Type.{v})
@[instance] constant {u v} monad_state_adapter_trans (σ : Type.{u}) (σ' : Type.{u}) (m : Type.{u} -> Type.{v}) (m' : Type.{u} -> Type.{v}) (n : Type.{u} -> Type.{v}) (n' : Type.{u} -> Type.{v}) [_inst_1 : monad_functor.{u v v} m m' n n'] [_inst_2 : monad_state_adapter.{u v} σ σ' m m'] : monad_state_adapter.{u v} σ σ' n n'
@[instance] constant {u v} state_t.monad_state_adapter (σ : Type.{u}) (σ' : Type.{u}) (m : Type.{u} -> Type.{v}) [_inst_1 : monad.{u v} m] : monad_state_adapter.{u (max u v)} σ σ' (state_t.{u v} σ m) (state_t.{u v} σ' m)
@[instance] constant {u_1 u_2} state_t.monad_run (σ : Type.{u_1}) (m : Type.{u_1} -> Type.{u_2}) (out : Type.{u_1} -> Type.{u_2}) [_inst_1 : monad_run.{u_1 u_2} out m] : monad_run.{u_1 (max u_1 u_2)} (fun (α : Type.{u_1}), (σ -> (out (prod.{u_1 u_1} α σ)))) (state_t.{u_1 u_2} σ m)
constant {u v} reader_t : Type.{u} -> (Type.{u} -> Type.{v}) -> Type.{u} -> Type.{max u v}
@[instance] constant {u v} reader_t.monad (ρ : Type.{u}) (m : Type.{u} -> Type.{v}) [_inst_1 : monad.{u v} m] : monad.{u (max u v)} (reader_t.{u v} ρ m)
@[instance] constant {u u_1} reader_t.has_monad_lift (ρ : Type.{u}) (m : Type.{u} -> Type.{u_1}) [_inst_2 : monad.{u u_1} m] : has_monad_lift.{u u_1 (max u u_1)} m (reader_t.{u u_1} ρ m)
@[instance] constant {u_1 u_2} reader_t.monad_functor (ρ : Type.{u_1}) (m : Type.{u_1} -> Type.{u_2}) (m' : Type.{u_1} -> Type.{u_2}) [_inst_2 : monad.{u_1 u_2} m] [_inst_3 : monad.{u_1 u_2} m'] : monad_functor.{u_1 u_2 (max u_1 u_2)} m m' (reader_t.{u_1 u_2} ρ m) (reader_t.{u_1 u_2} ρ m')
@[instance] constant {u v} reader_t.alternative (ρ : Type.{u}) (m : Type.{u} -> Type.{v}) [_inst_1 : monad.{u v} m] [_inst_2 : alternative.{u v} m] : alternative.{u (max u v)} (reader_t.{u v} ρ m)
@[instance] constant {u v u_1} reader_t.monad_except (ρ : Type.{u}) (m : Type.{u} -> Type.{v}) [_inst_1 : monad.{u v} m] (ε : Type.{u_1}) [_inst_2 : monad.{u v} m] [_inst_3 : monad_except.{u_1 u v} ε m] : monad_except.{u_1 u (max u v)} ε (reader_t.{u v} ρ m)
class {u v} monad_reader (ρ : Type.{u}) (m : Type.{u} -> Type.{v})
@[instance] constant {u v w} monad_reader_trans (ρ : Type.{u}) (m : Type.{u} -> Type.{v}) (n : Type.{u} -> Type.{w}) [_inst_1 : has_monad_lift.{u v w} m n] [_inst_2 : monad_reader.{u v} ρ m] : monad_reader.{u w} ρ n
@[instance] constant {u v} reader_t.monad_reader (ρ : Type.{u}) (m : Type.{u} -> Type.{v}) [_inst_1 : monad.{u v} m] : monad_reader.{u (max u v)} ρ (reader_t.{u v} ρ m)
class {u v} monad_reader_adapter (ρ : Type.{u}) (ρ' : Type.{u}) (m : Type.{u} -> Type.{v}) (m' : Type.{u} -> Type.{v})
@[instance] constant {u v} monad_reader_adapter_trans (ρ : Type.{u}) (ρ' : Type.{u}) (m : Type.{u} -> Type.{v}) (m' : Type.{u} -> Type.{v}) (n : Type.{u} -> Type.{v}) (n' : Type.{u} -> Type.{v}) [_inst_1 : monad_functor.{u v v} m m' n n'] [_inst_2 : monad_reader_adapter.{u v} ρ ρ' m m'] : monad_reader_adapter.{u v} ρ ρ' n n'
@[instance] constant {u v} reader_t.monad_reader_adapter (ρ : Type.{u}) (ρ' : Type.{u}) (m : Type.{u} -> Type.{v}) [_inst_1 : monad.{u v} m] : monad_reader_adapter.{u (max u v)} ρ ρ' (reader_t.{u v} ρ m) (reader_t.{u v} ρ' m)
@[instance] constant {u u_1} reader_t.monad_run (ρ : Type.{u}) (m : Type.{u} -> Type.{u_1}) (out : Type.{u} -> Type.{u_1}) [_inst_1 : monad_run.{u u_1} out m] : monad_run.{u (max u u_1)} (fun (α : Type.{u}), (ρ -> (out α))) (reader_t.{u u_1} ρ m)
constant {u v} option_t : (Type.{u} -> Type.{v}) -> Type.{u} -> Type.{v}
@[instance] constant {u v} option_t.monad (m : Type.{u} -> Type.{v}) [_inst_1 : monad.{u v} m] : monad.{u v} (option_t.{u v} m)
@[instance] constant {u v} option_t.alternative (m : Type.{u} -> Type.{v}) [_inst_1 : monad.{u v} m] : alternative.{u v} (option_t.{u v} m)
@[instance] constant {u v} option_t.has_monad_lift (m : Type.{u} -> Type.{v}) [_inst_1 : monad.{u v} m] : has_monad_lift.{u v v} m (option_t.{u v} m)
@[instance] constant {u v} option_t.monad_functor (m : Type.{u} -> Type.{v}) [_inst_1 : monad.{u v} m] (m' : Type.{u} -> Type.{v}) [_inst_2 : monad.{u v} m'] : monad_functor.{u v v} m m' (option_t.{u v} m) (option_t.{u v} m')
@[instance] constant {u v} option_t.monad_except (m : Type.{u} -> Type.{v}) [_inst_1 : monad.{u v} m] : monad_except.{0 u v} punit.{1} (option_t.{u v} m)
@[instance] constant {u_1 u_2} option_t.monad_run (m : Type.{u_1} -> Type.{u_2}) (out : Type.{u_1} -> Type.{u_2}) [_inst_2 : monad_run.{u_1 u_2} out m] : monad_run.{u_1 u_2} (fun (α : Type.{u_1}), (out (option.{u_1} α))) (option_t.{u_1 u_2} m)
class {u v} is_lawful_functor (f : Type.{u} -> Type.{v}) (_inst_1 : functor.{u v} f)
class {u v} is_lawful_applicative (f : Type.{u} -> Type.{v}) (_inst_1 : applicative.{u v} f)
@[instance] constant {u v} is_lawful_applicative.to_is_lawful_functor (f : Type.{u} -> Type.{v}) [_inst_1 : applicative.{u v} f] [c : is_lawful_applicative.{u v} f _inst_1] : is_lawful_functor.{u v} f (applicative.to_functor.{u v} f _inst_1)
class {u v} is_lawful_monad (m : Type.{u} -> Type.{v}) (_inst_1 : monad.{u v} m)
@[instance] constant {u v} is_lawful_monad.to_is_lawful_applicative (m : Type.{u} -> Type.{v}) [_inst_1 : monad.{u v} m] [c : is_lawful_monad.{u v} m _inst_1] : is_lawful_applicative.{u v} m (monad.to_applicative.{u v} m _inst_1)
def {} p118 : functor.{0 0} (id.{2} Type) := infer_instance
def {} p119 : has_bind.{0 0} (id.{2} Type) := infer_instance
def {} p120 : has_pure.{0 0} (id.{2} Type) := infer_instance
def {u_1} p121 : monad.{u_1 u_1} (id.{(u_1+1)+1} Type.{u_1}) := infer_instance
def {u_1} p122 : applicative.{u_1 u_1} (id.{(u_1+1)+1} Type.{u_1}) := infer_instance
@[instance] constant {u_1} id.is_lawful_monad  : is_lawful_monad.{u_1 u_1} (id.{(u_1+1)+1} Type.{u_1}) id.monad.{u_1}
@[instance] constant {u v} state_t.is_lawful_monad (m : Type.{u} -> Type.{v}) [_inst_1 : monad.{u v} m] [_inst_2 : is_lawful_monad.{u v} m _inst_1] (σ : Type.{u}) : is_lawful_monad.{u (max u v)} (state_t.{u v} σ m) (state_t.monad.{u v} σ m _inst_1)
@[instance] constant {u v} except_t.is_lawful_monad (m : Type.{u} -> Type.{v}) [_inst_1 : monad.{u v} m] [_inst_2 : is_lawful_monad.{u v} m _inst_1] (ε : Type.{u}) : is_lawful_monad.{u v} (except_t.{u v} ε m) (except_t.monad.{u v} ε m _inst_1)
@[instance] constant {u v} reader_t.is_lawful_monad (ρ : Type.{u}) (m : Type.{u} -> Type.{v}) [_inst_1 : monad.{u v} m] [_inst_2 : is_lawful_monad.{u v} m _inst_1] : is_lawful_monad.{u (max u v)} (reader_t.{u v} ρ m) (reader_t.monad.{u v} ρ m _inst_1)
@[instance] constant {u v} option_t.is_lawful_monad (m : Type.{u} -> Type.{v}) [_inst_1 : monad.{u v} m] [_inst_2 : is_lawful_monad.{u v} m _inst_1] : is_lawful_monad.{u v} (option_t.{u v} m) (option_t.monad.{u v} m _inst_1)
@[instance] constant {u_1} punit.subsingleton  : subsingleton.{u_1} punit.{u_1}
@[instance] constant {} punit.inhabited  : inhabited.{1} punit.{1}
@[instance] constant {u_1} punit.decidable_eq (a : punit.{u_1}) (b : punit.{u_1}) : decidable (eq.{u_1} punit.{u_1} a b)
constant {u} set : Type.{u} -> Sort.{max (u+1) 1}
@[instance] constant {u} set.has_mem (α : Type.{u}) : has_mem.{u u} α (set.{u} α)
@[instance] constant {u} set.has_subset (α : Type.{u}) : has_subset.{u} (set.{u} α)
@[instance] constant {u} set.has_sep (α : Type.{u}) : has_sep.{u u} α (set.{u} α)
@[instance] constant {u} set.has_emptyc (α : Type.{u}) : has_emptyc.{u} (set.{u} α)
@[instance] constant {u} set.has_insert (α : Type.{u}) : has_insert.{u u} α (set.{u} α)
@[instance] constant {u} set.has_union (α : Type.{u}) : has_union.{u} (set.{u} α)
@[instance] constant {u} set.has_inter (α : Type.{u}) : has_inter.{u} (set.{u} α)
@[instance] constant {u} set.has_neg (α : Type.{u}) : has_neg.{u} (set.{u} α)
@[instance] constant {u} set.has_sdiff (α : Type.{u}) : has_sdiff.{u} (set.{u} α)
@[instance] constant {u_1} set.functor  : functor.{u_1 u_1} set.{u_1}
def {u_1} p123 : functor.{u_1 u_1} set.{u_1} := infer_instance
@[instance] constant {u_1} set.is_lawful_functor  : is_lawful_functor.{u_1 u_1} set.{u_1} set.functor.{u_1}
def {} p124 : decidable (not (eq.{1} nat (has_one.one.{0} nat nat.has_one) (has_zero.zero.{0} nat nat.has_zero))) := infer_instance
constant {} param_info : Type
@[instance] constant {} param_info.has_to_format  : has_to_format.{0} param_info
def {} p125 : has_to_format.{0} (list.{0} param_info) := infer_instance
constant {} fun_info : Type
@[instance] constant {} fun_info.has_to_format  : has_to_format.{0} fun_info
constant {} subsingleton_info : Type
@[instance] constant {} subsingleton_info.has_to_format  : has_to_format.{0} subsingleton_info
@[instance] constant {} tactic.binder_info.has_decidable_eq (a : binder_info) (b : binder_info) : decidable (eq.{1} binder_info a b)
constant {u} conv : Type.{u} -> Sort.{max 1 (u+1)}
@[instance] constant {u_1} conv.monad  : monad.{u_1 u_1} conv.{u_1}
def {u_1} p126 : monad_fail.{u_1 u_1} (fun (α : Type.{u_1}), (tactic_state -> (interaction_monad.result.{u_1} tactic_state α))) := infer_instance
@[instance] constant {u_1} conv.monad_fail  : monad_fail.{u_1 u_1} conv.{u_1}
def {u_1} p127 : alternative.{u_1 u_1} (fun (α : Type.{u_1}), (tactic_state -> (interaction_monad.result.{u_1} tactic_state α))) := infer_instance
@[instance] constant {u_1} conv.alternative  : alternative.{u_1 u_1} conv.{u_1}
def {} p128 : has_bind.{0 0} conv.{0} := infer_instance
def {} p129 : monad.{0 0} conv.{0} := infer_instance
def {} p130 : monad_fail.{0 0} conv.{0} := infer_instance
def {} p131 : alternative.{0 0} conv.{0} := infer_instance
def {} p132 : has_orelse.{0 0} conv.{0} := infer_instance
constant {} vm_obj_kind : Type
@[instance] constant {} vm_obj_kind.decidable_eq (a : vm_obj_kind) (b : vm_obj_kind) : decidable (eq.{1} vm_obj_kind a b)
constant {} vm_core : Type -> Type
@[instance] constant {} vm_core.monad  : monad.{0 0} vm_core
def {} p133 : has_bind.{0 0} (option_t.{0 0} vm_core) := infer_instance
def {} p134 : monad.{0 0} (option_t.{0 0} vm_core) := infer_instance
def {} p135 : has_coe_t.{1 1} (option.{0} (prod.{0 0} (expr bool.tt) (expr bool.tt))) (tactic_state -> (interaction_monad.result.{0} tactic_state (prod.{0 0} (expr bool.tt) (expr bool.tt)))) := infer_instance
constant {} hinst_lemma : Type
@[instance] constant {} hinst_lemma.has_to_tactic_format  : has_to_tactic_format.{0} hinst_lemma
constant {} hinst_lemmas : Type
@[instance] constant {} hinst_lemmas.has_to_tactic_format  : has_to_tactic_format.{0} hinst_lemmas
def {} p136 : has_coe_t.{1 1} (reflected.{2} Type (user_attribute hinst_lemmas punit.{1})) (expr bool.tt) := infer_instance
def {} p137 : has_coe_t.{1 1} (reflected.{2} Type (user_attribute punit.{1} punit.{1})) (expr bool.tt) := infer_instance
constant {} cc_config : Type
constant {} ematch_config : Type
constant {} smt_pre_config : Type
constant {} smt_state : Type
@[instance] constant {} smt_state.has_append  : has_append.{0} smt_state
def {} p138 : monad.{0 0} (state_t.{0 0} smt_state (fun (α : Type), (tactic_state -> (interaction_monad.result.{0} tactic_state α)))) := infer_instance
@[instance] constant {} smt_tactic.monad  : monad.{0 0} (state_t.{0 0} smt_state (fun (α : Type), (tactic_state -> (interaction_monad.result.{0} tactic_state α))))
def {} p139 : alternative.{0 0} (state_t.{0 0} smt_state (fun (α : Type), (tactic_state -> (interaction_monad.result.{0} tactic_state α)))) := infer_instance
@[instance] constant {} smt_tactic.alternative  : alternative.{0 0} (state_t.{0 0} smt_state (fun (α : Type), (tactic_state -> (interaction_monad.result.{0} tactic_state α))))
def {} p140 : monad_state.{0 0} smt_state (state_t.{0 0} smt_state (fun (α : Type), (tactic_state -> (interaction_monad.result.{0} tactic_state α)))) := infer_instance
@[instance] constant {} smt_tactic.monad_state  : monad_state.{0 0} smt_state (state_t.{0 0} smt_state (fun (α : Type), (tactic_state -> (interaction_monad.result.{0} tactic_state α))))
constant {} smt_tactic : Type -> Type
@[instance] constant {} smt_tactic.has_monad_lift  : has_monad_lift.{0 0 0} (fun (α : Type), (tactic_state -> (interaction_monad.result.{0} tactic_state α))) smt_tactic
def {} p141 : has_monad_lift_t.{0 0 0} (fun (α : Type), (tactic_state -> (interaction_monad.result.{0} tactic_state α))) smt_tactic := infer_instance
@[instance] constant {} smt_tactic.has_coe (α : Type) : has_coe.{1 1} (tactic_state -> (interaction_monad.result.{0} tactic_state α)) (smt_tactic α)
def {} p142 : monad.{0 0} smt_tactic := infer_instance
@[instance] constant {} smt_tactic.monad_fail  : monad_fail.{0 0} smt_tactic
def {} p143 : has_bind.{0 0} smt_tactic := infer_instance
def {} p144 : has_coe_t.{1 1} (tactic_state -> (interaction_monad.result.{0} tactic_state hinst_lemma)) (smt_tactic hinst_lemma) := infer_instance
def {} p145 : has_orelse.{0 0} smt_tactic := infer_instance
def {} p146 : monad_state.{0 0} smt_state smt_tactic := infer_instance
def {} p147 : has_coe_t.{1 1} (tactic_state -> (interaction_monad.result.{0} tactic_state tactic_state)) (smt_tactic tactic_state) := infer_instance
def {} p148 : has_append.{0} smt_state := infer_instance
def {} p149 : has_coe_t.{1 1} (tactic_state -> (interaction_monad.result.{0} tactic_state punit.{1})) (smt_tactic punit.{1}) := infer_instance
def {} p150 : monad_fail.{0 0} smt_tactic := infer_instance
def {} p151 : has_coe_t.{1 1} (tactic_state -> (interaction_monad.result.{0} tactic_state (expr bool.tt))) (smt_tactic (expr bool.tt)) := infer_instance
def {} p152 : functor.{0 0} smt_tactic := infer_instance
constant {} smt_goal : Type
def {} p153 : monad_state.{0 0} (list.{0} smt_goal) smt_tactic := infer_instance
def {} p154 : has_coe_t.{1 1} (tactic_state -> (interaction_monad.result.{0} tactic_state (list.{0} (expr bool.tt)))) (smt_tactic (list.{0} (expr bool.tt))) := infer_instance
def {} p155 : has_append.{0} (list.{0} smt_goal) := infer_instance
@[instance] constant {} smt_tactic.has_andthen  : has_andthen.{0 0 0} (smt_tactic punit.{1}) (smt_tactic punit.{1}) (smt_tactic punit.{1})
def {} p156 : has_coe_t.{1 1} (tactic_state -> (interaction_monad.result.{0} tactic_state (list.{0} (prod.{0 0} name (expr bool.tt))))) (smt_tactic (list.{0} (prod.{0 0} name (expr bool.tt)))) := infer_instance
def {} p157 : has_coe_t.{1 1} (tactic_state -> (interaction_monad.result.{0} tactic_state bool)) (smt_tactic bool) := infer_instance
def {} p158 : alternative.{0 0} smt_tactic := infer_instance
def {} p159 : has_coe_t.{1 1} (tactic_state -> (interaction_monad.result.{0} tactic_state level)) (smt_tactic level) := infer_instance
def {} p160 : has_coe_t.{1 1} (tactic_state -> (interaction_monad.result.{0} tactic_state name)) (smt_tactic name) := infer_instance
def {} p161 : has_coe_t.{1 1} (tactic_state -> (interaction_monad.result.{0} tactic_state (expr bool.ff))) (smt_tactic (expr bool.ff)) := infer_instance
def {} p162 : has_coe_t.{1 1} (tactic_state -> (interaction_monad.result.{0} tactic_state hinst_lemmas)) (smt_tactic hinst_lemmas) := infer_instance
constant {u v} psigma : Pi (α : Sort.{u}) (β : α -> Sort.{v}), Sort.{max 1 u v}
@[instance] constant {u v} psigma.has_well_founded (α : Type.{u}) (β : α -> Type.{v}) [s₁ : has_well_founded.{u+1} α] [s₂ : Pi (a : α), (has_well_founded.{v+1} (β a))] : has_well_founded.{(max 1 (u+1) (v+1))} (psigma.{u+1 v+1} α β)
class {u v} is_symm_op (α : Type.{u}) (β : Type.{v}) (op : α -> α -> β)
class {u} is_commutative (α : Type.{u}) (op : α -> α -> α)
@[instance] constant {u} is_symm_op_of_is_commutative (α : Type.{u}) (op : α -> α -> α) [_inst_1 : is_commutative.{u} α op] : is_symm_op.{u u} α α op
class {u} is_associative (α : Type.{u}) (op : α -> α -> α)
class {u} is_left_id (α : Type.{u}) (op : α -> α -> α) (o : α)
class {u} is_right_id (α : Type.{u}) (op : α -> α -> α) (o : α)
class {u} is_left_null (α : Type.{u}) (op : α -> α -> α) (o : α)
class {u} is_right_null (α : Type.{u}) (op : α -> α -> α) (o : α)
class {u} is_left_cancel (α : Type.{u}) (op : α -> α -> α)
class {u} is_right_cancel (α : Type.{u}) (op : α -> α -> α)
class {u} is_idempotent (α : Type.{u}) (op : α -> α -> α)
class {u} is_left_distrib (α : Type.{u}) (op₁ : α -> α -> α) (op₂ : α -> α -> α)
class {u} is_right_distrib (α : Type.{u}) (op₁ : α -> α -> α) (op₂ : α -> α -> α)
class {u} is_left_inv (α : Type.{u}) (op : α -> α -> α) (inv : α -> α) (o : α)
class {u} is_right_inv (α : Type.{u}) (op : α -> α -> α) (inv : α -> α) (o : α)
class {u} is_cond_left_inv (α : Type.{u}) (op : α -> α -> α) (inv : α -> α) (o : α) (p : α -> Prop)
class {u} is_cond_right_inv (α : Type.{u}) (op : α -> α -> α) (inv : α -> α) (o : α) (p : α -> Prop)
class {u} is_distinct (α : Type.{u}) (a : α) (b : α)
class {u} is_irrefl (α : Type.{u}) (r : α -> α -> Prop)
class {u} is_refl (α : Type.{u}) (r : α -> α -> Prop)
class {u} is_symm (α : Type.{u}) (r : α -> α -> Prop)
@[instance] constant {u} is_symm_op_of_is_symm (α : Type.{u}) (r : α -> α -> Prop) [_inst_1 : is_symm.{u} α r] : is_symm_op.{u 0} α Prop r
class {u} is_asymm (α : Type.{u}) (r : α -> α -> Prop)
class {u} is_antisymm (α : Type.{u}) (r : α -> α -> Prop)
class {u} is_trans (α : Type.{u}) (r : α -> α -> Prop)
class {u} is_total (α : Type.{u}) (r : α -> α -> Prop)
class {u} is_preorder (α : Type.{u}) (r : α -> α -> Prop)
@[instance] constant {u} is_preorder.to_is_refl (α : Type.{u}) (r : α -> α -> Prop) [c : is_preorder.{u} α r] : is_refl.{u} α r
@[instance] constant {u} is_preorder.to_is_trans (α : Type.{u}) (r : α -> α -> Prop) [c : is_preorder.{u} α r] : is_trans.{u} α r
class {u} is_total_preorder (α : Type.{u}) (r : α -> α -> Prop)
@[instance] constant {u} is_total_preorder.to_is_trans (α : Type.{u}) (r : α -> α -> Prop) [c : is_total_preorder.{u} α r] : is_trans.{u} α r
@[instance] constant {u} is_total_preorder.to_is_total (α : Type.{u}) (r : α -> α -> Prop) [c : is_total_preorder.{u} α r] : is_total.{u} α r
@[instance] constant {u} is_total_preorder_is_preorder (α : Type.{u}) (r : α -> α -> Prop) [s : is_total_preorder.{u} α r] : is_preorder.{u} α r
class {u} is_partial_order (α : Type.{u}) (r : α -> α -> Prop)
@[instance] constant {u} is_partial_order.to_is_preorder (α : Type.{u}) (r : α -> α -> Prop) [c : is_partial_order.{u} α r] : is_preorder.{u} α r
@[instance] constant {u} is_partial_order.to_is_antisymm (α : Type.{u}) (r : α -> α -> Prop) [c : is_partial_order.{u} α r] : is_antisymm.{u} α r
class {u} is_linear_order (α : Type.{u}) (r : α -> α -> Prop)
@[instance] constant {u} is_linear_order.to_is_partial_order (α : Type.{u}) (r : α -> α -> Prop) [c : is_linear_order.{u} α r] : is_partial_order.{u} α r
@[instance] constant {u} is_linear_order.to_is_total (α : Type.{u}) (r : α -> α -> Prop) [c : is_linear_order.{u} α r] : is_total.{u} α r
class {u} is_equiv (α : Type.{u}) (r : α -> α -> Prop)
@[instance] constant {u} is_equiv.to_is_preorder (α : Type.{u}) (r : α -> α -> Prop) [c : is_equiv.{u} α r] : is_preorder.{u} α r
@[instance] constant {u} is_equiv.to_is_symm (α : Type.{u}) (r : α -> α -> Prop) [c : is_equiv.{u} α r] : is_symm.{u} α r
class {u} is_per (α : Type.{u}) (r : α -> α -> Prop)
@[instance] constant {u} is_per.to_is_symm (α : Type.{u}) (r : α -> α -> Prop) [c : is_per.{u} α r] : is_symm.{u} α r
@[instance] constant {u} is_per.to_is_trans (α : Type.{u}) (r : α -> α -> Prop) [c : is_per.{u} α r] : is_trans.{u} α r
class {u} is_strict_order (α : Type.{u}) (r : α -> α -> Prop)
@[instance] constant {u} is_strict_order.to_is_irrefl (α : Type.{u}) (r : α -> α -> Prop) [c : is_strict_order.{u} α r] : is_irrefl.{u} α r
@[instance] constant {u} is_strict_order.to_is_trans (α : Type.{u}) (r : α -> α -> Prop) [c : is_strict_order.{u} α r] : is_trans.{u} α r
class {u} is_incomp_trans (α : Type.{u}) (lt : α -> α -> Prop)
class {u} is_strict_weak_order (α : Type.{u}) (lt : α -> α -> Prop)
@[instance] constant {u} is_strict_weak_order.to_is_strict_order (α : Type.{u}) (lt : α -> α -> Prop) [c : is_strict_weak_order.{u} α lt] : is_strict_order.{u} α lt
@[instance] constant {u} is_strict_weak_order.to_is_incomp_trans (α : Type.{u}) (lt : α -> α -> Prop) [c : is_strict_weak_order.{u} α lt] : is_incomp_trans.{u} α lt
class {u} is_trichotomous (α : Type.{u}) (lt : α -> α -> Prop)
class {u} is_strict_total_order (α : Type.{u}) (lt : α -> α -> Prop)
@[instance] constant {u} is_strict_total_order.to_is_trichotomous (α : Type.{u}) (lt : α -> α -> Prop) [c : is_strict_total_order.{u} α lt] : is_trichotomous.{u} α lt
@[instance] constant {u} is_strict_total_order.to_is_strict_weak_order (α : Type.{u}) (lt : α -> α -> Prop) [c : is_strict_total_order.{u} α lt] : is_strict_weak_order.{u} α lt
@[instance] constant {u} eq_is_equiv (α : Type.{u}) : is_equiv.{u} α (eq.{u+1} α)
@[instance] constant {u} is_asymm_of_is_trans_of_is_irrefl (α : Type.{u}) (r : α -> α -> Prop) [_inst_1 : is_trans.{u} α r] [_inst_2 : is_irrefl.{u} α r] : is_asymm.{u} α r
constant {u} strict_weak_order.equiv : Pi (α : Type.{u}) (r : α -> α -> Prop) (a : α) (b : α), Prop
@[instance] constant {u} strict_weak_order.is_equiv (α : Type.{u}) (r : α -> α -> Prop) [_inst_1 : is_strict_weak_order.{u} α r] : is_equiv.{u} α (strict_weak_order.equiv.{u} α r)
class {u} preorder (α : Type.{u})
@[instance] constant {u} preorder.to_has_le (α : Type.{u}) [s : preorder.{u} α] : has_le.{u} α
@[instance] constant {u} preorder.to_has_lt (α : Type.{u}) [s : preorder.{u} α] : has_lt.{u} α
class {u} partial_order (α : Type.{u})
@[instance] constant {u} partial_order.to_preorder (α : Type.{u}) [s : partial_order.{u} α] : preorder.{u} α
class {u} linear_order (α : Type.{u})
@[instance] constant {u} linear_order.to_partial_order (α : Type.{u}) [s : linear_order.{u} α] : partial_order.{u} α
@[instance] constant {u} decidable_lt_of_decidable_le (α : Type.{u}) [_inst_1 : preorder.{u} α] [_inst_2 : Pi (a : α) (b : α), (decidable (has_le.le.{u} α (preorder.to_has_le.{u} α _inst_1) a b))] (a : α) (b : α) : decidable (has_lt.lt.{u} α (preorder.to_has_lt.{u} α _inst_1) a b)
@[instance] constant {u} decidable_eq_of_decidable_le (α : Type.{u}) [_inst_1 : partial_order.{u} α] [_inst_2 : Pi (a : α) (b : α), (decidable (has_le.le.{u} α (preorder.to_has_le.{u} α (partial_order.to_preorder.{u} α _inst_1)) a b))] (a : α) (b : α) : decidable (eq.{u+1} α a b)
class {u} decidable_linear_order (α : Type.{u})
@[instance] constant {u} decidable_linear_order.to_linear_order (α : Type.{u}) [s : decidable_linear_order.{u} α] : linear_order.{u} α
constant {u} preorder.mk : Pi (α : Type.{u}) (le : α -> α -> Prop) (lt : α -> α -> Prop) (le_refl : Pi (a : α), (le a a)) (le_trans : Pi (a : α) (b : α) (c : α) (a_1 : le a b) (a_1 : le b c), (le a c)) (lt_iff_le_not_le : Pi (a : α) (b : α), (iff (lt a b) (and (le a b) (not (le b a))))), (preorder.{u} α)
constant {u} partial_order.mk : Pi (α : Type.{u}) (le : α -> α -> Prop) (lt : α -> α -> Prop) (le_refl : Pi (a : α), (le a a)) (le_trans : Pi (a : α) (b : α) (c : α) (a_1 : le a b) (a_1 : le b c), (le a c)) (lt_iff_le_not_le : Pi (a : α) (b : α), (iff (lt a b) (and (le a b) (not (le b a))))) (le_antisymm : Pi (a : α) (b : α) (a_1 : has_le.le.{u} α (preorder.to_has_le.{u} α (preorder.mk.{u} α le lt le_refl le_trans lt_iff_le_not_le)) a b) (a_1 : has_le.le.{u} α (preorder.to_has_le.{u} α (preorder.mk.{u} α le lt le_refl le_trans lt_iff_le_not_le)) b a), (eq.{u+1} α a b)), (partial_order.{u} α)
constant {u} linear_order.mk : Pi (α : Type.{u}) (le : α -> α -> Prop) (lt : α -> α -> Prop) (le_refl : Pi (a : α), (le a a)) (le_trans : Pi (a : α) (b : α) (c : α) (a_1 : le a b) (a_1 : le b c), (le a c)) (lt_iff_le_not_le : Pi (a : α) (b : α), (iff (lt a b) (and (le a b) (not (le b a))))) (le_antisymm : Pi (a : α) (b : α) (a_1 : has_le.le.{u} α (preorder.to_has_le.{u} α (preorder.mk.{u} α le lt le_refl le_trans lt_iff_le_not_le)) a b) (a_1 : has_le.le.{u} α (preorder.to_has_le.{u} α (preorder.mk.{u} α le lt le_refl le_trans lt_iff_le_not_le)) b a), (eq.{u+1} α a b)) (le_total : Pi (a : α) (b : α), (or (has_le.le.{u} α (preorder.to_has_le.{u} α (partial_order.to_preorder.{u} α (partial_order.mk.{u} α le lt le_refl le_trans lt_iff_le_not_le le_antisymm))) a b) (has_le.le.{u} α (preorder.to_has_le.{u} α (partial_order.to_preorder.{u} α (partial_order.mk.{u} α le lt le_refl le_trans lt_iff_le_not_le le_antisymm))) b a))), (linear_order.{u} α)
constant {u} decidable_linear_order.le : Pi (α : Type.{u}) (c : decidable_linear_order.{u} α) (a : α) (a : α), Prop
constant {u} decidable_linear_order.lt : Pi (α : Type.{u}) (c : decidable_linear_order.{u} α) (a : α) (a : α), Prop
constant {u} decidable_linear_order.le_refl : Pi (α : Type.{u}) (c : decidable_linear_order.{u} α) (a : α), (decidable_linear_order.le.{u} α c a a)
constant {u} decidable_linear_order.le_trans : Pi (α : Type.{u}) (c : decidable_linear_order.{u} α) (a : α) (b : α) (c_1 : α) (a_1 : decidable_linear_order.le.{u} α c a b) (a_1 : decidable_linear_order.le.{u} α c b c_1), (decidable_linear_order.le.{u} α c a c_1)
constant {u} decidable_linear_order.lt_iff_le_not_le : Pi (α : Type.{u}) (c : decidable_linear_order.{u} α) (a : α) (b : α), (iff (decidable_linear_order.lt.{u} α c a b) (and (decidable_linear_order.le.{u} α c a b) (not (decidable_linear_order.le.{u} α c b a))))
constant {u} decidable_linear_order.le_antisymm : Pi (α : Type.{u}) (c : decidable_linear_order.{u} α) (a : α) (b : α) (a_1 : has_le.le.{u} α (preorder.to_has_le.{u} α (preorder.mk.{u} α (decidable_linear_order.le.{u} α c) (decidable_linear_order.lt.{u} α c) (decidable_linear_order.le_refl.{u} α c) (decidable_linear_order.le_trans.{u} α c) (decidable_linear_order.lt_iff_le_not_le.{u} α c))) a b) (a_1 : has_le.le.{u} α (preorder.to_has_le.{u} α (preorder.mk.{u} α (decidable_linear_order.le.{u} α c) (decidable_linear_order.lt.{u} α c) (decidable_linear_order.le_refl.{u} α c) (decidable_linear_order.le_trans.{u} α c) (decidable_linear_order.lt_iff_le_not_le.{u} α c))) b a), (eq.{u+1} α a b)
constant {u} decidable_linear_order.le_total : Pi (α : Type.{u}) (c : decidable_linear_order.{u} α) (a : α) (b : α), (or (has_le.le.{u} α (preorder.to_has_le.{u} α (partial_order.to_preorder.{u} α (partial_order.mk.{u} α (decidable_linear_order.le.{u} α c) (decidable_linear_order.lt.{u} α c) (decidable_linear_order.le_refl.{u} α c) (decidable_linear_order.le_trans.{u} α c) (decidable_linear_order.lt_iff_le_not_le.{u} α c) (decidable_linear_order.le_antisymm.{u} α c)))) a b) (has_le.le.{u} α (preorder.to_has_le.{u} α (partial_order.to_preorder.{u} α (partial_order.mk.{u} α (decidable_linear_order.le.{u} α c) (decidable_linear_order.lt.{u} α c) (decidable_linear_order.le_refl.{u} α c) (decidable_linear_order.le_trans.{u} α c) (decidable_linear_order.lt_iff_le_not_le.{u} α c) (decidable_linear_order.le_antisymm.{u} α c)))) b a))
@[instance] constant {u} has_lt.lt.decidable (α : Type.{u}) [_inst_1 : decidable_linear_order.{u} α] (a : α) (b : α) : decidable (has_lt.lt.{u} α (preorder.to_has_lt.{u} α (partial_order.to_preorder.{u} α (linear_order.to_partial_order.{u} α (linear_order.mk.{u} α (decidable_linear_order.le.{u} α _inst_1) (decidable_linear_order.lt.{u} α _inst_1) (decidable_linear_order.le_refl.{u} α _inst_1) (decidable_linear_order.le_trans.{u} α _inst_1) (decidable_linear_order.lt_iff_le_not_le.{u} α _inst_1) (decidable_linear_order.le_antisymm.{u} α _inst_1) (decidable_linear_order.le_total.{u} α _inst_1))))) a b)
@[instance] constant {u} has_le.le.decidable (α : Type.{u}) [_inst_1 : decidable_linear_order.{u} α] (a : α) (b : α) : decidable (has_le.le.{u} α (preorder.to_has_le.{u} α (partial_order.to_preorder.{u} α (linear_order.to_partial_order.{u} α (linear_order.mk.{u} α (decidable_linear_order.le.{u} α _inst_1) (decidable_linear_order.lt.{u} α _inst_1) (decidable_linear_order.le_refl.{u} α _inst_1) (decidable_linear_order.le_trans.{u} α _inst_1) (decidable_linear_order.lt_iff_le_not_le.{u} α _inst_1) (decidable_linear_order.le_antisymm.{u} α _inst_1) (decidable_linear_order.le_total.{u} α _inst_1))))) a b)
@[instance] constant {u} eq.decidable (α : Type.{u}) [_inst_1 : decidable_linear_order.{u} α] (a : α) (b : α) : decidable (eq.{u+1} α a b)
@[instance] constant {u} has_le.le.is_total_preorder (α : Type.{u}) [_inst_1 : decidable_linear_order.{u} α] : is_total_preorder.{u} α (has_le.le.{u} α (preorder.to_has_le.{u} α (partial_order.to_preorder.{u} α (linear_order.to_partial_order.{u} α (decidable_linear_order.to_linear_order.{u} α _inst_1)))))
@[instance] constant {u} is_strict_weak_order_of_decidable_linear_order (α : Type.{u}) [_inst_1 : decidable_linear_order.{u} α] : is_strict_weak_order.{u} α (has_lt.lt.{u} α (preorder.to_has_lt.{u} α (partial_order.to_preorder.{u} α (linear_order.to_partial_order.{u} α (decidable_linear_order.to_linear_order.{u} α _inst_1)))))
@[instance] constant {u} is_strict_total_order_of_decidable_linear_order (α : Type.{u}) [_inst_1 : decidable_linear_order.{u} α] : is_strict_total_order.{u} α (has_lt.lt.{u} α (preorder.to_has_lt.{u} α (partial_order.to_preorder.{u} α (linear_order.to_partial_order.{u} α (decidable_linear_order.to_linear_order.{u} α _inst_1)))))
class {u} semigroup (α : Type.{u})
@[instance] constant {u} semigroup.to_has_mul (α : Type.{u}) [s : semigroup.{u} α] : has_mul.{u} α
class {u} comm_semigroup (α : Type.{u})
@[instance] constant {u} comm_semigroup.to_semigroup (α : Type.{u}) [s : comm_semigroup.{u} α] : semigroup.{u} α
class {u} left_cancel_semigroup (α : Type.{u})
@[instance] constant {u} left_cancel_semigroup.to_semigroup (α : Type.{u}) [s : left_cancel_semigroup.{u} α] : semigroup.{u} α
class {u} right_cancel_semigroup (α : Type.{u})
@[instance] constant {u} right_cancel_semigroup.to_semigroup (α : Type.{u}) [s : right_cancel_semigroup.{u} α] : semigroup.{u} α
class {u} monoid (α : Type.{u})
@[instance] constant {u} monoid.to_semigroup (α : Type.{u}) [s : monoid.{u} α] : semigroup.{u} α
@[instance] constant {u} monoid.to_has_one (α : Type.{u}) [s : monoid.{u} α] : has_one.{u} α
class {u} comm_monoid (α : Type.{u})
@[instance] constant {u} comm_monoid.to_monoid (α : Type.{u}) [s : comm_monoid.{u} α] : monoid.{u} α
@[instance] constant {u} comm_monoid.to_comm_semigroup (α : Type.{u}) [s : comm_monoid.{u} α] : comm_semigroup.{u} α
class {u} group (α : Type.{u})
@[instance] constant {u} group.to_monoid (α : Type.{u}) [s : group.{u} α] : monoid.{u} α
@[instance] constant {u} group.to_has_inv (α : Type.{u}) [s : group.{u} α] : has_inv.{u} α
class {u} comm_group (α : Type.{u})
@[instance] constant {u} comm_group.to_group (α : Type.{u}) [s : comm_group.{u} α] : group.{u} α
@[instance] constant {u} comm_group.to_comm_monoid (α : Type.{u}) [s : comm_group.{u} α] : comm_monoid.{u} α
constant {u} has_mul.mul : Pi (α : Type.{u}) (c : has_mul.{u} α) (a : α) (a : α), α
@[instance] constant {u} semigroup_to_is_associative (α : Type.{u}) [_inst_1 : semigroup.{u} α] : is_associative.{u} α (has_mul.mul.{u} α (semigroup.to_has_mul.{u} α _inst_1))
@[instance] constant {u} comm_semigroup_to_is_commutative (α : Type.{u}) [_inst_1 : comm_semigroup.{u} α] : is_commutative.{u} α (has_mul.mul.{u} α (semigroup.to_has_mul.{u} α (comm_semigroup.to_semigroup.{u} α _inst_1)))
@[instance] constant {u} group.to_left_cancel_semigroup (α : Type.{u}) [s : group.{u} α] : left_cancel_semigroup.{u} α
@[instance] constant {u} group.to_right_cancel_semigroup (α : Type.{u}) [s : group.{u} α] : right_cancel_semigroup.{u} α
class {u} add_semigroup (α : Type.{u})
@[instance] constant {u} add_semigroup.to_has_add (α : Type.{u}) [s : add_semigroup.{u} α] : has_add.{u} α
class {u} add_comm_semigroup (α : Type.{u})
@[instance] constant {u} add_comm_semigroup.to_add_semigroup (α : Type.{u}) [s : add_comm_semigroup.{u} α] : add_semigroup.{u} α
class {u} add_left_cancel_semigroup (α : Type.{u})
@[instance] constant {u} add_left_cancel_semigroup.to_add_semigroup (α : Type.{u}) [s : add_left_cancel_semigroup.{u} α] : add_semigroup.{u} α
class {u} add_right_cancel_semigroup (α : Type.{u})
@[instance] constant {u} add_right_cancel_semigroup.to_add_semigroup (α : Type.{u}) [s : add_right_cancel_semigroup.{u} α] : add_semigroup.{u} α
class {u} add_monoid (α : Type.{u})
@[instance] constant {u} add_monoid.to_add_semigroup (α : Type.{u}) [s : add_monoid.{u} α] : add_semigroup.{u} α
@[instance] constant {u} add_monoid.to_has_zero (α : Type.{u}) [s : add_monoid.{u} α] : has_zero.{u} α
class {u} add_comm_monoid (α : Type.{u})
@[instance] constant {u} add_comm_monoid.to_add_monoid (α : Type.{u}) [s : add_comm_monoid.{u} α] : add_monoid.{u} α
@[instance] constant {u} add_comm_monoid.to_add_comm_semigroup (α : Type.{u}) [s : add_comm_monoid.{u} α] : add_comm_semigroup.{u} α
class {u} add_group (α : Type.{u})
@[instance] constant {u} add_group.to_add_monoid (α : Type.{u}) [s : add_group.{u} α] : add_monoid.{u} α
@[instance] constant {u} add_group.to_has_neg (α : Type.{u}) [s : add_group.{u} α] : has_neg.{u} α
class {u} add_comm_group (α : Type.{u})
@[instance] constant {u} add_comm_group.to_add_group (α : Type.{u}) [s : add_comm_group.{u} α] : add_group.{u} α
@[instance] constant {u} add_comm_group.to_add_comm_monoid (α : Type.{u}) [s : add_comm_group.{u} α] : add_comm_monoid.{u} α
def {} p163 : has_lt.{0} name := infer_instance
def {} p164 : Pi (a : name) (b : name), (decidable (has_lt.lt.{0} name name.has_lt a b)) := infer_instance
@[instance] constant {u} add_group.to_left_cancel_add_semigroup (α : Type.{u}) [s : add_group.{u} α] : add_left_cancel_semigroup.{u} α
@[instance] constant {u} add_group.to_right_cancel_add_semigroup (α : Type.{u}) [s : add_group.{u} α] : add_right_cancel_semigroup.{u} α
constant {u} has_add.add : Pi (α : Type.{u}) (c : has_add.{u} α) (a : α) (a : α), α
@[instance] constant {u} add_semigroup_to_is_eq_associative (α : Type.{u}) [_inst_1 : add_semigroup.{u} α] : is_associative.{u} α (has_add.add.{u} α (add_semigroup.to_has_add.{u} α _inst_1))
@[instance] constant {u} add_comm_semigroup_to_is_eq_commutative (α : Type.{u}) [_inst_1 : add_comm_semigroup.{u} α] : is_commutative.{u} α (has_add.add.{u} α (add_semigroup.to_has_add.{u} α (add_comm_semigroup.to_add_semigroup.{u} α _inst_1)))
@[instance] constant {u} add_group_has_sub (α : Type.{u}) [_inst_1 : add_group.{u} α] : has_sub.{u} α
class {u} ordered_cancel_comm_monoid (α : Type.{u})
@[instance] constant {u} ordered_cancel_comm_monoid.to_add_comm_monoid (α : Type.{u}) [s : ordered_cancel_comm_monoid.{u} α] : add_comm_monoid.{u} α
@[instance] constant {u} ordered_cancel_comm_monoid.to_add_left_cancel_semigroup (α : Type.{u}) [s : ordered_cancel_comm_monoid.{u} α] : add_left_cancel_semigroup.{u} α
@[instance] constant {u} ordered_cancel_comm_monoid.to_add_right_cancel_semigroup (α : Type.{u}) [s : ordered_cancel_comm_monoid.{u} α] : add_right_cancel_semigroup.{u} α
@[instance] constant {u} ordered_cancel_comm_monoid.to_partial_order (α : Type.{u}) [s : ordered_cancel_comm_monoid.{u} α] : partial_order.{u} α
class {u} ordered_comm_group (α : Type.{u})
@[instance] constant {u} ordered_comm_group.to_add_comm_group (α : Type.{u}) [s : ordered_comm_group.{u} α] : add_comm_group.{u} α
@[instance] constant {u} ordered_comm_group.to_partial_order (α : Type.{u}) [s : ordered_comm_group.{u} α] : partial_order.{u} α
@[instance] constant {u} ordered_comm_group.to_ordered_cancel_comm_monoid (α : Type.{u}) [s : ordered_comm_group.{u} α] : ordered_cancel_comm_monoid.{u} α
class {u} decidable_linear_ordered_comm_group (α : Type.{u})
@[instance] constant {u} decidable_linear_ordered_comm_group.to_add_comm_group (α : Type.{u}) [s : decidable_linear_ordered_comm_group.{u} α] : add_comm_group.{u} α
@[instance] constant {u} decidable_linear_ordered_comm_group.to_decidable_linear_order (α : Type.{u}) [s : decidable_linear_ordered_comm_group.{u} α] : decidable_linear_order.{u} α
@[instance] constant {u} decidable_linear_ordered_comm_group.to_ordered_comm_group (α : Type.{u}) [s : decidable_linear_ordered_comm_group.{u} α] : ordered_comm_group.{u} α
class {u} decidable_linear_ordered_cancel_comm_monoid (α : Type.{u})
@[instance] constant {u} decidable_linear_ordered_cancel_comm_monoid.to_ordered_cancel_comm_monoid (α : Type.{u}) [s : decidable_linear_ordered_cancel_comm_monoid.{u} α] : ordered_cancel_comm_monoid.{u} α
@[instance] constant {u} decidable_linear_ordered_cancel_comm_monoid.to_decidable_linear_order (α : Type.{u}) [s : decidable_linear_ordered_cancel_comm_monoid.{u} α] : decidable_linear_order.{u} α
class {u} distrib (α : Type.{u})
@[instance] constant {u} distrib.to_has_mul (α : Type.{u}) [s : distrib.{u} α] : has_mul.{u} α
@[instance] constant {u} distrib.to_has_add (α : Type.{u}) [s : distrib.{u} α] : has_add.{u} α
class {u} mul_zero_class (α : Type.{u})
@[instance] constant {u} mul_zero_class.to_has_mul (α : Type.{u}) [s : mul_zero_class.{u} α] : has_mul.{u} α
@[instance] constant {u} mul_zero_class.to_has_zero (α : Type.{u}) [s : mul_zero_class.{u} α] : has_zero.{u} α
class {u} zero_ne_one_class (α : Type.{u})
@[instance] constant {u} zero_ne_one_class.to_has_zero (α : Type.{u}) [s : zero_ne_one_class.{u} α] : has_zero.{u} α
@[instance] constant {u} zero_ne_one_class.to_has_one (α : Type.{u}) [s : zero_ne_one_class.{u} α] : has_one.{u} α
class {u} semiring (α : Type.{u})
@[instance] constant {u} semiring.to_add_comm_monoid (α : Type.{u}) [s : semiring.{u} α] : add_comm_monoid.{u} α
@[instance] constant {u} semiring.to_monoid (α : Type.{u}) [s : semiring.{u} α] : monoid.{u} α
@[instance] constant {u} semiring.to_distrib (α : Type.{u}) [s : semiring.{u} α] : distrib.{u} α
@[instance] constant {u} semiring.to_mul_zero_class (α : Type.{u}) [s : semiring.{u} α] : mul_zero_class.{u} α
class {u} comm_semiring (α : Type.{u})
@[instance] constant {u} comm_semiring.to_semiring (α : Type.{u}) [s : comm_semiring.{u} α] : semiring.{u} α
@[instance] constant {u} comm_semiring.to_comm_monoid (α : Type.{u}) [s : comm_semiring.{u} α] : comm_monoid.{u} α
@[instance] constant {u} comm_semiring_has_dvd (α : Type.{u}) [_inst_1 : comm_semiring.{u} α] : has_dvd.{u} α
class {u} ring (α : Type.{u})
@[instance] constant {u} ring.to_add_comm_group (α : Type.{u}) [s : ring.{u} α] : add_comm_group.{u} α
@[instance] constant {u} ring.to_monoid (α : Type.{u}) [s : ring.{u} α] : monoid.{u} α
@[instance] constant {u} ring.to_distrib (α : Type.{u}) [s : ring.{u} α] : distrib.{u} α
@[instance] constant {u} ring.to_semiring (α : Type.{u}) [s : ring.{u} α] : semiring.{u} α
class {u} comm_ring (α : Type.{u})
@[instance] constant {u} comm_ring.to_ring (α : Type.{u}) [s : comm_ring.{u} α] : ring.{u} α
@[instance] constant {u} comm_ring.to_comm_semigroup (α : Type.{u}) [s : comm_ring.{u} α] : comm_semigroup.{u} α
@[instance] constant {u} comm_ring.to_comm_semiring (α : Type.{u}) [s : comm_ring.{u} α] : comm_semiring.{u} α
class {u} no_zero_divisors (α : Type.{u})
@[instance] constant {u} no_zero_divisors.to_has_mul (α : Type.{u}) [s : no_zero_divisors.{u} α] : has_mul.{u} α
@[instance] constant {u} no_zero_divisors.to_has_zero (α : Type.{u}) [s : no_zero_divisors.{u} α] : has_zero.{u} α
class {u} integral_domain (α : Type.{u})
@[instance] constant {u} integral_domain.to_comm_ring (α : Type.{u}) [s : integral_domain.{u} α] : comm_ring.{u} α
@[instance] constant {u} integral_domain.to_no_zero_divisors (α : Type.{u}) [s : integral_domain.{u} α] : no_zero_divisors.{u} α
@[instance] constant {u} integral_domain.to_zero_ne_one_class (α : Type.{u}) [s : integral_domain.{u} α] : zero_ne_one_class.{u} α
class {u} ordered_semiring (α : Type.{u})
@[instance] constant {u} ordered_semiring.to_semiring (α : Type.{u}) [s : ordered_semiring.{u} α] : semiring.{u} α
@[instance] constant {u} ordered_semiring.to_ordered_cancel_comm_monoid (α : Type.{u}) [s : ordered_semiring.{u} α] : ordered_cancel_comm_monoid.{u} α
class {u} linear_ordered_semiring (α : Type.{u})
@[instance] constant {u} linear_ordered_semiring.to_ordered_semiring (α : Type.{u}) [s : linear_ordered_semiring.{u} α] : ordered_semiring.{u} α
@[instance] constant {u} linear_ordered_semiring.to_linear_order (α : Type.{u}) [s : linear_ordered_semiring.{u} α] : linear_order.{u} α
class {u} decidable_linear_ordered_semiring (α : Type.{u})
@[instance] constant {u} decidable_linear_ordered_semiring.to_linear_ordered_semiring (α : Type.{u}) [s : decidable_linear_ordered_semiring.{u} α] : linear_ordered_semiring.{u} α
@[instance] constant {u} decidable_linear_ordered_semiring.to_decidable_linear_order (α : Type.{u}) [s : decidable_linear_ordered_semiring.{u} α] : decidable_linear_order.{u} α
class {u} ordered_ring (α : Type.{u})
@[instance] constant {u} ordered_ring.to_ring (α : Type.{u}) [s : ordered_ring.{u} α] : ring.{u} α
@[instance] constant {u} ordered_ring.to_ordered_comm_group (α : Type.{u}) [s : ordered_ring.{u} α] : ordered_comm_group.{u} α
@[instance] constant {u} ordered_ring.to_zero_ne_one_class (α : Type.{u}) [s : ordered_ring.{u} α] : zero_ne_one_class.{u} α
@[instance] constant {u} ordered_ring.to_ordered_semiring (α : Type.{u}) [s : ordered_ring.{u} α] : ordered_semiring.{u} α
class {u} linear_ordered_ring (α : Type.{u})
@[instance] constant {u} linear_ordered_ring.to_ordered_ring (α : Type.{u}) [s : linear_ordered_ring.{u} α] : ordered_ring.{u} α
@[instance] constant {u} linear_ordered_ring.to_linear_order (α : Type.{u}) [s : linear_ordered_ring.{u} α] : linear_order.{u} α
@[instance] constant {u} linear_ordered_ring.to_linear_ordered_semiring (α : Type.{u}) [s : linear_ordered_ring.{u} α] : linear_ordered_semiring.{u} α
class {u} linear_ordered_comm_ring (α : Type.{u})
@[instance] constant {u} linear_ordered_comm_ring.to_linear_ordered_ring (α : Type.{u}) [s : linear_ordered_comm_ring.{u} α] : linear_ordered_ring.{u} α
@[instance] constant {u} linear_ordered_comm_ring.to_comm_monoid (α : Type.{u}) [s : linear_ordered_comm_ring.{u} α] : comm_monoid.{u} α
@[instance] constant {u} linear_ordered_comm_ring.to_integral_domain (α : Type.{u}) [s : linear_ordered_comm_ring.{u} α] : integral_domain.{u} α
class {u} decidable_linear_ordered_comm_ring (α : Type.{u})
@[instance] constant {u} decidable_linear_ordered_comm_ring.to_linear_ordered_comm_ring (α : Type.{u}) [s : decidable_linear_ordered_comm_ring.{u} α] : linear_ordered_comm_ring.{u} α
@[instance] constant {u} decidable_linear_ordered_comm_ring.to_decidable_linear_ordered_comm_group (α : Type.{u}) [s : decidable_linear_ordered_comm_ring.{u} α] : decidable_linear_ordered_comm_group.{u} α
@[instance] constant {u} decidable_linear_ordered_comm_ring.to_decidable_linear_ordered_semiring (α : Type.{u}) [d : decidable_linear_ordered_comm_ring.{u} α] : decidable_linear_ordered_semiring.{u} α
class {u} division_ring (α : Type.{u})
@[instance] constant {u} division_ring.to_ring (α : Type.{u}) [s : division_ring.{u} α] : ring.{u} α
@[instance] constant {u} division_ring.to_has_inv (α : Type.{u}) [s : division_ring.{u} α] : has_inv.{u} α
@[instance] constant {u} division_ring.to_zero_ne_one_class (α : Type.{u}) [s : division_ring.{u} α] : zero_ne_one_class.{u} α
@[instance] constant {u} division_ring_has_div (α : Type.{u}) [_inst_1 : division_ring.{u} α] [_inst_2 : division_ring.{u} α] : has_div.{u} α
class {u} field (α : Type.{u})
@[instance] constant {u} field.to_division_ring (α : Type.{u}) [s : field.{u} α] : division_ring.{u} α
@[instance] constant {u} field.to_comm_ring (α : Type.{u}) [s : field.{u} α] : comm_ring.{u} α
class {u} discrete_field (α : Type.{u})
@[instance] constant {u} discrete_field.to_field (α : Type.{u}) [s : discrete_field.{u} α] : field.{u} α
@[instance] constant {u} discrete_field.has_decidable_eq (α : Type.{u}) [c : discrete_field.{u} α] (a : α) (b : α) : decidable (eq.{u+1} α a b)
@[instance] constant {u} discrete_field.to_integral_domain (α : Type.{u}) [_inst_1 : discrete_field.{u} α] [s : discrete_field.{u} α] : integral_domain.{u} α
class {u} linear_ordered_field (α : Type.{u})
@[instance] constant {u} linear_ordered_field.to_linear_ordered_ring (α : Type.{u}) [s : linear_ordered_field.{u} α] : linear_ordered_ring.{u} α
@[instance] constant {u} linear_ordered_field.to_field (α : Type.{u}) [s : linear_ordered_field.{u} α] : field.{u} α
class {u} discrete_linear_ordered_field (α : Type.{u})
@[instance] constant {u} discrete_linear_ordered_field.to_linear_ordered_field (α : Type.{u}) [s : discrete_linear_ordered_field.{u} α] : linear_ordered_field.{u} α
@[instance] constant {u} discrete_linear_ordered_field.to_decidable_linear_ordered_comm_ring (α : Type.{u}) [s : discrete_linear_ordered_field.{u} α] : decidable_linear_ordered_comm_ring.{u} α
@[instance] constant {u} discrete_linear_ordered_field.to_discrete_field (α : Type.{u}) [s : discrete_linear_ordered_field.{u} α] : discrete_field.{u} α
@[instance] constant {} nat.zero_ne_one_class  : zero_ne_one_class.{0} nat
@[instance] constant {} nat.comm_semiring  : comm_semiring.{0} nat
@[instance] constant {} nat.linear_order  : linear_order.{0} nat
def {} p165 : partial_order.{0} nat := infer_instance
def {} p166 : add_comm_semigroup.{0} nat := infer_instance
def {} p167 : distrib.{0} nat := infer_instance
def {} p168 : comm_semigroup.{0} nat := infer_instance
def {} p169 : preorder.{0} nat := infer_instance
@[instance] constant {} nat.decidable_linear_ordered_semiring  : decidable_linear_ordered_semiring.{0} nat
@[instance] constant {} nat.decidable_linear_ordered_cancel_comm_monoid  : decidable_linear_ordered_cancel_comm_monoid.{0} nat
def {} p170 : linear_ordered_semiring.{0} nat := infer_instance
def {} p171 : add_monoid.{0} nat := infer_instance
def {} p172 : ordered_cancel_comm_monoid.{0} nat := infer_instance
def {} p173 : add_comm_monoid.{0} nat := infer_instance
@[instance] constant {} nat.add_comm_monoid  : add_comm_monoid.{0} nat
@[instance] constant {} nat.add_monoid  : add_monoid.{0} nat
def {} p174 : monoid.{0} nat := infer_instance
@[instance] constant {} nat.monoid  : monoid.{0} nat
def {} p175 : comm_monoid.{0} nat := infer_instance
@[instance] constant {} nat.comm_monoid  : comm_monoid.{0} nat
@[instance] constant {} nat.comm_semigroup  : comm_semigroup.{0} nat
def {} p176 : semigroup.{0} nat := infer_instance
@[instance] constant {} nat.semigroup  : semigroup.{0} nat
@[instance] constant {} nat.add_comm_semigroup  : add_comm_semigroup.{0} nat
def {} p177 : add_semigroup.{0} nat := infer_instance
@[instance] constant {} nat.add_semigroup  : add_semigroup.{0} nat
@[instance] constant {} nat.distrib  : distrib.{0} nat
def {} p178 : semiring.{0} nat := infer_instance
@[instance] constant {} nat.semiring  : semiring.{0} nat
def {} p179 : ordered_semiring.{0} nat := infer_instance
@[instance] constant {} nat.ordered_semiring  : ordered_semiring.{0} nat
def {} p180 : linear_order.{0} nat := infer_instance
def {} p181 : decidable_linear_order.{0} nat := infer_instance
constant {u} bit0 : Pi (α : Type.{u}) (s : has_add.{u} α) (a : α), α
def {} p182 : decidable (has_lt.lt.{0} nat nat.has_lt (has_zero.zero.{0} nat nat.has_zero) (bit0.{0} nat nat.has_add (has_one.one.{0} nat nat.has_one))) := infer_instance
def {} p183 : mul_zero_class.{0} nat := infer_instance
def {} p184 : zero_ne_one_class.{0} nat := infer_instance
def {} p185 : has_andthen.{0 0 0} (tactic_state -> (interaction_monad.result.{0} tactic_state punit.{1})) (list.{0} (tactic_state -> (interaction_monad.result.{0} tactic_state punit.{1}))) (tactic_state -> (interaction_monad.result.{0} tactic_state punit.{1})) := infer_instance
def {} p186 : has_dvd.{0} nat := infer_instance
def {} p187 : comm_semiring.{0} nat := infer_instance
def {} p188 : decidable (has_lt.lt.{0} nat nat.has_lt (has_zero.zero.{0} nat nat.has_zero) (has_one.one.{0} nat nat.has_one)) := infer_instance
constant {u} has_dvd.dvd : Pi (α : Type.{u}) (c : has_dvd.{u} α) (a : α) (a : α), Prop
@[instance] constant {} nat.decidable_dvd (a : nat) (b : nat) : decidable (has_dvd.dvd.{0} nat (comm_semiring_has_dvd.{0} nat nat.comm_semiring) a b)
@[instance] constant {u} list.has_subset (α : Type.{u}) : has_subset.{u} (list.{u} α)
@[instance] constant {u_1} list.monad  : monad.{u_1 u_1} list.{u_1}
def {u_1} p189 : monad.{u_1 u_1} list.{u_1} := infer_instance
def {u_1} p190 : applicative.{u_1 u_1} list.{u_1} := infer_instance
@[instance] constant {u_1} list.is_lawful_monad  : is_lawful_monad.{u_1 u_1} list.{u_1} list.monad.{u_1}
@[instance] constant {u_1} list.alternative  : alternative.{u_1 u_1} list.{u_1}
constant {u} bin_tree : Type.{u} -> Type.{u}
@[instance] constant {u} list.bin_tree_to_list (α : Type.{u}) : has_coe.{u+1 u+1} (bin_tree.{u} α) (list.{u} α)
@[instance] constant {u} list.decidable_bex (α : Type.{u}) (p : α -> Prop) [_inst_1 : Pi (a : α), (decidable (p a))] (l : list.{u} α) : decidable (Exists.{u+1} α (fun (x : α), (Exists.{0} (has_mem.mem.{u u} α (list.{u} α) (list.has_mem.{u} α) x l) (fun (H : has_mem.mem.{u u} α (list.{u} α) (list.has_mem.{u} α) x l), (p x)))))
@[instance] constant {u} list.decidable_ball (α : Type.{u}) (p : α -> Prop) [_inst_1 : Pi (a : α), (decidable (p a))] (l : list.{u} α) : decidable (Pi (x : α) (H : has_mem.mem.{u u} α (list.{u} α) (list.has_mem.{u} α) x l), (p x))
def {} p191 : Pi (a : list.{0} char) (b : list.{0} char), (decidable (eq.{1} (list.{0} char) a b)) := infer_instance
@[instance] constant {} string.has_decidable_eq (a : string) (b : string) : decidable (eq.{1} string a b)
constant {} nat.add_assoc : Pi (n : nat) (m : nat) (k : nat), (eq.{1} nat (has_add.add.{0} nat nat.has_add (has_add.add.{0} nat nat.has_add n m) k) (has_add.add.{0} nat nat.has_add n (has_add.add.{0} nat nat.has_add m k)))
def {} p192 : has_coe_t.{1 1} (reflected.{0} (Pi (n : nat) (m : nat) (k : nat), (eq.{1} nat (has_add.add.{0} nat nat.has_add (has_add.add.{0} nat nat.has_add n m) k) (has_add.add.{0} nat nat.has_add n (has_add.add.{0} nat nat.has_add m k)))) nat.add_assoc) (expr bool.tt) := infer_instance
constant {} nat.add_comm : Pi (n : nat) (m : nat), (eq.{1} nat (has_add.add.{0} nat nat.has_add n m) (has_add.add.{0} nat nat.has_add m n))
def {} p193 : has_coe_t.{1 1} (reflected.{0} (Pi (n : nat) (m : nat), (eq.{1} nat (has_add.add.{0} nat nat.has_add n m) (has_add.add.{0} nat nat.has_add m n))) nat.add_comm) (expr bool.tt) := infer_instance
def {} p194 : has_coe_t.{1 1} (reflected.{2} Type nat) (expr bool.tt) := infer_instance
def {} p195 : Pi (a : expr bool.tt) (b : expr bool.tt), (decidable (eq.{1} (expr bool.tt) a b)) := infer_instance
def {} p196 : has_well_founded.{1} nat := infer_instance
constant {u} cond : Pi (a : Type.{u}) (a_1 : bool) (a_1 : a) (a_1 : a), a
def {} p197 : decidable (has_lt.lt.{0} nat nat.has_lt (cond.{0} nat bool.ff (has_one.one.{0} nat nat.has_one) (has_zero.zero.{0} nat nat.has_zero)) (bit0.{0} nat nat.has_add (has_one.one.{0} nat nat.has_one))) := infer_instance
def {} p198 : decidable (has_lt.lt.{0} nat nat.has_lt (cond.{0} nat bool.tt (has_one.one.{0} nat nat.has_one) (has_zero.zero.{0} nat nat.has_zero)) (bit0.{0} nat nat.has_add (has_one.one.{0} nat nat.has_one))) := infer_instance
def {} p199 : has_well_founded.{1} (psigma.{1 1} nat (fun (a : nat), nat)) := infer_instance
def {} p200 : Pi (a : nat) (b : nat), (decidable (eq.{1} nat a b)) := infer_instance
constant {} int : Type
@[instance] constant {} int.decidable_eq (a : int) (b : int) : decidable (eq.{1} int a b)
@[instance] constant {} int.has_coe  : has_coe.{1 1} nat int
@[instance] constant {} int.has_repr  : has_repr.{0} int
@[instance] constant {} int.has_to_string  : has_to_string.{0} int
def {} p201 : has_lift_t.{1 1} nat int := infer_instance
@[instance] constant {} int.has_zero  : has_zero.{0} int
@[instance] constant {} int.has_one  : has_one.{0} int
def {} p202 : has_zero.{0} int := infer_instance
def {} p203 : has_one.{0} int := infer_instance
def {} p204 : has_coe_t.{1 1} nat int := infer_instance
@[instance] constant {} int.has_neg  : has_neg.{0} int
@[instance] constant {} int.has_add  : has_add.{0} int
@[instance] constant {} int.has_mul  : has_mul.{0} int
def {} p205 : has_add.{0} int := infer_instance
def {} p206 : has_mul.{0} int := infer_instance
def {} p207 : has_neg.{0} int := infer_instance
@[instance] constant {} int.has_div  : has_div.{0} int
@[instance] constant {} int.has_mod  : has_mod.{0} int
@[instance] constant {} int.comm_ring  : comm_ring.{0} int
def {} p208 : has_sub.{0} int := infer_instance
@[instance] constant {} int.has_sub  : has_sub.{0} int
def {} p209 : add_comm_monoid.{0} int := infer_instance
@[instance] constant {} int.add_comm_monoid  : add_comm_monoid.{0} int
def {} p210 : add_monoid.{0} int := infer_instance
@[instance] constant {} int.add_monoid  : add_monoid.{0} int
def {} p211 : monoid.{0} int := infer_instance
@[instance] constant {} int.monoid  : monoid.{0} int
def {} p212 : comm_monoid.{0} int := infer_instance
@[instance] constant {} int.comm_monoid  : comm_monoid.{0} int
def {} p213 : comm_semigroup.{0} int := infer_instance
@[instance] constant {} int.comm_semigroup  : comm_semigroup.{0} int
def {} p214 : semigroup.{0} int := infer_instance
@[instance] constant {} int.semigroup  : semigroup.{0} int
def {} p215 : add_comm_semigroup.{0} int := infer_instance
@[instance] constant {} int.add_comm_semigroup  : add_comm_semigroup.{0} int
def {} p216 : add_semigroup.{0} int := infer_instance
@[instance] constant {} int.add_semigroup  : add_semigroup.{0} int
def {} p217 : comm_semiring.{0} int := infer_instance
@[instance] constant {} int.comm_semiring  : comm_semiring.{0} int
def {} p218 : semiring.{0} int := infer_instance
@[instance] constant {} int.semiring  : semiring.{0} int
def {} p219 : ring.{0} int := infer_instance
@[instance] constant {} int.ring  : ring.{0} int
def {} p220 : distrib.{0} int := infer_instance
@[instance] constant {} int.distrib  : distrib.{0} int
@[instance] constant {} int.zero_ne_one_class  : zero_ne_one_class.{0} int
def {} p221 : add_group.{0} int := infer_instance
def {} p222 : add_comm_group.{0} int := infer_instance
def {} p223 : has_mod.{0} int := infer_instance
@[instance] constant {} int.has_le  : has_le.{0} int
def {} p224 : has_le.{0} int := infer_instance
@[instance] constant {} int.has_lt  : has_lt.{0} int
@[instance] constant {} int.decidable_le (a : int) (b : int) : decidable (has_le.le.{0} int int.has_le a b)
def {} p225 : has_lt.{0} int := infer_instance
@[instance] constant {} int.decidable_lt (a : int) (b : int) : decidable (has_lt.lt.{0} int int.has_lt a b)
def {} p226 : add_left_cancel_semigroup.{0} int := infer_instance
@[instance] constant {} int.decidable_linear_ordered_comm_ring  : decidable_linear_ordered_comm_ring.{0} int
def {} p227 : decidable_linear_ordered_comm_group.{0} int := infer_instance
@[instance] constant {} int.decidable_linear_ordered_comm_group  : decidable_linear_ordered_comm_group.{0} int
def {} p228 : linear_order.{0} int := infer_instance
def {} p229 : preorder.{0} int := infer_instance
def {} p230 : ordered_comm_group.{0} int := infer_instance
def {} p231 : ordered_cancel_comm_monoid.{0} int := infer_instance
def {} p232 : integral_domain.{0} int := infer_instance
def {} p233 : linear_ordered_semiring.{0} int := infer_instance
def {} p234 : has_mem.{0 0} char (list.{0} char) := infer_instance
constant {} char.is_whitespace : char -> Prop
@[instance] constant {} char.decidable_is_whitespace (a : char) : decidable (char.is_whitespace a)
constant {} char.is_upper : char -> Prop
@[instance] constant {} char.decidable_is_upper (a : char) : decidable (char.is_upper a)
constant {} char.is_lower : char -> Prop
@[instance] constant {} char.decidable_is_lower (a : char) : decidable (char.is_lower a)
constant {} char.is_alpha : char -> Prop
@[instance] constant {} char.decidable_is_alpha (a : char) : decidable (char.is_alpha a)
constant {} char.is_digit : char -> Prop
@[instance] constant {} char.decidable_is_digit (a : char) : decidable (char.is_digit a)
constant {} char.is_alphanum : char -> Prop
@[instance] constant {} char.decidable_is_alphanum (a : char) : decidable (char.is_alphanum a)
constant {} char.is_punctuation : char -> Prop
@[instance] constant {} char.decidable_is_punctuation (a : char) : decidable (char.is_punctuation a)
def {} p235 : decidable (iff (not (eq.{1} bool bool.ff bool.tt)) (eq.{1} bool bool.ff bool.ff)) := infer_instance
def {} p236 : decidable (iff (not (eq.{1} bool bool.tt bool.tt)) (eq.{1} bool bool.tt bool.ff)) := infer_instance
constant {} bor : bool -> bool -> bool
def {} p237 : decidable (iff (eq.{1} bool (bor bool.ff bool.ff) bool.tt) (or (eq.{1} bool bool.ff bool.tt) (eq.{1} bool bool.ff bool.tt))) := infer_instance
def {} p238 : decidable (iff (eq.{1} bool (bor bool.ff bool.tt) bool.tt) (or (eq.{1} bool bool.ff bool.tt) (eq.{1} bool bool.tt bool.tt))) := infer_instance
def {} p239 : decidable (iff (eq.{1} bool (bor bool.tt bool.ff) bool.tt) (or (eq.{1} bool bool.tt bool.tt) (eq.{1} bool bool.ff bool.tt))) := infer_instance
def {} p240 : decidable (iff (eq.{1} bool (bor bool.tt bool.tt) bool.tt) (or (eq.{1} bool bool.tt bool.tt) (eq.{1} bool bool.tt bool.tt))) := infer_instance
constant {} band : bool -> bool -> bool
def {} p241 : decidable (iff (eq.{1} bool (band bool.ff bool.ff) bool.tt) (and (eq.{1} bool bool.ff bool.tt) (eq.{1} bool bool.ff bool.tt))) := infer_instance
def {} p242 : decidable (iff (eq.{1} bool (band bool.ff bool.tt) bool.tt) (and (eq.{1} bool bool.ff bool.tt) (eq.{1} bool bool.tt bool.tt))) := infer_instance
def {} p243 : decidable (iff (eq.{1} bool (band bool.tt bool.ff) bool.tt) (and (eq.{1} bool bool.tt bool.tt) (eq.{1} bool bool.ff bool.tt))) := infer_instance
def {} p244 : decidable (iff (eq.{1} bool (band bool.tt bool.tt) bool.tt) (and (eq.{1} bool bool.tt bool.tt) (eq.{1} bool bool.tt bool.tt))) := infer_instance
constant {} bxor : bool -> bool -> bool
def {} p245 : decidable (iff (eq.{1} bool (bxor bool.ff bool.ff) bool.tt) (xor (eq.{1} bool bool.ff bool.tt) (eq.{1} bool bool.ff bool.tt))) := infer_instance
def {} p246 : decidable (iff (eq.{1} bool (bxor bool.ff bool.tt) bool.tt) (xor (eq.{1} bool bool.ff bool.tt) (eq.{1} bool bool.tt bool.tt))) := infer_instance
def {} p247 : decidable (iff (eq.{1} bool (bxor bool.tt bool.ff) bool.tt) (xor (eq.{1} bool bool.tt bool.tt) (eq.{1} bool bool.ff bool.tt))) := infer_instance
def {} p248 : decidable (iff (eq.{1} bool (bxor bool.tt bool.tt) bool.tt) (xor (eq.{1} bool bool.tt bool.tt) (eq.{1} bool bool.tt bool.tt))) := infer_instance
@[instance] constant {u} subtype.decidable_eq (α : Type.{u}) (p : α -> Prop) [_inst_1 : Pi (a : α) (b : α), (decidable (eq.{u+1} α a b))] (a : subtype.{u+1} α p) (b : subtype.{u+1} α p) : decidable (eq.{(max 1 (u+1))} (subtype.{u+1} α p) a b)
constant {u} d_array : Pi (n : nat) (α : (fin n) -> Type.{u}), Type.{u}
@[instance] constant {u} d_array.decidable_eq (n : nat) (α : (fin n) -> Type.{u}) [_inst_1 : Pi (i : fin n) (a : α i) (b : α i), (decidable (eq.{u+1} (α i) a b))] (a : d_array.{u} n α) (b : d_array.{u} n α) : decidable (eq.{u+1} (d_array.{u} n α) a b)
constant {u} array : nat -> Type.{u} -> Type.{u}
@[instance] constant {u} array.has_mem (n : nat) (α : Type.{u}) : has_mem.{u u} α (array.{u} n α)
@[instance] constant {u} array.has_repr (n : nat) (α : Type.{u}) [_inst_1 : has_repr.{u} α] : has_repr.{u} (array.{u} n α)
@[instance] constant {u} array.has_to_format (n : nat) (α : Type.{u}) [_inst_1 : has_to_format.{u} α] : has_to_format.{u} (array.{u} n α)
@[instance] constant {u} array.has_to_tactic_format (n : nat) (α : Type.{u}) [_inst_1 : has_to_tactic_format.{u} α] : has_to_tactic_format.{u} (array.{u} n α)
@[instance] constant {u} array.decidable_eq (n : nat) (α : Type.{u}) [_inst_1 : Pi (a : α) (b : α), (decidable (eq.{u+1} α a b))] (a : array.{u} n α) (b : array.{u} n α) : decidable (eq.{u+1} (array.{u} n α) a b)
constant {} nat.succ : nat -> nat
@[instance] constant {} fin.has_zero (n : nat) : has_zero.{0} (fin (nat.succ n))
@[instance] constant {} fin.has_one (n : nat) : has_one.{0} (fin (nat.succ n))
@[instance] constant {} fin.has_add (n : nat) : has_add.{0} (fin n)
@[instance] constant {} fin.has_sub (n : nat) : has_sub.{0} (fin n)
@[instance] constant {} fin.has_mul (n : nat) : has_mul.{0} (fin n)
@[instance] constant {} fin.has_mod (n : nat) : has_mod.{0} (fin n)
@[instance] constant {} fin.has_div (n : nat) : has_div.{0} (fin n)
@[instance] constant {} unsigned.has_zero  : has_zero.{0} unsigned
@[instance] constant {} unsigned.has_one  : has_one.{0} unsigned
@[instance] constant {} unsigned.has_add  : has_add.{0} unsigned
@[instance] constant {} unsigned.has_sub  : has_sub.{0} unsigned
@[instance] constant {} unsigned.has_mul  : has_mul.{0} unsigned
@[instance] constant {} unsigned.has_mod  : has_mod.{0} unsigned
@[instance] constant {} unsigned.has_div  : has_div.{0} unsigned
@[instance] constant {} unsigned.has_lt  : has_lt.{0} unsigned
@[instance] constant {} unsigned.has_le  : has_le.{0} unsigned
constant {} rbnode.color : Type
@[instance] constant {} rbnode.color.decidable_eq (a : rbnode.color) (b : rbnode.color) : decidable (eq.{1} rbnode.color a b)
constant {u} rbtree : Pi (α : Type.{u}) (lt : α -> α -> Prop), Type.{u}
@[instance] constant {u} rbtree.has_mem (α : Type.{u}) (lt : α -> α -> Prop) : has_mem.{u u} α (rbtree.{u} α lt)
@[instance] constant {u} rbtree.has_repr (α : Type.{u}) (lt : α -> α -> Prop) [_inst_1 : has_repr.{u} α] : has_repr.{u} (rbtree.{u} α lt)
constant {u v} rbmap : Pi (α : Type.{u}) (β : Type.{v}) (lt : α -> α -> Prop), Type.{max u v}
@[instance] constant {u v} rbmap.has_mem (α : Type.{u}) (β : Type.{v}) (lt : α -> α -> Prop) : has_mem.{u (max u v)} α (rbmap.{u v} α β lt)
@[instance] constant {u v} rbmap.has_repr (α : Type.{u}) (β : Type.{v}) (lt : α -> α -> Prop) [_inst_1 : has_repr.{u} α] [_inst_2 : has_repr.{v} β] : has_repr.{(max u v)} (rbmap.{u v} α β lt)
def {u_1} p249 : monad.{u_1 u_1} option.{u_1} := infer_instance
def {u_1} p250 : applicative.{u_1 u_1} option.{u_1} := infer_instance
@[instance] constant {u_1} option.is_lawful_monad  : is_lawful_monad.{u_1 u_1} option.{u_1} option.monad.{u_1}
end test
