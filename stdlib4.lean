namespace test
class decidable (p : Prop)
class has_zero.{u} (α : Type.{u})
class has_one.{u} (α : Type.{u})
class has_add.{u} (α : Type.{u})
class has_mul.{u} (α : Type.{u})
class has_inv.{u} (α : Type.{u})
class has_neg.{u} (α : Type.{u})
class has_sub.{u} (α : Type.{u})
class has_div.{u} (α : Type.{u})
class has_dvd.{u} (α : Type.{u})
class has_mod.{u} (α : Type.{u})
class has_le.{u} (α : Type.{u})
class has_lt.{u} (α : Type.{u})
class has_append.{u} (α : Type.{u})
class has_andthen.{u, v, w} (α : Type.{u}) (β : Type.{v}) (σ : Type.{w})
class has_union.{u} (α : Type.{u})
class has_inter.{u} (α : Type.{u})
class has_sdiff.{u} (α : Type.{u})
class has_equiv.{u} (α : Sort.{u})
class has_subset.{u} (α : Type.{u})
class has_ssubset.{u} (α : Type.{u})
class has_emptyc.{u} (α : Type.{u})
class has_insert.{u, v} (α : Type.{u}) (γ : Type.{v})
class has_sep.{u, v} (α : Type.{u}) (γ : Type.{v})
class has_mem.{u, v} (α : Type.{u}) (γ : Type.{v})
class has_pow.{u, v} (α : Type.{u}) (β : Type.{v})
axiom nat : Type
@[instance] axiom nat.has_zero  : has_zero.{0} nat
@[instance] axiom nat.has_one  : has_one.{0} nat
@[instance] axiom nat.has_add  : has_add.{0} nat
#synth has_one.{0} nat
#synth has_add.{0} nat
class has_sizeof.{u} (α : Sort.{u})
#synth has_zero.{0} nat
axiom true : Prop
@[instance] axiom decidable.true  : decidable true
axiom false : Prop
@[instance] axiom decidable.false  : decidable false
axiom and : Prop -> Prop -> Prop
@[instance] axiom and.decidable (p : Prop) (q : Prop) [_inst_1 : decidable p] [_inst_2 : decidable q] : decidable (and p q)
axiom or : Prop -> Prop -> Prop
@[instance] axiom or.decidable (p : Prop) (q : Prop) [_inst_1 : decidable p] [_inst_2 : decidable q] : decidable (or p q)
axiom not : Prop -> Prop
@[instance] axiom not.decidable (p : Prop) [_inst_1 : decidable p] : decidable (not p)
@[instance] axiom implies.decidable (p : Prop) (q : Prop) [_inst_1 : decidable p] [_inst_2 : decidable q] : decidable (p -> q)
axiom iff : Prop -> Prop -> Prop
@[instance] axiom iff.decidable (p : Prop) (q : Prop) [_inst_1 : decidable p] [_inst_2 : decidable q] : decidable (iff p q)
axiom xor : Prop -> Prop -> Prop
@[instance] axiom xor.decidable (p : Prop) (q : Prop) [_inst_1 : decidable p] [_inst_2 : decidable q] : decidable (xor p q)
axiom Exists.{u} : forall (α : Sort.{u}) (p : α -> Prop), Prop
@[instance] axiom exists_prop_decidable (p : Prop) (P : p -> Prop) [Dp : decidable p] [DP : forall (h : p), (decidable (P h))] : decidable (Exists.{0} p P)
@[instance] axiom forall_prop_decidable (p : Prop) (P : p -> Prop) [Dp : decidable p] [DP : forall (h : p), (decidable (P h))] : decidable (forall (h : p), (P h))
#synth decidable false
axiom eq.{u} : forall (α : Sort.{u}) (a : α) (a : α), Prop
@[instance] axiom ne.decidable.{u} (α : Sort.{u}) [_inst_1 : forall (a : α) (b : α), (decidable (eq.{u} α a b))] (a : α) (b : α) : decidable (not (eq.{u} α a b))
axiom bool : Type
@[instance] axiom bool.decidable_eq (a : bool) (b : bool) : decidable (eq.{1} bool a b)
class inhabited.{u} (α : Sort.{u})
@[instance] axiom prop.inhabited  : inhabited.{1} Prop
@[instance] axiom fun.inhabited.{u, v} (α : Sort.{u}) (β : Sort.{v}) [h : inhabited.{v} β] : inhabited.{(imax u v)} (α -> β)
@[instance] axiom pi.inhabited.{u, v} (α : Sort.{u}) (β : α -> Sort.{v}) [_inst_1 : forall (x : α), (inhabited.{v} (β x))] : inhabited.{(imax u v)} (forall (x : α), (β x))
@[instance] axiom bool.inhabited  : inhabited.{1} bool
@[instance] axiom true.inhabited  : inhabited.{0} true
class nonempty.{u} (α : Sort.{u})
@[instance] axiom nonempty_of_inhabited.{u} (α : Sort.{u}) [_inst_1 : inhabited.{u} α] : nonempty.{u} α
class subsingleton.{u} (α : Sort.{u})
@[instance] axiom subsingleton_prop (p : Prop) : subsingleton.{0} p
@[instance] axiom decidable.subsingleton (p : Prop) : subsingleton.{1} (decidable p)
axiom ite.{u} : forall (c : Prop) (h : decidable c) (α : Sort.{u}) (t : α) (e : α), α
@[instance] axiom ite.decidable (c : Prop) (t : Prop) (e : Prop) [d_c : decidable c] [d_t : decidable t] [d_e : decidable e] : decidable (ite.{1} c d_c Prop t e)
axiom dite.{u} : forall (c : Prop) (h : decidable c) (α : Sort.{u}) (a : c -> α) (a : (not c) -> α), α
@[instance] axiom dite.decidable (c : Prop) (t : c -> Prop) (e : (not c) -> Prop) [d_c : decidable c] [d_t : forall (h : c), (decidable (t h))] [d_e : forall (h : not c), (decidable (e h))] : decidable (dite.{1} c d_c Prop t e)
axiom prod.{u, v} : Type.{u} -> Type.{v} -> Sort.{max (u+1) (v+1)}
@[instance] axiom prod.inhabited.{u, v} (α : Type.{u}) (β : Type.{v}) [_inst_1 : inhabited.{u+1} α] [_inst_2 : inhabited.{v+1} β] : inhabited.{(max (u+1) (v+1))} (prod.{u, v} α β)
@[instance] axiom prod.decidable_eq.{u, v} (α : Type.{u}) (β : Type.{v}) [h₁ : forall (a : α) (b : α), (decidable (eq.{u+1} α a b))] [h₂ : forall (a : β) (b : β), (decidable (eq.{v+1} β a b))] (a : prod.{u, v} α β) (b : prod.{u, v} α β) : decidable (eq.{(max (u+1) (v+1))} (prod.{u, v} α β) a b)
@[instance] axiom prod.has_lt.{u, v} (α : Type.{u}) (β : Type.{v}) [_inst_1 : has_lt.{u} α] [_inst_2 : has_lt.{v} β] : has_lt.{(max u v)} (prod.{u, v} α β)
axiom has_lt.lt.{u} : forall (α : Type.{u}) (c : has_lt.{u} α) (a : α) (a : α), Prop
@[instance] axiom prod_has_decidable_lt.{u, v} (α : Type.{u}) (β : Type.{v}) [_inst_1 : has_lt.{u} α] [_inst_2 : has_lt.{v} β] [_inst_3 : forall (a : α) (b : α), (decidable (eq.{u+1} α a b))] [_inst_4 : forall (a : β) (b : β), (decidable (eq.{v+1} β a b))] [_inst_5 : forall (a : α) (b : α), (decidable (has_lt.lt.{u} α _inst_1 a b))] [_inst_6 : forall (a : β) (b : β), (decidable (has_lt.lt.{v} β _inst_2 a b))] (s : prod.{u, v} α β) (t : prod.{u, v} α β) : decidable (has_lt.lt.{(max u v)} (prod.{u, v} α β) (prod.has_lt.{u, v} α β _inst_1 _inst_2) s t)
@[instance] axiom nat.has_le  : has_le.{0} nat
@[instance] axiom nat.has_lt  : has_lt.{0} nat
@[instance] axiom nat.has_sub  : has_sub.{0} nat
@[instance] axiom nat.has_mul  : has_mul.{0} nat
@[instance] axiom nat.decidable_eq (a : nat) (b : nat) : decidable (eq.{1} nat a b)
@[instance] axiom nat.inhabited  : inhabited.{1} nat
#synth has_le.{0} nat
#synth has_lt.{0} nat
axiom has_le.le.{u} : forall (α : Type.{u}) (c : has_le.{u} α) (a : α) (a : α), Prop
@[instance] axiom nat.decidable_le (a : nat) (b : nat) : decidable (has_le.le.{0} nat nat.has_le a b)
@[instance] axiom nat.decidable_lt (a : nat) (b : nat) : decidable (has_lt.lt.{0} nat nat.has_lt a b)
#synth has_sub.{0} nat
#synth has_mul.{0} nat
@[instance] axiom nat.has_pow  : has_pow.{0, 0} nat nat
#synth has_pow.{0, 0} nat nat
class has_well_founded.{u} (α : Sort.{u})
@[instance] axiom has_well_founded_of_has_sizeof.{u} (α : Sort.{u}) [_inst_1 : has_sizeof.{u} α] : has_well_founded.{u} α
@[instance] axiom prod.has_well_founded.{u, v} (α : Type.{u}) (β : Type.{v}) [s₁ : has_well_founded.{u+1} α] [s₂ : has_well_founded.{v+1} β] : has_well_founded.{(max (u+1) (v+1))} (prod.{u, v} α β)
class setoid.{u} (α : Sort.{u})
@[instance] axiom setoid_has_equiv.{u} (α : Sort.{u}) [_inst_1 : setoid.{u} α] : has_equiv.{u} α
axiom has_equiv.equiv.{u} : forall (α : Sort.{u}) (c : has_equiv.{u} α) (a : α) (a : α), Prop
axiom quotient.{u} : forall (α : Sort.{u}) (s : setoid.{u} α), Sort.{u}
@[instance] axiom quotient.decidable_eq.{u} (α : Sort.{u}) (s : setoid.{u} α) [d : forall (a : α) (b : α), (decidable (has_equiv.equiv.{u} α (setoid_has_equiv.{u} α s) a b))] (a : quotient.{u} α s) (b : quotient.{u} α s) : decidable (eq.{u} (quotient.{u} α s) a b)
@[instance] axiom pi.subsingleton.{u, v} (α : Sort.{u}) (β : α -> Sort.{v}) [_inst_1 : forall (a : α), (subsingleton.{v} (β a))] : subsingleton.{(imax u v)} (forall (a : α), (β a))
axiom list.{u} : Type.{u} -> Type.{u}
@[instance] axiom list.inhabited.{u} (α : Type.{u}) : inhabited.{u+1} (list.{u} α)
@[instance] axiom list.decidable_eq.{u} (α : Type.{u}) [_inst_1 : forall (a : α) (b : α), (decidable (eq.{u+1} α a b))] (a : list.{u} α) (b : list.{u} α) : decidable (eq.{u+1} (list.{u} α) a b)
@[instance] axiom list.has_append.{u} (α : Type.{u}) : has_append.{u} (list.{u} α)
@[instance] axiom list.has_mem.{u} (α : Type.{u}) : has_mem.{u, u} α (list.{u} α)
axiom has_mem.mem.{u, v} : forall (α : Type.{u}) (γ : Type.{v}) (c : has_mem.{u, v} α γ) (a : α) (a : γ), Prop
@[instance] axiom list.decidable_mem.{u} (α : Type.{u}) [_inst_1 : forall (a : α) (b : α), (decidable (eq.{u+1} α a b))] (a : α) (l : list.{u} α) : decidable (has_mem.mem.{u, u} α (list.{u} α) (list.has_mem.{u} α) a l)
@[instance] axiom list.has_emptyc.{u} (α : Type.{u}) : has_emptyc.{u} (list.{u} α)
@[instance] axiom list.has_insert.{u} (α : Type.{u}) [_inst_1 : forall (a : α) (b : α), (decidable (eq.{u+1} α a b))] : has_insert.{u, u} α (list.{u} α)
@[instance] axiom list.has_union.{u} (α : Type.{u}) [_inst_1 : forall (a : α) (b : α), (decidable (eq.{u+1} α a b))] : has_union.{u} (list.{u} α)
@[instance] axiom list.has_inter.{u} (α : Type.{u}) [_inst_1 : forall (a : α) (b : α), (decidable (eq.{u+1} α a b))] : has_inter.{u} (list.{u} α)
@[instance] axiom list.has_lt.{u} (α : Type.{u}) [_inst_1 : has_lt.{u} α] : has_lt.{u} (list.{u} α)
@[instance] axiom list.has_decidable_lt.{u} (α : Type.{u}) [_inst_1 : has_lt.{u} α] [h : forall (a : α) (b : α), (decidable (has_lt.lt.{u} α _inst_1 a b))] (l₁ : list.{u} α) (l₂ : list.{u} α) : decidable (has_lt.lt.{u} (list.{u} α) (list.has_lt.{u} α _inst_1) l₁ l₂)
@[instance] axiom list.has_le.{u} (α : Type.{u}) [_inst_1 : has_lt.{u} α] : has_le.{u} (list.{u} α)
@[instance] axiom list.has_decidable_le.{u} (α : Type.{u}) [_inst_1 : has_lt.{u} α] [h : forall (a : α) (b : α), (decidable (has_lt.lt.{u} α _inst_1 a b))] (l₁ : list.{u} α) (l₂ : list.{u} α) : decidable (has_le.le.{u} (list.{u} α) (list.has_le.{u} α _inst_1) l₁ l₂)
axiom char : Type
@[instance] axiom char.has_lt  : has_lt.{0} char
@[instance] axiom char.has_le  : has_le.{0} char
#synth has_lt.{0} char
@[instance] axiom char.decidable_lt (a : char) (b : char) : decidable (has_lt.lt.{0} char char.has_lt a b)
#synth has_le.{0} char
@[instance] axiom char.decidable_le (a : char) (b : char) : decidable (has_le.le.{0} char char.has_le a b)
@[instance] axiom char.decidable_eq (a : char) (b : char) : decidable (eq.{1} char a b)
@[instance] axiom char.inhabited  : inhabited.{1} char
#synth has_lt.{0} (list.{0} char)
axiom string : Type
@[instance] axiom string.has_lt  : has_lt.{0} string
#synth has_lt.{0} string
#synth forall (a : char) (b : char), (decidable (has_lt.lt.{0} char char.has_lt a b))
@[instance] axiom string.has_decidable_lt (s₁ : string) (s₂ : string) : decidable (has_lt.lt.{0} string string.has_lt s₁ s₂)
#synth has_append.{0} (list.{0} char)
#synth inhabited.{1} char
@[instance] axiom string.inhabited  : inhabited.{1} string
@[instance] axiom string.has_append  : has_append.{0} string
#synth has_append.{0} string
axiom subtype.{u} : forall (α : Sort.{u}) (p : α -> Prop), Sort.{max 1 u}
@[instance] axiom subtype.inhabited.{u} (α : Type.{u}) (p : α -> Prop) (a : α) (h : p a) : inhabited.{(max 1 (u+1))} (subtype.{u+1} α p)
axiom fin : nat -> Type
@[instance] axiom fin.has_lt (n : nat) : has_lt.{0} (fin n)
@[instance] axiom fin.has_le (n : nat) : has_le.{0} (fin n)
@[instance] axiom fin.decidable_lt (n : nat) (a : fin n) (b : fin n) : decidable (has_lt.lt.{0} (fin n) (fin.has_lt n) a b)
@[instance] axiom fin.decidable_le (n : nat) (a : fin n) (b : fin n) : decidable (has_le.le.{0} (fin n) (fin.has_le n) a b)
@[instance] axiom fin.decidable_eq (n : nat) (a : fin n) (b : fin n) : decidable (eq.{1} (fin n) a b)
axiom unsigned : Type
@[instance] axiom unsigned.decidable_eq (a : unsigned) (b : unsigned) : decidable (eq.{1} unsigned a b)
axiom sum.{u, v} : Type.{u} -> Type.{v} -> Sort.{max (u+1) (v+1)}
@[instance] axiom sum.inhabited_left.{u, v} (α : Type.{u}) (β : Type.{v}) [h : inhabited.{u+1} α] : inhabited.{(max (u+1) (v+1))} (sum.{u, v} α β)
@[instance] axiom sum.inhabited_right.{u, v} (α : Type.{u}) (β : Type.{v}) [h : inhabited.{v+1} β] : inhabited.{(max (u+1) (v+1))} (sum.{u, v} α β)
@[instance] axiom nat.has_div  : has_div.{0} nat
#synth has_div.{0} nat
@[instance] axiom nat.has_mod  : has_mod.{0} nat
#synth has_mod.{0} nat
class has_repr.{u} (α : Type.{u})
@[instance] axiom bool.has_repr  : has_repr.{0} bool
@[instance] axiom decidable.has_repr (p : Prop) : has_repr.{0} (decidable p)
@[instance] axiom list.has_repr.{u} (α : Type.{u}) [_inst_1 : has_repr.{u} α] : has_repr.{u} (list.{u} α)
axiom punit.{u} : Sort.{u}
@[instance] axiom unit.has_repr  : has_repr.{0} punit.{1}
axiom option.{u} : Type.{u} -> Type.{u}
@[instance] axiom option.has_repr.{u} (α : Type.{u}) [_inst_1 : has_repr.{u} α] : has_repr.{u} (option.{u} α)
@[instance] axiom sum.has_repr.{u, v} (α : Type.{u}) (β : Type.{v}) [_inst_1 : has_repr.{u} α] [_inst_2 : has_repr.{v} β] : has_repr.{(max u v)} (sum.{u, v} α β)
@[instance] axiom prod.has_repr.{u, v} (α : Type.{u}) (β : Type.{v}) [_inst_1 : has_repr.{u} α] [_inst_2 : has_repr.{v} β] : has_repr.{(max u v)} (prod.{u, v} α β)
axiom sigma.{u, v} : forall (α : Type.{u}) (β : α -> Type.{v}), Sort.{max (u+1) (v+1)}
@[instance] axiom sigma.has_repr.{u, v} (α : Type.{u}) (β : α -> Type.{v}) [_inst_1 : has_repr.{u} α] [s : forall (x : α), (has_repr.{v} (β x))] : has_repr.{(max u v)} (sigma.{u, v} α β)
@[instance] axiom subtype.has_repr.{u} (α : Type.{u}) (p : α -> Prop) [_inst_1 : has_repr.{u} α] : has_repr.{u} (subtype.{u+1} α p)
@[instance] axiom nat.has_repr  : has_repr.{0} nat
@[instance] axiom char.has_repr  : has_repr.{0} char
@[instance] axiom string.has_repr  : has_repr.{0} string
#synth has_repr.{0} nat
@[instance] axiom fin.has_repr (n : nat) : has_repr.{0} (fin n)
@[instance] axiom unsigned.has_repr  : has_repr.{0} unsigned
#synth has_repr.{0} char
axiom ordering : Type
@[instance] axiom ordering.has_repr  : has_repr.{0} ordering
@[instance] axiom ordering.decidable_eq (a : ordering) (b : ordering) : decidable (eq.{1} ordering a b)
class has_lift.{u, v} (a : Sort.{u}) (b : Sort.{v})
class has_lift_t.{u, v} (a : Sort.{u}) (b : Sort.{v})
class has_coe.{u, v} (a : Sort.{u}) (b : Sort.{v})
class has_coe_t.{u, v} (a : Sort.{u}) (b : Sort.{v})
class has_coe_to_fun.{u, v} (a : Sort.{u})
class has_coe_to_sort.{u, v} (a : Sort.{u})
@[instance] axiom lift_trans.{u₁, u₂, u₃} (a : Sort.{u₁}) (b : Sort.{u₂}) (c : Sort.{u₃}) [_inst_1 : has_lift.{u₁, u₂} a b] [_inst_2 : has_lift_t.{u₂, u₃} b c] : has_lift_t.{u₁, u₃} a c
@[instance] axiom lift_base.{u, v} (a : Sort.{u}) (b : Sort.{v}) [_inst_1 : has_lift.{u, v} a b] : has_lift_t.{u, v} a b
@[instance] axiom coe_trans.{u₁, u₂, u₃} (a : Sort.{u₁}) (b : Sort.{u₂}) (c : Sort.{u₃}) [_inst_1 : has_coe.{u₁, u₂} a b] [_inst_2 : has_coe_t.{u₂, u₃} b c] : has_coe_t.{u₁, u₃} a c
@[instance] axiom coe_base.{u, v} (a : Sort.{u}) (b : Sort.{v}) [_inst_1 : has_coe.{u, v} a b] : has_coe_t.{u, v} a b
@[instance] axiom coe_option.{u} (a : Type.{u}) : has_coe_t.{u+1, u+1} a (option.{u} a)
class has_coe_t_aux.{u, v} (a : Sort.{u}) (b : Sort.{v})
@[instance] axiom coe_trans_aux.{u₁, u₂, u₃} (a : Sort.{u₁}) (b : Sort.{u₂}) (c : Sort.{u₃}) [_inst_1 : has_coe.{u₁, u₂} a b] [_inst_2 : has_coe_t_aux.{u₂, u₃} b c] : has_coe_t_aux.{u₁, u₃} a c
@[instance] axiom coe_base_aux.{u, v} (a : Sort.{u}) (b : Sort.{v}) [_inst_1 : has_coe.{u, v} a b] : has_coe_t_aux.{u, v} a b
@[instance] axiom coe_fn_trans.{u₁, u₂, u₃} (a : Sort.{u₁}) (b : Sort.{u₂}) [_inst_1 : has_coe_t_aux.{u₁, u₂} a b] [_inst_2 : has_coe_to_fun.{u₂, u₃} b] : has_coe_to_fun.{u₁, u₃} a
@[instance] axiom coe_sort_trans.{u₁, u₂, u₃} (a : Sort.{u₁}) (b : Sort.{u₂}) [_inst_1 : has_coe_t_aux.{u₁, u₂} a b] [_inst_2 : has_coe_to_sort.{u₂, u₃} b] : has_coe_to_sort.{u₁, u₃} a
@[instance] axiom coe_to_lift.{u, v} (a : Sort.{u}) (b : Sort.{v}) [_inst_1 : has_coe_t.{u, v} a b] : has_lift_t.{u, v} a b
@[instance] axiom coe_bool_to_Prop  : has_coe.{1, 1} bool Prop
@[instance] axiom coe_sort_bool  : has_coe_to_sort.{1, 1} bool
#synth has_lift_t.{1, 1} bool Prop
axiom lift_t.{u, v} : forall (a : Sort.{u}) (b : Sort.{v}) (_inst_1 : has_lift_t.{u, v} a b) (a : a), b
@[instance] axiom coe_decidable_eq (x : bool) : decidable (lift_t.{1, 1} bool Prop (coe_to_lift.{1, 1} bool Prop (coe_base.{1, 1} bool Prop coe_bool_to_Prop)) x)
@[instance] axiom coe_subtype.{u} (a : Sort.{u}) (p : a -> Prop) : has_coe.{(max 1 u) u} (subtype.{u} a p) a
@[instance] axiom lift_fn.{ua₁, ua₂, ub₁, ub₂} (a₁ : Sort.{ua₁}) (a₂ : Sort.{ua₂}) (b₁ : Sort.{ub₁}) (b₂ : Sort.{ub₂}) [_inst_1 : has_lift.{ua₂, ua₁} a₂ a₁] [_inst_2 : has_lift_t.{ub₁, ub₂} b₁ b₂] : has_lift.{(imax ua₁ ub₁) (imax ua₂ ub₂)} (a₁ -> b₁) (a₂ -> b₂)
@[instance] axiom lift_fn_range.{ua, ub₁, ub₂} (a : Sort.{ua}) (b₁ : Sort.{ub₁}) (b₂ : Sort.{ub₂}) [_inst_1 : has_lift_t.{ub₁, ub₂} b₁ b₂] : has_lift.{(imax ua ub₁) (imax ua ub₂)} (a -> b₁) (a -> b₂)
@[instance] axiom lift_fn_dom.{ua₁, ua₂, ub} (a₁ : Sort.{ua₁}) (a₂ : Sort.{ua₂}) (b : Sort.{ub}) [_inst_1 : has_lift.{ua₂, ua₁} a₂ a₁] : has_lift.{(imax ua₁ ub) (imax ua₂ ub)} (a₁ -> b) (a₂ -> b)
@[instance] axiom lift_pair.{ua₁, ub₁, ub₂} (a₁ : Type.{ua₁}) (a₂ : Type.{ub₂}) (b₁ : Type.{ub₁}) (b₂ : Type.{ub₂}) [_inst_1 : has_lift_t.{ua₁+1, ub₂+1} a₁ a₂] [_inst_2 : has_lift_t.{ub₁+1, ub₂+1} b₁ b₂] : has_lift.{(max (ua₁+1) (ub₁+1)) ub₂+1} (prod.{ua₁, ub₁} a₁ b₁) (prod.{ub₂, ub₂} a₂ b₂)
@[instance] axiom lift_pair₁.{ua₁, ua₂, ub} (a₁ : Type.{ua₁}) (a₂ : Type.{ua₂}) (b : Type.{ub}) [_inst_1 : has_lift_t.{ua₁+1, ua₂+1} a₁ a₂] : has_lift.{(max (ua₁+1) (ub+1)) (max (ua₂+1) (ub+1))} (prod.{ua₁, ub} a₁ b) (prod.{ua₂, ub} a₂ b)
@[instance] axiom lift_pair₂.{ua, ub₁, ub₂} (a : Type.{ua}) (b₁ : Type.{ub₁}) (b₂ : Type.{ub₂}) [_inst_1 : has_lift_t.{ub₁+1, ub₂+1} b₁ b₂] : has_lift.{(max (ua+1) (ub₁+1)) (max (ua+1) (ub₂+1))} (prod.{ua, ub₁} a b₁) (prod.{ua, ub₂} a b₂)
@[instance] axiom lift_list.{u, v} (a : Type.{u}) (b : Type.{v}) [_inst_1 : has_lift_t.{u+1, v+1} a b] : has_lift.{u+1, v+1} (list.{u} a) (list.{v} b)
class has_to_string.{u} (α : Type.{u})
@[instance] axiom string.has_to_string  : has_to_string.{0} string
@[instance] axiom bool.has_to_string  : has_to_string.{0} bool
@[instance] axiom decidable.has_to_string (p : Prop) : has_to_string.{0} (decidable p)
@[instance] axiom list.has_to_string.{u} (α : Type.{u}) [_inst_1 : has_to_string.{u} α] : has_to_string.{u} (list.{u} α)
@[instance] axiom unit.has_to_string  : has_to_string.{0} punit.{1}
@[instance] axiom nat.has_to_string  : has_to_string.{0} nat
@[instance] axiom char.has_to_string  : has_to_string.{0} char
#synth has_to_string.{0} nat
@[instance] axiom fin.has_to_string (n : nat) : has_to_string.{0} (fin n)
@[instance] axiom unsigned.has_to_string  : has_to_string.{0} unsigned
@[instance] axiom option.has_to_string.{u} (α : Type.{u}) [_inst_1 : has_to_string.{u} α] : has_to_string.{u} (option.{u} α)
@[instance] axiom sum.has_to_string.{u, v} (α : Type.{u}) (β : Type.{v}) [_inst_1 : has_to_string.{u} α] [_inst_2 : has_to_string.{v} β] : has_to_string.{(max u v)} (sum.{u, v} α β)
@[instance] axiom prod.has_to_string.{u, v} (α : Type.{u}) (β : Type.{v}) [_inst_1 : has_to_string.{u} α] [_inst_2 : has_to_string.{v} β] : has_to_string.{(max u v)} (prod.{u, v} α β)
@[instance] axiom sigma.has_to_string.{u, v} (α : Type.{u}) (β : α -> Type.{v}) [_inst_1 : has_to_string.{u} α] [s : forall (x : α), (has_to_string.{v} (β x))] : has_to_string.{(max u v)} (sigma.{u, v} α β)
@[instance] axiom subtype.has_to_string.{u} (α : Type.{u}) (p : α -> Prop) [_inst_1 : has_to_string.{u} α] : has_to_string.{u} (subtype.{u+1} α p)
axiom name : Type
@[instance] axiom name.inhabited  : inhabited.{1} name
@[instance] axiom string_to_name  : has_coe.{1, 1} string name
#synth has_repr.{0} unsigned
@[instance] axiom name.has_to_string  : has_to_string.{0} name
axiom name.lt : name -> name -> Prop
@[instance] axiom name.lt.decidable_rel (a : name) (b : name) : decidable (name.lt a b)
@[instance] axiom name.has_lt  : has_lt.{0} name
@[instance] axiom name.has_decidable_eq (a : name) (b : name) : decidable (eq.{1} name a b)
@[instance] axiom name.has_append  : has_append.{0} name
class functor.{u, v} (f : Type.{u} -> Type.{v})
class has_pure.{u, v} (f : Type.{u} -> Type.{v})
class has_seq.{u, v} (f : Type.{u} -> Type.{v})
class has_seq_left.{u, v} (f : Type.{u} -> Type.{v})
class has_seq_right.{u, v} (f : Type.{u} -> Type.{v})
class applicative.{u, v} (f : Type.{u} -> Type.{v})
@[instance] axiom applicative.to_functor.{u, v} (f : Type.{u} -> Type.{v}) [c : applicative.{u, v} f] : functor.{u, v} f
@[instance] axiom applicative.to_has_pure.{u, v} (f : Type.{u} -> Type.{v}) [c : applicative.{u, v} f] : has_pure.{u, v} f
@[instance] axiom applicative.to_has_seq.{u, v} (f : Type.{u} -> Type.{v}) [c : applicative.{u, v} f] : has_seq.{u, v} f
@[instance] axiom applicative.to_has_seq_left.{u, v} (f : Type.{u} -> Type.{v}) [c : applicative.{u, v} f] : has_seq_left.{u, v} f
@[instance] axiom applicative.to_has_seq_right.{u, v} (f : Type.{u} -> Type.{v}) [c : applicative.{u, v} f] : has_seq_right.{u, v} f
class has_orelse.{u, v} (f : Type.{u} -> Type.{v})
class alternative.{u, v} (f : Type.{u} -> Type.{v})
@[instance] axiom alternative.to_applicative.{u, v} (f : Type.{u} -> Type.{v}) [c : alternative.{u, v} f] : applicative.{u, v} f
@[instance] axiom alternative.to_has_orelse.{u, v} (f : Type.{u} -> Type.{v}) [c : alternative.{u, v} f] : has_orelse.{u, v} f
class has_bind.{u, v} (m : Type.{u} -> Type.{v})
class monad.{u, v} (m : Type.{u} -> Type.{v})
@[instance] axiom monad.to_applicative.{u, v} (m : Type.{u} -> Type.{v}) [c : monad.{u, v} m] : applicative.{u, v} m
@[instance] axiom monad.to_has_bind.{u, v} (m : Type.{u} -> Type.{v}) [c : monad.{u, v} m] : has_bind.{u, v} m
class has_monad_lift.{u, v, w} (m : Type.{u} -> Type.{v}) (n : Type.{u} -> Type.{w})
class has_monad_lift_t.{u, v, w} (m : Type.{u} -> Type.{v}) (n : Type.{u} -> Type.{w})
@[instance] axiom has_monad_lift_t_trans.{u_1, u_2, u_3, u_4} (m : Type.{u_1} -> Type.{u_2}) (n : Type.{u_1} -> Type.{u_3}) (o : Type.{u_1} -> Type.{u_4}) [_inst_1 : has_monad_lift.{u_1, u_3, u_4} n o] [_inst_2 : has_monad_lift_t.{u_1, u_2, u_3} m n] : has_monad_lift_t.{u_1, u_2, u_4} m o
@[instance] axiom has_monad_lift_t_refl.{u_1, u_2} (m : Type.{u_1} -> Type.{u_2}) : has_monad_lift_t.{u_1, u_2, u_2} m m
class monad_functor.{u, v, w} (m : Type.{u} -> Type.{v}) (m' : Type.{u} -> Type.{v}) (n : Type.{u} -> Type.{w}) (n' : Type.{u} -> Type.{w})
class monad_functor_t.{u, v, w} (m : Type.{u} -> Type.{v}) (m' : Type.{u} -> Type.{v}) (n : Type.{u} -> Type.{w}) (n' : Type.{u} -> Type.{w})
@[instance] axiom monad_functor_t_trans.{u_1, u_2, u_3, u_4} (m : Type.{u_1} -> Type.{u_2}) (m' : Type.{u_1} -> Type.{u_2}) (n : Type.{u_1} -> Type.{u_3}) (n' : Type.{u_1} -> Type.{u_3}) (o : Type.{u_1} -> Type.{u_4}) (o' : Type.{u_1} -> Type.{u_4}) [_inst_1 : monad_functor.{u_1, u_3, u_4} n n' o o'] [_inst_2 : monad_functor_t.{u_1, u_2, u_3} m m' n n'] : monad_functor_t.{u_1, u_2, u_4} m m' o o'
@[instance] axiom monad_functor_t_refl.{u_1, u_2} (m : Type.{u_1} -> Type.{u_2}) (m' : Type.{u_1} -> Type.{u_2}) : monad_functor_t.{u_1, u_2, u_2} m m' m m'
class monad_run.{u, v} (out : Type.{u} -> Type.{v}) (m : Type.{u} -> Type.{v})
#synth has_coe_to_sort.{1, 1} bool
@[instance] axiom option.monad.{u_1}  : monad.{u_1, u_1} option.{u_1}
#synth has_pure.{u_1, u_1} option.{u_1}
#synth has_seq.{u_1, u_1} option.{u_1}
@[instance] axiom option.alternative.{u_1}  : alternative.{u_1, u_1} option.{u_1}
@[instance] axiom option.inhabited.{u} (α : Type.{u}) : inhabited.{u+1} (option.{u} α)
@[instance] axiom option.decidable_eq.{u} (α : Type.{u}) [d : forall (a : α) (b : α), (decidable (eq.{u+1} α a b))] (a : option.{u} α) (b : option.{u} α) : decidable (eq.{u+1} (option.{u} α) a b)
axiom options : Type
@[instance] axiom options.has_decidable_eq (a : options) (b : options) : decidable (eq.{1} options a b)
@[instance] axiom options.has_add  : has_add.{0} options
@[instance] axiom options.inhabited  : inhabited.{1} options
axiom format : Type
@[instance] axiom format.inhabited  : inhabited.{1} format
@[instance] axiom format.has_append  : has_append.{0} format
@[instance] axiom format.has_to_string  : has_to_string.{0} format
class has_to_format.{u} (α : Type.{u})
@[instance] axiom format.has_to_format  : has_to_format.{0} format
@[instance] axiom nat_to_format  : has_coe.{1, 1} nat format
@[instance] axiom string_to_format  : has_coe.{1, 1} string format
#synth has_append.{0} format
@[instance] axiom options.has_to_format  : has_to_format.{0} options
@[instance] axiom bool.has_to_format  : has_to_format.{0} bool
@[instance] axiom decidable.has_to_format (p : Prop) : has_to_format.{0} (decidable p)
@[instance] axiom string.has_to_format  : has_to_format.{0} string
@[instance] axiom nat.has_to_format  : has_to_format.{0} nat
#synth has_to_format.{0} nat
@[instance] axiom unsigned.has_to_format  : has_to_format.{0} unsigned
@[instance] axiom char.has_to_format  : has_to_format.{0} char
#synth has_to_format.{0} string
#synth has_coe_t.{1, 1} string format
@[instance] axiom list.has_to_format.{u} (α : Type.{u}) [_inst_1 : has_to_format.{u} α] : has_to_format.{u} (list.{u} α)
@[instance] axiom string.has_to_format  : has_to_format.{0} string
@[instance] axiom name.has_to_format  : has_to_format.{0} name
@[instance] axiom unit.has_to_format  : has_to_format.{0} punit.{1}
@[instance] axiom option.has_to_format.{u} (α : Type.{u}) [_inst_1 : has_to_format.{u} α] : has_to_format.{u} (option.{u} α)
@[instance] axiom sum_has_to_format.{u, v} (α : Type.{u}) (β : Type.{v}) [_inst_1 : has_to_format.{u} α] [_inst_2 : has_to_format.{v} β] : has_to_format.{(max u v)} (sum.{u, v} α β)
@[instance] axiom prod.has_to_format.{u, v} (α : Type.{u}) (β : Type.{v}) [_inst_1 : has_to_format.{u} α] [_inst_2 : has_to_format.{v} β] : has_to_format.{(max u v)} (prod.{u, v} α β)
@[instance] axiom sigma.has_to_format.{u, v} (α : Type.{u}) (β : α -> Type.{v}) [_inst_1 : has_to_format.{u} α] [s : forall (x : α), (has_to_format.{v} (β x))] : has_to_format.{(max u v)} (sigma.{u, v} α β)
@[instance] axiom subtype.has_to_format.{u} (α : Type.{u}) (p : α -> Prop) [_inst_1 : has_to_format.{u} α] : has_to_format.{u} (subtype.{u+1} α p)
class monad_fail.{u, v} (m : Type.{u} -> Type.{v})
@[instance] axiom monad_fail_lift.{u, v} (m : Type.{u} -> Type.{v}) (n : Type.{u} -> Type.{v}) [_inst_1 : has_monad_lift.{u, v, v} m n] [_inst_2 : monad_fail.{u, v} m] [_inst_3 : monad.{u, v} n] : monad_fail.{u, v} n
#synth has_to_string.{0} format
axiom exceptional : Type -> Type
@[instance] axiom exceptional.has_to_string (α : Type) [_inst_1 : has_to_string.{0} α] : has_to_string.{0} (exceptional α)
@[instance] axiom exceptional.monad  : monad.{0, 0} exceptional
axiom level : Type
@[instance] axiom level.inhabited  : inhabited.{1} level
@[instance] axiom level.has_decidable_eq (a : level) (b : level) : decidable (eq.{1} level a b)
@[instance] axiom level.has_to_string  : has_to_string.{0} level
@[instance] axiom level.has_to_format  : has_to_format.{0} level
#synth forall (a : nat) (b : nat), (decidable (has_lt.lt.{0} nat nat.has_lt a b))
axiom native.rb_map.{u₁, u₂} : Type.{u₁} -> Type.{u₂} -> Type.{max u₁ u₂}
@[instance] axiom native.has_to_format (key : Type) (data : Type) [_inst_1 : has_to_format.{0} key] [_inst_2 : has_to_format.{0} data] : has_to_format.{0} (native.rb_map.{0, 0} key data)
@[instance] axiom native.has_to_string (key : Type) (data : Type) [_inst_1 : has_to_string.{0} key] [_inst_2 : has_to_string.{0} data] : has_to_string.{0} (native.rb_map.{0, 0} key data)
axiom native.rb_set.{u_1} : Type.{u_1} -> Type.{u_1}
@[instance] axiom native.rb_set.has_to_format (key : Type) [_inst_1 : has_to_format.{0} key] : has_to_format.{0} (native.rb_set.{0} key)
#synth has_to_format.{0} name
axiom name_set : Type
@[instance] axiom name_set.has_to_format  : has_to_format.{0} name_set
axiom pos : Type
@[instance] axiom pos.decidable_eq (a : pos) (b : pos) : decidable (eq.{1} pos a b)
#synth has_coe_t.{1, 1} nat format
@[instance] axiom pos.has_to_format  : has_to_format.{0} pos
axiom binder_info : Type
@[instance] axiom binder_info.has_repr  : has_repr.{0} binder_info
axiom expr : bool -> Type
axiom bool.tt : bool
@[instance] axiom expr.inhabited  : inhabited.{1} (expr bool.tt)
@[instance] axiom expr.has_decidable_eq (a : expr bool.tt) (b : expr bool.tt) : decidable (eq.{1} (expr bool.tt) a b)
@[instance] axiom expr.has_to_string (elab : bool) : has_to_string.{0} (expr elab)
@[instance] axiom expr.has_to_format (elab : bool) : has_to_format.{0} (expr elab)
@[instance] axiom expr.has_coe_to_fun (elab : bool) : has_coe_to_fun.{1, 1} (expr elab)
class reflected.{u} (α : Sort.{u}) (a : α)
@[instance] axiom expr.reflect (elab : bool) (e : expr elab) : reflected.{1} (expr elab) e
@[instance] axiom string.reflect (s : string) : reflected.{1} string s
@[instance] axiom expr.has_coe.{u} (α : Sort.{u}) (a : α) : has_coe.{1, 1} (reflected.{u} α a) (expr bool.tt)
#synth has_to_format.{0} (expr bool.tt)
@[instance] axiom reflected.has_to_format.{u_1} (α : Sort.{u_1}) (a : α) : has_to_format.{0} (reflected.{u_1} α a)
axiom expr.expr.lt_prop : (expr bool.tt) -> (expr bool.tt) -> Prop
@[instance] axiom expr.decidable_rel (a : expr bool.tt) (b : expr bool.tt) : decidable (expr.expr.lt_prop a b)
@[instance] axiom expr.has_lt  : has_lt.{0} (expr bool.tt)
#synth has_coe_to_fun.{1, 1} (expr bool.tt)
#synth has_to_format.{0} level
#synth has_to_format.{0} (list.{0} level)
#synth has_repr.{0} binder_info
#synth has_lt.{0} (expr bool.tt)
#synth forall (a : expr bool.tt) (b : expr bool.tt), (decidable (has_lt.lt.{0} (expr bool.tt) expr.has_lt a b))
#synth inhabited.{1} (expr bool.tt)
axiom environment : Type
@[instance] axiom environment.has_repr  : has_repr.{0} environment
@[instance] axiom environment.inhabited  : inhabited.{1} environment
class has_to_pexpr.{u} (α : Sort.{u})
axiom bool.ff : bool
@[instance] axiom pexpr.has_to_pexpr  : has_to_pexpr.{1} (expr bool.ff)
@[instance] axiom expr.has_to_pexpr  : has_to_pexpr.{1} (expr bool.tt)
@[instance] axiom reflected.has_to_pexpr.{u} (α : Sort.{u}) (a : α) : has_to_pexpr.{1} (reflected.{u} α a)
axiom interaction_monad.result.{u} : Type -> Type.{u} -> Type.{u}
@[instance] axiom interaction_monad.result_has_string.{u} (state : Type) (α : Type.{u}) [_inst_1 : has_to_string.{u} α] : has_to_string.{u} (interaction_monad.result.{u} state α)
@[instance] axiom interaction_monad.monad.{u_1} (state : Type) : monad.{u_1, u_1} (fun (α : Type.{u_1}), (state -> (interaction_monad.result.{u_1} state α)))
#synth has_to_format.{0} format
@[instance] axiom interaction_monad.monad_fail.{u_1} (state : Type) : monad_fail.{u_1, u_1} (fun (α : Type.{u_1}), (state -> (interaction_monad.result.{u_1} state α)))
axiom tactic_state : Type
@[instance] axiom tactic_state.has_to_format  : has_to_format.{0} tactic_state
#synth has_to_format.{0} tactic_state
@[instance] axiom tactic_state.has_to_string  : has_to_string.{0} tactic_state
@[instance] axiom tactic.alternative.{u_1}  : alternative.{u_1, u_1} (fun (α : Type.{u_1}), (tactic_state -> (interaction_monad.result.{u_1} tactic_state α)))
#synth has_orelse.{0, 0} (fun (α : Type), (tactic_state -> (interaction_monad.result.{0} tactic_state α)))
#synth has_bind.{0, 0} (fun (α : Type), (tactic_state -> (interaction_monad.result.{0} tactic_state α)))
@[instance] axiom tactic.opt_to_tac.{u} (α : Type.{u}) : has_coe.{u+1, (max, 1, (u+1))} (option.{u} α) (tactic_state -> (interaction_monad.result.{u} tactic_state α))
#synth monad.{0, 0} (fun (α : Type), (tactic_state -> (interaction_monad.result.{0} tactic_state α)))
@[instance] axiom tactic.ex_to_tac (α : Type) : has_coe.{1, 1} (exceptional α) (tactic_state -> (interaction_monad.result.{0} tactic_state α))
class has_to_tactic_format.{u} (α : Type.{u})
@[instance] axiom expr.has_to_tactic_format  : has_to_tactic_format.{0} (expr bool.tt)
#synth functor.{0, 0} (fun (α : Type), (tactic_state -> (interaction_monad.result.{0} tactic_state α)))
#synth has_to_format.{0} (list.{0} format)
@[instance] axiom list.has_to_tactic_format.{u} (α : Type.{u}) [_inst_1 : has_to_tactic_format.{u} α] : has_to_tactic_format.{u} (list.{u} α)
#synth has_seq.{0, 0} (fun (α : Type), (tactic_state -> (interaction_monad.result.{0} tactic_state α)))
#synth has_to_format.{0} (prod.{0, 0} format format)
@[instance] axiom prod.has_to_tactic_format.{u, v} (α : Type.{u}) (β : Type.{v}) [_inst_1 : has_to_tactic_format.{u} α] [_inst_2 : has_to_tactic_format.{v} β] : has_to_tactic_format.{(max u v)} (prod.{u, v} α β)
@[instance] axiom option.has_to_tactic_format.{u} (α : Type.{u}) [_inst_1 : has_to_tactic_format.{u} α] : has_to_tactic_format.{u} (option.{u} α)
#synth has_to_tactic_format.{0} (expr bool.tt)
@[instance] axiom reflected.has_to_tactic_format.{u_1} (α : Sort.{u_1}) (a : α) : has_to_tactic_format.{0} (reflected.{u_1} α a)
@[instance] axiom has_to_format_to_has_to_tactic_format (α : Type) [_inst_1 : has_to_format.{0} α] : has_to_tactic_format.{0} α
axiom declaration : Type
#synth has_coe_t.{1, 1} (exceptional declaration) (tactic_state -> (interaction_monad.result.{0} tactic_state declaration))
#synth has_to_tactic_format.{0} format
axiom tactic.transparency : Type
axiom tactic.new_goals : Type
#synth has_bind.{u_1, u_1} (fun (α : Type.{u_1}), (tactic_state -> (interaction_monad.result.{u_1} tactic_state α)))
#synth has_coe_t.{1, 1} (reflected.{2} Type Prop) (expr bool.tt)
#synth monad.{0, 0} exceptional
#synth has_append.{0} (list.{0} (expr bool.tt))
#synth has_pure.{0, 0} (fun (α : Type), (tactic_state -> (interaction_monad.result.{0} tactic_state α)))
#synth monad_fail.{0, 0} (fun (α : Type), (tactic_state -> (interaction_monad.result.{0} tactic_state α)))
#synth alternative.{0, 0} (fun (α : Type), (tactic_state -> (interaction_monad.result.{0} tactic_state α)))
#synth has_orelse.{u, u} (fun (α : Type.{u}), (tactic_state -> (interaction_monad.result.{u} tactic_state α)))
@[instance] axiom tactic.andthen_seq  : has_andthen.{0, 0, 0} (tactic_state -> (interaction_monad.result.{0} tactic_state punit.{1})) (tactic_state -> (interaction_monad.result.{0} tactic_state punit.{1})) (tactic_state -> (interaction_monad.result.{0} tactic_state punit.{1}))
@[instance] axiom tactic.andthen_seq_focus  : has_andthen.{0, 0, 0} (tactic_state -> (interaction_monad.result.{0} tactic_state punit.{1})) (list.{0} (tactic_state -> (interaction_monad.result.{0} tactic_state punit.{1}))) (tactic_state -> (interaction_monad.result.{0} tactic_state punit.{1}))
#synth has_to_pexpr.{1} (expr bool.ff)
#synth has_to_pexpr.{1} (expr bool.tt)
#synth functor.{u_1, u_1} (fun (α : Type.{u_1}), (tactic_state -> (interaction_monad.result.{u_1} tactic_state α)))
#synth inhabited.{1} name
#synth has_append.{0} name
axiom task.{u} : Type.{u} -> Type.{u}
@[instance] axiom task.monad.{u_1}  : monad.{u_1, u_1} task.{u_1}
#synth has_mem.{0, 0} nat (list.{0} nat)
axiom occurrences : Type
@[instance] axiom occurrences.inhabited  : inhabited.{1} occurrences
#synth has_repr.{0} (list.{0} nat)
@[instance] axiom occurrences.has_repr  : has_repr.{0} occurrences
#synth has_to_format.{0} (list.{0} nat)
@[instance] axiom occurrences.has_to_format  : has_to_format.{0} occurrences
axiom tactic.apply_cfg : Type
axiom has_zero.zero.{u} : forall (α : Type.{u}) (c : has_zero.{u} α), α
axiom has_one.one.{u} : forall (α : Type.{u}) (c : has_one.{u} α), α
@[instance] axiom nat.reflect (a : nat) : reflected.{1} nat a
@[instance] axiom unsigned.reflect (a : unsigned) : reflected.{1} unsigned a
axiom name.anonymous : name
@[instance] axiom name.reflect (a : name) : reflected.{1} name a
@[instance] axiom list.reflect (α : Type) [_inst_1 : forall (a : α), (reflected.{1} α a)] [_inst_2 : reflected.{2} Type α] (a : list.{0} α) : reflected.{1} (list.{0} α) a
axiom punit.star.{u} : punit.{u}
@[instance] axiom punit.reflect (a : punit.{1}) : reflected.{1} punit.{1} a
axiom lean.parser_state : Type
@[instance] axiom lean.parser.alternative  : alternative.{0, 0} (fun (α : Type), (lean.parser_state -> (interaction_monad.result.{0} lean.parser_state α)))
#synth has_orelse.{0, 0} (fun (α : Type), (lean.parser_state -> (interaction_monad.result.{0} lean.parser_state α)))
#synth has_seq.{0, 0} (fun (α : Type), (lean.parser_state -> (interaction_monad.result.{0} lean.parser_state α)))
#synth functor.{0, 0} (fun (α : Type), (lean.parser_state -> (interaction_monad.result.{0} lean.parser_state α)))
#synth monad.{0, 0} (fun (α : Type), (lean.parser_state -> (interaction_monad.result.{0} lean.parser_state α)))
#synth alternative.{0, 0} (fun (α : Type), (lean.parser_state -> (interaction_monad.result.{0} lean.parser_state α)))
#synth has_seq_right.{0, 0} (fun (α : Type), (lean.parser_state -> (interaction_monad.result.{0} lean.parser_state α)))
@[instance] axiom lean.parser.has_coe (α : Type) : has_coe.{1, 1} (tactic_state -> (interaction_monad.result.{0} tactic_state α)) (lean.parser_state -> (interaction_monad.result.{0} lean.parser_state α))
axiom user_attribute_cache_cfg : Type -> Type
axiom user_attribute_cache_cfg.mk : forall (cache_ty : Type) (mk_cache : (list.{0} name) -> tactic_state -> (interaction_monad.result.{0} tactic_state cache_ty)) (dependencies : list.{0} name), (user_attribute_cache_cfg cache_ty)
axiom has_pure.pure.{u, v} : forall (f : Type.{u} -> Type.{v}) (c : has_pure.{u, v} f) (α : Type.{u}) (a : α), (f α)
axiom list.nil.{u} : forall (T : Type.{u}), (list.{u} T)
#synth has_coe_t.{1, 1} (reflected.{1} (user_attribute_cache_cfg punit.{1}) (user_attribute_cache_cfg.mk punit.{1} (fun (_x : list.{0} name), (has_pure.pure.{0, 0} (fun (α : Type), (tactic_state -> (interaction_monad.result.{0} tactic_state α))) (applicative.to_has_pure.{0, 0} (fun (α : Type), (tactic_state -> (interaction_monad.result.{0} tactic_state α))) (alternative.to_applicative.{0, 0} (fun (α : Type), (tactic_state -> (interaction_monad.result.{0} tactic_state α))) tactic.alternative.{0})) punit.{1} punit.star.{1})) (list.nil.{0} name))) (expr bool.tt)
#synth has_pure.{0, 0} (fun (α : Type), (lean.parser_state -> (interaction_monad.result.{0} lean.parser_state α)))
#synth has_coe_t.{1, 1} (reflected.{1} (lean.parser_state -> (interaction_monad.result.{0} lean.parser_state punit.{1})) (has_pure.pure.{0, 0} (fun (α : Type), (lean.parser_state -> (interaction_monad.result.{0} lean.parser_state α))) (applicative.to_has_pure.{0, 0} (fun (α : Type), (lean.parser_state -> (interaction_monad.result.{0} lean.parser_state α))) (alternative.to_applicative.{0, 0} (fun (α : Type), (lean.parser_state -> (interaction_monad.result.{0} lean.parser_state α))) lean.parser.alternative)) punit.{1} punit.star.{1})) (expr bool.tt)
axiom user_attribute : Type -> Type -> Type
#synth has_coe_t.{1, 1} (reflected.{2} Type (user_attribute name_set punit.{1})) (expr bool.tt)
axiom simp_lemmas : Type
@[instance] axiom simp_lemmas.has_to_tactic_format  : has_to_tactic_format.{0} simp_lemmas
axiom tactic.dsimp_config : Type
#synth monad.{0, 0} option.{0}
#synth has_coe_t.{1, 1} (option.{0} (expr bool.tt)) (tactic_state -> (interaction_monad.result.{0} tactic_state (expr bool.tt)))
axiom tactic.simp_config : Type
#synth has_coe_t.{1, 1} (reflected.{2} Type (user_attribute simp_lemmas punit.{1})) (expr bool.tt)
#synth has_coe_t.{1, 1} (reflected.{1} Prop false) (expr bool.tt)
#synth has_coe_t.{1, 1} (expr bool.tt) (option.{0} (expr bool.tt))
#synth has_append.{0} (list.{0} (tactic_state -> (interaction_monad.result.{0} tactic_state punit.{1})))
#synth has_seq_left.{0, 0} (fun (α : Type), (lean.parser_state -> (interaction_monad.result.{0} lean.parser_state α)))
#synth has_append.{0} (list.{0} format)
#synth has_bind.{0, 0} (fun (α : Type), (lean.parser_state -> (interaction_monad.result.{0} lean.parser_state α)))
#synth monad_fail.{0, 0} (fun (α : Type), (lean.parser_state -> (interaction_monad.result.{0} lean.parser_state α)))
axiom cc_state : Type
@[instance] axiom cc_state.has_to_tactic_format  : has_to_tactic_format.{0} cc_state
#synth has_to_tactic_format.{0} cc_state
#synth has_coe_t.{1, 1} (option.{0} name) (tactic_state -> (interaction_monad.result.{0} tactic_state name))
#synth has_append.{0} (list.{0} name)
#synth has_to_format.{0} (expr bool.ff)
axiom derive_handler : Type
@[instance] axiom bool.has_reflect (a : bool) : reflected.{1} bool a
@[instance] axiom prod.has_reflect (α : Type) [a : forall (a : α), (reflected.{1} α a)] (β : Type) [a : forall (a : β), (reflected.{1} β a)] [a : reflected.{2} Type α] [a : reflected.{2} Type β] (a : prod.{0, 0} α β) : reflected.{1} (prod.{0, 0} α β) a
@[instance] axiom sum.has_reflect (α : Type) [a : forall (a : α), (reflected.{1} α a)] (β : Type) [a : forall (a : β), (reflected.{1} β a)] [a : reflected.{2} Type α] [a : reflected.{2} Type β] (a : sum.{0, 0} α β) : reflected.{1} (sum.{0, 0} α β) a
@[instance] axiom option.has_reflect (α : Type) [a : forall (a : α), (reflected.{1} α a)] [a : reflected.{2} Type α] (a : option.{0} α) : reflected.{1} (option.{0} α) a
axiom interactive.loc : Type
axiom interactive.loc.wildcard : interactive.loc
axiom interactive.loc.ns : (list.{0} (option.{0} name)) -> interactive.loc
@[instance] axiom interactive.loc.has_reflect (a : interactive.loc) : reflected.{1} interactive.loc a
axiom pos.mk : nat -> nat -> pos
@[instance] axiom pos.has_reflect (a : pos) : reflected.{1} pos a
#synth has_to_tactic_format.{0} nat
#synth has_to_tactic_format.{0} (list.{0} level)
#synth has_to_tactic_format.{0} (list.{0} (expr bool.tt))
axiom tactic.pattern : Type
@[instance] axiom tactic.has_to_tactic_format  : has_to_tactic_format.{0} tactic.pattern
#synth has_coe_t.{1, 1} nat (option.{0} nat)
axiom tactic.interactive.rw_rule : Type
axiom tactic.interactive.rw_rule.mk : pos -> bool -> (expr bool.ff) -> tactic.interactive.rw_rule
@[instance] axiom tactic.interactive.rw_rule.has_reflect (a : tactic.interactive.rw_rule) : reflected.{1} tactic.interactive.rw_rule a
axiom tactic.interactive.rw_rules_t : Type
axiom tactic.interactive.rw_rules_t.mk : (list.{0} tactic.interactive.rw_rule) -> (option.{0} pos) -> tactic.interactive.rw_rules_t
@[instance] axiom tactic.interactive.rw_rules_t.has_reflect (a : tactic.interactive.rw_rules_t) : reflected.{1} tactic.interactive.rw_rules_t a
#synth monad.{u_1, u_1} (fun (α : Type.{u_1}), (tactic_state -> (interaction_monad.result.{u_1} tactic_state α)))
#synth has_coe_t.{1, 1} (tactic_state -> (interaction_monad.result.{0} tactic_state (prod.{0, 0} (expr bool.ff) name))) (lean.parser_state -> (interaction_monad.result.{0} lean.parser_state (prod.{0, 0} (expr bool.ff) name)))
#synth has_coe_t.{1, 1} name (option.{0} name)
axiom expr.is_local_constant : (expr bool.tt) -> bool
#synth forall (a : expr bool.tt), (decidable (eq.{1} bool (expr.is_local_constant a) bool.tt))
#synth forall (a : name) (b : name), (decidable (eq.{1} name a b))
#synth has_to_string.{0} (list.{0} name)
#synth has_to_string.{0} (list.{0} (list.{0} name))
#synth has_bind.{0, 0} option.{0}
#synth alternative.{0, 0} option.{0}
#synth has_pure.{0, 0} option.{0}
#synth has_mem.{0, 0} (expr bool.tt) (list.{0} (expr bool.tt))
#synth has_orelse.{0, 0} option.{0}
#synth has_to_string.{0} name
#synth has_mem.{0, 0} name (list.{0} name)
axiom tactic.simp_arg_type : Type
axiom tactic.simp_arg_type.all_hyps : tactic.simp_arg_type
axiom tactic.simp_arg_type.except : name -> tactic.simp_arg_type
axiom tactic.simp_arg_type.expr : (expr bool.ff) -> tactic.simp_arg_type
@[instance] axiom tactic.simp_arg_type.has_reflect (a : tactic.simp_arg_type) : reflected.{1} tactic.simp_arg_type a
#synth has_coe_t.{1, 1} simp_lemmas (option.{0} simp_lemmas)
#synth has_coe_t.{1, 1} string name
#synth has_andthen.{0, 0, 0} (tactic_state -> (interaction_monad.result.{0} tactic_state punit.{1})) (tactic_state -> (interaction_monad.result.{0} tactic_state punit.{1})) (tactic_state -> (interaction_monad.result.{0} tactic_state punit.{1}))
axiom id.{u} : forall (α : Sort.{u}) (a : α), α
@[instance] axiom id.monad.{u}  : monad.{u, u} (id.{(u+1)+1} Type.{u})
@[instance] axiom id.monad_run.{u_1}  : monad_run.{u_1, u_1} (id.{(u_1+1)+1} Type.{u_1}) (id.{(u_1+1)+1} Type.{u_1})
axiom except.{u, v} : Type.{u} -> Type.{v} -> Sort.{max (u+1) (v+1)}
@[instance] axiom except.monad.{u, u_1} (ε : Type.{u}) : monad.{u_1, (max, u, u_1)} (except.{u, u_1} ε)
axiom except_t.{u, v} : Type.{u} -> (Type.{u} -> Type.{v}) -> Type.{u} -> Type.{v}
@[instance] axiom except_t.has_monad_lift.{u, v} (ε : Type.{u}) (m : Type.{u} -> Type.{v}) [_inst_1 : monad.{u, v} m] : has_monad_lift.{u, v, v} m (except_t.{u, v} ε m)
@[instance] axiom except_t.monad_functor.{u, v} (ε : Type.{u}) (m : Type.{u} -> Type.{v}) [_inst_1 : monad.{u, v} m] (m' : Type.{u} -> Type.{v}) [_inst_2 : monad.{u, v} m'] : monad_functor.{u, v, v} m m' (except_t.{u, v} ε m) (except_t.{u, v} ε m')
@[instance] axiom except_t.monad.{u, v} (ε : Type.{u}) (m : Type.{u} -> Type.{v}) [_inst_1 : monad.{u, v} m] : monad.{u, v} (except_t.{u, v} ε m)
class monad_except.{u, v, w} (ε : Type.{u}) (m : Type.{v} -> Type.{w})
@[instance] axiom except_t.monad_except.{u_1, u_2} (m : Type.{u_1} -> Type.{u_2}) (ε : Type.{u_1}) [_inst_1 : monad.{u_1, u_2} m] : monad_except.{u_1, u_1, u_2} ε (except_t.{u_1, u_2} ε m)
class monad_except_adapter.{u, v} (ε : Type.{u}) (ε' : Type.{u}) (m : Type.{u} -> Type.{v}) (m' : Type.{u} -> Type.{v})
@[instance] axiom monad_except_adapter_trans.{u, v} (ε : Type.{u}) (ε' : Type.{u}) (m : Type.{u} -> Type.{v}) (m' : Type.{u} -> Type.{v}) (n : Type.{u} -> Type.{v}) (n' : Type.{u} -> Type.{v}) [_inst_1 : monad_functor.{u, v, v} m m' n n'] [_inst_2 : monad_except_adapter.{u, v} ε ε' m m'] : monad_except_adapter.{u, v} ε ε' n n'
@[instance] axiom except_t.monad_except_adapter.{u, v} (ε : Type.{u}) (ε' : Type.{u}) (m : Type.{u} -> Type.{v}) [_inst_1 : monad.{u, v} m] : monad_except_adapter.{u, v} ε ε' (except_t.{u, v} ε m) (except_t.{u, v} ε' m)
@[instance] axiom except_t.monad_run.{u_1, u_2} (ε : Type.{u_1}) (m : Type.{u_1} -> Type.{u_2}) (out : Type.{u_1} -> Type.{u_2}) [_inst_1 : monad_run.{u_1, u_2} out m] : monad_run.{u_1, u_2} (fun (α : Type.{u_1}), (out (except.{u_1, u_1} ε α))) (except_t.{u_1, u_2} ε m)
axiom state_t.{u, v} : Type.{u} -> (Type.{u} -> Type.{v}) -> Type.{u} -> Type.{max u v}
@[instance] axiom state_t.monad.{u, v} (σ : Type.{u}) (m : Type.{u} -> Type.{v}) [_inst_1 : monad.{u, v} m] : monad.{u, (max, u, v)} (state_t.{u, v} σ m)
@[instance] axiom state_t.alternative.{u, v} (σ : Type.{u}) (m : Type.{u} -> Type.{v}) [_inst_1 : monad.{u, v} m] [_inst_2 : alternative.{u, v} m] : alternative.{u, (max, u, v)} (state_t.{u, v} σ m)
@[instance] axiom state_t.has_monad_lift.{u, v} (σ : Type.{u}) (m : Type.{u} -> Type.{v}) [_inst_1 : monad.{u, v} m] : has_monad_lift.{u, v, (max, u, v)} m (state_t.{u, v} σ m)
@[instance] axiom state_t.monad_functor.{u_1, u_2} (σ : Type.{u_1}) (m : Type.{u_1} -> Type.{u_2}) (m' : Type.{u_1} -> Type.{u_2}) [_inst_2 : monad.{u_1, u_2} m] [_inst_3 : monad.{u_1, u_2} m'] : monad_functor.{u_1, u_2, (max, u_1, u_2)} m m' (state_t.{u_1, u_2} σ m) (state_t.{u_1, u_2} σ m')
@[instance] axiom state_t.monad_except.{u, v, u_1} (σ : Type.{u}) (m : Type.{u} -> Type.{v}) [_inst_1 : monad.{u, v} m] (ε : Type.{u_1}) [_inst_2 : monad_except.{u_1, u, v} ε m] : monad_except.{u_1, u, (max, u, v)} ε (state_t.{u, v} σ m)
class monad_state.{u, v} (σ : Type.{u}) (m : Type.{u} -> Type.{v})
@[instance] axiom monad_state_trans.{u, v, w} (σ : Type.{u}) (m : Type.{u} -> Type.{v}) (n : Type.{u} -> Type.{w}) [_inst_1 : has_monad_lift.{u, v, w} m n] [_inst_2 : monad_state.{u, v} σ m] : monad_state.{u, w} σ n
@[instance] axiom state_t.monad_state.{u, v} (σ : Type.{u}) (m : Type.{u} -> Type.{v}) [_inst_1 : monad.{u, v} m] : monad_state.{u, (max, u, v)} σ (state_t.{u, v} σ m)
#synth monad.{u, u} (id.{(u+1)+1} Type.{u})
class monad_state_adapter.{u, v} (σ : Type.{u}) (σ' : Type.{u}) (m : Type.{u} -> Type.{v}) (m' : Type.{u} -> Type.{v})
@[instance] axiom monad_state_adapter_trans.{u, v} (σ : Type.{u}) (σ' : Type.{u}) (m : Type.{u} -> Type.{v}) (m' : Type.{u} -> Type.{v}) (n : Type.{u} -> Type.{v}) (n' : Type.{u} -> Type.{v}) [_inst_1 : monad_functor.{u, v, v} m m' n n'] [_inst_2 : monad_state_adapter.{u, v} σ σ' m m'] : monad_state_adapter.{u, v} σ σ' n n'
@[instance] axiom state_t.monad_state_adapter.{u, v} (σ : Type.{u}) (σ' : Type.{u}) (m : Type.{u} -> Type.{v}) [_inst_1 : monad.{u, v} m] : monad_state_adapter.{u, (max, u, v)} σ σ' (state_t.{u, v} σ m) (state_t.{u, v} σ' m)
@[instance] axiom state_t.monad_run.{u_1, u_2} (σ : Type.{u_1}) (m : Type.{u_1} -> Type.{u_2}) (out : Type.{u_1} -> Type.{u_2}) [_inst_1 : monad_run.{u_1, u_2} out m] : monad_run.{u_1, (max, u_1, u_2)} (fun (α : Type.{u_1}), (σ -> (out (prod.{u_1, u_1} α σ)))) (state_t.{u_1, u_2} σ m)
axiom reader_t.{u, v} : Type.{u} -> (Type.{u} -> Type.{v}) -> Type.{u} -> Type.{max u v}
@[instance] axiom reader_t.monad.{u, v} (ρ : Type.{u}) (m : Type.{u} -> Type.{v}) [_inst_1 : monad.{u, v} m] : monad.{u, (max, u, v)} (reader_t.{u, v} ρ m)
@[instance] axiom reader_t.has_monad_lift.{u, u_1} (ρ : Type.{u}) (m : Type.{u} -> Type.{u_1}) [_inst_2 : monad.{u, u_1} m] : has_monad_lift.{u, u_1, (max, u, u_1)} m (reader_t.{u, u_1} ρ m)
@[instance] axiom reader_t.monad_functor.{u_1, u_2} (ρ : Type.{u_1}) (m : Type.{u_1} -> Type.{u_2}) (m' : Type.{u_1} -> Type.{u_2}) [_inst_2 : monad.{u_1, u_2} m] [_inst_3 : monad.{u_1, u_2} m'] : monad_functor.{u_1, u_2, (max, u_1, u_2)} m m' (reader_t.{u_1, u_2} ρ m) (reader_t.{u_1, u_2} ρ m')
@[instance] axiom reader_t.alternative.{u, v} (ρ : Type.{u}) (m : Type.{u} -> Type.{v}) [_inst_1 : monad.{u, v} m] [_inst_2 : alternative.{u, v} m] : alternative.{u, (max, u, v)} (reader_t.{u, v} ρ m)
@[instance] axiom reader_t.monad_except.{u, v, u_1} (ρ : Type.{u}) (m : Type.{u} -> Type.{v}) [_inst_1 : monad.{u, v} m] (ε : Type.{u_1}) [_inst_2 : monad.{u, v} m] [_inst_3 : monad_except.{u_1, u, v} ε m] : monad_except.{u_1, u, (max, u, v)} ε (reader_t.{u, v} ρ m)
class monad_reader.{u, v} (ρ : Type.{u}) (m : Type.{u} -> Type.{v})
@[instance] axiom monad_reader_trans.{u, v, w} (ρ : Type.{u}) (m : Type.{u} -> Type.{v}) (n : Type.{u} -> Type.{w}) [_inst_1 : has_monad_lift.{u, v, w} m n] [_inst_2 : monad_reader.{u, v} ρ m] : monad_reader.{u, w} ρ n
@[instance] axiom reader_t.monad_reader.{u, v} (ρ : Type.{u}) (m : Type.{u} -> Type.{v}) [_inst_1 : monad.{u, v} m] : monad_reader.{u, (max, u, v)} ρ (reader_t.{u, v} ρ m)
class monad_reader_adapter.{u, v} (ρ : Type.{u}) (ρ' : Type.{u}) (m : Type.{u} -> Type.{v}) (m' : Type.{u} -> Type.{v})
@[instance] axiom monad_reader_adapter_trans.{u, v} (ρ : Type.{u}) (ρ' : Type.{u}) (m : Type.{u} -> Type.{v}) (m' : Type.{u} -> Type.{v}) (n : Type.{u} -> Type.{v}) (n' : Type.{u} -> Type.{v}) [_inst_1 : monad_functor.{u, v, v} m m' n n'] [_inst_2 : monad_reader_adapter.{u, v} ρ ρ' m m'] : monad_reader_adapter.{u, v} ρ ρ' n n'
@[instance] axiom reader_t.monad_reader_adapter.{u, v} (ρ : Type.{u}) (ρ' : Type.{u}) (m : Type.{u} -> Type.{v}) [_inst_1 : monad.{u, v} m] : monad_reader_adapter.{u, (max, u, v)} ρ ρ' (reader_t.{u, v} ρ m) (reader_t.{u, v} ρ' m)
@[instance] axiom reader_t.monad_run.{u, u_1} (ρ : Type.{u}) (m : Type.{u} -> Type.{u_1}) (out : Type.{u} -> Type.{u_1}) [_inst_1 : monad_run.{u, u_1} out m] : monad_run.{u, (max, u, u_1)} (fun (α : Type.{u}), (ρ -> (out α))) (reader_t.{u, u_1} ρ m)
axiom option_t.{u, v} : (Type.{u} -> Type.{v}) -> Type.{u} -> Type.{v}
@[instance] axiom option_t.monad.{u, v} (m : Type.{u} -> Type.{v}) [_inst_1 : monad.{u, v} m] : monad.{u, v} (option_t.{u, v} m)
@[instance] axiom option_t.alternative.{u, v} (m : Type.{u} -> Type.{v}) [_inst_1 : monad.{u, v} m] : alternative.{u, v} (option_t.{u, v} m)
@[instance] axiom option_t.has_monad_lift.{u, v} (m : Type.{u} -> Type.{v}) [_inst_1 : monad.{u, v} m] : has_monad_lift.{u, v, v} m (option_t.{u, v} m)
@[instance] axiom option_t.monad_functor.{u, v} (m : Type.{u} -> Type.{v}) [_inst_1 : monad.{u, v} m] (m' : Type.{u} -> Type.{v}) [_inst_2 : monad.{u, v} m'] : monad_functor.{u, v, v} m m' (option_t.{u, v} m) (option_t.{u, v} m')
@[instance] axiom option_t.monad_except.{u, v} (m : Type.{u} -> Type.{v}) [_inst_1 : monad.{u, v} m] : monad_except.{0, u, v} punit.{1} (option_t.{u, v} m)
@[instance] axiom option_t.monad_run.{u_1, u_2} (m : Type.{u_1} -> Type.{u_2}) (out : Type.{u_1} -> Type.{u_2}) [_inst_2 : monad_run.{u_1, u_2} out m] : monad_run.{u_1, u_2} (fun (α : Type.{u_1}), (out (option.{u_1} α))) (option_t.{u_1, u_2} m)
class is_lawful_functor.{u, v} (f : Type.{u} -> Type.{v}) (_inst_1 : functor.{u, v} f)
class is_lawful_applicative.{u, v} (f : Type.{u} -> Type.{v}) (_inst_1 : applicative.{u, v} f)
@[instance] axiom is_lawful_applicative.to_is_lawful_functor.{u, v} (f : Type.{u} -> Type.{v}) [_inst_1 : applicative.{u, v} f] [c : is_lawful_applicative.{u, v} f _inst_1] : is_lawful_functor.{u, v} f (applicative.to_functor.{u, v} f _inst_1)
class is_lawful_monad.{u, v} (m : Type.{u} -> Type.{v}) (_inst_1 : monad.{u, v} m)
@[instance] axiom is_lawful_monad.to_is_lawful_applicative.{u, v} (m : Type.{u} -> Type.{v}) [_inst_1 : monad.{u, v} m] [c : is_lawful_monad.{u, v} m _inst_1] : is_lawful_applicative.{u, v} m (monad.to_applicative.{u, v} m _inst_1)
#synth functor.{0, 0} (id.{2} Type)
#synth has_bind.{0, 0} (id.{2} Type)
#synth has_pure.{0, 0} (id.{2} Type)
#synth monad.{u_1, u_1} (id.{(u_1+1)+1} Type.{u_1})
#synth applicative.{u_1, u_1} (id.{(u_1+1)+1} Type.{u_1})
@[instance] axiom id.is_lawful_monad.{u_1}  : is_lawful_monad.{u_1, u_1} (id.{(u_1+1)+1} Type.{u_1}) id.monad.{u_1}
@[instance] axiom state_t.is_lawful_monad.{u, v} (m : Type.{u} -> Type.{v}) [_inst_1 : monad.{u, v} m] [_inst_2 : is_lawful_monad.{u, v} m _inst_1] (σ : Type.{u}) : is_lawful_monad.{u, (max, u, v)} (state_t.{u, v} σ m) (state_t.monad.{u, v} σ m _inst_1)
@[instance] axiom except_t.is_lawful_monad.{u, v} (m : Type.{u} -> Type.{v}) [_inst_1 : monad.{u, v} m] [_inst_2 : is_lawful_monad.{u, v} m _inst_1] (ε : Type.{u}) : is_lawful_monad.{u, v} (except_t.{u, v} ε m) (except_t.monad.{u, v} ε m _inst_1)
@[instance] axiom reader_t.is_lawful_monad.{u, v} (ρ : Type.{u}) (m : Type.{u} -> Type.{v}) [_inst_1 : monad.{u, v} m] [_inst_2 : is_lawful_monad.{u, v} m _inst_1] : is_lawful_monad.{u, (max, u, v)} (reader_t.{u, v} ρ m) (reader_t.monad.{u, v} ρ m _inst_1)
@[instance] axiom option_t.is_lawful_monad.{u, v} (m : Type.{u} -> Type.{v}) [_inst_1 : monad.{u, v} m] [_inst_2 : is_lawful_monad.{u, v} m _inst_1] : is_lawful_monad.{u, v} (option_t.{u, v} m) (option_t.monad.{u, v} m _inst_1)
@[instance] axiom punit.subsingleton.{u_1}  : subsingleton.{u_1} punit.{u_1}
@[instance] axiom punit.inhabited  : inhabited.{1} punit.{1}
@[instance] axiom punit.decidable_eq.{u_1} (a : punit.{u_1}) (b : punit.{u_1}) : decidable (eq.{u_1} punit.{u_1} a b)
axiom set.{u} : Type.{u} -> Sort.{max (u+1) 1}
@[instance] axiom set.has_mem.{u} (α : Type.{u}) : has_mem.{u, u} α (set.{u} α)
@[instance] axiom set.has_subset.{u} (α : Type.{u}) : has_subset.{u} (set.{u} α)
@[instance] axiom set.has_sep.{u} (α : Type.{u}) : has_sep.{u, u} α (set.{u} α)
@[instance] axiom set.has_emptyc.{u} (α : Type.{u}) : has_emptyc.{u} (set.{u} α)
@[instance] axiom set.has_insert.{u} (α : Type.{u}) : has_insert.{u, u} α (set.{u} α)
@[instance] axiom set.has_union.{u} (α : Type.{u}) : has_union.{u} (set.{u} α)
@[instance] axiom set.has_inter.{u} (α : Type.{u}) : has_inter.{u} (set.{u} α)
@[instance] axiom set.has_neg.{u} (α : Type.{u}) : has_neg.{u} (set.{u} α)
@[instance] axiom set.has_sdiff.{u} (α : Type.{u}) : has_sdiff.{u} (set.{u} α)
@[instance] axiom set.functor.{u_1}  : functor.{u_1, u_1} set.{u_1}
#synth functor.{u_1, u_1} set.{u_1}
@[instance] axiom set.is_lawful_functor.{u_1}  : is_lawful_functor.{u_1, u_1} set.{u_1} set.functor.{u_1}
#synth decidable (not (eq.{1} nat (has_one.one.{0} nat nat.has_one) (has_zero.zero.{0} nat nat.has_zero)))
axiom param_info : Type
@[instance] axiom param_info.has_to_format  : has_to_format.{0} param_info
#synth has_to_format.{0} (list.{0} param_info)
axiom fun_info : Type
@[instance] axiom fun_info.has_to_format  : has_to_format.{0} fun_info
axiom subsingleton_info : Type
@[instance] axiom subsingleton_info.has_to_format  : has_to_format.{0} subsingleton_info
@[instance] axiom tactic.binder_info.has_decidable_eq (a : binder_info) (b : binder_info) : decidable (eq.{1} binder_info a b)
axiom conv.{u} : Type.{u} -> Sort.{max 1 (u+1)}
@[instance] axiom conv.monad.{u_1}  : monad.{u_1, u_1} conv.{u_1}
#synth monad_fail.{u_1, u_1} (fun (α : Type.{u_1}), (tactic_state -> (interaction_monad.result.{u_1} tactic_state α)))
@[instance] axiom conv.monad_fail.{u_1}  : monad_fail.{u_1, u_1} conv.{u_1}
#synth alternative.{u_1, u_1} (fun (α : Type.{u_1}), (tactic_state -> (interaction_monad.result.{u_1} tactic_state α)))
@[instance] axiom conv.alternative.{u_1}  : alternative.{u_1, u_1} conv.{u_1}
#synth has_bind.{0, 0} conv.{0}
#synth monad.{0, 0} conv.{0}
#synth monad_fail.{0, 0} conv.{0}
#synth alternative.{0, 0} conv.{0}
#synth has_orelse.{0, 0} conv.{0}
axiom vm_obj_kind : Type
@[instance] axiom vm_obj_kind.decidable_eq (a : vm_obj_kind) (b : vm_obj_kind) : decidable (eq.{1} vm_obj_kind a b)
axiom vm_core : Type -> Type
@[instance] axiom vm_core.monad  : monad.{0, 0} vm_core
#synth has_bind.{0, 0} (option_t.{0, 0} vm_core)
#synth monad.{0, 0} (option_t.{0, 0} vm_core)
#synth has_coe_t.{1, 1} (option.{0} (prod.{0, 0} (expr bool.tt) (expr bool.tt))) (tactic_state -> (interaction_monad.result.{0} tactic_state (prod.{0, 0} (expr bool.tt) (expr bool.tt))))
axiom hinst_lemma : Type
@[instance] axiom hinst_lemma.has_to_tactic_format  : has_to_tactic_format.{0} hinst_lemma
axiom hinst_lemmas : Type
@[instance] axiom hinst_lemmas.has_to_tactic_format  : has_to_tactic_format.{0} hinst_lemmas
#synth has_coe_t.{1, 1} (reflected.{2} Type (user_attribute hinst_lemmas punit.{1})) (expr bool.tt)
#synth has_coe_t.{1, 1} (reflected.{2} Type (user_attribute punit.{1} punit.{1})) (expr bool.tt)
axiom cc_config : Type
axiom ematch_config : Type
axiom smt_pre_config : Type
axiom smt_state : Type
@[instance] axiom smt_state.has_append  : has_append.{0} smt_state
#synth monad.{0, 0} (state_t.{0, 0} smt_state (fun (α : Type), (tactic_state -> (interaction_monad.result.{0} tactic_state α))))
@[instance] axiom smt_tactic.monad  : monad.{0, 0} (state_t.{0, 0} smt_state (fun (α : Type), (tactic_state -> (interaction_monad.result.{0} tactic_state α))))
#synth alternative.{0, 0} (state_t.{0, 0} smt_state (fun (α : Type), (tactic_state -> (interaction_monad.result.{0} tactic_state α))))
@[instance] axiom smt_tactic.alternative  : alternative.{0, 0} (state_t.{0, 0} smt_state (fun (α : Type), (tactic_state -> (interaction_monad.result.{0} tactic_state α))))
#synth monad_state.{0, 0} smt_state (state_t.{0, 0} smt_state (fun (α : Type), (tactic_state -> (interaction_monad.result.{0} tactic_state α))))
@[instance] axiom smt_tactic.monad_state  : monad_state.{0, 0} smt_state (state_t.{0, 0} smt_state (fun (α : Type), (tactic_state -> (interaction_monad.result.{0} tactic_state α))))
axiom smt_tactic : Type -> Type
@[instance] axiom smt_tactic.has_monad_lift  : has_monad_lift.{0, 0, 0} (fun (α : Type), (tactic_state -> (interaction_monad.result.{0} tactic_state α))) smt_tactic
#synth has_monad_lift_t.{0, 0, 0} (fun (α : Type), (tactic_state -> (interaction_monad.result.{0} tactic_state α))) smt_tactic
@[instance] axiom smt_tactic.has_coe (α : Type) : has_coe.{1, 1} (tactic_state -> (interaction_monad.result.{0} tactic_state α)) (smt_tactic α)
#synth monad.{0, 0} smt_tactic
@[instance] axiom smt_tactic.monad_fail  : monad_fail.{0, 0} smt_tactic
#synth has_bind.{0, 0} smt_tactic
#synth has_coe_t.{1, 1} (tactic_state -> (interaction_monad.result.{0} tactic_state hinst_lemma)) (smt_tactic hinst_lemma)
#synth has_orelse.{0, 0} smt_tactic
#synth monad_state.{0, 0} smt_state smt_tactic
#synth has_coe_t.{1, 1} (tactic_state -> (interaction_monad.result.{0} tactic_state tactic_state)) (smt_tactic tactic_state)
#synth has_append.{0} smt_state
#synth has_coe_t.{1, 1} (tactic_state -> (interaction_monad.result.{0} tactic_state punit.{1})) (smt_tactic punit.{1})
#synth monad_fail.{0, 0} smt_tactic
#synth has_coe_t.{1, 1} (tactic_state -> (interaction_monad.result.{0} tactic_state (expr bool.tt))) (smt_tactic (expr bool.tt))
#synth functor.{0, 0} smt_tactic
axiom smt_goal : Type
#synth monad_state.{0, 0} (list.{0} smt_goal) smt_tactic
#synth has_coe_t.{1, 1} (tactic_state -> (interaction_monad.result.{0} tactic_state (list.{0} (expr bool.tt)))) (smt_tactic (list.{0} (expr bool.tt)))
#synth has_append.{0} (list.{0} smt_goal)
@[instance] axiom smt_tactic.has_andthen  : has_andthen.{0, 0, 0} (smt_tactic punit.{1}) (smt_tactic punit.{1}) (smt_tactic punit.{1})
#synth has_coe_t.{1, 1} (tactic_state -> (interaction_monad.result.{0} tactic_state (list.{0} (prod.{0, 0} name (expr bool.tt))))) (smt_tactic (list.{0} (prod.{0, 0} name (expr bool.tt))))
#synth has_coe_t.{1, 1} (tactic_state -> (interaction_monad.result.{0} tactic_state bool)) (smt_tactic bool)
#synth alternative.{0, 0} smt_tactic
#synth has_coe_t.{1, 1} (tactic_state -> (interaction_monad.result.{0} tactic_state level)) (smt_tactic level)
#synth has_coe_t.{1, 1} (tactic_state -> (interaction_monad.result.{0} tactic_state name)) (smt_tactic name)
#synth has_coe_t.{1, 1} (tactic_state -> (interaction_monad.result.{0} tactic_state (expr bool.ff))) (smt_tactic (expr bool.ff))
#synth has_coe_t.{1, 1} (tactic_state -> (interaction_monad.result.{0} tactic_state hinst_lemmas)) (smt_tactic hinst_lemmas)
axiom psigma.{u, v} : forall (α : Sort.{u}) (β : α -> Sort.{v}), Sort.{max 1 u v}
@[instance] axiom psigma.has_well_founded.{u, v} (α : Type.{u}) (β : α -> Type.{v}) [s₁ : has_well_founded.{u+1} α] [s₂ : forall (a : α), (has_well_founded.{v+1} (β a))] : has_well_founded.{(max 1 (u+1) (v+1))} (psigma.{u+1, v+1} α β)
class is_symm_op.{u, v} (α : Type.{u}) (β : Type.{v}) (op : α -> α -> β)
class is_commutative.{u} (α : Type.{u}) (op : α -> α -> α)
@[instance] axiom is_symm_op_of_is_commutative.{u} (α : Type.{u}) (op : α -> α -> α) [_inst_1 : is_commutative.{u} α op] : is_symm_op.{u, u} α α op
class is_associative.{u} (α : Type.{u}) (op : α -> α -> α)
class is_left_id.{u} (α : Type.{u}) (op : α -> α -> α) (o : α)
class is_right_id.{u} (α : Type.{u}) (op : α -> α -> α) (o : α)
class is_left_null.{u} (α : Type.{u}) (op : α -> α -> α) (o : α)
class is_right_null.{u} (α : Type.{u}) (op : α -> α -> α) (o : α)
class is_left_cancel.{u} (α : Type.{u}) (op : α -> α -> α)
class is_right_cancel.{u} (α : Type.{u}) (op : α -> α -> α)
class is_idempotent.{u} (α : Type.{u}) (op : α -> α -> α)
class is_left_distrib.{u} (α : Type.{u}) (op₁ : α -> α -> α) (op₂ : α -> α -> α)
class is_right_distrib.{u} (α : Type.{u}) (op₁ : α -> α -> α) (op₂ : α -> α -> α)
class is_left_inv.{u} (α : Type.{u}) (op : α -> α -> α) (inv : α -> α) (o : α)
class is_right_inv.{u} (α : Type.{u}) (op : α -> α -> α) (inv : α -> α) (o : α)
class is_cond_left_inv.{u} (α : Type.{u}) (op : α -> α -> α) (inv : α -> α) (o : α) (p : α -> Prop)
class is_cond_right_inv.{u} (α : Type.{u}) (op : α -> α -> α) (inv : α -> α) (o : α) (p : α -> Prop)
class is_distinct.{u} (α : Type.{u}) (a : α) (b : α)
class is_irrefl.{u} (α : Type.{u}) (r : α -> α -> Prop)
class is_refl.{u} (α : Type.{u}) (r : α -> α -> Prop)
class is_symm.{u} (α : Type.{u}) (r : α -> α -> Prop)
@[instance] axiom is_symm_op_of_is_symm.{u} (α : Type.{u}) (r : α -> α -> Prop) [_inst_1 : is_symm.{u} α r] : is_symm_op.{u, 0} α Prop r
class is_asymm.{u} (α : Type.{u}) (r : α -> α -> Prop)
class is_antisymm.{u} (α : Type.{u}) (r : α -> α -> Prop)
class is_trans.{u} (α : Type.{u}) (r : α -> α -> Prop)
class is_total.{u} (α : Type.{u}) (r : α -> α -> Prop)
class is_preorder.{u} (α : Type.{u}) (r : α -> α -> Prop)
@[instance] axiom is_preorder.to_is_refl.{u} (α : Type.{u}) (r : α -> α -> Prop) [c : is_preorder.{u} α r] : is_refl.{u} α r
@[instance] axiom is_preorder.to_is_trans.{u} (α : Type.{u}) (r : α -> α -> Prop) [c : is_preorder.{u} α r] : is_trans.{u} α r
class is_total_preorder.{u} (α : Type.{u}) (r : α -> α -> Prop)
@[instance] axiom is_total_preorder.to_is_trans.{u} (α : Type.{u}) (r : α -> α -> Prop) [c : is_total_preorder.{u} α r] : is_trans.{u} α r
@[instance] axiom is_total_preorder.to_is_total.{u} (α : Type.{u}) (r : α -> α -> Prop) [c : is_total_preorder.{u} α r] : is_total.{u} α r
@[instance] axiom is_total_preorder_is_preorder.{u} (α : Type.{u}) (r : α -> α -> Prop) [s : is_total_preorder.{u} α r] : is_preorder.{u} α r
class is_partial_order.{u} (α : Type.{u}) (r : α -> α -> Prop)
@[instance] axiom is_partial_order.to_is_preorder.{u} (α : Type.{u}) (r : α -> α -> Prop) [c : is_partial_order.{u} α r] : is_preorder.{u} α r
@[instance] axiom is_partial_order.to_is_antisymm.{u} (α : Type.{u}) (r : α -> α -> Prop) [c : is_partial_order.{u} α r] : is_antisymm.{u} α r
class is_linear_order.{u} (α : Type.{u}) (r : α -> α -> Prop)
@[instance] axiom is_linear_order.to_is_partial_order.{u} (α : Type.{u}) (r : α -> α -> Prop) [c : is_linear_order.{u} α r] : is_partial_order.{u} α r
@[instance] axiom is_linear_order.to_is_total.{u} (α : Type.{u}) (r : α -> α -> Prop) [c : is_linear_order.{u} α r] : is_total.{u} α r
class is_equiv.{u} (α : Type.{u}) (r : α -> α -> Prop)
@[instance] axiom is_equiv.to_is_preorder.{u} (α : Type.{u}) (r : α -> α -> Prop) [c : is_equiv.{u} α r] : is_preorder.{u} α r
@[instance] axiom is_equiv.to_is_symm.{u} (α : Type.{u}) (r : α -> α -> Prop) [c : is_equiv.{u} α r] : is_symm.{u} α r
class is_per.{u} (α : Type.{u}) (r : α -> α -> Prop)
@[instance] axiom is_per.to_is_symm.{u} (α : Type.{u}) (r : α -> α -> Prop) [c : is_per.{u} α r] : is_symm.{u} α r
@[instance] axiom is_per.to_is_trans.{u} (α : Type.{u}) (r : α -> α -> Prop) [c : is_per.{u} α r] : is_trans.{u} α r
class is_strict_order.{u} (α : Type.{u}) (r : α -> α -> Prop)
@[instance] axiom is_strict_order.to_is_irrefl.{u} (α : Type.{u}) (r : α -> α -> Prop) [c : is_strict_order.{u} α r] : is_irrefl.{u} α r
@[instance] axiom is_strict_order.to_is_trans.{u} (α : Type.{u}) (r : α -> α -> Prop) [c : is_strict_order.{u} α r] : is_trans.{u} α r
class is_incomp_trans.{u} (α : Type.{u}) (lt : α -> α -> Prop)
class is_strict_weak_order.{u} (α : Type.{u}) (lt : α -> α -> Prop)
@[instance] axiom is_strict_weak_order.to_is_strict_order.{u} (α : Type.{u}) (lt : α -> α -> Prop) [c : is_strict_weak_order.{u} α lt] : is_strict_order.{u} α lt
@[instance] axiom is_strict_weak_order.to_is_incomp_trans.{u} (α : Type.{u}) (lt : α -> α -> Prop) [c : is_strict_weak_order.{u} α lt] : is_incomp_trans.{u} α lt
class is_trichotomous.{u} (α : Type.{u}) (lt : α -> α -> Prop)
class is_strict_total_order.{u} (α : Type.{u}) (lt : α -> α -> Prop)
@[instance] axiom is_strict_total_order.to_is_trichotomous.{u} (α : Type.{u}) (lt : α -> α -> Prop) [c : is_strict_total_order.{u} α lt] : is_trichotomous.{u} α lt
@[instance] axiom is_strict_total_order.to_is_strict_weak_order.{u} (α : Type.{u}) (lt : α -> α -> Prop) [c : is_strict_total_order.{u} α lt] : is_strict_weak_order.{u} α lt
@[instance] axiom eq_is_equiv.{u} (α : Type.{u}) : is_equiv.{u} α (eq.{u+1} α)
@[instance] axiom is_asymm_of_is_trans_of_is_irrefl.{u} (α : Type.{u}) (r : α -> α -> Prop) [_inst_1 : is_trans.{u} α r] [_inst_2 : is_irrefl.{u} α r] : is_asymm.{u} α r
axiom strict_weak_order.equiv.{u} : forall (α : Type.{u}) (r : α -> α -> Prop) (a : α) (b : α), Prop
@[instance] axiom strict_weak_order.is_equiv.{u} (α : Type.{u}) (r : α -> α -> Prop) [_inst_1 : is_strict_weak_order.{u} α r] : is_equiv.{u} α (strict_weak_order.equiv.{u} α r)
class preorder.{u} (α : Type.{u})
@[instance] axiom preorder.to_has_le.{u} (α : Type.{u}) [s : preorder.{u} α] : has_le.{u} α
@[instance] axiom preorder.to_has_lt.{u} (α : Type.{u}) [s : preorder.{u} α] : has_lt.{u} α
class partial_order.{u} (α : Type.{u})
@[instance] axiom partial_order.to_preorder.{u} (α : Type.{u}) [s : partial_order.{u} α] : preorder.{u} α
class linear_order.{u} (α : Type.{u})
@[instance] axiom linear_order.to_partial_order.{u} (α : Type.{u}) [s : linear_order.{u} α] : partial_order.{u} α
@[instance] axiom decidable_lt_of_decidable_le.{u} (α : Type.{u}) [_inst_1 : preorder.{u} α] [_inst_2 : forall (a : α) (b : α), (decidable (has_le.le.{u} α (preorder.to_has_le.{u} α _inst_1) a b))] (a : α) (b : α) : decidable (has_lt.lt.{u} α (preorder.to_has_lt.{u} α _inst_1) a b)
@[instance] axiom decidable_eq_of_decidable_le.{u} (α : Type.{u}) [_inst_1 : partial_order.{u} α] [_inst_2 : forall (a : α) (b : α), (decidable (has_le.le.{u} α (preorder.to_has_le.{u} α (partial_order.to_preorder.{u} α _inst_1)) a b))] (a : α) (b : α) : decidable (eq.{u+1} α a b)
class decidable_linear_order.{u} (α : Type.{u})
@[instance] axiom decidable_linear_order.to_linear_order.{u} (α : Type.{u}) [s : decidable_linear_order.{u} α] : linear_order.{u} α
axiom preorder.mk.{u} : forall (α : Type.{u}) (le : α -> α -> Prop) (lt : α -> α -> Prop) (le_refl : forall (a : α), (le a a)) (le_trans : forall (a : α) (b : α) (c : α) (a_1 : le a b) (a_1 : le b c), (le a c)) (lt_iff_le_not_le : forall (a : α) (b : α), (iff (lt a b) (and (le a b) (not (le b a))))), (preorder.{u} α)
axiom partial_order.mk.{u} : forall (α : Type.{u}) (le : α -> α -> Prop) (lt : α -> α -> Prop) (le_refl : forall (a : α), (le a a)) (le_trans : forall (a : α) (b : α) (c : α) (a_1 : le a b) (a_1 : le b c), (le a c)) (lt_iff_le_not_le : forall (a : α) (b : α), (iff (lt a b) (and (le a b) (not (le b a))))) (le_antisymm : forall (a : α) (b : α) (a_1 : has_le.le.{u} α (preorder.to_has_le.{u} α (preorder.mk.{u} α le lt le_refl le_trans lt_iff_le_not_le)) a b) (a_1 : has_le.le.{u} α (preorder.to_has_le.{u} α (preorder.mk.{u} α le lt le_refl le_trans lt_iff_le_not_le)) b a), (eq.{u+1} α a b)), (partial_order.{u} α)
axiom linear_order.mk.{u} : forall (α : Type.{u}) (le : α -> α -> Prop) (lt : α -> α -> Prop) (le_refl : forall (a : α), (le a a)) (le_trans : forall (a : α) (b : α) (c : α) (a_1 : le a b) (a_1 : le b c), (le a c)) (lt_iff_le_not_le : forall (a : α) (b : α), (iff (lt a b) (and (le a b) (not (le b a))))) (le_antisymm : forall (a : α) (b : α) (a_1 : has_le.le.{u} α (preorder.to_has_le.{u} α (preorder.mk.{u} α le lt le_refl le_trans lt_iff_le_not_le)) a b) (a_1 : has_le.le.{u} α (preorder.to_has_le.{u} α (preorder.mk.{u} α le lt le_refl le_trans lt_iff_le_not_le)) b a), (eq.{u+1} α a b)) (le_total : forall (a : α) (b : α), (or (has_le.le.{u} α (preorder.to_has_le.{u} α (partial_order.to_preorder.{u} α (partial_order.mk.{u} α le lt le_refl le_trans lt_iff_le_not_le le_antisymm))) a b) (has_le.le.{u} α (preorder.to_has_le.{u} α (partial_order.to_preorder.{u} α (partial_order.mk.{u} α le lt le_refl le_trans lt_iff_le_not_le le_antisymm))) b a))), (linear_order.{u} α)
axiom decidable_linear_order.le.{u} : forall (α : Type.{u}) (c : decidable_linear_order.{u} α) (a : α) (a : α), Prop
axiom decidable_linear_order.lt.{u} : forall (α : Type.{u}) (c : decidable_linear_order.{u} α) (a : α) (a : α), Prop
axiom decidable_linear_order.le_refl.{u} : forall (α : Type.{u}) (c : decidable_linear_order.{u} α) (a : α), (decidable_linear_order.le.{u} α c a a)
axiom decidable_linear_order.le_trans.{u} : forall (α : Type.{u}) (c : decidable_linear_order.{u} α) (a : α) (b : α) (c_1 : α) (a_1 : decidable_linear_order.le.{u} α c a b) (a_1 : decidable_linear_order.le.{u} α c b c_1), (decidable_linear_order.le.{u} α c a c_1)
axiom decidable_linear_order.lt_iff_le_not_le.{u} : forall (α : Type.{u}) (c : decidable_linear_order.{u} α) (a : α) (b : α), (iff (decidable_linear_order.lt.{u} α c a b) (and (decidable_linear_order.le.{u} α c a b) (not (decidable_linear_order.le.{u} α c b a))))
axiom decidable_linear_order.le_antisymm.{u} : forall (α : Type.{u}) (c : decidable_linear_order.{u} α) (a : α) (b : α) (a_1 : has_le.le.{u} α (preorder.to_has_le.{u} α (preorder.mk.{u} α (decidable_linear_order.le.{u} α c) (decidable_linear_order.lt.{u} α c) (decidable_linear_order.le_refl.{u} α c) (decidable_linear_order.le_trans.{u} α c) (decidable_linear_order.lt_iff_le_not_le.{u} α c))) a b) (a_1 : has_le.le.{u} α (preorder.to_has_le.{u} α (preorder.mk.{u} α (decidable_linear_order.le.{u} α c) (decidable_linear_order.lt.{u} α c) (decidable_linear_order.le_refl.{u} α c) (decidable_linear_order.le_trans.{u} α c) (decidable_linear_order.lt_iff_le_not_le.{u} α c))) b a), (eq.{u+1} α a b)
axiom decidable_linear_order.le_total.{u} : forall (α : Type.{u}) (c : decidable_linear_order.{u} α) (a : α) (b : α), (or (has_le.le.{u} α (preorder.to_has_le.{u} α (partial_order.to_preorder.{u} α (partial_order.mk.{u} α (decidable_linear_order.le.{u} α c) (decidable_linear_order.lt.{u} α c) (decidable_linear_order.le_refl.{u} α c) (decidable_linear_order.le_trans.{u} α c) (decidable_linear_order.lt_iff_le_not_le.{u} α c) (decidable_linear_order.le_antisymm.{u} α c)))) a b) (has_le.le.{u} α (preorder.to_has_le.{u} α (partial_order.to_preorder.{u} α (partial_order.mk.{u} α (decidable_linear_order.le.{u} α c) (decidable_linear_order.lt.{u} α c) (decidable_linear_order.le_refl.{u} α c) (decidable_linear_order.le_trans.{u} α c) (decidable_linear_order.lt_iff_le_not_le.{u} α c) (decidable_linear_order.le_antisymm.{u} α c)))) b a))
@[instance] axiom has_lt.lt.decidable.{u} (α : Type.{u}) [_inst_1 : decidable_linear_order.{u} α] (a : α) (b : α) : decidable (has_lt.lt.{u} α (preorder.to_has_lt.{u} α (partial_order.to_preorder.{u} α (linear_order.to_partial_order.{u} α (linear_order.mk.{u} α (decidable_linear_order.le.{u} α _inst_1) (decidable_linear_order.lt.{u} α _inst_1) (decidable_linear_order.le_refl.{u} α _inst_1) (decidable_linear_order.le_trans.{u} α _inst_1) (decidable_linear_order.lt_iff_le_not_le.{u} α _inst_1) (decidable_linear_order.le_antisymm.{u} α _inst_1) (decidable_linear_order.le_total.{u} α _inst_1))))) a b)
@[instance] axiom has_le.le.decidable.{u} (α : Type.{u}) [_inst_1 : decidable_linear_order.{u} α] (a : α) (b : α) : decidable (has_le.le.{u} α (preorder.to_has_le.{u} α (partial_order.to_preorder.{u} α (linear_order.to_partial_order.{u} α (linear_order.mk.{u} α (decidable_linear_order.le.{u} α _inst_1) (decidable_linear_order.lt.{u} α _inst_1) (decidable_linear_order.le_refl.{u} α _inst_1) (decidable_linear_order.le_trans.{u} α _inst_1) (decidable_linear_order.lt_iff_le_not_le.{u} α _inst_1) (decidable_linear_order.le_antisymm.{u} α _inst_1) (decidable_linear_order.le_total.{u} α _inst_1))))) a b)
@[instance] axiom eq.decidable.{u} (α : Type.{u}) [_inst_1 : decidable_linear_order.{u} α] (a : α) (b : α) : decidable (eq.{u+1} α a b)
@[instance] axiom has_le.le.is_total_preorder.{u} (α : Type.{u}) [_inst_1 : decidable_linear_order.{u} α] : is_total_preorder.{u} α (has_le.le.{u} α (preorder.to_has_le.{u} α (partial_order.to_preorder.{u} α (linear_order.to_partial_order.{u} α (decidable_linear_order.to_linear_order.{u} α _inst_1)))))
@[instance] axiom is_strict_weak_order_of_decidable_linear_order.{u} (α : Type.{u}) [_inst_1 : decidable_linear_order.{u} α] : is_strict_weak_order.{u} α (has_lt.lt.{u} α (preorder.to_has_lt.{u} α (partial_order.to_preorder.{u} α (linear_order.to_partial_order.{u} α (decidable_linear_order.to_linear_order.{u} α _inst_1)))))
@[instance] axiom is_strict_total_order_of_decidable_linear_order.{u} (α : Type.{u}) [_inst_1 : decidable_linear_order.{u} α] : is_strict_total_order.{u} α (has_lt.lt.{u} α (preorder.to_has_lt.{u} α (partial_order.to_preorder.{u} α (linear_order.to_partial_order.{u} α (decidable_linear_order.to_linear_order.{u} α _inst_1)))))
class semigroup.{u} (α : Type.{u})
@[instance] axiom semigroup.to_has_mul.{u} (α : Type.{u}) [s : semigroup.{u} α] : has_mul.{u} α
class comm_semigroup.{u} (α : Type.{u})
@[instance] axiom comm_semigroup.to_semigroup.{u} (α : Type.{u}) [s : comm_semigroup.{u} α] : semigroup.{u} α
class left_cancel_semigroup.{u} (α : Type.{u})
@[instance] axiom left_cancel_semigroup.to_semigroup.{u} (α : Type.{u}) [s : left_cancel_semigroup.{u} α] : semigroup.{u} α
class right_cancel_semigroup.{u} (α : Type.{u})
@[instance] axiom right_cancel_semigroup.to_semigroup.{u} (α : Type.{u}) [s : right_cancel_semigroup.{u} α] : semigroup.{u} α
class monoid.{u} (α : Type.{u})
@[instance] axiom monoid.to_semigroup.{u} (α : Type.{u}) [s : monoid.{u} α] : semigroup.{u} α
@[instance] axiom monoid.to_has_one.{u} (α : Type.{u}) [s : monoid.{u} α] : has_one.{u} α
class comm_monoid.{u} (α : Type.{u})
@[instance] axiom comm_monoid.to_monoid.{u} (α : Type.{u}) [s : comm_monoid.{u} α] : monoid.{u} α
@[instance] axiom comm_monoid.to_comm_semigroup.{u} (α : Type.{u}) [s : comm_monoid.{u} α] : comm_semigroup.{u} α
class group.{u} (α : Type.{u})
@[instance] axiom group.to_monoid.{u} (α : Type.{u}) [s : group.{u} α] : monoid.{u} α
@[instance] axiom group.to_has_inv.{u} (α : Type.{u}) [s : group.{u} α] : has_inv.{u} α
class comm_group.{u} (α : Type.{u})
@[instance] axiom comm_group.to_group.{u} (α : Type.{u}) [s : comm_group.{u} α] : group.{u} α
@[instance] axiom comm_group.to_comm_monoid.{u} (α : Type.{u}) [s : comm_group.{u} α] : comm_monoid.{u} α
axiom has_mul.mul.{u} : forall (α : Type.{u}) (c : has_mul.{u} α) (a : α) (a : α), α
@[instance] axiom semigroup_to_is_associative.{u} (α : Type.{u}) [_inst_1 : semigroup.{u} α] : is_associative.{u} α (has_mul.mul.{u} α (semigroup.to_has_mul.{u} α _inst_1))
@[instance] axiom comm_semigroup_to_is_commutative.{u} (α : Type.{u}) [_inst_1 : comm_semigroup.{u} α] : is_commutative.{u} α (has_mul.mul.{u} α (semigroup.to_has_mul.{u} α (comm_semigroup.to_semigroup.{u} α _inst_1)))
@[instance] axiom group.to_left_cancel_semigroup.{u} (α : Type.{u}) [s : group.{u} α] : left_cancel_semigroup.{u} α
@[instance] axiom group.to_right_cancel_semigroup.{u} (α : Type.{u}) [s : group.{u} α] : right_cancel_semigroup.{u} α
class add_semigroup.{u} (α : Type.{u})
@[instance] axiom add_semigroup.to_has_add.{u} (α : Type.{u}) [s : add_semigroup.{u} α] : has_add.{u} α
class add_comm_semigroup.{u} (α : Type.{u})
@[instance] axiom add_comm_semigroup.to_add_semigroup.{u} (α : Type.{u}) [s : add_comm_semigroup.{u} α] : add_semigroup.{u} α
class add_left_cancel_semigroup.{u} (α : Type.{u})
@[instance] axiom add_left_cancel_semigroup.to_add_semigroup.{u} (α : Type.{u}) [s : add_left_cancel_semigroup.{u} α] : add_semigroup.{u} α
class add_right_cancel_semigroup.{u} (α : Type.{u})
@[instance] axiom add_right_cancel_semigroup.to_add_semigroup.{u} (α : Type.{u}) [s : add_right_cancel_semigroup.{u} α] : add_semigroup.{u} α
class add_monoid.{u} (α : Type.{u})
@[instance] axiom add_monoid.to_add_semigroup.{u} (α : Type.{u}) [s : add_monoid.{u} α] : add_semigroup.{u} α
@[instance] axiom add_monoid.to_has_zero.{u} (α : Type.{u}) [s : add_monoid.{u} α] : has_zero.{u} α
class add_comm_monoid.{u} (α : Type.{u})
@[instance] axiom add_comm_monoid.to_add_monoid.{u} (α : Type.{u}) [s : add_comm_monoid.{u} α] : add_monoid.{u} α
@[instance] axiom add_comm_monoid.to_add_comm_semigroup.{u} (α : Type.{u}) [s : add_comm_monoid.{u} α] : add_comm_semigroup.{u} α
class add_group.{u} (α : Type.{u})
@[instance] axiom add_group.to_add_monoid.{u} (α : Type.{u}) [s : add_group.{u} α] : add_monoid.{u} α
@[instance] axiom add_group.to_has_neg.{u} (α : Type.{u}) [s : add_group.{u} α] : has_neg.{u} α
class add_comm_group.{u} (α : Type.{u})
@[instance] axiom add_comm_group.to_add_group.{u} (α : Type.{u}) [s : add_comm_group.{u} α] : add_group.{u} α
@[instance] axiom add_comm_group.to_add_comm_monoid.{u} (α : Type.{u}) [s : add_comm_group.{u} α] : add_comm_monoid.{u} α
#synth has_lt.{0} name
#synth forall (a : name) (b : name), (decidable (has_lt.lt.{0} name name.has_lt a b))
@[instance] axiom add_group.to_left_cancel_add_semigroup.{u} (α : Type.{u}) [s : add_group.{u} α] : add_left_cancel_semigroup.{u} α
@[instance] axiom add_group.to_right_cancel_add_semigroup.{u} (α : Type.{u}) [s : add_group.{u} α] : add_right_cancel_semigroup.{u} α
axiom has_add.add.{u} : forall (α : Type.{u}) (c : has_add.{u} α) (a : α) (a : α), α
@[instance] axiom add_semigroup_to_is_eq_associative.{u} (α : Type.{u}) [_inst_1 : add_semigroup.{u} α] : is_associative.{u} α (has_add.add.{u} α (add_semigroup.to_has_add.{u} α _inst_1))
@[instance] axiom add_comm_semigroup_to_is_eq_commutative.{u} (α : Type.{u}) [_inst_1 : add_comm_semigroup.{u} α] : is_commutative.{u} α (has_add.add.{u} α (add_semigroup.to_has_add.{u} α (add_comm_semigroup.to_add_semigroup.{u} α _inst_1)))
@[instance] axiom add_group_has_sub.{u} (α : Type.{u}) [_inst_1 : add_group.{u} α] : has_sub.{u} α
class ordered_cancel_comm_monoid.{u} (α : Type.{u})
@[instance] axiom ordered_cancel_comm_monoid.to_add_comm_monoid.{u} (α : Type.{u}) [s : ordered_cancel_comm_monoid.{u} α] : add_comm_monoid.{u} α
@[instance] axiom ordered_cancel_comm_monoid.to_add_left_cancel_semigroup.{u} (α : Type.{u}) [s : ordered_cancel_comm_monoid.{u} α] : add_left_cancel_semigroup.{u} α
@[instance] axiom ordered_cancel_comm_monoid.to_add_right_cancel_semigroup.{u} (α : Type.{u}) [s : ordered_cancel_comm_monoid.{u} α] : add_right_cancel_semigroup.{u} α
@[instance] axiom ordered_cancel_comm_monoid.to_partial_order.{u} (α : Type.{u}) [s : ordered_cancel_comm_monoid.{u} α] : partial_order.{u} α
class ordered_comm_group.{u} (α : Type.{u})
@[instance] axiom ordered_comm_group.to_add_comm_group.{u} (α : Type.{u}) [s : ordered_comm_group.{u} α] : add_comm_group.{u} α
@[instance] axiom ordered_comm_group.to_partial_order.{u} (α : Type.{u}) [s : ordered_comm_group.{u} α] : partial_order.{u} α
@[instance] axiom ordered_comm_group.to_ordered_cancel_comm_monoid.{u} (α : Type.{u}) [s : ordered_comm_group.{u} α] : ordered_cancel_comm_monoid.{u} α
class decidable_linear_ordered_comm_group.{u} (α : Type.{u})
@[instance] axiom decidable_linear_ordered_comm_group.to_add_comm_group.{u} (α : Type.{u}) [s : decidable_linear_ordered_comm_group.{u} α] : add_comm_group.{u} α
@[instance] axiom decidable_linear_ordered_comm_group.to_decidable_linear_order.{u} (α : Type.{u}) [s : decidable_linear_ordered_comm_group.{u} α] : decidable_linear_order.{u} α
@[instance] axiom decidable_linear_ordered_comm_group.to_ordered_comm_group.{u} (α : Type.{u}) [s : decidable_linear_ordered_comm_group.{u} α] : ordered_comm_group.{u} α
class decidable_linear_ordered_cancel_comm_monoid.{u} (α : Type.{u})
@[instance] axiom decidable_linear_ordered_cancel_comm_monoid.to_ordered_cancel_comm_monoid.{u} (α : Type.{u}) [s : decidable_linear_ordered_cancel_comm_monoid.{u} α] : ordered_cancel_comm_monoid.{u} α
@[instance] axiom decidable_linear_ordered_cancel_comm_monoid.to_decidable_linear_order.{u} (α : Type.{u}) [s : decidable_linear_ordered_cancel_comm_monoid.{u} α] : decidable_linear_order.{u} α
class distrib.{u} (α : Type.{u})
@[instance] axiom distrib.to_has_mul.{u} (α : Type.{u}) [s : distrib.{u} α] : has_mul.{u} α
@[instance] axiom distrib.to_has_add.{u} (α : Type.{u}) [s : distrib.{u} α] : has_add.{u} α
class mul_zero_class.{u} (α : Type.{u})
@[instance] axiom mul_zero_class.to_has_mul.{u} (α : Type.{u}) [s : mul_zero_class.{u} α] : has_mul.{u} α
@[instance] axiom mul_zero_class.to_has_zero.{u} (α : Type.{u}) [s : mul_zero_class.{u} α] : has_zero.{u} α
class zero_ne_one_class.{u} (α : Type.{u})
@[instance] axiom zero_ne_one_class.to_has_zero.{u} (α : Type.{u}) [s : zero_ne_one_class.{u} α] : has_zero.{u} α
@[instance] axiom zero_ne_one_class.to_has_one.{u} (α : Type.{u}) [s : zero_ne_one_class.{u} α] : has_one.{u} α
class semiring.{u} (α : Type.{u})
@[instance] axiom semiring.to_add_comm_monoid.{u} (α : Type.{u}) [s : semiring.{u} α] : add_comm_monoid.{u} α
@[instance] axiom semiring.to_monoid.{u} (α : Type.{u}) [s : semiring.{u} α] : monoid.{u} α
@[instance] axiom semiring.to_distrib.{u} (α : Type.{u}) [s : semiring.{u} α] : distrib.{u} α
@[instance] axiom semiring.to_mul_zero_class.{u} (α : Type.{u}) [s : semiring.{u} α] : mul_zero_class.{u} α
class comm_semiring.{u} (α : Type.{u})
@[instance] axiom comm_semiring.to_semiring.{u} (α : Type.{u}) [s : comm_semiring.{u} α] : semiring.{u} α
@[instance] axiom comm_semiring.to_comm_monoid.{u} (α : Type.{u}) [s : comm_semiring.{u} α] : comm_monoid.{u} α
@[instance] axiom comm_semiring_has_dvd.{u} (α : Type.{u}) [_inst_1 : comm_semiring.{u} α] : has_dvd.{u} α
class ring.{u} (α : Type.{u})
@[instance] axiom ring.to_add_comm_group.{u} (α : Type.{u}) [s : ring.{u} α] : add_comm_group.{u} α
@[instance] axiom ring.to_monoid.{u} (α : Type.{u}) [s : ring.{u} α] : monoid.{u} α
@[instance] axiom ring.to_distrib.{u} (α : Type.{u}) [s : ring.{u} α] : distrib.{u} α
@[instance] axiom ring.to_semiring.{u} (α : Type.{u}) [s : ring.{u} α] : semiring.{u} α
class comm_ring.{u} (α : Type.{u})
@[instance] axiom comm_ring.to_ring.{u} (α : Type.{u}) [s : comm_ring.{u} α] : ring.{u} α
@[instance] axiom comm_ring.to_comm_semigroup.{u} (α : Type.{u}) [s : comm_ring.{u} α] : comm_semigroup.{u} α
@[instance] axiom comm_ring.to_comm_semiring.{u} (α : Type.{u}) [s : comm_ring.{u} α] : comm_semiring.{u} α
class no_zero_divisors.{u} (α : Type.{u})
@[instance] axiom no_zero_divisors.to_has_mul.{u} (α : Type.{u}) [s : no_zero_divisors.{u} α] : has_mul.{u} α
@[instance] axiom no_zero_divisors.to_has_zero.{u} (α : Type.{u}) [s : no_zero_divisors.{u} α] : has_zero.{u} α
class integral_domain.{u} (α : Type.{u})
@[instance] axiom integral_domain.to_comm_ring.{u} (α : Type.{u}) [s : integral_domain.{u} α] : comm_ring.{u} α
@[instance] axiom integral_domain.to_no_zero_divisors.{u} (α : Type.{u}) [s : integral_domain.{u} α] : no_zero_divisors.{u} α
@[instance] axiom integral_domain.to_zero_ne_one_class.{u} (α : Type.{u}) [s : integral_domain.{u} α] : zero_ne_one_class.{u} α
class ordered_semiring.{u} (α : Type.{u})
@[instance] axiom ordered_semiring.to_semiring.{u} (α : Type.{u}) [s : ordered_semiring.{u} α] : semiring.{u} α
@[instance] axiom ordered_semiring.to_ordered_cancel_comm_monoid.{u} (α : Type.{u}) [s : ordered_semiring.{u} α] : ordered_cancel_comm_monoid.{u} α
class linear_ordered_semiring.{u} (α : Type.{u})
@[instance] axiom linear_ordered_semiring.to_ordered_semiring.{u} (α : Type.{u}) [s : linear_ordered_semiring.{u} α] : ordered_semiring.{u} α
@[instance] axiom linear_ordered_semiring.to_linear_order.{u} (α : Type.{u}) [s : linear_ordered_semiring.{u} α] : linear_order.{u} α
class decidable_linear_ordered_semiring.{u} (α : Type.{u})
@[instance] axiom decidable_linear_ordered_semiring.to_linear_ordered_semiring.{u} (α : Type.{u}) [s : decidable_linear_ordered_semiring.{u} α] : linear_ordered_semiring.{u} α
@[instance] axiom decidable_linear_ordered_semiring.to_decidable_linear_order.{u} (α : Type.{u}) [s : decidable_linear_ordered_semiring.{u} α] : decidable_linear_order.{u} α
class ordered_ring.{u} (α : Type.{u})
@[instance] axiom ordered_ring.to_ring.{u} (α : Type.{u}) [s : ordered_ring.{u} α] : ring.{u} α
@[instance] axiom ordered_ring.to_ordered_comm_group.{u} (α : Type.{u}) [s : ordered_ring.{u} α] : ordered_comm_group.{u} α
@[instance] axiom ordered_ring.to_zero_ne_one_class.{u} (α : Type.{u}) [s : ordered_ring.{u} α] : zero_ne_one_class.{u} α
@[instance] axiom ordered_ring.to_ordered_semiring.{u} (α : Type.{u}) [s : ordered_ring.{u} α] : ordered_semiring.{u} α
class linear_ordered_ring.{u} (α : Type.{u})
@[instance] axiom linear_ordered_ring.to_ordered_ring.{u} (α : Type.{u}) [s : linear_ordered_ring.{u} α] : ordered_ring.{u} α
@[instance] axiom linear_ordered_ring.to_linear_order.{u} (α : Type.{u}) [s : linear_ordered_ring.{u} α] : linear_order.{u} α
@[instance] axiom linear_ordered_ring.to_linear_ordered_semiring.{u} (α : Type.{u}) [s : linear_ordered_ring.{u} α] : linear_ordered_semiring.{u} α
class linear_ordered_comm_ring.{u} (α : Type.{u})
@[instance] axiom linear_ordered_comm_ring.to_linear_ordered_ring.{u} (α : Type.{u}) [s : linear_ordered_comm_ring.{u} α] : linear_ordered_ring.{u} α
@[instance] axiom linear_ordered_comm_ring.to_comm_monoid.{u} (α : Type.{u}) [s : linear_ordered_comm_ring.{u} α] : comm_monoid.{u} α
@[instance] axiom linear_ordered_comm_ring.to_integral_domain.{u} (α : Type.{u}) [s : linear_ordered_comm_ring.{u} α] : integral_domain.{u} α
class decidable_linear_ordered_comm_ring.{u} (α : Type.{u})
@[instance] axiom decidable_linear_ordered_comm_ring.to_linear_ordered_comm_ring.{u} (α : Type.{u}) [s : decidable_linear_ordered_comm_ring.{u} α] : linear_ordered_comm_ring.{u} α
@[instance] axiom decidable_linear_ordered_comm_ring.to_decidable_linear_ordered_comm_group.{u} (α : Type.{u}) [s : decidable_linear_ordered_comm_ring.{u} α] : decidable_linear_ordered_comm_group.{u} α
@[instance] axiom decidable_linear_ordered_comm_ring.to_decidable_linear_ordered_semiring.{u} (α : Type.{u}) [d : decidable_linear_ordered_comm_ring.{u} α] : decidable_linear_ordered_semiring.{u} α
class division_ring.{u} (α : Type.{u})
@[instance] axiom division_ring.to_ring.{u} (α : Type.{u}) [s : division_ring.{u} α] : ring.{u} α
@[instance] axiom division_ring.to_has_inv.{u} (α : Type.{u}) [s : division_ring.{u} α] : has_inv.{u} α
@[instance] axiom division_ring.to_zero_ne_one_class.{u} (α : Type.{u}) [s : division_ring.{u} α] : zero_ne_one_class.{u} α
@[instance] axiom division_ring_has_div.{u} (α : Type.{u}) [_inst_1 : division_ring.{u} α] [_inst_2 : division_ring.{u} α] : has_div.{u} α
class field.{u} (α : Type.{u})
@[instance] axiom field.to_division_ring.{u} (α : Type.{u}) [s : field.{u} α] : division_ring.{u} α
@[instance] axiom field.to_comm_ring.{u} (α : Type.{u}) [s : field.{u} α] : comm_ring.{u} α
class discrete_field.{u} (α : Type.{u})
@[instance] axiom discrete_field.to_field.{u} (α : Type.{u}) [s : discrete_field.{u} α] : field.{u} α
@[instance] axiom discrete_field.has_decidable_eq.{u} (α : Type.{u}) [c : discrete_field.{u} α] (a : α) (b : α) : decidable (eq.{u+1} α a b)
@[instance] axiom discrete_field.to_integral_domain.{u} (α : Type.{u}) [_inst_1 : discrete_field.{u} α] [s : discrete_field.{u} α] : integral_domain.{u} α
class linear_ordered_field.{u} (α : Type.{u})
@[instance] axiom linear_ordered_field.to_linear_ordered_ring.{u} (α : Type.{u}) [s : linear_ordered_field.{u} α] : linear_ordered_ring.{u} α
@[instance] axiom linear_ordered_field.to_field.{u} (α : Type.{u}) [s : linear_ordered_field.{u} α] : field.{u} α
class discrete_linear_ordered_field.{u} (α : Type.{u})
@[instance] axiom discrete_linear_ordered_field.to_linear_ordered_field.{u} (α : Type.{u}) [s : discrete_linear_ordered_field.{u} α] : linear_ordered_field.{u} α
@[instance] axiom discrete_linear_ordered_field.to_decidable_linear_ordered_comm_ring.{u} (α : Type.{u}) [s : discrete_linear_ordered_field.{u} α] : decidable_linear_ordered_comm_ring.{u} α
@[instance] axiom discrete_linear_ordered_field.to_discrete_field.{u} (α : Type.{u}) [s : discrete_linear_ordered_field.{u} α] : discrete_field.{u} α
@[instance] axiom nat.zero_ne_one_class  : zero_ne_one_class.{0} nat
@[instance] axiom nat.comm_semiring  : comm_semiring.{0} nat
@[instance] axiom nat.linear_order  : linear_order.{0} nat
#synth partial_order.{0} nat
#synth add_comm_semigroup.{0} nat
#synth distrib.{0} nat
#synth comm_semigroup.{0} nat
#synth preorder.{0} nat
@[instance] axiom nat.decidable_linear_ordered_semiring  : decidable_linear_ordered_semiring.{0} nat
@[instance] axiom nat.decidable_linear_ordered_cancel_comm_monoid  : decidable_linear_ordered_cancel_comm_monoid.{0} nat
#synth linear_ordered_semiring.{0} nat
#synth add_monoid.{0} nat
#synth ordered_cancel_comm_monoid.{0} nat
#synth add_comm_monoid.{0} nat
@[instance] axiom nat.add_comm_monoid  : add_comm_monoid.{0} nat
@[instance] axiom nat.add_monoid  : add_monoid.{0} nat
#synth monoid.{0} nat
@[instance] axiom nat.monoid  : monoid.{0} nat
#synth comm_monoid.{0} nat
@[instance] axiom nat.comm_monoid  : comm_monoid.{0} nat
@[instance] axiom nat.comm_semigroup  : comm_semigroup.{0} nat
#synth semigroup.{0} nat
@[instance] axiom nat.semigroup  : semigroup.{0} nat
@[instance] axiom nat.add_comm_semigroup  : add_comm_semigroup.{0} nat
#synth add_semigroup.{0} nat
@[instance] axiom nat.add_semigroup  : add_semigroup.{0} nat
@[instance] axiom nat.distrib  : distrib.{0} nat
#synth semiring.{0} nat
@[instance] axiom nat.semiring  : semiring.{0} nat
#synth ordered_semiring.{0} nat
@[instance] axiom nat.ordered_semiring  : ordered_semiring.{0} nat
#synth linear_order.{0} nat
#synth decidable_linear_order.{0} nat
axiom bit0.{u} : forall (α : Type.{u}) (s : has_add.{u} α) (a : α), α
#synth decidable (has_lt.lt.{0} nat nat.has_lt (has_zero.zero.{0} nat nat.has_zero) (bit0.{0} nat nat.has_add (has_one.one.{0} nat nat.has_one)))
#synth mul_zero_class.{0} nat
#synth zero_ne_one_class.{0} nat
#synth has_andthen.{0, 0, 0} (tactic_state -> (interaction_monad.result.{0} tactic_state punit.{1})) (list.{0} (tactic_state -> (interaction_monad.result.{0} tactic_state punit.{1}))) (tactic_state -> (interaction_monad.result.{0} tactic_state punit.{1}))
#synth has_dvd.{0} nat
#synth comm_semiring.{0} nat
#synth decidable (has_lt.lt.{0} nat nat.has_lt (has_zero.zero.{0} nat nat.has_zero) (has_one.one.{0} nat nat.has_one))
axiom has_dvd.dvd.{u} : forall (α : Type.{u}) (c : has_dvd.{u} α) (a : α) (a : α), Prop
@[instance] axiom nat.decidable_dvd (a : nat) (b : nat) : decidable (has_dvd.dvd.{0} nat (comm_semiring_has_dvd.{0} nat nat.comm_semiring) a b)
@[instance] axiom list.has_subset.{u} (α : Type.{u}) : has_subset.{u} (list.{u} α)
@[instance] axiom list.monad.{u_1}  : monad.{u_1, u_1} list.{u_1}
#synth monad.{u_1, u_1} list.{u_1}
#synth applicative.{u_1, u_1} list.{u_1}
@[instance] axiom list.is_lawful_monad.{u_1}  : is_lawful_monad.{u_1, u_1} list.{u_1} list.monad.{u_1}
@[instance] axiom list.alternative.{u_1}  : alternative.{u_1, u_1} list.{u_1}
axiom bin_tree.{u} : Type.{u} -> Type.{u}
@[instance] axiom list.bin_tree_to_list.{u} (α : Type.{u}) : has_coe.{u+1, u+1} (bin_tree.{u} α) (list.{u} α)
@[instance] axiom list.decidable_bex.{u} (α : Type.{u}) (p : α -> Prop) [_inst_1 : forall (a : α), (decidable (p a))] (l : list.{u} α) : decidable (Exists.{u+1} α (fun (x : α), (Exists.{0} (has_mem.mem.{u, u} α (list.{u} α) (list.has_mem.{u} α) x l) (fun (H : has_mem.mem.{u, u} α (list.{u} α) (list.has_mem.{u} α) x l), (p x)))))
@[instance] axiom list.decidable_ball.{u} (α : Type.{u}) (p : α -> Prop) [_inst_1 : forall (a : α), (decidable (p a))] (l : list.{u} α) : decidable (forall (x : α) (H : has_mem.mem.{u, u} α (list.{u} α) (list.has_mem.{u} α) x l), (p x))
#synth forall (a : list.{0} char) (b : list.{0} char), (decidable (eq.{1} (list.{0} char) a b))
@[instance] axiom string.has_decidable_eq (a : string) (b : string) : decidable (eq.{1} string a b)
axiom nat.add_assoc : forall (n : nat) (m : nat) (k : nat), (eq.{1} nat (has_add.add.{0} nat nat.has_add (has_add.add.{0} nat nat.has_add n m) k) (has_add.add.{0} nat nat.has_add n (has_add.add.{0} nat nat.has_add m k)))
#synth has_coe_t.{1, 1} (reflected.{0} (forall (n : nat) (m : nat) (k : nat), (eq.{1} nat (has_add.add.{0} nat nat.has_add (has_add.add.{0} nat nat.has_add n m) k) (has_add.add.{0} nat nat.has_add n (has_add.add.{0} nat nat.has_add m k)))) nat.add_assoc) (expr bool.tt)
axiom nat.add_comm : forall (n : nat) (m : nat), (eq.{1} nat (has_add.add.{0} nat nat.has_add n m) (has_add.add.{0} nat nat.has_add m n))
#synth has_coe_t.{1, 1} (reflected.{0} (forall (n : nat) (m : nat), (eq.{1} nat (has_add.add.{0} nat nat.has_add n m) (has_add.add.{0} nat nat.has_add m n))) nat.add_comm) (expr bool.tt)
#synth has_coe_t.{1, 1} (reflected.{2} Type nat) (expr bool.tt)
#synth forall (a : expr bool.tt) (b : expr bool.tt), (decidable (eq.{1} (expr bool.tt) a b))
#synth has_well_founded.{1} nat
axiom cond.{u} : forall (a : Type.{u}) (a_1 : bool) (a_1 : a) (a_1 : a), a
#synth decidable (has_lt.lt.{0} nat nat.has_lt (cond.{0} nat bool.ff (has_one.one.{0} nat nat.has_one) (has_zero.zero.{0} nat nat.has_zero)) (bit0.{0} nat nat.has_add (has_one.one.{0} nat nat.has_one)))
#synth decidable (has_lt.lt.{0} nat nat.has_lt (cond.{0} nat bool.tt (has_one.one.{0} nat nat.has_one) (has_zero.zero.{0} nat nat.has_zero)) (bit0.{0} nat nat.has_add (has_one.one.{0} nat nat.has_one)))
#synth has_well_founded.{1} (psigma.{1, 1} nat (fun (a : nat), nat))
#synth forall (a : nat) (b : nat), (decidable (eq.{1} nat a b))
axiom int : Type
@[instance] axiom int.decidable_eq (a : int) (b : int) : decidable (eq.{1} int a b)
@[instance] axiom int.has_coe  : has_coe.{1, 1} nat int
@[instance] axiom int.has_repr  : has_repr.{0} int
@[instance] axiom int.has_to_string  : has_to_string.{0} int
#synth has_lift_t.{1, 1} nat int
@[instance] axiom int.has_zero  : has_zero.{0} int
@[instance] axiom int.has_one  : has_one.{0} int
#synth has_zero.{0} int
#synth has_one.{0} int
#synth has_coe_t.{1, 1} nat int
@[instance] axiom int.has_neg  : has_neg.{0} int
@[instance] axiom int.has_add  : has_add.{0} int
@[instance] axiom int.has_mul  : has_mul.{0} int
#synth has_add.{0} int
#synth has_mul.{0} int
#synth has_neg.{0} int
@[instance] axiom int.has_div  : has_div.{0} int
@[instance] axiom int.has_mod  : has_mod.{0} int
@[instance] axiom int.comm_ring  : comm_ring.{0} int
#synth has_sub.{0} int
@[instance] axiom int.has_sub  : has_sub.{0} int
#synth add_comm_monoid.{0} int
@[instance] axiom int.add_comm_monoid  : add_comm_monoid.{0} int
#synth add_monoid.{0} int
@[instance] axiom int.add_monoid  : add_monoid.{0} int
#synth monoid.{0} int
@[instance] axiom int.monoid  : monoid.{0} int
#synth comm_monoid.{0} int
@[instance] axiom int.comm_monoid  : comm_monoid.{0} int
#synth comm_semigroup.{0} int
@[instance] axiom int.comm_semigroup  : comm_semigroup.{0} int
#synth semigroup.{0} int
@[instance] axiom int.semigroup  : semigroup.{0} int
#synth add_comm_semigroup.{0} int
@[instance] axiom int.add_comm_semigroup  : add_comm_semigroup.{0} int
#synth add_semigroup.{0} int
@[instance] axiom int.add_semigroup  : add_semigroup.{0} int
#synth comm_semiring.{0} int
@[instance] axiom int.comm_semiring  : comm_semiring.{0} int
#synth semiring.{0} int
@[instance] axiom int.semiring  : semiring.{0} int
#synth ring.{0} int
@[instance] axiom int.ring  : ring.{0} int
#synth distrib.{0} int
@[instance] axiom int.distrib  : distrib.{0} int
@[instance] axiom int.zero_ne_one_class  : zero_ne_one_class.{0} int
#synth add_group.{0} int
#synth add_comm_group.{0} int
#synth has_mod.{0} int
@[instance] axiom int.has_le  : has_le.{0} int
#synth has_le.{0} int
@[instance] axiom int.has_lt  : has_lt.{0} int
@[instance] axiom int.decidable_le (a : int) (b : int) : decidable (has_le.le.{0} int int.has_le a b)
#synth has_lt.{0} int
@[instance] axiom int.decidable_lt (a : int) (b : int) : decidable (has_lt.lt.{0} int int.has_lt a b)
#synth add_left_cancel_semigroup.{0} int
@[instance] axiom int.decidable_linear_ordered_comm_ring  : decidable_linear_ordered_comm_ring.{0} int
#synth decidable_linear_ordered_comm_group.{0} int
@[instance] axiom int.decidable_linear_ordered_comm_group  : decidable_linear_ordered_comm_group.{0} int
#synth linear_order.{0} int
#synth preorder.{0} int
#synth ordered_comm_group.{0} int
#synth ordered_cancel_comm_monoid.{0} int
#synth integral_domain.{0} int
#synth linear_ordered_semiring.{0} int
#synth has_mem.{0, 0} char (list.{0} char)
axiom char.is_whitespace : char -> Prop
@[instance] axiom char.decidable_is_whitespace (a : char) : decidable (char.is_whitespace a)
axiom char.is_upper : char -> Prop
@[instance] axiom char.decidable_is_upper (a : char) : decidable (char.is_upper a)
axiom char.is_lower : char -> Prop
@[instance] axiom char.decidable_is_lower (a : char) : decidable (char.is_lower a)
axiom char.is_alpha : char -> Prop
@[instance] axiom char.decidable_is_alpha (a : char) : decidable (char.is_alpha a)
axiom char.is_digit : char -> Prop
@[instance] axiom char.decidable_is_digit (a : char) : decidable (char.is_digit a)
axiom char.is_alphanum : char -> Prop
@[instance] axiom char.decidable_is_alphanum (a : char) : decidable (char.is_alphanum a)
axiom char.is_punctuation : char -> Prop
@[instance] axiom char.decidable_is_punctuation (a : char) : decidable (char.is_punctuation a)
#synth decidable (iff (not (eq.{1} bool bool.ff bool.tt)) (eq.{1} bool bool.ff bool.ff))
#synth decidable (iff (not (eq.{1} bool bool.tt bool.tt)) (eq.{1} bool bool.tt bool.ff))
axiom bor : bool -> bool -> bool
#synth decidable (iff (eq.{1} bool (bor bool.ff bool.ff) bool.tt) (or (eq.{1} bool bool.ff bool.tt) (eq.{1} bool bool.ff bool.tt)))
#synth decidable (iff (eq.{1} bool (bor bool.ff bool.tt) bool.tt) (or (eq.{1} bool bool.ff bool.tt) (eq.{1} bool bool.tt bool.tt)))
#synth decidable (iff (eq.{1} bool (bor bool.tt bool.ff) bool.tt) (or (eq.{1} bool bool.tt bool.tt) (eq.{1} bool bool.ff bool.tt)))
#synth decidable (iff (eq.{1} bool (bor bool.tt bool.tt) bool.tt) (or (eq.{1} bool bool.tt bool.tt) (eq.{1} bool bool.tt bool.tt)))
axiom band : bool -> bool -> bool
#synth decidable (iff (eq.{1} bool (band bool.ff bool.ff) bool.tt) (and (eq.{1} bool bool.ff bool.tt) (eq.{1} bool bool.ff bool.tt)))
#synth decidable (iff (eq.{1} bool (band bool.ff bool.tt) bool.tt) (and (eq.{1} bool bool.ff bool.tt) (eq.{1} bool bool.tt bool.tt)))
#synth decidable (iff (eq.{1} bool (band bool.tt bool.ff) bool.tt) (and (eq.{1} bool bool.tt bool.tt) (eq.{1} bool bool.ff bool.tt)))
#synth decidable (iff (eq.{1} bool (band bool.tt bool.tt) bool.tt) (and (eq.{1} bool bool.tt bool.tt) (eq.{1} bool bool.tt bool.tt)))
axiom bxor : bool -> bool -> bool
#synth decidable (iff (eq.{1} bool (bxor bool.ff bool.ff) bool.tt) (xor (eq.{1} bool bool.ff bool.tt) (eq.{1} bool bool.ff bool.tt)))
#synth decidable (iff (eq.{1} bool (bxor bool.ff bool.tt) bool.tt) (xor (eq.{1} bool bool.ff bool.tt) (eq.{1} bool bool.tt bool.tt)))
#synth decidable (iff (eq.{1} bool (bxor bool.tt bool.ff) bool.tt) (xor (eq.{1} bool bool.tt bool.tt) (eq.{1} bool bool.ff bool.tt)))
#synth decidable (iff (eq.{1} bool (bxor bool.tt bool.tt) bool.tt) (xor (eq.{1} bool bool.tt bool.tt) (eq.{1} bool bool.tt bool.tt)))
@[instance] axiom subtype.decidable_eq.{u} (α : Type.{u}) (p : α -> Prop) [_inst_1 : forall (a : α) (b : α), (decidable (eq.{u+1} α a b))] (a : subtype.{u+1} α p) (b : subtype.{u+1} α p) : decidable (eq.{(max 1 (u+1))} (subtype.{u+1} α p) a b)
axiom d_array.{u} : forall (n : nat) (α : (fin n) -> Type.{u}), Type.{u}
@[instance] axiom d_array.decidable_eq.{u} (n : nat) (α : (fin n) -> Type.{u}) [_inst_1 : forall (i : fin n) (a : α i) (b : α i), (decidable (eq.{u+1} (α i) a b))] (a : d_array.{u} n α) (b : d_array.{u} n α) : decidable (eq.{u+1} (d_array.{u} n α) a b)
axiom array.{u} : nat -> Type.{u} -> Type.{u}
@[instance] axiom array.has_mem.{u} (n : nat) (α : Type.{u}) : has_mem.{u, u} α (array.{u} n α)
@[instance] axiom array.has_repr.{u} (n : nat) (α : Type.{u}) [_inst_1 : has_repr.{u} α] : has_repr.{u} (array.{u} n α)
@[instance] axiom array.has_to_format.{u} (n : nat) (α : Type.{u}) [_inst_1 : has_to_format.{u} α] : has_to_format.{u} (array.{u} n α)
@[instance] axiom array.has_to_tactic_format.{u} (n : nat) (α : Type.{u}) [_inst_1 : has_to_tactic_format.{u} α] : has_to_tactic_format.{u} (array.{u} n α)
@[instance] axiom array.decidable_eq.{u} (n : nat) (α : Type.{u}) [_inst_1 : forall (a : α) (b : α), (decidable (eq.{u+1} α a b))] (a : array.{u} n α) (b : array.{u} n α) : decidable (eq.{u+1} (array.{u} n α) a b)
axiom nat.succ : nat -> nat
@[instance] axiom fin.has_zero (n : nat) : has_zero.{0} (fin (nat.succ n))
@[instance] axiom fin.has_one (n : nat) : has_one.{0} (fin (nat.succ n))
@[instance] axiom fin.has_add (n : nat) : has_add.{0} (fin n)
@[instance] axiom fin.has_sub (n : nat) : has_sub.{0} (fin n)
@[instance] axiom fin.has_mul (n : nat) : has_mul.{0} (fin n)
@[instance] axiom fin.has_mod (n : nat) : has_mod.{0} (fin n)
@[instance] axiom fin.has_div (n : nat) : has_div.{0} (fin n)
@[instance] axiom unsigned.has_zero  : has_zero.{0} unsigned
@[instance] axiom unsigned.has_one  : has_one.{0} unsigned
@[instance] axiom unsigned.has_add  : has_add.{0} unsigned
@[instance] axiom unsigned.has_sub  : has_sub.{0} unsigned
@[instance] axiom unsigned.has_mul  : has_mul.{0} unsigned
@[instance] axiom unsigned.has_mod  : has_mod.{0} unsigned
@[instance] axiom unsigned.has_div  : has_div.{0} unsigned
@[instance] axiom unsigned.has_lt  : has_lt.{0} unsigned
@[instance] axiom unsigned.has_le  : has_le.{0} unsigned
axiom rbnode.color : Type
@[instance] axiom rbnode.color.decidable_eq (a : rbnode.color) (b : rbnode.color) : decidable (eq.{1} rbnode.color a b)
axiom rbtree.{u} : forall (α : Type.{u}) (lt : α -> α -> Prop), Type.{u}
@[instance] axiom rbtree.has_mem.{u} (α : Type.{u}) (lt : α -> α -> Prop) : has_mem.{u, u} α (rbtree.{u} α lt)
@[instance] axiom rbtree.has_repr.{u} (α : Type.{u}) (lt : α -> α -> Prop) [_inst_1 : has_repr.{u} α] : has_repr.{u} (rbtree.{u} α lt)
axiom rbmap.{u, v} : forall (α : Type.{u}) (β : Type.{v}) (lt : α -> α -> Prop), Type.{max u v}
@[instance] axiom rbmap.has_mem.{u, v} (α : Type.{u}) (β : Type.{v}) (lt : α -> α -> Prop) : has_mem.{u, (max, u, v)} α (rbmap.{u, v} α β lt)
@[instance] axiom rbmap.has_repr.{u, v} (α : Type.{u}) (β : Type.{v}) (lt : α -> α -> Prop) [_inst_1 : has_repr.{u} α] [_inst_2 : has_repr.{v} β] : has_repr.{(max u v)} (rbmap.{u, v} α β lt)
#synth monad.{u_1, u_1} option.{u_1}
#synth applicative.{u_1, u_1} option.{u_1}
@[instance] axiom option.is_lawful_monad.{u_1}  : is_lawful_monad.{u_1, u_1} option.{u_1} option.monad.{u_1}
end test
