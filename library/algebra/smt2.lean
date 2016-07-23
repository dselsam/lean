import algebra.ordered_field

-- Core
constants (xor : Prop → Prop → Prop)
--constants (distinct: Π {A : Type}, A → A → Prop) -- not actually used

-- Arithmetic
constants (int real : Type.{1})

constants (int_has_add : has_add int)
constants (int_has_mul : has_mul int)
constants (int_has_sub : has_sub int)
constants (int_has_neg : has_neg int)
constants (int_has_div : has_div int)
constants (int_has_lt : has_lt int)
constants (int_has_le : has_le int)
constants (int_has_mod : has_mod int)
constants (int_decidable_linear_ordered_comm_group : decidable_linear_ordered_comm_group int)
attribute [instance] int_has_add int_has_mul int_has_sub int_has_div int_has_neg int_has_le int_has_lt int_has_mod int_decidable_linear_ordered_comm_group

constants (real_has_add : has_add real)
constants (real_has_mul : has_mul real)
constants (real_has_sub : has_sub real)
constants (real_has_neg : has_neg real)
constants (real_has_div : has_div real)
constants (real_has_lt : has_lt real)
constants (real_has_le : has_le real)

attribute [instance] real_has_add real_has_mul real_has_sub real_has_neg real_has_div real_has_le real_has_lt

constants (real.of_int : int → real) (real.to_int : real → int) (real.is_int : real → Prop)

-- Arrays
-- Note: we don't use map yet because of the [option] in the return type
-- Need: inhabited instances
constant (array : Type → Type → Type)
namespace array
constant (select : Π (A B : Type), A → array A B → B)

universe variables l₁ l₂ l₃
constant (store : Π (A : Type.{l₁}) (B : Type.{l₂}), A → B → array.{l₁ l₂ l₃} A B → array.{l₁ l₂ l₃} A B)
end array

namespace tactic
meta_definition smt2 : tactic unit := trace_state >> now
end tactic
