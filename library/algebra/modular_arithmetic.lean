/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam
-/
import .ordered_field

structure has_modular_arith [class] (A : Type) [has_mod A] (n : ℕ) :=
(eq_modulo : ∀ (a : A), a = (a % n))

-- TODO(dhs): put into actual bit-vector development

constant (nat_pow : ℕ → ℕ → ℕ)
constant (bv : Π (n : ℕ), Type.{1})
constant (bmod : Π {n:ℕ}, bv n → ℕ → bv n)
constant (b_eq_modulo : ∀ (n:ℕ) (v : bv n), v = bmod v (nat_pow 2 n))

definition bv_has_mod [instance] (n : ℕ) : has_mod (bv n) := has_mod.mk bmod

definition bv_has_modular_arith [instance] (n : ℕ) : has_modular_arith (bv n) (nat_pow 2 n) :=
  has_modular_arith.mk (b_eq_modulo n)

definition bv_comm_ring [instance] (n : ℕ) : comm_ring (bv n) := sorry

set_option simplify.numerals true

example (n : ℕ) : (0 : bv n) + 12 = 12 := by tactic.simp >> tactic.triv
example (n : ℕ) : (11 : bv n) + 12 = 23 := by tactic.simp >> tactic.triv

-- TODO(dhs): some examples with modular arithmetic (need 2^n)

-- TODO(dhs): replace once ints have been developed
constants (int : Type.{1})
definition int_decidable_linear_ordered_comm_ring [instance] (n : ℕ) : decidable_linear_ordered_comm_ring int := sorry
constant (nat_to_int : nat → int)

constants (real : Type.{1})
definition real_discrete_linear_ordered_field [instance] (n : ℕ) : discrete_linear_ordered_field real := sorry
constants (nat_to_real : nat → real) (int_to_real : int → real)
