/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam
-/

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
