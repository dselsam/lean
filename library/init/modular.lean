/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam
-/
prelude
import init.nat

-- TODO(dhs): put this in a better place
structure has_mod [class] (A : Type) := (mod : A → ℕ → A)
definition mod    {A : Type} [has_mod A]    : A → ℕ → A    := has_mod.mod
infix %    := mod
notation [parsing_only] x ` %[`:70 A:0 `] `:0 y:70 := @mod A _ x y
