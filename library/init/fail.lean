/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Daniel Selsam
-/
prelude
import init.functor init.string init.trace

structure has_fail [class] (A : Type) : Type := (fail : A)

inline definition fail {A : Type} [has_fail A] : A := has_fail.fail A
