import algebra.ring
constants (A : Type.{1}) (A_cr : comm_ring A) (x y z w : A)
attribute A_cr [instance]

open tactic
open simplifier.unit simplifier.ac simplifier.distrib

set_option trace.simplifier.canonicalize true
--set_option trace.defeq_exhaustive_canonicalizer.canonicalize true

--set_option pp.all true

example : x + y = y + x := by simp >> triv

example : (x + y) * (z + w) = x * z + x * w + y * z + y * w * 1 + 0 :=
by simp >> trace_state >> triv
