import algebra.ring
constants (A : Type.{1}) (A_cr : comm_ring A) (x y z w : A)
attribute A_cr [instance]

open tactic
open simplifier.unit simplifier.ac simplifier.distrib

--set_option trace.simplifier.canonicalize true
--set_option trace.defeq_exhaustive_canonicalizer.canonicalize true

set_option pp.all true

--example : x + y = y + x := by simp >> triv
--example : x + y + z = z + y + x := by simp >> triv
--example : (x + y) * z = x * z + y * z := by simp >> triv
--example : (x + y) * (z + w) = x * z + x * w + y * z + y * w := by simp >> triv

example : (x + y) * (z + w) = w * x + w * y + y * z + x * z := by simp >> triv


--example : (x + y) * (z + w) = x * z + x * w + y * z + y * w * 1 + 0 :=
--by simp >> trace_state >> triv
/-
example : @distrib.to_has_mul.{1} A (@ring.to_distrib.{1} A (@comm_ring.to_ring.{1} A A_cr)) = (@comm_semigroup._trans_of_to_semigroup.{1} A (@comm_ring.to_comm_semigroup.{1} A A_cr)) := rfl
-/

--check @distrib.to_has_mul.{1} A (@ring.to_distrib.{1} A (@comm_ring.to_ring.{1} A A_cr))
--check (@comm_semigroup._trans_of_to_semigroup.{1} A (@comm_ring.to_comm_semigroup.{1} A A_cr))
--eval @distrib.to_has_mul.{1} A (@ring.to_distrib.{1} A (@comm_ring.to_ring.{1} A A_cr))
--eval (@comm_semigroup._trans_of_to_semigroup.{1} A (@comm_ring.to_comm_semigroup.{1} A A_cr))
