import smt.smt_theory smt.smt_tactic smt.smt_constants

namespace Errors
open tactic
open tactic.smt

-- No dependent types
example (X : Int → Type) (x : X 0) : x ≠ x → false := by Z3

-- No numerals besides Int, Real, BitVec
example (n : nat) : 2 * n ≠ n + n → false := by generalizeNonTheoryConstants >> Z3



end Errors
