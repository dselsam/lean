import smt.util smt.core smt.typeclasses smt.constants smt.lambda

namespace tactic
namespace smt

meta def Z3 : tactic unit :=
do revertAll,
   -- Note: all Extensions are
   -- (a) verifying, meaning the transformations are proved sound
   -- (b) have PRE and POST conditions of every hypothesis reverted
   liftLambdas,
   stripTheoryTypeclasses,
   generalizeNonTheoryConstants,
   mkTargetFalse,
   -- Z3Core transforms the proof state into an SMT file,
   -- proves UNSAT using Z3, and then uses a macro to justify the proof.
   Z3Core

end smt
end tactic
