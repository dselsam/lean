import smt.core smt.typeclasses smt.constants

namespace tactic
namespace smt

meta def Z3 : tactic unit :=
do revertAll,
   trace "\nbefore strip:",
   trace_state,
   stripTypeclasses,
   trace "\nafter strip:",
   trace_state,
   generalizeNonTheoryConstants,
   intros,
   try introNot,
   try $ by_contradiction `_SMT_negated_goal,
   Z3Core

end smt
end tactic
