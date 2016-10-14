import smt.core smt.constants

namespace tactic
namespace smt

meta def Z3 : tactic unit :=
do revertAll,
   generalizeNonTheoryConstants,
   intros,
   try introNot,
   try $ by_contradiction `_SMT_negated_goal,
   Z3Core

end smt
end tactic
