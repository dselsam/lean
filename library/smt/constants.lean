import smt.core

namespace tactic
namespace smt
open expr monad

-- TODO(dhs): note that the order of the list matters for generalizing
meta def collectConstants (f : name → bool) : expr → list expr
| (const n ls)               := if f n then [const n ls] else []
| (app f arg)                := list.union (collectConstants f) (collectConstants arg)
| (lam n bi dom bod)         := list.union (collectConstants dom) (collectConstants bod)
| (pi n bi dom bod)          := list.union (collectConstants dom) (collectConstants bod)
| (elet n ty val bod)        := list.union (list.union (collectConstants ty) (collectConstants val)) (collectConstants bod)
| (local_const n pp_n bi ty) := collectConstants ty
| (mvar n ty)                := collectConstants ty
| _                          := []

meta def collectNonTheoryConstants (e : expr) : list expr :=
     collectConstants (λ (n : name), bnot $ isTheoryName n) e

-- Pre: everything has been reverted
-- TODO(dhs): rough edge, recursion is hard even in meta mode
meta def generalizeNonTheoryConstantsCore : unit → tactic unit
| _ := do tgt ← target,
          cs ← return $ list.reverse (collectNonTheoryConstants tgt),
          match cs with
          | [] := skip
          | _  := do mapM' (function.uncurry generalize) (list.zip cs (list.map const_name cs)),
                     revertAll,
                     generalizeNonTheoryConstantsCore ()
          end

meta def generalizeNonTheoryConstants : tactic unit :=
do xs ← local_context,
   match xs with
   | [] := generalizeNonTheoryConstantsCore ()
   | _  := fail $ "generalizeNonTheoryConstants expecting all hypotheses to have been reverted"
   end

end smt
end tactic
