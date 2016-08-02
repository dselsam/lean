namespace smt
open tactic

meta_definition prove : tactic unit :=
do n ← local_context >>= revert_lst,
   simp,
   now

end smt
