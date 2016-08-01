namespace smt
open tactic

meta_definition prove : tactic unit :=
do local_context >>= revert_lst,
   simp

end smt
