namespace smt
open tactic

meta_definition intro_all : tactic unit :=
do t ← target,
   n ← mk_fresh_name,
   if expr.is_pi t = tt ∨ expr.is_let t = tt then intro n >> intro_all
   else return unit.star

lemma true_imp_true [simp] (P : Prop) : (P → true) = true :=
propext $ and.intro (assume p, trivial) (assume p q, p)
/-
meta_definition prove : tactic unit :=
do n ← local_context >>= revert_lst,
   simp,
   intro_all,
   assumption
-/

meta_definition prove : tactic unit :=
do n ← local_context >>= revert_lst,
   simp

end smt
