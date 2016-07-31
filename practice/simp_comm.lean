import algebra.binary
open tactic

constants (A : Type.{1}) (a b c d e f g h : A) (op : A → A → A) (op_assoc : is_associative op) (op_comm : is_commutative op)
attribute op_assoc [instance]
attribute op_comm [instance]

infixr `%%` := op

-- |pattern| = 2
-- beginning

namespace pat2
constant (H : a %% b = f)
local attribute H [simp]

example : a %% b = f := by simp
example : c %% a %% b = c %% f := by simp
example : a %% c %% b = c %% f := by simp
example : b %% c %% a = c %% f := by simp
example : b %% a %% c = c %% f := by simp


example : a %% b %% c %% d = d %% f %% c := by simp
example : c %% b %% a %% d = c %% f %% d := by simp
example : c %% d %% a %% b = c %% d %% f := by simp

end pat2

namespace pat3
constant (H : a %% b %% g = f)
attribute H [simp]

set_option pp.notation false

example : a %% b %% g = f := by simp
example : a %% c %% b %% g = c %% f := by simp
example : b %% c %% g %% a = f %% c := by simp
example : g %% a %% b %% c %% d = c %% f %% d := by simp
example : a %% d %% c %% b %% g %% c %% d = c %% d %% f %% c %% d := by simp

end pat3
