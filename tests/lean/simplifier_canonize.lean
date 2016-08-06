import algebra.group
open tactic

set_option simplify.theory false
set_option pp.implicit true

universe l

constants (f₁ : Π (X : Type) (X_grp : group X), X)
constants (f₂ : Π (X : Type) [X_grp : group X], X)
constants (A : Type.{l}) (A_grp₁ : group A)

definition A_grp₂ [irreducible] : group A := A_grp₁
definition A_grp₃ [irreducible] (t : true) : group A := A_grp₁

set_option simplify.canonize_fixed_point false
print "This should fail, since A_grp₂ is not unfolded, and it is not an instance arg"
example : @f₁ A A_grp₁ = @f₁ A A_grp₂ := by simp >> reflexivity

print "This should succeed, since A_grp₂ is an instance arg and gets canonized"
example : @f₂ A A_grp₁ = @f₂ A A_grp₂ := by simp >> reflexivity

print "This should fail to simplify, since we do not reach a fixed point"
example : @f₂ A (A_grp₃ trivial) = @f₂ A A_grp₂ := by simp

print "This should simplify, since we reach a fixed point"
set_option simplify.canonize_fixed_point true
example : @f₂ A (A_grp₃ trivial) = @f₂ A A_grp₂ := by simp
