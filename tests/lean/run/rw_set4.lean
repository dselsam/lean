open tactic

print [congr] congr

example (A : Type) (a b c : A) : (a = b) → (a = c) → a = b :=
by simp >> intron 2 >> reflexivity

example (A : Type) (a b c : A) : (a = c) → (a = b) → a = b :=
by simp >> intron 2 >> reflexivity
