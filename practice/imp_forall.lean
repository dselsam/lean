set_option trace.simplifier true
open tactic
--set_option simplify.max_steps 2000
--attribute imp_congr_eq [congr] [priority 1001]


constants (A B C D : Prop) (HAC : A = C) (HBC : B = C) (f : Prop → Prop)
attribute HAC HBC [simp]

example : (A = D) → f C = f D := by simp >> intron 1 >> triv

/-

example {A B : Prop} {P Q : A → Prop} : (A = B) → (∀ (x : A), P x = Q x) → ((∀ (x : A), P x) = (∀ (x : A), Q x)) := by simp >> intron 2 >> triv

e
xample : 1 = (1:nat) := by simp
-/
