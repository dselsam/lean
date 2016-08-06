open tactic

meta_definition psimp : tactic unit :=
do simp_lemmas  ← mk_simp_lemmas_core reducible [] [`congr],
   (new_target, Heq) ← target >>= simplify_core failed `iff simp_lemmas,
   assert `Htarget new_target, swap,
   Ht ← get_local `Htarget,
   mk_app `iff.mpr [Heq, Ht] >>= exact,
   try triv



variables (P Q R : Prop)

-- Iff
example : P ↔ P := by psimp

-- Eq
example : (P = P) ↔ true := by psimp
example : ((¬ P) = (¬ Q)) ↔ (P = Q) := by psimp
example : (true = P) ↔ P := by psimp
example : (false = P) ↔ ¬ P := by psimp
example : (false = ¬ P) ↔ P := by psimp
example : (P = true) ↔ P := by psimp
example : (P = false) ↔ ¬ P := by psimp
example : (¬ P = false) ↔ P := by psimp
example : (P = ¬ P) ↔ false := by psimp
example : (¬ P = P) ↔ false := by psimp

-- Not
example : ¬ ¬ P ↔ P := by psimp
example : ¬ ¬ ¬ P ↔ ¬ P := by psimp
example : ¬ false ↔ true := by psimp
example : ¬ true ↔ false := by psimp

example : ¬ (P = Q) ↔ (¬ P) = Q := by psimp

-- And
example : P ∧ P ↔ P := by psimp
example : P ∧ P ↔ P ∧ P ∧ P := by psimp

example : P ∧ Q ↔ Q ∧ P := by psimp
example : P ∧ Q ∧ R ↔ R ∧ Q ∧ P := by psimp
example : P ∧ Q ∧ R ∧ P ∧ Q ∧ R ↔ R ∧ Q ∧ P := by psimp

example : P ∧ true ↔ P := by psimp
example : true ∧ P ∧ true ∧ P ∧ true ↔ P := by psimp

example : P ∧ false ↔ false := by psimp
example : false ∧ P ∧ false ∧ P ∧ false ↔ false := by psimp

example : P ∧ Q ∧ R ∧ true ∧ ¬ P ↔ false := by psimp

-- Or
example : P ∨ P ↔ P := by psimp
example : P ∨ P ↔ P ∨ P ∨ P := by psimp

example : P ∨ Q ↔ Q ∨ P := by psimp
example : P ∨ Q ∨ R ↔ R ∨ Q ∨ P := by psimp
example : P ∨ Q ∨ R ∨ P ∨ Q ∨ R ↔ R ∨ Q ∨ P := by psimp

example : P ∨ false ↔ P := by psimp
example : false ∨ P ∨ false ∨ P ∨ false ↔ P := by psimp

example : P ∨ true ↔ true := by psimp
example : true ∨ P ∨ true ∨ P ∨ true ↔ true := by psimp

example : P ∨ Q ∨ R ∨ false ∨ ¬ P ↔ true := by psimp

-- Contextual
example : (P ↔ Q) → (P ↔ Q) := by psimp >> intron 1 >> triv
example : (P ↔ Q) → ((P ∧ P) ↔ (Q ∧ Q)) := by psimp >> intron 1 >> triv

example : (P ↔ (Q ∧ R)) → ((P ∧ P) ↔ (R ∧ P ∧ Q)) := by psimp >> intron 1 >> triv

set_option trace.simplifier.theory true
example : (P ↔ (Q ∧ R ∧ Q)) → ((P ∧ P) ↔ (R ∧ P ∧ Q)) := by psimp >> intron 1 >> triv
