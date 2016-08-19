open tactic nat expr

meta_definition collect_props : list expr → tactic (list expr)
| []        := return []
| (h :: hs) := do
  props   ← collect_props hs,
  ht      ← infer_type h,
  htt     ← infer_type ht,
  (unify htt prop >> return (h :: props)) <|> return props

meta_definition simp_add_prove_max_depth (lemmas : list expr) : ℕ → tactic unit
| 0        := failed
| (succ d) := do l ← local_context >>= collect_props,
                 simplify_goal (simp_add_prove_max_depth lemmas d) (l ++ lemmas),
                 triv

meta_definition strong_simp_add (lemmas : list expr) : tactic unit :=
do l ← local_context >>= collect_props,
   simplify_goal (simp_add_prove_max_depth lemmas 10) (l ++ lemmas),
   try triv

meta_definition strong_simp : tactic unit :=
strong_simp_add []

meta_definition strong_simp_at_add (h : expr) (lemmas : list expr) : tactic unit :=
do simp_core_at (simp_add_prove_max_depth lemmas 10) lemmas h

meta_definition strong_simp_at (h : expr) : tactic unit :=
do strong_simp_at_add h []

meta_definition strong_simp_hyps_add (lemmas : list expr) : tactic unit :=
have aux : list expr → tactic unit
     | []        := skip
     | (h :: hs) := try (strong_simp_at_add h lemmas) >> aux hs,
do l ← local_context,
   aux l

meta_definition strong_simp_hyps : tactic unit :=
strong_simp_hyps_add []

section

variables (a b c d e f : Prop)
example (p : Prop) (a b : nat) : a = b → b ≠ a → p := by strong_simp
example (A : Type₁) (a₁ a₂ : A) : a₁ = a₂ → (λ (B : Type₁) (f : A → B), f a₁) = (λ (B : Type₁) (f : A → B), f a₂) := by strong_simp

end
