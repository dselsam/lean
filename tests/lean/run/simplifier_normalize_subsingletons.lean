open tactic

namespace synth_congr

universe variable l
constants (ss : Π {A : Type.{l}}, A → Type.{l})
          [ss_ss : ∀ T (t : T), subsingleton (ss t)]
          (A : Type.{l})
          (a₁ a₁' : A) (H₁ : a₁ = a₁')
          (ss₁ : ss a₁)
          (ss₁' : ss a₁')
          (f :  Π (X : Type.{l}) (x₁ : X) (ss_x₁ : ss x₁), Type.{l})

attribute ss_ss [instance]
attribute H₁ [simp]

set_option trace.simplifier.subsingleton true
example : f A a₁ ss₁ = f A a₁' ss₁' := by simp

end synth_congr

namespace user_congr

universe variable l
constants (ss : Π {A : Type.{l}}, A → Type.{l})
          [ss_ss : ∀ T (t : T), subsingleton (ss t)]
          (A : Type.{l})
          (a₁ a₁' : A) (H₁ : a₁ = a₁')
          (ss₁ : ss a₁)
          (ss₁' : ss a₁')
          (f :  Π (X : Type.{l}) (x₁ : X) (ss_x₁ : ss x₁), Type.{l})
          (f_congr : Π (X : Type.{l}) (x₁ x₂ : X) (Hx : x₁ = x₂) (ss₁ : ss x₁), f X x₁ ss₁ = f X x₂ (eq.rec ss₁ Hx))

attribute ss_ss [instance]
attribute H₁ [simp]
attribute f_congr [congr]


set_option trace.simplifier.subsingleton true
example : f A a₁ ss₁ = f A a₁' ss₁' := by simp

end user_congr

namespace lambda

universe variable l
constants (ss : Π {A : Type.{l}}, A → Type.{l})
          [ss_ss : ∀ (T : Type) (t : T), subsingleton (ss t)]
          (A : Type.{l}) (a : A)
          (ss₁ ss₂ : ss a)

attribute ss_ss [instance]

set_option trace.simplifier.subsingleton true
example : ss₁ = ss₂ := by simp
example : (λ p : Prop, ss₁) = (λ p : Prop, ss₂) := by simp
example : (λ (A : Type) (a : A), ss₁) = (λ (A : Type) (a : A), ss₂) := by simp

end lambda

namespace dont_crash_when_locals_incompatible

universe variable l
constants (ss : Π {A : Type.{l}}, A → Type.{l})
          [ss_ss : ∀ (T : Type) (t : T), subsingleton (ss t)]
          (A : Type.{l}) (a : A)
          (ss₁ ss₂ : ss a)

attribute ss_ss [instance]

example : (λ (s : ss a), s) = (λ (s : ss a), ss₁) :=
by try simp >> exact sorry

end dont_crash_when_locals_incompatible
