import logic

set_option blast.strategy "simple"
set_option blast.ematch true

constants (A : Type.{1})
          (a b : A) (f g : A → A)
          (Hfa : ∀ x, f x = a)
          (Hfb : ∀ x, f x = b)

definition A_inhabited [instance] : inhabited A := inhabited.mk a

attribute Hfa [forward]
attribute Hfb [forward]

--set_option trace.cc.lambda true
--set_option trace.blast.ematch true
definition lam :
(λ x : A, f x) == (λ x : A, f x)
→
(λ x : A, g x) == (λ x : A, g x)
→
a = b := by blast
