import logic

set_option pp.purify_locals false
set_option blast.strategy "simple"

universe l

--set_option trace.cc.lambda true
--set_option trace.blast.ematch true
--set_option trace.debug.blast.ematch true
set_option blast.ematch true
--set_option trace.blast.action true
--set_option trace.blast.search true
--set_option trace.cc.merge true
--set_option trace.cc.state true
set_option pp.all true
set_option trace.app_builder true
constants (A : Type.{l}) (x : A) (f : A → A → A)
constant (f.comm : ∀ x y, (: f x y :) = f y x)
attribute f.comm [forward]


definition lam1 : (λ y, f x y) == (λ y, f y x) := by blast
definition lam2 : (λ x y, f x y) == (λ x y, f y x) := by blast
definition lam3 : (λ x y z, f (f x z) y) == (λ x y z, f y (f z x)) := by blast
definition lam4 : (λ x y, f (f x y) y) == (λ x y, f y (f y x)) := by blast

constant (f.assoc : ∀ x y z, (: f (f x y) z :) = (: f x (f y z) :))
attribute f.assoc [forward]

definition lam3.assoc : (λ x y z, f (f x z) y) == (λ x y z, f (f y z) x) := by blast
definition lam4.assoc : (λ x y z w, f (f x y) (f w z)) == (λ x y z w, f z (f (f w y) x)) := by blast
