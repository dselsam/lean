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

constants (A A' : Type.{l}) (x : A) (f : A → A' → A) (g : A' → A → A) (h : A → A → A') (HA : A = A')
          (f.comm : ∀ x y, (: f x y :) = (: g y x :))
attribute f.comm [forward]

definition lam1 : (λ (x : A) (z : A'), f x z) == (λ x z, g z x) := by blast
definition lam2 : (λ (x : A) (z w : A'), f (g z x) w) == (λ x z w, g w (f x z)) := by blast
definition lam3 : (λ (x y : A) (z w : A'), f (g z x) w) == (λ (x y : A) (z w : A'), g w (f x z)) := by blast


definition lam4 : (λ (y : A) (z : A'), f y z) == (λ (y : A) (z : A'), g z y) := by blast
definition lam5 : (λ (y : A) (z : A'), prod.mk (g z y) z) == (λ (y : A) (z : A'), prod.mk (f y z) z) := by blast
definition lam6 : (λ (y : A) (z : A'), prod.mk (g z y) z) == (λ (y : A) (z : A'), prod.mk (f y z) z) := by blast
definition lam7 : (λ (x y : A) (z : A'), f (g z y) z) == (λ (x y : A) (z : A'), g z (g z y)) := by blast
definition lam8 : (λ (x y : A) (z : A'), f (g z y) z) == (λ (x y : A) (z : A'), g z (f y z)) := by blast
definition lam9 : (λ (x y : A) (z : A'), f (g z y) z) == (λ (x y : A) (z : A'), g z (g z y)) := by blast

definition lam10 : (λ (x y : A) (z w : A'), f (g (h x y) y) (h y x)) == (λ (x y : A) (z w : A'), g (h y x) (f y (h x y))) := by blast
