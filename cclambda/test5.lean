import logic
import data.nat data.fin data.real data.fintype algebra.group
open nat real fintype finset fin

set_option blast.strategy "simple"
set_option blast.ematch true

set_option unifier.conservative true
set_option elaborator.coercions false

theorem Suml_ext {A B : Type} [add_monoid B] (l : list A) (f g : A → B) : (∀ a, f a = g a) → Suml l f = Suml l g := sorry

attribute union_comm [simp]
attribute union_assoc [simp]

namespace fli

constant (n : ℕ)
definition var [reducible] := fin n
definition val [reducible] := bool

namespace assignment

definition assignment (xs : finset var) := Π (x : var), x ∈ xs → val

definition restrict {xs : finset var} (γ : assignment xs) (ys : finset var) (Hss : ys ⊆ xs) : assignment ys :=
  λ (y : var) (Hy : y ∈ ys), γ y (mem_of_subset_of_mem Hss Hy)

lemma restrict_more [forward] (xs xs₁ xs₂ : finset var) (γ : assignment xs) (H12 : xs₁ ⊆ xs₂) (H2 : xs₂ ⊆ xs) :
 restrict (restrict γ xs₂ H2) xs₁ H12 = restrict γ xs₁ (subset.trans H12 H2) :=
by unfold restrict; blast

definition extend {xs : finset var} (γ : assignment xs) {x : var} (Hx : x ∉ xs) (v : val) : assignment (insert x xs) :=
  λ (z : var) (Hz : z ∈ insert x xs),
    if H : z = x then v else γ z (mem_of_mem_insert_of_ne Hz H)
end assignment

open assignment

definition factor (xs : finset var) := assignment xs → ℝ

namespace factor

definition mul [reducible] {xs ys : finset var}
  (φ₁ : factor xs)
  (φ₂ : factor ys) :
    factor (xs ∪ ys) :=
      (λ (γ : assignment (xs ∪ ys)),
        φ₁ (restrict γ xs sorry) * φ₂ (restrict γ ys sorry))

infix `⬝`    := mul

set_option trace.blast.ematch true
set_option trace.cc.lambda true
attribute mul.comm [forward]

lemma mul_comm {xs ys : finset var} (φ₁ : factor xs) (φ₂ : factor ys) : φ₁ ⬝ φ₂ == φ₂ ⬝ φ₁ := by blast

end fli
