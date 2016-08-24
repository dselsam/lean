inductive vector (A : Type) : nat -> Type
| vnil : vector 0
| vcons : Pi (n : nat), A -> vector n -> vector (n+1)

inductive lvector (A : Type) : nat -> Type
| lnil : lvector 0
| lcons : Pi (n : nat), A -> lvector n -> lvector (n+1)

constants (f g h j : nat -> nat)

--Level 3
set_option trace.inductive_compiler.nested.translate true
set_option pp.binder_types true


namespace X
mutual_inductive foo, foo_vector (A : Type)
with foo : nat -> Type
| mk : Pi (n : nat), foo_vector n (g n) -> foo (j n)
with foo_vector : nat -> nat -> Type
| vnil : Pi (n : nat), foo_vector n 0
| vcons : Pi (n₁ n₂ : nat), foo (f n₁) -> foo_vector n₁ n₂ -> foo_vector n₁ (n₂ + 1)

definition vector_foo_to_foo_vector (A : Type) (n₁ : nat) :
  Pi (n₂ : nat), vector (@foo A (f n₁)) n₂ -> @foo_vector A n₁ n₂ :=
@vector.rec (@foo A (f n₁))
            (λ (n₂ : nat) (x : vector (@foo A (f n₁)) n₂), @foo_vector A n₁ n₂)
            (@foo_vector.vnil A n₁)
            (λ (n₂ : nat)
               (x : @foo A (f n₁))
               (xs : vector (@foo A (f n₁)) n₂)
               (IH : @foo_vector A n₁ n₂),
               @foo_vector.vcons A n₁ n₂ x IH)

print vector.vcons
set_option pp.all true
check @vector.rec
/-
[inductive_compiler.nested.translate] motive: λ (a : ℕ) (x_ignore : vector (foo (f n)) a), 28.vector A n a
[inductive_compiler.nested.translate] minor premise: 28.vector.vnil A n
[inductive_compiler.nested.translate] minor premise: λ (n_1 : ℕ) (a : foo (f n)) (a_1 : vector (foo (f n)) n_1) (x : 28.vector A n n_1), 28.vector.vcons A n n_1 a x
-/
end X

set_option trace.inductive_compiler.nested.nested_ind true
inductive foo (A : Type) : ℕ -> Type.{2}
| mk : Pi (n : nat), vector (foo (f n)) (g n) -> foo (j n)
