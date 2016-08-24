namespace basic
constant (f : ℕ → ℕ → Type)
constant (f00 : f 0 0)

constant (g : ℕ → Type)
constant (g0 : g 0)

mutual_inductive foo₁, foo₂, foo₃, foo₄ (A : Type)
with foo₁ : Π (n₁ n₂ : nat), f n₁ n₂ → Type
| mk : foo₁ 0 0 f00
with foo₂ : Π (n : nat), g n → Type
| mk : foo₂ 0 g0
with foo₃ : nat → Type
| mk {} : foo₃ 0
with foo₄ : Type
| mk {} : foo₄

check @foo₁
check @foo₁.mk
check @foo₂
check @foo₂.mk
check @foo₃
check @foo₃.mk
check @foo₄

check (foo₃.mk : foo₃ ℕ 0)
check (foo₄.mk : foo₄ ℕ)

end basic

namespace nested_indices
mutual_inductive foo, bar
with foo : Type -> Type
| mk : foo (foo (bar poly_unit)) -> foo (foo (bar poly_unit))
with bar : Type -> Type
| mk : bar (foo poly_unit) -> bar (foo (bar (foo (bar poly_unit))))

check @foo.mk
check @bar.mk

end nested_indices

namespace X1
mutual_inductive fonz, foo, bar, rig (A B : Type)
with fonz : nat -> nat -> nat -> Type
| mk : A -> bar tt -> foo 0 0 -> fonz 0 1 2 -> fonz 1 2 3
with foo : nat -> nat -> Type
| mk : B -> bar tt -> foo 0 0 -> foo 0 0
with bar : bool -> Type
| mk : Pi (b : bool) (n : nat), A -> foo 0 n -> foo n 0 -> bar b
with rig : Type
| mk : A -> B -> rig -> foo 0 0 -> bar tt -> rig

check @fonz.rec
check @foo.rec
check @bar.rec
check @rig.rec
end X1

namespace X2
mutual_inductive foo, bar
with foo : Type
| mk : (nat -> foo) -> foo
with bar : Type
| mk : bar

check @foo.rec
check @bar.rec
end X2
