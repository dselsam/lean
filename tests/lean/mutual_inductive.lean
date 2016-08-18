constant (f : nat -> nat -> Type)
constant (g : nat -> Type)
constant (f00 : f 0 0)

mutual_inductive foo₁, foo₂, foo₃, foo₄ (A : Type) (a : A)
with foo₁ : A -> Type
| mk₁ : foo₁ a
with foo₂ : nat -> Type
| mk₂ : forall (b : A) (n : nat), g n -> foo₁ b -> foo₂ (n+1)
with foo₃ : forall {n₁ n₂ : nat}, f n₁ n₂ -> Type
| mk₃ : A -> foo₂ 0 -> foo₃ f00
with foo₄ : Type
| mk₄ : foo₂ 0 → foo₄

set_option pp.binder_types true
check @foo₁
check @foo₂
check @foo₃
check @foo₄

check @foo₁.mk₁
check @foo₂.mk₂
check @foo₃.mk₃
check @foo₄.mk₄
