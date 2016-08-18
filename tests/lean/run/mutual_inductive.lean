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
