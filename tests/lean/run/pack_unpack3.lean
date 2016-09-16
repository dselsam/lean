set_option new_elaborator true

inductive vec (A : Type) : nat -> Type
| vnil : vec 0
| vcons : Pi (n : nat), A -> vec n -> vec (n+1)

inductive tree (A : Type)
| leaf : A -> tree
| node : Pi (n : nat), vec (list tree) n -> tree

attribute [pattern] tree.node
attribute [pattern] tree.leaf

set_option trace.eqn_compiler true

constant P {A : Type} : tree A → Type₁
constant mk1 {A : Type} (a : A) : P (tree.leaf a)
constant mk2 {A : Type} (n : nat) (x : vec (list (tree A)) n) : P (tree.node n x)

noncomputable definition bla {A : Type} : ∀ n : tree A, P n
| (tree.leaf a) := mk1 a
| (tree.node n x) := mk2 n x

check bla._main.equations.eqn_1
check bla._main.equations.eqn_2

noncomputable definition foo {A : Type} [inhabited A] : nat → tree A → nat
| 0     _                                    := sorry
| (n+1) (tree.leaf a)                        := 0
| (n+1) (tree.node m x)                      := foo n (tree.node 0 (vec.vnil (list (tree A))))

check @foo._main.equations.eqn_1
check @foo._main.equations.eqn_2
print @foo._main.equations.eqn_3
