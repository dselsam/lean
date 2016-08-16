prelude
definition Prop := Type.{0}

xinductive nat
| zero : nat
| succ : nat → nat

xinductive list (A : Type)
| nil {} : list
| cons   : A → list → list

xinductive list2 (A : Type) : Type
| nil2 {} : list2
| cons2   : A → list2 → list2

xinductive and (A B : Prop) : Prop
| and_intro : A → B → and

xinductive cls {T1 : Type} (R1 : T1 → T1 → Prop) {T2 : Type} (R2 : T2 → T2 → Prop) (f : T1 → T2)
| mk : (∀x y : T1, R1 x y → R2 (f x) (f y)) → cls
