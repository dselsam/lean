set_option pp.binder_types true

-- Note: this could be a regular test, but
-- we construct the types for the outermost types
-- directly from what the user provides, so the type-checker
-- is guaranteeing that the construction is correct

inductive vec (A : Type) : nat -> Type
| vnil : vec 0
| vcons : Pi (n : nat), A -> vec n -> vec (n+1)

constants (f g h j : nat -> nat)

namespace X1
print "simplest possible"

inductive foo.{l} : Type.{max 1 l}
| mk : list foo -> foo

check @foo
check @foo.mk

end X1

namespace X2
print "with a parameter"

inductive foo.{l} (A : Type.{l}) : Type.{max 1 l}
| mk : A -> list foo -> foo

check @foo
check @foo.mk

end X2

namespace X3
print "with an index"

inductive foo.{l} (A : Type.{l}) : nat -> Type.{max 1 l}
| mk : A -> list (foo 0) -> foo 0

check @foo
check @foo.mk

end X3

namespace X4
print "with multiple parameters and indices"
inductive foo.{l} (A B : Type.{l}) : nat -> nat -> Type.{max 1 l}
| mk : A -> B -> list (foo 0 0) -> foo 0 1

check @foo
check @foo.mk

end X4

namespace X5
print "with a local"
inductive foo.{l} (A B : Type.{l}) : nat -> nat -> Type.{max 1 l}
| mk : Π (n : nat), A -> B -> list (foo n 0) -> foo 0 n

check @foo
check @foo.mk

end X5

namespace X6
print "nested occ occurs in a Pi"

inductive foo.{l} : Type.{max 1 l}
| mk : (bool -> list foo) -> foo

check @foo
check @foo.mk

end X6

namespace X7
print "nested occ occurs in a Pi and has a Pi local"

inductive foo.{l} : nat -> Type.{max 1 l}
| mk : (Π (n : nat), list (foo n)) -> foo 0

check @foo
check @foo.mk

end X7

namespace X8
print "nested occ occurs in a Pi and has both types of locals"

inductive foo.{l} : nat -> nat -> Type.{max 1 l}
| mk : Π (n₁ : nat), (Π (n₂ : nat), list (foo n₁ n₂)) -> foo n₁ (f n₁)

check @foo
check @foo.mk

end X8

namespace X9
print "nested occ occurs twice"

inductive foo.{l} : Type.{max 1 l}
| mk : list foo -> list foo -> foo

check @foo
check @foo.mk

end X9

namespace X10
print "nested occ occurs twice with different locals"

inductive foo.{l} : nat -> Type.{max 1 l}
| mk : Π (n₁ n₂ : nat), list (foo n₁) -> list (foo n₂) -> foo 0

check @foo
check @foo.mk

end X10

namespace X11
print "nested occ occurs in different intro rules"

inductive foo.{l} : nat -> Type.{max 1 l}
| mk₁ : Π (n : nat), list (foo n) -> list (foo n) -> foo 0
| mk₂ : Π (n : nat), list (foo n) -> list (foo n) -> foo 1

check @foo
check @foo.mk₁
check @foo.mk₂

end X11

namespace X12
print "nested occ occurs with different params"

inductive foo.{l} : nat -> Type.{max 1 l}
| mk : Π (n : nat), list (foo n) -> list (foo (f n)) -> foo 0

check @foo
check @foo.mk

end X12

namespace X13
print "nested ind has indices"

inductive foo.{l} : nat -> Type.{max 1 l}
| mk : Pi (n : nat), vec (foo (f n)) (g n) -> foo (h n)

check @foo
check @foo.mk

end X13

namespace X14
print "capstone with indices"

inductive foo.{l} (A : Type.{l}) : ℕ -> Type.{max 1 l}
| mk₁ : A -> Pi (n : nat), vec (foo (f n)) (g n) -> vec (foo (f n)) (h n) -> foo (j n)
| mk₂ : A -> vec (foo 0) 1 -> (Pi (n : nat), vec (foo 0) (f n)) -> foo 3
| mk₃ : A -> Pi (n : nat), vec (foo (f n)) 0 -> vec (foo (f n)) 1 -> foo (j n)
| mk₄ : A -> Pi (n : nat), (Pi (m : nat), prod A (foo (f (n + m)))) -> foo 0

check @foo
check @foo.mk₁
check @foo.mk₂
check @foo.mk₃
check @foo.mk₄

end X14

namespace X15
print "with Prop"

inductive foo (A B : Prop) : Prop
| mk : and foo foo -> foo

check @foo
check @foo.mk
end X15

namespace X16
print "capstone in Prop "
inductive even (A : Type) : nat -> Prop
| z : A -> even 0
| s : Pi n, A -> even n -> even (n+2)

inductive foo (A B : Prop) : nat -> Prop
| mk₁ : Pi (n₁ : nat), and (foo n₁) (foo (n₁ + 1)) -> or (foo 0) (foo n₁) -> foo (n₁ + 5)
| mk₂ : Pi (n₁ : nat), (Pi (n₂ : nat), and (foo n₂) (foo n₁)) -> foo (n₁ + 6)
| mk₃ : Pi (n₁ : nat), or (foo n₁) (foo (n₁ + 1)) -> and (foo 0) (foo n₁) -> foo (n₁ + 5)
| mk₄ : Pi (n₁ : nat), (Pi (n₂ : nat), or (foo n₂) (foo n₁)) -> foo (n₁ + 6)
| mk₅ : Pi (n₁ : nat), (Pi (n₂ : nat), even (foo (n₁ + n₂)) (n₁ + n₂)) -> even (foo n₁) n₁ -> foo (n₁ + 6)

check @foo
check @foo.mk₁
check @foo.mk₂

end X16

namespace X16b
print "capstone in Prop II"
inductive even (A : Type) : nat -> Prop
| z : A -> even 0
| s : Pi n, A -> even n -> even (n+2)

inductive foo (A B : Prop) : nat -> nat -> Prop
| mk₁ : Pi (n₁ : nat), and (foo 5 n₁) (foo 5 (n₁ + 1)) -> or (foo 5 0) (foo 5 n₁) -> foo 5 (n₁ + 5)
| mk₂ : Pi (n₁ : nat), (Pi (n₂ : nat), and (foo 5 n₂) (foo 5 n₁)) -> foo 5 (n₁ + 6)
| mk₃ : Pi (n₁ : nat), or (foo 5 n₁) (foo 5 (n₁ + 1)) -> and (foo 5 0) (foo 5 n₁) -> foo 5 (n₁ + 5)
| mk₄ : Pi (n₁ : nat), (Pi (n₂ : nat), or (foo 5 n₂) (foo 5 n₁)) -> foo 5 (n₁ + 6)
| mk₅ : Pi (n₁ : nat), (Pi (n₂ : nat), even (foo 5 (n₁ + n₂)) (n₁ + n₂)) -> even (foo 5 n₁) n₁ -> foo 5 (n₁ + 6)

check @foo
check @foo.mk₁
check @foo.mk₂

end X16b

-- Now we start with nested-nested inductives
namespace X17
print "list (list foo) -> foo"
inductive foo.{l} : Type.{max 1 l}
| mk : list (list foo) -> foo

check @foo
check @foo.mk
end X17

namespace X18
print "nested with vecs"
inductive foo.{l} (A : Type.{l}) : A -> Type.{max 1 l}
| mk : Pi (n : nat) (a : A), vec (vec (foo a) n) (f n) -> foo a

check @foo
check @foo.mk

end X18

namespace X19
print "nested with multiple intro rules"
inductive foo.{l} : Type.{max 1 l}
| mk₁ : list (vec foo 0) -> foo
| mk₂ : vec (list foo) 0 -> foo

check @foo
check @foo.mk₁
check @foo.mk₂

end X19

namespace X20
print "nested with pis, indices, and multiple intro rules"
inductive foo.{l} (A : Type.{l}) : A -> Type.{max 1 l}
| mk₁ : Pi (n : nat) (a : A), (Pi (b : A), bool -> list (vec (vec (foo b) n) (f n))) -> foo a
| mk₂ : Pi (n₁ : nat) (a : A), (Pi (n₂ : nat), vec (list (foo a)) (f (n₁ + n₂))) -> foo a

check @foo
check @foo.mk₁
check @foo.mk₂

end X20

namespace X21
print "nested with inductive types whose intro rules introduce additional nesting"
set_option trace.inductive_compiler.nested.mimic_ind true
inductive box (A : Type) : Type
| mk : list (list A) -> box

inductive foo.{l} (A : Type.{l}) : A -> Type.{max 1 l}
| mk₁ : Pi (n : nat) (a : A), (Pi (b : A), bool -> box (list (vec (vec (foo b) n) (f n)))) -> foo a
| mk₂ : Pi (n₁ : nat) (a : A), (Pi (n₂ : nat), vec (box ((list (box (foo a))))) (f (n₁ + n₂))) -> foo a

check @foo
check @foo.mk₁
check @foo.mk₂

end X21

namespace X22
inductive mlist.{l} (A : Type.{l}) : Type.{max 1 l}
| cons : mlist -> mlist -> mlist

inductive foo.{l} : Type.{max 1 l}
| mk : mlist foo -> foo

check @foo
check @foo.mk
end X22

namespace X23
inductive mlist.{l} (A : Type.{l}) : Type.{max 1 l}
| cons : mlist -> mlist -> mlist

inductive foo.{l} : Type.{max 1 l}
| mk : mlist (mlist foo) -> foo

check @foo
check @foo.mk
end X23

namespace X24
inductive vec₁ (A : Type) : nat -> Type
| nil₁ : vec₁ 0
| cons₁ : Pi (n : nat), A -> vec₁ n -> vec₁ (n+1)

inductive vec₂ (A : Type) : nat -> Type
| nil₂ : vec₂ 0
| cons₂ : Pi (n : nat), A -> vec₂ n -> vec₂ (n+1)

constants (f g h j : nat -> nat)

inductive foo.{l} (A : Type.{l}) : ℕ -> Type.{max 1 l}
| mk : Pi (n : nat), vec₂ (vec₁ (foo (f n)) (g n)) (h n) -> foo (j n)

check @foo
check @foo.mk

end X24

namespace X25
print "another random capstone"

inductive box (A : Type) : nat -> Type
| mk₁ : Pi (n₁ n₂ : nat), (Pi (n₃ : nat), vec (list A) (n₁ + n₂ + n₃)) -> box (n₁ + n₂)
| mk₂ : Pi (n₁ n₂ : nat), (Pi (n₃ : nat), list (vec A (n₁ + n₂ + n₃))) -> box (n₁ + n₂)

inductive foo.{l} (A : Type.{l}) : A -> ℕ -> Type.{max 1 l}
| mk₁ : Pi (n : nat) (a : A) (u : A -> A -> A), (Pi (b : A), box (foo (u a b) (f n)) (g n)) ->  foo (u a a) n
| mk₂ : Pi (n : nat) (a : A), (Pi (u : A -> A -> A) (b : A), box (foo (u a b) (f n)) (g n)) ->  foo a n

check @foo
check @foo.mk₁
check @foo.mk₂

end X25

namespace X26
print "nested with a nested"

inductive wrap (A : Type)
| mk : A -> wrap

inductive box.{l} (A : Type.{l}) : Type.{max 1 l}
| mk : wrap box -> box

inductive foo.{l} : Type.{max 1 l}
| mk : box foo -> foo

check @foo
check @foo.mk

end X26

namespace X27
print "nested definitions wrapping inductive types"

definition list₁ := @list

set_option trace.inductive_compiler.nested true
inductive foo.{l} : Type.{max 1 l}
| mk : list₁ (list₁ foo) -> foo

check @foo
check @foo.mk
end X27


/-
namespace X26
print "another random capstone in Prop"
-- TODO(dhs): uncomment once the kernel accepts non-recursive arguments after recursive ones
inductive box (A : Type) : nat -> Prop
| mk₁ : Pi (n₁ n₂ : nat) (P : Prop), (Pi (n₃ : nat) (Q : Prop), or (and P A) (and A Q)) -> box (n₁ + n₂)

inductive foo.{l} (A : Type.{l}) : A -> ℕ -> Prop
| mk₁ : Pi (n : nat) (a : A) (u : A -> A -> A), (Pi (b : A), box (foo (u a b) (f n)) (g n)) ->  foo (u a a) n
| mk₂ : Pi (n : nat) (a : A), (Pi (u : A -> A -> A) (b : A), box (foo (u a b) (f n)) (g n)) ->  foo a n

check @foo
check @foo.mk₁
check @foo.mk₂

end X26
-/
