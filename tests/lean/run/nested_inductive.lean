set_option pp.binder_types true

-- Note: this could be a regular test, but
-- we construct the types for the outermost types
-- directly from what the user provides, so the type-checker
-- is guaranteeing that the construction is correct

inductive vector (A : Type) : nat -> Type
| vnil : vector 0
| vcons : Pi (n : nat), A -> vector n -> vector (n+1)

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
| mk : Pi (n : nat), vector (foo (f n)) (g n) -> foo (h n)

check @foo
check @foo.mk

end X13

namespace X14
print "capstone with indices"

inductive foo.{l} (A : Type.{l}) : ℕ -> Type.{max 1 l}
| mk₁ : A -> Pi (n : nat), vector (foo (f n)) (g n) -> vector (foo (f n)) (h n) -> foo (j n)
| mk₂ : A -> vector (foo 0) 1 -> (Pi (n : nat), vector (foo 0) (f n)) -> foo 3
| mk₃ : A -> Pi (n : nat), vector (foo (f n)) 0 -> vector (foo (f n)) 1 -> foo (j n)
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

-- Now we start with nested-nested inductives
namespace X17

inductive foo.{l} : Type.{max 1 l}
| mk : list (list foo) -> foo

check @foo
check @foo.mk
end X17

namespace X18

inductive foo.{l} (A : Type.{l}) : A -> Type.{max 1 l}
| mk : Pi (n : nat) (a : A), vector (vector (foo a) n) (f n) -> foo a

check @foo
check @foo.mk

end X18

namespace X19

inductive foo.{l} : Type.{max 1 l}
| mk₁ : list (vector foo 0) -> foo
| mk₂ : vector (list foo) 0 -> foo

check @foo
check @foo.mk₁
check @foo.mk₂

end X19

namespace X20
inductive foo.{l} (A : Type.{l}) : A -> Type.{max 1 l}
| mk₁ : Pi (n : nat) (a : A), (Pi (b : A), bool -> list (vector (vector (foo b) n) (f n))) -> foo a
| mk₂ : Pi (n₁ : nat) (a : A), (Pi (n₂ : nat), vector (list (foo a)) (f (n₁ + n₂))) -> foo a

check @foo
check @foo.mk₁
check @foo.mk₂

end X20

namespace X21

set_option trace.inductive_compiler.nested.mimic_ind true
inductive box (A : Type) : Type
| mk : list (list A) -> box

inductive foo.{l} (A : Type.{l}) : A -> Type.{max 1 l}
| mk₁ : Pi (n : nat) (a : A), (Pi (b : A), bool -> box (list (vector (vector (foo b) n) (f n)))) -> foo a
| mk₂ : Pi (n₁ : nat) (a : A), (Pi (n₂ : nat), vector (box ((list (box (foo a))))) (f (n₁ + n₂))) -> foo a

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
end

namespace X23
inductive mlist.{l} (A : Type.{l}) : Type.{max 1 l}
| cons : mlist -> mlist -> mlist

inductive foo.{l} : Type.{max 1 l}
| mk : mlist (mlist foo) -> foo

check @foo
check @foo.mk
end X23
