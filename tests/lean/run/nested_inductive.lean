set_option trace.inductive_compiler.nested.define.failure true
set_option max_memory 1000000

inductive vec (A : Type) : nat -> Type
| vnil : vec 0
| vcons : Pi (n : nat), A -> vec n -> vec (n+1)

namespace X1

inductive foo
| mk : list foo -> foo

end X1

namespace X2

inductive foo (A : Type)
| mk : A -> list foo -> foo

end X2

namespace X3

inductive foo (A B : Type)
| mk : A -> B -> vec foo 0 -> foo

end X3

namespace X4

inductive foo (A : Type)
| mk : Pi (n : nat), A -> vec foo n -> foo

end X4

namespace X5

inductive foo (A : Type)
| mk : A -> (Pi (m : nat), vec foo m) -> foo

end X5

namespace X6

inductive foo (A : Type)
| mk : Pi (n : nat), A -> (Pi (m : nat), vec foo (n + m)) -> foo

end X6

namespace X7

inductive foo (A : Type)
| mk : Pi (n : nat), A -> list A -> prod A A -> (Pi (m : nat), vec foo (n + m)) -> vec foo n -> foo

end X7

namespace X8

inductive foo (A : Type)
| mk₁ : Pi (n : nat), A -> (Pi (m : nat), vec (list (list foo)) (n + m)) -> vec foo n -> foo
| mk₂ : Pi (n : nat), A -> list A -> prod A A -> (Pi (m : nat), vec foo (n + m)) -> vec foo n -> foo

end X8

namespace X9

inductive foo (A : Type)
| mk₁ : Pi (n : nat), A -> (Pi (m : nat), vec (list (list foo)) (n + m)) -> vec foo n -> foo
| mk₂ : Pi (n : nat), A -> list A -> prod A A -> (Pi (m : nat), vec foo (n + m)) -> vec foo n -> foo

end X9

namespace X10
print "many layers of nesting nested inductive types"

inductive wrap (A : Type)
| mk : A -> wrap

inductive box (A : Type)
| mk : A -> wrap (list box) -> box

inductive foo (A : Type)
| mk : A -> box foo -> foo

inductive bar
| mk : box (foo bar) -> bar

end X10

namespace X11
print "intro rule that introduces additional nesting"

inductive wrap (A : Type) : Type
| mk : list A -> wrap

inductive foo
| mk : wrap foo -> foo

end X11

namespace X12
print "intro rule that introduces a lot of additional nesting"

inductive wrap (A : Type) : Type
| mk : list (list A) -> wrap

inductive box (A : Type)
| mk : A -> wrap (list box) -> box

inductive foo (A : Type)
| mk : A -> box (wrap foo) -> foo

inductive bar
| mk : box (foo bar) -> bar

end X12

namespace X13
print "crazy additional nesting"

inductive wrap (A : Type) : Type
| mk : Pi (n : nat), vec (list A) n -> wrap

inductive box (A : Type)
| mk : Pi (n : nat), A -> vec (wrap box) n -> box

inductive foo (A : Type)
| mk : A -> box (wrap foo) -> foo

inductive bar
| mk : box (foo bar) -> bar

end X13

namespace X15
print "with reducible definitions"

attribute [reducible] definition list' := @list

inductive wrap (A : Type) : Type
| mk : A -> list' A -> wrap

attribute [reducible] definition wrap' := @wrap

inductive foo (A : Type)
| mk : A -> wrap' (list' foo) -> foo

inductive bar (A : Type)
| mk : A -> foo bar -> bar

end X15
