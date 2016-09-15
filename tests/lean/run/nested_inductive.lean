set_option trace.inductive_compiler.nested.define.failure true
set_option max_memory 1000000

inductive vec (A : Type) : nat -> Type
| vnil : vec 0
| vcons : Pi (n : nat), A -> vec n -> vec (n+1)

namespace X1

inductive foo.{l} : Type.{max 1 l}
| mk : list foo -> foo

end X1

namespace X2

inductive foo.{l} (A : Type.{l}) : Type.{max 1 l}
| mk : A -> list foo -> foo

end X2

namespace X3

inductive foo.{l} (A : Type.{l}) : Type.{max 1 l}
| mk : A -> vec foo 0 -> foo

end X3

namespace X4

inductive foo.{l} (A : Type.{l}) : Type.{max 1 l}
| mk : Pi (n : nat), A -> vec foo n -> foo

end X4

namespace X5

inductive foo.{l} (A : Type.{l}) : Type.{max 1 l}
| mk : A -> (Pi (m : nat), vec foo m) -> foo

end X5

namespace X6

inductive foo.{l} (A : Type.{l}) : Type.{max 1 l}
| mk : Pi (n : nat), A -> (Pi (m : nat), vec foo (n + m)) -> foo

end X6

namespace X7

inductive foo.{l} (A : Type.{l}) : Type.{max 1 l}
| mk₁ : Pi (n : nat), A -> (Pi (m : nat), vec foo (n + m)) -> vec foo n -> foo
| mk₂ : Pi (n : nat), A -> list A -> prod A A -> (Pi (m : nat), vec foo (n + m)) -> vec foo n -> foo

end X7

namespace X8

inductive foo.{l} (A : Type.{l}) : Type.{max 1 l}
| mk₁ : Pi (n : nat), A -> (Pi (m : nat), vec (list (list foo)) (n + m)) -> vec foo n -> foo
| mk₂ : Pi (n : nat), A -> list A -> prod A A -> (Pi (m : nat), vec foo (n + m)) -> vec foo n -> foo

end X8

namespace X9

inductive foo.{l} (A : Type.{l}) : Type.{max 1 l}
| mk₁ : Pi (n : nat), A -> (Pi (m : nat), vec (list (list foo)) (n + m)) -> vec foo n -> foo
| mk₂ : Pi (n : nat), A -> list A -> prod A A -> (Pi (m : nat), vec foo (n + m)) -> vec foo n -> foo

end X9

namespace X10
print "many layers of nesting nested inductive types"

inductive wrap (A : Type) : Type
| mk : A -> wrap

inductive box.{l} (A : Type.{l}) : Type.{max 1 l}
| mk : wrap (list box) -> box

inductive foo.{l} (A : Type.{l}) : Type.{max 1 l}
| mk : A -> box (box foo) -> foo

inductive bar.{l} : Type.{max 1 l}
| mk : box (foo bar) -> wrap (box (foo bar)) -> bar

end X10

namespace X11
print "intro rule that introduces additional nesting"

inductive wrap (A : Type) : Type
| mk : list A -> wrap

inductive foo.{l} : Type.{max 1 l}
| mk : wrap foo -> foo

end X11

namespace X12
print "intro rule that introduces a lot of additional nesting"

inductive wrap (A : Type) : Type
| mk : list (list A) -> wrap

inductive box.{l} (A : Type.{l}) : Type.{max 1 l}
| mk : wrap (list box) -> box

inductive foo.{l} (A : Type.{l}) : Type.{max 1 l}
| mk : A -> box (box foo) -> foo

inductive bar.{l} : Type.{max 1 l}
| mk : box (foo bar) -> wrap (box (foo bar)) -> bar

end X12

namespace X13
print "crazy additional nesting"

inductive wrap (A : Type) : Type
| mk : Pi (n : nat), vec (list (list A)) n -> wrap

inductive box.{l} (A : Type.{l}) : Type.{max 1 l}
| mk : Pi (n : nat), vec (wrap (list box)) n -> box

inductive foo.{l} (A : Type.{l}) : Type.{max 1 l}
| mk : A -> list (box (box (wrap foo))) -> foo

inductive bar.{l} : Type.{max 1 l}
| mk : foo (box (foo bar)) -> foo (wrap (box (foo bar))) -> bar

end X13

namespace X14
print "insane nesting"

inductive wrap (A : Type) : Type
| mk : Pi (n : nat), vec A n -> wrap

inductive box.{l} (A : Type.{l}) : Type.{max 1 l}
| mk : Pi (n : nat), vec (wrap (list box)) n -> box
| mk₂ : wrap box -> box

inductive foo.{l} (A : Type.{l}) : Type.{max 1 l}
| mk : A -> list (box (box (wrap foo))) -> foo

inductive bar.{l} : Type.{max 1 l}
| mk : foo (box (foo bar)) -> foo (wrap (box (foo bar))) -> bar


end X14
