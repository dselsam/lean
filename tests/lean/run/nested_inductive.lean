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

inductive foo : Prop
| mk : and foo foo -> foo

end X7
