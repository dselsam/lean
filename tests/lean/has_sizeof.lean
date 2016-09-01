set_option pp.binder_types true

namespace X0

inductive foo (A : Type) : Type
| mk : A -> foo -> foo

check @foo.has_sizeof
check @foo.mk.has_sizeof_spec

end X0

namespace X1

inductive foo (A : Type) (B : nat -> A -> A -> Type) (C : Type)  : Type
| mk : Pi (a : A) (n : nat), B n a a -> (bool -> B n a a) -> (bool -> C) -> (bool -> foo) -> foo

check @foo.has_sizeof
check @foo.mk.has_sizeof_spec

end X1
