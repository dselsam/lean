set_option pp.all true
set_option trace.inductive_compiler.nested.pack true

inductive box (A : Type) : Type
| mk : A -> box

inductive foo.{l} : Type.{max 1 l}
| mk : box foo -> foo

check @foo.pack_0_0
check @foo.unpack_0_0
