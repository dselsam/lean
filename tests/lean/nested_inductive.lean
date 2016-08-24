-- Error: cannot have type Type.{1} and Type.{0}
inductive foo (A B : Prop) : Prop
| mk : list foo -> foo
