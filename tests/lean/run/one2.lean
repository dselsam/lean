xinductive one1.{l} : Type.{l}
| unit : one1

xinductive pone : Type.{0}
| unit : pone

xinductive two.{l} : Type.{max 1 l}
| o : two
| u : two

xinductive wrap.{l} : Type.{max 1 l}
| mk : true → wrap

xinductive wrap2.{l} (A : Type.{l}) : Type.{max 1 l}
| mk : A → wrap2

set_option pp.universes true
check @one1.rec
check @pone.rec
check @two.rec
check @wrap.rec
check @wrap2.rec
