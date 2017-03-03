set_option pp.all true

universe variables u v w

namespace X1
print "?U does not unify: old solution"

inductive foo (A : Type u) (B : Type (v+1)) : Type (max u (v+1))
| mk : A → B → foo

check @foo

end X1

namespace X2
print "?U unifies with a constant, no others above: done"

inductive bar (A : Sort 2) : Sort 2
| mk : A → bar

inductive foo : Sort 2
| mk : Type → bar foo → foo

check @foo

end X2

namespace X3
print "?U unifies with a constant, and there are others: error if the others are not <= constant"
inductive bar (A : Sort 2) : Sort 2
| mk : A → bar

inductive foo (A : Sort (u+2)) : Sort 2
| mk : A → bar foo → foo

end X3

namespace X4
print "?U unifies with a meta, but nesting recursor goes to Prop"
print "TODO(dhs): do we throw error or just infer that result must be Prop?"
inductive bar (A : Sort u) : Sort u
| mk : A → bar

inductive foo : Sort u -- yield error, or guess Prop?
| mk : bar foo → foo

end X4

namespace X5
print "?U unifies with a meta, no others above: old approach, set level-param"

inductive bar (A : Sort u) : Sort (max u 1)
| mk : A → bar

inductive foo (A : Sort u) : Sort (max u 1)
--| mk : A → bar.{max u 1} foo → foo
| mk : A → bar foo → foo

end X5

namespace X6
print "?U unifies with a meta, with others above: old approach, set level-param "

inductive bar (A : Sort u) : Sort (max u 1)
| mk : A → bar

inductive foo (A : Sort v) : Sort (max v (max u 1))
--| mk : A → bar.{max v (max u 1)} foo → foo
| mk : A → bar foo → foo

end X6

namespace X7
print "?U unifies with a shifted meta, no others above: set level-param to be inverse of meta"

inductive bar (A : Sort (u + 3)) : Sort (u + 3)
| mk : A → bar

inductive foo (A : Sort u) : Sort (u + 3)
| mk : A → bar foo → foo

end X7

namespace X8
print "?U unifies with a shifted meta, with others above: error, cannot invert around the max"
inductive bar (A : Sort (u + 3)) : Sort (u + 3)
| mk : A → bar

inductive foo (A : Sort v) : Sort (max v (u + 3))
| mk : A → bar.{max v u} foo → foo


end X8
