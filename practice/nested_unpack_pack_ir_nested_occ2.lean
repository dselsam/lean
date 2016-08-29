set_option pp.all true
set_option pp.implicit true
set_option pp.binder_types true
set_option pp.universes false
set_option pp.beta true

/-
Issue: nested occurrences in constructors of inductive types involved in nested occurrences.
-/

inductive box.{l} (A : Type.{l}) : Type.{max 1 l}
| mk : list box -> box

print box

set_option trace.inductive_compiler true
inductive foo.{l} : Type.{max 1 l}
| mk : box foo -> foo

/-
[inductive_compiler.nested.found_occ] illegal occurrence: 22 foo (@sum.inr unit unit unit.star)

Surprisingly, this one fails because:
(a) we are applying WHNF to the ir arg types, and
(b) we only register the outermost guy as ginductive.

Is this what we want? Should we always unfold and only consider basic inductive types
as "real" inductive types?

Update: for now, we add all intermediate decls as ginductive decls.

Either way, we have exposed an error that causes an infinite loop.

mutual_inductive foo, fbox
with foo
| mk : fbox -> foo
with fbox
| mk : list (box foo) -> fbox

mutual_inductive foo, fbox, fbox'
with foo
| mk : fbox -> foo
with fbox
| mk : list fbox' -> fbox
with fbox'
| mk : list (box foo) -> fbox'

The solution is simple: "mimic_ir" needs to pack all arguments.
The correct second step is as follows:

mutual_inductive foo, fbox
with foo
| mk : fbox -> foo
with fbox
| mk : list fbox -> fbox

-/
