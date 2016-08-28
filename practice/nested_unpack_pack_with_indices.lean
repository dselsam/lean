set_option pp.implicit true
set_option pp.binder_types true
set_option pp.universes false
set_option pp.beta true

/-
The takeaway from this file is that the pack-unpack functions need to take indices.
Details still need to be worked out.
-/

inductive wrap (A : Type) : nat -> Type
| mk : A -> wrap 0 -> wrap 1 -> wrap 2

inductive box (A : Type) : Type
| mk : wrap A 0 -> box

inductive foo.{l} : Type.{max 1 l}
| mk : box foo -> foo

check @nest2.box.pack_0_0
check @nest2.box.unpack_0_0
check @nest2.box.unpack_pack_0_0
check @nest3.wrap.rec
/-
nest2.box.pack_0_0 : wrap nest2.foo 0 → nest3.wrap 0
nest2.box.unpack_0_0 : nest3.wrap 0 → wrap nest2.foo 0
nest2.box.unpack_pack_0_0 : ∀ (x_packed : nest3.wrap 0), nest2.box.pack_0_0 (nest2.box.unpack_0_0 x_packed) = x_packed
nest3.wrap.rec :
  Π (C : Π (a : ℕ), nest3.wrap a → Type),
    (Π (a : nest3.nest2.foo) (a_1 : nest3.wrap 0) (a_2 : nest3.wrap 1),
       C 0 a_1 → C 1 a_2 → C 2 (nest3.wrap.mk a a_1 a_2)) →
    (Π (a : ℕ) (x : nest3.wrap a), C a x)
-/

/-
We can already see the mismatch.
The [unpack_pack] lemma uses [pack] and [unpack] that are specialized for the index,
where as [nest3.wrap.rec] require a motive that is parametric on the indices,
and so the motive cannot even be stated cleanly as is.

On the surface it seems simple enough to work around.
[pack] and [unpack] are defined by recursion and so can originally take the indices as arguments,
we just specialized them before putting them in the environment.
We can take the indices as arguments instead in the environment version.

But what happens if there is an index that has local variables in it?
I think this is easy as well.

When we apply the [pack] and [unpack], we will be in a local context that let's us state them.
The version in the environment doesn't need to refer to the indices at all, and so does not
need to be abstracted over locals that appear in them.
-/
