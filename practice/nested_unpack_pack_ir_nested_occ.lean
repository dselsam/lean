set_option pp.implicit true
set_option pp.binder_types true
set_option pp.universes false
set_option pp.beta true

/-
I can't seem to reconstruct the issue I was concerned with earlier today.
I tentatively conclude that I was confused before and am thinking clearly now.
-/

inductive wrap (A : Type) : Type
| mk : A -> wrap

inductive box (A : Type) : Type
| mk : wrap A -> box

inductive foo.{l} : Type.{max 1 l}
| mk : box foo -> foo

/-
check @nest2.box.pack_0_0
check @nest2.box.unpack_0_0
check @nest2.box.unpack_pack_0_0
check @nest3.wrap.rec

nest2.box.pack_0_0 : wrap nest2.foo → nest3.wrap
nest2.box.unpack_0_0 : nest3.wrap → wrap nest2.foo
nest2.box.unpack_pack_0_0 : ∀ (x_packed : nest3.wrap), nest2.box.pack_0_0 (nest2.box.unpack_0_0 x_packed) = x_packed
nest3.wrap.rec :
  Π (C : nest3.wrap → Type), (Π (a : nest3.nest2.foo), C (nest3.wrap.mk a)) → (Π (x : nest3.wrap), C x)
-/
lemma nest2.box.unpack_pack_0_0.proof : forall (xs : nest3.wrap), nest2.box.pack_0_0 (nest2.box.unpack_0_0 xs) = xs :=
@nest3.wrap.rec
  (λ (xs : nest3.wrap), nest2.box.pack_0_0 (nest2.box.unpack_0_0 xs) = xs)
  (λ (x : nest3.nest2.foo),
    show nest2.box.pack_0_0 (nest2.box.unpack_0_0 (nest3.wrap.mk x)) = nest3.wrap.mk x, from rfl)


print foo.pack_0_0
print foo.unpack_0_0
--check @foo.unpack_pack_0_0
--check @nest2.box.rec
/-
foo.pack_0_0 : box foo → nest2.box
foo.unpack_0_0 : nest2.box → box foo
foo.unpack_pack_0_0 : ∀ (x_packed : nest2.box), foo.pack_0_0 (foo.unpack_0_0 x_packed) = x_packed
nest2.box.rec : Π (C : nest2.box → Type), (Π (a : wrap nest2.foo), C (nest2.box.mk a)) → (Π (x : nest2.box), C x)
-/

lemma foo.unpack_pack_0_0.proof : forall (xs : nest2.box), foo.pack_0_0 (foo.unpack_0_0 xs) = xs :=
@nest2.box.rec
  (λ (xs : nest2.box), foo.pack_0_0 (foo.unpack_0_0 xs) = xs)
  (λ (x : wrap nest2.foo),
    show foo.pack_0_0 (foo.unpack_0_0 (nest2.box.mk x)) = nest2.box.mk x, from sorry)
