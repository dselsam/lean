set_option pp.all true
set_option pp.universes false
set_option pp.beta true
--set_option trace.inductive_compiler.nested.pack true


inductive wrap (A : Type)
| mk : A -> wrap

inductive box (A : Type) : Type
| mk : list A -> list A -> box -> box

inductive foo.{l} : Type.{max 1 l}
| mk : box foo -> foo

check @nest2.box.unpack_pack_0_0
/-
nest2.box.pack_0_0 : list nest2.foo → nest3.list
nest2.box.pack_0_1 : list nest2.foo → list nest2.foo → nest3.list
nest2.box.unpack_0_0 : nest3.list → list nest2.foo
nest2.box.unpack_0_1 : list nest2.foo → nest3.list → list nest2.foo
-/

/-
@nest3.list.rec :
  Π (C : nest3.list → Type),
    C nest3.list.nil →
    (Π (a : nest3.nest2.foo) (a_1 : nest3.list), C a_1 → C (nest3.list.cons a a_1)) → (Π (x : nest3.list), C x)
-/

lemma nest2.box.unpack_0_0.cons :
  forall (x : nest3.nest2.foo) (xs : nest3.list),
    nest2.box.unpack_0_0 (nest3.list.cons x xs) = list.cons x (nest2.box.unpack_0_0 xs) :=
assume x xs, rfl


lemma nest2.box.unpack_pack_0_0.proof :
  ∀ (xs : nest3.list), nest2.box.pack_0_0 (nest2.box.unpack_0_0 xs) = xs :=
@nest3.list.rec (λ (xs : nest3.list), nest2.box.pack_0_0 (nest2.box.unpack_0_0 xs) = xs)
                rfl
                (λ (x : nest3.nest2.foo)
                   (xs : nest3.list)
                   (H : nest2.box.pack_0_0 (nest2.box.unpack_0_0 xs) = xs),
                   have H_no_compute : nest3.list.cons x (nest2.box.pack_0_0 (nest2.box.unpack_0_0 xs)) = nest3.list.cons x xs, from
                   @eq.rec_on _
                              _
                              (λ (ys : nest3.list), nest3.list.cons x ys = nest3.list.cons x xs)
                              _
                              (eq.symm H)
                              rfl,
                   show nest2.box.pack_0_0 (nest2.box.unpack_0_0 (nest3.list.cons x xs)) = nest3.list.cons x xs, from H_no_compute)







/-
nest2.box.unpack_pack_0_1 :
  ∀ (a : list nest2.foo) (x_packed : nest3.list),
    @eq nest3.list (nest2.box.pack_0_1 a (nest2.box.unpack_0_1 a x_packed)) x_packed
nest2.box.unpack_pack_0_1 :
  ∀ (a : list nest2.foo) (x_packed : nest3.list),
    @eq nest3.list (nest2.box.pack_0_1 a (nest2.box.unpack_0_1 a x_packed)) x_packed
-/
