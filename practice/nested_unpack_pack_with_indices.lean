set_option pp.implicit true
set_option pp.binder_types true
set_option pp.universes false
set_option pp.beta true

/-
The takeaway from this file is that the pack-unpack functions need to take indices.
Details still need to be worked out.
-/

constant (f : nat -> nat -> nat)

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
nest2.box.pack_0_2 : Π (n1 n2 : ℕ), wrap (nest2.foo (f n1 n2)) 0 → nest3.wrap n1 n2 0
nest2.box.unpack_0_2 : Π (n1 n2 : ℕ), nest3.wrap n1 n2 0 → wrap (nest2.foo (f n1 n2)) 0
nest2.box.unpack_pack_0_2 :
  ∀ (n1 n2 : ℕ) (x_packed : nest3.wrap n1 n2 0),
    nest2.box.pack_0_2 n1 n2 (nest2.box.unpack_0_2 n1 n2 x_packed) = x_packed
nest3.wrap.rec :
  Π (C : Π (n1 n2 a : ℕ), nest3.wrap n1 n2 a → Type),
    (Π (n1 n2 : ℕ) (a : nest3.nest2.foo (f n1 n2)) (a_1 : nest3.wrap n1 n2 0) (a_2 : nest3.wrap n1 n2 1),
       C n1 n2 0 a_1 → C n1 n2 1 a_2 → C n1 n2 2 (nest3.wrap.mk n1 n2 a a_1 a_2)) →
    (Π (n1 n2 a : ℕ) (x : nest3.wrap n1 n2 a), C n1 n2 a x)
-/


--definition nest3.wrap.rec.no_indices
--  (C : Pi (n1 n2 : nat), nest3.wrap n1 n2

/-
Okay, we are at a dead-end.
Our pack/unpack lemmas seem to need to take the indices as arguments.
But can we even define these functions?
Suppose we are not willing to exploit decidable equality here, no way.

Alternatively, can we define a nest3.wrap.rec that does not take the indices in the motive?
Best solution is to find a simple way to take the indices in the pack/unpack functions.
Possible issues: what if the indices contain additional local variables?


-/


lemma nest2.box.unpack_pack_0_2.proof :
  forall (n1 n2 n3 : nat) (xs : nest3.wrap n1 n2 n3), nest2.box.pack_0_2 n1 n2 (nest2.box.unpack_0_2 n1 n2 xs) = xs :=
@nest3.wrap.rec (λ (n1 n2 n3 : nat) (xs : nest3.wrap n1 n2 n3), nest2.box.pack_0_2 n1 n2 (nest2.box.unpack_0_2 n1 n2 xs) = xs)
                (λ (n1 n2 : nat)
                   (x : nest3.nest2.foo (f n1 n2))
                   (xs ys : nest3.wrap)
                   (Hxs : nest2.box.pack_0_2 n1 n2 (nest2.box.unpack_0_2 n1 n2 xs) = xs)
                   (Hys : nest2.box.pack_0_2 n1 n2 (nest2.box.unpack_0_2 n1 n2 ys) = ys),
                 have H1 : nest2.box.pack_0_2 n1 n2 (nest2.box.unpack_0_2 n1 n2 (nest3.wrap.mk x xs ys)) = nest3.wrap.mk x xs ys, from sorry,
                 show nest3.wrap.mk x
                                    (nest2.box.pack_0_2 n1 n2 (nest2.box.unpack_0_2 n1 n2 xs))
                                    (nest2.box.pack_0_2 n1 n2 (nest2.box.unpack_0_2 n1 n2 ys))
                      =
                      nest3.wrap.mk x xs ys, from H1)

-- Note to self: something is not right
-- I think it is only coincidence that [nest2.box.pack_0_0] does something on the inner arguments
--


-- (nest3.wrap.mk xs ys)) = nest3.wrap.mk xs ys, from sorry,















/-
lemma nest2.box.unpack_pack_0_1.proof :
   ∀ (prev : list nest2.foo) (xs : nest3.list),
           nest2.box.pack_0_1 prev (nest2.box.unpack_0_1 prev xs) = xs :=
assume prev,
@nest3.list.rec (λ (xs : nest3.list), nest2.box.pack_0_1 prev (nest2.box.unpack_0_1 prev xs) = xs)
                rfl
                (λ (x : nest3.nest2.foo)
                   (xs : nest3.list)
                   (H : nest2.box.pack_0_1 prev (nest2.box.unpack_0_1 prev xs) = xs),
                   have H_no_compute : nest3.list.cons x (nest2.box.pack_0_1 prev (nest2.box.unpack_0_1 prev xs)) = nest3.list.cons x xs, from
                   @eq.rec_on _
                              _
                              (λ (ys : nest3.list), nest3.list.cons x ys = nest3.list.cons x xs)
                              _
                              (eq.symm H)
                              rfl,
                   show nest2.box.pack_0_1 prev (nest2.box.unpack_0_1 prev (nest3.list.cons x xs)) = nest3.list.cons x xs, from H_no_compute)
-/










/-
nest2.box.unpack_pack_0_1 :
  ∀ (a : list nest2.foo) (x_packed : nest3.list),
    @eq nest3.list (nest2.box.pack_0_1 a (nest2.box.unpack_0_1 a x_packed)) x_packed
nest2.box.unpack_pack_0_1 :
  ∀ (a : list nest2.foo) (x_packed : nest3.list),
    @eq nest3.list (nest2.box.pack_0_1 a (nest2.box.unpack_0_1 a x_packed)) x_packed
-/
