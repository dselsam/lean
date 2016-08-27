set_option pp.implicit true
set_option pp.universes false
set_option pp.beta true
set_option trace.inductive_compiler.nested.pack true
set_option trace.inductive_compiler.nested.mimic_ind true
set_option trace.inductive_compiler.nested.mimic_ir true

inductive wrap (A : Type) : nat -> Type
| mk : A -> wrap 0 -> wrap 1 -> wrap 2

inductive box (A : Type) : Type
| mk : wrap A 0 -> box

inductive foo.{l} : Type.{max 1 l}
| mk : box foo -> foo

print nest3.nest2.box.rec
/-
definition nest2.box.rec : Π (C : nest2.box → Type), (Π (a : wrap nest2.foo 0), C (nest2.box.mk a)) → (Π (x : nest2.box), C x) :=
λ C mp x,
  nest3.nest2.box.rec C
    (λ a,
       @eq.rec (nest3.wrap 0) (nest2.box.pack_0_0 (nest2.box.unpack_0_0 a)) (λ a, C (nest3.nest2.box.mk a))
         (mp (nest2.box.unpack_0_0 a))
         a
         (nest2.box.unpack_pack_0_0 a))
    x
-/
check @nest2.box.pack_0_0
check @nest2.box.unpack_0_0
check @nest2.box.unpack_pack_0_0

check @nest3.wrap.rec
/-
nest2.box.unpack_pack_0_0 : ∀ x_packed, nest2.box.pack_0_0 (nest2.box.unpack_0_0 x_packed) = x_packed
nest3.wrap.rec : Π C, (Π a a_1 a_2, C 0 a_1 → C 1 a_2 → C 2 (nest3.wrap.mk a a_1 a_2)) → (Π a x, C a x)
-/
lemma nest2.box.unpack_pack_0_0.proof :
  forall (xs : nest3.wrap), nest2.box.pack_0_0 (nest2.box.unpack_0_0 xs) = xs :=
@nest3.wrap.rec (λ (xs : nest3.wrap), nest2.box.pack_0_0 (nest2.box.unpack_0_0 xs) = xs)
                (λ (x : nest3.nest2.foo)
                   (xs ys : nest3.wrap)
                   (Hxs : nest2.box.pack_0_0 (nest2.box.unpack_0_0 xs) = xs)
                   (Hys : nest2.box.pack_0_0 (nest2.box.unpack_0_0 ys) = ys),
                 have H1 : nest2.box.pack_0_0 (nest2.box.unpack_0_0 (nest3.wrap.mk x xs ys)) = nest3.wrap.mk x xs ys, from sorry,
                 show nest3.wrap.mk x
                                    (nest2.box.pack_0_0 (nest2.box.unpack_0_0 xs))
                                    (nest2.box.pack_0_0 (nest2.box.unpack_0_0 ys))
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
