set_option pp.all true
set_option pp.universes false
set_option pp.beta true
set_option trace.inductive_compiler.nested.pack true

inductive wrap (A : Type)
| mk : A -> wrap -> wrap -> wrap

inductive box (A : Type) : Type
| mk : wrap A -> box

inductive foo.{l} : Type.{max 1 l}
| mk : box foo -> foo

check @nest2.box.pack_0_0













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
