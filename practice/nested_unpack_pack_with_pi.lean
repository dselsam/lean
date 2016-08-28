set_option pp.implicit true
set_option pp.binder_types true
set_option pp.universes false
set_option pp.beta true

/-
Takeaway: we need to store the pack/unpack in the environment for the INNER guy,
and then define a light wrapper pack/unpack at the Pi level in terms of it.
Then when we prove things, we introduce guys, unfold to expose the inner pack,
and then use FUNEXT
-/

constant (f : nat -> nat -> nat)

inductive wrap (A : Type) : Type
| mk : A -> wrap -> wrap

inductive box (A : Type) : Type
| mk : (nat -> wrap A) -> box

inductive foo.{l} : nat -> Type.{max 1 l}
| mk : Pi (n1 : nat), (Pi (n2 : nat), box (foo (f n1 n2))) -> foo n1

definition nest2.box.pack_0_2_inner (n1 n2 : nat) (xs : wrap (nest2.foo (f n1 n2))) : nest3.wrap n1 n2 := sorry
definition nest2.box.pack_0_2_outer (n1 n2 : nat) (fxs : nat -> wrap (nest2.foo (f n1 n2))) (n3 : nat) : nest3.wrap n1 n2 :=
nest2.box.pack_0_2_inner n1 n2 (fxs n3)

definition nest2.box.unpack_0_2_inner (n1 n2 : nat) (xs : nest3.wrap n1 n2) : wrap (nest2.foo (f n1 n2)) := sorry
definition nest2.box.unpack_0_2_outer (n1 n2 : nat) (fxs : nat -> nest3.wrap n1 n2) (n3 : nat) : wrap (nest2.foo (f n1 n2)) :=
nest2.box.unpack_0_2_inner n1 n2 (fxs n3)

lemma nest2.box.unpack_pack_0_2.proof :
  forall (n1 n2 : nat) (x : nat → nest3.wrap n1 n2),
    nest2.box.pack_0_2_outer n1 n2 (nest2.box.unpack_0_2_outer n1 n2 x) = x :=
assume (n1 n2 : nat) (x : nat -> nest3.wrap n1 n2),
show nest2.box.pack_0_2_outer n1 n2 (nest2.box.unpack_0_2_outer n1 n2 x) = x, from
have H1 : forall (n : nat), nest2.box.pack_0_2_outer n1 n2 (nest2.box.unpack_0_2_outer n1 n2 x) n = x n, from
  assume (n : nat),
  show nest2.box.pack_0_2_outer n1 n2 (nest2.box.unpack_0_2_outer n1 n2 x) n = x n, from
  show nest2.box.pack_0_2_inner n1 n2 (nest2.box.unpack_0_2_inner n1 n2 (x n)) = x n, from
  have H2 : forall (xs : nest3.wrap n1 n2), nest2.box.pack_0_2_inner n1 n2 (nest2.box.unpack_0_2_inner n1 n2 xs) = xs, from
  @nest3.wrap.rec
    (λ (n1 n2 : nat) (xs : nest3.wrap n1 n2), nest2.box.pack_0_2_inner n1 n2 (nest2.box.unpack_0_2_inner n1 n2 xs) = xs)
    (λ (n1 n2 : nat)
       (x : nest3.nest2.foo (f n1 n2))
       (xs : nest3.wrap n1 n2)
       (Hxs : nest2.box.pack_0_2_inner n1 n2 (nest2.box.unpack_0_2_inner n1 n2 xs) = xs),
         have H_no_compute : nest3.wrap.mk n1 n2 x (nest2.box.pack_0_2_inner n1 n2 (nest2.box.unpack_0_2_inner n1 n2 xs)) = nest3.wrap.mk n1 n2 x xs, from
         @eq.rec_on _
                    _
                    (λ (ys : nest3.wrap n1 n2), nest3.wrap.mk n1 n2 x ys = nest3.wrap.mk n1 n2 x xs)
                    _
                    (eq.symm Hxs)
                    rfl,
         show nest2.box.pack_0_2_inner n1 n2 (nest2.box.unpack_0_2_inner n1 n2 (nest3.wrap.mk n1 n2 x xs)) = nest3.wrap.mk n1 n2 x xs, from sorry)
    n1 n2,
  H2 (x n),

funext H1
