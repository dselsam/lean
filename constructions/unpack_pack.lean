open tactic

--set_option trace.inductive_compiler.nested.pack true
set_option pp.binder_types true
set_option pp.notation false
--set_option trace.inductive_compiler.nested.pack true

/-
namespace nest1
-- This suggests the following strategy. At each level,
-- (a) define pack and unpack
-- (b) define RFL lemmas pushing them over each constructor (a pain)
-- (c) prove unpack/pack by induction : simp


inductive foo.{l} : Type.{max 1 l}
| mk : list foo -> foo

attribute [simp] definition foo.unpack_pack_0_0.cons (x : _) (xs : nest0.list)
  : foo.pack_0_0 (foo.unpack_0_0 (nest0.list.cons x xs)) = nest0.list.cons x (foo.pack_0_0 (foo.unpack_0_0 xs)) := rfl

--print foo.unpack_0_0

lemma foo.unpack_pack_0_0.proof : forall (xs : nest0.list), foo.pack_0_0 (foo.unpack_0_0 xs) = xs :=
by do xs ← intro `xs,
      induction_core semireducible xs `nest0.list.rec [] ; (reflexivity <|> simp_using_hs)
end nest1
-/

namespace nest2

inductive foo.{l} : Type.{max 1 l}
| mk : list (list foo) -> foo

-- This suggests the following strategy. At each level,
-- (a) define pack and unpack
-- (b) prove [simp] lemmas pushing them over each constructor (a pain to setup, but the proofs should just be [simp])
-- (c) prove unpack/pack by induction ; simp and tag the result as [simp]

-- Note: can do this in C++ just as easily
-- Note: I do not need to store the inner pack/unpack infos anywhere except the temporary simp set.
-- Note: I don't need the intermediate simp rules for previous proofs. For each one,
-- I prove the constructor versions using simp, and TMP add the constructors versions to the simp set,
-- and then remove them once I add the unpack/pack one.

attribute [simp] definition nest0.nest2.foo.unpack_pack_0_0.cons (x : _) (xs : _) :
nest0.nest2.foo.pack_0_0 (nest0.nest2.foo.unpack_0_0 (nest1.list.cons x xs))
=
nest1.list.cons x (nest0.nest2.foo.pack_0_0 (nest0.nest2.foo.unpack_0_0 xs)) := rfl

attribute [simp] lemma nest0.nest2.foo.unpack_pack_0_0.proof : forall (xs : nest1.list), nest0.nest2.foo.pack_0_0 (nest0.nest2.foo.unpack_0_0 xs) = xs :=
by do xs ← intro `xs,
      induction_core semireducible xs `nest1.list.rec [],
      reflexivity,
      simp_using_hs

attribute [simp] definition foo.unpack_pack_0_0.cons (x : nest0.list) (xs : _) :
  foo.pack_0_0 (foo.unpack_0_0 (list.cons x xs)) = list.cons x (foo.pack_0_0 (foo.unpack_0_0 xs)) := sorry

lemma foo.unpack_pack_0_0.proof : forall (xs : list nest0.list), foo.pack_0_0 (foo.unpack_0_0 xs) = xs :=
by do xs ← intro `xs,
      induction_core semireducible xs `list.rec [] ; (reflexivity <|> simp_using_hs)




/-
attribute [defeq] definition foo.unpack_pack_0_0.cons (x : _) (xs : nest0.list)
  : foo.pack_0_0 (foo.unpack_0_0 (nest0.list.cons x xs)) = nest0.list.cons x (foo.pack_0_0 (foo.unpack_0_0 xs)) := rfl

lemma foo.unpack_pack_0_0.proof : forall (xs : nest0.list), foo.pack_0_0 (foo.unpack_0_0 xs) = xs :=
by do xs ← intro `xs,
      induction_core semireducible xs `nest0.list.rec [],
      reflexivity,
      dsimp,
      lrewrite `x,
      reflexivity
-/
end nest2
