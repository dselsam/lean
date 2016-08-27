print "nested with inductive types whose intro rules introduce additional nesting"
--set_option trace.inductive_compiler.nested.nested_rec true
set_option trace.inductive_compiler.nested.pack true

set_option pp.all true
set_option pp.universes false

inductive box (A : Type) : nat -> Type
| mk : Pi (n : nat), A -> box n

inductive vec (A : Type) : nat -> Type
| cons : Pi (n : nat), box A n -> vec n -> vec (n+1)

inductive foo.{l} : nat -> Type.{max 1 l}
| mk : Pi (n : nat), vec (foo n) n -> foo n

check @NEST.NEST.vec.rec
check @NEST.vec.unpack_pack
check @NEST.vec.unpack
check @NEST.vec.pack

-- eq.rec_on : Π {A : Type} {a : A} {C : A → Type} {a_1 : A}, @eq A a a_1 → C a → C a_1


definition nest.vec.rec
           (C : Pi (n1 n2 : nat), NEST.vec n1 n2 -> Type)
           (mp : Pi (n1 n2 : nat) (x : box (NEST.foo n1) n2) (y : NEST.vec n1 n2) (Cy : C n1 n2 y),
                    C n1 (n2+1) (NEST.vec.cons n1 n2 x y))
           (n1 n2 : nat)
           (x : NEST.vec n1 n2) : C n1 n2 x :=
@NEST.NEST.vec.rec C
                   (λ (n1 n2 : nat) (x : NEST.box n1 n2) (y : NEST.NEST.vec n1 n2) (Cy : C n1 n2 y),
                   @eq.rec_on (NEST.box n1 n2)
                              (NEST.vec.pack n1 n2 (NEST.vec.unpack n1 n2 x))
                              (λ (x : NEST.box n1 n2), C n1 (n2+1) (NEST.NEST.vec.cons n1 n2 x y)) -- GOAL
                              x
                              (NEST.vec.unpack_pack n1 n2 x)
                              (mp n1 n2 (NEST.vec.unpack n1 n2 x) y Cy))
                   n1 n2
                   x

print nest.vec.rec
