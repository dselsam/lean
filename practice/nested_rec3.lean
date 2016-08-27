set_option pp.all true

inductive wrap (A : Type)
| mk : A -> wrap

inductive box (A : Type) : Type
| mk : list A -> list A -> box -> box

-- inductive foo.{l} : Type.{max 1 l}
-- | mk : box foo -> foo

mutual_inductive foo, fbox, flist
with foo : Type
| mk : fbox -> foo
with fbox : Type
| mk : flist -> flist -> fbox -> fbox
with flist : Type
| cons : foo -> flist -> flist

definition foo₂ := @foo
definition fbox₂ := @fbox

/-
flist.rec.{l_1} :
  Π (C : flist → Type.{l_1}), (Π (a : foo) (a_1 : flist), C a_1 → C (flist.cons a a_1)) → (Π (x : flist), C x)
-/

set_option trace.inductive_compiler.nested.pack true
definition pack_flist : list foo -> flist := sorry
definition unpack_flist : flist -> list foo := sorry

/-
flist.rec.{l_1} :
  Π (C : flist → Type.{l_1}), (Π (a : foo) (a_1 : flist), C a_1 → C (flist.cons a a_1)) → (Π (x : flist), C x)
-/
/-
eq.rec_on.{l_1 l_2} : Π {A : Type.{l_2}} {a : A} {C : A → Type.{l_1}} {a_1 : A}, @eq.{l_2} A a a_1 → C a → C a_1
-/
definition flist_pack_unpack : Pi (xs : flist), pack_flist (unpack_flist xs) = xs :=
@flist.rec (λ (xs : flist), pack_flist (unpack_flist xs) = xs)
           (λ (x : foo) (xs : flist) (H : pack_flist (unpack_flist xs) = xs),
             have H1 : flist.cons x (pack_flist (unpack_flist xs)) = (flist.cons x xs), from
             @eq.rec_on _
                        _
                        (λ (ys : flist), flist.cons x ys = flist.cons x xs)
                        _
                        (eq.symm H)
                        rfl,
             show pack_flist (unpack_flist (flist.cons x xs)) = flist.cons x xs, from sorry
           )




definition flist_unpack_pack : Pi (xs : list foo), unpack_flist (pack_flist xs) = xs := sorry

attribute [reducible] definition foo₂.mk (fb : fbox₂) : foo₂ := foo.mk fb
attribute [reducible] definition fbox₂.mk (xs ys : list foo) (b : fbox₂) : fbox₂ := fbox.mk (pack_flist xs) (pack_flist ys) b

-- eq.rec_on : Π {A : Type} {a : A} {C : A → Type} {a_1 : A}, a = a_1 → C a → C a_1
/-
fbox.rec.{l_1} :
  Π (C : fbox → Type.{l_1}),
    (Π (a a_1 : flist) (a_2 : fbox), C a_2 → C (fbox.mk a a_1 a_2)) → (Π (x : fbox), C x)
-/

-- and we want to define fbox₂.rec:
open tactic

-- meta_constant rewrite_core : transparency → bool → occurrences → bool → expr → tactic unit
/-
meta_definition prove_rec : tactic unit :=
do trace_state,
   to_expr `(flist_pack_unpack  >>= rewrite_core semireducible ff occurrences.all tt,
   trace_state
-/
definition fbox₂.rec (C : fbox₂ → Type)
                     (mp : Pi (xs ys : list foo) (x : fbox), C x -> C (fbox₂.mk xs ys x))
                     (x : fbox₂) : C x :=
by do to_expr `(@fbox.rec C) >>= apply,
      xs ← intro `xs,
      ys ← intro `ys,
      x ← intro `x,
      to_expr `(flist_pack_unpack xs) >>= rewrite_core semireducible ff occurrences.all tt,
      to_expr `(flist_pack_unpack ys) >>= rewrite_core semireducible ff occurrences.all tt,
      to_expr `(mp) >>= apply


definition fbox₂.rec₃ (C : fbox₂ → Type)
                     (mp : Pi (xs ys : list foo) (x : fbox), C x -> C (fbox₂.mk xs ys x))
                     (x : fbox₂) : C x :=
@fbox.rec C
          (λ (xs ys : flist) (x : fbox) (Cx : C x),
            @eq.rec_on flist
                       (pack_flist (unpack_flist xs))
                       (λ (xs : flist), C (fbox.mk xs ys x)) -- this is the GOAL
                       xs
                       (flist_pack_unpack xs)
                       (@eq.rec_on flist
                                   (pack_flist (unpack_flist ys))
                                   (λ (ys : flist), C (fbox.mk (pack_flist (unpack_flist xs)) ys x)) -- this is the GOAL after rewriting the first time
                                   ys
                                   (flist_pack_unpack ys)
                                   (mp (unpack_flist xs) (unpack_flist ys) x Cx)))
          x
