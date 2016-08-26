set_option pp.all true

inductive box (A : Type) : Type
| mk : list A -> box

-- inductive foo.{l} : Type.{max 1 l}
-- | mk : box foo -> foo

mutual_inductive foo, fbox, flist
with foo : Type
| mk : fbox -> foo
with fbox : Type
| mk : flist -> fbox
with flist : Type
| cons : foo -> flist -> flist

definition foo₂ := @foo
definition fbox₂ := @fbox

definition pack_flist : list foo -> flist := sorry
definition unpack_flist : flist -> list foo := sorry
definition flist_pack_unpack : Pi (xs : flist), pack_flist (unpack_flist xs) = xs := sorry
definition flist_unpack_pack : Pi (xs : list foo), unpack_flist (pack_flist xs) = xs := sorry

attribute [reducible] definition foo₂.mk (fb : fbox₂) : foo₂ := foo.mk fb
attribute [reducible] definition fbox₂.mk (xs : list foo) : fbox₂ := fbox.mk (pack_flist xs)

-- eq.rec_on : Π {A : Type} {a : A} {C : A → Type} {a_1 : A}, a = a_1 → C a → C a_1

-- We start with fbox.rec:
-- fbox.rec : Π (C : fbox → Type), (Π (a : flist), C (fbox.mk a)) → (Π (x : fbox), C x)

-- and we want to define fbox₂.rec:

definition fbox₂.rec (C : fbox₂ → Type)
                     (mp : Pi (a : list foo), C (fbox₂.mk a))
                     (x : fbox₂) : C x :=
@fbox.rec C
          (λ (a : flist),
            @eq.rec_on flist
                       (pack_flist (unpack_flist a))
                       (λ (a : flist), C (fbox.mk a))
                       a
                       (flist_pack_unpack a)
                       (mp (unpack_flist a)))
          x

-- The motive only takes indices and the inductive type, all of which will stay the same.
-- Same with the major premise and friends.
-- So we need to process the introduction rules.

-- Suppose given minor premise type:
-- (Π (a : flist), C (fbox.mk a))
-- We can "unpack" this type to yield
-- (Π (a : list foo), C (fbox.mk₂ a))
-- Note that we did two things:
-- 1. We replaced arguments of type TY with arguments of type (unpack_type TY)
-- 2. In the conclusions, we replaced occurrences of <intro_rule> with (lift_intro_rules <intro_rule>)

-- The value is much more complicated.
-- We introduce the local for the inner rec type: (a : flist)
-- When we reach the result `C (fbox.mk a)`,
-- we apply the lifted minor premise local to the (unpack_flist a)
-- Unfortunately, this gives us an element of type `C (fbox.mk (pack_flist (unpack_flist a)))`, and so we need to cast.

-- Before we overfit to this example, let's consider something a little more complicated.
