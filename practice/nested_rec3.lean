set_option pp.all true

inductive wrap (A : Type)
| mk : A -> wrap

inductive box (A : Type) : Type
| mk : list A -> list A -> box

-- inductive foo.{l} : Type.{max 1 l}
-- | mk : box foo -> foo

mutual_inductive foo, fbox, flist
with foo : Type
| mk : fbox -> foo
with fbox : Type
| mk : flist -> flist -> fbox
with flist : Type
| cons : foo -> flist -> flist

definition foo₂ := @foo
definition fbox₂ := @fbox

definition pack_flist : list foo -> flist := sorry
definition unpack_flist : flist -> list foo := sorry
definition flist_pack_unpack : Pi (xs : flist), pack_flist (unpack_flist xs) = xs := sorry
definition flist_unpack_pack : Pi (xs : list foo), unpack_flist (pack_flist xs) = xs := sorry

attribute [reducible] definition foo₂.mk (fb : fbox₂) : foo₂ := foo.mk fb
attribute [reducible] definition fbox₂.mk (xs ys : list foo) : fbox₂ := fbox.mk (pack_flist xs) (pack_flist ys)

-- eq.rec_on : Π {A : Type} {a : A} {C : A → Type} {a_1 : A}, a = a_1 → C a → C a_1

-- We start with fbox.rec:
-- fbox.rec : Π (C : fbox → Type), (Π (a : flist), C (fbox.mk a)) → (Π (x : fbox), C x)

-- and we want to define fbox₂.rec:

definition fbox₂.rec (C : fbox₂ → Type)
                     (mp : Pi (xs ys : list foo), C (fbox₂.mk xs ys))
                     (x : fbox₂) : C x :=
@fbox.rec C
          (λ (xs ys : flist),
            @eq.rec_on flist
                       (pack_flist (unpack_flist xs))
                       (λ (xs : flist), C (fbox.mk xs ys))
                       xs
                       (flist_pack_unpack xs)
                       (eq.rec_on (flist_pack_unpack ys) (mp (unpack_flist xs) (unpack_flist ys))))
          x
