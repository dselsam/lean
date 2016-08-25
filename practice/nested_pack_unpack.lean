open tactic
set_option pp.all true

mutual_inductive foo, foo_list
with foo : Type
| mk : foo_list -> foo
with foo_list : Type
| nil : foo_list
| cons : foo -> foo_list -> foo_list

definition Foo := foo
definition Foo.pack : list Foo -> foo_list :=
@list.rec Foo (λ (ignore : list Foo), foo_list) @foo_list.nil (λ (x : Foo) (ignore : list Foo) (xs : foo_list), foo_list.cons x xs)

definition Foo.unpack : foo_list -> list Foo :=
@foo_list.rec (λ (ignore : foo_list), list Foo) (@list.nil Foo) (λ (x : Foo) (ignore : foo_list) (xs : list Foo), list.cons x xs)

-- protected eliminator eq.rec : Π {A : Type.{l_1}} {a : A} {C : A → Type.{l}}, C a → (Π {a_1 : A}, @eq.{l_1} A a a_1 → C a_1)

lemma Foo.unpack_pack : forall (xs : list Foo), xs = Foo.unpack (Foo.pack xs) :=
@list.rec Foo (λ (xs : list Foo), xs = Foo.unpack (Foo.pack xs))
              rfl
-- Goal: list.cons x xs = Foo.unpack (Foo.pack (list.cons x xs))
-- Can use: Foo.unpack (Foo.pack (list.cons x xs)) = list.cons x (Foo.unpack (Foo.pack xs))
--
              (λ (x : foo) (xs : list Foo) (H : xs = Foo.unpack (Foo.pack xs)),
                @eq.rec (list Foo) xs (λ (zs : list foo), list.cons x xs = list.cons x zs) rfl (Foo.unpack (Foo.pack xs)) H)

/-
  ∀ (x : foo) (xs : list.{?M_5} Foo) (ys : foo_list) (H : @eq.{?M_6} (?M_7 x xs ys) (Foo.unpack (Foo.pack xs)) xs),
    @eq.{?M_8} (?M_9 x xs ys H) (?M_10 x xs ys H) (?M_10 x xs ys H)

  ∀ (a : Foo) (a_1 : list.{?M_1} Foo),
    (λ (xs : list.{?M_2} Foo), @eq.{?M_3} (?M_4 xs) (Foo.unpack (Foo.pack xs)) xs) a_1 →
    (λ (xs : list.{?M_2} Foo), @eq.{?M_3} (?M_4 xs) (Foo.unpack (Foo.pack xs)) xs) (@list.cons.{?M_1} Foo a a_1)
-/
