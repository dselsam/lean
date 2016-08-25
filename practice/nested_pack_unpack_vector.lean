inductive vec₁ (A : Type) : nat -> Type
| nil₁ : vec₁ 0
| cons₁ : Pi (n : nat), A -> vec₁ n -> vec₁ (n+1)

inductive vec₂ (A : Type) : nat -> Type
| nil₂ : vec₂ 0
| cons₂ : Pi (n : nat), A -> vec₂ n -> vec₂ (n+1)

constants (f g h j : nat -> nat)

namespace X

inductive foo.{l} (A : Type.{l}) : ℕ -> Type.{max 1 l}
| mk : Pi (n : nat), vec₂ (vec₁ (foo (f n)) (g n)) (h n) -> foo (j n)

end X
mutual_inductive foo, fvec₁, fvec₂ (A : Type)
with foo : nat -> Type
| mk : Pi (n : nat), fvec₂ n (h n) -> foo (j n)
with fvec₁ : nat -> nat -> Type
| nil₁ : Pi (n1 : nat), fvec₁ n1 0
| cons₁ : Pi (n1 n2 : nat), foo (f n1) -> fvec₁ n1 n2 -> fvec₁ n1 (n2+1)
with fvec₂ : nat -> nat -> Type
| nil₂ : Pi (n : nat), fvec₂ n 0
| cons₂ : Pi (n1 n2 : nat), fvec₁ n1 (g n1) -> fvec₂ n1 n2 -> fvec₂ n1 (n2+1)

definition Foo (A : Type) : nat -> Type.{1} := @foo A
definition Fvec₁ : Pi (A : Type), nat -> nat -> Type.{1} := @fvec₁

definition vec₂_to_fvec₂ (A : Type) (n₁ : nat)
  : Pi (n₂ : nat), vec₂ (Fvec₁ A n₁ (g n₁)) n₂ -> fvec₂ A n₁ n₂ :=
@vec₂.rec (Fvec₁ A n₁ (g n₁))
             (λ (n₂ : nat) (v : vec₂ (Fvec₁ A n₁ (g n₁)) n₂), fvec₂ A n₁ n₂)
             (@fvec₂.nil₂ A n₁)
             (λ (n₂ : nat)
                (x : Fvec₁ A n₁ (g n₁))
                (vs : vec₂ (Fvec₁ A n₁ (g n₁)) n₂)
                (fvs : fvec₂ A n₁ n₂),
                  @fvec₂.cons₂ A n₁ n₂ x fvs)

definition Foo.mk
  : Pi (A : Type) (n : nat) (fvs : vec₂ (fvec₁ A n (g n)) (h n)), Foo A (j n) :=
    assume A n fvs, foo.mk n (vec₂_to_fvec₂ A n (h n) fvs)

definition Fvec₁.nil₁
  : Pi (A : Type) (n : nat), Fvec₁ A n 0 :=
    @fvec₁.nil₁

definition Fvec₁.cons₁
  : Pi (A : Type) (n1 n2 : nat), Foo A (f n1) -> Fvec₁ A n1 n2 -> Fvec₁ A n1 (n2+1) :=
    @fvec₁.cons₁

definition FOO : Pi (A : Type), nat -> Type.{1} := @Foo

definition vec₁_to_fvec₁ (A : Type) (n₁ : nat)
  : Π (n₂ : nat), vec₁ (FOO A (f n₁)) n₂ -> Fvec₁ A n₁ n₂ :=
@vec₁.rec   (FOO A (f n₁))
            (λ (n₂ : nat) (v : vec₁ (FOO A (f n₁)) n₂), Fvec₁ A n₁ n₂)
            (@Fvec₁.nil₁ A n₁)
            (λ (n₂ : nat)
               (x : FOO A (f n₁))
               (vs : vec₁ (FOO A (f n₁)) n₂)
               (fvs : Fvec₁ A n₁ n₂),
                 @Fvec₁.cons₁ A n₁ n₂ x fvs)
set_option pp.all true
definition fvec₁_to_vec₁ (A : Type)
  : Π (n₁ : nat) (n₂ : nat), Fvec₁ A n₁ n₂ -> vec₁ (FOO A (f n₁)) n₂ :=
@fvec₁.rec  A
            (λ (n₁ : nat) (n₂ : nat) (v : Fvec₁ A n₁ n₂), vec₁ (FOO A (f n₁)) n₂)
            (λ (n₁ : nat), @vec₁.nil₁ (FOO A (f n₁)))
            (λ (n₁ : nat)
               (n₂ : nat)
               (x : FOO A (f n₁))
               (vs : Fvec₁ A n₁ n₂)
               (fvs : vec₁ (FOO A (f n₁)) n₂),
                 @vec₁.cons₁ (FOO A (f n₁)) n₂ x fvs)

namespace X
universe l
constant (A : Type.{l})
constant (n₁ : nat)
check vec₁.{1} (FOO A n₁) n₁

end X
print fvec₁_to_vec₁
-- eq.rec : Π {A : Type} {a : A} {C : A → Type}, C a → (Π {a_1 : A}, a = a_1 → C a_1)
set_option pp.binder_types true
definition vec₁_to_fvec₁_and_back (A : Type) :
  ∀ (n₁ : nat) (n₂ : nat) (xs : vec₁ (FOO A (f n₁)) n₂),
    fvec₁_to_vec₁ A n₁ n₂ (vec₁_to_fvec₁ A n₁ n₂ xs) = xs :=
assume (n₁ : nat),
@vec₁.rec (FOO A (f n₁))
          (λ (n₂ : nat) (xs : vec₁ (FOO A (f n₁)) n₂), fvec₁_to_vec₁ A n₁ n₂ (vec₁_to_fvec₁ A n₁ n₂ xs) = xs)
          rfl
          (λ (n₂ : nat)
             (x : FOO A (f n₁))
             (xs : vec₁ (FOO A (f n₁)) n₂)
             (H : fvec₁_to_vec₁ A n₁ n₂ (vec₁_to_fvec₁ A n₁ n₂ xs) = xs),
               @eq.rec (vec₁ (FOO A (f n₁)) n₂)
                       xs
                       (λ (zs : vec₁ (FOO A (f n₁)) n₂), vec₁.cons₁ n₂ x zs = vec₁.cons₁ n₂ x xs)
                       rfl
                       (@fvec₁_to_vec₁ A n₁ n₂ (vec₁_to_fvec₁ A n₁ n₂ xs))
                       (eq.symm H))

definition vec₂_vec₁_to_vec₂_fvec₁ (A : Type) (n₁ : nat) :
  Pi (n₂ : nat), vec₂ (vec₁ (foo A (f n₁)) (g n₁)) n₂ -> vec₂ (Fvec₁ A n₁ (g n₁)) n₂ :=
@vec₂.rec (vec₁ (foo A (f n₁)) (g n₁))
          (λ (n₂ : nat) (lv : vec₂ (vec₁ (foo A (f n₁)) (g n₁)) n₂), vec₂ (Fvec₁ A n₁ (g n₁)) n₂)
          (@vec₂.nil₂ (Fvec₁ A n₁ (g n₁)))
          (λ (n₂ : nat)
             (x : vec₁ (foo A (f n₁)) (g n₁))
             (lv : vec₂ (vec₁ (foo A (f n₁)) (g n₁)) n₂)
             (lv' : vec₂ (Fvec₁ A n₁ (g n₁)) n₂),
             (@vec₂.cons₂ (Fvec₁ A n₁ (g n₁)) n₂ (@vec₁_to_fvec₁ A n₁ (g n₁) x) lv'))

definition FOO.mk : Pi (A : Type) (n : nat), vec₂ (vec₁ (foo A (f n)) (g n)) (h n) -> FOO A (j n) :=
  assume A n lv,
  @Foo.mk A n (@vec₂_vec₁_to_vec₂_fvec₁ A n (h n) lv)

definition vec₂_vec₁_to_vec₂_fvec₁ (A : Type) (n₁ : nat) :
  Pi (n₂ : nat), vec₂ (vec₁ (foo A (f n₁)) (g n₁)) n₂ -> vec₂ (Fvec₁ A n₁ (g n₁)) n₂ :=
@vec₂.rec (vec₁ (foo A (f n₁)) (g n₁))
          (λ (n₂ : nat) (lv : vec₂ (vec₁ (foo A (f n₁)) (g n₁)) n₂), vec₂ (Fvec₁ A n₁ (g n₁)) n₂)
          (@vec₂.nil₂ (Fvec₁ A n₁ (g n₁)))
          (λ (n₂ : nat)
             (x : vec₁ (foo A (f n₁)) (g n₁))
             (lv : vec₂ (vec₁ (foo A (f n₁)) (g n₁)) n₂)
             (lv' : vec₂ (Fvec₁ A n₁ (g n₁)) n₂),
             (@vec₂.cons₂ (Fvec₁ A n₁ (g n₁)) n₂ (@vec₁_to_fvec₁ A n₁ (g n₁) x) lv'))
