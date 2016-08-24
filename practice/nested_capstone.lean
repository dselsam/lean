inductive vector (A : Type) : nat -> Type
| vnil : vector 0
| vcons : Pi (n : nat), A -> vector n -> vector (n+1)

inductive lvector (A : Type) : nat -> Type
| lnil : lvector 0
| lcons : Pi (n : nat), A -> lvector n -> lvector (n+1)

constants (f g h j : nat -> nat)

-- Level 3
-- inductive foo (A : Type) : ℕ -> Type
-- | mk : Pi (n : nat), lvector (vector (foo (f n)) (g n)) (h n) -> foo (j n)

/- Level 2
mutual_inductive foo, fvector
with foo : ℕ -> Type
| mk : Pi (n : ℕ), lvector (fvector n (g n)) (h n) -> foo (j n)
with fvector : nat -> nat -> Type :=
| vnil  : Pi (n₁ : ℕ), fvector n₁ 0
| vcons : Pi (n₁ : ℕ) (n₂ : ℕ), foo (f n₁) -> fvector n₁ n₂ -> fvector n₁ (n₂+1)
-/

-- Level 1
mutual_inductive foo, fvector, flvector (A : Type)
with foo : nat -> Type
| mk : Pi (n : nat), flvector n (h n) -> foo (j n)
with fvector : nat -> nat -> Type
| vnil : Pi (n1 : nat), fvector n1 0
| vcons : Pi (n1 n2 : nat), foo (f n1) -> fvector n1 n2 -> fvector n1 (n2+1)
with flvector : nat -> nat -> Type
| lnil : Pi (n : nat), flvector n 0
| lcons : Pi (n1 n2 : nat), fvector n1 (g n1) -> flvector n1 n2 -> flvector n1 (n2+1)

-- Define layer 2
definition foo₂ : Pi (A : Type), nat -> Type.{1} := @foo
definition fvector₂ : Pi (A : Type), nat -> nat -> Type.{1} := @fvector

definition lvector_to_flvector (A : Type) (n₁ : nat) : Pi (n₂ : nat), lvector (fvector₂ A n₁ (g n₁)) n₂ -> flvector A n₁ n₂ :=
@lvector.rec (fvector₂ A n₁ (g n₁))
             (λ (n₂ : nat) (v : lvector (fvector₂ A n₁ (g n₁)) n₂), flvector A n₁ n₂)
             (@flvector.lnil A n₁)
             (λ (n₂ : nat)
                (x : fvector₂ A n₁ (g n₁))
                (vs : lvector (fvector₂ A n₁ (g n₁)) n₂)
                (fvs : flvector A n₁ n₂),
                  @flvector.lcons A n₁ n₂ x fvs)

definition foo₂.mk : Pi (A : Type) (n : nat) (fvs : lvector (fvector A n (g n)) (h n)), foo₂ A (j n) :=
  assume A n fvs, foo.mk n (lvector_to_flvector A n (h n) fvs)

definition fvector₂.vnil : Pi (A : Type) (n : nat), fvector₂ A n 0 := @fvector.vnil
definition fvector₂.vcons : Pi (A : Type) (n1 n2 : nat), foo₂ A (f n1) -> fvector₂ A n1 n2 -> fvector₂ A n1 (n2+1) := @fvector.vcons

-- Define layer 3
definition foo₃ : Pi (A : Type), nat -> Type.{1} := @foo₂

definition vector_to_fvector (A : Type) (n₁ : nat) : Π (n₂ : nat), vector (foo₃ A (f n₁)) n₂ -> fvector₂ A n₁ n₂ :=
@vector.rec (foo₃ A (f n₁))
            (λ (n₂ : nat) (v : vector (foo₃ A (f n₁)) n₂), fvector₂ A n₁ n₂)
            (@fvector₂.vnil A n₁)
            (λ (n₂ : nat)
               (x : foo₃ A (f n₁))
               (vs : vector (foo₃ A (f n₁)) n₂)
               (fvs : fvector₂ A n₁ n₂),
                 @fvector.vcons A n₁ n₂ x fvs)

definition lvector_vector_to_lvector_fvector (A : Type) (n₁ : nat) : Pi (n₂ : nat), lvector (vector (foo A (f n₁)) (g n₁)) n₂ -> lvector (fvector A n₁ (g n₁)) n₂ :=
@lvector.rec (vector (foo A (f n₁)) (g n₁))
             (λ (n₂ : nat) (lv : lvector _ n₂), lvector (fvector A n₁ (g n₁)) n₂)
             (@lvector.lnil _)
             (λ (n₂ : nat)
                (x : vector (foo A (f n₁)) (g n₁))
                (lv : lvector _ n₂)
                (lv' : lvector (fvector A n₁ (g n₁)) n₂),
                (@lvector.lcons _ n₂ (vector_to_fvector A n₁ (g n₁) x) lv'))

definition foo₃.mk : Pi (A : Type) (n : nat), lvector (vector (foo A (f n)) (g n)) (h n) -> foo₃ A (j n) :=
  assume A n lv,
  @foo₂.mk A n (@lvector_vector_to_lvector_fvector A n (h n) lv)
