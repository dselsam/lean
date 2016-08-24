infixr `⊎`:50 := sum

definition I₁ := unit
definition I₂ := nat

definition I := I₁ ⊎ I₂

definition put₁ (p : I₁) : I := sum.inl p
definition put₂ (p : I₂) : I := sum.inr p

inductive foo_vector : I → Type
| cons : Pi (n : nat), foo_vector (put₁ $ unit.star) -> foo_vector (put₂ n) -> foo_vector (put₂ (n+1))
| mk : foo_vector (put₁ $ unit.star)


definition foo := foo_vector (put₁ $ unit.star)

definition vector (n : nat) := foo_vector (put₂ $ n)
definition vector.cons (n : nat) (a : foo) (v : vector n) : vector (n+1) := foo_vector.cons n a v

set_option pp.binder_types true
/-
foo_vector.rec :
  Π {C : Π (a : I), foo_vector a → Type},

    (Π (n : ℕ) (a : foo_vector (put₁ ())) (a_1 : foo_vector (put₂ n)),
       C (put₁ ()) a → C (put₂ n) a_1 → C (put₂ (n + 1)) (foo_vector.cons n a a_1)) →

    C (put₁ ()) foo_vector.mk → (Π {a : I} (n : foo_vector a), C a n)
-/

definition vector.rec (C : Pi (n : nat), vector n -> Type)
                      (mp₁ : Pi (n : nat) (a : foo) (v : vector n), C n v -> C (n+1) (vector.cons n a v))
                      (n : nat)
                      (v : vector n) : C n v :=
@foo_vector.rec (λ (i : I), @sum.cases_on I₁
                                          I₂
                                          (λ (c : I₁ ⊎ I₂), @foo_vector c -> Type)
                                          i
                                          (λ (i : I₁) (x : @foo_vector (put₁ i)), poly_unit)
                                          (λ (n : I₂) (x : @foo_vector (put₂ n)), C n x))
                (λ (n : nat) (a : foo) (x : vector n) (ignore : poly_unit) (c : C n x), mp₁ n a x c)
                poly_unit.star
                (put₂ n)
                v

check @sigma nat (fun (n : nat), nat)
