inductive th | t0, t1, t2
open th
/-
mutual_inductive foo, bar, rig (A : Type)
with foo : nat → nat → Type
| mk : bar t0 → rig → foo 2 2
with bar : th → Type
| mk : rig → foo 1 1 → bar t2
with rig : Type
| mk : foo 0 0 → bar t1 → rig-/

infixr `⊎`:50 := sum

definition I₁ := Σ (n₁ n₂ : nat), bool
definition I₂ := Σ (t : th), unit
definition I₃ := unit

definition mk₁ (n₁ n₂ : nat) (b : bool) : I₁ := sigma.mk n₁ (sigma.mk n₂ b)
definition mk₂ (t : th)                 : I₂ := sigma.mk t unit.star
definition mk₃                          : I₃ := unit.star

definition I := I₁ ⊎ (I₂ ⊎ I₃)

definition put₁ (p : I₁) : I := sum.inl p
definition put₂ (p : I₂) : I := sum.inr (sum.inl p)
definition put₃ (p : I₃) : I := sum.inr (sum.inr p)

inductive FBR (A : Type) : I → Type
| fmk : FBR (put₂ $ mk₂ t0)     → FBR (put₃ $ mk₃)        → FBR (put₁ $ mk₁ 2 2 tt)
| bmk : FBR (put₃ $ mk₃)        → FBR (put₁ $ mk₁ 1 1 tt) → FBR (put₂ $ mk₂ t2)
| rmk : FBR (put₁ $ mk₁ 0 0 tt) → FBR (put₂ $ mk₂ t1)     → FBR (put₃ $ mk₃)

definition foo (A : Type) (n₁ n₂ : nat) (b : bool) := FBR A (put₁ $ mk₁ n₁ n₂ b)
definition bar (A : Type) (t : th)                 := FBR A (put₂ $ mk₂ t)
definition rig_core (A : Type) (u : unit)          := FBR A (put₃ $ mk₃)
definition rig (A : Type)                          := FBR A (put₃ $ mk₃)

definition foo.mk (A : Type) := @FBR.fmk A
definition bar.mk (A : Type) := @FBR.bmk A
definition rig.mk (A : Type) := @FBR.rmk A

set_option pp.binder_types true
check @sum.cases_on
check @FBR.cases_on
check @sigma
check @sigma.cases_on

/-
sum.cases_on :
  Π {A : Type} {B : Type} {C : A⊎B → Type} (n : A⊎B),
    (Π (a : A), C (sum.inl a)) → (Π (a : B), C (sum.inr a)) → C n
FBR.cases_on :
  Π {A : Type} {C : Π (a : I), FBR A a → Type} {a : I} (n : FBR A a),
    (Π (a : FBR A (put₂ (mk₂ t0))) (a_1 : FBR A (put₃ mk₃)), C (put₁ (mk₁ 2 2)) (FBR.fmk a a_1)) →
    (Π (a : FBR A (put₃ mk₃)) (a_1 : FBR A (put₁ (mk₁ 1 1))), C (put₂ (mk₂ t2)) (FBR.bmk a a_1)) →
    (Π (a : FBR A (put₁ (mk₁ 0 0))) (a_1 : FBR A (put₂ (mk₂ t1))), C (put₃ mk₃) (FBR.rmk a a_1)) → C a n
sigma : Π {A : Type}, (A → Type) → Type
sigma.cases_on :
  Π {A : Type} {B : A → Type} {C : sigma B → Type} (n : sigma B),
    (Π (pr1 : A) (pr2 : B pr1), C (sigma.mk pr1 pr2)) → C n
-/

definition foo.cases_on {A : Type}
                        {C : Π {n₁ n₂ : nat} {b : bool}, foo A n₁ n₂ b → Type}
                        {n₁ n₂ : nat} {b : bool}
                        (f : foo A n₁ n₂ b)
                        (mp : Π (b : bar A t0) (r : rig A), C (foo.mk A b r)) : C f :=
@FBR.cases_on A
              (λ (i : I),
                @sum.cases_on I₁
                              (I₂ ⊎ I₃)
                              (λ (i : I₁ ⊎ (I₂ ⊎ I₃)), FBR A i -> Type)
                              i
                              (λ (i₁ : sigma (λ (n₁ : nat), sigma (λ (n₂ : nat), bool))),
                                @sigma.cases_on nat
                                                (λ (n₁ : nat), sigma (λ (n₂:nat), bool))
                                                (λ (i₁ : sigma (λ (n₁ : nat), sigma (λ (n₂ : nat), bool))), FBR A (sum.inl i₁) -> Type)
                                                i₁
                                                (λ (n₁ : nat) (q₂ : sigma (λ (n₂ : nat), bool)),
                                                  @sigma.cases_on nat
                                                                  (λ (n₂ : nat), bool)
                                                                  (λ (q₃ : sigma (λ (n₂ : nat), bool)),
                                                                     FBR A (sum.inl (sigma.mk n₁ q₃)) -> Type)
                                                                  q₂
                                                                  (λ (n₂ : nat) (b : bool)
                                                                     (x : FBR A (put₁ $ mk₁ n₁ n₂ b)), C x)))
                                (λ (i_ignore : I₂ ⊎ I₃) (x_ignore : FBR A (sum.inr i_ignore)),
                                  poly_unit))
              (put₁ (mk₁ n₁ n₂ b))
              f
              mp
              (λ (r : rig A) (f : foo A 1 1 tt), poly_unit.star)
              (λ (f : foo A 0 0 tt) (b : bar A t1), poly_unit.star)


check @foo.cases_on
