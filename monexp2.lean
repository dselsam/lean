-- New approach: return `expr` to the C++ and avoid the need for contexts entirely.
import algebra.group

constants (name : Type) (expr : Type) (list : Type → Type)
          (quote : Π {A : Type}, A → expr)
          (app2 : expr → expr → expr → expr)
          (app3 : expr → expr → expr → expr → expr)
          (app4 : expr → expr → expr → expr → expr → expr)

inductive monexp (A : Type) [A_mon : monoid A] :=
| atom {} : expr → monexp A
| ident {} : monexp A
| op : monexp A → monexp A → monexp A

namespace monexp

definition denote {A : Type} [monoid A] : monexp A → expr
| ident := quote monoid.one
| (atom e) := e
| (op e1 e2) := app4 (quote monoid.mul) _ _ (denote e1) (denote e2)

constant flatten : Π {A : Type} [monoid A], monexp A → monexp A

theorem correct {A : Type} [monoid A] :
  ∀ (m₁ m₂ : monexp A), denote (flatten m₁) = denote (flatten m₂) → denote m₁ = denote m₂ := sorry

definition reify {A : Type} [monoid A] : expr → monexp A
| (loc n) := atom (loc n)
| (const "monoid.one") := ident
| (app4 (app2 (const "monoid.mul") _ _) _ _ e1 e2) := op (reify e1) (reify e2)

definition reify_eq {A : Type} [monoid A] : expr → expr
| (app3 (const "eq") _ e1 e2) := app3 (const "eq") _ (quote (denote (reify e1))) (quote (denote (reify e2)))
| _ := const "false"

-- Tactic types
constant change : expr → tactic unit
constant get_target : tactic expr
constant apply : expr → tactic unit
constant compute : tactic unit
constant solve_by : tactic unit → tactic unit

tactic definition dec_monoid : tactic unit := do
  target <- get_target
  change (reify_eq target)
  apply correct
  solve_by compute

end monexp
