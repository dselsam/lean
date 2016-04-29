/-
What do you think about the following style for dealing with contexts?
Note that environments, in contrast to contexts, can actually be reflected,
since the environments really do map `name → option A` at the top-level.
In contrast, contexts only make sense inside lambdas.
-/
import algebra.group

constants (name : Type) (expr : Type) (list : Type → Type)
          (context : Type → Type) (context.lookup : Π {A : Type}, ℕ → context A → option A)

inductive monexp (A : Type) [A_mon : monoid A] :=
| atom : ℕ → monexp A
| ident : monexp A
| op : monexp A → monexp A → monexp A

namespace monexp

definition denote {A : Type} [monoid A] (ctx : context A) : monexp A → A
| (atom _ n) := option.rec_on (context.lookup n ctx) (@monoid.one A _) id
| (ident _) := (@monoid.one A _)
| (op e1 e2) := monoid.mul (denote e1) (denote e2)

constant flatten : Π {A : Type} [monoid A], monexp A → monexp A

theorem correct {A : Type} [monoid A] (ctx : context A) :
  ∀ (m₁ m₂ : monexp A),
     denote ctx (flatten m₁) = denote ctx (flatten m₂)
     → denote ctx m₁ = denote ctx m₂ := sorry

constant reify_monoid {A : Type} [monoid A] : expr → monexp A

end monexp
/-
a : A
b : A
c : A
------------
a * (b * (c * a)) = (a * b) * (c * a)

[tactic] reflect reify denote

a : A
b : A
c : A
let ctx : context A := λ n, match n with O => some a | 1 => some b | 2 => some c | none
------------
denote ctx (reify (quote (a * (b * (c * a)))))
=
denote ctx (reify (quote ((a * b) * (c * a))))

[tactic] apply correct

a : A
b : A
c : A
let ctx : context A := λ n, match n with O => some a | 1 => some b | 2 => some c | none
------------
denote ctx (flatten (reify (quote (a * (b * (c * a))))))
=
denote ctx (flatten (reify (quote ((a * b) * (c * a)))))

[tactic] compute

a : A
b : A
c : A
let ctx : context A := λ n, match n with O => some a | 1 => some b | 2 => some c | none
------------
a * (b * (c * a)) = a * (b * (c * a))

[tactic] reflexivity

(solved)
-/
