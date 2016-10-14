import smt.tactic smt.constants

namespace Examples
open tactic
open tactic.smt

-- Prop logic
--example (P : Prop) : P → P → false := by Z3 -- should FAIL
example (P : Prop) : P → ¬ P → false := by Z3
example (P Q : Prop) : P ∧ Q → ¬ P → (¬ P ∨ ¬ Q) → false := by Z3
example (P Q : Prop) : P ∧ Q → ¬ P → (¬ P → ¬ Q) → false := by Z3

-- EUF
--example (X Y : Type) (f g : X → X → Y) (x1 x1B x2 x2B : X) : x1 ≠ x1B → x2 ≠ x2B → f x1 x2 = f x1B x2B → false := by Z3 -- should FAIL
example (X Y : Type) (f g : X → X → Y) (x1 x1B x2 x2B : X) : x1 = x1B → x2 = x2B → f x1 x2 ≠ f x1B x2B → false := by Z3

-- Ints
--example (z1 z2 z3 : Int) : z1 = z2 + z3 → z2 = z1 + z3 → z3 = z1 + z2 → z1 = 0 → false := by Z3 -- should FAIL
example (z1 z2 z3 : Int) : z1 = z2 + z3 → z2 = z1 + z3 → z3 = z1 + z2 → z1 > 0 → false := by Z3
example : (∀ (n : Int), ∃ (m : Int), n * m = 1) → false := by Z3
example : (7 : Int) * 5 > 40 → false := by Z3
example : (∃ (n : Int), (7 : Int) * n = 1) → false := by Z3

-- Reals
--example (z1 z2 z3 : Real) : z1 = z2 + z3 → z2 = z1 + z3 → z3 = z1 + z2 → z1 = 0 → false := by Z3 -- should FAIL
-- example : (∀ (n : Real), n ≠ 0 → ∃ (m : Real), n * m = 1) → false := by Z3 -- should FAIL/TIMEOUT
example (z1 z2 z3 : Real) : z1 = z2 + z3 → z2 = z1 + z3 → z3 = z1 + z2 → z1 > 0 → false := by Z3
example : (7 : Real) * 5 > 40 → false := by Z3
example : (∃ (n : Real), n > 10 ∧ (7 : Real) * n = 1) → false := by Z3

-- Quantifiers
--example (X : Type) (x : X) (f g : X → X) : (∀ (x : X), f x = g x) → (∃ (x : X), f x = g x) → false := by Z3 -- should FAIL
example (X : Type) (x1 x2 : X) (f : X → X) : (∀ (x1 x2 : X), f x1 = f x2 → x1 = x2) →  f x1 = f x2 → x1 ≠ x2 → false := by Z3
example (X : Type) (x : X) (f g : X → X) : (∃ (x : X), f x = g x) → (∀ (x : X), f x ≠ g x) → false := by Z3
example (X : Type) (x1 x2 : X) : x1 ≠ x2 → (¬ ∃ (x1 x2 : X), x1 ≠ x2) → false := by Z3

-- BitVectors
example (x y z : BitVec 16) : x + x = y → y + y = z → x + x + x + x ≠ z → false := by Z3
example (x y z : BitVec 16) : 2 * x = y → 3 * y = z → 6 * x ≠ z → false := by Z3
example : (¬ ∃ (x : BitVec 16), x ≠ 0 ∧ 2 * x = 0) → false := by Z3

-- Let
-- (a) let as a hypothesis (define-fun)
example (X : Type) (x : X) (f : X → X) : let y : X := f x in y ≠ f x → false := by Z3
-- (b) let in a term (let ((...)) ...)
-- TODO(dhs): uncomment and test once compiler is fixed
-- example (X : Type) (x : X) (f : X → X) : (let y : X := f x in y ≠ f x) → false := by Z3

-- Compound names
-- Note: cannot even form compound binders, so I can only trigger the compound-name bug programmatically
-- example (X.hello : Type) (x.hello : X) : x ≠ x → false := by Z3

-- Generalizing constants
namespace WithConstants
constants (Y : Type) (y : Y)

example (X : Type) (x : X) (f : X → Y) : f x = y → y ≠ f x → false := by Z3

-- This one is tricker, as generalizing a constant introduces a new constant
example : y ≠ y → false := by Z3


end WithConstants

end Examples
