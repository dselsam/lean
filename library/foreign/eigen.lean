import foreign.float

namespace Eigen

def TShape : Type := list ℕ

constant T : TShape → Type

namespace T

constant π : T []

def tsize : TShape → ℕ
| [] := 1
| (d::ds) := d * tsize ds

constant box (α : Float) : T []

constant const (α : T []) : Π (shape : TShape), T shape
constant lift₁ (f : T [] → T []) : Π {shape : TShape}, T shape → T shape
constant lift₂ (f : T [] → T [] → T []) : Π {shape : TShape}, T shape → T shape → T shape

constant zero (shape : TShape) : T shape
constant one (shape : TShape) : T shape

constant neg {shape : TShape} : T shape → T shape
constant inv {shape : TShape} : T shape → T shape
constant log {shape : TShape} : T shape → T shape
constant exp {shape : TShape} : T shape → T shape
constant sqrt {shape : TShape} : T shape → T shape
constant tanh {shape : TShape} : T shape → T shape

constant add {shape : TShape} : T shape → T shape → T shape
constant mul {shape : TShape} : T shape → T shape → T shape
constant sub {shape : TShape} : T shape → T shape → T shape
constant div {shape : TShape} : T shape → T shape → T shape

constant smul (α : T []) : Π {shape : TShape}, T shape → T shape

constant sum : Π {shape : TShape}, T shape → T []
constant prod : Π {shape : TShape}, T shape → T []

constant get_row {m n : ℕ} (M : T [m, n]) (ridx : fin m) : T [n]
constant get_col {m n : ℕ} (M : T [m, n]) (cidx : fin n) : T [m]

constant gemv {m n : ℕ} (M : T [m, n]) (x : T [n]) : T [m]
constant gemm {m n p : ℕ} (M : T [m, n]) (N : T [n, p]) : T [m, p]

-- constant get_col_range {m n : ℕ} (M : T [m, n]) (cidx : fin n) (ncols_to_take : ℕ) : T [m, ncols_to_take]
-- constant dot {n : ℕ} (x y : T [n]) : T []
-- constant append_col {n p : ℕ} (N : T [n, p]) (x : T [n]) : T [n, p+1]

end T
end Eigen

namespace Test
open Eigen

noncomputable def t₁ : T [2, 2] := T.add (T.one _) (T.one _)
--vm_eval T.gemm t₁ t₁

end Test
