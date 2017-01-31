import foreign.float

namespace eigen

def tshape : Type := list ℕ

def tsize : tshape → ℕ
| [] := 1
| (d::ds) := d * tsize ds

meta constant T : tshape → Type

meta constant box (α : float) : T []

meta def π : T [] := box float.pi

meta constant const (α : T []) : Π (shape : tshape), T shape
--meta constant lift₁ (f : T [] → T []) : Π {shape : tshape}, T shape → T shape
--meta constant lift₂ (f : T [] → T [] → T []) : Π {shape : tshape}, T shape → T shape → T shape

meta constant zero (shape : tshape) : T shape
meta constant one (shape : tshape) : T shape

meta constants neg inv log exp sqrt tanh : Π {shape : tshape}, T shape → T shape
meta constants add mul sub div : Π {shape : tshape}, T shape → T shape → T shape

meta constant smul (α : T []) : Π {shape : tshape}, T shape → T shape

meta constants sum prod : Π {shape : tshape}, T shape → T []

meta constant get_row {m n : ℕ} (M : T [m, n]) (ridx : fin m) : T [n]
meta constant get_col {m n : ℕ} (M : T [m, n]) (cidx : fin n) : T [m]

meta constant gemv {m n : ℕ} (M : T [m, n]) (x : T [n]) : T [m]
meta constant gemm {m n p : ℕ} (M : T [m, n]) (N : T [n, p]) : T [m, p]

meta constant get_col_range {m n : ℕ} (M : T [m, n]) (cidx : fin n) (ncols_to_take : ℕ) : T [m, ncols_to_take]

end T
end eigen

namespace Test
open eigen

meta def t₁ : T [2, 2] := T.add (T.one _) (T.one _)

vm_eval t₁
vm_eval T.gemm t₁ t₁

end Test
