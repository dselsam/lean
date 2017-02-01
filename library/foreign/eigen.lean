namespace certigrad
namespace approx

meta constant RNG : Type

namespace RNG
meta constant mk : ℕ → RNG
meta constant to_string : RNG → string
meta instance : has_to_string RNG := has_to_string.mk to_string
end RNG

def TShape : Type := list ℕ

meta constant T : TShape → Type

namespace T

meta constant to_string {shape : TShape} : T shape → string

meta instance {shape : TShape} : has_to_string (T shape) :=
has_to_string.mk to_string

meta constant const (α : T []) : Π (shape : TShape), T shape

meta constants zero one pi : Π (shape : TShape), T shape

meta constants neg inv log exp sqrt tanh : Π {shape : TShape}, T shape → T shape
meta constants add mul sub div : Π {shape : TShape}, T shape → T shape → T shape

meta constant smul (α : T []) : Π {shape : TShape}, T shape → T shape

meta constants sum prod : Π {shape : TShape}, T shape → T []

meta constant get_row {m n : ℕ} (M : T [m, n]) (ridx : fin m) : T [n]
meta constant get_col {m n : ℕ} (M : T [m, n]) (cidx : fin n) : T [m]

meta constant get_col_range {m n : ℕ} (M : T [m, n]) (cidx : fin n) (ncols_to_take : ℕ) : T [m, ncols_to_take]

meta constant gemv {m n : ℕ} (M : T [m, n]) (x : T [n]) : T [m]
meta constant gemm {m n p : ℕ} (M : T [m, n]) (N : T [n, p]) : T [m, p]

meta constant sample_gauss (shape : TShape) : state RNG (T shape)

end T

end approx
end certigrad
