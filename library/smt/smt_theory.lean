-- Arith
constants (Int Real : Type)

instance : has_zero Int := sorry
instance : has_one Int := sorry
instance : has_add Int := sorry
instance : has_mul Int := sorry
instance : has_lt Int := sorry

instance : has_zero Real := sorry
instance : has_one Real := sorry
instance : has_add Real := sorry
instance : has_mul Real := sorry
instance : has_lt Real := sorry

-- Bit vectors

constants (BitVec : ℕ → Type)

instance (n : ℕ) : has_zero (BitVec n) := sorry
instance (n : ℕ) : has_one (BitVec n) := sorry
instance (n : ℕ) : has_add (BitVec n) := sorry
instance (n : ℕ) : has_mul (BitVec n) := sorry
