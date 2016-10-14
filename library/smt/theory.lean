-- Core
/-
Already in Lean:
Prop, true, false, and, or, not, xor, implies, eq, ite
Note: including 'ne' for convenience
Note: skipping 'distinct' for now
-/

-- Int
constants (Int : Type)
namespace Int
constants (zero one : Int)
          (neg abs : Int → Int)
          (add mul div sub mod : Int → Int → Int)
          (le lt : Int → Int → Prop)

noncomputable instance : has_zero Int := ⟨zero⟩
noncomputable instance : has_one Int := ⟨one⟩
noncomputable instance : has_add Int := ⟨add⟩
noncomputable instance : has_mul Int := ⟨mul⟩
noncomputable instance : has_lt Int := ⟨lt⟩
noncomputable instance : has_le Int := ⟨le⟩

end Int

-- Real
constants (Real : Type)
namespace Real
constants (zero one : Real)
          (add mul div sub : Real → Real → Real)
          (lt le : Real → Real → Prop)

noncomputable instance : has_zero Real := ⟨zero⟩
noncomputable instance : has_one Real := ⟨one⟩
noncomputable instance : has_add Real := ⟨add⟩
noncomputable instance : has_mul Real := ⟨mul⟩
noncomputable instance : has_lt Real := ⟨lt⟩
noncomputable instance : has_le Real := ⟨le⟩

end Real

constants (BitVec : ℕ → Type)
namespace BitVec

constants (zero one : Pi n, BitVec n)
          (add mul : Pi n, BitVec n → BitVec n → BitVec n)

noncomputable instance (n : nat) : has_zero (BitVec n) := ⟨zero n⟩
noncomputable instance (n : nat) : has_one (BitVec n) := ⟨one n⟩
noncomputable instance (n : nat) : has_add (BitVec n) := ⟨add n⟩
noncomputable instance (n : nat) : has_mul (BitVec n) := ⟨mul n⟩

end BitVec
