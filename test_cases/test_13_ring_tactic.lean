import Mathlib.Data.Nat.Basic

/-- Simple arithmetic properties -/
theorem simple_mul_zero (x : Nat) : x * 0 = 0 := by
  simp

/-- Simple addition properties -/
theorem simple_add_zero (x : Nat) : x + 0 = x := by
  simp

/-- Simple successor properties -/
theorem simple_succ_eq_add_one (x : Nat) : Nat.succ x = x + 1 := by
  simp

/-- Simple multiplication properties -/
theorem simple_mul_one (x : Nat) : x * 1 = x := by
  simp

/-- Simple power properties -/
theorem simple_pow_zero (x : Nat) : x^0 = 1 := by
  simp
