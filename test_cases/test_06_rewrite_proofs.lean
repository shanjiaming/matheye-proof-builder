import Mathlib.Data.Nat.Basic

/-- Simple rewrite with addition -/
theorem rewrite_add_zero (n : Nat) : n + 0 = n := by
  rw [Nat.add_zero]

/-- Rewrite with successor -/
theorem rewrite_succ (n : Nat) : Nat.succ n = n + 1 := by
  rw [Nat.succ_eq_add_one]

/-- Multiple rewrites -/
theorem rewrite_multiple (n m : Nat) : (n + m) + 0 = n + m := by
  rw [Nat.add_zero]

/-- Rewrite in hypothesis -/
theorem rewrite_hypothesis (n m : Nat) : n + m = m + n → m + n = n + m := by
  intro h
  rw [h]

/-- Rewrite with left arrow -/
theorem rewrite_left (n : Nat) : n + 0 = n := by
  rw [← Nat.add_zero n]

/-- Rewrite with commutativity -/
theorem rewrite_comm (n m : Nat) : n + m = m + n := by
  rw [Nat.add_comm]

/-- Rewrite in complex expression -/
theorem rewrite_complex (n m k : Nat) : n + (m + k) = (n + m) + k := by
  rw [Nat.add_assoc]

/-- Rewrite with pattern -/
theorem rewrite_pattern (n : Nat) : 2 * n = n + n := by
  rw [Nat.two_mul]

