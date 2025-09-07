import Mathlib.Data.Nat.Basic

/-- Simple inequalities -/
theorem simple_ineq (x y : Nat) : x ≤ x + y := by
  exact Nat.le_add_right x y

/-- Transitivity of less equal -/
theorem le_trans_simple (a b c : Nat) : a ≤ b → b ≤ c → a ≤ c := by
  intros h1 h2
  exact Nat.le_trans h1 h2

/-- Addition preserves inequalities -/
theorem add_le_add (x y z : Nat) : x ≤ y → x + z ≤ y + z := by
  intro h
  exact Nat.add_le_add_right h z

/-- Multiplication by two -/
theorem mul_two (n : Nat) : 2 * n = n + n := by
  simp [Nat.two_mul]

/-- Simple arithmetic -/
theorem add_comm_simple (a b : Nat) : a + b = b + a := by
  exact Nat.add_comm a b
