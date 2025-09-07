import Mathlib.Data.Nat.Basic

/-- Simple induction on natural numbers -/
theorem nat_induction_simple (n : Nat) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ k ih => rw [Nat.add_succ, ih]

/-- Induction with successor -/
theorem succ_add_one (n : Nat) : Nat.succ n = n + 1 := by
  induction n with
  | zero => rfl
  | succ k ih => rw [Nat.add_succ, ih]

/-- Induction on lists -/
theorem list_length_cons (α : Type) (x : α) (xs : List α) : (x :: xs).length = xs.length + 1 := by
  induction xs with
  | nil => simp
  | cons y ys ih => simp [ih]

/-- Every natural number has a successor -/
theorem succ_positive (n : Nat) : n < Nat.succ n := by
  induction n with
  | zero => simp
  | succ k ih => simp [ih, Nat.lt_succ_self]
