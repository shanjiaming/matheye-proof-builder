import Mathlib.Data.Nat.Basic
import Mathlib.Data.List.Basic

/-- Using simp for arithmetic simplification -/
theorem zero_add_eq_zero (n : Nat) : 0 + n = n := by
  simp

/-- Using simp for equality -/
theorem succ_eq_add_one (n : Nat) : Nat.succ n = n + 1 := by
  simp

/-- Using simp for list operations -/
theorem list_length_cons (α : Type) (x : α) (xs : List α) : (x :: xs).length = xs.length + 1 := by
  simp [List.length_cons]

/-- Using simp for option operations -/
theorem option_some_getD (α : Type) (x y : α) : (some x).getD y = x := by
  simp
