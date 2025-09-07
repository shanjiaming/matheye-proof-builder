import Mathlib.Data.Nat.Basic

/-- Basic arithmetic properties -/
theorem mul_zero (n : Nat) : n * 0 = 0 := by
  induction n with
  | zero => rfl
  | succ k ih => rw [Nat.succ_mul, ih, Nat.add_zero]

/-- Properties of successor -/
theorem succ_inj (n m : Nat) : Nat.succ n = Nat.succ m → n = m := by
  intro h
  injection h

/-- Simple addition property -/
theorem add_zero_right (n : Nat) : n + 0 = n := by
  rfl

/-- Simple properties -/
theorem add_succ_eq_succ_add (n m : Nat) : Nat.succ n + m = n + Nat.succ m := by
  rw [Nat.succ_add, Nat.add_succ]

/-- Properties of lists -/
theorem list_length_ge_zero (α : Type) (xs : List α) : xs.length ≥ 0 := by
  cases xs with
  | nil => simp
  | cons y ys => simp [Nat.zero_le]

/-- Properties of options -/
theorem option_some_eq_some (α : Type) (x y : α) : some x = some y ↔ x = y := by
  constructor
  · intro h
    injection h
  · intro h
    rw [h]
