-- Basic theorem about natural numbers
theorem add_zero (n : Nat) : n + 0 = n := by
  induction n with
  | zero => rfl
  | succ k ih => rw [Nat.add_succ, ih]

-- Double of a number  
theorem double_eq_add_self (n : Nat) : 2 * n = n + n := by
  rw [Nat.two_mul]
