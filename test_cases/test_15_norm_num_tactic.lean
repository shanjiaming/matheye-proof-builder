import Mathlib.Tactic.NormNum

/-- Using norm_num for numerical evaluation -/
theorem norm_num_example : 2^3 = 8 := by
  norm_num

/-- Norm_num with fractions -/
theorem norm_num_fraction : 6 / 2 = 3 := by
  norm_num

/-- Norm_num with complex expressions -/
theorem norm_num_complex : 2 * 3 + 4 * 5 = 26 := by
  norm_num

/-- Norm_num with inequalities -/
theorem norm_num_ineq : 5 < 10 := by
  norm_num

/-- Norm_num with equality chains -/
theorem norm_num_chain : 2 + 2 = 4 ∧ 3 * 3 = 9 := by
  constructor
  · norm_num
  · norm_num





