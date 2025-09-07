import Mathlib.Data.Nat.Basic

/-- Using apply tactic -/
theorem apply_example (P Q : Prop) : (P → Q) → P → Q := by
  intro hpq hp
  apply hpq
  exact hp

/-- Apply with functions -/
theorem apply_function (n : Nat) : n ≥ 0 := by
  apply Nat.zero_le

/-- Apply with equality -/
theorem apply_eq (n m : Nat) : n = m → m = n := by
  intro h
  apply Eq.symm
  exact h

/-- Apply with multiple arguments -/
theorem apply_multiple (n m k : Nat) : n ≤ m → m ≤ k → n ≤ k := by
  intros h1 h2
  apply Nat.le_trans
  · exact h1
  · exact h2

/-- Apply with conjunction -/
theorem apply_and (P Q : Prop) : P ∧ Q → P := by
  intro h
  apply And.left
  exact h

/-- Apply with disjunction -/
theorem apply_or (P Q R : Prop) : P → P ∨ Q ∨ R := by
  intro hp
  apply Or.inl
  exact hp
