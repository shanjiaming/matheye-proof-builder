import Mathlib.Data.Nat.Basic

/-- Using have and exact for simple steps -/
theorem have_exact_simple (n : Nat) : n = n := by
  have h : n = n := rfl
  exact h

/-- Using have with natural numbers -/
theorem have_nat_example (n : Nat) : 0 + n = n := by
  have h : 0 + n = n := Nat.zero_add n
  exact h

/-- Using have with successor -/
theorem have_succ_example (n : Nat) : Nat.succ n = n + 1 := by
  have h : Nat.succ n = n + 1 := rfl
  exact h

/-- Using have with implication -/
theorem have_imp_example (P Q : Prop) : P → (Q → P) := by
  intro hp
  intro hq
  have h : P := hp
  exact h

/-- Using have with conjunction -/
theorem have_and_example (P Q : Prop) : P ∧ Q → P := by
  intro h
  have hp : P := h.left
  exact hp
