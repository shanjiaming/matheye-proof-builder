example (n : Nat) : n + 0 = n := by
  have h1 : ¬ (n + 0 = n) := by sorry

  sorry


example (P Q : Prop) : P ∧ Q → P := by
  intro h
  have h : ¬ (P) := by sorry
