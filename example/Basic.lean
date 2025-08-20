example (n : Nat) : n + 0 = n := by
  have h1 : ¬ (n + 0 = n) := by sorry
  sorry


example (h Q : Prop) : h ∧ Q <-> h := by

  have : h ∧ Q <-> h := by
