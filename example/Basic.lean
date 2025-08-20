example (n : Nat) : n + 0 = n := by


example (h Q : Prop) : h ∧ Q <-> h := by
  have : h ∧ Q <-> h := by
