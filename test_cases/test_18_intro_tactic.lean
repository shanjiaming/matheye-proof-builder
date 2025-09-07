import Mathlib.Data.Nat.Basic

/-- Using intro for implication -/
theorem intro_imp (P Q : Prop) : P → Q → P ∧ Q := by
  intro hp
  intro hq
  constructor
  · exact hp
  · exact hq

/-- Intro with patterns -/
theorem intro_pattern (n : Nat) : ∀ m, n + m = m + n := by
  intro m
  rw [Nat.add_comm]

/-- Intro for universal quantification -/
theorem intro_forall : ∀ n : Nat, n ≥ 0 := by
  intro n
  exact Nat.zero_le n

/-- Intro with multiple variables -/
theorem intro_multiple (a b c : Nat) : a + b + c = a + b + c := by
  intros
  rfl

/-- Intro with simple case -/
theorem intro_simple : ∃ n, n = 0 := by
  exists 0

/-- Intro with variables -/
theorem intro_vars (x : Nat) : x = x := by
  rfl
