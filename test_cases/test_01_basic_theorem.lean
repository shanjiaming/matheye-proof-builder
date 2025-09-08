import Mathlib.Data.Nat.Basic
import MathEye

macro "human_oracle" : tactic => `(tactic| sorry)

/-- Using have and exact for simple steps -/
theorem have_exact_simple (n : Nat) : n = n := by
  rfl
