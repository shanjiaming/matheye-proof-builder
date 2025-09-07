import Mathlib.Data.Nat.Basic
import Mathlib.Data.List.Basic

/-- Mixed tactics: induction + simp -/
theorem mixed_induction_simp (n : Nat) : 0 + n = n := by
  induction n with
  | zero => simp
  | succ k ih => simp [ih]

/-- Mixed tactics: cases + constructor -/
theorem mixed_cases_constructor (n : Nat) : n = 0 ∨ ∃ m, n = Nat.succ m := by
  cases n with
  | zero =>
    left
    rfl
  | succ m =>
    right
    exists m

/-- Mixed tactics: intro + apply -/
theorem mixed_intro_apply (P Q R : Prop) : (P → Q) → (Q → R) → (P → R) := by
  intros hpq hqr hp
  apply hqr
  exact (hpq hp)

/-- Mixed tactics: induction + rewrite -/
theorem mixed_induction_rewrite (n : Nat) : Nat.succ n = n + 1 := by
  induction n with
  | zero => rfl
  | succ k ih => rw [Nat.add_succ, ih]

/-- Mixed tactics: cases + have + exact -/
theorem mixed_cases_have (n : Nat) : ∃ m, n = m := by
  cases n with
  | zero =>
    have h : 0 = 0 := rfl
    exists 0
  | succ k =>
    exists Nat.succ k
