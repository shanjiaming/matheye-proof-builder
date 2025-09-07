import Mathlib.Data.Nat.Basic

/-- Simple conjunction extraction -/
theorem conj_left (P Q : Prop) : P ∧ Q → P := by
  intro h
  exact h.left

/-- Simple implication application -/
theorem imp_app (P Q R : Prop) : (P → Q ∧ R) → (P → Q) := by
  intros h hp
  exact (h hp).left

/-- Universal quantification application -/
theorem forall_app (P : Nat → Prop) : (∀ n, P n) → P 0 := by
  intro h
  exact h 0

/-- Existential quantification -/
theorem exists_nat (n : Nat) : ∃ m, n = m := by
  exists n

/-- Cases with natural numbers -/
theorem nat_cases (n : Nat) : n = 0 ∨ ∃ m, n = Nat.succ m := by
  cases n with
  | zero => left; rfl
  | succ m => right; exists m
