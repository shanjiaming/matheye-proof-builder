import Mathlib.Data.Nat.Basic

/-- Using cases on natural numbers -/
theorem cases_on_nat (n : Nat) : n = 0 ∨ ∃ k, n = Nat.succ k := by
  cases n with
  | zero => left; rfl
  | succ k => right; exists k

/-- Using cases on option type -/
theorem cases_on_option (α : Type) (x : Option α) : x = none ∨ ∃ y, x = some y := by
  cases x with
  | none => left; rfl
  | some y => right; exists y

/-- Using cases with inductive types -/
inductive EvenOdd : Nat → Prop
  | even_zero : EvenOdd 0
  | even_succ : ∀ n, EvenOdd n → EvenOdd (n + 2)
  | odd_one : EvenOdd 1
  | odd_succ : ∀ n, EvenOdd n → EvenOdd (n + 2)

theorem cases_on_even_odd (n : Nat) (h : EvenOdd n) : n = 0 ∨ n = 1 ∨ ∃ m, n = m + 2 := by
  cases h with
  | even_zero => left; exact rfl
  | even_succ m hm => right; right; exists m
  | odd_one => right; left; exact rfl
  | odd_succ m hm => right; right; exists m
