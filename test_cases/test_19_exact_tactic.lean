import Mathlib.Data.Nat.Basic

/-- Using exact for direct proof -/
theorem exact_refl (n : Nat) : n = n := by
  exact rfl

/-- Exact with hypothesis -/
theorem exact_hyp (P : Prop) : P → P := by
  intro h
  exact h

/-- Exact with function application -/
theorem exact_function (n : Nat) : n + 0 = n := by
  exact Nat.add_zero n

/-- Exact with multiple hypotheses -/
theorem exact_multiple (P Q : Prop) : P → Q → P ∧ Q := by
  intros hp hq
  exact ⟨hp, hq⟩

/-- Exact with equality -/
theorem exact_eq (n m : Nat) : n = m → m = n := by
  intro h
  exact Eq.symm h

/-- Exact with constructors -/
inductive MyBool
  | mytrue
  | myfalse

def exact_constructor : MyBool := MyBool.mytrue
