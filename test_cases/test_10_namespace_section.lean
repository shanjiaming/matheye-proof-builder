import Mathlib.Data.Nat.Basic

/-- Simple definitions without namespace -/
def my_add (n m : Nat) : Nat := n + m

def my_mul (n m : Nat) : Nat := n * m

/-- Theorem using defined functions -/
theorem my_add_comm (n m : Nat) : my_add n m = my_add m n := by
  unfold my_add
  rw [Nat.add_comm]

/-- Simple list operations -/
def my_sum_list : List Nat → Nat
  | [] => 0
  | x :: xs => x + my_sum_list xs

/-- Theorem about sum -/
theorem sum_list_zero : my_sum_list [] = 0 := rfl

/-- Simple notation example -/
def double_nat (x : Nat) : Nat := 2 * x

/-- Private definition example -/
private def secret_helper (n : Nat) : Nat := n + 42

def public_using_private (n : Nat) : Nat := secret_helper n - 42

/-- Theorem using private definition -/
theorem public_correct (n : Nat) : public_using_private n = n := by
  unfold public_using_private secret_helper
  rw [Nat.add_sub_cancel]
