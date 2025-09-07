theorem tactic_combo_test (P Q : Prop) : P → Q → P :=
  by intro hp hq
     exact hp

theorem cases_test (n : Nat) : n = n :=
  by cases n with
  | zero => rfl
  | succ m => rfl

def simple_double (n : Nat) : Nat :=
  match n with
  | 0 => 0
  | Nat.succ m => Nat.succ (Nat.succ (simple_double m))

theorem double_zero : simple_double 0 = 0 :=
  by simp [simple_double]
