import Mathlib.Data.Nat.Basic

/-- Using constructor for conjunction -/
theorem constructor_and (P Q : Prop) : P → Q → P ∧ Q := by
  intros hp hq
  constructor
  · exact hp
  · exact hq

/-- Constructor for disjunction -/
theorem constructor_or_left (P Q : Prop) : P → P ∨ Q := by
  intro hp
  constructor
  exact hp

/-- Constructor for existential -/
theorem constructor_exists (n : Nat) : ∃ m, n = m := by
  constructor
  rfl

/-- Constructor for custom inductive types -/
inductive MyColor
  | red
  | green
  | blue

def example_color : MyColor := MyColor.red

/-- Constructor with multiple cases -/
inductive SimpleTree (α : Type)
  | leaf (val : α)
  | node (left right : SimpleTree α)

def example_tree (x y z : Nat) : SimpleTree Nat :=
  SimpleTree.node (SimpleTree.leaf x) (SimpleTree.leaf y)
