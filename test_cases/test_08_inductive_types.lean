import Mathlib.Data.Nat.Basic

/-- Simple inductive type -/
inductive Bool' : Type
  | true
  | false

/-- Inductive type with parameters -/
inductive Option' (α : Type) : Type
  | none
  | some (val : α)

/-- Inductive type with recursion -/
inductive Nat' : Type
  | zero
  | succ (n : Nat')

/-- Inductive type for expressions -/
inductive Expr : Type
  | const (n : Nat)
  | var (name : String)
  | add (left right : Expr)
  | mul (left right : Expr)

/-- Inductive type with indices -/
inductive MyVector (α : Type) : Nat → Type
  | nil : MyVector α 0
  | cons (head : α) (tail : MyVector α n) : MyVector α (Nat.succ n)

/-- Inductive proposition -/
inductive Even : Nat → Prop
  | even_zero : Even 0
  | even_succ : ∀ n, Even n → Even (n + 2)

/-- Inductive proposition with multiple constructors -/
inductive Prime : Nat → Prop
  | prime_2 : Prime 2
  | prime_3 : Prime 3
  | prime_odd : ∀ n, n > 1 → (∀ d, d > 1 → d < n → ¬ (d ∣ n)) → Prime n

/-- Inductive type for binary trees -/
inductive Tree (α : Type) : Type
  | empty
  | node (value : α) (left right : Tree α)

/-- Inductive type with dependent types -/
inductive MyFin : Nat → Type
  | fz : MyFin (Nat.succ n)
  | fs : MyFin n → MyFin (Nat.succ n)
