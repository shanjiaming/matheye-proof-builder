import Mathlib.Data.Nat.Basic

/-- Simple recursive function definition -/
def factorial : Nat → Nat
  | 0 => 1
  | Nat.succ n => Nat.succ n * factorial n

/-- Recursive function with pattern matching -/
def fibonacci : Nat → Nat
  | 0 => 0
  | 1 => 1
  | Nat.succ (Nat.succ n) => fibonacci n + fibonacci (Nat.succ n)

/-- Non-recursive definition -/
def double (n : Nat) : Nat := 2 * n

/-- Definition with multiple arguments -/
def add_three (a b c : Nat) : Nat := a + b + c

/-- Recursive function on lists -/
def list_sum {α : Type} [Add α] [Zero α] : List α → α
  | [] => 0
  | x :: xs => x + list_sum xs

/-- Definition with let binding -/
def complicated_calc (n : Nat) : Nat :=
  let a := n + 1
  let b := a * 2
  let c := b - n
  c

/-- Simple recursive definition -/
def simple_length {α : Type} : List α → Nat
  | [] => 0
  | _ :: xs => 1 + simple_length xs

/-- Definition with type parameters -/
def identity {α : Type} (x : α) : α := x

/-- Recursive function with accumulator -/
def sum_range : Nat → Nat → Nat
  | 0, acc => acc
  | Nat.succ n, acc => sum_range n (acc + Nat.succ n)
