import Mathlib.Data.Nat.Basic

/-- Simple structure -/
structure Point where
  x : Nat
  y : Nat

/-- Structure with type parameters -/
structure Pair (α β : Type) where
  first : α
  second : β

/-- Structure with inheritance -/
structure Point3D extends Point where
  z : Nat

/-- Simple structure with properties -/
structure SimpleMonoid (α : Type) where
  mul : α → α → α
  one : α

/-- Simple structure with default values -/
structure SimpleConfig where
  timeout : Nat := 30
  retries : Nat := 3
  debug : Bool := false

/-- Simple structure with computed fields -/
structure SimpleRectangle where
  width : Nat
  height : Nat
  area : Nat := width * height

/-- Simple structure with proofs -/
structure SimpleIsEven (n : Nat) where
  witness : ∃ k, n = 2 * k

/-- Simple structure with functions -/
structure SimpleEither (α β : Type) where
  mkLeft : α → SimpleEither α β
  mkRight : β → SimpleEither α β
