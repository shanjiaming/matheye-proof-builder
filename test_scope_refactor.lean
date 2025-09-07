-- Test case for scope identification refactor
theorem test_match_scope (n : Nat) : n = n := by
  match n with
  | 0 => 
    -- This should be detected as match alternative
    rfl
  | Nat.succ m =>
    -- This should also be detected as match alternative  
    rfl

theorem test_simple_by (x : Nat) : x = x := by
  -- This should be detected as simple by-block
  rfl

theorem test_nested_match (n m : Nat) : n = n := by
  match n with
  | 0 =>
    match m with 
    | 0 => rfl
    | Nat.succ k => rfl
  | Nat.succ j => rfl