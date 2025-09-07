def test_let (n : Nat) : Nat :=
  let a := n + 1
  let b := a * 2  
  let c := b - n
  c