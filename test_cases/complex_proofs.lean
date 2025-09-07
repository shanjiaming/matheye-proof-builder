def my_length {α : Type} : List α → Nat
  | [] => 0
  | _ :: xs => 1 + my_length xs

theorem length_zero_empty {α : Type} : my_length ([] : List α) = 0 :=
  by simp [my_length]

theorem length_singleton {α : Type} (x : α) : my_length [x] = 1 :=
  by simp [my_length]
