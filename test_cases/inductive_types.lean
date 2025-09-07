inductive MyNat where
  | zero : MyNat
  | succ : MyNat → MyNat

def add : MyNat → MyNat → MyNat
  | MyNat.zero, n => n
  | MyNat.succ m, n => MyNat.succ (add m n)

theorem add_zero (n : MyNat) : add n MyNat.zero = n :=
  by cases n with
  | zero => rfl
  | succ m => simp [add, add_zero m]

theorem add_succ (m n : MyNat) : add m (MyNat.succ n) = MyNat.succ (add m n) :=
  by cases m with
  | zero => rfl
  | succ k => simp [add, add_succ k n]
