theorem simple_tactic_test (P Q R : Prop) : (P → Q) → (Q → R) → (P → R) :=
  by intro hpq hqr hp
     have hq : Q := hpq hp
     exact hqr hq
