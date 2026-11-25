import Tetrahedral

/-! The statement of the classification, restated without any definition from the library,
and the axioms it depends on. CI compares the printed axioms with the standard three. -/

example (n : ℕ) :
    (∃ m : ℕ, (n * (n + 1) * (n + 2) / 6 + 1 : ℚ) = m ^ 2) ↔
      n = 0 ∨ n = 5 ∨ n = 8 ∨ n = 22 ∨ n = 24 ∨ n = 63 ∨ n = 13775 :=
  Tetrahedral.tetrahedral_add_one_eq_sq_iff n

#print axioms Tetrahedral.tetrahedral_add_one_eq_sq_iff
