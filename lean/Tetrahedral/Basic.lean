import Mathlib.Tactic
import Mathlib.Data.Nat.Sqrt

/-! The equation is kept denominator-free until the final interface. -/
namespace Tetrahedral

def Solution (n m : ℕ) : Prop := 6 * m ^ 2 = n * (n + 1) * (n + 2) + 6

def Listed (n : ℕ) : Prop :=
  n = 0 ∨ n = 5 ∨ n = 8 ∨ n = 22 ∨ n = 24 ∨ n = 63 ∨ n = 13775

theorem listed_iff_witness (n : ℕ) : Listed n ↔
    (n = 0 ∧ Solution n 1) ∨ (n = 5 ∧ Solution n 6) ∨
    (n = 8 ∧ Solution n 11) ∨ (n = 22 ∧ Solution n 45) ∨
    (n = 24 ∧ Solution n 51) ∨ (n = 63 ∧ Solution n 209) ∨
    (n = 13775 ∧ Solution n 660099) := by
  unfold Listed Solution
  constructor
  · intro h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
  · tauto

theorem listed_has_solution {n : ℕ} (h : Listed n) : ∃ m, Solution n m := by
  rw [listed_iff_witness] at h
  rcases h with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩
  all_goals exact ⟨_, h⟩

theorem solution_shift {n m : ℕ} : Solution n m ↔
    6 * m ^ 2 = (n + 3) * (n ^ 2 + 2) := by
  unfold Solution
  have : n * (n + 1) * (n + 2) + 6 = (n + 3) * (n ^ 2 + 2) := by ring
  rw [this]

/-- The equation with the exact rational quotient, cleared of the denominator. -/
theorem original_equation {n m : ℕ} :
    (n * (n + 1) * (n + 2) / 6 + 1 : ℚ) = m ^ 2 ↔ Solution n m := by
  unfold Solution
  constructor
  · intro h
    have h6 : ((6 * m ^ 2 : ℕ) : ℚ) = ((n * (n + 1) * (n + 2) + 6 : ℕ) : ℚ) := by
      push_cast; linear_combination -6 * h
    exact_mod_cast h6
  · intro h
    have h6 : ((6 * m ^ 2 : ℕ) : ℚ) = ((n * (n + 1) * (n + 2) + 6 : ℕ) : ℚ) := by rw [h]
    push_cast at h6
    linear_combination -h6 / 6

end Tetrahedral
