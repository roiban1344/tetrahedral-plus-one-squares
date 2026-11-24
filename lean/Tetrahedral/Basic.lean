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

theorem solution_int {n m : ℕ} : Solution n m ↔
    6 * (m : ℤ) ^ 2 = ((n : ℤ) + 3) * ((n : ℤ) ^ 2 + 2) := by
  rw [solution_shift]
  exact_mod_cast (Iff.rfl :
    6 * m ^ 2 = (n + 3) * (n ^ 2 + 2) ↔ _)

theorem common_divisor_eleven (n d : ℤ)
    (h₁ : d ∣ n + 3) (h₂ : d ∣ n ^ 2 + 2) : d ∣ 11 := by
  have h := dvd_sub h₂ (dvd_mul_of_dvd_right h₁ (n - 3))
  convert h using 1; ring

theorem root_unique {n m k : ℕ} (hm : Solution n m) (hk : Solution n k) : m = k := by
  unfold Solution at *
  nlinarith [sq_nonneg ((m : ℤ) - k)]

theorem triple_divisible_six (n : ℕ) : 6 ∣ n * (n + 1) * (n + 2) := by
  have : n % 6 < 6 := Nat.mod_lt _ (by decide)
  interval_cases h : n % 6 <;>
    simp [Nat.dvd_iff_mod_eq_zero, Nat.mul_mod, Nat.add_mod, h]

def tetrahedral (n : ℕ) : ℕ := n * (n + 1) * (n + 2) / 6

theorem original_equation {n m : ℕ} :
    tetrahedral n + 1 = m ^ 2 ↔ Solution n m := by
  have h := Nat.div_mul_cancel (triple_divisible_six n)
  unfold tetrahedral Solution
  omega

end Tetrahedral

