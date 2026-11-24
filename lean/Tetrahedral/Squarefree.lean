import Tetrahedral.Basic
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Nat.Factorization.Basic

namespace Tetrahedral

/-- Cancel square factors only at the level of prime-exponent parity. -/
theorem squarefree_parity_cancel {c m d r x : ℕ} (hd : Squarefree d)
    (hc : c ≠ 0) (hm : m ≠ 0) (hr : r ≠ 0) (hx : x ≠ 0)
    (h : c * m ^ 2 = d * r ^ 2 * x) : d ∣ c * x := by
  apply (Nat.factorization_le_iff_dvd hd.ne_zero (mul_ne_zero hc hx)).mp
  intro p
  have hb := hd.natFactorization_le_one p
  have he := congrArg (fun z : ℕ => z.factorization p) h
  simp only [Nat.factorization_mul hc (pow_ne_zero _ hm),
    Nat.factorization_mul (mul_ne_zero hd.ne_zero (pow_ne_zero _ hr)) hx,
    Nat.factorization_mul hd.ne_zero (pow_ne_zero _ hr),
    Nat.factorization_pow, Finsupp.add_apply, Finsupp.smul_apply,
    smul_eq_mul] at he
  simp only [Nat.factorization_mul hc hx, Finsupp.add_apply]
  omega

theorem squarefree_part_dvd_66 {n m d r : ℕ} (h : Solution n m)
    (hd : Squarefree d) (hr : n + 3 = d * r ^ 2) : d ∣ 66 := by
  have hm : m ≠ 0 := by intro hm; subst m; unfold Solution at h; omega
  have hr0 : r ≠ 0 := by intro hr0; simp [hr0] at hr
  have he : 6 * m ^ 2 = d * r ^ 2 * (n ^ 2 + 2) := by
    rw [← hr]; exact solution_shift.mp h
  have hv := squarefree_parity_cancel hd (by decide) hm hr0 (by omega) he
  have h₁ : (d : ℤ) ∣ (n : ℤ) + 3 := by exact_mod_cast (hr ▸ dvd_mul_right d (r ^ 2))
  have h₂ : (d : ℤ) ∣ 6 * ((n : ℤ) ^ 2 + 2) := by exact_mod_cast hv
  have hc := dvd_sub h₂ (dvd_mul_of_dvd_right h₁ (6 * ((n : ℤ) - 3)))
  have hf : (d : ℤ) ∣ 66 := by convert hc using 1; ring
  exact_mod_cast hf

theorem squarefree_reduction {n m : ℕ} (h : Solution n m) :
    ∃ d r : ℕ, 0 < d ∧ 0 < r ∧ Squarefree d ∧ d ∣ 66 ∧ n + 3 = d * r ^ 2 := by
  obtain ⟨d, r, hd, hr, he, hs⟩ := Nat.sq_mul_squarefree_of_pos (show 0 < n + 3 by omega)
  have he' : n + 3 = d * r ^ 2 := by nlinarith [he]
  exact ⟨d, r, hd, hr, hs, squarefree_part_dvd_66 h hs he', he'⟩

theorem divisors_66 {d : ℕ} (h : d ∣ 66) :
    d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 6 ∨ d = 11 ∨ d = 22 ∨ d = 33 ∨ d = 66 := by
  have hb : d ≤ 66 := Nat.le_of_dvd (by decide) h
  interval_cases d <;> norm_num at *

end Tetrahedral

