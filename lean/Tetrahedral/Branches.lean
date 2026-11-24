import Tetrahedral.IntegerSquareObstructions
import Tetrahedral.Squarefree
import Mathlib.Data.Rat.Lemmas

namespace Tetrahedral

private theorem sf66 : Squarefree (66 : ℕ) := by
  have h2 : Squarefree (2 : ℕ) := (by decide : Nat.Prime 2).squarefree
  have h3 : Squarefree (3 : ℕ) := (by decide : Nat.Prime 3).squarefree
  have h11 : Squarefree (11 : ℕ) := (by decide : Nat.Prime 11).squarefree
  rw [show (66 : ℕ) = 2 * (3 * 11) by norm_num, Nat.squarefree_mul_iff, Nat.squarefree_mul_iff]
  norm_num [h2, h3, h11]

theorem isSquare_cancel_sq {r x : ℕ} (hr : r ≠ 0)
    (h : IsSquare (r ^ 2 * x)) : IsSquare x := by
  apply Rat.isSquare_natCast_iff.mp
  obtain ⟨z, hz⟩ := h
  have he : (r : ℚ) ^ 2 * x = (z : ℚ) * z := by exact_mod_cast hz
  have hr' : (r : ℚ) ≠ 0 := by exact_mod_cast hr
  refine ⟨(z : ℚ) / r, ?_⟩
  field_simp
  nlinarith [he]

theorem squarefree_extract {e x : ℕ} (he : Squarefree e)
    (h : IsSquare (e * x)) : ∃ y : ℕ, x = e * y ^ 2 := by
  obtain ⟨z, hz⟩ := he.dvd_of_isSquare_mul h
  have hsq : IsSquare (e ^ 2 * z) := by convert h using 1 <;> nlinarith [hz]
  obtain ⟨y, hy⟩ := isSquare_cancel_sq he.ne_zero hsq
  exact ⟨y, by nlinarith [hz, hy]⟩

theorem square_from_equation {c m d r x : ℕ} (hr : r ≠ 0)
    (h : c * m ^ 2 = d * r ^ 2 * x) : IsSquare (c * d * x) := by
  apply Rat.isSquare_natCast_iff.mp
  have he : (c : ℚ) * m ^ 2 = d * r ^ 2 * x := by exact_mod_cast h
  have hr' : (r : ℚ) ≠ 0 := by exact_mod_cast hr
  refine ⟨(c : ℚ) * m / r, ?_⟩
  push_cast
  field_simp
  nlinarith [he]

theorem second_factor {n m d r e k : ℕ} (h : Solution n m)
    (hr : n + 3 = d * r ^ 2) (he : Squarefree e) (hk : k ≠ 0)
    (hde : 6 * d = k ^ 2 * e) : ∃ y : ℕ, n ^ 2 + 2 = e * y ^ 2 := by
  have hr0 : r ≠ 0 := by intro hz; simp [hz] at hr
  have h' := solution_shift.mp h
  rw [hr] at h'
  have hs := square_from_equation hr0 h'
  rw [hde, mul_assoc] at hs
  exact squarefree_extract he (isSquare_cancel_sq hk hs)

theorem exclude_d6 {n m r : ℕ} (h : Solution n m) : n + 3 ≠ 6 * r ^ 2 := by
  intro hr
  obtain ⟨y, hy⟩ := second_factor (e := 1) (k := 6) h hr (sf66.squarefree_of_dvd (by norm_num)) (by decide) (by norm_num)
  exact IntegerParity.norm_minus_two_mod_four n y 1 (by decide) (by exact_mod_cast hy)

theorem exclude_d22 {n m r : ℕ} (h : Solution n m) : n + 3 ≠ 22 * r ^ 2 := by
  intro hr
  obtain ⟨y, hy⟩ := second_factor (e := 33) (k := 2) h hr (sf66.squarefree_of_dvd (by norm_num)) (by decide) (by norm_num)
  exact IntegerParity.norm_minus_two_mod_four n y 33 (by decide) (by exact_mod_cast hy)

theorem exclude_d33 {n m r : ℕ} (h : Solution n m) : n + 3 ≠ 33 * r ^ 2 := by
  intro hr
  obtain ⟨y, hy⟩ := second_factor (e := 22) (k := 3) h hr (sf66.squarefree_of_dvd (by norm_num)) (by decide) (by norm_num)
  have hr' : (n:ℤ)+3=33*(r:ℤ)^2 := by exact_mod_cast hr
  have hy' : (n:ℤ)^2+2=22*(y:ℤ)^2 := by exact_mod_cast hy
  have hd : (3:ℤ) ∣ n := ⟨11*(r:ℤ)^2-1,by linear_combination hr'⟩
  obtain ⟨k,hk⟩ := hd
  apply IntegerSquareObstructions.mod_three (y:ℤ)
  refine ⟨k*(n:ℤ)+1-7*(y:ℤ)^2,?_⟩
  linear_combination -hy'+(n:ℤ)*hk

/-- All remaining infinite branches. No unit-group completeness is assumed. -/
theorem five_branches {n m : ℕ} (h : Solution n m) :
    ∃ d r e y : ℕ,
      (d = 1 ∧ e = 6 ∨ d = 2 ∧ e = 3 ∨ d = 3 ∧ e = 2 ∨
       d = 11 ∧ e = 66 ∨ d = 66 ∧ e = 11) ∧
      n + 3 = d * r ^ 2 ∧ n ^ 2 + 2 = e * y ^ 2 := by
  obtain ⟨d, r, _, _, _, hd, hr⟩ := squarefree_reduction h
  rcases divisors_66 hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨y, hy⟩ := second_factor (e := 6) (k := 1) h hr (sf66.squarefree_of_dvd (by norm_num)) (by decide) (by norm_num)
    exact ⟨1, r, 6, y, by simp, hr, hy⟩
  · obtain ⟨y, hy⟩ := second_factor (e := 3) (k := 2) h hr (sf66.squarefree_of_dvd (by norm_num)) (by decide) (by norm_num)
    exact ⟨2, r, 3, y, by simp, hr, hy⟩
  · obtain ⟨y, hy⟩ := second_factor (e := 2) (k := 3) h hr (sf66.squarefree_of_dvd (by norm_num)) (by decide) (by norm_num)
    exact ⟨3, r, 2, y, by simp, hr, hy⟩
  · exact (exclude_d6 h hr).elim
  · obtain ⟨y, hy⟩ := second_factor (e := 66) (k := 1) h hr (sf66.squarefree_of_dvd (by norm_num)) (by decide) (by norm_num)
    exact ⟨11, r, 66, y, by simp, hr, hy⟩
  · exact (exclude_d22 h hr).elim
  · exact (exclude_d33 h hr).elim
  · obtain ⟨y, hy⟩ := second_factor (e := 11) (k := 6) h hr (sf66.squarefree_of_dvd (by norm_num)) (by decide) (by norm_num)
    exact ⟨66, r, 11, y, by simp, hr, hy⟩

theorem branch_pair_sound {n d r e y k : ℕ}
    (hr : n + 3 = d * r ^ 2) (hy : n ^ 2 + 2 = e * y ^ 2)
    (hde : d * e = 6 * k ^ 2) : Solution n (k * r * y) := by
  rw [solution_shift, hr, hy]
  calc
    6 * (k * r * y) ^ 2 = (6 * k ^ 2) * r ^ 2 * y ^ 2 := by ring
    _ = (d * r ^ 2) * (e * y ^ 2) := by rw [← hde]; ring

/-- An entirely elementary equivalence to five simultaneous Pell-type systems. -/
theorem solution_iff_five_branches (n : ℕ) : (∃ m, Solution n m) ↔
    ∃ d r e y : ℕ,
      (d = 1 ∧ e = 6 ∨ d = 2 ∧ e = 3 ∨ d = 3 ∧ e = 2 ∨
       d = 11 ∧ e = 66 ∨ d = 66 ∧ e = 11) ∧
      n + 3 = d * r ^ 2 ∧ n ^ 2 + 2 = e * y ^ 2 := by
  constructor
  · rintro ⟨m, hm⟩; exact five_branches hm
  · rintro ⟨d, r, e, y, hc, hr, hy⟩
    rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨_, branch_pair_sound (k := 1) hr hy (by norm_num)⟩
    · exact ⟨_, branch_pair_sound (k := 1) hr hy (by norm_num)⟩
    · exact ⟨_, branch_pair_sound (k := 1) hr hy (by norm_num)⟩
    · exact ⟨_, branch_pair_sound (k := 11) hr hy (by norm_num)⟩
    · exact ⟨_, branch_pair_sound (k := 11) hr hy (by norm_num)⟩

end Tetrahedral



