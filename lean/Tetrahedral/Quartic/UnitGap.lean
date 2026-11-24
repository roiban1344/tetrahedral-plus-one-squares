import Mathlib.Tactic
import Mathlib.NumberTheory.Real.Irrational

/-!
# A gap for relative units, from one norm inequality

Let `u = A + B·s` be a relative unit with `B ≠ 0`, and `S = σ(u)`, `T = σ(τu) = 1/S` at the real
place where `s ↦ d > 0`, `d² = D₊`. At the other place of `F`, `A'² + D₋·B'² = 1` with `D₋ > 0`.
If `|B·B'| ≥ ν` (a norm from `F`, hence bounded below), then

  `(S − T)² = 4B²D₊ ≥ 4ν²·D₊·D₋ = 4ν²|N(D)|`  (`gap`).

So every nontrivial relative unit is far from `±1`. If `u` and `ρ·τu` were both nontrivial with
`1 ≤ |σ| < Λ`, the product of their `|σ|` would be `Λ`, and `Λ < 4ν²|N(D)|` gives a contradiction
(`contra`). This replaces the enumeration of a box of lattice points.
-/

namespace Tetrahedral.UnitGap

theorem gap (S T B B' A' d Dp Dm ν : ℝ) (hST : S-T=2*B*d) (hd : d^2=Dp) (hDm : 0 < Dm)
    (hconj : A'^2+Dm*B'^2=1) (hk : ν^2 ≤ (B*B')^2) :
    4*ν^2*Dp*Dm ≤ (S-T)^2 := by
  have h1 : Dm*B'^2 ≤ 1 := by nlinarith [sq_nonneg A']
  have h2 : Dm*ν^2 ≤ B^2 := by
    have : Dm*ν^2 ≤ Dm*(B*B')^2 := mul_le_mul_of_nonneg_left hk hDm.le
    have h3 : Dm*(B*B')^2=B^2*(Dm*B'^2) := by ring
    have h4 : B^2*(Dm*B'^2) ≤ B^2*1 := mul_le_mul_of_nonneg_left h1 (sq_nonneg B)
    linarith
  rw [hST]
  have : (2*B*d)^2=4*B^2*Dp := by rw [← hd]; ring
  rw [this]
  have hDp : 0 ≤ Dp := by rw [← hd]; positivity
  nlinarith [mul_le_mul_of_nonneg_right h2 hDp]

/-- `(S − 1/S)² = (|S| − 1/|S|)²`. -/
theorem sq_sub_inv_abs (S : ℝ) : (S-S⁻¹)^2=(|S|-|S|⁻¹)^2 := by
  rcases le_or_gt 0 S with h|h
  · rw [abs_of_nonneg h]
  · rw [abs_of_neg h,inv_neg]; ring

/-- `(S + 1/S)² = (|S| + 1/|S|)²`. -/
theorem sq_add_inv_abs (S : ℝ) : (S+S⁻¹)^2=(|S|+|S|⁻¹)^2 := by
  rcases le_or_gt 0 S with h|h
  · rw [abs_of_nonneg h]
  · rw [abs_of_neg h,inv_neg]; ring

theorem sq_le_of_one_le (a : ℝ) (ha : 1 ≤ a) : (a-a⁻¹)^2 ≤ a^2 := by
  have h0 : 0 < a⁻¹ := inv_pos.mpr (by linarith)
  have h1 : a⁻¹ ≤ 1 := inv_le_one_of_one_le₀ ha
  have : 0 ≤ a-a⁻¹ := by linarith
  nlinarith

theorem contra (a b L M : ℝ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : a*b=L) (hL : L < 4*M)
    (hga : 4*M ≤ (a-a⁻¹)^2) (hgb : 4*M ≤ (b-b⁻¹)^2) : False := by
  have ha2 := sq_le_of_one_le a ha
  have hb2 := sq_le_of_one_le b hb
  have hM : 0 < M := by nlinarith
  have hA : 4*M ≤ a^2 := le_trans hga ha2
  have hB : 4*M ≤ b^2 := le_trans hgb hb2
  have : (4*M)*(4*M) ≤ a^2*b^2 := mul_le_mul hA hB (by linarith) (sq_nonneg a)
  have hL2 : L^2=a^2*b^2 := by rw [← hab]; ring
  nlinarith

/-- The extra step for `d = 1`, where `Λ ≈ 37.57` exceeds `4·8`: both `|σ|` lie in
`[5.828, 6.452]`, which pins `((a+a⁻¹)/2)²` into `[8, 10.97]`. -/
theorem low_of_gap (z : ℝ) (hz : 1 ≤ z) (hg : 32 ≤ (z-z⁻¹)^2) : 5.828 ≤ z := by
  by_contra hlt; push_neg at hlt
  have hzpos : 0 < z := by linarith
  have hzi : z*z⁻¹=1 := mul_inv_cancel₀ hzpos.ne'
  have hi : 0.1715 < z⁻¹ := by
    have : (1:ℝ)/5.828 < z⁻¹ := by rw [one_div]; exact inv_strictAnti₀ hzpos hlt
    norm_num at this ⊢; linarith
  have h0 : 0 ≤ z-z⁻¹ := by
    have : z⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hz
    linarith
  have h1 : z-z⁻¹ < 5.6565 := by linarith
  have : (z-z⁻¹)^2 < 5.6565^2 := by
    have := mul_lt_mul'' h1 h1 h0 h0; nlinarith
  norm_num at this; linarith

theorem d1_bounds (a b L : ℝ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : a*b=L) (hL : L < 37.6)
    (hga : 32 ≤ (a-a⁻¹)^2) (hgb : 32 ≤ (b-b⁻¹)^2) :
    8 ≤ ((a+a⁻¹)/2)^2 ∧ ((a+a⁻¹)/2)^2 ≤ 10.97 := by
  have ha5 := low_of_gap a ha hga
  have hb5 := low_of_gap b hb hgb
  have hapos : 0 < a := by linarith
  have haup : a < 6.4517 := by nlinarith
  have hi0 : 0 < a⁻¹ := inv_pos.mpr hapos
  have hi1 : a⁻¹ ≤ 0.1716 := by
    have : a⁻¹ ≤ (5.828:ℝ)⁻¹ := inv_anti₀ (by norm_num) ha5
    norm_num at this ⊢; linarith
  have hs0 : 2.914 ≤ (a+a⁻¹)/2 := by linarith
  have hs1 : (a+a⁻¹)/2 ≤ 3.3117 := by linarith
  constructor <;> nlinarith

/-- `a²−e·b² ≠ 0` for `(a,b) ≠ 0` when `√e` is irrational. -/
theorem norm_ne_zero (e : ℕ) (he : Irrational (Real.sqrt (e:ℝ))) (a b : ℤ)
    (h : ¬(a=0 ∧ b=0)) : a^2-(e:ℤ)*b^2≠0 := by
  intro h0
  have hb : b≠0 := by
    rintro rfl
    apply h; refine ⟨?_,rfl⟩
    simpa using h0
  apply he
  refine ⟨(|a|:ℚ)/|b|,?_⟩
  have hbR : (0:ℝ) < |(b:ℝ)| := abs_pos.mpr (by exact_mod_cast hb)
  have he0 : (0:ℝ) ≤ e := by positivity
  push_cast
  rw [eq_comm,Real.sqrt_eq_iff_mul_self_eq he0 (by positivity)]
  have hR : (a:ℝ)^2=(e:ℝ)*(b:ℝ)^2 := by
    have : ((a^2-(e:ℤ)*b^2:ℤ):ℝ)=0 := by exact_mod_cast h0
    push_cast at this; linarith
  field_simp
  rw [← sq_abs (a:ℝ),← sq_abs (b:ℝ)] at hR
  nlinarith [hR]

end Tetrahedral.UnitGap
