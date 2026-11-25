import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Tetrahedral.RelativeUnitGap

/-- A centered multiplicative interval bounds both real conjugates.
Only a single small-unit obstruction is needed; no companion is constructed. -/
theorem generate {R : Type*} [CommRing R]
    (sigma : R →* ℝ) (N C : R → Prop) (rho : Rˣ)
    (hLambda : 1<sigma (rho:R))
    (hmul : ∀ x z, N x → N z → N (x*z))
    (hpowers : ∀ i : ℤ, N (↑(rho^i):R))
    (hne : ∀ x, N x → sigma x≠0)
    (htrivial : ∀ x, N x → C x → x=1 ∨ x= -1)
    (hsmall : ∀ x, N x → ¬ C x → (sigma x)^2≤sigma (rho:R) →
      ((sigma x)⁻¹)^2≤sigma (rho:R) → False)
    (u : R) (hu : N u) : ∃ i : ℤ, u=(↑(rho^i):R) ∨ u= -(↑(rho^i):R) := by
  let L := sigma (rho:R)
  have hL : 0<L := by dsimp [L]; linarith
  have ht : 0<Real.sqrt L := Real.sqrt_pos.mpr hL
  have ht2 : (Real.sqrt L)^2=L := Real.sq_sqrt hL.le
  obtain ⟨i,hi1,hi2⟩ := exists_mem_Ico_zpow (mul_pos (abs_pos.mpr (hne u hu)) ht) hLambda
  have sigpow (j : ℤ) : sigma (↑(rho^j):R)=L^j := by
    have hh := congrArg (fun z : ℝˣ => (z:ℝ)) (map_zpow (Units.map sigma) rho j)
    simpa only [Units.coe_map,Units.val_zpow_eq_zpow_val] using hh
  let v := u*(↑(rho^(-i)):R)
  have hvN : N v := hmul _ _ hu (hpowers (-i))
  have hsv : |sigma v|=|sigma u| * L^(-i) := by
    rw [show v=u*(↑(rho^(-i)):R) from rfl,map_mul,sigpow,abs_mul,abs_of_pos (zpow_pos hL _)]
  have hpos : 0<L^(-i) := zpow_pos hL _
  have hlo : 1≤ |sigma v| *Real.sqrt L := by
    rw [hsv]
    have hh : L^i*L^(-i)=1 := by rw [←zpow_add₀ hL.ne']; simp
    have hp := mul_le_mul_of_nonneg_right hi1 hpos.le
    nlinarith only [hh,hp]
  have hhi : |sigma v| *Real.sqrt L<L := by
    rw [hsv]
    have hh : L^(i+1)*L^(-i)=L := by rw [←zpow_add₀ hL.ne']; simp
    have hp := mul_lt_mul_of_pos_right hi2 hpos
    nlinarith only [hh,hp]
  have hr : L/Real.sqrt L=Real.sqrt L := (div_eq_iff ht.ne').mpr (by nlinarith only [ht2])
  have hupper : |sigma v|<Real.sqrt L := by
    rw [←hr]
    exact (lt_div_iff₀ ht).mpr hhi
  have hvpos : 0< |sigma v| := abs_pos.mpr (hne v hvN)
  have hinv : |sigma v|⁻¹≤Real.sqrt L := by
    rw [←one_div]
    apply (div_le_iff₀ hvpos).mpr
    nlinarith only [hlo]
  have hS : (sigma v)^2≤L := by
    have hh := mul_self_le_mul_self (abs_nonneg (sigma v)) hupper.le
    nlinarith only [hh,ht2,sq_abs (sigma v)]
  have hT : ((sigma v)⁻¹)^2≤L := by
    have hh : (|sigma v|⁻¹)^2≤L := by
      have hh := mul_self_le_mul_self (inv_nonneg.mpr hvpos.le) hinv
      nlinarith only [hh,ht2]
    simpa only [←abs_inv,sq_abs] using hh
  have hback : u=v*(↑(rho^i):R) := by
    dsimp [v]; rw [mul_assoc,←Units.val_mul,←zpow_add]; simp
  by_cases hvC : C v
  · rcases htrivial v hvN hvC with he|he
    · exact ⟨i,Or.inl (by rw [hback,he,one_mul])⟩
    · exact ⟨i,Or.inr (by rw [hback,he]; ring)⟩
  exact (hsmall v hvN hvC hS hT).elim

/-- A reciprocal pair bounded in both directions has a small half-trace. -/
theorem half_trace_bound (S T A L B : ℝ) (hprod : S*T=1) (htrace : 2*A=S+T)
    (hS : S^2≤L) (hT : T^2≤L) (hL : L+3<4*B) : A^2<B := by
  have hp : S^2*T^2=1 := by rw [←mul_pow,hprod]; norm_num
  have hsq : 4*A^2=S^2+T^2+2 := by
    linear_combination (2*A+S+T)*htrace+2*hprod
  have hsum : S^2+T^2≤L+1 := by
    by_cases hs : S^2≤1
    · linarith
    · have ht : T^2≤1 := by
        have hh := mul_nonneg (sub_nonneg.mpr (le_of_lt (lt_of_not_ge hs))) (sq_nonneg T)
        nlinarith only [hh,hp]
      linarith
  linarith

/-- A positive product of two nonzero integers gives a lower trace bound. -/
theorem integer_trace_lower (a b : ℤ) (s e : ℝ) (hs : s^2=e)
    (hab : 0<a*b) :
    1+e+2*s*(a*b:ℤ)≤((a:ℝ)+(b:ℝ)*s)^2 := by
  have ha : a≠0 := by intro hz; simp [hz] at hab
  have hb : b≠0 := by intro hz; simp [hz] at hab
  have ha2 : (1:ℝ)≤(a:ℝ)^2 := by
    have hh : (1:ℤ)≤a^2 := by nlinarith [Int.one_le_abs ha,sq_abs a]
    exact_mod_cast hh
  have hb2 : (1:ℝ)≤(b:ℝ)^2 := by
    have hh : (1:ℤ)≤b^2 := by nlinarith [Int.one_le_abs hb,sq_abs b]
    exact_mod_cast hh
  have he : 0≤e := by rw [←hs]; exact sq_nonneg _
  have hh := mul_nonneg he (sub_nonneg.mpr hb2)
  have hid : ((a:ℝ)+(b:ℝ)*s)^2=(a:ℝ)^2+e*(b:ℝ)^2+2*s*(a*b:ℤ) := by
    push_cast
    linear_combination (b:ℝ)^2*hs
  linarith

end Tetrahedral.RelativeUnitGap
