import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Tetrahedral.RelativeUnitGap

/-- One multiplicative interval and the companion rho*tau(v) suffice to
generate all relative units. Each field only excludes one nontrivial unit in the smaller half-interval. -/
theorem generate {R : Type*} [CommRing R]
    (sigma : R →* ℝ) (tau : R → R) (N C : R → Prop) (rho : Rˣ)
    (hLambda : 1<sigma (rho:R)) (hneg : |sigma (-1)|=1)
    (hmul : ∀ x z, N x → N z → N (x*z))
    (htau : ∀ x, N x → N (tau x))
    (hpowers : ∀ i : ℤ, N (↑(rho^i):R))
    (hprod : ∀ x, N x → sigma x*sigma (tau x)=1)
    (htrivial : ∀ x, N x → C x → x=1 ∨ x= -1)
    (hsmall : ∀ x, N x → ¬ C x → 1≤|sigma x| →
      |sigma x|^2≤sigma (rho:R) → False)
    (u : R) (hu : N u) : ∃ i : ℤ, u=(↑(rho^i):R) ∨ u= -(↑(rho^i):R) := by
  let L := sigma (rho:R)
  have hL : 0<L := by dsimp [L]; linarith
  have hne : sigma u≠0 := by
    intro h; have hh := hprod u hu; rw [h,zero_mul] at hh; exact zero_ne_one hh
  obtain ⟨i,hi1,hi2⟩ := exists_mem_Ico_zpow (abs_pos.mpr hne) hLambda
  have sigpow (j : ℤ) : sigma (↑(rho^j):R)=L^j := by
    have hh := congrArg (fun z : ℝˣ => (z:ℝ)) (map_zpow (Units.map sigma) rho j)
    simpa only [Units.coe_map,Units.val_zpow_eq_zpow_val] using hh
  let v := u*(↑(rho^(-i)):R)
  have hvN : N v := hmul _ _ hu (hpowers (-i))
  have hsv : |sigma v|=|sigma u| * L^(-i) := by
    rw [show v=u*(↑(rho^(-i)):R) from rfl,map_mul,sigpow,abs_mul,abs_of_pos (zpow_pos hL _)]
  have hpos : 0<L^(-i) := zpow_pos hL _
  have hlo : 1≤|sigma v| := by
    rw [hsv]
    have hh : L^i*L^(-i)=1 := by rw [← zpow_add₀ hL.ne']; simp
    nlinarith
  have hhi : |sigma v|<L := by
    rw [hsv]
    have hh : L^(i+1)*L^(-i)=L := by rw [← zpow_add₀ hL.ne']; simp
    nlinarith
  have hback : u=v*(↑(rho^i):R) := by
    dsimp [v]; rw [mul_assoc,← Units.val_mul,← zpow_add]; simp
  by_cases hvC : C v
  · rcases htrivial v hvN hvC with he|he
    · exact ⟨i,Or.inl (by rw [hback,he,one_mul])⟩
    · exact ⟨i,Or.inr (by rw [hback,he]; ring)⟩
  let z := (rho:R)*tau v
  have hrho : N (rho:R) := by simpa only [zpow_one] using hpowers 1
  have hzN : N z := hmul _ _ hrho (htau v hvN)
  have hsig : sigma z=L*(sigma v)⁻¹ := by
    have hinv : sigma (tau v)=(sigma v)⁻¹ := eq_inv_of_mul_eq_one_right (hprod v hvN)
    change sigma ((rho:R)*tau v)=L*(sigma v)⁻¹
    rw [map_mul,hinv]
  have hvpos : 0< |sigma v| := by linarith
  have hab : |sigma v| * |sigma z|=L := by
    rw [hsig,abs_mul,abs_of_pos hL,abs_inv,mul_left_comm,mul_inv_cancel₀ hvpos.ne',mul_one]
  have hzlo : 1≤|sigma z| := by
    have hh : |sigma z|=L/|sigma v| := eq_div_of_mul_eq hvpos.ne' (by rw [mul_comm]; exact hab)
    rw [hh,le_div_iff₀ hvpos]; linarith
  have hzC : ¬ C z := by
    intro h
    have hzabs : |sigma z|=1 := by
      rcases htrivial z hzN h with he|he
      · rw [he,map_one,abs_one]
      · rwa [he]
    rw [hzabs,mul_one] at hab; linarith
  rcases le_total |sigma v| |sigma z| with hle|hle
  · have hvsmall : |sigma v|^2≤sigma (rho:R) := by
      have hh := mul_le_mul_of_nonneg_left hle (abs_nonneg (sigma v))
      nlinarith only [hh,hab]
    exact (hsmall v hvN hvC hlo hvsmall).elim
  · have hzsmall : |sigma z|^2≤sigma (rho:R) := by
      have hh := mul_le_mul_of_nonneg_left hle (abs_nonneg (sigma z))
      nlinarith only [hh,hab]
    exact (hsmall z hzN hzC hzlo hzsmall).elim

/-- The smaller half-interval bounds the squared base-field half-trace. -/
theorem half_trace_bound (S T A L B : ℝ) (hprod : S*T=1) (htrace : 2*A=S+T)
    (hlo : 1≤|S|) (hsmall : |S|^2≤L) (hL : L+3<4*B) : A^2<B := by
  have hT : T=S⁻¹ := eq_inv_of_mul_eq_one_right hprod
  have habs : (S+S⁻¹)^2=(|S|+|S|⁻¹)^2 := by
    rcases le_or_gt 0 S with hs|hs
    · rw [abs_of_nonneg hs]
    · rw [abs_of_neg hs,inv_neg]; ring
  have hsq : 4*A^2=(|S|+|S|⁻¹)^2 := by
    rw [←habs,←hT,←htrace]; ring
  have hi0 : 0≤|S|⁻¹ := inv_nonneg.mpr (by linarith)
  have hi1 : |S|⁻¹≤1 := inv_le_one_of_one_le₀ hlo
  have he : |S| * |S|⁻¹=1 := mul_inv_cancel₀ (by linarith)
  nlinarith [mul_self_le_mul_self hi0 hi1]

/-- Two conjugate trace bounds force an integral coefficient to vanish. -/
theorem trace_coefficient_zero (a b : ℤ) (s e : ℝ) (hs : s^2=e)
    (hA : ((a:ℝ)+(b:ℝ)*s)^2<2*e-1)
    (hA' : ((a:ℝ)-(b:ℝ)*s)^2≤1) : b=0 := by
  by_contra hb
  have hb2 : (1:ℝ)≤(b:ℝ)^2 := by
    have hh : (1:ℤ)≤b^2 := by
      have hh := Int.one_le_abs hb; nlinarith [sq_abs b]
    exact_mod_cast hh
  have he : 0≤e := by rw [←hs]; exact sq_nonneg _
  have hp := mul_nonneg he (sub_nonneg.mpr hb2)
  have hd : ((a:ℝ)+(b:ℝ)*s-((a:ℝ)-(b:ℝ)*s))^2=4*e*(b:ℝ)^2 := by
    linear_combination 4*(b:ℝ)^2*hs
  nlinarith only [hA,hA',hp,hd,sq_nonneg ((a:ℝ)+(b:ℝ)*s+((a:ℝ)-(b:ℝ)*s))]

end Tetrahedral.RelativeUnitGap
