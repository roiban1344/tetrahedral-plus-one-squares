import Tetrahedral.Quartic.UnitGap
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Tetrahedral.RelativeUnitGap

/-- A norm-one real parameter turns the conjugate gap into an absolute gap. -/
theorem absolute_gap (S T M : ℝ) (hprod : S*T=1) (hgap : 4*M≤(S-T)^2) :
    4*M≤(|S|-|S|⁻¹)^2 := by
  have he : T=S⁻¹ := eq_inv_of_mul_eq_one_right hprod
  rwa [he,UnitGap.sq_sub_inv_abs] at hgap

/-- One multiplicative interval and the companion rho*tau(v) suffice to
generate all relative units. All field-specific work is the pair obstruction. -/
theorem generate {R : Type*} [CommRing R]
    (sigma : R →* ℝ) (tau : R → R) (N C : R → Prop) (rho : Rˣ)
    (hLambda : 1<sigma (rho:R)) (hneg : |sigma (-1)|=1)
    (hmul : ∀ x z, N x → N z → N (x*z))
    (htau : ∀ x, N x → N (tau x))
    (hpowers : ∀ i : ℤ, N (↑(rho^i):R))
    (hprod : ∀ x, N x → sigma x*sigma (tau x)=1)
    (htrivial : ∀ x, N x → C x → x=1 ∨ x= -1)
    (hpair : ∀ x z, N x → N z → ¬ C x → ¬ C z →
      1≤|sigma x| → 1≤|sigma z| → |sigma x| * |sigma z|=sigma (rho:R) → False)
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
  exact (hpair v z hvN hzN hvC hzC hlo hzlo hab).elim

/-- A coarse bound on the companion gap bounds the squared half-trace.
No approximation to either square root is needed. -/
theorem trace_bound (a b L : ℝ) (ha1 : 1≤a) (hb1 : 1≤b)
    (hab : a*b=L) (hL : L<40) (hb : 32≤(b-b⁻¹)^2) :
    ((a+a⁻¹)/2)^2<14 := by
  have hb2 : 32≤b^2 := le_trans hb (UnitGap.sq_le_of_one_le b hb1)
  have hab2 : a^2*b^2=L^2 := by rw [← hab]; ring
  have hprod := mul_le_mul_of_nonneg_left hb2 (sq_nonneg a)
  have hLpos : 0<L := by nlinarith
  have hupper := mul_pos (sub_pos.mpr hL) (show 0<40+L by linarith)
  have ha2 : a^2<50 := by nlinarith
  have hi0 : 0≤a⁻¹ := inv_nonneg.mpr (by linarith)
  have hi1 : a⁻¹≤1 := inv_le_one_of_one_le₀ ha1
  have he : a*a⁻¹=1 := mul_inv_cancel₀ (by linarith)
  nlinarith

end Tetrahedral.RelativeUnitGap
