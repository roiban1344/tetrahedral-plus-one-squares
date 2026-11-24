import Tetrahedral.Quartic.D11Ring
import Mathlib.NumberTheory.Zsqrtd.Basic
import Tetrahedral.Quartic.UnitGap
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Relative units of the d=11 order by one real parameter

Real place: `q ↦ √66`, `s ↦ √(176+22√66)`, `t = qs/11`. At the other place of `F` the relative
norm is `A'² + (22√66−176)·B'²` with a positive coefficient. If `u ≠ ±1` then the `s`-coefficient `B` is nonzero, so `|N(B)|` is bounded below and
`(σ(u) − σ(u)⁻¹)² ≥ 4ν²|N(D)|` (`gap_x`). Applied to `u` and `ρ·τu` with `1 ≤ |σ(u)| < σ(ρ)`, this
contradicts `σ(ρ) < 4ν²|N(D)|`, so no box of lattice points is enumerated.
-/

namespace Tetrahedral.Quartic11
open R

noncomputable def cR : ℝ := Real.sqrt 66
noncomputable def dR : ℝ := Real.sqrt (176+22*cR)

theorem cR_sq : cR^2=66 := Real.sq_sqrt (by norm_num)
theorem cR_pos : 0 < cR := Real.sqrt_pos.mpr (by norm_num)
theorem cR_lo : 8.124 < cR := (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
theorem cR_hi : cR < 8.1241 := (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
theorem dR_sq : dR^2=176+22*cR := Real.sq_sqrt (by have := cR_pos; positivity)
theorem dR_pos : 0 < dR := Real.sqrt_pos.mpr (by have := cR_pos; positivity)
theorem dR_lo : 18.834 < dR := (Real.lt_sqrt (by norm_num)).mpr (by have := cR_lo; nlinarith)
theorem dR_hi : dR < 18.8344 := (Real.sqrt_lt' (by norm_num)).mpr (by have := cR_hi; nlinarith)

/-- The real embedding. -/
noncomputable def sig (x : R) : ℝ := (x 0:ℝ)+(x 1:ℝ)*cR+((x 2:ℝ)+(x 3:ℝ)*cR/11)*dR

theorem sig_mul (x y : R) : sig (x*y)=sig x*sig y := by
  have hc := cR_sq; have hd := dR_sq
  simp only [sig,mul_apply0,mul_apply1,mul_apply2,mul_apply3]; push_cast
  linear_combination ((-16/11:ℝ)*(x 3:ℝ)*(y 3:ℝ)+(-2/11:ℝ)*(x 3:ℝ)*(y 3:ℝ)*cR+(-2)*(x 3:ℝ)*(y 2:ℝ)+(-1/11:ℝ)*(x 3:ℝ)*(y 1:ℝ)*dR+(-2)*(x 2:ℝ)*(y 3:ℝ)+(-1/11:ℝ)*(x 1:ℝ)*(y 3:ℝ)*dR+(-1)*(x 1:ℝ)*(y 1:ℝ))*hc+((-1/121:ℝ)*(x 3:ℝ)*(y 3:ℝ)*cR^2+(-1/11:ℝ)*(x 3:ℝ)*(y 2:ℝ)*cR+(-1/11:ℝ)*(x 2:ℝ)*(y 3:ℝ)*cR+(-1)*(x 2:ℝ)*(y 2:ℝ))*hd

noncomputable def sigHom : R →* ℝ where
  toFun := sig
  map_one' := by simp [sig]
  map_mul' := sig_mul

theorem sig_tau (x : R) : sig x*sig (tau x)=(relH x:ℝ)+(relK x:ℝ)*cR := by
  have hc := cR_sq; have hd := dR_sq
  simp only [sig,tau_apply0,tau_apply1,tau_apply2,tau_apply3,relH,relK]; push_cast
  linear_combination ((-16/11:ℝ)*(x 3:ℝ)^2+(-2/11:ℝ)*(x 3:ℝ)^2*cR+(-4)*(x 2:ℝ)*(x 3:ℝ)+(1)*(x 1:ℝ)^2)*hc+(-((x 2:ℝ)+(x 3:ℝ)*cR/11)^2)*hd

theorem conj_place (x : R) :
    ((x 0:ℝ)-(x 1:ℝ)*cR)^2+(22*cR-176)*((x 2:ℝ)-(x 3:ℝ)*cR/11)^2=(relH x:ℝ)-(relK x:ℝ)*cR := by
  have hc := cR_sq
  simp only [relH,relK]; push_cast
  linear_combination ((-16/11:ℝ)*(x 3:ℝ)^2+(2/11:ℝ)*(x 3:ℝ)^2*cR+(-4)*(x 2:ℝ)*(x 3:ℝ)+(1)*(x 1:ℝ)^2)*hc

/-! ## Bounds from one real parameter -/

noncomputable def Lam : ℝ := sig rho
theorem Lam_val : Lam=33+4*cR+(2+2*cR/11)*dR := by simp [Lam,sig,rho]
theorem Lam_lt : Lam < 131 := by
  rw [Lam_val]; have := cR_hi; have := dR_hi; have := cR_pos; have := dR_pos; nlinarith
theorem one_lt_Lam : 1 < Lam := by
  rw [Lam_val]; have := cR_pos; have := dR_pos; nlinarith

/-! ## The descent -/

def relNR : R →* ℤ√66 where
  toFun x := ⟨relH x,relK x⟩
  map_one' := by ext <;> rfl
  map_mul' x y := by ext <;> simp [relH_mul,relK_mul]

theorem relN_rho_zpow (m : ℤ) : relH (↑(rhoU^m):R)=1 ∧ relK (↑(rhoU^m):R)=0 := by
  have h1 : Units.map relNR rhoU=1 := by ext <;> rfl
  have := congrArg (fun z : (ℤ√66)ˣ => (z:ℤ√66)) (map_zpow (Units.map relNR) rhoU m)
  simp only [h1,one_zpow,Units.coe_map,Units.val_one] at this
  exact ⟨congrArg Zsqrtd.re this,congrArg Zsqrtd.im this⟩

theorem sig_rho_zpow (m : ℤ) : sig (↑(rhoU^m):R)=Lam^m := by
  have := congrArg (fun z : ℝˣ => (z:ℝ)) (map_zpow (Units.map sigHom) rhoU m)
  simp only [Units.coe_map,Units.val_zpow_eq_zpow_val] at this
  exact this

/-! ## The gap -/

theorem tau_rel (x : R) : relH (tau x)=relH x ∧ relK (tau x)=relK x := by
  constructor <;> simp [relH,relK,tau]

theorem sig_tau_inv (x : R) (hH : relH x=1) (hK : relK x=0) : sig (tau x)=(sig x)⁻¹ := by
  have h : sig x*sig (tau x)=1 := by rw [sig_tau,hH,hK]; simp
  exact eq_inv_of_mul_eq_one_right h

theorem trivial_unit (x : R) (hH : relH x=1) (hK : relK x=0) (h0 : x 2=0 ∧ x 3=0) :
    x=1 ∨ x= -1 := by
  obtain ⟨h2,h3⟩ := h0
  simp only [relH,relK,h2,h3] at hH hK
  have h1sq : (x 1)^2=0 := by nlinarith [sq_nonneg (x 0),sq_nonneg (x 1)]
  have h1 : x 1=0 := pow_eq_zero_iff (n:=2) (by norm_num) |>.mp h1sq
  rw [h1] at hH
  have : (x 0-1)*(x 0+1)=0 := by nlinarith
  rcases mul_eq_zero.mp this with h|h
  · left; ext i; fin_cases i <;> simp [h1,h2,h3] <;> omega
  · right; ext i; fin_cases i <;> simp [h1,h2,h3] <;> omega

theorem sqrt_irr : Irrational (Real.sqrt ((66:ℕ):ℝ)) := by
  apply irrational_sqrt_natCast_iff.mpr
  rintro ⟨r,hr⟩
  have : r ≤ 66 := by nlinarith
  interval_cases r <;> omega

theorem k_ge3 (a b : ℤ) (hk : 11*a^2-6*b^2≠0) : (3:ℤ) ≤ |11*a^2-6*b^2| := by
  by_contra h; push_neg at h
  have m3 : ∀ a : ZMod 3, 2*a^2≠1 := by decide
  have m11 : ∀ b : ZMod 11, -6*b^2≠-1 ∧ -6*b^2≠2 := by decide
  have c3 : ((11*a^2-6*b^2:ℤ):ZMod 3)=2*(a:ZMod 3)^2 := by
    push_cast; rw [show (11:ZMod 3)=2 by decide,show (6:ZMod 3)=0 by decide]; ring
  have c11 : ((11*a^2-6*b^2:ℤ):ZMod 11)=-6*(b:ZMod 11)^2 := by
    push_cast; rw [show (11:ZMod 11)=0 by decide]; ring
  rw [abs_lt] at h
  have : 11*a^2-6*b^2=1 ∨ 11*a^2-6*b^2= -2 ∨ 11*a^2-6*b^2= -1 ∨ 11*a^2-6*b^2=2 := by omega
  rcases this with e|e|e|e <;> rw [e] at c3 c11 <;> push_cast at c3 c11
  · exact m3 _ c3.symm
  · exact m3 _ (by rw [← c3]; decide)
  · exact (m11 _).1 c11.symm
  · exact (m11 _).2 c11.symm

theorem normB (x : R) (hnz : ¬(x 2=0 ∧ x 3=0)) : ((3:ℝ)/11)^2 ≤ (((x 2:ℝ)+(x 3:ℝ)*cR/11)*((x 2:ℝ)-(x 3:ℝ)*cR/11))^2 := by
  have hk0 : 11*(x 2)^2-6*(x 3)^2≠0 := by
    have := UnitGap.norm_ne_zero 66 sqrt_irr (11*x 2) (x 3)
      (by intro h; exact hnz ⟨by omega,h.2⟩)
    intro h0; apply this; push_cast; linear_combination 11*h0
  have h3 := k_ge3 (x 2) (x 3) hk0
  have h9 : (9:ℤ) ≤ (11*(x 2)^2-6*(x 3)^2)^2 := by nlinarith [sq_abs (11*(x 2)^2-6*(x 3)^2)]
  have e1 : ((x 2:ℝ)+(x 3:ℝ)*cR/11)*((x 2:ℝ)-(x 3:ℝ)*cR/11)=((11*(x 2)^2-6*(x 3)^2:ℤ):ℝ)/11 := by
    push_cast; have := cR_sq; field_simp; linear_combination (-(x 3:ℝ)^2)*this
  have h9r : (9:ℝ) ≤ (11*(x 2:ℝ)^2-6*(x 3:ℝ)^2)^2 := by exact_mod_cast h9
  rw [e1,div_pow,div_pow,div_le_div_iff_of_pos_right (by norm_num)]
  push_cast; norm_num; linarith

theorem gap_x (x : R) (hH : relH x=1) (hK : relK x=0) (hnz : ¬(x 2=0 ∧ x 3=0)) :
    4*72 ≤ (sig x-sig (tau x))^2 := by
  have hc1 : ((x 0:ℝ)-(x 1:ℝ)*cR)^2+(22*cR-176)*((x 2:ℝ)-(x 3:ℝ)*cR/11)^2=1 := by
    have := conj_place x; rw [hH,hK] at this; push_cast at this; linarith
  have hDm : 0 < (22*cR-176) := by have := cR_lo; nlinarith
  have hST : sig x-sig (tau x)=2*((x 2:ℝ)+(x 3:ℝ)*cR/11)*dR := by
    simp only [sig,tau_apply0,tau_apply1,tau_apply2,tau_apply3]; push_cast; ring
  have := UnitGap.gap (sig x) (sig (tau x)) ((x 2:ℝ)+(x 3:ℝ)*cR/11) ((x 2:ℝ)-(x 3:ℝ)*cR/11) ((x 0:ℝ)-(x 1:ℝ)*cR) dR
    (176+22*cR) (22*cR-176) ((3:ℝ)/11) hST dR_sq hDm hc1 (normB x hnz)
  have hM : 4*((3:ℝ)/11)^2*(176+22*cR)*(22*cR-176)=4*72 := by
    have := cR_sq; linear_combination (4*((3:ℝ)/11)^2*22^2)*this
  linarith

theorem rel_unit_trace (u : R) (hH : relH u=1) (hK : relK u=0) :
    ∃ m : ℤ, u=(↑(rhoU^m):R) ∨ u= -(↑(rhoU^m):R) := by
  have hst : sig u*sig (tau u)=1 := by rw [sig_tau,hH,hK]; simp
  have hne : sig u≠0 := by intro h; rw [h,zero_mul] at hst; exact zero_ne_one hst
  obtain ⟨m,hm1,hm2⟩ := exists_mem_Ico_zpow (abs_pos.mpr hne) one_lt_Lam
  have hLpos : 0 < Lam := by linarith [one_lt_Lam]
  set v := u*(↑(rhoU^(-m)):R) with hv
  have hsv : |sig v| = |sig u| * Lam^(-m) := by
    rw [hv,sig_mul,sig_rho_zpow,abs_mul,abs_of_pos (zpow_pos hLpos _)]
  have hpos : 0 < Lam^(-m) := zpow_pos hLpos _
  have hlo : 1 ≤ |sig v| := by
    rw [hsv]
    have : Lam^m*Lam^(-m)=1 := by rw [← zpow_add₀ hLpos.ne']; simp
    nlinarith
  have hhi : |sig v| < Lam := by
    rw [hsv]
    have : Lam^(m+1)*Lam^(-m)=Lam := by rw [← zpow_add₀ hLpos.ne']; simp
    nlinarith
  obtain ⟨r1,r2⟩ := relN_rho_zpow (-m)
  have hvH : relH v=1 := by rw [hv,relH_mul,hH,hK,r1,r2]; ring
  have hvK : relK v=0 := by rw [hv,relK_mul,hH,hK,r1,r2]; ring
  have hback : u=v*(↑(rhoU^m):R) := by
    rw [hv,mul_assoc,← Units.val_mul,← zpow_add]; simp
  by_cases hv0 : v 2=0 ∧ v 3=0
  · rcases trivial_unit v hvH hvK hv0 with e|e
    · exact ⟨m,Or.inl (by rw [hback,e,one_mul])⟩
    · exact ⟨m,Or.inr (by rw [hback,e]; ring)⟩
  exfalso
  -- the companion `v' = ρ·τv`, with `|σ(v)|·|σ(v')| = Λ`
  set v' := rho*tau v with hv'
  have hrH : relH rho=1 := by decide
  have hrK : relK rho=0 := by decide
  have hv'H : relH v'=1 := by rw [hv',relH_mul,hrH,hrK,(tau_rel v).1,(tau_rel v).2,hvH,hvK]; ring
  have hv'K : relK v'=0 := by rw [hv',relK_mul,hrH,hrK,(tau_rel v).1,(tau_rel v).2,hvH,hvK]; ring
  have hsig' : sig v'=Lam*(sig v)⁻¹ := by
    rw [hv',sig_mul,sig_tau_inv v hvH hvK,Lam]
  set a := |sig v| with ha_def
  set b := |sig v'| with hb_def
  have hapos : 0 < a := by linarith
  have hab : a*b=Lam := by
    rw [hb_def,hsig',abs_mul,abs_of_pos hLpos,abs_inv,← ha_def,mul_left_comm,
      mul_inv_cancel₀ hapos.ne',mul_one]
  have hb1 : 1 ≤ b := by
    have : b=Lam/a := eq_div_of_mul_eq hapos.ne' (by rw [mul_comm]; exact hab)
    rw [this,le_div_iff₀ hapos]; linarith
  have hv'0 : ¬(v' 2=0 ∧ v' 3=0) := by
    intro h0
    have hs1 : b=1 := by
      rcases trivial_unit v' hv'H hv'K h0 with e|e <;> rw [hb_def,e] <;> simp [sig]
    rw [hs1,mul_one] at hab; linarith
  have ha : 4*72 ≤ (a-a⁻¹)^2 := by
    have := gap_x v hvH hvK hv0
    rw [sig_tau_inv v hvH hvK,UnitGap.sq_sub_inv_abs] at this; exact this
  have hb : 4*72 ≤ (b-b⁻¹)^2 := by
    have := gap_x v' hv'H hv'K hv'0
    rw [sig_tau_inv v' hv'H hv'K,UnitGap.sq_sub_inv_abs] at this; exact this
  exact UnitGap.contra a b Lam 72 hlo hb1 hab (by linarith [Lam_lt]) ha hb

end Tetrahedral.Quartic11
