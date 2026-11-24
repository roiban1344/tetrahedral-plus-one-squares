import Tetrahedral.Quartic.D66Ring
import Mathlib.NumberTheory.Zsqrtd.Basic
import Tetrahedral.Quartic.UnitGap
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Relative units of `ℤ[q][t]` by one real parameter (d=66)

Real place `q ↦ √11`, `t ↦ √(756+228√11)`; at the other place of `F` the relative norm is
`A'² + (228√11−756)·B'²` with the small positive coefficient `≈ 0.19`. If `u ≠ ±1` then the `s`-coefficient `B` is nonzero, so `|N(B)|` is bounded below and
`(σ(u) − σ(u)⁻¹)² ≥ 4ν²|N(D)|` (`gap_x`). Applied to `u` and `ρ·τu` with `1 ≤ |σ(u)| < σ(ρ)`, this
contradicts `σ(ρ) < 4ν²|N(D)|`, so no box of lattice points is enumerated.
-/

namespace Tetrahedral.Quartic66
open R

noncomputable def cR : ℝ := Real.sqrt 11
noncomputable def dR : ℝ := Real.sqrt (756+228*cR)

theorem cR_sq : cR^2=11 := Real.sq_sqrt (by norm_num)
theorem cR_pos : 0 < cR := Real.sqrt_pos.mpr (by norm_num)
theorem cR_lo : 3.3166247 < cR := (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
theorem cR_hi : cR < 3.3166248 := (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
theorem dR_sq : dR^2=756+228*cR := Real.sq_sqrt (by have := cR_pos; positivity)
theorem dR_pos : 0 < dR := Real.sqrt_pos.mpr (by have := cR_pos; positivity)
theorem dR_lo : 38.8868 < dR := (Real.lt_sqrt (by norm_num)).mpr (by have := cR_lo; nlinarith)
theorem dR_hi : dR < 38.887 := (Real.sqrt_lt' (by norm_num)).mpr (by have := cR_hi; nlinarith)

/-- The real embedding `q ↦ √11`, `t ↦ √(756+228√11)`. -/
noncomputable def sig (x : R) : ℝ := (x 0:ℝ)+(x 1:ℝ)*cR+((x 2:ℝ)+(x 3:ℝ)*cR)*dR

theorem sig_mul (x y : R) : sig (x*y)=sig x*sig y := by
  have hc := cR_sq; have hd := dR_sq
  simp only [sig,mul_apply0,mul_apply1,mul_apply2,mul_apply3]; push_cast
  linear_combination ((-756)*(x 3:ℝ)*(y 3:ℝ)+(-228)*(x 3:ℝ)*(y 3:ℝ)*cR+(-228)*(x 3:ℝ)*(y 2:ℝ)+(-1)*(x 3:ℝ)*(y 1:ℝ)*dR+(-228)*(x 2:ℝ)*(y 3:ℝ)+(-1)*(x 1:ℝ)*(y 3:ℝ)*dR+(-1)*(x 1:ℝ)*(y 1:ℝ))*hc+((-1)*(x 3:ℝ)*(y 3:ℝ)*cR^2+(-1)*(x 3:ℝ)*(y 2:ℝ)*cR+(-1)*(x 2:ℝ)*(y 3:ℝ)*cR+(-1)*(x 2:ℝ)*(y 2:ℝ))*hd

noncomputable def sigHom : R →* ℝ where
  toFun := sig
  map_one' := by simp [sig]
  map_mul' := sig_mul

/-- `σ(x)·σ(τx)` is the relative norm at the real place. -/
theorem sig_tau (x : R) : sig x*sig (tau x)=(relH x:ℝ)+(relK x:ℝ)*cR := by
  have hc := cR_sq; have hd := dR_sq
  simp only [sig,tau_apply0,tau_apply1,tau_apply2,tau_apply3,relH,relK]; push_cast
  linear_combination ((-756)*(x 3:ℝ)^2+(-228)*(x 3:ℝ)^2*cR+(-456)*(x 2:ℝ)*(x 3:ℝ)+(1)*(x 1:ℝ)^2)*hc+((-1)*(x 3:ℝ)^2*cR^2+(-2)*(x 2:ℝ)*(x 3:ℝ)*cR+(-1)*(x 2:ℝ)^2)*hd

/-- The relative norm at the other place of `F` (`q ↦ −√2`). -/
theorem conj_place (x : R) :
    ((x 0:ℝ)-(x 1:ℝ)*cR)^2+(228*cR-756)*((x 2:ℝ)-(x 3:ℝ)*cR)^2=(relH x:ℝ)-(relK x:ℝ)*cR := by
  have hc := cR_sq
  simp only [relH,relK]; push_cast
  linear_combination ((-756)*(x 3:ℝ)^2+(228)*(x 3:ℝ)^2*cR+(-456)*(x 2:ℝ)*(x 3:ℝ)+(1)*(x 1:ℝ)^2)*hc

/-! ## Bounds from one real parameter -/

noncomputable def Lam : ℝ := sig rho
theorem Lam_val : Lam=19+6*cR+dR := by simp [Lam,sig,rho]
theorem Lam_lt : Lam < 77.8 := by
  rw [Lam_val]; have := cR_hi; have := dR_hi; have := cR_pos; have := dR_pos; nlinarith
theorem one_lt_Lam : 1 < Lam := by
  rw [Lam_val]; have := cR_pos; have := dR_pos; nlinarith

/-! ## The descent -/

def relNR : R →* ℤ√11 where
  toFun x := ⟨relH x,relK x⟩
  map_one' := by ext <;> rfl
  map_mul' x y := by ext <;> simp [relH_mul,relK_mul]

theorem relN_rho_zpow (m : ℤ) : relH (↑(rhoU^m):R)=1 ∧ relK (↑(rhoU^m):R)=0 := by
  have h1 : Units.map relNR rhoU=1 := by ext <;> rfl
  have := congrArg (fun z : (ℤ√11)ˣ => (z:ℤ√11)) (map_zpow (Units.map relNR) rhoU m)
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

theorem sqrt_irr : Irrational (Real.sqrt ((11:ℕ):ℝ)) := by
  apply irrational_sqrt_natCast_iff.mpr
  rintro ⟨r,hr⟩
  have : r ≤ 11 := by nlinarith
  interval_cases r <;> omega

theorem normB (x : R) (hnz : ¬(x 2=0 ∧ x 3=0)) : (1:ℝ)^2 ≤ (((x 2:ℝ)+(x 3:ℝ)*cR)*((x 2:ℝ)-(x 3:ℝ)*cR))^2 := by
  have hk := UnitGap.norm_ne_zero 11 sqrt_irr (x 2) (x 3) hnz
  have h1 : (1:ℤ) ≤ ((x 2)^2-(11:ℕ)*(x 3)^2)^2 := by
    have := Int.one_le_abs hk; nlinarith [sq_abs ((x 2)^2-(11:ℕ)*(x 3)^2)]
  have e1 : ((x 2:ℝ)+(x 3:ℝ)*cR)*((x 2:ℝ)-(x 3:ℝ)*cR)=(((x 2)^2-(11:ℕ)*(x 3)^2:ℤ):ℝ) := by
    push_cast; have := cR_sq; linear_combination (-(x 3:ℝ)^2)*this
  rw [e1]; exact_mod_cast h1

theorem gap_x (x : R) (hH : relH x=1) (hK : relK x=0) (hnz : ¬(x 2=0 ∧ x 3=0)) :
    4*288 ≤ (sig x-sig (tau x))^2 := by
  have hc1 : ((x 0:ℝ)-(x 1:ℝ)*cR)^2+(228*cR-756)*((x 2:ℝ)-(x 3:ℝ)*cR)^2=1 := by
    have := conj_place x; rw [hH,hK] at this; push_cast at this; linarith
  have hDm : 0 < (228*cR-756) := by have := cR_lo; nlinarith
  have hST : sig x-sig (tau x)=2*((x 2:ℝ)+(x 3:ℝ)*cR)*dR := by
    simp only [sig,tau_apply0,tau_apply1,tau_apply2,tau_apply3]; push_cast; ring
  have := UnitGap.gap (sig x) (sig (tau x)) ((x 2:ℝ)+(x 3:ℝ)*cR) ((x 2:ℝ)-(x 3:ℝ)*cR) ((x 0:ℝ)-(x 1:ℝ)*cR) dR
    (756+228*cR) (228*cR-756) 1 hST dR_sq hDm hc1 (normB x hnz)
  have hM : 4*1^2*(756+228*cR)*(228*cR-756)=4*288 := by
    have := cR_sq; linear_combination (4*1^2*228^2)*this
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
  have ha : 4*288 ≤ (a-a⁻¹)^2 := by
    have := gap_x v hvH hvK hv0
    rw [sig_tau_inv v hvH hvK,UnitGap.sq_sub_inv_abs] at this; exact this
  have hb : 4*288 ≤ (b-b⁻¹)^2 := by
    have := gap_x v' hv'H hv'K hv'0
    rw [sig_tau_inv v' hv'H hv'K,UnitGap.sq_sub_inv_abs] at this; exact this
  exact UnitGap.contra a b Lam 288 hlo hb1 hab (by linarith [Lam_lt]) ha hb

end Tetrahedral.Quartic66
