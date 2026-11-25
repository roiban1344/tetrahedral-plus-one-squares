import Tetrahedral.Quartic.D2Ring
import Mathlib.NumberTheory.Zsqrtd.Basic
import Tetrahedral.Quartic.RelativeUnitGap
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Relative units from a balanced trace window (d=2)

A centered power interval bounds both real conjugates. The nonconstant
norm coefficient is positive by the norm-minus-two identity, so a nontrivial unit has
positive product of its two base coefficients. Integer trace lower bounds
contradict the small trace window; no other-place norm bound is used.

-/

namespace Tetrahedral.Quartic2
open R

noncomputable def cR : ℝ := Real.sqrt 3
noncomputable def dR : ℝ := Real.sqrt (20+12*cR)

theorem cR_sq : cR^2=3 := Real.sq_sqrt (by norm_num)
theorem cR_pos : 0 < cR := Real.sqrt_pos.mpr (by norm_num)

theorem dR_sq : dR^2=20+12*cR := Real.sq_sqrt (by have := cR_pos; positivity)
theorem dR_pos : 0 < dR := Real.sqrt_pos.mpr (by have := cR_pos; positivity)

/-- The real embedding `q ↦ √3`, `s ↦ √(20+12√3)`. -/
noncomputable def sig (x : R) : ℝ := (x 0:ℝ)+(x 1:ℝ)*cR+((x 2:ℝ)+(x 3:ℝ)*cR)*dR

theorem sig_mul (x y : R) : sig (x*y)=sig x*sig y := by
  have hc := cR_sq; have hd := dR_sq
  simp only [sig,mul_apply0,mul_apply1,mul_apply2,mul_apply3]; push_cast
  linear_combination ((-20)*(x 3:ℝ)*(y 3:ℝ)+(-12)*(x 3:ℝ)*(y 3:ℝ)*cR+(-12)*(x 3:ℝ)*(y 2:ℝ)+(-1)*(x 3:ℝ)*(y 1:ℝ)*dR+(-12)*(x 2:ℝ)*(y 3:ℝ)+(-1)*(x 1:ℝ)*(y 3:ℝ)*dR+(-1)*(x 1:ℝ)*(y 1:ℝ))*hc+((-1)*(x 3:ℝ)*(y 3:ℝ)*cR^2+(-1)*(x 3:ℝ)*(y 2:ℝ)*cR+(-1)*(x 2:ℝ)*(y 3:ℝ)*cR+(-1)*(x 2:ℝ)*(y 2:ℝ))*hd

noncomputable def sigHom : R →* ℝ where
  toFun := sig
  map_one' := by simp [sig]
  map_mul' := sig_mul

/-- `σ(x)·σ(τx)` is the relative norm at the real place. -/
theorem sig_tau (x : R) : sig x*sig (tau x)=(relH x:ℝ)+(relK x:ℝ)*cR := by
  have hc := cR_sq; have hd := dR_sq
  simp only [sig,tau_apply0,tau_apply1,tau_apply2,tau_apply3,relH,relK]; push_cast
  linear_combination ((-20)*(x 3:ℝ)^2+(-12)*(x 3:ℝ)^2*cR+(-24)*(x 2:ℝ)*(x 3:ℝ)+(1)*(x 1:ℝ)^2)*hc+((-1)*(x 3:ℝ)^2*cR^2+(-2)*(x 2:ℝ)*(x 3:ℝ)*cR+(-1)*(x 2:ℝ)^2)*hd

/-! ## Bounds from one real parameter -/

noncomputable def Lam : ℝ := sig rho
theorem Lam_val : Lam=3+2*cR+dR := by simp [Lam,sig,rho]

theorem Lam_coarse : Lam < 14 := by
  have hc : cR < 2 := by nlinarith [cR_sq,cR_pos]
  have hd : dR < 7 := by nlinarith [dR_sq,dR_pos]
  rw [Lam_val]; nlinarith [cR_pos,dR_pos]

theorem one_lt_Lam : 1 < Lam := by
  rw [Lam_val]; have := cR_pos; have := dR_pos; nlinarith

/-! ## The descent -/

def relNR : R →* ℤ√3 where
  toFun x := ⟨relH x,relK x⟩
  map_one' := by ext <;> rfl
  map_mul' x y := by ext <;> simp [relH_mul,relK_mul]

theorem relN_rho_zpow (m : ℤ) : relH (↑(rhoU^m):R)=1 ∧ relK (↑(rhoU^m):R)=0 := by
  have h1 : Units.map relNR rhoU=1 := by ext <;> rfl
  have := congrArg (fun z : (ℤ√3)ˣ => (z:ℤ√3)) (map_zpow (Units.map relNR) rhoU m)
  simp only [h1,one_zpow,Units.coe_map,Units.val_one] at this
  exact ⟨congrArg Zsqrtd.re this,congrArg Zsqrtd.im this⟩

/-! ## The small trace window -/


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

theorem rel_unit_trace (u : R) (hH : relH u=1) (hK : relK u=0) :
    ∃ m : ℤ, u=(↑(rhoU^m):R) ∨ u= -(↑(rhoU^m):R) := by
  apply RelativeUnitGap.generate sigHom
    (fun x => relH x=1 ∧ relK x=0) (fun x => x 2=0 ∧ x 3=0)
    rhoU one_lt_Lam
    (fun x z hx hz => by
      constructor <;> simp [relH_mul,relK_mul,hx.1,hx.2,hz.1,hz.2])
    relN_rho_zpow
    (fun x hx => by
      intro hz
      change sig x=0 at hz
      have hh := sig_tau x
      rw [hx.1,hx.2,hz] at hh
      norm_num at hh)
    (fun x hx => trivial_unit x hx.1 hx.2) ?_ u ⟨hH,hK⟩
  intro v hv hv0 hS hT
  change (sig v)^2≤Lam at hS
  change ((sig v)⁻¹)^2≤Lam at hT
  have hp : sig v*sig (tau v)=1 := by rw [sig_tau,hv.1,hv.2]; simp
  have hTau : (sig (tau v))^2≤Lam := by
    rw [eq_inv_of_mul_eq_one_right hp]; exact hT
  have ht : 2*((v 0:ℝ)+(v 1:ℝ)*cR)=sig v+sig (tau v) := by
    simp only [sig,tau_apply0,tau_apply1,tau_apply2,tau_apply3]; push_cast; ring
  have hA := RelativeUnitGap.half_trace_bound (sig v) (sig (tau v))
    ((v 0:ℝ)+(v 1:ℝ)*cR) Lam hp ht hS hTau
  have hQ := RelativeUnitGap.norm_minus_two_positive 5 3 3 (v 2) (v 3)
    (by norm_num) (by norm_num) (by simpa using hv0)
  have hk := hv.2
  simp only [relK] at hk
  have hab : 0<v 0*v 1 := by nlinarith only [hk,hQ]
  have hlo := RelativeUnitGap.integer_trace_lower (v 0) (v 1) cR 3 cR_sq hab
  have hp : (1:ℝ)≤(v 0*v 1:ℤ) := by
    have hh : (1:ℤ)≤v 0*v 1 := hab
    exact_mod_cast hh
  have hc : 1<cR := by nlinarith [cR_sq,cR_pos]
  have hh := mul_nonneg cR_pos.le (sub_nonneg.mpr hp)
  nlinarith only [hlo,hA,Lam_coarse,hh,hc]

end Tetrahedral.Quartic2
