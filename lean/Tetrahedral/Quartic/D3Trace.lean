import Tetrahedral.Quartic.D3Ring
import Mathlib.NumberTheory.Zsqrtd.Basic
import Tetrahedral.Quartic.RelativeUnitGap
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Relative units from a balanced trace window (d=3)

The half-trace has square less than 19. The nonconstant norm coefficient
then bounds c²+2t² below two; integrality forces t=0. Both norm equations
reduce to positive sums of squares. No irrationality or norm gap is needed.

-/

namespace Tetrahedral.Quartic3
open R

noncomputable def cR : ℝ := Real.sqrt 2
noncomputable def dR : ℝ := Real.sqrt (6*cR)

theorem cR_sq : cR^2=2 := Real.sq_sqrt (by norm_num)
theorem cR_pos : 0 < cR := Real.sqrt_pos.mpr (by norm_num)

theorem dR_sq : dR^2=6*cR := Real.sq_sqrt (by have := cR_pos; positivity)
theorem dR_pos : 0 < dR := Real.sqrt_pos.mpr (by have := cR_pos; positivity)



/-- The real embedding `q ↦ √2`, `s ↦ √(6√2)`. -/
noncomputable def sig (x : R) : ℝ := (x 0:ℝ)+(x 1:ℝ)*cR+((x 2:ℝ)+(x 3:ℝ)*cR)*dR

theorem sig_mul (x y : R) : sig (x*y)=sig x*sig y := by
  have hc := cR_sq; have hd := dR_sq
  simp only [sig,mul_apply0,mul_apply1,mul_apply2,mul_apply3]; push_cast
  linear_combination ((-6)*(x 3:ℝ)*(y 3:ℝ)*cR+(-6)*(x 3:ℝ)*(y 2:ℝ)+(-1)*(x 3:ℝ)*(y 1:ℝ)*dR+(-6)*(x 2:ℝ)*(y 3:ℝ)+(-1)*(x 1:ℝ)*(y 3:ℝ)*dR+(-1)*(x 1:ℝ)*(y 1:ℝ))*hc+((-1)*(x 3:ℝ)*(y 3:ℝ)*cR^2+(-1)*(x 3:ℝ)*(y 2:ℝ)*cR+(-1)*(x 2:ℝ)*(y 3:ℝ)*cR+(-1)*(x 2:ℝ)*(y 2:ℝ))*hd

noncomputable def sigHom : R →* ℝ where
  toFun := sig
  map_one' := by simp [sig]
  map_mul' := sig_mul

/-- `σ(x)·σ(τx)` is the relative norm at the real place. -/
theorem sig_tau (x : R) : sig x*sig (tau x)=(relH x:ℝ)+(relK x:ℝ)*cR := by
  have hc := cR_sq; have hd := dR_sq
  simp only [sig,tau_apply0,tau_apply1,tau_apply2,tau_apply3,relH,relK]; push_cast
  linear_combination ((x 1:ℝ)^2-12*(x 2:ℝ)*(x 3:ℝ)-6*(x 3:ℝ)^2*cR)*hc
    +(-((x 2:ℝ)+(x 3:ℝ)*cR)^2)*hd


/-! ## Bounds from one real parameter -/

noncomputable def Lam : ℝ := sig rho
theorem Lam_val : Lam=17+12*cR+(6+4*cR)*dR := by simp [Lam,sig,rho]

theorem Lam_coarse : Lam < 72 := by
  have hc : cR < 3/2 := by nlinarith [cR_sq,cR_pos]
  have hd : dR < 3 := by nlinarith [dR_sq,dR_pos]
  have hcd : cR*dR < 9/2 := calc
    cR*dR < (3/2)*dR := mul_lt_mul_of_pos_right hc dR_pos
    _ < 9/2 := by linarith
  rw [Lam_val]; nlinarith [cR_pos,dR_pos]

theorem one_lt_Lam : 1 < Lam := by
  rw [Lam_val]; have := cR_pos; have := dR_pos; nlinarith

/-! ## The descent -/

def relNR : R →* ℤ√2 where
  toFun x := ⟨relH x,relK x⟩
  map_one' := by ext <;> rfl
  map_mul' x y := by ext <;> simp [relH_mul,relK_mul]

theorem relN_rho_zpow (m : ℤ) : relH (↑(rhoU^m):R)=1 ∧ relK (↑(rhoU^m):R)=0 := by
  have h1 : Units.map relNR rhoU=1 := by ext <;> rfl
  have := congrArg (fun z : (ℤ√2)ˣ => (z:ℤ√2)) (map_zpow (Units.map relNR) rhoU m)
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
    ((v 0:ℝ)+(v 1:ℝ)*cR) Lam 19
    hp ht hS hTau (by linarith [Lam_coarse])
  have hab : v 0*v 1=3*((v 2)^2+2*(v 3)^2) := by
    have hk := hv.2; simp only [relK] at hk; linarith
  have habR : (v 0:ℝ)*(v 1:ℝ)=3*((v 2:ℝ)^2+2*(v 3:ℝ)^2) := by exact_mod_cast hab
  have he : ((v 0:ℝ)+(v 1:ℝ)*cR)^2=
      ((v 0:ℝ)-(v 1:ℝ)*cR)^2+12*((v 2:ℝ)^2+2*(v 3:ℝ)^2)*cR := by
    linear_combination 4*cR*habR
  have hc : (1:ℝ)<cR := by nlinarith [cR_sq,cR_pos]
  have hC : (v 2:ℝ)^2+2*(v 3:ℝ)^2<2 := by
    by_contra hn
    have hge : 2≤(v 2:ℝ)^2+2*(v 3:ℝ)^2 := by linarith
    have hp := mul_nonneg (sub_nonneg.mpr hge) cR_pos.le
    nlinarith only [hA,he,hp,hc,sq_nonneg ((v 0:ℝ)-(v 1:ℝ)*cR)]
  have hCi : (v 2)^2+2*(v 3)^2<2 := by exact_mod_cast hC
  have h3 : v 3=0 := by
    by_contra hn
    have hh := Int.one_le_abs hn
    nlinarith [sq_abs (v 3),sq_nonneg (v 2)]
  have hh := hv.1
  norm_num [relH,h3] at hh
  have h1sq : (v 1)^2=0 := by nlinarith [sq_nonneg (v 0),sq_nonneg (v 1)]
  have h1 : v 1=0 := (pow_eq_zero_iff (n:=2) (by norm_num)).mp h1sq
  have hk := hv.2
  norm_num [relK,h1,h3] at hk
  have h2 : v 2=0 := by nlinarith
  exact hv0 ⟨h2,h3⟩

end Tetrahedral.Quartic3
