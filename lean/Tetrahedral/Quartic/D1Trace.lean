import Tetrahedral.Quartic.D1Ring
import Mathlib.NumberTheory.Zsqrtd.Basic
import Tetrahedral.Quartic.RelativeUnitGap
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Relative units from a balanced trace window (d=1)

A centered power interval bounds the squares of both real conjugates by Λ. Its half-trace has square less than 2e−1; the other trace has square
at most one. Their difference forces the integral base coefficient to vanish.
The remaining norm coefficient is a positive quadratic form.

-/

namespace Tetrahedral.Quartic1
open R

noncomputable def cR : ℝ := Real.sqrt 6
noncomputable def dR : ℝ := Real.sqrt (44+18*cR)

theorem cR_sq : cR^2=6 := Real.sq_sqrt (by norm_num)
theorem cR_pos : 0 < cR := Real.sqrt_pos.mpr (by norm_num)

theorem dR_sq : dR^2=44+18*cR := Real.sq_sqrt (by have := cR_pos; positivity)
theorem dR_pos : 0 < dR := Real.sqrt_pos.mpr (by have := cR_pos; positivity)

theorem conjugate_pos : 0 < 18*cR-44 := by
  apply pos_of_mul_pos_left (b:=(44+18*cR))
  · nlinarith [cR_sq]
  · have := cR_pos; positivity

/-- The real embedding `q ↦ √6`, `s ↦ √(44+18√6)`. -/
noncomputable def sig (x : R) : ℝ := (x 0:ℝ)+(x 1:ℝ)*cR+((x 2:ℝ)+(x 3:ℝ)*cR)*dR

theorem sig_mul (x y : R) : sig (x*y)=sig x*sig y := by
  have hc := cR_sq; have hd := dR_sq
  simp only [sig,mul_apply0,mul_apply1,mul_apply2,mul_apply3]; push_cast
  linear_combination ((-44)*(x 3:ℝ)*(y 3:ℝ)+(-18)*(x 3:ℝ)*(y 3:ℝ)*cR+(-18)*(x 3:ℝ)*(y 2:ℝ)+(-1)*(x 3:ℝ)*(y 1:ℝ)*dR+(-18)*(x 2:ℝ)*(y 3:ℝ)+(-1)*(x 1:ℝ)*(y 3:ℝ)*dR+(-1)*(x 1:ℝ)*(y 1:ℝ))*hc+((-1)*(x 3:ℝ)*(y 3:ℝ)*cR^2+(-1)*(x 3:ℝ)*(y 2:ℝ)*cR+(-1)*(x 2:ℝ)*(y 3:ℝ)*cR+(-1)*(x 2:ℝ)*(y 2:ℝ))*hd

noncomputable def sigHom : R →* ℝ where
  toFun := sig
  map_one' := by simp [sig]
  map_mul' := sig_mul

/-- `σ(x)·σ(τx)` is the relative norm at the real place. -/
theorem sig_tau (x : R) : sig x*sig (tau x)=(relH x:ℝ)+(relK x:ℝ)*cR := by
  have hc := cR_sq; have hd := dR_sq
  simp only [sig,tau_apply0,tau_apply1,tau_apply2,tau_apply3,relH,relK]; push_cast
  linear_combination ((-44)*(x 3:ℝ)^2+(-18)*(x 3:ℝ)^2*cR+(-36)*(x 2:ℝ)*(x 3:ℝ)+(1)*(x 1:ℝ)^2)*hc+((-1)*(x 3:ℝ)^2*cR^2+(-2)*(x 2:ℝ)*(x 3:ℝ)*cR+(-1)*(x 2:ℝ)^2)*hd

/-- The relative norm at the other place of `F` (`q ↦ −√6`). -/
theorem conj_place (x : R) :
    ((x 0:ℝ)-(x 1:ℝ)*cR)^2+(18*cR-44)*((x 2:ℝ)-(x 3:ℝ)*cR)^2=(relH x:ℝ)-(relK x:ℝ)*cR := by
  have hc := cR_sq
  simp only [relH,relK]; push_cast
  linear_combination ((-44)*(x 3:ℝ)^2+(18)*(x 3:ℝ)^2*cR+(-36)*(x 2:ℝ)*(x 3:ℝ)+(1)*(x 1:ℝ)^2)*hc

/-! ## Bounds from one real parameter -/

noncomputable def Lam : ℝ := sig rho
theorem Lam_val : Lam=9+4*cR+2*dR := by simp [Lam,sig,rho]

theorem Lam_coarse : Lam < 40 := by
  have hc : cR < 5/2 := by nlinarith [cR_sq,cR_pos]
  have hd : dR < 10 := by nlinarith [dR_sq,dR_pos]
  rw [Lam_val]; nlinarith [cR_pos,dR_pos]

theorem one_lt_Lam : 1 < Lam := by
  rw [Lam_val]; have := cR_pos; have := dR_pos; nlinarith

/-! ## The descent -/

def relNR : R →* ℤ√6 where
  toFun x := ⟨relH x,relK x⟩
  map_one' := by ext <;> rfl
  map_mul' x y := by ext <;> simp [relH_mul,relK_mul]

theorem relN_rho_zpow (m : ℤ) : relH (↑(rhoU^m):R)=1 ∧ relK (↑(rhoU^m):R)=0 := by
  have h1 : Units.map relNR rhoU=1 := by ext <;> rfl
  have := congrArg (fun z : (ℤ√6)ˣ => (z:ℤ√6)) (map_zpow (Units.map relNR) rhoU m)
  simp only [h1,one_zpow,Units.coe_map,Units.val_one] at this
  exact ⟨congrArg Zsqrtd.re this,congrArg Zsqrtd.im this⟩

/-! ## The gap -/


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
    ((v 0:ℝ)+(v 1:ℝ)*cR) Lam (2*6-1)
    hp ht hS hTau (by linarith [Lam_coarse])
  have hc1 : ((v 0:ℝ)-(v 1:ℝ)*cR)^2+(18*cR-44)*((v 2:ℝ)-(v 3:ℝ)*cR)^2=1 := by
    have hh := conj_place v; rw [hv.1,hv.2] at hh; push_cast at hh; linarith
  have hA' : ((v 0:ℝ)-(v 1:ℝ)*cR)^2≤1 := by
    have hh := mul_nonneg conjugate_pos.le (sq_nonneg ((v 2:ℝ)-(v 3:ℝ)*cR))
    linarith
  have h1 := RelativeUnitGap.trace_coefficient_zero (v 0) (v 1) cR 6 cR_sq hA hA'
  have hk := hv.2
  simp only [relK,h1,mul_zero] at hk
  have hs : (9*v 2+22*v 3)^2+2*(v 3)^2=0 := by nlinarith only [hk]
  have h3 : v 3=0 := by nlinarith [sq_nonneg (9*v 2+22*v 3)]
  have h2 : v 2=0 := by rw [h3] at hs; nlinarith
  exact hv0 ⟨h2,h3⟩

end Tetrahedral.Quartic1
