import Tetrahedral.Quartic.D11Ring
import Mathlib.NumberTheory.Zsqrtd.Basic
import Tetrahedral.Quartic.RelativeUnitGap
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Relative units from a balanced trace window (d=11)

The smaller of a reduced unit and its companion has squared real value at
most Λ. Its half-trace has square less than 2e−1; the other trace has square
at most one. Their difference forces the integral base coefficient to vanish.
The remaining norm coefficient is a positive quadratic form.

-/

namespace Tetrahedral.Quartic11
open R

noncomputable def cR : ℝ := Real.sqrt 66
noncomputable def dR : ℝ := Real.sqrt (176+22*cR)

theorem cR_sq : cR^2=66 := Real.sq_sqrt (by norm_num)
theorem cR_pos : 0 < cR := Real.sqrt_pos.mpr (by norm_num)

theorem dR_sq : dR^2=176+22*cR := Real.sq_sqrt (by have := cR_pos; positivity)
theorem dR_pos : 0 < dR := Real.sqrt_pos.mpr (by have := cR_pos; positivity)

theorem conjugate_pos : 0 < 22*cR-176 := by
  apply pos_of_mul_pos_left (b:=(176+22*cR))
  · nlinarith [cR_sq]
  · have := cR_pos; positivity

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

theorem Lam_coarse : Lam < 142 := by
  have hc : cR < 9 := by nlinarith [cR_sq,cR_pos]
  have hd : dR < 20 := by nlinarith [dR_sq,dR_pos]
  have hcd : cR*dR < 180 := calc
    cR*dR < 9*dR := mul_lt_mul_of_pos_right hc dR_pos
    _ < 180 := by linarith
  rw [Lam_val]; nlinarith [cR_pos,dR_pos]

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

/-! ## The gap -/

theorem tau_rel (x : R) : relH (tau x)=relH x ∧ relK (tau x)=relK x := by
  constructor <;> simp [relH,relK,tau]

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
  apply RelativeUnitGap.generate sigHom tau
    (fun x => relH x=1 ∧ relK x=0) (fun x => x 2=0 ∧ x 3=0)
    rhoU one_lt_Lam (by change |sig (-1)|=1; simp [sig])
    (fun x z hx hz => by
      constructor <;> simp [relH_mul,relK_mul,hx.1,hx.2,hz.1,hz.2])
    (fun x hx => by rw [(tau_rel x).1,(tau_rel x).2]; exact hx)
    relN_rho_zpow
    (fun x hx => by change sig x*sig (tau x)=1; rw [sig_tau,hx.1,hx.2]; simp)
    (fun x hx => trivial_unit x hx.1 hx.2) ?_ u ⟨hH,hK⟩
  intro v hv hv0 hlo hsmall
  change 1≤|sig v| at hlo
  change |sig v|^2≤Lam at hsmall
  have ht : 2*((v 0:ℝ)+(v 1:ℝ)*cR)=sig v+sig (tau v) := by
    simp only [sig,tau_apply0,tau_apply1,tau_apply2,tau_apply3]; push_cast; ring
  have hA := RelativeUnitGap.half_trace_bound (sig v) (sig (tau v))
    ((v 0:ℝ)+(v 1:ℝ)*cR) Lam (2*66-1)
    (by rw [sig_tau,hv.1,hv.2]; simp) ht hlo hsmall (by linarith [Lam_coarse])
  have hc1 : ((v 0:ℝ)-(v 1:ℝ)*cR)^2+(22*cR-176)*((v 2:ℝ)-(v 3:ℝ)*cR/11)^2=1 := by
    have hh := conj_place v; rw [hv.1,hv.2] at hh; push_cast at hh; linarith
  have hA' : ((v 0:ℝ)-(v 1:ℝ)*cR)^2≤1 := by
    have hh := mul_nonneg conjugate_pos.le (sq_nonneg ((v 2:ℝ)-(v 3:ℝ)*cR/11))
    linarith
  have h1 := RelativeUnitGap.trace_coefficient_zero (v 0) (v 1) cR 66 cR_sq hA hA'
  have hk := hv.2
  simp only [relK,h1,mul_zero] at hk
  have hs : (11*v 2+8*v 3)^2+2*(v 3)^2=0 := by nlinarith only [hk]
  have h3 : v 3=0 := by nlinarith [sq_nonneg (11*v 2+8*v 3)]
  have h2 : v 2=0 := by rw [h3] at hs; nlinarith
  exact hv0 ⟨h2,h3⟩

end Tetrahedral.Quartic11
