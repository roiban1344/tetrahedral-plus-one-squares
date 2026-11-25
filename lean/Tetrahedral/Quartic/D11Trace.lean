import Tetrahedral.Quartic.D11Ring
import Mathlib.NumberTheory.Zsqrtd.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Real embeddings and known unit powers (d=11)

The explicit unit and its relative norm are used to reduce norm-eleven elements.
A classification of all relative norm-one units is no longer used here.
-/

namespace Tetrahedral.Quartic11
open R

noncomputable def cR : ℝ := Real.sqrt 66
noncomputable def dR : ℝ := Real.sqrt (176+22*cR)

theorem cR_sq : cR^2=66 := Real.sq_sqrt (by norm_num)
theorem cR_pos : 0 < cR := Real.sqrt_pos.mpr (by norm_num)

theorem dR_sq : dR^2=176+22*cR := Real.sq_sqrt (by have := cR_pos; positivity)
theorem dR_pos : 0 < dR := Real.sqrt_pos.mpr (by have := cR_pos; positivity)

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


end Tetrahedral.Quartic11
