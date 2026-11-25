import Tetrahedral.Quartic.D66Ring
import Mathlib.NumberTheory.Zsqrtd.Basic
import Tetrahedral.Quartic.RelativeUnitGap
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

theorem dR_sq : dR^2=756+228*cR := Real.sq_sqrt (by have := cR_pos; positivity)
theorem dR_pos : 0 < dR := Real.sqrt_pos.mpr (by have := cR_pos; positivity)

theorem conjugate_pos : 0 < 228*cR-756 := by
  apply pos_of_mul_pos_left (b:=(756+228*cR))
  · nlinarith [cR_sq]
  · have := cR_pos; positivity

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

theorem Lam_coarse : Lam < 84 := by
  have hc : cR < 4 := by nlinarith [cR_sq,cR_pos]
  have hd : dR < 41 := by nlinarith [dR_sq,dR_pos]
  rw [Lam_val]; nlinarith [cR_pos,dR_pos]

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
  have hDm : 0 < (228*cR-756) := conjugate_pos
  have hST : sig x-sig (tau x)=2*((x 2:ℝ)+(x 3:ℝ)*cR)*dR := by
    simp only [sig,tau_apply0,tau_apply1,tau_apply2,tau_apply3]; push_cast; ring
  have := UnitGap.gap (sig x) (sig (tau x)) ((x 2:ℝ)+(x 3:ℝ)*cR) ((x 2:ℝ)-(x 3:ℝ)*cR) ((x 0:ℝ)-(x 1:ℝ)*cR) dR
    (756+228*cR) (228*cR-756) 1 hST dR_sq hDm hc1 (normB x hnz)
  have hM : 4*1^2*(756+228*cR)*(228*cR-756)=4*288 := by
    have := cR_sq; linear_combination (4*1^2*228^2)*this
  linarith

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
  intro v z hv hz hv0 hz0 hlo hb1 hab
  change 1≤|sig v| at hlo
  change 1≤|sig z| at hb1
  change |sig v| * |sig z|=Lam at hab
  have ha := RelativeUnitGap.absolute_gap (sig v) (sig (tau v)) 288
    (by rw [sig_tau,hv.1,hv.2]; simp) (gap_x v hv.1 hv.2 hv0)
  have hb := RelativeUnitGap.absolute_gap (sig z) (sig (tau z)) 288
    (by rw [sig_tau,hz.1,hz.2]; simp) (gap_x z hz.1 hz.2 hz0)
  exact UnitGap.contra |sig v| |sig z| Lam 288 hlo hb1 hab (by linarith [Lam_coarse]) ha hb

end Tetrahedral.Quartic66
