import Tetrahedral.Quartic.D11Ring
import Mathlib.NumberTheory.Zsqrtd.Basic
import Tetrahedral.Quartic.RelativeUnitGap
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
  have hDm : 0 < (22*cR-176) := conjugate_pos
  have hST : sig x-sig (tau x)=2*((x 2:ℝ)+(x 3:ℝ)*cR/11)*dR := by
    simp only [sig,tau_apply0,tau_apply1,tau_apply2,tau_apply3]; push_cast; ring
  have := UnitGap.gap (sig x) (sig (tau x)) ((x 2:ℝ)+(x 3:ℝ)*cR/11) ((x 2:ℝ)-(x 3:ℝ)*cR/11) ((x 0:ℝ)-(x 1:ℝ)*cR) dR
    (176+22*cR) (22*cR-176) ((3:ℝ)/11) hST dR_sq hDm hc1 (normB x hnz)
  have hM : 4*((3:ℝ)/11)^2*(176+22*cR)*(22*cR-176)=4*72 := by
    have := cR_sq; linear_combination (4*((3:ℝ)/11)^2*22^2)*this
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
  have ha := RelativeUnitGap.absolute_gap (sig v) (sig (tau v)) 72
    (by rw [sig_tau,hv.1,hv.2]; simp) (gap_x v hv.1 hv.2 hv0)
  have hb := RelativeUnitGap.absolute_gap (sig z) (sig (tau z)) 72
    (by rw [sig_tau,hz.1,hz.2]; simp) (gap_x z hz.1 hz.2 hz0)
  exact UnitGap.contra |sig v| |sig z| Lam 72 hlo hb1 hab (by linarith [Lam_coarse]) ha hb

end Tetrahedral.Quartic11
