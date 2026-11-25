import Tetrahedral.Quartic.D1Ring
import Mathlib.NumberTheory.Zsqrtd.Basic
import Tetrahedral.Quartic.RelativeUnitGap
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Relative units of `ℤ[q][s]` by one real parameter (d=1)

The same norm gap and companion reduction as in the other four orders apply.
Here `Λ < 4·8` fails. Instead `Λ < 40` gives `A² < 14`, while the other
embedding gives `A'² ≤ 1`. Weighted Cauchy forces `(A−A')² < 24`, so
the integer coefficient of `√6` in `A` vanishes. The gap then excludes `A=±1`.
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

theorem sqrt_irr : Irrational (Real.sqrt ((6:ℕ):ℝ)) := by
  apply irrational_sqrt_natCast_iff.mpr
  rintro ⟨r,hr⟩
  have : r ≤ 6 := by nlinarith
  interval_cases r <;> omega

theorem normB (x : R) (hnz : ¬(x 2=0 ∧ x 3=0)) : (1:ℝ)^2 ≤ (((x 2:ℝ)+(x 3:ℝ)*cR)*((x 2:ℝ)-(x 3:ℝ)*cR))^2 := by
  have hk := UnitGap.norm_ne_zero 6 sqrt_irr (x 2) (x 3) hnz
  have h1 : (1:ℤ) ≤ ((x 2)^2-(6:ℕ)*(x 3)^2)^2 := by
    have := Int.one_le_abs hk; nlinarith [sq_abs ((x 2)^2-(6:ℕ)*(x 3)^2)]
  have e1 : ((x 2:ℝ)+(x 3:ℝ)*cR)*((x 2:ℝ)-(x 3:ℝ)*cR)=(((x 2)^2-(6:ℕ)*(x 3)^2:ℤ):ℝ) := by
    push_cast; have := cR_sq; linear_combination (-(x 3:ℝ)^2)*this
  rw [e1]; exact_mod_cast h1

theorem gap_x (x : R) (hH : relH x=1) (hK : relK x=0) (hnz : ¬(x 2=0 ∧ x 3=0)) :
    4*8 ≤ (sig x-sig (tau x))^2 := by
  have hc1 : ((x 0:ℝ)-(x 1:ℝ)*cR)^2+(18*cR-44)*((x 2:ℝ)-(x 3:ℝ)*cR)^2=1 := by
    have := conj_place x; rw [hH,hK] at this; push_cast at this; linarith
  have hDm : 0 < (18*cR-44) := conjugate_pos
  have hST : sig x-sig (tau x)=2*((x 2:ℝ)+(x 3:ℝ)*cR)*dR := by
    simp only [sig,tau_apply0,tau_apply1,tau_apply2,tau_apply3]; push_cast; ring
  have := UnitGap.gap (sig x) (sig (tau x)) ((x 2:ℝ)+(x 3:ℝ)*cR) ((x 2:ℝ)-(x 3:ℝ)*cR) ((x 0:ℝ)-(x 1:ℝ)*cR) dR
    (44+18*cR) (18*cR-44) 1 hST dR_sq hDm hc1 (normB x hnz)
  have hM : 4*1^2*(44+18*cR)*(18*cR-44)=4*8 := by
    have := cR_sq; linear_combination (4*1^2*18^2)*this
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
  have ha := RelativeUnitGap.absolute_gap (sig v) (sig (tau v)) 8
    (by rw [sig_tau,hv.1,hv.2]; simp) (gap_x v hv.1 hv.2 hv0)
  have hb := RelativeUnitGap.absolute_gap (sig z) (sig (tau z)) 8
    (by rw [sig_tau,hz.1,hz.2]; simp) (gap_x z hz.1 hz.2 hz0)
  have hA14 := RelativeUnitGap.trace_bound |sig v| |sig z| Lam hlo hb1 hab
    (by linarith [Lam_coarse]) (by linarith)
  have hvH := hv.1
  have hvK := hv.2
  let a := |sig v|
  have hc1 : ((v 0:ℝ)-(v 1:ℝ)*cR)^2+(18*cR-44)*((v 2:ℝ)-(v 3:ℝ)*cR)^2=1 := by
    have := conj_place v; rw [hvH,hvK] at this; push_cast at this; linarith
  have hDm : 0 < 18*cR-44 := conjugate_pos
  have hA'2 : ((v 0:ℝ)-(v 1:ℝ)*cR)^2 ≤ 1 := by
    have := mul_nonneg hDm.le (sq_nonneg ((v 2:ℝ)-(v 3:ℝ)*cR)); linarith
  have e2 : 2*((v 0:ℝ)+(v 1:ℝ)*cR)=sig v+(sig v)⁻¹ := by
    rw [← sig_tau_inv v hvH hvK]
    simp only [sig,tau_apply0,tau_apply1,tau_apply2,tau_apply3]; push_cast; ring
  have hA : ((v 0:ℝ)+(v 1:ℝ)*cR)^2=((a+a⁻¹)/2)^2 := by
    have h4 : (2*((v 0:ℝ)+(v 1:ℝ)*cR))^2=(a+a⁻¹)^2 := by rw [e2,UnitGap.sq_add_inv_abs]
    have : ((a+a⁻¹)/2)^2=(a+a⁻¹)^2/4 := by ring
    rw [this,← h4]; ring
  rw [← hA] at hA14
  have hdiff : ((v 0:ℝ)+(v 1:ℝ)*cR-((v 0:ℝ)-(v 1:ℝ)*cR))^2=24*(v 1:ℝ)^2 := by
    have := cR_sq; linear_combination 4*(v 1:ℝ)^2*this
  have hpar : ((v 0:ℝ)+(v 1:ℝ)*cR-((v 0:ℝ)-(v 1:ℝ)*cR))^2 ≤
      (3/2)*((v 0:ℝ)+(v 1:ℝ)*cR)^2+3*((v 0:ℝ)-(v 1:ℝ)*cR)^2 := by
    nlinarith [sq_nonneg ((v 0:ℝ)+(v 1:ℝ)*cR+2*((v 0:ℝ)-(v 1:ℝ)*cR))]
  rcases eq_or_ne (v 1) 0 with h1|h1
  · have : ((v 0:ℝ)+(v 1:ℝ)*cR)^2=((v 0:ℝ)-(v 1:ℝ)*cR)^2 := by rw [h1]; simp
    have hinv : |sig v| * |sig v|⁻¹=1 := mul_inv_cancel₀ (by linarith)
    nlinarith [hA]
  · have h1' : (1:ℝ) ≤ (v 1:ℝ)^2 := by
      have : (1:ℤ) ≤ (v 1)^2 := by have := Int.one_le_abs h1; nlinarith [sq_abs (v 1)]
      exact_mod_cast this
    linarith

end Tetrahedral.Quartic1
