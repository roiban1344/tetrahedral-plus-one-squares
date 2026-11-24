import Tetrahedral.Quartic.D2H
import Tetrahedral.Quartic.D2Euler
import Tetrahedral.NormEleven.Certificates

namespace Tetrahedral.NormEleven.Branch2
open Tetrahedral.Quartic2
open R

def tauHom : R →* R where
  toFun := tau
  map_one' := by ext i; fin_cases i <;> rfl
  map_mul' := tau_mul

theorem tau_rhoU : Units.map tauHom rhoU=rhoU⁻¹ := by
  ext i; fin_cases i <;> rfl

theorem tau_rho_zpow (m : ℤ) : tau (↑(rhoU^m):R)=(↑(rhoU^(-m)):R) := by
  have := congrArg (fun z : Rˣ => (z:R)) (map_zpow (Units.map tauHom) rhoU m)
  simp only [tau_rhoU,inv_zpow',Units.coe_map] at this
  exact this

theorem f_tau (x : R) : f (tau x)=f x := by simp only [f,tau_apply0,tau_apply1]


theorem tau_neg (x : R) : tau (-x)= -tau x := by ext i; fin_cases i <;> simp [tau]

theorem branch_complete (n r y : ℕ) (hr : n+3=2*r^2) (hy : n^2+2=3*y^2) : n=5 ∨ n=13775 := by
  obtain ⟨ξ,hH,hK,hξ,h0⟩ := Certificates.d2 n r y hr hy
  obtain ⟨u,hu1,hu2,hcase⟩ := euler_type ξ hH hK
  obtain ⟨j,hj⟩ := rel_unit_trace u hu1 hu2
  have ttau0 : tau (tau xi0)=xi0 := by decide
  have ttau1 : tau (tau xi1)=xi1 := by decide
  -- normalise to `z = e·(ξᵢρ^m)` with `e = ±1`, `f z = 0`, `z 0 = n+3`
  obtain ⟨z,m,hz,hzf,hz0⟩ : ∃ z : R, ∃ m : ℤ,
      (z=(1:R)*(xi0*(↑(rhoU^m):R)) ∨ z=(-1:R)*(xi0*(↑(rhoU^m):R)) ∨
       z=(1:R)*(xi1*(↑(rhoU^m):R)) ∨ z=(-1:R)*(xi1*(↑(rhoU^m):R))) ∧ f z=0 ∧ z 0=(n:ℤ)+3 := by
    rcases hcase with hc|hc|hc|hc
    · refine ⟨tau ξ,-j,?_,by rw [f_tau]; exact hξ,by simp [h0]⟩
      rcases hj with e|e <;> rw [hc,e,tau_mul,ttau0]
      · left; rw [tau_rho_zpow]; ring
      · right; left; rw [tau_neg,tau_rho_zpow]; ring
    · refine ⟨ξ,j,?_,hξ,h0⟩
      rcases hj with e|e <;> rw [hc,e]
      · left; ring
      · right; left; ring
    · refine ⟨tau ξ,-j,?_,by rw [f_tau]; exact hξ,by simp [h0]⟩
      rcases hj with e|e <;> rw [hc,e,tau_mul,ttau1]
      · right; right; left; rw [tau_rho_zpow]; ring
      · right; right; right; rw [tau_neg,tau_rho_zpow]; ring
    · refine ⟨ξ,j,?_,hξ,h0⟩
      rcases hj with e|e <;> rw [hc,e]
      · right; right; left; ring
      · right; right; right; ring
  have hr2 : ∀ q : ℕ, q^2≠2 := by
    intro q hq
    have : q ≤ 1 := by nlinarith
    interval_cases q <;> simp at hq
  rcases hz with e|e|e|e <;> rw [e] at hzf hz0
  · rcases block1P m hzf with h|h|h <;> subst h
    · rw [c1_eq] at hz0; have : c1 0=13778 := rfl
      rw [this] at hz0; right; omega
    · rw [c2_eq] at hz0; have : c2 0=8 := rfl
      rw [this] at hz0; left; omega
    · rw [c3_eq] at hz0; have : c3 0=2 := rfl
      rw [this] at hz0; omega
  · rcases block2P m hzf with h <;> subst h
    rw [c4_eq] at hz0; have : c4 0= -16 := rfl
    rw [this] at hz0; omega
  · rcases block3P m hzf with h <;> subst h
    rw [c5_eq] at hz0; have : c5 0=4 := rfl
    rw [this] at hz0
    exfalso; exact hr2 r (by omega)
  · rcases block4P m hzf with h <;> subst h
    rw [c6_eq] at hz0; have : c6 0= -2 := rfl
    rw [this] at hz0; omega

end Tetrahedral.NormEleven.Branch2
