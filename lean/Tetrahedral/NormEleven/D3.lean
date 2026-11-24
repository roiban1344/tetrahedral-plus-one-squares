import Tetrahedral.Quartic.D3H
import Tetrahedral.Quartic.D3Euler
import Tetrahedral.NormEleven.Certificates

namespace Tetrahedral.NormEleven.Branch3
open Tetrahedral.Quartic3
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

theorem branch_complete (n r y : ℕ) (hr : n+3=3*r^2) (hy : n^2+2=2*y^2) : n=0 ∨ n=24 := by
  obtain ⟨ξ,hH,hK,hξ,h0⟩ := Certificates.d3 n r y hr hy
  obtain ⟨u,hu1,hu2,hcase⟩ := euler_type ξ hH hK
  obtain ⟨j,hj⟩ := rel_unit_trace u hu1 hu2
  -- reduce to `z = ±ξ₀ρ^m` with `f z = 0` and `z 0 = n+3`
  obtain ⟨z,m,hz,hzh,hz0⟩ : ∃ z : R, ∃ m : ℤ,
      (z=xi0*(↑(rhoU^m):R) ∨ z= -(xi0*(↑(rhoU^m):R))) ∧ f z=0 ∧ z 0=(n:ℤ)+3 := by
    rcases hcase with hc|hc
    · refine ⟨ξ,j,?_,hξ,h0⟩
      rcases hj with e|e <;> rw [hc,e]
      · left; ring
      · right; ring
    · refine ⟨tau ξ,-j,?_,by rw [f_tau]; exact hξ,by simp [h0]⟩
      have ttau : tau (tau xi0)=xi0 := by decide
      rcases hj with e|e <;> rw [hc,e,tau_mul,ttau]
      · left; rw [tau_rho_zpow]; ring
      · right
        have hneg : tau (-(↑(rhoU^j):R))= -tau (↑(rhoU^j):R) := by
          ext i; fin_cases i <;> simp [tau]
        rw [hneg,tau_rho_zpow]; ring
  rcases hz with e|e
  · rw [e] at hzh hz0
    rcases exponentsP m hzh with h|h <;> subst h
    · left; have : (xi0*(↑(rhoU^(0:ℤ)):R)) 0=3 := by decide
      rw [this] at hz0; omega
    · right; rw [y1_eq] at hz0; have : y1 0=27 := rfl
      rw [this] at hz0; omega
  · rw [e] at hzh; exact absurd hzh (exponentsP_neg m)

end Tetrahedral.NormEleven.Branch3
