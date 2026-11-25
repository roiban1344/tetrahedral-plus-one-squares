import Tetrahedral.OrbitReflection
import Tetrahedral.NormEleven.PositiveOrbitData
import Tetrahedral.NormEleven.D2Dyadic
import Tetrahedral.Quartic.D2Euler
import Tetrahedral.NormEleven.Certificates

namespace Tetrahedral.NormEleven.Branch2
open Tetrahedral.Quartic2
open R

abbrev tauHom : R →* R := Positive2.tauHom

theorem tau_rhoU : Units.map tauHom rhoU=rhoU⁻¹ := by
  ext i; fin_cases i <;> rfl

theorem tau_rho_zpow (m : ℤ) : tau (↑(rhoU^m):R)=(↑(rhoU^(-m)):R) :=
  OrbitReflection.zpow tauHom rhoU tau_rhoU m

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
  have hrZ : (n:ℤ)+3=2*(r:ℤ)^2 := by exact_mod_cast hr
  rcases hz with e|e|e|e <;> rw [e] at hzf hz0
  · rcases Dyadic2.roots m (by simpa only [one_mul] using hzf) with h|h|h <;> subst h
    · rw [c3_eq] at hz0; have : c3 0=2 := rfl
      rw [this] at hz0; omega
    · rw [c1_eq] at hz0; have : c1 0=13778 := rfl
      rw [this] at hz0; right; omega
    · rw [c2_eq] at hz0; have : c2 0=8 := rfl
      rw [this] at hz0; left; omega
  · have := Positive2.xi0_nonnegative m
    simp only [neg_one_mul,neg_apply] at hz0
    omega
  · exact (Dyadic2.exclude r m (by simpa only [one_mul] using hzf)
      (by simpa only [one_mul] using hz0.trans hrZ)).elim
  · have := Positive2.xi1_nonnegative m
    simp only [neg_one_mul,neg_apply] at hz0
    omega

end Tetrahedral.NormEleven.Branch2
