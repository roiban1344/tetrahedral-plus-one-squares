import Tetrahedral.OrbitReflection
import Tetrahedral.NormEleven.PositiveOrbitData
import Tetrahedral.NormEleven.DyadicCertificates
import Tetrahedral.Quartic.D1Division
import Tetrahedral.NormEleven.Certificates

namespace Tetrahedral.NormEleven.Branch1
open Tetrahedral.Quartic1
open R

abbrev tauHom : R →* R := Positive1.tauHom

theorem tau_rhoU : Units.map tauHom rhoU=rhoU⁻¹ := by
  ext i; fin_cases i <;> rfl

theorem tau_rho_zpow (m : ℤ) : tau (↑(rhoU^m):R)=(↑(rhoU^(-m)):R) :=
  OrbitReflection.zpow tauHom rhoU tau_rhoU m

theorem f_tau (x : R) : f (tau x)=f x := by simp only [f,tau_apply0,tau_apply1]


theorem branch_complete (n r y : ℕ) (hr : n+3=r^2) (hy : n^2+2=6*y^2) : n=22 := by
  obtain ⟨ξ,hH,hK,hξ,h0,h1⟩ := Certificates.d1 n r y hr hy
  have hpos := (Positive1.norm_positive ξ hH hK (by
    rw [h0,h1]; push_cast; have := cR_pos; positivity)).1
  obtain ⟨u,hu1,hu2,hcase⟩ := divide_eleven ξ hH hK
  have hup : 0<sig u := by
    rcases hcase with hc|hc
    · have hh := hpos
      rw [hc,sig_mul] at hh
      exact pos_of_mul_pos_left hh Positive1.xi0_positive.1.le
    · have hh := hpos
      rw [hc,sig_mul] at hh
      exact pos_of_mul_pos_left hh Positive1.xi0_positive.2.le
  obtain ⟨j,hj⟩ := Positive1.unit_positive u hu1 hu2 hup
  obtain ⟨z,m,hz,hzh,hz0⟩ : ∃ z : R, ∃ m : ℤ,
      z=xi0*(↑(rhoU^m):R) ∧ f z=0 ∧ z 0=(n:ℤ)+3 := by
    rcases hcase with hc|hc
    · refine ⟨ξ,j,?_,hξ,h0⟩
      rw [hc,hj]; ring
    · refine ⟨tau ξ,-j,?_,by rw [f_tau]; exact hξ,by simp [h0]⟩
      have ttau : tau (tau xi0)=xi0 := by decide
      rw [hc,hj,tau_mul,ttau,tau_rho_zpow]; ring
  rw [hz] at hzh hz0
  rcases Dyadic1.roots m hzh with h|h <;> subst h
  · have : (xi0*(↑(rhoU^(0:ℤ)):R)) 0=1 := by decide
    rw [this] at hz0; omega
  · rw [y1_eq] at hz0; have : y1 0=25 := rfl
    rw [this] at hz0; omega

end Tetrahedral.NormEleven.Branch1
