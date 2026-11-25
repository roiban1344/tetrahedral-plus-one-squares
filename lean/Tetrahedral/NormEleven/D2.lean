import Tetrahedral.OrbitReflection
import Tetrahedral.NormEleven.PositiveOrbitData
import Tetrahedral.NormEleven.D2Dyadic
import Tetrahedral.Quartic.D2Division
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


theorem branch_complete (n r y : ℕ) (hr : n+3=2*r^2) (hy : n^2+2=3*y^2) : n=5 ∨ n=13775 := by
  obtain ⟨ξ,hH,hK,hξ,h0,h1⟩ := Certificates.d2 n r y hr hy
  have hpos := (Positive2.norm_positive ξ hH hK (by
    rw [h0,h1]; push_cast; have := cR_pos; positivity)).1
  obtain ⟨u,hu1,hu2,hcase⟩ := divide_eleven ξ hH hK
  have hup : 0<sig u := by
    rcases hcase with hc|hc|hc|hc
    · have hh := hpos
      rw [hc,sig_mul] at hh
      exact pos_of_mul_pos_left hh Positive2.xi0_positive.2.le
    · have hh := hpos
      rw [hc,sig_mul] at hh
      exact pos_of_mul_pos_left hh Positive2.xi0_positive.1.le
    · have hh := hpos
      rw [hc,sig_mul] at hh
      exact pos_of_mul_pos_left hh Positive2.xi1_positive.2.le
    · have hh := hpos
      rw [hc,sig_mul] at hh
      exact pos_of_mul_pos_left hh Positive2.xi1_positive.1.le
  obtain ⟨j,hj⟩ := Positive2.unit_positive u hu1 hu2 hup
  have ttau0 : tau (tau xi0)=xi0 := by decide
  have ttau1 : tau (tau xi1)=xi1 := by decide
  obtain ⟨z,m,hz,hzf,hz0⟩ : ∃ z : R, ∃ m : ℤ,
      (z=xi0*(↑(rhoU^m):R) ∨ z=xi1*(↑(rhoU^m):R)) ∧
      f z=0 ∧ z 0=(n:ℤ)+3 := by
    rcases hcase with hc|hc|hc|hc
    · refine ⟨tau ξ,-j,Or.inl ?_,by rw [f_tau]; exact hξ,by simp [h0]⟩
      rw [hc,hj,tau_mul,ttau0,tau_rho_zpow]; ring
    · refine ⟨ξ,j,Or.inl ?_,hξ,h0⟩
      rw [hc,hj]; ring
    · refine ⟨tau ξ,-j,Or.inr ?_,by rw [f_tau]; exact hξ,by simp [h0]⟩
      rw [hc,hj,tau_mul,ttau1,tau_rho_zpow]; ring
    · refine ⟨ξ,j,Or.inr ?_,hξ,h0⟩
      rw [hc,hj]; ring
  have hrZ : (n:ℤ)+3=2*(r:ℤ)^2 := by exact_mod_cast hr
  rcases hz with e|e <;> rw [e] at hzf hz0
  · rcases Dyadic2.roots m hzf with h|h|h <;> subst h
    · rw [show xi0*(↑(rhoU^(0:ℤ)):R)=c3 by simpa only [one_mul] using c3_eq] at hz0; have : c3 0=2 := rfl
      rw [this] at hz0; omega
    · rw [show xi0*(↑(rhoU^(-4:ℤ)):R)=c1 by simpa only [one_mul] using c1_eq] at hz0; have : c1 0=13778 := rfl
      rw [this] at hz0; right; omega
    · rw [show xi0*(↑(rhoU^(-1:ℤ)):R)=c2 by simpa only [one_mul] using c2_eq] at hz0; have : c2 0=8 := rfl
      rw [this] at hz0; left; omega
  · exact (Dyadic2.exclude r m hzf (hz0.trans hrZ)).elim

end Tetrahedral.NormEleven.Branch2
