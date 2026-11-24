import Tetrahedral.Quartic.D66P
import Tetrahedral.NormEleven.Certificates

namespace Tetrahedral.NormEleven.Branch66
open Tetrahedral.Quartic66
open R

theorem branch_complete (n r y : ℕ) (hr : n+3=66*r^2) (hy : n^2+2=11*y^2) : n=63 := by
  obtain ⟨ξ,hH,hK,hξ,h0⟩ := Certificates.d66 n r y hr hy
  obtain ⟨u,hu1,hu2,hc⟩ := euler_mod ξ hH hK
  obtain ⟨j,hj⟩ := rel_unit_trace u hu1 hu2
  rcases hj with e|e
  · rw [hc,e,mul_comm] at hξ h0
    rcases exponents89 j hξ with h|h|h <;> subst h
    · have : (xi0*(↑(rhoU^(0:ℤ)):R)) 0=0 := by decide
      rw [this] at h0; omega
    · have : (xi0*(↑(rhoU^(1:ℤ)):R)) 0=66 := by decide
      rw [this] at h0; omega
    · have : (xi0*(↑(rhoU^(-1:ℤ)):R)) 0=66 := by decide
      rw [this] at h0; omega
  · rw [hc,e,neg_mul,mul_comm] at hξ h0
    have := exponents89_neg j hξ; subst this
    have : (-(xi0*(↑(rhoU^(0:ℤ)):R))) 0=0 := by decide
    rw [this] at h0; omega

end Tetrahedral.NormEleven.Branch66
