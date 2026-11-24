import Tetrahedral.Quartic.D11H
import Tetrahedral.NormEleven.Certificates

namespace Tetrahedral.NormEleven.Branch11
open Tetrahedral.Quartic11
open R


theorem branch_complete (n r y : ℕ) (hr : n+3=11*r^2) (hy : n^2+2=66*y^2) : n=8 := by
  obtain ⟨ξ,hH,hK,hξ,h0⟩ := Certificates.d11 n r y hr hy
  obtain ⟨u,hu1,hu2,hc⟩ := euler_mod ξ hH hK
  obtain ⟨j,hj⟩ := rel_unit_trace u hu1 hu2
  rcases hj with e|e
  · rw [hc,e,mul_comm] at hξ h0
    rcases exponentsP j hξ with h|h <;> subst h
    · have : (xi0*(↑(rhoU^(0:ℤ)):R)) 0=11 := by decide
      rw [this] at h0; omega
    · rw [y1_eq] at h0; have : (tau xi0) 0=11 := rfl
      rw [this] at h0; omega
  · rw [hc,e,neg_mul,mul_comm] at hξ
    exact absurd hξ (exponentsP_neg j)

end Tetrahedral.NormEleven.Branch11
