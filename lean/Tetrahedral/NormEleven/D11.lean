import Tetrahedral.NormEleven.PositiveOrbitData
import Tetrahedral.NormEleven.D11Dyadic
import Tetrahedral.NormEleven.Certificates

namespace Tetrahedral.NormEleven.Branch11
open Tetrahedral.Quartic11
open R


theorem branch_complete (n r y : ℕ) (hr : n+3=11*r^2) (hy : n^2+2=66*y^2) : n=8 := by
  obtain ⟨ξ,hH,hK,hξ,h0⟩ := Certificates.d11 n r y hr hy
  obtain ⟨u,hu1,hu2,hc⟩ := divide_eleven ξ hH hK
  obtain ⟨j,hj⟩ := rel_unit_trace u hu1 hu2
  rcases hj with e|e
  · rw [hc,e,mul_comm] at hξ h0
    have hv := Dyadic11.coordinate j hξ
    rw [hv] at h0; omega
  · rw [hc,e,neg_mul,mul_comm,neg_apply] at h0
    have := Positive11.xi0_nonnegative j
    omega

end Tetrahedral.NormEleven.Branch11
