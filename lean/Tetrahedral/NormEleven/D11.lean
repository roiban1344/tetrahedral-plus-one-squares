import Tetrahedral.NormEleven.PositiveOrbitData
import Tetrahedral.NormEleven.D11Dyadic
import Tetrahedral.NormEleven.Certificates

namespace Tetrahedral.NormEleven.Branch11
open Tetrahedral.Quartic11
open R


theorem branch_complete (n r y : ℕ) (hr : n+3=11*r^2) (hy : n^2+2=66*y^2) : n=8 := by
  obtain ⟨ξ,hH,hK,hξ,h0,h1⟩ := Certificates.d11 n r y hr hy
  have hpos := (Positive11.norm_positive ξ hH hK (by
    rw [h0,h1]; push_cast; have := cR_pos; positivity)).1
  obtain ⟨u,hu1,hu2,hc⟩ := divide_eleven ξ hH hK
  have hup : 0<sig u := by
    have hh := hpos
    rw [hc,sig_mul] at hh
    exact pos_of_mul_pos_left hh Positive11.xi0_positive.1.le
  obtain ⟨j,hj⟩ := Positive11.unit_positive u hu1 hu2 hup
  rw [hc,hj,mul_comm] at hξ h0
  have hv := Dyadic11.coordinate j hξ
  rw [hv] at h0; omega

end Tetrahedral.NormEleven.Branch11
