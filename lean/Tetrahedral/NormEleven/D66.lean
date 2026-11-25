import Tetrahedral.NormEleven.Reduction
import Tetrahedral.NormEleven.PositiveOrbitData
import Tetrahedral.NormEleven.D66Dyadic
import Tetrahedral.NormEleven.Certificates

namespace Tetrahedral.NormEleven.Branch66
open Tetrahedral.Quartic66
open R

theorem branch_complete (n r y : ℕ) (hr : n+3=66*r^2) (hy : n^2+2=11*y^2) : n=63 := by
  obtain ⟨ξ,hH,hK,hξ,h0,h1⟩ := Certificates.d66 n r y hr hy
  have hpos := (Positive66.norm_positive ξ hH hK (by
    rw [h0,h1]; push_cast; have := cR_pos; positivity)).1
  obtain ⟨j,hj⟩ := Window66.norm_eleven_positive ξ hH hK hpos
  rw [hj] at hξ h0
  have hrZ : (n:ℤ)+3=66*(r:ℤ)^2 := by exact_mod_cast hr
  have hr0 : (r:ℤ)≠0 := by intro h; rw [h] at hrZ; norm_num at hrZ; omega
  have hv := Dyadic66.coordinate r hr0 j (h0.trans hrZ) hξ
  rw [hv] at h0; omega

end Tetrahedral.NormEleven.Branch66
