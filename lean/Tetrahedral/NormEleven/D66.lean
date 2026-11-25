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
  obtain ⟨u,hu1,hu2,hc⟩ := divide_eleven ξ hH hK
  have hup : 0<sig u := by
    have hh := hpos
    rw [hc,sig_mul] at hh
    exact pos_of_mul_pos_left hh Positive66.xi0_positive.1.le
  obtain ⟨j,hj⟩ := Positive66.unit_positive u hu1 hu2 hup
  rw [hc,hj,mul_comm] at hξ h0
  have hrZ : (n:ℤ)+3=66*(r:ℤ)^2 := by exact_mod_cast hr
  have hr0 : (r:ℤ)≠0 := by intro h; rw [h] at hrZ; norm_num at hrZ; omega
  have hv := Dyadic66.coordinate r hr0 j (h0.trans hrZ) hξ
  rw [hv] at h0; omega

end Tetrahedral.NormEleven.Branch66
