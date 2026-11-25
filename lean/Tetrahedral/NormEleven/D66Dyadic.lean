import Tetrahedral.NormEleven.LatticeDirectionData
import Tetrahedral.NormEleven.D66Square
import Tetrahedral.NormEleven.DyadicSimple

namespace Tetrahedral.NormEleven.Dyadic66
open Quartic66 R

abbrev step : R := Local66.step
theorem step_eq : (↑(rhoU^4):R)=1+4*step := Local66.step_eq

/-- The original square coordinate removes every even exponent, including
zero, before any condition on f is used. -/
theorem odd (r : ℤ) (hr : r≠0) (m : ℤ)
    (hs : (xi0*(↑(rhoU^m):R)) 0=66*r^2) : ¬ (2:ℤ) ∣ m := by
  rintro ⟨i,hi⟩
  have hcoord (z : R) : (xi0*z) 0=11*z 1 := by simp [xi0]
  rw [hcoord,hi,zpow_mul,zpow_ofNat] at hs
  have he := Square66.zero_phase i r (by omega)
  rw [he] at hs
  norm_num at hs
  exact hr (by nlinarith [sq_nonneg r])

theorem roots (r : ℤ) (hr : r≠0) (m : ℤ)
    (hs : (xi0*(↑(rhoU^m):R)) 0=66*r^2)
    (hm : f (xi0*(↑(rhoU^m):R))=0) : m=1 ∨ m= -1 := by
  have ho := odd r hr m hs
  obtain ⟨i,hi⟩ : ∃ i : ℤ, m=1+2*i := by
    refine ⟨m/2,?_⟩
    have hlo := Int.emod_nonneg m (by decide : (2:ℤ)≠0)
    have hhi := Int.emod_lt_of_pos m (by decide : (0:ℤ)<2)
    have hne : m%2≠0 := by intro h; exact ho (Int.dvd_of_emod_eq_zero h)
    have := Int.emod_add_mul_ediv m 2
    omega
  have he (c : Fin 2) : rhoU*((rhoU^2)^(DyadicSimple.centre c))=
      rhoU^(Local66.centre c) := by
    calc _=rhoU^((1:ℤ)+2*DyadicSimple.centre c) := by
           rw [zpow_add,zpow_mul,zpow_one,zpow_ofNat]
         _=rhoU^(Local66.centre c) := by
           congr 1; fin_cases c <;> norm_num [DyadicSimple.centre,Local66.centre]
  have h4 : (rhoU^2)^2=rhoU^4 := by rw [← pow_mul]
  have hu : ∀ c : Fin 2, ∀ a : ℤ,
      f (((xi0*(rhoU:R))*(↑((rhoU^2)^(DyadicSimple.centre c)):R))*
        (↑(((rhoU^2)^2)^a):R))=0 → a=0 := by
    intro c a ha
    rw [h4] at ha
    apply Local66.unique c a
    simpa only [mul_assoc,← Units.val_mul,he c] using ha
  have hp : rhoU^m=rhoU*(rhoU^2)^i := by
    rw [hi,zpow_add,zpow_mul,zpow_one,zpow_ofNat]
  have h := DyadicSimple.pair f (rhoU^2) (xi0*(rhoU:R)) hu i (by
    simpa only [hp,Units.val_mul,mul_assoc] using hm)
  rcases h with h|h <;> omega

end Tetrahedral.NormEleven.Dyadic66
