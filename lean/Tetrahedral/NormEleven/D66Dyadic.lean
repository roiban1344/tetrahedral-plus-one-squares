import Tetrahedral.NormEleven.ParityDirectionData
import Tetrahedral.NormEleven.D66Square
import Tetrahedral.NormEleven.PositiveOrbitData
import Tetrahedral.OrbitReflection

namespace Tetrahedral.NormEleven.Dyadic66
open Quartic66 R

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

theorem reflected (m : ℤ) : tau (xi0*(↑(rhoU^m):R))=
    xi0*(↑(rhoU^(0-m)):R) :=
  OrbitReflection.point Positive66.tauHom rhoU
    (by ext i; fin_cases i <;> rfl) xi0 0 (by ext i; fin_cases i <;> rfl) m

/-- Odd exponents fold into the class of 1 under reflection; the required
coordinate is fixed by conjugation. -/
theorem coordinate (r : ℤ) (hr : r≠0) (m : ℤ)
    (hs : (xi0*(↑(rhoU^m):R)) 0=66*r^2)
    (hm : f (xi0*(↑(rhoU^m):R))=0) : (xi0*(↑(rhoU^m):R)) 0=66 := by
  have ho := odd r hr m hs
  let F (i : ℤ) := f (xi0*(↑(rhoU^i):R))
  let P (i : ℤ) := (xi0*(↑(rhoU^i):R)) 0
  have hF (i : ℤ) : F (0-i)=F i := by dsimp [F]; rw [← reflected]; rfl
  have hP (i : ℤ) : P (0-i)=P i := by
    change (xi0*(↑(rhoU^(0-i)):R)) 0=(xi0*(↑(rhoU^i):R)) 0
    rw [← reflected]; rfl
  have hlocal (a : ℤ) (ha : F (1+4*a)=0) : a=0 := by
    apply Differential66.unique 0 a
    change f ((xi0*(rhoU:R))*(↑((rhoU^4)^a):R))=0
    have hp : rhoU^(1+4*a)=rhoU*(rhoU^4)^a := by
      rw [zpow_add,zpow_mul,zpow_one,zpow_ofNat]
    simpa only [F,hp,Units.val_mul,mul_assoc] using ha
  have hcover : m%4=1%4 ∨ (0-m)%4=1%4 := by
    have hne : m%2≠0 := by intro h; exact ho (Int.dvd_of_emod_eq_zero h)
    omega
  have hv := OrbitReflection.value F P 0 1 4 hF hP hlocal m hcover hm
  have h1 : P 1=66 := by decide +kernel
  exact hv.trans h1

end Tetrahedral.NormEleven.Dyadic66
