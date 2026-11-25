import Tetrahedral.NormEleven.ParityDirectionData
import Tetrahedral.NormEleven.PositiveOrbitData
import Tetrahedral.OrbitReflection

namespace Tetrahedral.NormEleven.Dyadic11
open Quartic11 R

theorem reflected (m : ℤ) : tau (xi0*(↑(rhoU^m):R))=
    xi0*(↑(rhoU^(-1-m)):R) :=
  OrbitReflection.point Positive11.tauHom rhoU
    (by ext i; fin_cases i <;> rfl) xi0 (-1) y1_eq.symm m

/-- Reflection preserves the required coordinate, so only one centre is needed. -/
theorem coordinate (m : ℤ) (hm : f (xi0*(↑(rhoU^m):R))=0) :
    (xi0*(↑(rhoU^m):R)) 0=11 := by
  let F (i : ℤ) := f (xi0*(↑(rhoU^i):R))
  let P (i : ℤ) := (xi0*(↑(rhoU^i):R)) 0
  have hF (i : ℤ) : F (-1-i)=F i := by dsimp [F]; rw [← reflected]; rfl
  have hP (i : ℤ) : P (-1-i)=P i := by
    change (xi0*(↑(rhoU^(-1-i)):R)) 0=(xi0*(↑(rhoU^i):R)) 0
    rw [← reflected]; rfl
  have hlocal (a : ℤ) (ha : F (0+2*a)=0) : a=0 := by
    apply Differential11.unique 0 a
    change f (xi0*(↑((rhoU^2)^a):R))=0
    have hp : rhoU^((2:ℤ)*a)=(rhoU^2)^a := by rw [zpow_mul,zpow_ofNat]
    simpa only [F,zero_add,hp] using ha
  have hcover : m%2=0%2 ∨ (-1-m)%2=0%2 := by omega
  have hv := OrbitReflection.value F P (-1) 0 2 hF hP hlocal m hcover hm
  have h0 : P 0=11 := by decide +kernel
  exact hv.trans h0

end Tetrahedral.NormEleven.Dyadic11
