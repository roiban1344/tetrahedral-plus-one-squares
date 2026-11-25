import Tetrahedral.Quartic.D1Trace
import Tetrahedral.Binomial

/-! Arithmetic of the element of relative norm 11 for this branch.
The element itself is constructed in NormEleven.Parameters. -/

namespace Tetrahedral.Quartic1
open R

def xi0 : R := ⟨![1,1,5,-2]⟩

/-! ## The norm condition -/

def f (x : R) : ℤ := (x 0-3)^2-6*(x 1)^2+2

def Lf (y : R) : R →ₗ[ℤ] ℤ where
  toFun z := 2*(y 0-3)*z 0-12*y 1*z 1
  map_add' a b := by simp only [add_apply]; ring
  map_smul' c a := by simp only [zsmul_apply,smul_eq_mul,RingHom.id_apply]; ring

def y1 : R := ⟨![25,9,-5,0]⟩
theorem y1_eq : xi0*(↑(rhoU^(-1:ℤ)):R)=y1 := by
  rw [zpow_neg_one]; decide +kernel

end Tetrahedral.Quartic1
