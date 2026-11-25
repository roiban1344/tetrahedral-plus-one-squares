import Tetrahedral.Quartic.D11Trace
import Tetrahedral.Binomial

/-! Arithmetic of the element of relative norm 11 for this branch.
The element itself is constructed in NormEleven.Parameters. -/

namespace Tetrahedral.Quartic11
open R

def xi0 : R := ⟨![11,1,1,0]⟩

/-! ## Division by the ramified 11 -/

theorem cast_zero_iff (z : ℤ) : (z:ZMod 11)=0 ↔ (11:ℤ) ∣ z := ZMod.intCast_zmod_eq_zero_iff_dvd z 11

/-! ## The norm condition -/

/-- `N(A−3)+2` for the `F`-part `A = a+bq`. -/
def f (x : R) : ℤ := (x 0-3)^2-66*(x 1)^2+2

def Lf (y : R) : R →ₗ[ℤ] ℤ where
  toFun z := 2*(y 0-3)*z 0-132*y 1*z 1
  map_add' a b := by simp only [add_apply]; ring
  map_smul' c a := by simp only [zsmul_apply,smul_eq_mul,RingHom.id_apply]; ring

theorem y1_eq : xi0*(↑(rhoU^(-1:ℤ)):R)=tau xi0 := by
  rw [zpow_neg_one]; decide +kernel

end Tetrahedral.Quartic11
