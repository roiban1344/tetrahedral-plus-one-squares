import Tetrahedral.Quartic.D66Trace

/-! Arithmetic of the element of relative norm 11 for this branch.
The element itself is constructed in NormEleven.Parameters. -/

namespace Tetrahedral.Quartic66
open R

def xi0 : R := ⟨![0,1,0,0]⟩

/-! ## Division by the ramified 11 -/

theorem cast_zero_iff (z : ℤ) : (z:ZMod 11)=0 ↔ (11:ℤ) ∣ z := ZMod.intCast_zmod_eq_zero_iff_dvd z 11

/-- `8` is not a square modulo `11` (here `756 ≡ 8`). -/
theorem qnr8 : ∀ a c : ZMod 11, a^2-756*c^2=0 → a=0 ∧ c=0 := by decide

/-! ## The norm condition -/

/-- `N(A−3)+2` for the `F`-part `A = a+bq`. -/
def f (x : R) : ℤ := (x 0-3)^2-11*(x 1)^2+2

def Lf (y : R) : R →ₗ[ℤ] ℤ where
  toFun z := 2*(y 0-3)*z 0-22*y 1*z 1
  map_add' a b := by simp only [add_apply]; ring
  map_smul' c a := by simp only [zsmul_apply,smul_eq_mul,RingHom.id_apply]; ring

/-! ## The norm condition on `±√11·x` -/

theorem rel_rho (m : ℤ) : relH (↑(rhoU^m):R)=1 ∧ relK (↑(rhoU^m):R)=0 := by
  induction m using Int.induction_on with
  | zero => exact ⟨by decide,by decide⟩
  | succ n ih =>
    rw [zpow_add_one,Units.val_mul,relH_mul,relK_mul,ih.1,ih.2]
    exact ⟨by decide,by decide⟩
  | pred n ih =>
    rw [zpow_sub_one,Units.val_mul,relH_mul,relK_mul,ih.1,ih.2]
    exact ⟨by decide,by decide⟩

end Tetrahedral.Quartic66
