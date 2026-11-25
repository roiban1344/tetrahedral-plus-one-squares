import Tetrahedral.Quartic.D2Trace
import Tetrahedral.Binomial

/-! Arithmetic of the element of relative norm 11 for this branch.
The element itself is constructed in NormEleven.Parameters. -/

namespace Tetrahedral.Quartic2
open R

def xi0 : R := ⟨![2,1,2,-1]⟩
-- The reduced norm-eleven representative, with Pell coordinate y=1.
def shiftedSeed : R := ⟨![4,1,1,-1]⟩

/-! ## The norm condition -/

def f (x : R) : ℤ := (x 0-3)^2-3*(x 1)^2+2

def Lf (y : R) : R →ₗ[ℤ] ℤ where
  toFun z := 2*(y 0-3)*z 0-6*y 1*z 1
  map_add' a b := by simp only [add_apply]; ring
  map_smul' c a := by simp only [zsmul_apply,smul_eq_mul,RingHom.id_apply]; ring

theorem val_zpow_nat (k : ℕ) : (↑(rhoU^(k:ℤ)):R)=rho^k := by
  rw [zpow_natCast,Units.val_pow_eq_pow_val]; rfl
theorem val_zpow_neg (k : ℕ) : (↑(rhoU^(-(k:ℤ))):R)=rhoInv^k := by
  rw [zpow_neg,zpow_natCast,← inv_pow,Units.val_pow_eq_pow_val]; rfl

/-! The three zeros of the norm condition used in the classification. -/

def c1 : R := ⟨![13778,7953,-2158,-1245]⟩
theorem c1_eq : (1:R)*(xi0*(↑(rhoU^(-4:ℤ)):R))=c1 := by
  rw [show ((-4:ℤ))=-((4:ℕ):ℤ) by norm_num,val_zpow_neg]; decide +kernel
def c2 : R := ⟨![8,3,-2,0]⟩
theorem c2_eq : (1:R)*(xi0*(↑(rhoU^(-1:ℤ)):R))=c2 := by
  rw [show ((-1:ℤ))=-((1:ℕ):ℤ) by norm_num,val_zpow_neg]; decide +kernel
def c3 : R := ⟨![2,1,2,-1]⟩
theorem c3_eq : (1:R)*(xi0*(↑(rhoU^(0:ℤ)):R))=c3 := by
  rw [show ((0:ℤ))=((0:ℕ):ℤ) by norm_num,val_zpow_nat]; decide +kernel
end Tetrahedral.Quartic2
