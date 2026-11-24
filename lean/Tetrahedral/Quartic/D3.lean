import Tetrahedral.Quartic.D3Trace
import Tetrahedral.Binomial

/-! Arithmetic of the element of relative norm 11 for this branch.
The element itself is constructed in NormEleven.Parameters. -/

namespace Tetrahedral.Quartic3
open R

/-! ## 2. The element of relative norm 11 -/

def xi0 : R := ⟨![3,1,1,0]⟩

theorem relH_smul (k : ℤ) (x : R) : relH (k • x)=k^2*relH x := by
  simp only [relH,zsmul_apply]; ring
theorem relK_smul (k : ℤ) (x : R) : relK (k • x)=k^2*relK x := by
  simp only [relK,zsmul_apply]; ring

/-! ## 3. Euler's division modulo 11 -/

theorem cast_zero_iff (z : ℤ) : (z:ZMod 11)=0 ↔ (11:ℤ) ∣ z := ZMod.intCast_zmod_eq_zero_iff_dvd z 11

/-- `2` is not a square modulo `11`, so `11` stays prime in `ℤ[√2]`. -/
theorem qnr11 : ∀ a b : ZMod 11, a^2-2*b^2=0 → a=0 ∧ b=0 := by decide

/-! ## 4. The norm condition and the descent at the centres -/

/-- `N(A−3)+2` for the `F`-part `A = x₀+x₁q`. -/
def f (x : R) : ℤ := (x 0-3)^2-2*(x 1)^2+2

def Lf (y : R) : R →ₗ[ℤ] ℤ where
  toFun z := 2*(y 0-3)*z 0-4*y 1*z 1
  map_add' a b := by simp only [add_apply]; ring
  map_smul' c a := by simp only [zsmul_apply,smul_eq_mul,RingHom.id_apply]; ring
def Qf (z : R) : ℤ := (z 0)^2-2*(z 1)^2

theorem f_expand (y z : R) (n : ℤ) : f (y+n • z)=f y+n*Lf y z+n^2*Qf z := by
  simp only [f,Lf,Qf,add_apply,zsmul_apply,LinearMap.coe_mk,AddHom.coe_mk]; ring

def y1 : R := ⟨![27,17,-9,-6]⟩
theorem y1_eq : xi0*(↑(rhoU^(-1:ℤ)):R)=y1 := by
  rw [zpow_neg_one]; decide +kernel


theorem f_mod (M : ℕ) (x z : R) : (f (x+(M:ℤ) • z):ZMod M)=(f x:ZMod M) := by
  simp only [f,add_apply,zsmul_apply]; push_cast; rw [ZMod.natCast_self]; ring

theorem f_neg_mod (M : ℕ) (x z : R) : (f (-(x+(M:ℤ) • z)):ZMod M)=(f (-x):ZMod M) := by
  rw [neg_add,show -((M:ℤ) • z)=(M:ℤ) • (-z) by simp,f_mod]

theorem period (M : ℕ) (P : ℕ) (V : R) (hV : (↑(rhoU^P):R)=1+(M:R)*V) (x : R) (t : ℤ) :
    ∃ Z : R, x*(↑((rhoU^P)^t):R)=x+((M:ℤ)) • Z := by
  obtain ⟨E,hE⟩ := first_order_zpow (rhoU^P) (M:R) V hV t
  exact ⟨x*((t:R)*V+(M:R)*E),by rw [hE,zsmul_eq_mul]; push_cast; ring⟩

end Tetrahedral.Quartic3
