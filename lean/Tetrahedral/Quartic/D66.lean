import Tetrahedral.Quartic.D66Trace

/-! Arithmetic of the element of relative norm 11 for this branch.
The element itself is constructed in NormEleven.Parameters. -/

namespace Tetrahedral.Quartic66
open R

def xi0 : R := ⟨![0,1,0,0]⟩

theorem relH_smul (k : ℤ) (x : R) : relH (k • x)=k^2*relH x := by
  simp only [relH,zsmul_apply]; ring
theorem relK_smul (k : ℤ) (x : R) : relK (k • x)=k^2*relK x := by
  simp only [relK,zsmul_apply]; ring

/-! ## 3. Euler's division for the ramified 11 -/

theorem cast_zero_iff (z : ℤ) : (z:ZMod 11)=0 ↔ (11:ℤ) ∣ z := ZMod.intCast_zmod_eq_zero_iff_dvd z 11

/-- `8` is not a square modulo `11` (here `756 ≡ 8`). -/
theorem qnr8 : ∀ a c : ZMod 11, a^2-756*c^2=0 → a=0 ∧ c=0 := by decide

theorem euler_mod (x : R) (hH : relH x=11) (hK : relK x=0) :
    ∃ u : R, relH u=1 ∧ relK u=0 ∧ x=u*xi0 := by
  have h11 : (11:ℤ) ∣ (x 0)^2-756*(x 2)^2 :=
    ⟨1-(x 1)^2+456*x 2*x 3+756*(x 3)^2,by simp only [relH] at hH; linarith⟩
  rw [← cast_zero_iff] at h11; push_cast at h11
  obtain ⟨ha,hc⟩ := qnr8 _ _ h11
  rw [cast_zero_iff] at ha hc
  obtain ⟨a,ha⟩ := ha; obtain ⟨c,hc⟩ := hc
  set P := x*xi0 with hP
  have hdiv : ∀ i, (11:ℤ) ∣ P i := by
    intro i; fin_cases i <;> simp [hP,xi0] <;> omega
  obtain ⟨u,hu⟩ : ∃ u : R, (11:ℤ) • u=P :=
    ⟨⟨fun i => P i/11⟩,by ext i; simp only [zsmul_apply]; exact Int.mul_ediv_cancel' (hdiv i)⟩
  have e1 := congrArg relH hu; have e2 := congrArg relK hu
  have t1 : relH xi0=11 := by decide
  have t2 : relK xi0=0 := by decide
  rw [relH_smul,hP,relH_mul,hH,hK,t1,t2] at e1
  rw [relK_smul,hP,relK_mul,hH,hK,t1,t2] at e2
  refine ⟨u,by nlinarith,by nlinarith,?_⟩
  have hxi : xi0*xi0=(11:ℤ) • (1:R) := by ext i; fin_cases i <;> rfl
  have h11' : (11:ℤ) • (u*xi0)=(11:ℤ) • x := by
    rw [← smul_mul_assoc,hu,hP,mul_assoc,hxi,mul_smul_comm,mul_one]
  ext i
  have := congrArg (fun w : R => w i) h11'
  simp only [zsmul_apply] at this
  omega

/-! ## 4. The norm condition -/

/-- `N(A−3)+2` for the `F`-part `A = a+bq`. -/
def f (x : R) : ℤ := (x 0-3)^2-11*(x 1)^2+2

def Lf (y : R) : R →ₗ[ℤ] ℤ where
  toFun z := 2*(y 0-3)*z 0-22*y 1*z 1
  map_add' a b := by simp only [add_apply]; ring
  map_smul' c a := by simp only [zsmul_apply,smul_eq_mul,RingHom.id_apply]; ring
def Qf (z : R) : ℤ := (z 0)^2-11*(z 1)^2

theorem f_expand (y z : R) (n : ℤ) : f (y+n • z)=f y+n*Lf y z+n^2*Qf z := by
  simp only [f,Lf,Qf,add_apply,zsmul_apply,LinearMap.coe_mk,AddHom.coe_mk]; ring

/-! ## 6. The norm condition on `±√11·x` -/

/-- The norm condition on `±√11·x`, in the `F`-coordinates `c₀+c₁q` of `x`. -/
def phi (sg c0 c1 : ℤ) : ℤ := (sg*11*c1-3)^2-11*c0^2+2

theorem f_xi0 (x : R) : f (xi0*x)=phi 1 (x 0) (x 1) := by
  simp [f,phi,xi0]
theorem f_neg_xi0 (x : R) : f (-(xi0*x))=phi (-1) (x 0) (x 1) := by
  simp [f,phi,xi0]

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
