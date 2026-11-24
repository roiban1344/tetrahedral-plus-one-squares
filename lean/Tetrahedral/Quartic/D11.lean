import Tetrahedral.Quartic.D11Trace
import Tetrahedral.Binomial

/-! Arithmetic of the element of relative norm 11 for this branch.
The element itself is constructed in NormEleven.Parameters. -/

namespace Tetrahedral.Quartic11
open R

def xi0 : R := ⟨![11,1,1,0]⟩

theorem relH_smul (k : ℤ) (x : R) : relH (k • x)=k^2*relH x := by
  simp only [relH,zsmul_apply]; ring
theorem relK_smul (k : ℤ) (x : R) : relK (k • x)=k^2*relK x := by
  simp only [relK,zsmul_apply]; ring

/-! ## 3. Euler's division for the ramified 11 -/

theorem cast_zero_iff (z : ℤ) : (z:ZMod 11)=0 ↔ (11:ℤ) ∣ z := ZMod.intCast_zmod_eq_zero_iff_dvd z 11

/-- `8` is not a square modulo `11` (here `96 ≡ 8`). -/
theorem qnr8 : ∀ a d : ZMod 11, a^2-96*d^2=0 → a=0 ∧ d=0 := by decide

theorem euler_mod (x : R) (hH : relH x=11) (hK : relK x=0) :
    ∃ u : R, relH u=1 ∧ relK u=0 ∧ x=u*xi0 := by
  have h11 : (11:ℤ) ∣ (x 0)^2-96*(x 3)^2 :=
    ⟨1-6*(x 1)^2+16*(x 2)^2+24*x 2*x 3,by simp only [relH] at hH; linarith⟩
  rw [← cast_zero_iff] at h11; push_cast at h11
  obtain ⟨ha,hd⟩ := qnr8 _ _ h11
  rw [cast_zero_iff] at ha hd
  obtain ⟨a,ha⟩ := ha; obtain ⟨d,hd⟩ := hd
  set P := x*tau xi0 with hP
  have hdiv : ∀ i, (11:ℤ) ∣ P i := by
    intro i; fin_cases i <;> simp [hP,xi0,tau] <;> omega
  obtain ⟨u,hu⟩ : ∃ u : R, (11:ℤ) • u=P :=
    ⟨⟨fun i => P i/11⟩,by ext i; simp only [zsmul_apply]; exact Int.mul_ediv_cancel' (hdiv i)⟩
  have e1 := congrArg relH hu; have e2 := congrArg relK hu
  have t1 : relH (tau xi0)=11 := by decide
  have t2 : relK (tau xi0)=0 := by decide
  rw [relH_smul,hP,relH_mul,hH,hK,t1,t2] at e1
  rw [relK_smul,hP,relK_mul,hH,hK,t1,t2] at e2
  refine ⟨u,by nlinarith,by nlinarith,?_⟩
  have hxi : xi0*tau xi0=(11:ℤ) • (1:R) := by ext i; fin_cases i <;> rfl
  have h11' : (11:ℤ) • (u*xi0)=(11:ℤ) • x := by
    rw [← smul_mul_assoc,hu,hP,mul_assoc,mul_comm (tau xi0) xi0,hxi,mul_smul_comm,mul_one]
  ext i
  have := congrArg (fun w : R => w i) h11'
  simp only [zsmul_apply] at this
  omega

/-! ## 4. The norm condition and the descent at the centres -/

/-- `N(A−3)+2` for the `F`-part `A = a+bq`. -/
def f (x : R) : ℤ := (x 0-3)^2-66*(x 1)^2+2

def Lf (y : R) : R →ₗ[ℤ] ℤ where
  toFun z := 2*(y 0-3)*z 0-132*y 1*z 1
  map_add' a b := by simp only [add_apply]; ring
  map_smul' c a := by simp only [zsmul_apply,smul_eq_mul,RingHom.id_apply]; ring
def Qf (z : R) : ℤ := (z 0)^2-66*(z 1)^2

theorem f_expand (y z : R) (n : ℤ) : f (y+n • z)=f y+n*Lf y z+n^2*Qf z := by
  simp only [f,Lf,Qf,add_apply,zsmul_apply,LinearMap.coe_mk,AddHom.coe_mk]; ring

/-- `x ≡ 1` modulo `M` gives `x = 1 + M•V`. -/
theorem one_add_smul (x : R) (M : ℤ) (h : ∀ i, M ∣ (x-1) i) : ∃ V : R, x=1+M • V := by
  refine ⟨⟨fun i => (x-1) i/M⟩,?_⟩
  ext i
  have := Int.mul_ediv_cancel' (h i)
  simp only [add_apply,zsmul_apply,sub_apply] at this ⊢
  linarith

theorem y1_eq : xi0*(↑(rhoU^(-1:ℤ)):R)=tau xi0 := by
  rw [zpow_neg_one]; decide +kernel


theorem f_mod (M : ℕ) (x z : R) : (f (x+(M:ℤ) • z):ZMod M)=(f x:ZMod M) := by
  simp only [f,add_apply,zsmul_apply]; push_cast; rw [ZMod.natCast_self]; ring

theorem f_neg_mod (M : ℕ) (x z : R) : (f (-(x+(M:ℤ) • z)):ZMod M)=(f (-x):ZMod M) := by
  rw [neg_add,show -((M:ℤ) • z)=(M:ℤ) • (-z) by simp,f_mod]

theorem period (M : ℕ) (P : ℕ) (V : R) (hV : (↑(rhoU^P):R)=1+(M:ℤ) • V) (x : R) (t : ℤ) :
    ∃ Z : R, x*(↑((rhoU^P)^t):R)=x+((M:ℤ)) • Z := by
  rw [zsmul_eq_mul] at hV
  obtain ⟨E,hE⟩ := first_order_zpow (rhoU^P) ((M:ℤ):R) V hV t
  exact ⟨x*((t:R)*V+((M:ℤ):R)*E),by rw [hE,zsmul_eq_mul]; ring⟩

end Tetrahedral.Quartic11
