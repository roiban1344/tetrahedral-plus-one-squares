import Tetrahedral.Quartic.D66Trace
import Tetrahedral.Quartic.ExponentP
import Tetrahedral.Quartic.ModIter

/-! Arithmetic of the element of relative norm 11 for this branch.
The element itself is constructed in NormEleven.Parameters. -/

namespace Tetrahedral.Quartic66
open R ModIter

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

theorem one_add_smul (x : R) (M : ℤ) (h : ∀ i, M ∣ (x-1) i) : ∃ V : R, x=1+M • V := by
  refine ⟨⟨fun i => (x-1) i/M⟩,?_⟩
  ext i
  have := Int.mul_ediv_cancel' (h i)
  simp only [add_apply,zsmul_apply,sub_apply] at this ⊢
  linarith

theorem f_mod (M : ℕ) (x z : R) : (f (x+(M:ℤ) • z):ZMod M)=(f x:ZMod M) := by
  simp only [f,add_apply,zsmul_apply]; push_cast; rw [ZMod.natCast_self]; ring

theorem period (M : ℕ) (P : ℕ) (V : R) (hV : (↑(rhoU^P):R)=1+(M:ℤ) • V) (x : R) (t : ℤ) :
    ∃ Z : R, x*(↑((rhoU^P)^t):R)=x+((M:ℤ)) • Z := by
  rw [zsmul_eq_mul] at hV
  obtain ⟨E,hE⟩ := first_order_zpow (rhoU^P) ((M:ℤ):R) V hV t
  exact ⟨x*((t:R)*V+((M:ℤ):R)*E),by rw [hE,zsmul_eq_mul]; ring⟩

theorem split_pow (m : ℤ) (P : ℕ) (hP : 0 < P) :
    rhoU^m=rhoU^((m%P).toNat)*(rhoU^P)^(m/P) := by
  have h0 : 0 ≤ m%P := Int.emod_nonneg m (by omega)
  rw [← zpow_natCast rhoU P,← zpow_mul,← zpow_natCast,← zpow_add,Int.toNat_of_nonneg h0]
  congr 1; have := Int.emod_add_mul_ediv m (P:ℤ); linarith

/-! ## 5. Orbits modulo `M`, by iteration -/

abbrev VZ (M : ℕ) := ZMod M × ZMod M × ZMod M × ZMod M

def mulZ {M : ℕ} (x y : VZ M) : VZ M :=
  (8316*x.2.2.2*y.2.2.2+2508*x.2.2.2*y.2.2.1+2508*x.2.2.1*y.2.2.2+756*x.2.2.1*y.2.2.1
      +11*x.2.1*y.2.1+x.1*y.1,
   2508*x.2.2.2*y.2.2.2+756*x.2.2.2*y.2.2.1+756*x.2.2.1*y.2.2.2+228*x.2.2.1*y.2.2.1
      +x.2.1*y.1+x.1*y.2.1,
   11*x.2.2.2*y.2.1+x.2.2.1*y.1+11*x.2.1*y.2.2.2+x.1*y.2.2.1,
   x.2.2.2*y.1+x.2.2.1*y.2.1+x.2.1*y.2.2.1+x.1*y.2.2.2)
def stepZ (M : ℕ) (v : VZ M) : VZ M := mulZ v (19,6,1,0)
def fZ {M : ℕ} (v : VZ M) : ZMod M := (v.1-3)^2-11*v.2.1^2+2
def castV (M : ℕ) (x : R) : VZ M := ((x 0:ZMod M),(x 1:ZMod M),(x 2:ZMod M),(x 3:ZMod M))

theorem castV_mul (M : ℕ) (x y : R) : castV M (x*y)=mulZ (castV M x) (castV M y) := by
  simp only [castV,mulZ,mul_apply0,mul_apply1,mul_apply2,mul_apply3,Prod.mk.injEq]
  push_cast
  refine ⟨by ring,by ring,by ring,by ring⟩

theorem f_cast (M : ℕ) (x : R) : ((f x:ℤ):ZMod M)=fZ (castV M x) := by
  simp only [f,fZ,castV]; push_cast; ring

theorem castV_orbit (M : ℕ) (z : R) (k : ℕ) :
    castV M (z*rho^k)=(stepZ M)^[k] (castV M z) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ,← mul_assoc,castV_mul,ih,Function.iterate_succ_apply']
    simp only [stepZ,castV,rho]; norm_num

theorem castV_one (M : ℕ) : castV M 1=(1,0,0,0) := by simp [castV]
theorem castV_xi0 (M : ℕ) : castV M xi0=(0,1,0,0) := by simp [castV,xi0]
theorem castV_negxi0 (M : ℕ) : castV M (-xi0)=(0,-1,0,0) := by simp [castV,xi0]

theorem period_of_check (M P : ℕ)
    (h : check (fun _ _ => true) (stepZ M) (1,0,0,0) P 0 (1,0,0,0)=true) :
    ∃ V : R, (↑(rhoU^P):R)=1+(M:ℤ) • V := by
  apply one_add_smul
  have h' := castV_orbit M 1 P
  rw [castV_one,(check_spec _ _ _ _ _ _ h).2,one_mul,← castV_one M] at h'
  rw [Units.val_pow_eq_pow_val,show (↑rhoU:R)=rho from rfl]
  simp only [castV,Prod.mk.injEq] at h'
  intro i
  rw [sub_apply,← ZMod.intCast_eq_intCast_iff_dvd_sub]
  fin_cases i
  · exact h'.1.symm
  · exact h'.2.1.symm
  · exact h'.2.2.1.symm
  · exact h'.2.2.2.symm

/-- The value of the norm condition modulo `M` along `y·ρ^m`, read off the iterate. -/
theorem table_eval (M P : ℕ) (hP : 0 < P) (V : R) (hV : (↑(rhoU^P):R)=1+(M:ℤ) • V)
    (y : R) (m : ℤ) :
    ((f (y*(↑(rhoU^m):R)):ℤ):ZMod M)=fZ ((stepZ M)^[(m%P).toNat] (castV M y)) := by
  rw [split_pow m P hP,Units.val_mul,← mul_assoc]
  obtain ⟨Z,hZ⟩ := period M P V hV (y*(↑(rhoU^((m%P).toNat)):R)) (m/P)
  rw [hZ,f_mod,f_cast,Units.val_pow_eq_pow_val,show (↑rhoU:R)=rho from rfl,castV_orbit]

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
