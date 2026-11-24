import Tetrahedral.Quartic.D3
import Tetrahedral.Quartic.ExponentP
import Tetrahedral.Quartic.ModIter

/-!
# The exponents for d=3 by a small sieve and one Skolem prime

The residues of the norm condition on `±ξ·ρ^m` modulo [8, 73] (periods dividing 36) leave only the
classes modulo 36 of the known zeros. Each zero is simple at 73: with `ρ^36 = 1 + 73^1·U`, the
first-order term `L(y·U)` is not divisible by 73 (`exponentp_unique`). All tables are short enough
to print.
-/

namespace Tetrahedral.Quartic3
open R ModIter

abbrev VZ (M : ℕ) := ZMod M × ZMod M × ZMod M × ZMod M
def mulZ {M : ℕ} (x y : VZ M) : VZ M :=
  (x.1*y.1+2*x.2.1*y.2.1+12*(x.2.2.1*y.2.2.2+x.2.2.2*y.2.2.1),
   x.1*y.2.1+x.2.1*y.1+6*(x.2.2.1*y.2.2.1+2*x.2.2.2*y.2.2.2),
   x.1*y.2.2.1+x.2.2.1*y.1+2*(x.2.1*y.2.2.2+x.2.2.2*y.2.1),
   x.1*y.2.2.2+x.2.2.2*y.1+x.2.1*y.2.2.1+x.2.2.1*y.2.1)
def stepZ (M : ℕ) (v : VZ M) : VZ M := mulZ v (17, 12, 6, 4)
def fZ {M : ℕ} (v : VZ M) : ZMod M := (v.1-3)^2-2*v.2.1^2+2
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

theorem one_add_smulP (x : R) (M : ℤ) (h : ∀ i, M ∣ (x-1) i) : ∃ V : R, x=1+M • V := by
  refine ⟨⟨fun i => (x-1) i/M⟩,?_⟩
  ext i
  have := Int.mul_ediv_cancel' (h i)
  simp only [R.add_apply,R.zsmul_apply,R.sub_apply] at this ⊢
  linarith

theorem split_powP (m : ℤ) (P : ℕ) (hP : 0 < P) :
    rhoU^m=rhoU^((m%P).toNat)*(rhoU^P)^(m/P) := by
  have h0 : 0 ≤ m%P := Int.emod_nonneg m (by omega)
  rw [← zpow_natCast rhoU P,← zpow_mul,← zpow_natCast,← zpow_add,Int.toNat_of_nonneg h0]
  congr 1; have := Int.emod_add_mul_ediv m (P:ℤ); linarith

theorem period_of_check (M P : ℕ)
    (h : check (fun _ _ => true) (stepZ M) (1,0,0,0) P 0 (1,0,0,0)=true) :
    ∃ V : R, (↑(rhoU^P):R)=1+(M:ℤ) • V := by
  apply one_add_smulP
  have h' := castV_orbit M 1 P
  rw [castV_one,(check_spec _ _ _ _ _ _ h).2,one_mul,← castV_one M] at h'
  rw [Units.val_pow_eq_pow_val,show (↑rhoU:R)=rho from rfl]
  simp only [castV,Prod.mk.injEq] at h'
  intro i
  rw [R.sub_apply,← ZMod.intCast_eq_intCast_iff_dvd_sub]
  fin_cases i
  · exact h'.1.symm
  · exact h'.2.1.symm
  · exact h'.2.2.1.symm
  · exact h'.2.2.2.symm

theorem periodP (M : ℕ) (P : ℕ) (V : R) (hV : (↑(rhoU^P):R)=1+(M:ℤ) • V) (x : R) (t : ℤ) :
    ∃ Z : R, x*(↑((rhoU^P)^t):R)=x+((M:ℤ)) • Z := by
  rw [zsmul_eq_mul] at hV
  obtain ⟨E,hE⟩ := first_order_zpow (rhoU^P) ((M:ℤ):R) V hV t
  exact ⟨x*((t:R)*V+((M:ℤ):R)*E),by rw [hE,zsmul_eq_mul]; ring⟩

theorem table_eval (M P : ℕ) (hP : 0 < P) (V : R) (hV : (↑(rhoU^P):R)=1+(M:ℤ) • V)
    (y : R) (m : ℤ) :
    ((f (y*(↑(rhoU^m):R)):ℤ):ZMod M)=fZ ((stepZ M)^[(m%P).toNat] (castV M y)) := by
  rw [split_powP m P hP,Units.val_mul,← mul_assoc]
  obtain ⟨Z,hZ⟩ := periodP M P V hV (y*(↑(rhoU^((m%P).toNat)):R)) (m/P)
  rw [hZ,f_mod,f_cast,Units.val_pow_eq_pow_val,show (↑rhoU:R)=rho from rfl,castV_orbit]

theorem valP_nat (k : ℕ) : (↑(rhoU^(k:ℤ)):R)=rho^k := by
  rw [zpow_natCast,Units.val_pow_eq_pow_val]; rfl
theorem valP_neg (k : ℕ) : (↑(rhoU^(-(k:ℤ))):R)=rhoInv^k := by
  rw [zpow_neg,zpow_natCast,← inv_pow,Units.val_pow_eq_pow_val]; rfl

/-! ## The certificate: sieve modulo [8, 73], Skolem at 73 -/

theorem rhoP : ∃ V : R, (↑(rhoU^36):R)=1+((73:ℕ):ℤ) • V :=
  period_of_check 73 36 (by decide +kernel)
theorem rhoS8 : ∃ V : R, (↑(rhoU^4):R)=1+((8:ℕ):ℤ) • V :=
  period_of_check 8 4 (by decide +kernel)
theorem rhoS73 : ∃ V : R, (↑(rhoU^36):R)=1+((73:ℕ):ℤ) • V :=
  period_of_check 73 36 (by decide +kernel)

/-- A simple zero at `y`, unique in its class modulo 36 (`ρ^36 = 1 + 73^1·U`). -/
theorem centreP (y : R) (hy : f y=0) (hL : ¬ (5329:ℤ) ∣ Lf y (y*(rho^36-1)))
    (i : ℤ) (hi : f (y*(↑((rhoU^36)^i):R))=0) : i=0 := by
  obtain ⟨V,hV⟩ := rhoP
  have hw : (↑(rhoU^36):R)=1+((73:ℕ):R)^1*V := by rw [hV,zsmul_eq_mul]; norm_num
  refine exponentp_unique f (Lf y) Qf y (rhoU^36) 73 (by norm_num) (by norm_num) 1 (by norm_num) V hw
    (by intro z n; rw [f_expand,hy]; ring) ?_ i hi
  intro h
  apply hL
  have hs : rho^36-1=(73:ℤ) • V := by
    rw [Units.val_pow_eq_pow_val,show (↑rhoU:R)=rho from rfl] at hV
    rw [hV,add_sub_cancel_left]; norm_num
  rw [hs,mul_smul_comm,map_zsmul,smul_eq_mul]
  obtain ⟨c,hc⟩ := h
  exact ⟨c,by push_cast at hc ⊢; rw [hc]; ring⟩

def pred0_8 (k : ℕ) (v : VZ 8) : Bool := if k ∈ [0, 1, 2, 3] then true else fZ v != 0
theorem castY0_8 : castV 8 (xi0)=(3,1,1,0) := by decide +kernel
theorem tab0_8 : check pred0_8 (stepZ 8) (3,1,1,0) 4 0 (3,1,1,0)=true := by decide +kernel

def pred0_73 (k : ℕ) (v : VZ 73) : Bool := if k ∈ [0, 35] then true else fZ v != 0
theorem castY0_73 : castV 73 (xi0)=(3,1,1,0) := by decide +kernel
theorem tab0_73 : check pred0_73 (stepZ 73) (3,1,1,0) 36 0 (3,1,1,0)=true := by decide +kernel
theorem combine0 : ∀ k : Fin 36, k.val%4 ∈ [0, 1, 2, 3] → k.val%36 ∈ [0, 35] → k.val ∈ [0, 35] := by decide
def y0_0 : R := ⟨![3,1,1,0]⟩
theorem y0_0_eq : (xi0)*(↑(rhoU^(0:ℤ)):R)=y0_0 := by
  rw [show (0:ℤ)=((0:ℕ):ℤ) by norm_num,valP_nat]; decide +kernel
def y0_1 : R := ⟨![27,17,-9,-6]⟩
theorem y0_1_eq : (xi0)*(↑(rhoU^(-1:ℤ)):R)=y0_1 := by
  rw [show (-1:ℤ)=-((1:ℕ):ℤ) by norm_num,valP_neg]; decide +kernel
theorem exponentsP (m : ℤ) (hm : f (xi0*(↑(rhoU^m):R))=0) : m=0 ∨ m= -1 := by
  have hm' : f ((xi0)*(↑(rhoU^m):R))=0 := by
    rw [show (xi0)*(↑(rhoU^m):R)=xi0*(↑(rhoU^m):R) by ring]; exact hm
  set k := (m%36).toNat with hkdef
  have hkk : (k:ℤ)=m%36 := Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num))
  have hklt : k < 36 := by omega
  have z8 : k%4 ∈ [0, 1, 2, 3] := by
    obtain ⟨V,hV⟩ := rhoS8
    have ht := table_eval 8 4 (by norm_num) V hV (xi0) m
    simp only [Nat.cast_ofNat,castY0_8] at ht
    have hj := Int.toNat_of_nonneg (Int.emod_nonneg m (by norm_num : (4:ℤ)≠0))
    have hlt : (m%4).toNat < 4 := by omega
    have hp := (check_spec _ _ _ _ _ _ tab0_8).1 _ hlt
    rw [zero_add,pred0_8] at hp
    have hkj : k%4=(m%4).toNat := by omega
    rw [hkj]
    by_contra hc
    rw [if_neg hc,← ht,hm'] at hp; simp at hp
  have z73 : k%36 ∈ [0, 35] := by
    obtain ⟨V,hV⟩ := rhoS73
    have ht := table_eval 73 36 (by norm_num) V hV (xi0) m
    simp only [Nat.cast_ofNat,castY0_73] at ht
    have hj := Int.toNat_of_nonneg (Int.emod_nonneg m (by norm_num : (36:ℤ)≠0))
    have hlt : (m%36).toNat < 36 := by omega
    have hp := (check_spec _ _ _ _ _ _ tab0_73).1 _ hlt
    rw [zero_add,pred0_73] at hp
    have hkj : k%36=(m%36).toNat := by omega
    rw [hkj]
    by_contra hc
    rw [if_neg hc,← ht,hm'] at hp; simp at hp
  have hc := combine0 ⟨k,hklt⟩ z8 z73
  simp only at hc
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with hc|hc
  · obtain ⟨t,rfl⟩ : ∃ t, m=(0)+36*t := ⟨(m-(0))/36,by omega⟩
    have e : (xi0)*(↑(rhoU^((0)+36*t)):R)=y0_0*(↑((rhoU^36)^t):R) := by
      rw [← y0_0_eq,mul_assoc (xi0),← Units.val_mul,← zpow_natCast rhoU 36,← zpow_mul,← zpow_add]
      simp only [Nat.cast_ofNat]
    rw [e] at hm'
    have := centreP _ (by decide +kernel) (by decide +kernel) t hm'; omega
  · obtain ⟨t,rfl⟩ : ∃ t, m=(-1)+36*t := ⟨(m-(-1))/36,by omega⟩
    have e : (xi0)*(↑(rhoU^((-1)+36*t)):R)=y0_1*(↑((rhoU^36)^t):R) := by
      rw [← y0_1_eq,mul_assoc (xi0),← Units.val_mul,← zpow_natCast rhoU 36,← zpow_mul,← zpow_add]
      simp only [Nat.cast_ofNat]
    rw [e] at hm'
    have := centreP _ (by decide +kernel) (by decide +kernel) t hm'; omega

def pred1_8 (k : ℕ) (v : VZ 8) : Bool := if k ∈ [] then true else fZ v != 0
theorem castY1_8 : castV 8 (-xi0)=(5,7,7,0) := by decide +kernel
theorem tab1_8 : check pred1_8 (stepZ 8) (5,7,7,0) 4 0 (5,7,7,0)=true := by decide +kernel

def pred1_73 (k : ℕ) (v : VZ 73) : Bool := if k ∈ [19, 32] then true else fZ v != 0
theorem castY1_73 : castV 73 (-xi0)=(70,72,72,0) := by decide +kernel
theorem tab1_73 : check pred1_73 (stepZ 73) (70,72,72,0) 36 0 (70,72,72,0)=true := by decide +kernel
theorem combine1 : ∀ k : Fin 36, k.val%4 ∈ [] → k.val%36 ∈ [19, 32] → k.val ∈ [] := by decide
theorem exponentsP_neg (m : ℤ) : f (-(xi0*(↑(rhoU^m):R)))≠0 := by
  intro hm
  have hm' : f ((-xi0)*(↑(rhoU^m):R))=0 := by
    rw [show (-xi0)*(↑(rhoU^m):R)=-(xi0*(↑(rhoU^m):R)) by ring]; exact hm
  set k := (m%36).toNat with hkdef
  have hkk : (k:ℤ)=m%36 := Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num))
  have hklt : k < 36 := by omega
  have z8 : k%4 ∈ [] := by
    obtain ⟨V,hV⟩ := rhoS8
    have ht := table_eval 8 4 (by norm_num) V hV (-xi0) m
    simp only [Nat.cast_ofNat,castY1_8] at ht
    have hj := Int.toNat_of_nonneg (Int.emod_nonneg m (by norm_num : (4:ℤ)≠0))
    have hlt : (m%4).toNat < 4 := by omega
    have hp := (check_spec _ _ _ _ _ _ tab1_8).1 _ hlt
    rw [zero_add,pred1_8] at hp
    have hkj : k%4=(m%4).toNat := by omega
    rw [hkj]
    by_contra hc
    rw [if_neg hc,← ht,hm'] at hp; simp at hp
  have z73 : k%36 ∈ [19, 32] := by
    obtain ⟨V,hV⟩ := rhoS73
    have ht := table_eval 73 36 (by norm_num) V hV (-xi0) m
    simp only [Nat.cast_ofNat,castY1_73] at ht
    have hj := Int.toNat_of_nonneg (Int.emod_nonneg m (by norm_num : (36:ℤ)≠0))
    have hlt : (m%36).toNat < 36 := by omega
    have hp := (check_spec _ _ _ _ _ _ tab1_73).1 _ hlt
    rw [zero_add,pred1_73] at hp
    have hkj : k%36=(m%36).toNat := by omega
    rw [hkj]
    by_contra hc
    rw [if_neg hc,← ht,hm'] at hp; simp at hp
  have hc := combine1 ⟨k,hklt⟩ z8 z73
  simp only at hc
  simp at hc

end Tetrahedral.Quartic3
