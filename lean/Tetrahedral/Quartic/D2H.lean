import Tetrahedral.Quartic.D2
import Tetrahedral.Quartic.ExponentP
import Tetrahedral.Quartic.ModIter

/-!
# The exponents for d=2 by a small sieve and one Skolem prime

The residues of the norm condition on `±ξ·ρ^m` modulo [9, 97] (periods dividing 48) leave only the
classes modulo 48 of the known zeros. Each zero is simple at 3: with `ρ^48 = 1 + 3^2·U`, the
first-order term `L(y·U)` is not divisible by 3 (`exponentp_unique`). All tables are short enough
to print.
-/

namespace Tetrahedral.Quartic2
open R ModIter

abbrev VZ (M : ℕ) := ZMod M × ZMod M × ZMod M × ZMod M
def mulZ {M : ℕ} (x y : VZ M) : VZ M :=
  ((60)*x.2.2.2*y.2.2.2+(36)*x.2.2.2*y.2.2.1+(36)*x.2.2.1*y.2.2.2+(20)*x.2.2.1*y.2.2.1+(3)*x.2.1*y.2.1+(1)*x.1*y.1,
   (36)*x.2.2.2*y.2.2.2+(20)*x.2.2.2*y.2.2.1+(20)*x.2.2.1*y.2.2.2+(12)*x.2.2.1*y.2.2.1+(1)*x.2.1*y.1+(1)*x.1*y.2.1,
   (3)*x.2.2.2*y.2.1+(1)*x.2.2.1*y.1+(3)*x.2.1*y.2.2.2+(1)*x.1*y.2.2.1,
   (1)*x.2.2.2*y.1+(1)*x.2.2.1*y.2.1+(1)*x.2.1*y.2.2.1+(1)*x.1*y.2.2.2)
def stepZ (M : ℕ) (v : VZ M) : VZ M := mulZ v (3, 2, 1, 0)
def fZ {M : ℕ} (v : VZ M) : ZMod M := (v.1-3)^2-3*v.2.1^2+2
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

/-! ## The certificate: sieve modulo [9, 97], Skolem at 3 -/

theorem rhoP : ∃ V : R, (↑(rhoU^48):R)=1+((9:ℕ):ℤ) • V :=
  period_of_check 9 48 (by decide +kernel)
theorem rhoS9 : ∃ V : R, (↑(rhoU^12):R)=1+((9:ℕ):ℤ) • V :=
  period_of_check 9 12 (by decide +kernel)
theorem rhoS97 : ∃ V : R, (↑(rhoU^48):R)=1+((97:ℕ):ℤ) • V :=
  period_of_check 97 48 (by decide +kernel)

/-- A simple zero at `y`, unique in its class modulo 48 (`ρ^48 = 1 + 3^2·U`). -/
theorem centreP (y : R) (hy : f y=0) (hL : ¬ (27:ℤ) ∣ Lf y (y*(rho^48-1)))
    (i : ℤ) (hi : f (y*(↑((rhoU^48)^i):R))=0) : i=0 := by
  obtain ⟨V,hV⟩ := rhoP
  have hw : (↑(rhoU^48):R)=1+((3:ℕ):R)^2*V := by rw [hV,zsmul_eq_mul]; norm_num
  refine exponentp_unique f (Lf y) Qf y (rhoU^48) 3 (by norm_num) (by norm_num) 2 (by norm_num) V hw
    (by intro z n; rw [f_expand,hy]; ring) ?_ i hi
  intro h
  apply hL
  have hs : rho^48-1=(9:ℤ) • V := by
    rw [Units.val_pow_eq_pow_val,show (↑rhoU:R)=rho from rfl] at hV
    rw [hV,add_sub_cancel_left]; norm_num
  rw [hs,mul_smul_comm,map_zsmul,smul_eq_mul]
  obtain ⟨c,hc⟩ := h
  exact ⟨c,by push_cast at hc ⊢; rw [hc]; ring⟩

def pred0_9 (k : ℕ) (v : VZ 9) : Bool := if k ∈ [0, 7, 8, 11] then true else fZ v != 0
theorem castY0_9 : castV 9 ((1:R)*xi0)=(2,1,2,8) := by decide +kernel
theorem tab0_9 : check pred0_9 (stepZ 9) (2,1,2,8) 12 0 (2,1,2,8)=true := by decide +kernel

def pred0_97 (k : ℕ) (v : VZ 97) : Bool := if k ∈ [0, 44, 47] then true else fZ v != 0
theorem castY0_97 : castV 97 ((1:R)*xi0)=(2,1,2,96) := by decide +kernel
theorem tab0_97 : check pred0_97 (stepZ 97) (2,1,2,96) 48 0 (2,1,2,96)=true := by decide +kernel
theorem combine0 : ∀ k : Fin 48, k.val%12 ∈ [0, 7, 8, 11] → k.val%48 ∈ [0, 44, 47] → k.val ∈ [0, 44, 47] := by decide
def y0_0 : R := ⟨![13778,7953,-2158,-1245]⟩
theorem y0_0_eq : ((1:R)*xi0)*(↑(rhoU^(-4:ℤ)):R)=y0_0 := by
  rw [show (-4:ℤ)=-((4:ℕ):ℤ) by norm_num,valP_neg]; decide +kernel
def y0_1 : R := ⟨![8,3,-2,0]⟩
theorem y0_1_eq : ((1:R)*xi0)*(↑(rhoU^(-1:ℤ)):R)=y0_1 := by
  rw [show (-1:ℤ)=-((1:ℕ):ℤ) by norm_num,valP_neg]; decide +kernel
def y0_2 : R := ⟨![2,1,2,-1]⟩
theorem y0_2_eq : ((1:R)*xi0)*(↑(rhoU^(0:ℤ)):R)=y0_2 := by
  rw [show (0:ℤ)=((0:ℕ):ℤ) by norm_num,valP_nat]; decide +kernel
theorem block1P (m : ℤ) (hm : f ((1:R)*(xi0*(↑(rhoU^m):R)))=0) : m=(-4:ℤ) ∨ m=(-1:ℤ) ∨ m=(0:ℤ) := by
  have hm' : f (((1:R)*xi0)*(↑(rhoU^m):R))=0 := by
    rw [show ((1:R)*xi0)*(↑(rhoU^m):R)=(1:R)*(xi0*(↑(rhoU^m):R)) by ring]; exact hm
  set k := (m%48).toNat with hkdef
  have hkk : (k:ℤ)=m%48 := Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num))
  have hklt : k < 48 := by omega
  have z9 : k%12 ∈ [0, 7, 8, 11] := by
    obtain ⟨V,hV⟩ := rhoS9
    have ht := table_eval 9 12 (by norm_num) V hV ((1:R)*xi0) m
    simp only [Nat.cast_ofNat,castY0_9] at ht
    have hj := Int.toNat_of_nonneg (Int.emod_nonneg m (by norm_num : (12:ℤ)≠0))
    have hlt : (m%12).toNat < 12 := by omega
    have hp := (check_spec _ _ _ _ _ _ tab0_9).1 _ hlt
    rw [zero_add,pred0_9] at hp
    have hkj : k%12=(m%12).toNat := by omega
    rw [hkj]
    by_contra hc
    rw [if_neg hc,← ht,hm'] at hp; simp at hp
  have z97 : k%48 ∈ [0, 44, 47] := by
    obtain ⟨V,hV⟩ := rhoS97
    have ht := table_eval 97 48 (by norm_num) V hV ((1:R)*xi0) m
    simp only [Nat.cast_ofNat,castY0_97] at ht
    have hj := Int.toNat_of_nonneg (Int.emod_nonneg m (by norm_num : (48:ℤ)≠0))
    have hlt : (m%48).toNat < 48 := by omega
    have hp := (check_spec _ _ _ _ _ _ tab0_97).1 _ hlt
    rw [zero_add,pred0_97] at hp
    have hkj : k%48=(m%48).toNat := by omega
    rw [hkj]
    by_contra hc
    rw [if_neg hc,← ht,hm'] at hp; simp at hp
  have hc := combine0 ⟨k,hklt⟩ z9 z97
  simp only at hc
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with hc|hc|hc
  · obtain ⟨t,rfl⟩ : ∃ t, m=(0)+48*t := ⟨(m-(0))/48,by omega⟩
    have e : ((1:R)*xi0)*(↑(rhoU^((0)+48*t)):R)=y0_2*(↑((rhoU^48)^t):R) := by
      rw [← y0_2_eq,mul_assoc ((1:R)*xi0),← Units.val_mul,← zpow_natCast rhoU 48,← zpow_mul,← zpow_add]
      simp only [Nat.cast_ofNat]
    rw [e] at hm'
    have := centreP _ (by decide +kernel) (by decide +kernel) t hm'; omega
  · obtain ⟨t,rfl⟩ : ∃ t, m=(-4)+48*t := ⟨(m-(-4))/48,by omega⟩
    have e : ((1:R)*xi0)*(↑(rhoU^((-4)+48*t)):R)=y0_0*(↑((rhoU^48)^t):R) := by
      rw [← y0_0_eq,mul_assoc ((1:R)*xi0),← Units.val_mul,← zpow_natCast rhoU 48,← zpow_mul,← zpow_add]
      simp only [Nat.cast_ofNat]
    rw [e] at hm'
    have := centreP _ (by decide +kernel) (by decide +kernel) t hm'; omega
  · obtain ⟨t,rfl⟩ : ∃ t, m=(-1)+48*t := ⟨(m-(-1))/48,by omega⟩
    have e : ((1:R)*xi0)*(↑(rhoU^((-1)+48*t)):R)=y0_1*(↑((rhoU^48)^t):R) := by
      rw [← y0_1_eq,mul_assoc ((1:R)*xi0),← Units.val_mul,← zpow_natCast rhoU 48,← zpow_mul,← zpow_add]
      simp only [Nat.cast_ofNat]
    rw [e] at hm'
    have := centreP _ (by decide +kernel) (by decide +kernel) t hm'; omega

def pred1_9 (k : ℕ) (v : VZ 9) : Bool := if k ∈ [1, 2, 5, 6] then true else fZ v != 0
theorem castY1_9 : castV 9 ((-1:R)*xi0)=(7,8,7,1) := by decide +kernel
theorem tab1_9 : check pred1_9 (stepZ 9) (7,8,7,1) 12 0 (7,8,7,1)=true := by decide +kernel

def pred1_97 (k : ℕ) (v : VZ 97) : Bool := if k ∈ [1] then true else fZ v != 0
theorem castY1_97 : castV 97 ((-1:R)*xi0)=(95,96,95,1) := by decide +kernel
theorem tab1_97 : check pred1_97 (stepZ 97) (95,96,95,1) 48 0 (95,96,95,1)=true := by decide +kernel
theorem combine1 : ∀ k : Fin 48, k.val%12 ∈ [1, 2, 5, 6] → k.val%48 ∈ [1] → k.val ∈ [1] := by decide
def y1_0 : R := ⟨![-16,-11,-2,-2]⟩
theorem y1_0_eq : ((-1:R)*xi0)*(↑(rhoU^(1:ℤ)):R)=y1_0 := by
  rw [show (1:ℤ)=((1:ℕ):ℤ) by norm_num,valP_nat]; decide +kernel
theorem block2P (m : ℤ) (hm : f ((-1:R)*(xi0*(↑(rhoU^m):R)))=0) : m=(1:ℤ) := by
  have hm' : f (((-1:R)*xi0)*(↑(rhoU^m):R))=0 := by
    rw [show ((-1:R)*xi0)*(↑(rhoU^m):R)=(-1:R)*(xi0*(↑(rhoU^m):R)) by ring]; exact hm
  set k := (m%48).toNat with hkdef
  have hkk : (k:ℤ)=m%48 := Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num))
  have hklt : k < 48 := by omega
  have z9 : k%12 ∈ [1, 2, 5, 6] := by
    obtain ⟨V,hV⟩ := rhoS9
    have ht := table_eval 9 12 (by norm_num) V hV ((-1:R)*xi0) m
    simp only [Nat.cast_ofNat,castY1_9] at ht
    have hj := Int.toNat_of_nonneg (Int.emod_nonneg m (by norm_num : (12:ℤ)≠0))
    have hlt : (m%12).toNat < 12 := by omega
    have hp := (check_spec _ _ _ _ _ _ tab1_9).1 _ hlt
    rw [zero_add,pred1_9] at hp
    have hkj : k%12=(m%12).toNat := by omega
    rw [hkj]
    by_contra hc
    rw [if_neg hc,← ht,hm'] at hp; simp at hp
  have z97 : k%48 ∈ [1] := by
    obtain ⟨V,hV⟩ := rhoS97
    have ht := table_eval 97 48 (by norm_num) V hV ((-1:R)*xi0) m
    simp only [Nat.cast_ofNat,castY1_97] at ht
    have hj := Int.toNat_of_nonneg (Int.emod_nonneg m (by norm_num : (48:ℤ)≠0))
    have hlt : (m%48).toNat < 48 := by omega
    have hp := (check_spec _ _ _ _ _ _ tab1_97).1 _ hlt
    rw [zero_add,pred1_97] at hp
    have hkj : k%48=(m%48).toNat := by omega
    rw [hkj]
    by_contra hc
    rw [if_neg hc,← ht,hm'] at hp; simp at hp
  have hc := combine1 ⟨k,hklt⟩ z9 z97
  simp only at hc
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
  obtain ⟨t,rfl⟩ : ∃ t, m=(1)+48*t := ⟨(m-(1))/48,by omega⟩
  have e : ((-1:R)*xi0)*(↑(rhoU^((1)+48*t)):R)=y1_0*(↑((rhoU^48)^t):R) := by
    rw [← y1_0_eq,mul_assoc ((-1:R)*xi0),← Units.val_mul,← zpow_natCast rhoU 48,← zpow_mul,← zpow_add]
    simp only [Nat.cast_ofNat]
  rw [e] at hm'
  have := centreP _ (by decide +kernel) (by decide +kernel) t hm'; omega

def pred2_9 (k : ℕ) (v : VZ 9) : Bool := if k ∈ [2, 4, 6, 11] then true else fZ v != 0
theorem castY2_9 : castV 9 ((1:R)*xi1)=(2,3,1,0) := by decide +kernel
theorem tab2_9 : check pred2_9 (stepZ 9) (2,3,1,0) 12 0 (2,3,1,0)=true := by decide +kernel

def pred2_97 (k : ℕ) (v : VZ 97) : Bool := if k ∈ [36, 47] then true else fZ v != 0
theorem castY2_97 : castV 97 ((1:R)*xi1)=(2,3,1,0) := by decide +kernel
theorem tab2_97 : check pred2_97 (stepZ 97) (2,3,1,0) 48 0 (2,3,1,0)=true := by decide +kernel
theorem combine2 : ∀ k : Fin 48, k.val%12 ∈ [2, 4, 6, 11] → k.val%48 ∈ [36, 47] → k.val ∈ [47] := by decide
def y2_0 : R := ⟨![4,1,1,-1]⟩
theorem y2_0_eq : ((1:R)*xi1)*(↑(rhoU^(-1:ℤ)):R)=y2_0 := by
  rw [show (-1:ℤ)=-((1:ℕ):ℤ) by norm_num,valP_neg]; decide +kernel
theorem block3P (m : ℤ) (hm : f ((1:R)*(xi1*(↑(rhoU^m):R)))=0) : m=(-1:ℤ) := by
  have hm' : f (((1:R)*xi1)*(↑(rhoU^m):R))=0 := by
    rw [show ((1:R)*xi1)*(↑(rhoU^m):R)=(1:R)*(xi1*(↑(rhoU^m):R)) by ring]; exact hm
  set k := (m%48).toNat with hkdef
  have hkk : (k:ℤ)=m%48 := Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num))
  have hklt : k < 48 := by omega
  have z9 : k%12 ∈ [2, 4, 6, 11] := by
    obtain ⟨V,hV⟩ := rhoS9
    have ht := table_eval 9 12 (by norm_num) V hV ((1:R)*xi1) m
    simp only [Nat.cast_ofNat,castY2_9] at ht
    have hj := Int.toNat_of_nonneg (Int.emod_nonneg m (by norm_num : (12:ℤ)≠0))
    have hlt : (m%12).toNat < 12 := by omega
    have hp := (check_spec _ _ _ _ _ _ tab2_9).1 _ hlt
    rw [zero_add,pred2_9] at hp
    have hkj : k%12=(m%12).toNat := by omega
    rw [hkj]
    by_contra hc
    rw [if_neg hc,← ht,hm'] at hp; simp at hp
  have z97 : k%48 ∈ [36, 47] := by
    obtain ⟨V,hV⟩ := rhoS97
    have ht := table_eval 97 48 (by norm_num) V hV ((1:R)*xi1) m
    simp only [Nat.cast_ofNat,castY2_97] at ht
    have hj := Int.toNat_of_nonneg (Int.emod_nonneg m (by norm_num : (48:ℤ)≠0))
    have hlt : (m%48).toNat < 48 := by omega
    have hp := (check_spec _ _ _ _ _ _ tab2_97).1 _ hlt
    rw [zero_add,pred2_97] at hp
    have hkj : k%48=(m%48).toNat := by omega
    rw [hkj]
    by_contra hc
    rw [if_neg hc,← ht,hm'] at hp; simp at hp
  have hc := combine2 ⟨k,hklt⟩ z9 z97
  simp only at hc
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
  obtain ⟨t,rfl⟩ : ∃ t, m=(-1)+48*t := ⟨(m-(-1))/48,by omega⟩
  have e : ((1:R)*xi1)*(↑(rhoU^((-1)+48*t)):R)=y2_0*(↑((rhoU^48)^t):R) := by
    rw [← y2_0_eq,mul_assoc ((1:R)*xi1),← Units.val_mul,← zpow_natCast rhoU 48,← zpow_mul,← zpow_add]
    simp only [Nat.cast_ofNat]
  rw [e] at hm'
  have := centreP _ (by decide +kernel) (by decide +kernel) t hm'; omega

def pred3_9 (k : ℕ) (v : VZ 9) : Bool := if k ∈ [0, 5, 8, 10] then true else fZ v != 0
theorem castY3_9 : castV 9 ((-1:R)*xi1)=(7,6,8,0) := by decide +kernel
theorem tab3_9 : check pred3_9 (stepZ 9) (7,6,8,0) 12 0 (7,6,8,0)=true := by decide +kernel

def pred3_97 (k : ℕ) (v : VZ 97) : Bool := if k ∈ [0] then true else fZ v != 0
theorem castY3_97 : castV 97 ((-1:R)*xi1)=(95,94,96,0) := by decide +kernel
theorem tab3_97 : check pred3_97 (stepZ 97) (95,94,96,0) 48 0 (95,94,96,0)=true := by decide +kernel
theorem combine3 : ∀ k : Fin 48, k.val%12 ∈ [0, 5, 8, 10] → k.val%48 ∈ [0] → k.val ∈ [0] := by decide
def y3_0 : R := ⟨![-2,-3,-1,0]⟩
theorem y3_0_eq : ((-1:R)*xi1)*(↑(rhoU^(0:ℤ)):R)=y3_0 := by
  rw [show (0:ℤ)=((0:ℕ):ℤ) by norm_num,valP_nat]; decide +kernel
theorem block4P (m : ℤ) (hm : f ((-1:R)*(xi1*(↑(rhoU^m):R)))=0) : m=(0:ℤ) := by
  have hm' : f (((-1:R)*xi1)*(↑(rhoU^m):R))=0 := by
    rw [show ((-1:R)*xi1)*(↑(rhoU^m):R)=(-1:R)*(xi1*(↑(rhoU^m):R)) by ring]; exact hm
  set k := (m%48).toNat with hkdef
  have hkk : (k:ℤ)=m%48 := Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num))
  have hklt : k < 48 := by omega
  have z9 : k%12 ∈ [0, 5, 8, 10] := by
    obtain ⟨V,hV⟩ := rhoS9
    have ht := table_eval 9 12 (by norm_num) V hV ((-1:R)*xi1) m
    simp only [Nat.cast_ofNat,castY3_9] at ht
    have hj := Int.toNat_of_nonneg (Int.emod_nonneg m (by norm_num : (12:ℤ)≠0))
    have hlt : (m%12).toNat < 12 := by omega
    have hp := (check_spec _ _ _ _ _ _ tab3_9).1 _ hlt
    rw [zero_add,pred3_9] at hp
    have hkj : k%12=(m%12).toNat := by omega
    rw [hkj]
    by_contra hc
    rw [if_neg hc,← ht,hm'] at hp; simp at hp
  have z97 : k%48 ∈ [0] := by
    obtain ⟨V,hV⟩ := rhoS97
    have ht := table_eval 97 48 (by norm_num) V hV ((-1:R)*xi1) m
    simp only [Nat.cast_ofNat,castY3_97] at ht
    have hj := Int.toNat_of_nonneg (Int.emod_nonneg m (by norm_num : (48:ℤ)≠0))
    have hlt : (m%48).toNat < 48 := by omega
    have hp := (check_spec _ _ _ _ _ _ tab3_97).1 _ hlt
    rw [zero_add,pred3_97] at hp
    have hkj : k%48=(m%48).toNat := by omega
    rw [hkj]
    by_contra hc
    rw [if_neg hc,← ht,hm'] at hp; simp at hp
  have hc := combine3 ⟨k,hklt⟩ z9 z97
  simp only at hc
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
  obtain ⟨t,rfl⟩ : ∃ t, m=(0)+48*t := ⟨(m-(0))/48,by omega⟩
  have e : ((-1:R)*xi1)*(↑(rhoU^((0)+48*t)):R)=y3_0*(↑((rhoU^48)^t):R) := by
    rw [← y3_0_eq,mul_assoc ((-1:R)*xi1),← Units.val_mul,← zpow_natCast rhoU 48,← zpow_mul,← zpow_add]
    simp only [Nat.cast_ofNat]
  rw [e] at hm'
  have := centreP _ (by decide +kernel) (by decide +kernel) t hm'; omega

end Tetrahedral.Quartic2
