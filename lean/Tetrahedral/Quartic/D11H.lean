import Tetrahedral.Quartic.D11
import Tetrahedral.Quartic.ExponentP
import Tetrahedral.Quartic.ModIter

/-!
# The exponents for d=11 by a small sieve and one Skolem prime

The residues of the norm condition on `±ξ·ρ^m` modulo [7, 19] (periods dividing 5) leave only the
classes modulo 5 of the known zeros. Each zero is simple at 7: with `ρ^5 = 1 + 7^1·U`, the
first-order term `L(y·U)` is not divisible by 7 (`exponentp_unique`). All tables are short enough
to print.
-/

namespace Tetrahedral.Quartic11
open R ModIter

abbrev VZ (M : ℕ) := ZMod M × ZMod M × ZMod M × ZMod M
def mulZ {M : ℕ} (x y : VZ M) : VZ M :=
  (x.1*y.1+66*x.2.1*y.2.1+176*x.2.2.1*y.2.2.1+132*(x.2.2.1*y.2.2.2+x.2.2.2*y.2.2.1)+96*x.2.2.2*y.2.2.2,
   x.1*y.2.1+x.2.1*y.1+22*x.2.2.1*y.2.2.1+16*(x.2.2.1*y.2.2.2+x.2.2.2*y.2.2.1)+12*x.2.2.2*y.2.2.2,
   x.1*y.2.2.1+x.2.2.1*y.1+6*(x.2.1*y.2.2.2+x.2.2.2*y.2.1),
   x.1*y.2.2.2+x.2.2.2*y.1+11*(x.2.1*y.2.2.1+x.2.2.1*y.2.1))
def stepZ (M : ℕ) (v : VZ M) : VZ M := mulZ v (33, 4, 2, 2)
def fZ {M : ℕ} (v : VZ M) : ZMod M := (v.1-3)^2-66*v.2.1^2+2
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

/-! ## The certificate: sieve modulo [7, 19], Skolem at 7 -/

theorem rhoP : ∃ V : R, (↑(rhoU^5):R)=1+((7:ℕ):ℤ) • V :=
  period_of_check 7 5 (by decide +kernel)
theorem rhoS7 : ∃ V : R, (↑(rhoU^5):R)=1+((7:ℕ):ℤ) • V :=
  period_of_check 7 5 (by decide +kernel)
theorem rhoS19 : ∃ V : R, (↑(rhoU^5):R)=1+((19:ℕ):ℤ) • V :=
  period_of_check 19 5 (by decide +kernel)

/-- A simple zero at `y`, unique in its class modulo 5 (`ρ^5 = 1 + 7^1·U`). -/
theorem centreP (y : R) (hy : f y=0) (hL : ¬ (49:ℤ) ∣ Lf y (y*(rho^5-1)))
    (i : ℤ) (hi : f (y*(↑((rhoU^5)^i):R))=0) : i=0 := by
  obtain ⟨V,hV⟩ := rhoP
  have hw : (↑(rhoU^5):R)=1+((7:ℕ):R)^1*V := by rw [hV,zsmul_eq_mul]; norm_num
  refine exponentp_unique f (Lf y) Qf y (rhoU^5) 7 (by norm_num) (by norm_num) 1 (by norm_num) V hw
    (by intro z n; rw [f_expand,hy]; ring) ?_ i hi
  intro h
  apply hL
  have hs : rho^5-1=(7:ℤ) • V := by
    rw [Units.val_pow_eq_pow_val,show (↑rhoU:R)=rho from rfl] at hV
    rw [hV,add_sub_cancel_left]; norm_num
  rw [hs,mul_smul_comm,map_zsmul,smul_eq_mul]
  obtain ⟨c,hc⟩ := h
  exact ⟨c,by push_cast at hc ⊢; rw [hc]; ring⟩

def pred0_7 (k : ℕ) (v : VZ 7) : Bool := if k ∈ [0, 1, 3, 4] then true else fZ v != 0
theorem castY0_7 : castV 7 (xi0)=(4,1,1,0) := by decide +kernel
theorem tab0_7 : check pred0_7 (stepZ 7) (4,1,1,0) 5 0 (4,1,1,0)=true := by decide +kernel

def pred0_19 (k : ℕ) (v : VZ 19) : Bool := if k ∈ [0, 2, 4] then true else fZ v != 0
theorem castY0_19 : castV 19 (xi0)=(11,1,1,0) := by decide +kernel
theorem tab0_19 : check pred0_19 (stepZ 19) (11,1,1,0) 5 0 (11,1,1,0)=true := by decide +kernel
theorem combine0 : ∀ k : Fin 5, k.val%5 ∈ [0, 1, 3, 4] → k.val%5 ∈ [0, 2, 4] → k.val ∈ [0, 4] := by decide
def y0_0 : R := ⟨![11,1,1,0]⟩
theorem y0_0_eq : (xi0)*(↑(rhoU^(0:ℤ)):R)=y0_0 := by
  rw [show (0:ℤ)=((0:ℕ):ℤ) by norm_num,valP_nat]; decide +kernel
def y0_1 : R := ⟨![11,1,-1,0]⟩
theorem y0_1_eq : (xi0)*(↑(rhoU^(-1:ℤ)):R)=y0_1 := by
  rw [show (-1:ℤ)=-((1:ℕ):ℤ) by norm_num,valP_neg]; decide +kernel
theorem exponentsP (m : ℤ) (hm : f (xi0*(↑(rhoU^m):R))=0) : m=0 ∨ m= -1 := by
  have hm' : f ((xi0)*(↑(rhoU^m):R))=0 := by
    rw [show (xi0)*(↑(rhoU^m):R)=xi0*(↑(rhoU^m):R) by ring]; exact hm
  set k := (m%5).toNat with hkdef
  have hkk : (k:ℤ)=m%5 := Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num))
  have hklt : k < 5 := by omega
  have z7 : k%5 ∈ [0, 1, 3, 4] := by
    obtain ⟨V,hV⟩ := rhoS7
    have ht := table_eval 7 5 (by norm_num) V hV (xi0) m
    simp only [Nat.cast_ofNat,castY0_7] at ht
    have hj := Int.toNat_of_nonneg (Int.emod_nonneg m (by norm_num : (5:ℤ)≠0))
    have hlt : (m%5).toNat < 5 := by omega
    have hp := (check_spec _ _ _ _ _ _ tab0_7).1 _ hlt
    rw [zero_add,pred0_7] at hp
    have hkj : k%5=(m%5).toNat := by omega
    rw [hkj]
    by_contra hc
    rw [if_neg hc,← ht,hm'] at hp; simp at hp
  have z19 : k%5 ∈ [0, 2, 4] := by
    obtain ⟨V,hV⟩ := rhoS19
    have ht := table_eval 19 5 (by norm_num) V hV (xi0) m
    simp only [Nat.cast_ofNat,castY0_19] at ht
    have hj := Int.toNat_of_nonneg (Int.emod_nonneg m (by norm_num : (5:ℤ)≠0))
    have hlt : (m%5).toNat < 5 := by omega
    have hp := (check_spec _ _ _ _ _ _ tab0_19).1 _ hlt
    rw [zero_add,pred0_19] at hp
    have hkj : k%5=(m%5).toNat := by omega
    rw [hkj]
    by_contra hc
    rw [if_neg hc,← ht,hm'] at hp; simp at hp
  have hc := combine0 ⟨k,hklt⟩ z7 z19
  simp only at hc
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with hc|hc
  · obtain ⟨t,rfl⟩ : ∃ t, m=(0)+5*t := ⟨(m-(0))/5,by omega⟩
    have e : (xi0)*(↑(rhoU^((0)+5*t)):R)=y0_0*(↑((rhoU^5)^t):R) := by
      rw [← y0_0_eq,mul_assoc (xi0),← Units.val_mul,← zpow_natCast rhoU 5,← zpow_mul,← zpow_add]
      simp only [Nat.cast_ofNat]
    rw [e] at hm'
    have := centreP _ (by decide +kernel) (by decide +kernel) t hm'; omega
  · obtain ⟨t,rfl⟩ : ∃ t, m=(-1)+5*t := ⟨(m-(-1))/5,by omega⟩
    have e : (xi0)*(↑(rhoU^((-1)+5*t)):R)=y0_1*(↑((rhoU^5)^t):R) := by
      rw [← y0_1_eq,mul_assoc (xi0),← Units.val_mul,← zpow_natCast rhoU 5,← zpow_mul,← zpow_add]
      simp only [Nat.cast_ofNat]
    rw [e] at hm'
    have := centreP _ (by decide +kernel) (by decide +kernel) t hm'; omega

def pred1_7 (k : ℕ) (v : VZ 7) : Bool := if k ∈ [] then true else fZ v != 0
theorem castY1_7 : castV 7 (-xi0)=(3,6,6,0) := by decide +kernel
theorem tab1_7 : check pred1_7 (stepZ 7) (3,6,6,0) 5 0 (3,6,6,0)=true := by decide +kernel

def pred1_19 (k : ℕ) (v : VZ 19) : Bool := if k ∈ [1, 2, 3] then true else fZ v != 0
theorem castY1_19 : castV 19 (-xi0)=(8,18,18,0) := by decide +kernel
theorem tab1_19 : check pred1_19 (stepZ 19) (8,18,18,0) 5 0 (8,18,18,0)=true := by decide +kernel
theorem combine1 : ∀ k : Fin 5, k.val%5 ∈ [] → k.val%5 ∈ [1, 2, 3] → k.val ∈ [] := by decide
theorem exponentsP_neg (m : ℤ) : f (-(xi0*(↑(rhoU^m):R)))≠0 := by
  intro hm
  have hm' : f ((-xi0)*(↑(rhoU^m):R))=0 := by
    rw [show (-xi0)*(↑(rhoU^m):R)=-(xi0*(↑(rhoU^m):R)) by ring]; exact hm
  set k := (m%5).toNat with hkdef
  have hkk : (k:ℤ)=m%5 := Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num))
  have hklt : k < 5 := by omega
  have z7 : k%5 ∈ [] := by
    obtain ⟨V,hV⟩ := rhoS7
    have ht := table_eval 7 5 (by norm_num) V hV (-xi0) m
    simp only [Nat.cast_ofNat,castY1_7] at ht
    have hj := Int.toNat_of_nonneg (Int.emod_nonneg m (by norm_num : (5:ℤ)≠0))
    have hlt : (m%5).toNat < 5 := by omega
    have hp := (check_spec _ _ _ _ _ _ tab1_7).1 _ hlt
    rw [zero_add,pred1_7] at hp
    have hkj : k%5=(m%5).toNat := by omega
    rw [hkj]
    by_contra hc
    rw [if_neg hc,← ht,hm'] at hp; simp at hp
  have z19 : k%5 ∈ [1, 2, 3] := by
    obtain ⟨V,hV⟩ := rhoS19
    have ht := table_eval 19 5 (by norm_num) V hV (-xi0) m
    simp only [Nat.cast_ofNat,castY1_19] at ht
    have hj := Int.toNat_of_nonneg (Int.emod_nonneg m (by norm_num : (5:ℤ)≠0))
    have hlt : (m%5).toNat < 5 := by omega
    have hp := (check_spec _ _ _ _ _ _ tab1_19).1 _ hlt
    rw [zero_add,pred1_19] at hp
    have hkj : k%5=(m%5).toNat := by omega
    rw [hkj]
    by_contra hc
    rw [if_neg hc,← ht,hm'] at hp; simp at hp
  have hc := combine1 ⟨k,hklt⟩ z7 z19
  simp only at hc
  simp at hc

end Tetrahedral.Quartic11
