import Tetrahedral.Quartic.D66
import Tetrahedral.QuadraticPolynomialSecondOrder
import Tetrahedral.NormEleven.NormPrecisionData

set_option maxRecDepth 20000
set_option maxHeartbeats 0

namespace Tetrahedral.NormEleven.Dyadic66
open Quartic66 R

def step : R := ⟨fun i => ((rho^16-1 : R) i)/16⟩
theorem step_eq : (↑(rhoU^16):R)=1+16*step := by
  have h : (↑(rhoU^16):R)=1+(16:ℤ) • step := by
    ext i; fin_cases i <;> decide +kernel
  simpa only [zsmul_eq_mul,Int.cast_ofNat] using h

def sign (sg : Fin 2) : ℤ := if sg=0 then 1 else -1
def base (sg : Fin 2) : R := if sg=0 then xi0 else -xi0
def kernel (sg : Fin 2) (x : R) : ℤ := relH x+3*sign sg*relK x

/-- The norm calculation at the fixed centre.
It is an identity before choosing the local prime. -/
theorem double_equation (sg : Fin 2) (c : ℤ) (hc : c≠0) (V : R)
    (hrel : relH (1+c • V)=1 ∧ relK (1+c • V)=0)
    (hi : phi (sign sg) ((1+c • V) 0) ((1+c • V) 1)=0) :
    44*kernel sg V+c^2*(121*(relK V)^2-11*(relH V)^2)=0 := by
  have hH : relH (1+c • V)=1+2*c*V 0+c^2*relH V := by
    simp only [relH,add_apply,zsmul_apply,one_apply]; simp; ring
  have hK : relK (1+c • V)=2*c*V 1+c^2*relK V := by
    simp only [relK,add_apply,zsmul_apply,one_apply]; simp; ring
  obtain ⟨hh,hk⟩ := hrel
  rw [hH] at hh; rw [hK] at hk
  have h0 : 2*V 0= -c*relH V := by
    have h : c*(2*V 0+c*relH V)=0 := by linear_combination hh
    have := (mul_eq_zero.mp h).resolve_left hc; linarith
  have h1 : 2*V 1= -c*relK V := by
    have h : c*(2*V 1+c*relK V)=0 := by linear_combination hk
    have := (mul_eq_zero.mp h).resolve_left hc; linarith
  have hz0 : (1+c • V) 0=1+c*V 0 := by rw [add_apply,zsmul_apply]; rfl
  have hz1 : (1+c • V) 1=c*V 1 := by rw [add_apply,zsmul_apply]; simp
  rw [hz0,hz1] at hi
  have h4 : c^2*(44*kernel sg V+c^2*(121*(relK V)^2-11*(relH V)^2))=0 := by
    fin_cases sg
    · change c^2*(44*(relH V+3*1*relK V)+c^2*(121*(relK V)^2-11*(relH V)^2))=0
      change (1*11*(c*V 1)-3)^2-11*(1+c*V 0)^2+2=0 at hi
      linear_combination 4*hi-(121*c^2*(2*V 1-c*relK V)-132*c)*h1-
        (-44*c-11*c^2*(2*V 0-c*relH V))*h0
    · change c^2*(44*(relH V+3*(-1)*relK V)+c^2*(121*(relK V)^2-11*(relH V)^2))=0
      change ((-1)*11*(c*V 1)-3)^2-11*(1+c*V 0)^2+2=0 at hi
      linear_combination 4*hi-(121*c^2*(2*V 1-c*relK V)+132*c)*h1-
        (-44*c-11*c^2*(2*V 0-c*relH V))*h0
  exact (mul_eq_zero.mp h4).resolve_left (pow_ne_zero _ hc)

theorem kernel_precision (sg : Fin 2) (a : ℤ) (E : R)
    (hE : (4:ℤ) ∣ E 0 ∧ (4:ℤ) ∣ E 1) :
    (128:ℤ) ∣ kernel sg (a • step+(8:ℤ) • E)-a^2*kernel sg step := by
  have h0 : (2:ℤ) ∣ step 0 := by decide +kernel
  have h1 : (2:ℤ) ∣ step 1 := by decide +kernel
  obtain ⟨u,hu⟩ := h0; obtain ⟨v,hv⟩ := h1
  obtain ⟨b,hb⟩ := hE.1; obtain ⟨d,hd⟩ := hE.2
  simp only [kernel,relH,relK,add_apply,zsmul_apply,hu,hv,hb,hd]
  fin_cases sg <;> simp [sign] <;> ring_nf <;> omega

/-- A double zero still forces an even exponent: its second-order coefficient
has valuation six (positive sign) or three (negative sign). -/
theorem double_unique (sg : Fin 2) (i : ℤ)
    (hi : phi (sign sg) ((↑((rhoU^16)^i):R) 0) ((↑((rhoU^16)^i):R) 1)=0) : i=0 := by
  have hrw : ∀ j : ℤ, relH (↑((rhoU^16)^j):R)=1 ∧ relK (↑((rhoU^16)^j):R)=0 := by
    intro j; have h := rel_rho (16*j); rwa [zpow_mul,zpow_ofNat] at h
  have parity (k : ℕ) (a : ℤ)
      (ha : phi (sign sg) ((↑((rhoU^16)^((2:ℤ)^k*a)):R) 0)
        ((↑((rhoU^16)^((2:ℤ)^k*a)):R) 1)=0) : 2 ∣ a := by
    obtain ⟨E,hE⟩ := dyadic_zpow_precision (rhoU^16) 3 k step (by norm_num; exact step_eq) a
    have hg := Precision66.error 3 (by decide) (rhoU^16) step
      (by norm_num; exact step_eq) hrw k a E hE
    let c : ℤ := 2^(k+4)
    let V : R := a • step+(8:ℤ) • E
    have hz : (↑((rhoU^16)^((2:ℤ)^k*a)):R)=1+c • V := by
      rw [hE]; simp only [c,V,zsmul_eq_mul]; push_cast; ring
    have hr := rel_rho (16*((2:ℤ)^k*a))
    rw [zpow_mul,zpow_ofNat,hz] at hr
    rw [hz] at ha
    have he := double_equation sg c (by dsimp [c]; positivity) V hr ha
    have hU : (4:ℤ) ∣ step 0 ∧ (4:ℤ) ∣ step 1 := by decide +kernel
    have hV : (4:ℤ) ∣ V 0 ∧ (4:ℤ) ∣ V 1 := by
      simp only [V,add_apply,zsmul_apply]
      exact ⟨(hU.1.mul_left a).add (hg.1.mul_left 8),
        (hU.2.mul_left a).add (hg.2.mul_left 8)⟩
    obtain ⟨hH,hK⟩ := Precision66.norm V hV
    obtain ⟨h,hh⟩ := hH; obtain ⟨j,hj⟩ := hK
    have hJ : (2:ℤ) ∣ 121*(relK V)^2-11*(relH V)^2 := by rw [hh,hj]; ring_nf; omega
    obtain ⟨v,hv⟩ := hJ
    have hc : (512:ℤ) ∣ c^2*(121*(relK V)^2-11*(relH V)^2) := ⟨2^(2*k)*v,by
      rw [hv]; dsimp [c]
      rw [← pow_mul,← mul_assoc,← pow_succ,show (k+4)*2+1=9+2*k by omega,pow_add]
      norm_num; ring⟩
    have hn : (512:ℤ) ∣ 44*kernel sg V := by
      have hh := dvd_neg.mpr hc
      convert hh using 1 <;> linear_combination he
    obtain ⟨b,hb⟩ := kernel_precision sg a E hg
    have hd : (512:ℤ) ∣ 44*(kernel sg V-a^2*kernel sg step) :=
      ⟨11*b,by rw [hb]; ring⟩
    have hmul : (512:ℤ) ∣ a^2*(44*kernel sg step) := by
      convert hn.sub hd using 1 <;> ring
    have hker : ∀ s : Fin 2, (44*kernel s step)%512 ∈ [256,288] := by decide +kernel
    have hm := Int.emod_eq_zero_of_dvd hmul
    rw [Int.mul_emod] at hm
    have hh := hker sg
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hh
    have hs : (2:ℤ) ∣ a^2 := by rcases hh with hh|hh <;> rw [hh] at hm <;> omega
    exact (show Prime (2:ℤ) by norm_num).dvd_of_dvd_pow hs
  have hd (k : ℕ) : (2:ℤ)^k ∣ i := by
    induction k with
    | zero => simp
    | succ k ih =>
      obtain ⟨a,ha⟩ := ih
      obtain ⟨b,hb⟩ := parity k a (by rwa [← ha])
      exact ⟨b,by rw [ha,hb,pow_succ]; ring⟩
  apply Int.eq_zero_of_dvd_of_natAbs_lt_natAbs (hd i.natAbs)
  simpa only [Int.natAbs_pow,show (2:ℤ).natAbs=2 from rfl] using i.natAbs.lt_two_pow_self

def coord0 : R →ₗ[ℤ] ℤ where
  toFun x := x 0
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
def coord1 : R →ₗ[ℤ] ℤ where
  toFun x := x 1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def centre (sg : Fin 2) (c : Fin 3) : ℤ := if sg=0 then ![0,1,-1] c else 0
def modulus (j : Fin 7) : ℤ := ![16,64,256,512,1024,2048,8192] j

theorem phase_certificate : ∀ sg : Fin 2, ∀ r : Fin 16,
    (∃ c : Fin 3, (r.val:ℤ)=centre sg c%16) ∨
    ∃ j : Fin 7, modulus j ∣ (8192:ℤ) ∧
      modulus j ∣ 16*Lf (base sg*(↑(rhoU^r.val):R)) ((base sg*(↑(rhoU^r.val):R))*step)-
        128*Lf (base sg*(↑(rhoU^r.val):R)) ((base sg*(↑(rhoU^r.val):R))*step^2) ∧
      modulus j ∣ 128*Lf (base sg*(↑(rhoU^r.val):R)) ((base sg*(↑(rhoU^r.val):R))*step^2)+
        256*Qf ((base sg*(↑(rhoU^r.val):R))*step) ∧
      ¬ modulus j ∣ f (base sg*(↑(rhoU^r.val):R)) := by decide +kernel

def simpleCentre (c : Fin 2) : ℤ := if c=0 then 1 else -1

theorem simple_unique (c : Fin 2) (i : ℤ)
    (hi : f ((xi0*(↑(rhoU^(simpleCentre c)):R))*(↑((rhoU^16)^i):R))=0) : i=0 := by
  have hz : ∀ c : Fin 2, f (xi0*(↑(rhoU^(simpleCentre c)):R))=0 := by decide +kernel
  have hk : ∀ c : Fin 2, Lf (xi0*(↑(rhoU^(simpleCentre c)):R))
      ((xi0*(↑(rhoU^(simpleCentre c)):R))*step)%64=32 := by decide +kernel
  have hr : ∀ j : ℤ, relH (↑((rhoU^16)^j):R)=1 ∧ relK (↑((rhoU^16)^j):R)=0 := by
    intro j; have h := rel_rho (16*j); rwa [zpow_mul,zpow_ofNat] at h
  have hc : simpleCentre c=Precision66.centre c := by fin_cases c <;> rfl
  apply RelativeNormPrecision.unique Precision66.X Precision66.Y 4 f
    (Lf (xi0*(↑(rhoU^(simpleCentre c)):R))) Qf (xi0*(↑(rhoU^(simpleCentre c)):R))
    (rhoU^16) 3 step (by norm_num; exact step_eq) (hz c) (f_expand _)
    (Precision66.error 3 (by decide) (rhoU^16) step (by norm_num; exact step_eq) hr)
    (by decide +kernel) (by rw [hc]; exact Precision66.linear c)
    (Precision66.quadratic _) ?_ i hi
  intro a ha
  norm_num at ha
  have h := Int.emod_eq_zero_of_dvd ha
  rw [Int.mul_emod,hk c] at h
  omega

theorem roots (sg : Fin 2) (m : ℤ) (hm : f (base sg*(↑(rhoU^m):R))=0) :
    ∃ c : Fin 3, m=centre sg c := by
  have hval : QuadraticPolynomialSecondOrder.value coord0 coord1 11 3 2=f := rfl
  have hlin : QuadraticPolynomialSecondOrder.linear coord0 coord1 11 3=
      fun x z : R => Lf x z := rfl
  have hpure : QuadraticPolynomialSecondOrder.pure coord0 coord1 11=Qf := rfl
  obtain ⟨c,hc⟩ := QuadraticPolynomialSecondOrder.phase_roots coord0 coord1 11 3 2
    rhoU 16 (by decide) 4 step (by norm_num; exact step_eq) (base sg) (centre sg) modulus
    (by norm_num only [hval,hlin,hpure,Int.reducePow,Int.reduceMul,Nat.cast_ofNat]
        exact phase_certificate sg) m (by rw [hval]; exact hm)
  norm_num at hc
  have hd : (16:ℤ) ∣ m-centre sg c := Int.dvd_of_emod_eq_zero (by
    rw [Int.sub_emod,hc,sub_self,Int.zero_emod])
  obtain ⟨a,ha⟩ := hd
  have he : m=centre sg c+16*a := by omega
  have hp : rhoU^m=rhoU^(centre sg c)*(rhoU^16)^a := by
    rw [← zpow_natCast,← zpow_mul,← zpow_add]
    norm_num; rw [← he]
  have hb : f ((base sg*(↑(rhoU^(centre sg c)):R))*(↑((rhoU^16)^a):R))=0 := by
    simpa only [hp,Units.val_mul,mul_assoc] using hm
  have ha0 : a=0 := by
    fin_cases sg
    · fin_cases c
      · apply double_unique 0 a
        simpa [centre,base,sign,f_xi0] using hb
      · apply simple_unique 0 a
        simpa [centre,base,simpleCentre] using hb
      · apply simple_unique 1 a
        simpa [centre,base,simpleCentre] using hb
    · apply double_unique 1 a
      simpa [centre,base,sign,neg_mul,f_neg_xi0] using hb
  exact ⟨c,by simpa only [ha0,mul_zero,add_zero] using he⟩

theorem positive (m : ℤ) (hm : f (xi0*(↑(rhoU^m):R))=0) : m=0 ∨ m=1 ∨ m= -1 := by
  obtain ⟨c,hc⟩ := roots 0 m hm
  fin_cases c <;> simp_all [centre]

theorem negative (m : ℤ) (hm : f (-(xi0*(↑(rhoU^m):R)))=0) : m=0 := by
  obtain ⟨c,hc⟩ := roots 1 m (by simpa [base,neg_mul] using hm)
  simpa [centre] using hc

end Tetrahedral.NormEleven.Dyadic66
