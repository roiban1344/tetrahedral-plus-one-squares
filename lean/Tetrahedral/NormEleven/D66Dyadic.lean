import Tetrahedral.Quartic.D66
import Tetrahedral.NormEleven.TaylorObstructions

set_option maxRecDepth 20000
set_option maxHeartbeats 0

namespace Tetrahedral.NormEleven.Dyadic66
open Quartic66 R

abbrev step : R := Direction66.step
theorem step_eq : (↑(rhoU^4):R)=1+4*step := Direction66.step_eq

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

theorem kernel_precision (sg : Fin 2) (a : ℤ) (E : R) :
    (128:ℤ) ∣ kernel sg (a • step+(2:ℤ) • (step^2*E))-a^2*kernel sg step := by
  rw [Direction66.square_value]
  simp only [kernel,relH,relK,add_apply,zsmul_apply,mul_apply0,mul_apply1,mul_apply2,mul_apply3]
  fin_cases sg <;> norm_num [sign,step,Direction66.step,Direction66.square] <;> ring_nf <;> omega

theorem norm_direction (a : ℤ) (E : R) :
    let V : R := a • step+(2:ℤ) • (step^2*E)
    (4:ℤ) ∣ relH V ∧ (4:ℤ) ∣ relK V ∧ (8:ℤ) ∣ relH V-relK V := by
  dsimp only
  rw [Direction66.square_value]
  simp only [relH,relK,add_apply,zsmul_apply,mul_apply0,mul_apply1,mul_apply2,mul_apply3]
  norm_num [step,Direction66.step,Direction66.square]
  constructor
  · ring_nf; omega
  · constructor <;> ring_nf <;> omega

/-- A double zero still forces an even exponent: its second-order coefficient
has valuation six (positive sign) or three (negative sign). -/
theorem double_unique (sg : Fin 2) (i : ℤ)
    (hi : phi (sign sg) ((↑((rhoU^4)^i):R) 0) ((↑((rhoU^4)^i):R) 1)=0) : i=0 := by
  have parity (k : ℕ) (a : ℤ)
      (ha : phi (sign sg) ((↑((rhoU^4)^((2:ℤ)^k*a)):R) 0)
        ((↑((rhoU^4)^((2:ℤ)^k*a)):R) 1)=0) : 2 ∣ a := by
    obtain ⟨b,E,hE⟩ := dyadic_zpow_precision_scalar (rhoU^4) 1 k (by decide) step
      (by convert step_eq using 1 <;> ring) a
    let F : R := (b:R)+2*E
    let c : ℤ := 2^(k+2)
    let V : R := a • step+(2:ℤ) • (step^2*F)
    have hz : (↑((rhoU^4)^((2:ℤ)^k*a)):R)=1+c • V := by
      rw [hE]; simp only [c,V,F,zsmul_eq_mul]; push_cast; ring
    have hr := rel_rho (4*((2:ℤ)^k*a))
    rw [zpow_mul,zpow_ofNat,hz] at hr
    rw [hz] at ha
    have he := double_equation sg c (by dsimp [c]; positivity) V hr ha
    obtain ⟨hH,hK,hD⟩ := norm_direction a F
    obtain ⟨h,hh⟩ := hH; obtain ⟨j,hj⟩ := hK
    have hd : (2:ℤ) ∣ h-j := by rw [hh,hj] at hD; omega
    obtain ⟨d,hd⟩ := hd
    have heh : h=j+2*d := by omega
    have hJ : (32:ℤ) ∣ 121*(relK V)^2-11*(relH V)^2 := by
      change (32:ℤ) ∣ 121*(relK (a • step+(2:ℤ) • (step^2*F)))^2-
        11*(relH (a • step+(2:ℤ) • (step^2*F)))^2
      rw [hh,hj,heh]; ring_nf; omega
    obtain ⟨v,hv⟩ := hJ
    have hc : (512:ℤ) ∣ c^2*(121*(relK V)^2-11*(relH V)^2) := ⟨2^(2*k)*v,by
      rw [hv]; dsimp [c]
      rw [← pow_mul,← mul_assoc,show (32:ℤ)=2^5 by norm_num,← pow_add,
        show (k+2)*2+5=9+2*k by omega,pow_add]
      norm_num; ring⟩
    have hn : (512:ℤ) ∣ 44*kernel sg V := by
      have h := dvd_neg.mpr hc
      convert h using 1 <;> linear_combination he
    obtain ⟨b',hb'⟩ := kernel_precision sg a F
    have hd : (512:ℤ) ∣ 44*(kernel sg V-a^2*kernel sg step) :=
      ⟨11*b',by rw [hb']; ring⟩
    have hmul : (512:ℤ) ∣ a^2*(44*kernel sg step) := by
      convert hn.sub hd using 1 <;> ring
    have hker : ∀ s : Fin 2, (44*kernel s step)%512 ∈ [256,288] := by decide +kernel
    have hm := Int.emod_eq_zero_of_dvd hmul
    rw [Int.mul_emod] at hm
    have h := hker sg
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    have hs : (2:ℤ) ∣ a^2 := by rcases h with h|h <;> rw [h] at hm <;> omega
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
theorem phase_certificate : ∀ sg : Fin 2, ∀ r : Fin 4,
    (∃ c : Fin 3, (r.val:ℤ)=centre sg c%4) ∨
    ∃ j : Fin 4, base sg*(↑(rhoU^r.val):R)=Obstruction66.point j := by decide +kernel

def simpleCentre (c : Fin 2) : ℤ := if c=0 then 1 else -1

theorem simple_unique (c : Fin 2) (i : ℤ)
    (hi : f ((xi0*(↑(rhoU^(simpleCentre c)):R))*(↑((rhoU^4)^i):R))=0) : i=0 := by
  have hc : simpleCentre c=Direction66.centre c := by fin_cases c <;> rfl
  apply Direction66.unique c i
  simpa only [← hc] using hi

theorem roots (sg : Fin 2) (m : ℤ) (hm : f (base sg*(↑(rhoU^m):R))=0) :
    ∃ c : Fin 3, m=centre sg c := by
  obtain ⟨c,hc⟩ := TaylorOrbit.phase_roots f rhoU 4 (by decide) 1 step
    (by convert step_eq using 1 <;> ring) (base sg) (centre sg) (by
      intro r
      rcases phase_certificate sg r with h|⟨j,hj⟩
      · exact Or.inl h
      · right; intro a E; rw [hj]; exact Obstruction66.nonzero j a E) m hm
  norm_num at hc
  have hd : (4:ℤ) ∣ m-centre sg c := Int.dvd_of_emod_eq_zero (by
    rw [Int.sub_emod,hc,sub_self,Int.zero_emod])
  obtain ⟨a,ha⟩ := hd
  have he : m=centre sg c+4*a := by omega
  have hp : rhoU^m=rhoU^(centre sg c)*(rhoU^4)^a := by
    rw [← zpow_natCast,← zpow_mul,← zpow_add]
    norm_num; rw [← he]
  have hb : f ((base sg*(↑(rhoU^(centre sg c)):R))*(↑((rhoU^4)^a):R))=0 := by
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
