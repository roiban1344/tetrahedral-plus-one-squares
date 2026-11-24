import Tetrahedral.Quartic.D2
import Tetrahedral.QuadraticPolynomial

set_option maxRecDepth 20000
set_option maxHeartbeats 0

namespace Tetrahedral.NormEleven.Dyadic2
open Quartic2 R

def step : R := ⟨fun i => ((rho^128-1 : R) i)/128⟩
theorem step_eq : (↑(rhoU^128):R)=1+128*step := by
  have h : (↑(rhoU^128):R)=1+(128:ℤ) • step := by
    ext i; fin_cases i <;> decide +kernel
  simpa only [zsmul_eq_mul,Int.cast_ofNat] using h

def centre (c : Fin 3) : ℤ := ![0,-4,-1] c
def modulus (j : Fin 3) : ℤ := ![128,4096,8192] j

theorem phase_certificate : ∀ k : Fin 128,
    (∃ c : Fin 3, (k.val:ℤ)=centre c%128) ∨
    ∃ j : Fin 3, modulus j ∣ (128:ℤ)^2 ∧
      modulus j ∣ 128*Lf (xi0*(↑(rhoU^k.val):R)) ((xi0*(↑(rhoU^k.val):R))*step) ∧
      ¬ modulus j ∣ f (xi0*(↑(rhoU^k.val):R)) := by decide +kernel

theorem roots (m : ℤ) (hm : f (xi0*(↑(rhoU^m):R))=0) : m=0 ∨ m= -4 ∨ m= -1 := by
  obtain ⟨c,hc⟩ := QuadraticPolynomial.phase_roots f Lf Qf f_expand rhoU 128 (by decide)
    128 step (by norm_num; exact step_eq) xi0 centre modulus phase_certificate m hm
  norm_num at hc
  have hd : (128:ℤ) ∣ m-centre c := Int.dvd_of_emod_eq_zero (by
    rw [Int.sub_emod,hc,sub_self,Int.zero_emod])
  obtain ⟨a,ha⟩ := hd
  have he : m=centre c+128*a := by omega
  have hp : rhoU^m=rhoU^(centre c)*(rhoU^128)^a := by
    rw [← zpow_natCast,← zpow_mul,← zpow_add]
    norm_num; rw [← he]
  have hz : ∀ c : Fin 3, f (xi0*(↑(rhoU^(centre c)):R))=0 := by decide +kernel
  have hk : ∀ c : Fin 3, Lf (xi0*(↑(rhoU^(centre c)):R))
      ((xi0*(↑(rhoU^(centre c)):R))*step)%128 ∈ [32,64,96] := by decide +kernel
  have ha0 := QuadraticPolynomial.exponent_unique_even f
    (Lf (xi0*(↑(rhoU^(centre c)):R))) Qf (xi0*(↑(rhoU^(centre c)):R))
    (rhoU^128) 6 step (by norm_num; exact step_eq) (hz c) (f_expand _) (by
      intro z
      exact ⟨((xi0*(↑(rhoU^(centre c)):R)) 0-3)*z 0-3*(xi0*(↑(rhoU^(centre c)):R)) 1*z 1,
        by simp only [Lf,LinearMap.coe_mk,AddHom.coe_mk]; ring⟩) (by
      intro b hb
      norm_num at hb
      have hb' := Int.emod_eq_zero_of_dvd hb
      rw [Int.mul_emod] at hb'
      have hkc := hk c
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hkc
      rcases hkc with h|h|h <;> rw [h] at hb' <;> omega) a
    (by simpa only [hp,Units.val_mul,mul_assoc] using hm)
  have hmc : m=centre c := by simpa only [ha0,mul_zero,add_zero] using he
  fin_cases c <;> simp_all [centre]

def shortStep : R := ⟨fun i => ((rho^8-1 : R) i)/8⟩
theorem shortStep_eq : (↑(rhoU^8):R)=1+8*shortStep := by
  have h : (↑(rhoU^8):R)=1+(8:ℤ) • shortStep := by
    ext i; fin_cases i <;> decide +kernel
  simpa only [zsmul_eq_mul,Int.cast_ofNat] using h

def bad (c : Fin 3) : R := ![-xi0,xi1,-xi1] c
def coord : R →ₗ[ℤ] ℤ where
  toFun x := x 0
  map_add' x y := rfl
  map_smul' n x := rfl

/-- Keep the original square condition: three Euler types disappear before
any local uniqueness argument is needed. -/
theorem exclude (c : Fin 3) (r : ℕ) (m : ℤ)
    (hf : f (bad c*(↑(rhoU^m):R))=0)
    (hr : (bad c*(↑(rhoU^m):R)) 0=2*(r:ℤ)^2) : False := by
  have hLf : ∀ k : Fin 8, (32:ℤ) ∣ 8*Lf (bad c*(↑(rhoU^k.val):R))
      ((bad c*(↑(rhoU^k.val):R))*shortStep) := by fin_cases c <;> decide +kernel
  have hcoord : ∀ k : Fin 8, (32:ℤ) ∣ 8*coord
      ((bad c*(↑(rhoU^k.val):R))*shortStep) := by fin_cases c <;> decide +kernel
  have hf' := QuadraticPolynomial.phase_obstruction f Lf Qf f_expand rhoU 8 (by decide)
    8 32 shortStep (by norm_num; exact shortStep_eq) (bad c) (by norm_num) hLf m hf
  have hg : ∀ x z : R, ∀ n : ℤ,
      (x+n • z) 0-2*(r:ℤ)^2=(x 0-2*(r:ℤ)^2)+n*coord z+n^2*0 := by
    intro x z n
    change (x+n • z) 0-2*(r:ℤ)^2=(x 0-2*(r:ℤ)^2)+n*z 0+n^2*0
    simp only [add_apply,zsmul_apply]; ring
  have hr' := QuadraticPolynomial.phase_obstruction (fun x : R => x 0-2*(r:ℤ)^2)
    (fun _ => coord) (fun _ => 0) hg rhoU 8 (by decide)
    8 32 shortStep (by norm_num; exact shortStep_eq) (bad c) (by norm_num) hcoord m (by omega)
  have cert : ∀ k : Fin 8, ∀ s : ZMod 32,
      ((f (bad c*(↑(rhoU^k.val):R)):ℤ):ZMod 32)≠0 ∨
      (((bad c*(↑(rhoU^k.val):R)) 0:ℤ):ZMod 32)≠2*s^2 := by fin_cases c <;> decide +kernel
  have hlo := Int.emod_nonneg m (by norm_num : (8:ℤ)≠0)
  have hhi := Int.emod_lt_of_pos m (by norm_num : (0:ℤ)<8)
  rcases cert ⟨(m%8).toNat,by omega⟩ (r:ZMod 32) with h|h
  · exact h ((ZMod.intCast_zmod_eq_zero_iff_dvd _ 32).mpr hf')
  · apply h
    have hh := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 32).mpr hr'
    push_cast at hh
    linear_combination hh

end Tetrahedral.NormEleven.Dyadic2
