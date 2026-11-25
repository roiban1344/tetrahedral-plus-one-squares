import Tetrahedral.Quartic.D2
import Tetrahedral.NormEleven.TaylorObstructions

set_option maxRecDepth 20000
set_option maxHeartbeats 0

namespace Tetrahedral.NormEleven.Dyadic2
open Quartic2 R

abbrev step : R := Direction2.step
theorem step_eq : (↑(rhoU^8):R)=1+8*step := Direction2.step_eq

def centre (c : Fin 3) : ℤ := ![0,-4,-1] c

theorem phase_certificate : ∀ r : Fin 8,
    (∃ c : Fin 3, (r.val:ℤ)=centre c%8) ∨
    ∃ j : Fin 5, xi0*(↑(rhoU^r.val):R)=Obstruction2.point j := by decide +kernel

theorem roots (m : ℤ) (hm : f (xi0*(↑(rhoU^m):R))=0) : m=0 ∨ m= -4 ∨ m= -1 := by
  obtain ⟨c,hc⟩ := TaylorOrbit.phase_roots f rhoU 8 (by decide) 2 step
    (by convert step_eq using 1 <;> ring) xi0 centre (by
      intro r
      rcases phase_certificate r with h|⟨j,hj⟩
      · exact Or.inl h
      · right; intro a E; rw [hj]; exact Obstruction2.nonzero j a E) m hm
  norm_num at hc
  have hd : (8:ℤ) ∣ m-centre c := Int.dvd_of_emod_eq_zero (by
    rw [Int.sub_emod,hc,sub_self,Int.zero_emod])
  obtain ⟨a,ha⟩ := hd
  have he : m=centre c+8*a := by omega
  have hp : rhoU^m=rhoU^(centre c)*(rhoU^8)^a := by
    rw [← zpow_natCast,← zpow_mul,← zpow_add]
    norm_num; rw [← he]
  have ha0 := Direction2.unique c a (by simpa only [hp,Units.val_mul,mul_assoc,centre,Direction2.centre] using hm)
  have hmc : m=centre c := by simpa only [ha0,mul_zero,add_zero] using he
  fin_cases c <;> simp_all [centre]

abbrev shortStep : R := step
theorem shortStep_eq : (↑(rhoU^8):R)=1+8*shortStep := step_eq

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
