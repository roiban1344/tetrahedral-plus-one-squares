import Tetrahedral.Quartic.D2
import Tetrahedral.OrbitCongruence

namespace Tetrahedral.NormEleven.Extra2
open Quartic2 R

def index (j : Fin 2) : Fin 4 := ⟨j.val,by omega⟩

theorem coordinate_step (x : R) (j : Fin 2) :
    (8:ℤ) ∣ (x*(↑(rhoU^2):R)) (index j)-x (index j) := by
  have h : (↑(rhoU^2):R)=⟨![41,24,6,4]⟩ := by decide +kernel
  fin_cases j
  · change (8:ℤ) ∣ (x*(↑(rhoU^2):R)) 0-x 0
    rw [h,mul_apply0]; norm_num; omega
  · change (8:ℤ) ∣ (x*(↑(rhoU^2):R)) 1-x 1
    rw [h,mul_apply1]; norm_num; omega

theorem coordinate_orbit (x : R) (i : ℤ) (j : Fin 2) :
    (8:ℤ) ∣ (x*(↑((rhoU^2)^i):R)) (index j)-x (index j) :=
  OrbitCongruence.invariant (rhoU^2) (fun z : R => z (index j)) 8
    (fun z => coordinate_step z j) x i

def seed : Fin 2 → R := ![xi1,⟨![44,25,5,5]⟩]
theorem seed_eq : ∀ j : Fin 2, xi1*(↑(rhoU^j.val):R)=seed j := by decide +kernel

theorem exclude (r : ℕ) (m : ℤ)
    (hf : f (xi1*(↑(rhoU^m):R))=0)
    (hr : (xi1*(↑(rhoU^m):R)) 0=2*(r:ℤ)^2) : False := by
  let j : Fin 2 := ⟨(m%2).toNat,by omega⟩
  have he : m=(j.val:ℤ)+2*(m/2) := by dsimp [j]; omega
  have hp : xi1*(↑(rhoU^m):R)=
      (xi1*(↑(rhoU^j.val):R))*(↑((rhoU^2)^(m/2)):R) := by
    conv_lhs => rw [he,zpow_add,zpow_mul,zpow_ofNat,zpow_natCast,Units.val_mul,← mul_assoc]
  have h0 := coordinate_orbit (xi1*(↑(rhoU^j.val):R)) (m/2) 0
  have h1 := coordinate_orbit (xi1*(↑(rhoU^j.val):R)) (m/2) 1
  rw [← hp,seed_eq] at h0 h1
  clear he hp
  generalize hj : j=k at h0 h1
  fin_cases k
  · change (8:ℤ) ∣ (xi1*(↑(rhoU^m):R)) 0-2 at h0
    change (8:ℤ) ∣ (xi1*(↑(rhoU^m):R)) 1-3 at h1
    obtain ⟨a,ha⟩ := h0; obtain ⟨b,hb⟩ := h1
    have hres : (16:ℤ) ∣ f (xi1*(↑(rhoU^m):R))-8 := by
      simp only [f]
      have ha' : (xi1*(↑(rhoU^m):R)) 0=2+8*a := by omega
      have hb' : (xi1*(↑(rhoU^m):R)) 1=3+8*b := by omega
      rw [ha',hb']; ring_nf; omega
    rw [hf] at hres; omega
  · change (8:ℤ) ∣ (xi1*(↑(rhoU^m):R)) 0-44 at h0
    rw [hr] at h0
    have hd : (4:ℤ) ∣ (r:ℤ)^2-2 := by omega
    have hh := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).mpr hd
    push_cast at hh
    have cert : ∀ s : ZMod 4, s^2≠2 := by decide +kernel
    exact cert r (by linear_combination hh)

end Tetrahedral.NormEleven.Extra2
