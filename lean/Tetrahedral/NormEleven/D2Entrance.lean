import Tetrahedral.Quartic.D2
import Tetrahedral.FiniteDifference

namespace Tetrahedral.NormEleven.Entrance2
open Quartic2 R

/-- The affine lattice containing the entire two-sided orbit. -/
def lattice (x : R) : Prop := (2:ℤ) ∣ x 0 ∧
  (4:ℤ) ∣ x 1+2*x 3-3 ∧ (2:ℤ) ∣ x 2

theorem lattice_step (x : R) (hx : lattice x) :
    lattice (x*rho) ∧ lattice (x*rhoInv) := by
  obtain ⟨h0,h1,h2⟩ := hx
  constructor
  all_goals
    refine ⟨?_,?_,?_⟩ <;>
      simp only [mul_apply0,mul_apply1,mul_apply2,mul_apply3] <;>
      norm_num [rho,rhoInv] <;> omega

theorem orbit_lattice (m : ℤ) : lattice (xi0*(↑(rhoU^m):R)) := by
  induction m using Int.induction_on with
  | zero => norm_num [lattice,xi0]
  | succ n ih =>
    rw [zpow_add_one,Units.val_mul,← mul_assoc]
    exact (lattice_step _ ih).1
  | pred n ih =>
    rw [zpow_sub_one,Units.val_mul,← mul_assoc]
    exact (lattice_step _ ih).2

/-- The third finite difference vanishes on the whole lattice, not just on
a finite list of powers. -/
theorem third (x : R) (hx : lattice x) :
    (128:ℤ) ∣ f (x*(↑(rhoU^3):R))-3*f (x*(↑(rhoU^2):R))+
      3*f (x*(↑(rhoU^1):R))-f x := by
  obtain ⟨⟨a,ha⟩,⟨b,hb⟩,⟨c,hc⟩⟩ := hx
  have h0 : x 0=2*a := by omega
  have h1 : x 1=4*b+3-2*x 3 := by omega
  have h2 : x 2=2*c := by omega
  have hp2 : (↑(rhoU^2):R)=⟨![41,24,6,4]⟩ := by decide +kernel
  have hp3 : (↑(rhoU^3):R)=⟨![531,306,83,48]⟩ := by decide +kernel
  rw [hp2,hp3,pow_one]
  simp only [f,mul_apply0,mul_apply1]
  rw [h0,h1,h2]
  norm_num [rhoU,rho]
  ring_nf; omega

theorem orbit_third (m : ℤ) :
    (128:ℤ) ∣ f (xi0*(↑(rhoU^(m+3)):R))-3*f (xi0*(↑(rhoU^(m+2)):R))+
      3*f (xi0*(↑(rhoU^(m+1)):R))-f (xi0*(↑(rhoU^m):R)) := by
  have hp (j : ℕ) : (xi0*(↑(rhoU^m):R))*(↑(rhoU^j):R)=
      xi0*(↑(rhoU^(m+j)):R) := by
    rw [zpow_add,zpow_natCast,Units.val_mul,mul_assoc]
  have h3 := hp 3; have h2 := hp 2; have h1 := hp 1
  norm_num only [Nat.cast_ofNat] at h3 h2 h1
  rw [← h3,← h2,← h1]
  exact third _ (orbit_lattice m)

/-- A single quadratic congruence replaces the entrance table. -/
theorem polynomial (m : ℤ) :
    (128:ℤ) ∣ f (xi0*(↑(rhoU^m):R))-32*m*(m+1) := by
  let g (i : ℤ) := f (xi0*(↑(rhoU^i):R))-32*i*(i+1)
  have hi : ∀ j : Fin 3, (128:ℤ) ∣ g j.val := by decide +kernel
  have ht (i : ℤ) : (128:ℤ) ∣ g (i+3)-3*g (i+2)+3*g (i+1)-g i := by
    dsimp only [g]
    convert orbit_third i using 1 <;> ring
  exact FiniteDifference.zero_mod g 128 hi ht m

theorem root_residue (m : ℤ) (hm : f (xi0*(↑(rhoU^m):R))=0) :
    m%4=0 ∨ m%4=3 := by
  have h := polynomial m
  rw [hm,zero_sub] at h
  have hh : (128:ℤ) ∣ 32*(m*(m+1)) := by
    convert dvd_neg.mp h using 1 <;> ring
  have hd : (4:ℤ) ∣ m*(m+1) := by omega
  have hz := Int.emod_eq_zero_of_dvd hd
  rw [Int.mul_emod,Int.add_emod] at hz
  by_contra hn
  have hc : m%4=1 ∨ m%4=2 := by omega
  rcases hc with h|h <;> rw [h] at hz <;> norm_num at hz

end Tetrahedral.NormEleven.Entrance2
