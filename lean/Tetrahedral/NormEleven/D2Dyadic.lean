import Tetrahedral.Quartic.D2
import Tetrahedral.NormEleven.TaylorObstructions
import Tetrahedral.NormEleven.DyadicSimple

set_option maxRecDepth 20000
set_option maxHeartbeats 0

namespace Tetrahedral.NormEleven.Dyadic2
open Quartic2 R

abbrev step : R := Direction2Odd.step
theorem step_eq : (↑(rhoU^4):R)=1+4*step := Direction2Odd.step_eq

def centre (c : Fin 2) : ℤ := ![0,-1] c

theorem phase_certificate : ∀ r : Fin 4,
    (∃ c : Fin 2, (r.val:ℤ)=centre c%4) ∨
    ∃ j : Fin 2, xi0*(↑(rhoU^r.val):R)=Obstruction2.point j := by decide +kernel

/-- The two close roots share one class modulo four. A single parity split
separates them; the third root has its own, shorter local period. -/
theorem roots (m : ℤ) (hm : f (xi0*(↑(rhoU^m):R))=0) : m=0 ∨ m= -4 ∨ m= -1 := by
  obtain ⟨c,hc⟩ := TaylorOrbit.phase_roots f rhoU 4 (by decide) 1 step
    (by convert step_eq using 1 <;> ring) xi0 centre (by
      intro r
      rcases phase_certificate r with h|⟨j,hj⟩
      · exact Or.inl h
      · right; intro a E; rw [hj]; exact Obstruction2.nonzero j a E) m hm
  norm_num at hc
  have hd : (4:ℤ) ∣ m-centre c := Int.dvd_of_emod_eq_zero (by
    rw [Int.sub_emod,hc,sub_self,Int.zero_emod])
  obtain ⟨a,ha⟩ := hd
  have he : m=centre c+4*a := by omega
  have hp : rhoU^m=rhoU^(centre c)*(rhoU^4)^a := by
    rw [← zpow_natCast,← zpow_mul,← zpow_add]
    norm_num; rw [← he]
  have hb : f ((xi0*(↑(rhoU^(centre c)):R))*(↑((rhoU^4)^a):R))=0 := by
    simpa only [hp,Units.val_mul,mul_assoc] using hm
  fin_cases c
  · change m=0+4*a at he
    change f (xi0*(↑((rhoU^4)^a):R))=0 at hb
    rcases DyadicSimple.pair f (rhoU^4) xi0 (fun j i hi =>
      Direction2.unique j i (by simpa only [← pow_mul,Nat.reduceMul,Direction2.centre,DyadicSimple.centre] using hi)) a hb with h|h
    · left; omega
    · right; left; omega
  · change m= -1+4*a at he
    change f ((xi0*(↑(rhoU^(-1:ℤ)):R))*(↑((rhoU^4)^a):R))=0 at hb
    have ha0 := Direction2Odd.unique 0 a hb
    right; right; omega

/-- Only the second positive Euler type remains. Its two parity classes
fail different necessary conditions, at moduli 16 and 8. -/
abbrev shortStep : R := ⟨![20,12,3,2]⟩
theorem shortStep_eq : (↑(rhoU^2):R)=1+2*shortStep := by
  have h : (↑(rhoU^2):R)=1+(2:ℤ) • shortStep := by
    ext i; fin_cases i <;> decide +kernel
  simpa only [zsmul_eq_mul,Int.cast_ofNat] using h

def extraPoint : Fin 2 → R := ![xi1,⟨![44,25,5,5]⟩]
def extraFirst : Fin 2 → R := ![⟨![280,160,44,25]⟩,⟨![3580,2068,562,323]⟩]
def extraSecond : Fin 2 → R := ![⟨![22868,13204,3580,2068]⟩,⟨![293876,169668,46016,26568]⟩]
def extraThird : Fin 2 → R := ![⟨![1876768,1083552,293876,169668]⟩,
  ⟨![24117184,13924064,3776404,2180308]⟩]
theorem extra_point : ∀ j : Fin 2, xi1*(↑(rhoU^j.val):R)=extraPoint j := by decide +kernel
theorem extra_products : ∀ j : Fin 2,
    extraPoint j*shortStep=extraFirst j ∧
    extraPoint j*shortStep^2=extraSecond j ∧
    extraPoint j*shortStep^3=extraThird j := by decide +kernel

def extraModel (j : Fin 2) (a : ℤ) (E : R) : R := ⟨fun i => extraPoint j i+
  2*a*extraFirst j i+2*a*(a-1)*extraSecond j i+8*(extraThird j*E) i⟩
theorem extra_expansion (j : Fin 2) (a : ℤ) :
    ∃ E, xi1*(↑(rhoU^((j.val:ℤ)+2*a)):R)=extraModel j a E := by
  obtain ⟨E,hE⟩ := quadratic_even_zpow_factored (rhoU^2) (1:R) shortStep
    (by convert shortStep_eq using 1 <;> ring) a
  refine ⟨E,?_⟩
  simp only [one_pow,one_mul] at hE
  rw [zpow_add,zpow_mul,zpow_ofNat,Units.val_mul,hE,← mul_assoc,zpow_natCast,extra_point j]
  have h := extra_products j
  have hh : extraPoint j*(1+2*((a:R)*shortStep)+
      2*((a:R)*((a:R)-1)*shortStep^2)+8*(shortStep^3*E))=
      extraPoint j+(2*a) • extraFirst j+(2*a*(a-1)) • extraSecond j+
      (8:ℤ) • (extraThird j*E) := by
    rw [← h.1,← h.2.1,← h.2.2]
    simp only [zsmul_eq_mul]; push_cast; ring
  calc _=extraPoint j+(2*a) • extraFirst j+(2*a*(a-1)) • extraSecond j+
        (8:ℤ) • (extraThird j*E) := by convert hh using 1 <;> ring
       _=extraModel j a E := by ext i; simp only [extraModel,add_apply,zsmul_apply]


theorem extra_residue (a : ℤ) (E : R) :
    (16:ℤ) ∣ f (extraModel 0 a E)-8 ∧
    (8:ℤ) ∣ (extraModel 1 a E) 0-4 := by
  constructor <;> norm_num [f,extraModel,extraPoint,extraFirst,extraSecond,extraThird,xi1,
    mul_apply0,mul_apply1] <;> ring_nf <;> omega

theorem exclude (r : ℕ) (m : ℤ)
    (hf : f (xi1*(↑(rhoU^m):R))=0)
    (hr : (xi1*(↑(rhoU^m):R)) 0=2*(r:ℤ)^2) : False := by
  let j : Fin 2 := ⟨(m%2).toNat,by omega⟩
  have he : m=(j.val:ℤ)+2*(m/2) := by dsimp [j]; omega
  obtain ⟨E,hE⟩ := extra_expansion j (m/2)
  rw [← he] at hE
  rw [hE] at hf hr
  clear he hE
  generalize hj : j=k at hf hr
  fin_cases k
  · change f (extraModel 0 (m/2) E)=0 at hf
    have h := (extra_residue (m/2) E).1
    rw [hf] at h; omega
  · change (extraModel 1 (m/2) E) 0=2*(r:ℤ)^2 at hr
    have h := (extra_residue (m/2) E).2
    rw [hr] at h
    have hm : (4:ℤ) ∣ (r:ℤ)^2-2 := by omega
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).mpr hm
    push_cast at this
    have cert : ∀ s : ZMod 4, s^2≠2 := by decide +kernel
    exact cert r (by linear_combination this)

end Tetrahedral.NormEleven.Dyadic2
