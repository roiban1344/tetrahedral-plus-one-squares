import Tetrahedral.QuadraticPolynomial

namespace Tetrahedral.NormEleven.DyadicSimple

def centre : Fin 2 → ℤ := ![0,-1]

/-- Two known roots exhaust the two parity classes once uniqueness holds
under the square of the unit. No positive-phase table is needed. -/
theorem pair {R : Type*} [CommRing R] (f : R → ℤ) (u : Rˣ) (y : R)
    (hu : ∀ c : Fin 2, ∀ i : ℤ,
      f ((y*(↑(u^(centre c)):R))*(↑((u^2)^i):R))=0 → i=0)
    (m : ℤ) (hm : f (y*(↑(u^m):R))=0) : m=0 ∨ m= -1 := by
  have hlo := Int.emod_nonneg m (by norm_num : (2:ℤ)≠0)
  have hhi := Int.emod_lt_of_pos m (by norm_num : (0:ℤ)<2)
  obtain ⟨c,hc⟩ : ∃ c : Fin 2, m%2=centre c%2 := by
    by_cases h : m%2=0
    · exact ⟨0,by simpa [centre] using h⟩
    · exact ⟨1,by norm_num [centre]; omega⟩
  have hd : (2:ℤ) ∣ m-centre c := Int.dvd_of_emod_eq_zero (by
    rw [Int.sub_emod,hc,sub_self,Int.zero_emod])
  obtain ⟨a,ha⟩ := hd
  have he : m=centre c+2*a := by omega
  have hp : u^m=u^(centre c)*(u^2)^a := by
    rw [← zpow_natCast,← zpow_mul,← zpow_add]
    norm_num; rw [← he]
  have ha0 := hu c a (by simpa only [hp,Units.val_mul,mul_assoc] using hm)
  have hmc : m=centre c := by simpa only [ha0,mul_zero,add_zero] using he
  fin_cases c <;> simp_all [centre]

theorem negative {R : Type*} [CommRing R]
    (f : R → ℤ) (L : R → R →ₗ[ℤ] ℤ) (Q : R → ℤ)
    (hq : ∀ x z (n : ℤ), f (x+n • z)=f x+n*L x z+n^2*Q z)
    (u : Rˣ) (y U : R) (hw : (↑(u^2):R)=1+4*U)
    (hL : ∀ k : Fin 2, (8:ℤ) ∣ 4*L (-y*(↑(u^k.val):R)) ((-y*(↑(u^k.val):R))*U))
    (hp : ∀ k : Fin 2, ¬ (8:ℤ) ∣ f (-y*(↑(u^k.val):R)))
    (m : ℤ) : f (-(y*(↑(u^m):R)))≠0 := by
  intro hm
  have h := QuadraticPolynomial.phase_obstruction f L Q hq u 2 (by decide)
    4 8 U (by norm_num; exact hw) (-y) (by norm_num) hL m (by simpa only [neg_mul] using hm)
  exact hp ⟨(m%2).toNat,by have := Int.emod_lt_of_pos m (by norm_num : (0:ℤ)<2); omega⟩ h

end Tetrahedral.NormEleven.DyadicSimple
