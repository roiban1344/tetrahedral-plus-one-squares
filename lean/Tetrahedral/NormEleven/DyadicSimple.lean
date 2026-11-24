import Tetrahedral.QuadraticPolynomial
import Tetrahedral.Quartic.D1
import Tetrahedral.Quartic.D3
import Tetrahedral.Quartic.D11

namespace Tetrahedral.NormEleven.DyadicSimple

def centre (c : Fin 2) : ℤ := if c=0 then 0 else -1

section
variable {R : Type*} [CommRing R]
variable (f : R → ℤ) (L : R → R →ₗ[ℤ] ℤ) (Q : R → ℤ)
variable (hq : ∀ x z (n : ℤ), f (x+n • z)=f x+n*L x z+n^2*Q z)

include hq

/-- Two adjacent zeros, sixteen phases, and one dyadic descent. The period is
for the condition, not for all four coordinates of the ring element. -/
theorem pair (u : Rˣ) (y U : R) (hw : (↑(u^16):R)=1+32*U)
    (hL : ∀ k : Fin 16, (256:ℤ) ∣ 32*L (y*(↑(u^k.val):R)) ((y*(↑(u^k.val):R))*U))
    (hp : ∀ k : Fin 16, (256:ℤ) ∣ f (y*(↑(u^k.val):R)) → k.val=0 ∨ k.val=15)
    (hz : ∀ c : Fin 2, f (y*(↑(u^(centre c)):R))=0)
    (hk : ∀ c : Fin 2, L (y*(↑(u^(centre c)):R)) ((y*(↑(u^(centre c)):R))*U)%16=8)
    (m : ℤ) (hm : f (y*(↑(u^m):R))=0) : m=0 ∨ m= -1 := by
  have h := QuadraticPolynomial.phase_obstruction f L Q hq u 16 (by decide)
    32 256 U (by norm_num; exact hw) y (by norm_num) hL m hm
  have hlo := Int.emod_nonneg m (by norm_num : (16:ℤ)≠0)
  have hhi := Int.emod_lt_of_pos m (by norm_num : (0:ℤ)<16)
  have hh := hp ⟨(m%16).toNat,by omega⟩ h
  change (m%16).toNat=0 ∨ (m%16).toNat=15 at hh
  obtain ⟨c,hc⟩ := QuadraticPolynomial.lift_roots f L Q hq u 16 4 U
    (by norm_num; exact hw) y centre hz (by
      intro c a ha
      norm_num at ha
      have hmod := Int.emod_eq_zero_of_dvd ha
      rw [Int.mul_emod,hk c] at hmod
      omega) m hm (by
        rcases hh with hh|hh
        · exact ⟨0,by change m%16=0; omega⟩
        · exact ⟨1,by change m%16=15; omega⟩)
  fin_cases c <;> simp only [centre] at hc <;> simp_all

theorem negative (u : Rˣ) (y U : R) (hw : (↑(u^16):R)=1+32*U)
    (hL : ∀ k : Fin 16, (256:ℤ) ∣ 32*L (-y*(↑(u^k.val):R)) ((-y*(↑(u^k.val):R))*U))
    (hp : ∀ k : Fin 16, ¬ (256:ℤ) ∣ f (-y*(↑(u^k.val):R)))
    (m : ℤ) : f (-(y*(↑(u^m):R)))≠0 := by
  intro hm
  have h := QuadraticPolynomial.phase_obstruction f L Q hq u 16 (by decide)
    32 256 U (by norm_num; exact hw) (-y) (by norm_num) hL m (by simpa only [neg_mul] using hm)
  exact hp ⟨(m%16).toNat,by have := Int.emod_lt_of_pos m (by norm_num : (0:ℤ)<16); omega⟩ h

end

end Tetrahedral.NormEleven.DyadicSimple
