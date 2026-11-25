import Tetrahedral.QuadraticPolynomial
import Tetrahedral.QuadraticPowers

namespace Tetrahedral.QuadraticPolynomialSecondOrder
section
variable {R : Type*} [CommRing R]
variable (A B : R →ₗ[ℤ] ℤ) (e k c : ℤ)

def value (x : R) : ℤ := (A x-k)^2-e*(B x)^2+c
def linear (x z : R) : ℤ := 2*(A x-k)*A z-2*e*B x*B z
def pure (z : R) : ℤ := (A z)^2-e*(B z)^2
def cross (z v : R) : ℤ := A z*A v-e*B z*B v

/-- The quadratic coefficient of an orbit is visible before the cubic
remainder. This remains valid for negative integer exponents. -/
theorem orbit_congruence (w : Rˣ) (s : ℤ) (U : R)
    (hw : (w:R)=1+4*(s:R)*U) (y : R) (a : ℤ) :
    (128*s^3) ∣ value A B e k c (y*(↑(w^a):R))-
      (value A B e k c y+
        (4*s*linear A B e k y (y*U)-8*s^2*linear A B e k y (y*U^2))*a+
        (8*s^2*linear A B e k y (y*U^2)+16*s^2*pure A B e (y*U))*a^2) := by
  obtain ⟨E,hE⟩ := quadratic_even_zpow w (2*(s:R)) U (by convert hw using 1 <;> ring) a
  have he : y*(↑(w^a):R)=y+(4*s*a) • (y*U)+
      (8*s^2*(a*(a-1))) • (y*U^2)+(64*s^3) • (y*E) := by
    rw [hE]; simp only [zsmul_eq_mul]; push_cast; ring
  rw [he]
  obtain ⟨b,hb⟩ := consecutive_product_even a
  refine ⟨a*b*cross A B e (y*U) (y*U^2)+
    2*s*b^2*pure A B e (y*U^2)+(A y-k)*A (y*E)-e*B y*B (y*E)+
    4*s*a*cross A B e (y*U) (y*E)+
    8*s^2*a*(a-1)*cross A B e (y*U^2) (y*E)+32*s^3*pure A B e (y*E),?_⟩
  have hc := congrArg (fun z : ℤ => 64*s^3*
    (a*cross A B e (y*U) (y*U^2)+s*(a*(a-1)+2*b)*pure A B e (y*U^2))*z) hb
  simp only [value,linear,pure,cross,map_add,map_smul,smul_eq_mul]
  simp only [cross,pure] at hc
  linear_combination hc

theorem phase_roots {C J : Type*} (u : Rˣ) (P : ℕ) (hP : 0<P)
    (s : ℤ) (U : R) (hw : (↑(u^P):R)=1+4*(s:R)*U) (y : R)
    (centre : C → ℤ) (modulus : J → ℤ)
    (hcert : ∀ r : Fin P, (∃ z, (r.val:ℤ)=centre z%P) ∨
      ∃ j, modulus j ∣ 128*s^3 ∧
        modulus j ∣ 4*s*linear A B e k (y*(↑(u^r.val):R)) ((y*(↑(u^r.val):R))*U)-
          8*s^2*linear A B e k (y*(↑(u^r.val):R)) ((y*(↑(u^r.val):R))*U^2) ∧
        modulus j ∣ 8*s^2*linear A B e k (y*(↑(u^r.val):R)) ((y*(↑(u^r.val):R))*U^2)+
          16*s^2*pure A B e ((y*(↑(u^r.val):R))*U) ∧
        ¬ modulus j ∣ value A B e k c (y*(↑(u^r.val):R)))
    (i : ℤ) (hi : value A B e k c (y*(↑(u^i):R))=0) : ∃ z, i%P=centre z%P := by
  have hlo := Int.emod_nonneg i (show (P:ℤ)≠0 by omega)
  have hhi := Int.emod_lt_of_pos i (show (0:ℤ)<P by omega)
  let r : Fin P := ⟨(i%P).toNat,by omega⟩
  have hr : (r.val:ℤ)=i%P := by dsimp [r]; omega
  rcases hcert r with ⟨z,hz⟩|⟨j,hN,hL,hQ,hf⟩
  · exact ⟨z,by rw [← hr]; exact hz⟩
  · have hp : u^i=u^r.val*(u^P)^(i/P) := by
      rw [← zpow_natCast,← zpow_natCast u P,← zpow_mul,← zpow_add,hr]
      congr 1; have := Int.emod_add_mul_ediv i (P:ℤ); omega
    have h := dvd_trans hN (orbit_congruence A B e k c (u^P) s U hw
      (y*(↑(u^r.val):R)) (i/P))
    rw [mul_assoc,← Units.val_mul,← hp,hi,zero_sub] at h
    have hh := (dvd_neg.mp h).sub ((hL.mul_right (i/P)).add (hQ.mul_right ((i/P)^2)))
    exfalso; apply hf
    convert hh using 1 <;> ring

end
end Tetrahedral.QuadraticPolynomialSecondOrder
