import Tetrahedral.QuadraticPolynomial

namespace Tetrahedral.FactoredExponent

/-- The square of the direction and its scalar residue retain the useful
precision. -/
theorem unique {R : Type*} [CommRing R]
    (f : R → ℤ) (L : R →ₗ[ℤ] ℤ) (Q : R → ℤ)
    (y : R) (w : Rˣ) (t v : ℕ) (ht : 1≤t) (U : R)
    (hw : (w:R)=1+2^(t+1)*U) (hy : f y=0)
    (hquad : ∀ z (n : ℤ), f (y+n • z)=f y+n*L z+n^2*Q z)
    (F T : R) (hF : y*U=F) (hT : y*U^2=T)
    (hlinear : ∀ (b : ℤ) E, (2:ℤ)^v ∣ 2^t*L (T*((b:R)+2*E)))
    (hquadratic : ∀ (a b : ℤ) E, (2:ℤ)^v ∣ 2^(t+1)*
      Q (a • F+((2:ℤ)^t) • (T*((b:R)+2*E))))
    (hkernel : ∀ a : ℤ, (2:ℤ)^v ∣ a*L F → 2 ∣ a)
    (i : ℤ) (hi : f (y*(↑(w^i):R))=0) : i=0 := by
  apply QuadraticPolynomial.exponent_unique_from_precision f L Q y w t v U hy hquad
    (fun G => ∃ b : ℤ, ∃ E : R, G=U^2*((b:R)+2*E)) ?_ ?_ ?_ ?_ i hi
  · intro k a
    obtain ⟨b,E,hE⟩ := dyadic_zpow_precision_scalar w t k ht U hw a
    exact ⟨U^2*((b:R)+2*E),by simpa only [mul_assoc] using hE,b,E,rfl⟩
  · rintro G ⟨b,E,rfl⟩
    rw [← mul_assoc,hT]
    exact hlinear b E
  · rintro k a G ⟨b,E,rfl⟩
    rw [← mul_assoc,hT,hF]
    have hh := (hquadratic a b E).mul_left ((2:ℤ)^k)
    convert hh using 1
    simp only [pow_add]; ring
  · intro a ha
    rw [hF] at ha
    exact hkernel a ha

end Tetrahedral.FactoredExponent
