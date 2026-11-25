import Tetrahedral.QuadraticPolynomial

namespace Tetrahedral.FactoredExponent

/-- The square of the direction and its scalar residue retain the useful
precision. No norm condition on an arbitrary error needs to be recovered. -/
theorem unique {R : Type*} [CommRing R]
    (f : R → ℤ) (L : R →ₗ[ℤ] ℤ) (Q : R → ℤ)
    (y : R) (w : Rˣ) (t v : ℕ) (ht : 1≤t) (U : R)
    (hw : (w:R)=1+2^(t+1)*U) (hy : f y=0)
    (hquad : ∀ z (n : ℤ), f (y+n • z)=f y+n*L z+n^2*Q z)
    (hlinear : ∀ (b : ℤ) E, (2:ℤ)^v ∣ 2^t*L (y*(U^2*((b:R)+2*E))))
    (hquadratic : ∀ (a b : ℤ) E, (2:ℤ)^v ∣ 2^(t+1)*
      Q (y*((a:R)*U+2^t*U^2*((b:R)+2*E))))
    (hkernel : ∀ a : ℤ, (2:ℤ)^v ∣ a*L (y*U) → 2 ∣ a)
    (i : ℤ) (hi : f (y*(↑(w^i):R))=0) : i=0 := by
  apply QuadraticPolynomial.exponent_unique_from_precision f L Q y w t v U hy hquad
    (fun F => ∃ b : ℤ, ∃ E : R, F=U^2*((b:R)+2*E)) ?_ ?_ ?_ hkernel i hi
  · intro k a
    obtain ⟨b,E,hE⟩ := dyadic_zpow_precision_scalar w t k ht U hw a
    exact ⟨U^2*((b:R)+2*E),by simpa only [mul_assoc] using hE,b,E,rfl⟩
  · rintro F ⟨b,E,rfl⟩
    exact hlinear b E
  · rintro k a F ⟨b,E,rfl⟩
    have hh := (hquadratic a b E).mul_left ((2:ℤ)^k)
    convert hh using 1
    have he : a • (y*U)+((2:ℤ)^t) • (y*(U^2*((b:R)+2*E)))=
        y*((a:R)*U+2^t*U^2*((b:R)+2*E)) := by
      simp only [zsmul_eq_mul]; push_cast; ring
    rw [he]; simp only [pow_add]; ring

end Tetrahedral.FactoredExponent
