import Tetrahedral.Binomial

namespace Tetrahedral.QuadraticPolynomial

section
variable {R : Type*} [CommRing R]

/-- The dyadic descent also applies to a quadratic polynomial with a constant
and a linear part. Only its expansion at the chosen zero is needed. -/
theorem exponent_unique_from_precision (f : R → ℤ) (L : R →ₗ[ℤ] ℤ) (Q : R → ℤ)
    (y : R) (w : Rˣ) (t v : ℕ) (U : R)
    (hy : f y=0)
    (hquad : ∀ z (n : ℤ), f (y+n • z)=f y+n*L z+n^2*Q z)
    (Good : R → Prop)
    (hprecision : ∀ k (a : ℤ), ∃ E : R,
      (↑(w^((2:ℤ)^k*a)):R)=1+2^(k+t+1)*((a:R)*U+2^t*E) ∧ Good E)
    (hlinear : ∀ E, Good E → (2:ℤ)^v ∣ 2^t*L (y*E))
    (hquadratic : ∀ k (a : ℤ) E, Good E → (2:ℤ)^v ∣
      2^(k+t+1)*Q (a • (y*U)+((2:ℤ)^t) • (y*E)))
    (hkernel : ∀ a : ℤ, (2:ℤ)^v ∣ a*L (y*U) → 2 ∣ a)
    (i : ℤ) (hi : f (y*(↑(w^i):R))=0) : i=0 := by
  have parity (k : ℕ) (a : ℤ) (ha : f (y*(↑(w^((2:ℤ)^k*a)):R))=0) : 2 ∣ a := by
    obtain ⟨E,hE,hg⟩ := hprecision k a
    let V : R := a • (y*U)+((2:ℤ)^t) • (y*E)
    have hR : y*(↑(w^((2:ℤ)^k*a)):R)=y+((2:ℤ)^(k+t+1)) • V := by
      rw [hE]
      dsimp [V]
      simp only [zsmul_eq_mul,Int.cast_pow,Int.cast_ofNat,Int.cast_mul,pow_add]
      ring
    have hh := hquad V ((2:ℤ)^(k+t+1))
    rw [← hR,ha,hy] at hh
    have hzero : (2:ℤ)^(k+t+1)*(L V+2^(k+t+1)*Q V)=0 := by
      simpa only [smul_eq_mul,zero_add,pow_two,mul_add,mul_assoc] using hh.symm
    have hz := (mul_eq_zero.mp hzero).resolve_left (pow_ne_zero _ (by decide))
    have hL : L V=a*L (y*U)+2^t*L (y*E) := by
      simp only [V,map_add,map_smul,smul_eq_mul]
    apply hkernel a
    have hd := (hlinear E hg).add (hquadratic k a E hg)
    have he : 2^t*L (y*E)+2^(k+t+1)*Q V= -(a*L (y*U)) := by
      rw [hL] at hz; linarith
    rw [he] at hd
    exact dvd_neg.mp hd
  have hd (k : ℕ) : (2:ℤ)^k ∣ i := by
    induction k with
    | zero => simp
    | succ k ih =>
      obtain ⟨a,ha⟩ := ih
      obtain ⟨b,hb⟩ := parity k a (by rwa [← ha])
      exact ⟨b,by rw [ha,hb,pow_succ];ring⟩
  apply Int.eq_zero_of_dvd_of_natAbs_lt_natAbs (hd i.natAbs)
  simpa only [Int.natAbs_pow,show (2:ℤ).natAbs=2 from rfl] using i.natAbs.lt_two_pow_self



end
end Tetrahedral.QuadraticPolynomial
