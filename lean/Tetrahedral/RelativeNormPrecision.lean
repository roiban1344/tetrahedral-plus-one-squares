import Tetrahedral.QuadraticPolynomial

namespace Tetrahedral.RelativeNormPrecision

private theorem component (n q x h : ℤ) (hq : q≠0)
    (he : n+4*q*x+4*q^2*h=n) : x= -q*h := by
  have hz : (4*q)*(x+q*h)=0 := by linear_combination he
  have := (mul_eq_zero.mp hz).resolve_left (mul_ne_zero (by decide) hq)
  linarith

/-- The error of a unit power has more divisibility than an arbitrary ring
element: the relative norm controls both normal coordinates. -/
theorem error_dvd {R : Type*} [CommRing R]
    (X Y : R →ₗ[ℤ] ℤ) (H K : R → ℤ)
    (hH : ∀ q V, H (1+(2*q) • V)=1+4*q*X V+4*q^2*H V)
    (hK : ∀ q V, K (1+(2*q) • V)=4*q*Y V+4*q^2*K V)
    (m q a b : ℤ) (hq : q≠0) (hb : b≠0) (hmq : m ∣ q)
    (hdiv : ∀ V, m ∣ X V → m ∣ Y V → m ∣ H V ∧ m ∣ K V)
    (U E : R)
    (hu : H (1+(2*q) • U)=1 ∧ K (1+(2*q) • U)=0)
    (hz : H (1+(2*b*q) • (a • U+q • E))=1 ∧
      K (1+(2*b*q) • (a • U+q • E))=0) : m ∣ X E ∧ m ∣ Y E := by
  let V := a • U+q • E
  have hu0 := component 1 q (X U) (H U) hq (by rw [← hH]; exact hu.1)
  have hu1 := component 0 q (Y U) (K U) hq (by simpa using (hK q U).symm.trans hu.2)
  have hz' : H (1+(2*(b*q)) • V)=1 ∧ K (1+(2*(b*q)) • V)=0 := by
    simpa only [V,mul_assoc] using hz
  have hv0 := component 1 (b*q) (X V) (H V) (mul_ne_zero hb hq) (by
    rw [← hH]; exact hz'.1)
  have hv1 := component 0 (b*q) (Y V) (K V) (mul_ne_zero hb hq) (by
    simpa using (hK (b*q) V).symm.trans hz'.2)
  have hdu := hdiv U (by rw [hu0,neg_mul]; exact dvd_neg.mpr (hmq.mul_right _))
    (by rw [hu1,neg_mul]; exact dvd_neg.mpr (hmq.mul_right _))
  have hdv := hdiv V (by rw [hv0,neg_mul]; exact dvd_neg.mpr ((hmq.mul_left b).mul_right _))
    (by rw [hv1,neg_mul]; exact dvd_neg.mpr ((hmq.mul_left b).mul_right _))
  have hx0 : X E=a*H U-b*H V := by
    have hh : X V=a*X U+q*X E := by simp only [V,map_add,map_smul,smul_eq_mul]
    have he : q*(X E-a*H U+b*H V)=0 := by rw [hu0,hv0] at hh; linear_combination -hh
    have := (mul_eq_zero.mp he).resolve_left hq; linarith
  have hx1 : Y E=a*K U-b*K V := by
    have hh : Y V=a*Y U+q*Y E := by simp only [V,map_add,map_smul,smul_eq_mul]
    have he : q*(Y E-a*K U+b*K V)=0 := by rw [hu1,hv1] at hh; linear_combination -hh
    have := (mul_eq_zero.mp he).resolve_left hq; linarith
  constructor
  · rw [hx0]; exact (hdu.1.mul_left a).sub (hdv.1.mul_left b)
  · rw [hx1]; exact (hdu.2.mul_left a).sub (hdv.2.mul_left b)

/-- Apply the norm constraint to the actual remainder in a dyadic unit power. -/
theorem power_error_dvd {R : Type*} [CommRing R]
    (X Y : R →ₗ[ℤ] ℤ) (H K : R → ℤ)
    (hH : ∀ q V, H (1+(2*q) • V)=1+4*q*X V+4*q^2*H V)
    (hK : ∀ q V, K (1+(2*q) • V)=4*q*Y V+4*q^2*K V)
    (m : ℤ) (t : ℕ) (hm : m ∣ (2:ℤ)^t)
    (hdiv : ∀ V, m ∣ X V → m ∣ Y V → m ∣ H V ∧ m ∣ K V)
    (w : Rˣ) (U : R) (hw : (w:R)=1+2^(t+1)*U)
    (hrel : ∀ i : ℤ, H (↑(w^i):R)=1 ∧ K (↑(w^i):R)=0)
    (k : ℕ) (a : ℤ) (E : R)
    (he : (↑(w^((2:ℤ)^k*a)):R)=1+2^(k+t+1)*((a:R)*U+2^t*E)) :
    m ∣ X E ∧ m ∣ Y E := by
  have hw' : (w:R)=1+(2*(2:ℤ)^t) • U := by
    rw [hw]; simp only [zsmul_eq_mul]; push_cast; ring
  have he' : (↑(w^((2:ℤ)^k*a)):R)=
      1+(2*(2:ℤ)^k*2^t) • (a • U+((2:ℤ)^t) • E) := by
    rw [he]; simp only [zsmul_eq_mul]; push_cast; simp only [pow_add]; ring
  apply error_dvd X Y H K hH hK m (2^t) a (2^k)
    (pow_ne_zero _ (by decide)) (pow_ne_zero _ (by decide)) hm hdiv U E
  · rw [← hw']; simpa only [zpow_one] using hrel 1
  · rw [← he']; exact hrel _

/-- A unit-norm remainder stays in its coordinate lattice. The first
variation and quadratic part can be tested on that smaller lattice. -/
theorem unique {R : Type*} [CommRing R]
    (X Y : R →ₗ[ℤ] ℤ) (m : ℤ)
    (f : R → ℤ) (L : R →ₗ[ℤ] ℤ) (Q : R → ℤ)
    (y : R) (w : Rˣ) (t : ℕ) (U : R)
    (hw : (w:R)=1+2^(t+1)*U) (hy : f y=0)
    (hquad : ∀ z (n : ℤ), f (y+n • z)=f y+n*L z+n^2*Q z)
    (hgood : ∀ k (a : ℤ) E, (↑(w^((2:ℤ)^k*a)):R)=
      1+2^(k+t+1)*((a:R)*U+2^t*E) → m ∣ X E ∧ m ∣ Y E)
    (hU : m ∣ X U ∧ m ∣ Y U)
    (hlinear : ∀ E, m ∣ X E ∧ m ∣ Y E → (8:ℤ) ∣ L (y*E))
    (hquadratic : ∀ V, m ∣ X V ∧ m ∣ Y V → (4:ℤ) ∣ Q (y*V))
    (hkernel : ∀ a : ℤ, (2:ℤ)^(t+3) ∣ a*L (y*U) → 2 ∣ a)
    (i : ℤ) (hi : f (y*(↑(w^i):R))=0) : i=0 := by
  apply QuadraticPolynomial.exponent_unique_lattice f L Q y w t U hw hy hquad
    (fun E => m ∣ X E ∧ m ∣ Y E) hgood hlinear ?_ hkernel i hi
  intro a E hE
  let V := a • U+((2:ℤ)^t) • E
  have hv : m ∣ X V ∧ m ∣ Y V := by
    simp only [V,map_add,map_smul,smul_eq_mul]
    exact ⟨(hU.1.mul_left a).add (hE.1.mul_left _),
      (hU.2.mul_left a).add (hE.2.mul_left _)⟩
  have he : y*V=a • (y*U)+((2:ℤ)^t) • (y*E) := by
    simp only [V,zsmul_eq_mul]; ring
  rw [← he]
  exact hquadratic V hv

end Tetrahedral.RelativeNormPrecision
