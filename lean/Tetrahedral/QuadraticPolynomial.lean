import Tetrahedral.Binomial

namespace Tetrahedral.QuadraticPolynomial

section
variable {R : Type*} [CommRing R]

/-- The dyadic descent also applies to a quadratic polynomial with a constant
and a linear part. Only its expansion at the chosen zero is needed. -/
theorem exponent_unique_constrained (f : R → ℤ) (L : R →ₗ[ℤ] ℤ) (Q : R → ℤ)
    (y : R) (w : Rˣ) (t v : ℕ) (U : R)
    (hw : (↑w:R)=1+2^(t+1)*U) (hy : f y=0)
    (hquad : ∀ z (n : ℤ), f (y+n • z)=f y+n*L z+n^2*Q z)
    (Good : R → Prop)
    (hgood : ∀ k (a : ℤ) E, (↑(w^((2:ℤ)^k*a)):R)=
      1+2^(k+t+1)*((a:R)*U+2^t*E) → Good E)
    (hlinear : ∀ E, Good E → (2:ℤ)^v ∣ 2^t*L (y*E))
    (hquadratic : ∀ k (a : ℤ) E, Good E → (2:ℤ)^v ∣
      2^(k+t+1)*Q (a • (y*U)+((2:ℤ)^t) • (y*E)))
    (hkernel : ∀ a : ℤ, (2:ℤ)^v ∣ a*L (y*U) → 2 ∣ a)
    (i : ℤ) (hi : f (y*(↑(w^i):R))=0) : i=0 := by
  have parity (k : ℕ) (a : ℤ) (ha : f (y*(↑(w^((2:ℤ)^k*a)):R))=0) : 2 ∣ a := by
    obtain ⟨E,hE⟩ := dyadic_zpow_precision w t k U hw a
    have hg := hgood k a E hE
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

/-- Three bits of first-variation divisibility and two bits in the quadratic
part give a uniform gain when the actual remainder lies in a smaller lattice. -/
theorem exponent_unique_lattice (f : R → ℤ) (L : R →ₗ[ℤ] ℤ) (Q : R → ℤ)
    (y : R) (w : Rˣ) (t : ℕ) (U : R)
    (hw : (↑w:R)=1+2^(t+1)*U) (hy : f y=0)
    (hquad : ∀ z (n : ℤ), f (y+n • z)=f y+n*L z+n^2*Q z)
    (Good : R → Prop)
    (hgood : ∀ k (a : ℤ) E, (↑(w^((2:ℤ)^k*a)):R)=
      1+2^(k+t+1)*((a:R)*U+2^t*E) → Good E)
    (hlinear : ∀ E, Good E → (8:ℤ) ∣ L (y*E))
    (hquadratic : ∀ (a : ℤ) E, Good E → (4:ℤ) ∣
      Q (a • (y*U)+((2:ℤ)^t) • (y*E)))
    (hkernel : ∀ a : ℤ, (2:ℤ)^(t+3) ∣ a*L (y*U) → 2 ∣ a)
    (i : ℤ) (hi : f (y*(↑(w^i):R))=0) : i=0 :=
  exponent_unique_constrained f L Q y w t (t+3) U hw hy hquad Good hgood
    (by intro E hE; obtain ⟨b,hb⟩ := hlinear E hE
        exact ⟨b,by rw [hb,pow_add]; norm_num; ring⟩)
    (by intro k a E hE; obtain ⟨b,hb⟩ := hquadratic a E hE
        refine ⟨2^k*b,?_⟩; rw [hb]; simp only [pow_add]; ring)
    hkernel i hi


variable (f : R → ℤ) (L : R → R →ₗ[ℤ] ℤ) (Q : R → ℤ)
variable (hq : ∀ x z (n : ℤ), f (x+n • z)=f x+n*L x z+n^2*Q z)

include hq

/-- A second-order remainder allows a shorter period for the condition than
for the coordinates of the orbit. -/
theorem orbit_congruence (w : Rˣ) (δ N : ℤ) (U : R)
    (hw : (w:R)=1+(δ:R)*U) (y : R)
    (hδ : N ∣ δ^2) (hL : N ∣ δ*L y (y*U)) (i : ℤ) :
    N ∣ f (y*(↑(w^i):R))-f y := by
  obtain ⟨E,hE⟩ := first_order_zpow w (δ:R) U hw i
  let Z : R := i • (y*U)+δ • (y*E)
  have he : y*(↑(w^i):R)=y+δ • Z := by
    rw [hE]; dsimp [Z]; simp only [zsmul_eq_mul]; push_cast; ring
  rw [he,hq]
  have hz : L y Z=i*L y (y*U)+δ*L y (y*E) := by
    simp only [Z,map_add,map_smul,smul_eq_mul]
  have hd := (hL.mul_right i).add (hδ.mul_right (L y (y*E)+Q Z))
  convert hd using 1 <;> rw [hz] <;> ring

theorem phase_obstruction (u : Rˣ) (P : ℕ) (hP : 0<P)
    (δ N : ℤ) (U : R) (hw : (↑(u^P):R)=1+(δ:R)*U) (y : R)
    (hδ : N ∣ δ^2)
    (hL : ∀ k : Fin P, N ∣ δ*L (y*(↑(u^k.val):R)) ((y*(↑(u^k.val):R))*U))
    (i : ℤ) (hi : f (y*(↑(u^i):R))=0) :
    N ∣ f (y*(↑(u^((i%P).toNat)):R)) := by
  have hlo := Int.emod_nonneg i (show (P:ℤ)≠0 by omega)
  have hhi := Int.emod_lt_of_pos i (show (0:ℤ)<P by omega)
  let k : Fin P := ⟨(i%P).toNat,by omega⟩
  have hk : (k.val:ℤ)=i%P := by dsimp [k]; omega
  have hp : u^i=u^k.val*(u^P)^(i/P) := by
    rw [← zpow_natCast,← zpow_natCast u P,← zpow_mul,← zpow_add,hk]
    congr 1; have := Int.emod_add_mul_ediv i (P:ℤ); omega
  have h := orbit_congruence f L Q hq (u^P) δ N U hw
    (y*(↑(u^k.val):R)) hδ (hL k) (i/P)
  rw [mul_assoc,← Units.val_mul,← hp,hi,zero_sub] at h
  exact dvd_neg.mp h


end
end Tetrahedral.QuadraticPolynomial
