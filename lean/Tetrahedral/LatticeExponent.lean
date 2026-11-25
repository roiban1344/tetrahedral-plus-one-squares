import Tetrahedral.FactoredExponent

namespace Tetrahedral.LatticeExponent

/-- Integer divisibility of a linear map need only be checked on a basis. -/
theorem dvd_basis {R : Type*} [AddCommGroup R] (basis : Fin 4 → R)
    (coords : R → Fin 4 → ℤ) (repr : ∀ E, E=∑ j, coords E j • basis j)
    (P : R →ₗ[ℤ] ℤ) (D : ℤ) (h : ∀ j, D ∣ P (basis j)) (E : R) : D ∣ P E := by
  rw [repr E,map_sum]
  apply Finset.dvd_sum
  intro j _
  simpa only [map_smul,smul_eq_mul] using (h j).mul_left (coords E j)

/-- If every integer coordinate is divisible, the element itself is a multiple. -/
theorem smul_basis {R : Type*} [AddCommGroup R] (basis : Fin 4 → R)
    (coords : R → Fin 4 → ℤ) (repr : ∀ E, E=∑ j, coords E j • basis j)
    (m : ℤ) (T : R) (h : ∀ j, m ∣ coords T j) : ∃ V, T=m • V := by
  refine ⟨∑ j, (coords T j/m) • basis j,?_⟩
  conv_lhs => rw [repr T]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [smul_smul,Int.mul_ediv_cancel' (h j)]

def mulLinear {R : Type*} [CommRing R] (T : R) : R →ₗ[ℤ] R where
  toFun E := T*E
  map_add' := mul_add T
  map_smul' c E := by simp only [RingHom.id_apply,mul_smul_comm]

/-- A small coordinate lattice replaces the expansion in arbitrary error
coordinates. Only four linear columns and one extra scalar bit are needed. -/
theorem unique {R : Type*} [CommRing R]
    (f : R → ℤ) (L : R →ₗ[ℤ] ℤ) (Q : R → ℤ)
    (A B : R →ₗ[ℤ] ℤ) (e : ℤ)
    (y : R) (w : Rˣ) (t v : ℕ) (ht : 1≤t) (U : R)
    (hw : (w:R)=1+2^(t+1)*U) (hy : f y=0)
    (hquad : ∀ z (n : ℤ), f (y+n • z)=f y+n*L z+n^2*Q z)
    (hnorm : ∀ z, Q z=(A z)^2-e*(B z)^2)
    (m : ℤ) (hm : m≠0) (hv : (2:ℤ)^v=2^(t+1)*m^2)
    (F T : R) (hF : y*U=F) (hT : y*U^2=T)
    (basis : Fin 4 → R) (coords : R → Fin 4 → ℤ)
    (repr : ∀ E, E=∑ j, coords E j • basis j)
    (hfirst : m ∣ A F ∧ m ∣ B F)
    (hscalar : 2*m^2 ∣ L T)
    (hsquare : ∀ j, m ∣ coords (U^2) j)
    (hcolumns : ∀ j, m^2 ∣ L (T*basis j))
    (hderivative : (2:ℤ)^v ∣ L F-2^t*m^2)
    (i : ℤ) (hi : f (y*(↑(w^i):R))=0) : i=0 := by
  have column (P : R →ₗ[ℤ] ℤ) (D : ℤ)
      (h : ∀ j, D ∣ P (T*basis j)) (E : R) : D ∣ P (T*E) :=
    dvd_basis basis coords repr (P.comp (mulLinear T)) D h E
  obtain ⟨W,hW⟩ := smul_basis basis coords repr m (U^2) hsquare
  have hTm : T=m • (y*W) := by rw [← hT,hW,mul_smul_comm]
  have coord (P : R →ₗ[ℤ] ℤ) (E : R) : m ∣ P (T*E) := by
    rw [hTm,smul_mul_assoc,map_smul,smul_eq_mul]
    exact dvd_mul_right _ _
  apply FactoredExponent.unique f L Q y w t v ht U hw hy hquad F T hF hT
    ?_ ?_ ?_ i hi
  · intro b E
    have he := column L (m^2) hcolumns E
    have hd : 2*m^2 ∣ L (T*((b:R)+2*E)) := by
      have hz : T*((b:R)+2*E)=b • T+(2:ℤ) • (T*E) := by
        simp only [zsmul_eq_mul]; push_cast; ring
      rw [hz,map_add,map_smul,map_smul,smul_eq_mul,smul_eq_mul]
      have hh := (hscalar.mul_left b).add (mul_dvd_mul_left 2 he)
      convert hh using 1 <;> ring
    have hh := mul_dvd_mul_left ((2:ℤ)^t) hd
    rw [hv]
    convert hh using 1 <;> rw [pow_succ]; ring
  · intro a b E
    let V : R := a • F+((2:ℤ)^t) • (T*((b:R)+2*E))
    have hA : m ∣ A V := by
      simp only [V,map_add,map_smul,smul_eq_mul]
      exact (hfirst.1.mul_left a).add
        ((coord A _).mul_left _)
    have hB : m ∣ B V := by
      simp only [V,map_add,map_smul,smul_eq_mul]
      exact (hfirst.2.mul_left a).add
        ((coord B _).mul_left _)
    obtain ⟨p,hp⟩ := hA; obtain ⟨q,hq⟩ := hB
    have hd : m^2 ∣ Q V := ⟨p^2-e*q^2,by rw [hnorm,hp,hq]; ring⟩
    rw [hv]
    exact mul_dvd_mul_left _ hd
  · intro a ha
    obtain ⟨j,hj⟩ := hderivative
    obtain ⟨b,hb⟩ := ha
    rw [hv,pow_succ] at hj hb
    have hc : (2:ℤ)^t*m^2≠0 := mul_ne_zero (pow_ne_zero _ (by decide)) (pow_ne_zero _ hm)
    refine ⟨b-a*j,?_⟩
    apply mul_left_cancel₀ hc
    linear_combination hb-a*hj

end Tetrahedral.LatticeExponent
