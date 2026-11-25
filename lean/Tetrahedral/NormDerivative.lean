import Tetrahedral.FactoredExponent

namespace Tetrahedral.NormDerivative
section
variable {R : Type*} [CommRing R]

def value (A B : R →ₗ[ℤ] ℤ) (e : ℤ) (x : R) : ℤ := (A x-3)^2-e*(B x)^2+2
def norm (A B : R →ₗ[ℤ] ℤ) (e : ℤ) (x : R) : ℤ := (A x)^2-e*(B x)^2
def differential (A B : R →ₗ[ℤ] ℤ) (e : ℤ) (y : R) : R →ₗ[ℤ] ℤ where
  toFun z := 2*(A y-3)*A z-2*e*B y*B z
  map_add' x z := by simp only [map_add]; ring
  map_smul' c z := by simp only [map_smul,smul_eq_mul,RingHom.id_apply]; ring

theorem expansion (A B : R →ₗ[ℤ] ℤ) (e : ℤ) (y z : R) (n : ℤ) :
    value A B e (y+n • z)=value A B e y+n*differential A B e y z+n^2*norm A B e z := by
  simp only [value,norm,differential,map_add,map_smul,smul_eq_mul,
    LinearMap.coe_mk,AddHom.coe_mk]; ring

/-- The two coefficients of the norm differential have the same parity at a root. -/
theorem root_parity (e a b : ℤ) (h : a^2-e*b^2+2=0) : (2:ℤ) ∣ a-e*b := by
  have hh := congrArg (fun n : ℤ => (n:ZMod 2)) h
  push_cast at hh
  have hs : ∀ z : ZMod 2, z^2=z := by decide +kernel
  simp only [hs,show (2:ZMod 2)=0 by decide,add_zero] at hh
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd (a-e*b) 2).mp
  push_cast
  exact hh

/-- Width two needs only the factor two in a quadratic differential. -/
theorem image_two (A B : R →ₗ[ℤ] ℤ) (e : ℤ) (y G E : R) :
    (4:ℤ) ∣ differential A B e y ((y*((2:ℤ) • G))*E) := by
  have he : (y*((2:ℤ) • G))*E=(2:ℤ) • (y*G*E) := by
    rw [mul_smul_comm,smul_mul_assoc]
  rw [he]
  simp only [differential,LinearMap.coe_mk,AddHom.coe_mk,map_smul,smul_eq_mul]
  exact ⟨(A y-3)*A (y*G*E)-e*B y*B (y*G*E),by ring⟩

/-- At width four the extra bit comes from the parity character A+B.
A root supplies the coefficient parity. -/
theorem image_four (A B : R →ₗ[ℤ] ℤ) (e : ℤ) (y G E : R)
    (hy : value A B e y=0)
    (hmul : ∀ x z, (2:ℤ) ∣ A (x*z)+B (x*z)-(A x+B x)*(A z+B z))
    (hG : (2:ℤ) ∣ A G+B G) :
    (16:ℤ) ∣ differential A B e y ((y*((4:ℤ) • G))*E) := by
  have hz : (2:ℤ) ∣ A (y*G*E)+B (y*G*E) := by
    have hh := (hmul G (y*E)).add (hG.mul_right (A (y*E)+B (y*E)))
    have he : G*(y*E)=y*G*E := by ring
    rw [he] at hh
    convert hh using 1 <;> ring
  have hp := root_parity e (A y-3) (B y) hy
  have hd : (2:ℤ) ∣ A (y*G*E)-B (y*G*E) := by omega
  have hc : (2:ℤ) ∣ (A y-3)*A (y*G*E)-e*B y*B (y*G*E) := by
    convert (hp.mul_right (A (y*G*E))).add (hd.mul_left (e*B y)) using 1 <;> ring
  have he : (y*((4:ℤ) • G))*E=(4:ℤ) • (y*G*E) := by
    rw [mul_smul_comm,smul_mul_assoc]
  rw [he]
  simp only [differential,LinearMap.coe_mk,AddHom.coe_mk,map_smul,smul_eq_mul]
  convert mul_dvd_mul_left 8 hc using 1 <;> ring

/-- The local descent for the shifted binary norm. Its error terms are
controlled by the parity of the differential. -/
theorem unique (A B : R →ₗ[ℤ] ℤ) (e : ℤ)
    (y : R) (w : Rˣ) (t v : ℕ) (ht : 1≤t) (U : R)
    (hw : (w:R)=1+2^(t+1)*U) (hy : value A B e y=0)
    (h : ℤ) (hh : h≠0) (hv : (2:ℤ)^v=2^(t+1)*h^2)
    (G : R) (hsquare : U^2=h • G)
    (hgood : h=2 ∨ h=4 ∧
      (∀ x z, (2:ℤ) ∣ A (x*z)+B (x*z)-(A x+B x)*(A z+B z)) ∧
      (2:ℤ) ∣ A G+B G)
    (hfirst : h ∣ A (y*U) ∧ h ∣ B (y*U))
    (hscalar : 2*h^2 ∣ differential A B e y (y*U^2))
    (hderivative : (2:ℤ)^v ∣ differential A B e y (y*U)-2^t*h^2)
    (i : ℤ) (hi : value A B e (y*(↑(w^i):R))=0) : i=0 := by
  let L := differential A B e y
  let T := y*U^2
  have hTm : T=h • (y*G) := by dsimp [T]; rw [hsquare,mul_smul_comm]
  have image (E : R) : h^2 ∣ L (T*E) := by
    rcases hgood with rfl|⟨rfl,hmul,hG⟩
    · simpa only [L,T,hsquare,show (2:ℤ)^2=4 by norm_num] using image_two A B e y G E
    · simpa only [L,T,hsquare,show (4:ℤ)^2=16 by norm_num] using image_four A B e y G E hy hmul hG
  have coord (P : R →ₗ[ℤ] ℤ) (E : R) : h ∣ P (T*E) := by
    rw [hTm,smul_mul_assoc,map_smul,smul_eq_mul]
    exact dvd_mul_right _ _
  apply FactoredExponent.unique (value A B e) L (norm A B e) y w t v ht U hw hy
    (expansion A B e y) (y*U) T rfl rfl ?_ ?_ ?_ i hi
  · intro b E
    have hd : 2*h^2 ∣ L (T*((b:R)+2*E)) := by
      have hz : T*((b:R)+2*E)=b • T+(2:ℤ) • (T*E) := by
        simp only [zsmul_eq_mul]; push_cast; ring
      rw [hz,map_add,map_smul,map_smul,smul_eq_mul,smul_eq_mul]
      have hh := (hscalar.mul_left b).add (mul_dvd_mul_left 2 (image E))
      convert hh using 1 <;> ring
    have hh := mul_dvd_mul_left ((2:ℤ)^t) hd
    rw [hv]
    convert hh using 1 <;> rw [pow_succ]; ring
  · intro a b E
    let V : R := a • (y*U)+((2:ℤ)^t) • (T*((b:R)+2*E))
    have hA : h ∣ A V := by
      simp only [V,map_add,map_smul,smul_eq_mul]
      exact (hfirst.1.mul_left a).add ((coord A _).mul_left _)
    have hB : h ∣ B V := by
      simp only [V,map_add,map_smul,smul_eq_mul]
      exact (hfirst.2.mul_left a).add ((coord B _).mul_left _)
    obtain ⟨p,hp⟩ := hA; obtain ⟨q,hq⟩ := hB
    have hd : h^2 ∣ norm A B e V := ⟨p^2-e*q^2,by simp only [norm]; rw [hp,hq]; ring⟩
    rw [hv]
    exact mul_dvd_mul_left _ hd
  · intro a ha
    obtain ⟨j,hj⟩ := hderivative; obtain ⟨b,hb⟩ := ha
    rw [hv,pow_succ] at hj hb
    have hc : (2:ℤ)^t*h^2≠0 := mul_ne_zero (pow_ne_zero _ (by decide)) (pow_ne_zero _ hh)
    refine ⟨b-a*j,?_⟩
    apply mul_left_cancel₀ hc
    linear_combination hb-a*hj

end
end Tetrahedral.NormDerivative
