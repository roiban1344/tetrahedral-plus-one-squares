import Tetrahedral.Binomial

namespace Tetrahedral.QuadraticPolynomial

section
variable {R : Type*} [CommRing R]

/-- The dyadic descent also applies to a quadratic polynomial with a constant
and a linear part. Only its expansion at the chosen zero is needed. -/
theorem exponent_unique_precision (f : R → ℤ) (L : R →ₗ[ℤ] ℤ) (Q : R → ℤ)
    (y : R) (w : Rˣ) (t v : ℕ) (U : R)
    (hw : (↑w:R)=1+2^(t+1)*U) (hv : v≤t+1) (hy : f y=0)
    (hquad : ∀ z (n : ℤ), f (y+n • z)=f y+n*L z+n^2*Q z)
    (hlinear : ∀ z, (2:ℤ)^v ∣ 2^t*L z)
    (hkernel : ∀ a : ℤ, (2:ℤ)^v ∣ a*L (y*U) → 2 ∣ a)
    (i : ℤ) (hi : f (y*(↑(w^i):R))=0) : i=0 := by
  have parity (k : ℕ) (a : ℤ) (ha : f (y*(↑(w^((2:ℤ)^k*a)):R))=0) : 2 ∣ a := by
    obtain ⟨E,hE⟩ := dyadic_zpow_precision w t k U hw a
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
    have hd := (hlinear (y*E)).add
      ((pow_dvd_pow (2:ℤ) (show v≤k+t+1 by omega)).mul_right (Q V))
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

theorem exponent_unique (f : R → ℤ) (L : R →ₗ[ℤ] ℤ) (Q : R → ℤ)
    (y : R) (w : Rˣ) (t : ℕ) (U : R)
    (hw : (↑w:R)=1+2^(t+1)*U) (hy : f y=0)
    (hquad : ∀ z (n : ℤ), f (y+n • z)=f y+n*L z+n^2*Q z)
    (hkernel : ∀ a : ℤ, (2:ℤ)^t ∣ a*L (y*U) → 2 ∣ a)
    (i : ℤ) (hi : f (y*(↑(w^i):R))=0) : i=0 :=
  exponent_unique_precision f L Q y w t t U hw (by omega) hy hquad
    (by intro z; exact dvd_mul_right _ _) hkernel i hi

/-- An even first variation saves one bit in the step of the unit. -/
theorem exponent_unique_even (f : R → ℤ) (L : R →ₗ[ℤ] ℤ) (Q : R → ℤ)
    (y : R) (w : Rˣ) (t : ℕ) (U : R)
    (hw : (↑w:R)=1+2^(t+1)*U) (hy : f y=0)
    (hquad : ∀ z (n : ℤ), f (y+n • z)=f y+n*L z+n^2*Q z)
    (hlinear : ∀ z, (2:ℤ) ∣ L z)
    (hkernel : ∀ a : ℤ, (2:ℤ)^(t+1) ∣ a*L (y*U) → 2 ∣ a)
    (i : ℤ) (hi : f (y*(↑(w^i):R))=0) : i=0 :=
  exponent_unique_precision f L Q y w t (t+1) U hw le_rfl hy hquad (by
    intro z; obtain ⟨c,hc⟩ := hlinear z
    exact ⟨c,by rw [hc,pow_succ]; ring⟩) hkernel i hi

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

/-- Different phases may be obstructed at different precisions. There is no
need to impose the largest precision on phases already excluded earlier. -/
theorem phase_roots {C J : Type*} (u : Rˣ) (P : ℕ) (hP : 0<P)
    (δ : ℤ) (U : R) (hw : (↑(u^P):R)=1+(δ:R)*U) (y : R)
    (centre : C → ℤ) (modulus : J → ℤ)
    (hcert : ∀ k : Fin P, (∃ c, (k.val:ℤ)=centre c%P) ∨
      ∃ j, modulus j ∣ δ^2 ∧
        modulus j ∣ δ*L (y*(↑(u^k.val):R)) ((y*(↑(u^k.val):R))*U) ∧
        ¬ modulus j ∣ f (y*(↑(u^k.val):R)))
    (i : ℤ) (hi : f (y*(↑(u^i):R))=0) : ∃ c, i%P=centre c%P := by
  have hlo := Int.emod_nonneg i (show (P:ℤ)≠0 by omega)
  have hhi := Int.emod_lt_of_pos i (show (0:ℤ)<P by omega)
  let k : Fin P := ⟨(i%P).toNat,by omega⟩
  have hk : (k.val:ℤ)=i%P := by dsimp [k]; omega
  rcases hcert k with ⟨c,hc⟩|⟨j,hδ,hL,hf⟩
  · exact ⟨c,by rw [← hk]; exact hc⟩
  · have hp : u^i=u^k.val*(u^P)^(i/P) := by
      rw [← zpow_natCast,← zpow_natCast u P,← zpow_mul,← zpow_add,hk]
      congr 1; have := Int.emod_add_mul_ediv i (P:ℤ); omega
    have h := orbit_congruence f L Q hq (u^P) δ (modulus j) U hw
      (y*(↑(u^k.val):R)) hδ hL (i/P)
    rw [mul_assoc,← Units.val_mul,← hp,hi,zero_sub] at h
    exact absurd (dvd_neg.mp h) hf

theorem lift_roots {C : Type*} (u : Rˣ) (P : ℕ) (t : ℕ) (U : R)
    (hw : (↑(u^P):R)=1+2^(t+1)*U) (y : R) (centre : C → ℤ)
    (hz : ∀ c, f (y*(↑(u^(centre c)):R))=0)
    (hk : ∀ c (a : ℤ), (2:ℤ)^t ∣ a*L (y*(↑(u^(centre c)):R))
      ((y*(↑(u^(centre c)):R))*U) → 2 ∣ a)
    (i : ℤ) (hi : f (y*(↑(u^i):R))=0)
    (hphase : ∃ c, i%P=centre c%P) : ∃ c, i=centre c := by
  obtain ⟨c,hc⟩ := hphase
  have hd : (P:ℤ) ∣ i-centre c := Int.dvd_of_emod_eq_zero (by
    rw [Int.sub_emod,hc,sub_self,Int.zero_emod])
  obtain ⟨a,ha⟩ := hd
  have he : i=centre c+P*a := by omega
  have hp : u^i=u^(centre c)*(u^P)^a := by
    rw [← zpow_natCast,← zpow_mul,← zpow_add,← he]
  have ha0 := exponent_unique f (L (y*(↑(u^(centre c)):R))) Q
    (y*(↑(u^(centre c)):R)) (u^P) t U hw (hz c) (hq _) (hk c) a
    (by simpa only [hp,Units.val_mul,mul_assoc] using hi)
  exact ⟨c,by simpa only [ha0,mul_zero,add_zero] using he⟩

end
end Tetrahedral.QuadraticPolynomial
