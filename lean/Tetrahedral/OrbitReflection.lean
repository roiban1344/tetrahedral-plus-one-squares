import Mathlib.Tactic

namespace Tetrahedral.OrbitReflection

/-- Every integer power of the relative unit is conjugated by exponent reversal. -/
theorem zpow {M : Type*} [Monoid M] (tau : M →* M) (u : Mˣ)
    (hu : Units.map tau u=u⁻¹) (i : ℤ) :
    tau (↑(u^i):M)=(↑(u^(-i)):M) := by
  have hp := congrArg (fun z : Mˣ => (z:M)) (map_zpow (Units.map tau) u i)
  simpa only [hu,inv_zpow',Units.coe_map] using hp

/-- Conjugation of the initial factor shifts the reflected exponent. -/
theorem point {M : Type*} [Monoid M] (tau : M →* M) (u : Mˣ)
    (hu : Units.map tau u=u⁻¹) (y : M) (c : ℤ)
    (hy : tau y=y*(↑(u^c):M)) (i : ℤ) :
    tau (y*(↑(u^i):M))=y*(↑(u^(c-i)):M) := by
  rw [map_mul,hy,zpow tau u hu i,mul_assoc,← Units.val_mul,← zpow_add,← sub_eq_add_neg]

/-- Fold a reflected pair of residue classes into one local root. Only the
observable value is determined; classifying both exponents is unnecessary. -/
theorem value {V : Type*} (F : ℤ → ℤ) (P : ℤ → V) (c k D : ℤ)
    (hF : ∀ i, F (c-i)=F i) (hP : ∀ i, P (c-i)=P i)
    (hlocal : ∀ a : ℤ, F (k+D*a)=0 → a=0)
    (i : ℤ) (hcover : i%D=k%D ∨ (c-i)%D=k%D) (hi : F i=0) : P i=P k := by
  have local_root (j : ℤ) (hj : j%D=k%D) (hz : F j=0) : j=k := by
    have hd : D ∣ j-k := Int.dvd_of_emod_eq_zero (by
      rw [Int.sub_emod,hj,sub_self,Int.zero_emod])
    obtain ⟨a,ha⟩ := hd
    have he : j=k+D*a := by omega
    have ha0 := hlocal a (by rwa [← he])
    rw [ha0,mul_zero,add_zero] at he
    exact he
  rcases hcover with h|h
  · rw [local_root i h hi]
  · have he := local_root (c-i) h (by rw [hF]; exact hi)
    rw [← hP i,he]

end Tetrahedral.OrbitReflection
