import Tetrahedral.Binomial

namespace Tetrahedral

theorem consecutive_product_even (a : ℤ) : 2 ∣ a*(a-1) := by
  convert even_iff_two_dvd.mp (Int.even_mul_succ_self (a-1)) using 1 <;> ring

/-- Exact quadratic expansion for an even increment, including negative powers.
The parameter s retains the full divisibility of the cubic remainder. -/
theorem quadratic_even_zpow_factored {R : Type*} [CommRing R]
    (w : Rˣ) (s U : R) (hw : (w:R)=1+2*s*U) (a : ℤ) :
    ∃ E : R, (↑(w^a):R)=1+2*s*(a:R)*U+2*s^2*(a:R)*((a:R)-1)*U^2+8*s^3*U^3*E := by
  refine Int.induction_on a ?_ ?_ ?_
  · exact ⟨0,by simp⟩
  · intro n ih
    obtain ⟨E,hE⟩ := ih
    obtain ⟨k,hk⟩ := consecutive_product_even (n:ℤ)
    have hcast : (n:R)*((n:R)-1)=2*(k:R) := by
      have hh := congrArg (fun z : ℤ => (z:R)) hk
      push_cast at hh
      exact hh
    refine ⟨E*(↑w:R)+(k:R),?_⟩
    rw [zpow_add,zpow_one,Units.val_mul,hE,hw]
    push_cast
    linear_combination 4*s^3*U^3*hcast
  · intro n ih
    obtain ⟨E,hE⟩ := ih
    obtain ⟨k,hk⟩ := consecutive_product_even (-(n:ℤ)-1)
    have hcast : (-(n:R)-1)*(-(n:R)-2)=2*(k:R) := by
      have hh := congrArg (fun z : ℤ => (z:R)) hk
      push_cast at hh
      convert hh using 1 <;> ring
    refine ⟨(E-(k:R))*(↑w⁻¹:R),?_⟩
    have hInv : (1+2*s*U)*(↑w⁻¹:R)=1 := by
      rw [← hw,← Units.val_mul,mul_inv_cancel,Units.val_one]
    rw [zpow_sub,zpow_one,Units.val_mul,hE]
    push_cast
    linear_combination
      (1+2*s*(-(n:R)-1)*U+2*s^2*(-(n:R)-1)*(-(n:R)-2)*U^2)*hInv -
      4*s^3*U^3*(↑w⁻¹:R)*hcast


theorem quadratic_even_zpow {R : Type*} [CommRing R]
    (w : Rˣ) (s U : R) (hw : (w:R)=1+2*s*U) (a : ℤ) :
    ∃ E : R, (↑(w^a):R)=1+2*s*(a:R)*U+2*s^2*(a:R)*((a:R)-1)*U^2+8*s^3*E := by
  obtain ⟨E,hE⟩ := quadratic_even_zpow_factored w s U hw a
  exact ⟨U^3*E,by simpa only [mul_assoc] using hE⟩

theorem quadratic_four_zpow {R : Type*} [CommRing R]
    (w : Rˣ) (U : R) (hw : (w:R)=1+4*U) (a : ℤ) :
    ∃ E : R, (↑(w^a):R)=1+4*(a:R)*U+8*(a:R)*((a:R)-1)*U^2+64*E := by
  have hw' : (w:R)=1+2*(2:R)*U := by convert hw using 1 <;> ring
  obtain ⟨E,hE⟩ := quadratic_even_zpow w 2 U hw' a
  refine ⟨E,?_⟩
  convert hE using 1 <;> ring

end Tetrahedral
