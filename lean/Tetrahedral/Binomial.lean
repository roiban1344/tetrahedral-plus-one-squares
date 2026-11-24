import Mathlib.Tactic

namespace Tetrahedral
section
variable {R : Type*} [CommRing R]

theorem inverse_first_order (w : Rˣ) (δ u : R) (hw : (w : R) = 1+δ*u) :
    (↑w⁻¹ : R) = 1-δ*u+δ^2*u^2*(↑w⁻¹ : R) := by
  have h := w.mul_inv
  rw [hw] at h
  linear_combination (1-δ*u)*h

/-- Negative exponents have the same first-order expansion. Units are explicit,
so no inversion of a nonunit or division by an even integer is hidden. -/
theorem first_order_zpow (w : Rˣ) (δ u : R) (hw : (w : R) = 1+δ*u) (a : ℤ) :
    ∃ E : R, (↑(w^a) : R) = 1+(a : R)*δ*u+δ^2*E := by
  refine Int.induction_on a ?_ ?_ ?_
  · exact ⟨0, by simp⟩
  · intro n ih
    obtain ⟨E,hE⟩ := ih
    refine ⟨E*(↑w : R)+(n : R)*u^2, ?_⟩
    rw [zpow_add, zpow_one, Units.val_mul, hE, hw]
    push_cast
    ring
  · intro n ih
    obtain ⟨E,hE⟩ := ih
    refine ⟨E*(↑w⁻¹ : R) + (1-(n : R)*δ*u)*(u^2*(↑w⁻¹ : R)) + (n : R)*u^2, ?_⟩
    rw [zpow_sub, zpow_one, Units.val_mul, hE]
    push_cast
    have hInv := inverse_first_order w δ u hw
    linear_combination (1-(n : R)*δ*u)*hInv


/-- One unit, one integer exponent, and repeated squaring.
No second unit or two-variable expansion is involved. -/
theorem dyadic_zpow_precision (w : Rˣ) (t k : ℕ) (U : R)
    (hw : (w:R)=1+(2:R)^(t+1)*U) (a : ℤ) :
    ∃ E : R, (↑(w^((2:ℤ)^k*a)):R)=
      1+2^(k+t+1)*((a:R)*U+2^t*E) := by
  have squares (j : ℕ) : ∃ V : R,
      (w:R)^(2^j:ℕ)=1+2^(j+t+1)*(U+2^t*V) := by
    induction j with
    | zero => exact ⟨0,by simpa using hw⟩
    | succ j ih =>
      obtain ⟨V,hV⟩ := ih
      refine ⟨V+2^j*(U+2^t*V)^2,?_⟩
      rw [show (2:ℕ)^(j+1)=2^j*2 by rw [pow_succ],pow_mul,hV]
      simp only [pow_add,pow_succ]
      ring
  obtain ⟨V,hV⟩ := squares k
  have hv : (↑(w^(2^k:ℕ)):R)=1+2^(k+t+1)*(U+2^t*V) := hV
  obtain ⟨E,hE⟩ := first_order_zpow (w^(2^k:ℕ)) ((2:R)^(k+t+1)) (U+2^t*V) hv a
  refine ⟨(a:R)*V+2^(k+1)*E,?_⟩
  have hp : w^((2:ℤ)^k*a)=(w^(2^k:ℕ))^a := by
    rw [← zpow_natCast,← zpow_mul]
    push_cast
    rfl
  rw [hp,hE]
  simp only [pow_add,pow_succ]
  ring

end
end Tetrahedral

