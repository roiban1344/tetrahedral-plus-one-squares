import Mathlib.Tactic

namespace Tetrahedral.PositiveOrbit

/-- After two steps both tails lie in a multiplicatively closed positive
cone. Conjugation changes the negative tail into a positive power. -/
theorem nonnegative {R : Type*} [CommRing R]
    (P : R → ℤ) (τ : R →* R) (hP : ∀ x, P (τ x)=P x)
    (w : Rˣ) (hτ : τ (↑w⁻¹:R)=(w:R))
    (C : R → Prop) (h1 : C 1) (hmul : ∀ x y, C x → C y → C (x*y))
    (hC : ∀ x, C x → 0≤P x) (hw : C (w:R)) (y : R)
    (hsmall : ∀ n : Fin 2,
      0≤P (y*(w:R)^n.val) ∧ 0≤P (τ y*(w:R)^n.val))
    (hseed : C (y*(w:R)^2) ∧ C (τ y*(w:R)^2))
    (i : ℤ) : 0≤P (y*(↑(w^i):R)) := by
  have hp (n : ℕ) : C ((w:R)^n) := by
    induction n with
    | zero => simpa using h1
    | succ n ih => rw [pow_succ]; exact hmul _ _ ih hw
  have hnat (z : R) (hs : ∀ n : Fin 2, 0≤P (z*(w:R)^n.val))
      (hz : C (z*(w:R)^2)) (n : ℕ) : 0≤P (z*(w:R)^n) := by
    by_cases hn : n<2
    · exact hs ⟨n,hn⟩
    · obtain ⟨k,rfl⟩ : ∃ k, n=2+k := ⟨n-2,by omega⟩
      rw [pow_add,← mul_assoc]
      exact hC _ (hmul _ _ hz (hp k))
  cases i with
  | ofNat n =>
    change 0≤P (y*(↑(w^(n:ℤ)):R))
    simpa only [zpow_natCast,Units.val_pow_eq_pow_val] using
      hnat y (fun n => (hsmall n).1) hseed.1 n
  | negSucc n =>
    have he : w^(Int.negSucc n)=(w⁻¹)^(n+1) := by
      change w^(-((n+1:ℕ):ℤ))=_
      rw [zpow_neg,zpow_natCast,← inv_pow]
    rw [he,Units.val_pow_eq_pow_val,← hP (y*(↑w⁻¹:R)^(n+1)),map_mul,map_pow,hτ]
    exact hnat (τ y) (fun n => (hsmall n).2) hseed.2 (n+1)

end Tetrahedral.PositiveOrbit
