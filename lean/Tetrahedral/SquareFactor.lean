import Mathlib.Tactic
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.RingTheory.Int.Basic

namespace Tetrahedral.SpecialPell

/-- Multiply by c: the coprime product A*(c*B) is itself a square. -/
theorem int_square_factor {A B c r : ℤ} (hA : 0<A) (hcop : IsCoprime A (c*B)) (he : A*B=c*r^2) :
    ∃ s : ℤ, A=s^2 := by
  have hp : A*(c*B)=(c*r)^2 := by linear_combination c*he
  obtain ⟨s,hs|hs⟩ := Int.sq_of_isCoprime hcop hp
  · exact ⟨s,hs⟩
  · nlinarith [sq_nonneg s]
/-- Retain both nonnegative square roots after the squarefree multiplier. -/
theorem int_square_pair {A B r : ℤ} {c : ℕ}
    (hA : 0<A) (hB : 0<B) (hc : 0<c) (hcf : Squarefree c)
    (hcop : IsCoprime A ((c:ℤ)*B)) (he : A*B=(c:ℤ)*r^2) :
    ∃ s t : ℤ, 0≤s ∧ 0≤t ∧ A=s^2 ∧ B=(c:ℤ)*t^2 := by
  obtain ⟨s,hs⟩ := int_square_factor hA hcop he
  have hc0 : (0:ℤ)<c := by exact_mod_cast hc
  obtain ⟨t,ht⟩ := int_square_factor (mul_pos hc0 hB) (by simpa using hcop.symm)
    (show ((c:ℤ)*B)*A=1*((c:ℤ)*r)^2 by linear_combination (c:ℤ)*he)
  have hct : (c:ℤ) ∣ t^2 := ⟨B,ht.symm⟩
  obtain ⟨v,hv⟩ := ((Int.squarefree_natCast.mpr hcf).dvd_pow_iff_dvd (by decide : 2≠0)).mp hct
  refine ⟨|s|,|v|,abs_nonneg _,abs_nonneg _,by simpa only [sq_abs] using hs,?_⟩
  rw [sq_abs]
  apply mul_left_cancel₀ hc0.ne'
  calc
    (c:ℤ)*B=t^2 := ht
    _=(c:ℤ)*((c:ℤ)*v^2) := by rw [hv];ring

/-- In a coprime product equal to a prime times a square, the prime belongs
to exactly one factor. All square roots can be chosen nonnegative. -/
theorem int_prime_square_split {A B r : ℤ} {p : ℕ}
    (hA : 0<A) (hB : 0<B) (hp : Nat.Prime p)
    (hc : IsCoprime A B) (he : A*B=(p:ℤ)*r^2) :
    (∃ s t : ℤ, 0≤s ∧ 0≤t ∧ A=(p:ℤ)*s^2 ∧ B=t^2) ∨
    (∃ s t : ℤ, 0≤s ∧ 0≤t ∧ A=s^2 ∧ B=(p:ℤ)*t^2) := by
  have hd : (p:ℤ) ∣ A*B := ⟨r^2,he⟩
  rcases (Nat.prime_iff_prime_int.mp hp).dvd_mul.mp hd with ha|hb
  · have hbp := hc.symm.of_isCoprime_of_dvd_right ha
    obtain ⟨t,s,ht0,hs0,ht,hs⟩ := int_square_pair hB hA hp.pos hp.squarefree
      (hbp.mul_right hc.symm) (by simpa only [mul_comm B A] using he)
    exact Or.inl ⟨s,t,hs0,ht0,hs,ht⟩
  · have hap := hc.of_isCoprime_of_dvd_right hb
    exact Or.inr (int_square_pair hA hB hp.pos hp.squarefree (hap.mul_right hc) he)

end Tetrahedral.SpecialPell
