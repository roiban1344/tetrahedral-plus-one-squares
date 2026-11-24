import Tetrahedral.QuadraticParameters
import Tetrahedral.SquareFactor
import Tetrahedral.IntegerSquareObstructions

namespace Tetrahedral.SpecialPell
set_option maxHeartbeats 400000

/-- A square root of a positive Pell solution has norm plus or minus one. -/
theorem pell_two_square_root (X Y : ℤ) (hX : 0<X) (hY : 0≤Y) (hn : X^2-2*Y^2=1) :
    ∃ p q : ℤ, X=p^2+2*q^2 ∧ Y= -2*p*q ∧
      (p^2-2*q^2=1 ∨ p^2-2*q^2= -1) := by
  by_cases hX1 : X=1
  · have hY0 : Y=0 := by rw [hX1] at hn; nlinarith only [hn]
    exact ⟨1,0,by simp [hX1],by simp [hY0],Or.inl (by norm_num)⟩
  have hye : (2:ℤ) ∣ Y := IntegerParity.even_of_norm_one_mod_four X Y
    ⟨Y^2,by linear_combination hn⟩
  have hx2 : (2:ℤ) ∣ X^2-1 := ⟨Y^2,by linear_combination hn⟩
  have hxpar := IntegerParity.square_sub_self_even X
  have hxe : (2:ℤ) ∣ X-1 := by omega
  obtain ⟨v,hv⟩ := hxe
  obtain ⟨z,hz⟩ := hye
  have hvpos : 0<v := by omega
  have hup : 0<v+1 := by omega
  have hznon : 0≤z := by omega
  have hc : IsCoprime (v+1) v := ⟨1,-1,by ring⟩
  have hxv : X=2*v+1 := by omega
  have hprod : (v+1)*v=2*z^2 := by rw [hz,hxv] at hn; nlinarith only [hn]
  have finish (s t : ℤ) (hs0 : 0≤s) (ht0 : 0≤t)
      (hxx : X=s^2+2*t^2) (hzz : z^2=(s*t)^2)
      (hf : s^2-2*t^2=1 ∨ s^2-2*t^2= -1) :
      ∃ p q : ℤ, X=p^2+2*q^2 ∧ Y= -2*p*q ∧
        (p^2-2*q^2=1 ∨ p^2-2*q^2= -1) := by
    have hzt : z=s*t := (pow_left_inj₀ hznon (mul_nonneg hs0 ht0) (by decide : 2≠0)).mp hzz
    exact ⟨s,-t,by simpa only [neg_sq] using hxx,by rw [hz,hzt];ring,
      by simpa only [neg_sq] using hf⟩
  rcases int_prime_square_split hup hvpos (by decide : Nat.Prime 2) hc hprod with
    ⟨s,t,hs0,ht0,hs,ht⟩|⟨s,t,hs0,ht0,hs,ht⟩
  · norm_num at hs
    refine finish t s ht0 hs0 ?_ ?_ ?_
    · nlinarith only [hv,hs,ht]
    · rw [hs,ht] at hprod; nlinarith only [hprod]
    · right; nlinarith only [hs,ht]
  · norm_num at ht
    refine finish s t hs0 ht0 ?_ ?_ ?_
    · nlinarith only [hv,hs,ht]
    · rw [hs,ht] at hprod; nlinarith only [hprod]
    · left; nlinarith only [hs,ht]

/-- The exceptional e=2 branch uses coprime consecutive factors directly.
Divisibility by three selects the square root with norm one. -/
theorem d3_parameters (n r y : ℕ) (hr : n+3=3*r^2) (hy : n^2+2=2*y^2) :
    ∃ a b : ℤ, a^2-2*b^2=1 ∧ (n:ℤ)= -4*a*b ∧
      3*(r:ℤ)^2=3*a^2-4*a*b-6*b^2 ∧ IsCoprime a b := by
  have hy' : (n:ℤ)^2+2=2*(y:ℤ)^2 := by exact_mod_cast hy
  have hn2 : (2:ℤ) ∣ n := by
    have hsq := IntegerParity.square_sub_self_even (n:ℤ)
    have h2 : (2:ℤ) ∣ (n:ℤ)^2 := ⟨(y:ℤ)^2-1,by linear_combination hy'⟩
    omega
  obtain ⟨N,hN⟩ := hn2
  have hNN : 0 ≤ N := by
    have : (0:ℤ) ≤ n := by positivity
    omega
  have hny : (y:ℤ)^2-2*N^2=1 := by rw [hN] at hy';nlinarith [hy']
  have hypos : 0 < (y:ℤ) := by
    have hnon : (0:ℤ) ≤ y := by positivity
    nlinarith [hny,sq_nonneg N]
  have hN3 : N%3=0 := by
    have hr' : (n:ℤ)+3=3*(r:ℤ)^2 := by exact_mod_cast hr
    omega
  obtain ⟨p,q,_,hdouble,hcases⟩ := pell_two_square_root (y:ℤ) N hypos hNN hny
  have hf : p^2-2*q^2=1 := by
    rcases hcases with h|h
    · exact h
    · exfalso
      have hd : (3:ℤ) ∣ p*q := by
        have hdN : (3:ℤ) ∣ N := Int.dvd_of_emod_eq_zero hN3
        rw [hdouble] at hdN
        simp only [mul_assoc] at hdN
        omega
      exact IntegerSquareObstructions.negative_two_norm p q h hd
  refine ⟨p,q,hf,?_,?_,?_⟩
  · nlinarith only [hN,hdouble]
  · have hr' : (n:ℤ)+3=3*(r:ℤ)^2 := by exact_mod_cast hr
    nlinarith only [hr',hf,hN,hdouble]
  · exact form_coprime 0 p q (by simpa using hf)

end Tetrahedral.SpecialPell
