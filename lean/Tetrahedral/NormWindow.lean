import Tetrahedral.IntegerParity
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! A fixed positive norm is reduced by powers of a known unit.
No generation theorem for the full unit group is required. -/
namespace Tetrahedral.NormWindow

theorem norm_minus_two_form (p q e c t : ℤ) (hn : p^2-e*q^2= -2) :
    q*(q*c^2+2*p*c*t+e*q*t^2)=(q*c+p*t)^2+2*t^2 := by
  linear_combination -t^2*hn

theorem positive_pair (S T : ℝ) (hprod : 0<S*T) (hsum : 0<S+T) : 0<S ∧0<T := by
  rcases mul_pos_iff.mp hprod with h|h
  · exact h
  · exfalso; linarith [h.1,h.2]



theorem centered {R : Type*} [Monoid R] (sigma : R →* ℝ) (rho : Rˣ)
    (hLambda : 1<sigma (rho:R)) (N : ℝ) (hN : 0<N)
    (u : R) (hne : sigma u≠0) :
    ∃ i : ℤ, N≤(sigma (u*(↑(rho^(-i)):R)))^2*sigma (rho:R) ∧
      (sigma (u*(↑(rho^(-i)):R)))^2<N*sigma (rho:R) := by
  let L := sigma (rho:R)
  have hL : 0<L := by dsimp [L]; linarith
  have hL2 : 1<L^2 := by nlinarith [hLambda]
  have hu2 : 0<(sigma u)^2 := sq_pos_of_ne_zero hne
  let A := (sigma u)^2*L/N
  have hA : 0<A := by dsimp [A]; positivity
  obtain ⟨i,hi1,hi2⟩ := exists_mem_Ico_zpow hA hL2
  have sigpow (j : ℤ) : sigma (↑(rho^j):R)=L^j := by
    have hh := congrArg (fun z : ℝˣ => (z:ℝ)) (map_zpow (Units.map sigma) rho j)
    simpa only [Units.coe_map,Units.val_zpow_eq_zpow_val] using hh
  let M := (L^2)^(-i)
  have hM : 0<M := zpow_pos (sq_pos_of_pos hL) _
  have hs : (sigma (u*(↑(rho^(-i)):R)))^2=(sigma u)^2*M := by
    rw [map_mul,sigpow,mul_pow]
    have hh : (L^(-i))^2=(L^2)^(-i) := by simp only [pow_two,mul_zpow]
    rw [hh]
  have hc : (L^2)^i*M=1 := by
    dsimp [M]; rw [←zpow_add₀ (ne_of_gt (sq_pos_of_pos hL))]; simp
  have hc' : (L^2)^(i+1)*M=L^2 := by
    dsimp [M]; rw [←zpow_add₀ (ne_of_gt (sq_pos_of_pos hL))]; simp
  have hl : 1≤A*M := by
    have hh := mul_le_mul_of_nonneg_right hi1 hM.le
    rwa [hc] at hh
  have hh : A*M<L^2 := by
    have hh := mul_lt_mul_of_pos_right hi2 hM
    rwa [hc'] at hh
  have he : A*M*N=(sigma (u*(↑(rho^(-i)):R)))^2*L := by
    rw [hs]; dsimp [A]; field_simp
  refine ⟨i,?_,?_⟩
  · have hp := mul_le_mul_of_nonneg_right hl hN.le
    nlinarith only [hp,he]
  · have hp := mul_lt_mul_of_pos_right hh hN
    by_contra hn
    have hge : N*L≤(sigma (u*(↑(rho^(-i)):R)))^2 := le_of_not_gt hn
    have hx := mul_nonneg (sub_nonneg.mpr hge) hL.le
    nlinarith only [hp,he,hx]

theorem map_unit_zpow {R : Type*} [Monoid R] (sigma : R →* ℝ) (rho : Rˣ) (i : ℤ) :
    sigma (↑(rho^i):R)=(sigma (rho:R))^i := by
  have hh := congrArg (fun z : ℝˣ => (z:ℝ)) (map_zpow (Units.map sigma) rho i)
  simpa only [Units.coe_map,Units.val_zpow_eq_zpow_val] using hh

theorem centered_positive {R : Type*} [Monoid R] (sigma : R →* ℝ) (rho : Rˣ)
    (hLambda : 1<sigma (rho:R)) (N : ℝ) (hN : 0<N)
    (x : R) (hx : 0<sigma x) :
    ∃ v : R, ∃ i : ℤ, v=x*(↑(rho^(-i)):R) ∧x=v*(↑(rho^i):R) ∧
      0<sigma v ∧N≤(sigma v)^2*sigma (rho:R) ∧(sigma v)^2<N*sigma (rho:R) := by
  obtain ⟨i,hlo,hhi⟩ := centered sigma rho hLambda N hN x (ne_of_gt hx)
  let v := x*(↑(rho^(-i)):R)
  refine ⟨v,i,rfl,?_,?_,hlo,hhi⟩
  · dsimp [v]; rw [mul_assoc,←Units.val_mul,←zpow_add]; simp
  · dsimp [v]; rw [map_mul,map_unit_zpow]
    exact mul_pos hx (zpow_pos (by linarith [hLambda]) _)

theorem trace_window (S T A N L : ℝ) (hprod : S*T=N) (hS0 : 0<S) (hN : 0<N)
    (htrace : 2*A=S+T) (hlo : N≤S^2*L) (hhi : S^2≤N*L) :
    0<A ∧4*A^2≤N*(L+3) := by
  have hT0 : 0<T := pos_of_mul_pos_right (by rw [hprod]; exact hN) hS0.le
  have hp : S^2*T^2=N^2 := by rw [←mul_pow,hprod]
  have hpL := congrArg (fun z : ℝ => z*L) hp
  have hTb : T^2≤N*L := by
    by_contra h
    have hh := mul_nonneg (sub_nonneg.mpr hlo) (sq_nonneg T)
    have hn := mul_pos hN (sub_pos.mpr (lt_of_not_ge h))
    nlinarith only [hh,hpL,hn]
  have hsum : S^2+T^2≤N*L+N := by
    by_cases hs : S^2≤N
    · linarith
    · have ht : T^2≤N := by
        have hh := mul_nonneg (sub_nonneg.mpr (le_of_lt (lt_of_not_ge hs))) (sq_nonneg T)
        by_contra ht
        have hn := mul_pos hN (sub_pos.mpr (lt_of_not_ge ht))
        nlinarith only [hh,hp,hn]
      linarith
  have he : 4*A^2=S^2+T^2+2*N := by
    linear_combination (2*A+S+T)*htrace+2*hprod
  constructor <;> nlinarith only [hS0,hT0,htrace,he,hsum]

theorem coefficients_nonnegative (a b : ℤ) (s : ℝ) (hs : 0<s)
    (hab : 0≤a*b) (hA : 0<(a:ℝ)+(b:ℝ)*s) : 0≤a ∧0≤b := by
  rcases mul_nonneg_iff.mp hab with h|h
  · exact h
  · have ha : (a:ℝ)≤0 := by exact_mod_cast h.1
    have hb : (b:ℝ)≤0 := by exact_mod_cast h.2
    have hp := mul_nonpos_of_nonpos_of_nonneg hb hs.le
    exfalso; linarith

theorem norm_minus_two_nonnegative (p q e c t : ℤ) (hn : p^2-e*q^2= -2)
    (hq : 0<q) : 0≤q*c^2+2*p*c*t+e*q*t^2 := by
  have hf := norm_minus_two_form p q e c t hn
  by_contra h
  have hh := mul_neg_of_pos_of_neg hq (lt_of_not_ge h)
  nlinarith only [hh,hf,sq_nonneg (q*c+p*t),sq_nonneg t]


theorem parity_two (a b : ℤ) (h : (4:ℤ) ∣ a^2+2*b^2-11) :
    ¬(2:ℤ) ∣ a ∧¬(2:ℤ) ∣ b := by
  have ha2 : (2:ℤ) ∣ a^2-1 := by omega
  have ha4 : (4:ℤ) ∣ a^2-1 :=
    by simpa only [one_pow] using Tetrahedral.IntegerParity.square_difference_four a 1 ha2
  have hb2 : (2:ℤ) ∣ b^2-1 := by omega
  have hae := Tetrahedral.IntegerParity.square_sub_self_even a
  have hbe := Tetrahedral.IntegerParity.square_sub_self_even b
  constructor <;> omega
theorem parity_three (a b : ℤ) (h : (4:ℤ) ∣ a^2+3*b^2-11) :
    (2:ℤ) ∣ a ∧¬(2:ℤ) ∣ b := by
  have hbo : ¬(2:ℤ) ∣ b := by
    intro hb
    obtain ⟨k,hk⟩ := hb
    have hb4 : (4:ℤ) ∣ b^2 := ⟨k^2,by rw [hk]; ring⟩
    have ha2 : (2:ℤ) ∣ a^2-1 := by omega
    have ha4 : (4:ℤ) ∣ a^2-1 :=
      by simpa only [one_pow] using Tetrahedral.IntegerParity.square_difference_four a 1 ha2
    omega
  have hb2 : (2:ℤ) ∣ b^2-1 := by
    have hh := Tetrahedral.IntegerParity.square_sub_self_even b
    omega
  have hb4 : (4:ℤ) ∣ b^2-1 :=
    by simpa only [one_pow] using Tetrahedral.IntegerParity.square_difference_four b 1 hb2
  have ha2 : (2:ℤ) ∣ a^2 := by omega
  have hae := Tetrahedral.IntegerParity.square_sub_self_even a
  exact ⟨by omega,hbo⟩

end Tetrahedral.NormWindow
