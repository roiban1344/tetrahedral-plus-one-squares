import Mathlib.Tactic
namespace Tetrahedral.IntegerParity

theorem square_sub_self_even (x : ℤ) : 2 ∣ x^2-x := by
  convert even_iff_two_dvd.mp (Int.even_mul_succ_self (x-1)) using 1 <;> ring

theorem square_difference_four (x y : ℤ) (h : 2 ∣ x^2-y^2) : 4 ∣ x^2-y^2 := by
  have hx := square_sub_self_even x
  have hy := square_sub_self_even y
  have hxy : (2:ℤ) ∣ x-y := by omega
  obtain ⟨k,hk⟩ := hxy
  refine ⟨k*(y+k),?_⟩
  linear_combination (x+y+2*k)*hk

theorem odd_square_eight (x : ℤ) (hx : ¬2 ∣ x) : 8 ∣ x^2-1 := by
  have he : 2 ∣ x-1 := by omega
  obtain ⟨z,hz⟩ := he
  obtain ⟨k,hk⟩ := square_sub_self_even (z+1)
  refine ⟨k,?_⟩
  have hxx : x=2*z+1 := by omega
  rw [hxx]
  linear_combination 4*hk

theorem norm_minus_two_mod_four (n y e : ℤ) (h : e%4=1)
    (he : n^2+2=e*y^2) : False := by
  have hd : (4:ℤ) ∣ e-1 := by omega
  obtain ⟨k,hk⟩ := hd
  have h4 : (4:ℤ) ∣ n^2-y^2+2 := by
    refine ⟨k*y^2,?_⟩
    linear_combination he+y^2*hk
  have h2 : (2:ℤ) ∣ n^2-y^2 := by omega
  have hh := square_difference_four n y h2
  omega
theorem even_of_norm_one_mod_four (a c : ℤ) (h : 4 ∣ a^2+2*c^2-1) : 2 ∣ c := by
  have ha2 : (2:ℤ) ∣ a^2-1 := by omega
  have ha4 : (4:ℤ) ∣ a^2-1 := by
    simpa only [one_pow] using square_difference_four a 1 ha2
  have hc2 : (2:ℤ) ∣ c^2 := by omega
  have hp := square_sub_self_even c
  omega

end Tetrahedral.IntegerParity
