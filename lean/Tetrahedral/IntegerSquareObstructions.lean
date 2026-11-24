import Tetrahedral.IntegerParity
import Mathlib.Data.ZMod.Basic

namespace Tetrahedral.IntegerSquareObstructions

theorem mod_three (x : ℤ) : ¬3 ∣ x^2+1 := by
  have h : ∀ a : ZMod 3, a^2+1≠0 := by decide +kernel
  intro hd
  have hh := (ZMod.intCast_zmod_eq_zero_iff_dvd (x^2+1) 3).mpr hd
  push_cast at hh
  exact h x hh

theorem mod_eight_five (x : ℤ) (h : 8 ∣ x^2-5) : False := by
  have hp := IntegerParity.square_sub_self_even x
  have hx : ¬2 ∣ x := by omega
  have h8 := IntegerParity.odd_square_eight x hx
  omega

theorem negative_two_norm (p q : ℤ) (hf : p^2-2*q^2= -1) (hd : 3 ∣ p*q) : False := by
  rcases (show Prime (3:ℤ) by norm_num).dvd_mul.mp hd with hp|hq
  · obtain ⟨k,hk⟩ := hp
    apply mod_three q
    refine ⟨q^2-k*p,?_⟩
    linear_combination hf-p*hk
  · obtain ⟨k,hk⟩ := hq
    apply mod_three p
    refine ⟨2*k*q,?_⟩
    linear_combination hf+2*q*hk

end Tetrahedral.IntegerSquareObstructions
