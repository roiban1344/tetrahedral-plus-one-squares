import Mathlib.Tactic

namespace Tetrahedral.RelativeDirection

/-- The norm-one equation for 1+4qU determines the base coordinates of U. -/
theorem trace (q a N : ℤ) (hq : q≠0)
    (h : 1+8*q*a+16*q^2*N=1) : a= -2*q*N := by
  have he : q*(a+2*q*N)=0 := by nlinarith only [h]
  have := (mul_eq_zero.mp he).resolve_left hq
  linarith

/-- The square of a relative unit direction is its norm times minus the unit. -/
theorem square {R : Type*} [CommRing R] (U V N : R) (c : ℤ)
    (hN : U*V=N) (htrace : U+V= -c • N) :
    U^2= -(1+c • U)*N := by
  simp only [zsmul_eq_mul] at htrace ⊢
  push_cast at htrace
  linear_combination U*htrace-hN

theorem norm_two (a b H K q e : ℤ)
    (ha : a= -2*q*H) (hb : b= -2*q*K)
    (hH : 2 ∣ H-a^2-e*b^2) (hK : 2 ∣ K-2*a*b) :
    2 ∣ H ∧ 2 ∣ K := by
  obtain ⟨p,hp⟩ := hH; obtain ⟨r,hr⟩ := hK
  constructor
  · refine ⟨2*q^2*(H^2+e*K^2)+p,?_⟩
    rw [ha,hb] at hp; linear_combination hp
  · refine ⟨4*q^2*H*K+r,?_⟩
    rw [ha,hb] at hr; linear_combination hr

theorem norm_four (a b H K q e : ℤ)
    (ha : a= -2*q*H) (hb : b= -2*q*K)
    (hH : 4 ∣ H-a^2-e*b^2) (hK : 4 ∣ K-2*a*b) :
    4 ∣ H ∧ 4 ∣ K := by
  obtain ⟨p,hp⟩ := hH; obtain ⟨r,hr⟩ := hK
  constructor
  · refine ⟨q^2*(H^2+e*K^2)+p,?_⟩
    rw [ha,hb] at hp; linear_combination hp
  · refine ⟨2*q^2*H*K+r,?_⟩
    rw [ha,hb] at hr; linear_combination hr

end Tetrahedral.RelativeDirection
