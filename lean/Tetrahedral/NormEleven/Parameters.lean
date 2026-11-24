import Tetrahedral.SelectedParameters
import Tetrahedral.D3Parameters

namespace Tetrahedral.NormEleven

/-- Recover the positive square coefficient without constructing a Pell orbit. -/
theorem square_coefficient (A a b n y : ℤ)
    (hf : a^2-2*b^2+2*A*a*b=1) (hn : n=A*(a^2-2*b^2)-4*a*b)
    (hy : n^2+2=(A^2+2)*y^2) (hy0 : 0≤y) : y=a^2+2*b^2 := by
  have hid : (A*(a^2-2*b^2)-4*a*b)^2+2*(a^2-2*b^2+2*A*a*b)^2=
      (A^2+2)*(a^2+2*b^2)^2 := by ring
  rw [← hn,hf] at hid
  have hz : (A^2+2)*(y^2-(a^2+2*b^2)^2)=0 := by linear_combination hid-hy
  have he := (mul_eq_zero.mp hz).resolve_left (by nlinarith [sq_nonneg A])
  exact (sq_eq_sq₀ hy0 (by positivity)).mp (by nlinarith only [he])

/-- The relative norm is 11 for every square representation of w. -/
theorem norm_eleven (d e B C n y r u v : ℤ)
    (hn : n=B*(u^2+e*v^2)+2*e*C*u*v)
    (hy : y=C*(u^2+e*v^2)+2*B*u*v)
    (hr : n+3=d*r^2) (he : n^2+2=e*y^2) :
    (n+3)^2+e*y^2-2*d*r^2*(B*(u^2+e*v^2)+2*e*C*u*v)=11 ∧
    2*(n+3)*y-2*d*r^2*(C*(u^2+e*v^2)+2*B*u*v)=0 := by
  rw [← hn,← hy]
  constructor
  · linear_combination 2*n*hr-he
  · linear_combination 2*y*hr

theorem d1_parameters (n r y : ℕ) (hr : n+3=r^2) (hy : n^2+2=6*y^2) :
    ∃ u v : ℤ, (n:ℤ)=22*(u^2+6*v^2)+108*u*v ∧
      (y:ℤ)=9*(u^2+6*v^2)+44*u*v := by
  obtain ⟨a,b,hf,hn,_,_⟩ := SpecialPell.d1_parameters n r y hr hy
  have hY := square_coefficient (-2) a b n y (by nlinarith only [hf]) hn (by norm_num; exact_mod_cast hy) (by positivity)
  refine ⟨5*a+2*b,-2*a-b,?_,?_⟩
  · rw [hn]; ring
  · rw [hY]; ring

theorem d2_parameters (n r y : ℕ) (hr : n+3=2*r^2) (hy : n^2+2=3*y^2) :
    ∃ u v : ℤ, (n:ℤ)=5*(u^2+3*v^2)+18*u*v ∧
      (y:ℤ)=3*(u^2+3*v^2)+10*u*v := by
  obtain ⟨a,b,hf,hn,_,_⟩ := SpecialPell.d2_parameters n r y hr hy
  have hY := square_coefficient (-1) a b n y (by nlinarith only [hf])
    (by simpa using hn) (by norm_num; exact_mod_cast hy) (by positivity)
  refine ⟨2*a+b,-a-b,?_,?_⟩
  · rw [hn]; ring
  · rw [hY]; ring

theorem d3_parameters (n r y : ℕ) (hr : n+3=3*r^2) (hy : n^2+2=2*y^2) :
    ∃ u v : ℤ, (n:ℤ)=4*u*v ∧ (y:ℤ)=u^2+2*v^2 := by
  obtain ⟨a,b,hf,hn,_,_⟩ := SpecialPell.d3_parameters n r y hr hy
  have hY := square_coefficient 0 a b n y (by simpa using hf)
    (by simpa using hn) (by norm_num; exact_mod_cast hy) (by positivity)
  exact ⟨a,-b,by rw [hn]; ring,by rw [hY]; ring⟩

theorem d11_parameters (n r y : ℕ) (hr : n+3=11*r^2) (hy : n^2+2=66*y^2) :
    ∃ u v : ℤ, (n:ℤ)=8*(u^2+66*v^2)+132*u*v ∧
      (y:ℤ)=u^2+66*v^2+16*u*v := by
  obtain ⟨a,b,hf,hn,_,_⟩ := SpecialPell.d11_parameters n r y hr hy
  have hY := square_coefficient 8 a b n y hf hn (by norm_num; exact_mod_cast hy) (by positivity)
  refine ⟨a+8*b,-b,?_,?_⟩
  · rw [hn]; ring
  · rw [hY]; ring

theorem d66_parameters (n r y : ℕ) (hr : n+3=66*r^2) (hy : n^2+2=11*y^2) :
    ∃ u v : ℤ, (n:ℤ)=63*(u^2+11*v^2)+418*u*v ∧
      (y:ℤ)=19*(u^2+11*v^2)+126*u*v := by
  obtain ⟨A,a,b,hA,hf,hn,_⟩ := SpecialPell.natural_norm_two_parameters 3 n y
    (by decide) (by norm_num; exact hy)
  rcases hA with hA|hA
  · rw [hA] at hf hn
    have hoff := SpecialPell.parameter_offset 3 a b hf
    have hn' : (n:ℤ)=3-22*a*b := hn.trans hoff
    have hr' : (n:ℤ)+3=66*(r:ℤ)^2 := by exact_mod_cast hr
    have hd : (11:ℤ) ∣ 6 := ⟨2*a*b+6*(r:ℤ)^2,by linear_combination hr'-hn'⟩
    norm_num at hd
  · rw [hA] at hf hn
    have hY := square_coefficient (-3) a b n y hf hn (by norm_num; exact_mod_cast hy) (by positivity)
    refine ⟨10*a+3*b,-3*a-b,?_,?_⟩
    · rw [hn]; ring
    · rw [hY]; ring

end Tetrahedral.NormEleven
