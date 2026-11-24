import Tetrahedral.QuadraticParameters
import Tetrahedral.IntegerSquareObstructions

namespace Tetrahedral.SpecialPell

private theorem exclude_two (p q r : ℤ) (hf : p^2-2*q^2+4*p*q=1)
    (hr : 2*(p^2-2*q^2)-4*p*q+3=r^2) : False := by
  have hoff := parameter_offset 2 p q (by nlinarith only [hf])
  have hr' : r^2=5-12*p*q := by nlinarith only [hoff,hr]
  have hq : 2 ∣ q := IntegerParity.even_of_norm_one_mod_four p q
    ⟨q^2-p*q,by linear_combination hf⟩
  obtain ⟨k,hk⟩ := hq
  apply IntegerSquareObstructions.mod_eight_five r
  refine ⟨-3*p*k,?_⟩
  rw [hk] at hr'
  nlinarith only [hr']

private theorem exclude_one (p q r : ℤ) (hf : p^2-2*q^2+2*p*q=1)
    (hr : p^2-2*q^2-4*p*q+3=2*r^2) : False := by
  have hoff := parameter_offset 1 p q (by nlinarith only [hf])
  apply IntegerSquareObstructions.mod_three r
  refine ⟨1-p*q,?_⟩
  nlinarith only [hoff,hr]

private theorem exclude_neg_eight (p q r : ℤ) (hf : p^2-2*q^2-16*p*q=1)
    (hr : -8*(p^2-2*q^2)-4*p*q+3=11*r^2) : False := by
  have hoff := parameter_offset (-8) p q (by nlinarith only [hf])
  have hd : (11:ℤ) ∣ 5 := ⟨-r^2-12*p*q,by nlinarith only [hoff,hr]⟩
  norm_num at hd

theorem d1_parameters (n r y : ℕ) (hr : n+3=r^2) (hy : n^2+2=6*y^2) :
    ∃ p q : ℤ, p^2-2*q^2-4*p*q=1 ∧
      (n:ℤ)= -2*(p^2-2*q^2)-4*p*q ∧
      (r:ℤ)^2=p^2-16*p*q-2*q^2 ∧ IsCoprime p q := by
  obtain ⟨A,p,q,hA,hf,hn,hcop⟩ := natural_norm_two_parameters 2 n y (by decide) (by norm_num;exact hy)
  norm_num at hA
  have hr' : (n:ℤ)+3=(r:ℤ)^2 := by exact_mod_cast hr
  rcases hA with rfl|rfl
  · exfalso
    apply exclude_two p q r (by nlinarith [hf])
    nlinarith [hr',hn]
  · refine ⟨p,q,by nlinarith [hf],by nlinarith [hn],?_,hcop⟩
    nlinarith [hf,hn,hr']

theorem d2_parameters (n r y : ℕ) (hr : n+3=2*r^2) (hy : n^2+2=3*y^2) :
    ∃ p q : ℤ, p^2-2*q^2-2*p*q=1 ∧
      (n:ℤ)= -(p^2-2*q^2)-4*p*q ∧
      (r:ℤ)^2=p^2-5*p*q-2*q^2 ∧ IsCoprime p q := by
  obtain ⟨A,p,q,hA,hf,hn,hcop⟩ := natural_norm_two_parameters 1 n y (by decide) (by norm_num;exact hy)
  norm_num at hA
  have hr' : (n:ℤ)+3=2*(r:ℤ)^2 := by exact_mod_cast hr
  rcases hA with rfl|rfl
  · exfalso
    apply exclude_one p q r (by nlinarith [hf])
    nlinarith [hr',hn]
  · refine ⟨p,q,by nlinarith [hf],by nlinarith [hn],?_,hcop⟩
    nlinarith [hf,hn,hr']

theorem d11_parameters (n r y : ℕ) (hr : n+3=11*r^2) (hy : n^2+2=66*y^2) :
    ∃ p q : ℤ, p^2-2*q^2+16*p*q=1 ∧
      (n:ℤ)=8*(p^2-2*q^2)-4*p*q ∧
      (r:ℤ)^2=p^2+4*p*q-2*q^2 ∧ IsCoprime p q := by
  obtain ⟨A,p,q,hA,hf,hn,hcop⟩ := natural_norm_two_parameters 8 n y (by decide) (by norm_num;exact hy)
  norm_num at hA
  have hr' : (n:ℤ)+3=11*(r:ℤ)^2 := by exact_mod_cast hr
  rcases hA with rfl|rfl
  · refine ⟨p,q,by nlinarith [hf],by nlinarith [hn],?_,hcop⟩
    nlinarith [hf,hn,hr']
  · exfalso
    apply exclude_neg_eight p q r (by nlinarith [hf])
    nlinarith [hr',hn]

end Tetrahedral.SpecialPell
