import Tetrahedral.SpecialPell

namespace Tetrahedral.SpecialPell

theorem form_coprime (A p q : ℤ) (h : p^2-2*q^2+2*A*p*q=1) : IsCoprime p q := by
  refine ⟨p+2*A*q,-2*q,?_⟩
  linear_combination h

/-- The seed sign is visible before solving any quartic equation. -/
theorem parameter_offset (A p q : ℤ) (hf : p^2-2*q^2+2*A*p*q=1) :
    A*(p^2-2*q^2)-4*p*q=A-2*(A^2+2)*p*q := by
  linear_combination A*hf

/-- Construct the required parameters during the descent, without an orbit index. -/
theorem direct_parameters {a n y : ℤ} (ha : 0<a) (hn : 0≤n) (hy : 0<y)
    (he : n^2+2=(a^2+2)*y^2) :
    ∃ A p q : ℤ, (A=a ∨ A= -a) ∧ 0<p ∧ q≤0 ∧ a ∣ p-1 ∧
      p^2-2*q^2+2*A*p*q=1 ∧ n=A*(p^2-2*q^2)-4*p*q ∧ y=p^2+2*q^2 := by
  by_cases hy1 : y=1
  · subst y
    have hna : n=a := by nlinarith
    refine ⟨a,1,0,Or.inl rfl,by norm_num,by norm_num,by simp,by norm_num,?_,by norm_num⟩
    simpa using hna
  · obtain ⟨N,Z,hNpos,hZpos,hlt,hNorm,hBackN,hBackY⟩ :=
      positive_predecessor ha hn (by omega) he
    obtain ⟨A,p,q,hA,hp,hq,hdiv,hf,hNrep,hZrep⟩ :=
      direct_parameters ha hNpos hZpos hNorm
    rcases hA with hA|hA
    · subst A
      refine ⟨-a,p,q-a*p,Or.inr rfl,hp,by nlinarith [mul_pos ha hp],hdiv,?_,?_,?_⟩
      · linear_combination hf
      · rw [← hBackN,hNrep,hZrep]; dsimp [stepN]; ring
      · rw [← hBackY,hNrep,hZrep]; dsimp [stepY]; ring
    · subst A
      refine ⟨a,p-2*a*q,q,Or.inl rfl,?_,hq,?_,?_,?_,?_⟩
      · nlinarith [mul_nonpos_of_nonneg_of_nonpos ha.le hq]
      · convert hdiv.sub (dvd_mul_right a (2*q)) using 1 <;> ring
      · linear_combination hf
      · rw [← hBackN,hNrep,hZrep]; dsimp [stepN]; ring
      · rw [← hBackY,hNrep,hZrep]; dsimp [stepY]; ring
termination_by n.toNat
decreasing_by omega


/-- Integral quadratic parameters constructed during the elementary descent.
No orbit index or unique factorization theorem is required. -/
theorem norm_two_parameters {a n y : ℤ} (ha : 0 < a) (hn : 0 ≤ n) (hy : 0 < y)
    (he : n^2+2=(a^2+2)*y^2) :
    ∃ A p q : ℤ, (A=a ∨ A= -a) ∧ p^2-2*q^2+2*A*p*q=1 ∧
      n=A*(p^2-2*q^2)-4*p*q ∧ IsCoprime p q := by
  obtain ⟨A,p,q,hA,_,_,_,hf,hN,_⟩ := direct_parameters ha hn hy he
  exact ⟨A,p,q,hA,hf,hN,form_coprime A p q hf⟩

theorem natural_norm_two_parameters (a n y : ℕ) (ha : 0 < a)
    (he : n^2+2=(a^2+2)*y^2) :
    ∃ A p q : ℤ, (A=(a:ℤ) ∨ A= -(a:ℤ)) ∧ p^2-2*q^2+2*A*p*q=1 ∧
      (n:ℤ)=A*(p^2-2*q^2)-4*p*q ∧ IsCoprime p q := by
  have hy : 0 < y := by
    by_contra h
    have hz : y=0 := by omega
    simp [hz] at he
  apply norm_two_parameters (a:=(a:ℤ)) (n:=(n:ℤ)) (y:=(y:ℤ))
    (by exact_mod_cast ha) (by positivity) (by exact_mod_cast hy)
  exact_mod_cast he

end Tetrahedral.SpecialPell
