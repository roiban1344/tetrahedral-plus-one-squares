import Tetrahedral.QuadraticPowers

namespace Tetrahedral.TaylorOrbit
section
variable {R : Type*} [CommRing R]

def truncation (s : ℤ) (U y : R) (a : ℤ) (E : R) : R :=
  y+(4*s*a) • (y*U)+(8*s^2*a*(a-1)) • (y*U^2)+(64*s^3) • (y*U^3*E)

/-- Keep the direction of the cubic error, for positive and negative powers. -/
theorem expansion (w : Rˣ) (s : ℤ) (U : R) (hw : (w:R)=1+4*(s:R)*U)
    (y : R) (a : ℤ) : ∃ E : R, y*(↑(w^a):R)=truncation s U y a E := by
  obtain ⟨E,hE⟩ := quadratic_even_zpow_factored w (2*(s:R)) U
    (by convert hw using 1 <;> ring) a
  refine ⟨E,?_⟩
  rw [hE]; simp only [truncation,zsmul_eq_mul]; push_cast; ring

/-- A short phase is excluded by a polynomial identity in the integer
exponent and all four error coordinates, rather than by a longer orbit table. -/
theorem phase_roots {C : Type*} (f : R → ℤ) (u : Rˣ) (P : ℕ) (hP : 0<P)
    (s : ℤ) (U : R) (hw : (↑(u^P):R)=1+4*(s:R)*U) (y : R)
    (centre : C → ℤ)
    (hcert : ∀ r : Fin P, (∃ c, (r.val:ℤ)=centre c%P) ∨
      ∀ (a : ℤ) (E : R), f (truncation s U (y*(↑(u^r.val):R)) a E)≠0)
    (i : ℤ) (hi : f (y*(↑(u^i):R))=0) : ∃ c, i%P=centre c%P := by
  have hlo := Int.emod_nonneg i (show (P:ℤ)≠0 by omega)
  have hhi := Int.emod_lt_of_pos i (show (0:ℤ)<P by omega)
  let r : Fin P := ⟨(i%P).toNat,by omega⟩
  have hr : (r.val:ℤ)=i%P := by dsimp [r]; omega
  rcases hcert r with ⟨c,hc⟩|hbad
  · exact ⟨c,by rw [← hr]; exact hc⟩
  · have hp : u^i=u^r.val*(u^P)^(i/P) := by
      rw [← zpow_natCast,← zpow_natCast u P,← zpow_mul,← zpow_add,hr]
      congr 1; have := Int.emod_add_mul_ediv i (P:ℤ); omega
    obtain ⟨E,hE⟩ := expansion (u^P) s U hw (y*(↑(u^r.val):R)) (i/P)
    rw [mul_assoc,← Units.val_mul,← hp] at hE
    exact absurd (by rwa [← hE]) (hbad (i/P) E)

end
end Tetrahedral.TaylorOrbit
