import Tetrahedral.Branches
import Tetrahedral.NormEleven.D1
import Tetrahedral.NormEleven.D2
import Tetrahedral.NormEleven.D3
import Tetrahedral.NormEleven.D11
import Tetrahedral.NormEleven.D66

namespace Tetrahedral.NormEleven

/-- Direct quadratic parameters followed by the arithmetic of an element of relative norm 11. -/
theorem complete_classification (n : ℕ) :
    (∃ m, Solution n m) ↔ Listed n := by
  constructor
  · rintro ⟨m,hm⟩
    obtain ⟨d,r,e,y,hd,hr,hy⟩ := five_branches hm
    rcases hd with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · have := Branch1.branch_complete n r y (by simpa using hr) hy; unfold Listed; tauto
    · have := Branch2.branch_complete n r y hr hy; unfold Listed; tauto
    · have := Branch3.branch_complete n r y hr hy; unfold Listed; tauto
    · have := Branch11.branch_complete n r y hr hy; unfold Listed; tauto
    · have := Branch66.branch_complete n r y hr hy; unfold Listed; tauto
  · exact listed_has_solution

theorem tetrahedral_classification (n : ℕ) :
    (∃ m : ℕ, n*(n+1)*(n+2)/6+1=m^2) ↔
      n=0 ∨ n=5 ∨ n=8 ∨ n=22 ∨ n=24 ∨ n=63 ∨ n=13775 := by
  change (∃ m : ℕ, tetrahedral n+1=m^2) ↔ _
  simp_rw [original_equation]
  exact complete_classification n

end Tetrahedral.NormEleven
