import Mathlib.Tactic

/-! Elementary positive predecessors for the norm-minus-two equation.
QuadraticParameters constructs the required square factors during this descent. -/
namespace Tetrahedral.SpecialPell

def stepN (a n y : ℤ) : ℤ := (a^2+1)*n+a*(a^2+2)*y
def stepY (a n y : ℤ) : ℤ := a*n+(a^2+1)*y

theorem norm_preserved (a n y : ℤ) :
    stepN a n y ^ 2 - (a^2+2)*stepY a n y ^ 2 = n^2-(a^2+2)*y^2 := by
  unfold stepN stepY
  ring

/-- A norm -2 solution above the seed admits an explicit smaller solution.
No unit theorem, logarithm, or search bound is used. -/
theorem norm_two_descent {a n y : ℤ} (ha : 0 < a) (hn : 0 ≤ n) (hy : 1 < y)
    (h : n^2+2 = (a^2+2)*y^2) :
    let n' := (a^2+1)*n-a*(a^2+2)*y
    let y' := (a^2+1)*y-a*n
    0 < y' ∧ |n'| < n ∧ |n'|^2+2 = (a^2+2)*y'^2 := by
  dsimp
  have hay : 0 ≤ a*y := by positivity
  have hnay : a*y < n := by
    by_contra hc
    have hp := mul_nonneg (show 0 ≤ a*y-n by omega) (show 0 ≤ a*y+n by omega)
    nlinarith [h]
  have hdiff : ((a^2+1)*y)^2-(a*n)^2 = y^2+2*a^2 := by
    linear_combination -a^2*h
  have hy' : 0 < (a^2+1)*y-a*n := by
    by_contra hc
    have hp := mul_nonneg (show 0 ≤ a*n-(a^2+1)*y by omega)
      (show 0 ≤ a*n+(a^2+1)*y by positivity)
    nlinarith [hdiff]
  refine ⟨hy', ?_, ?_⟩
  · rw [abs_lt]
    constructor
    · have hp := mul_pos (show 0 < a^2+2 by positivity) (show 0 < n-a*y by omega)
      nlinarith [hp]
    · have hp := mul_pos ha (show 0 < ((a^2+1)*y-a*n)+y by omega)
      nlinarith [hp]
  · rw [sq_abs]
    have hp := norm_preserved a n (-y)
    unfold stepN stepY at hp
    nlinarith [hp,h]

theorem inverse_step (a n y : ℤ) :
    stepN a ((a^2+1)*n-a*(a^2+2)*y) ((a^2+1)*y-a*n) = n ∧
    stepY a ((a^2+1)*n-a*(a^2+2)*y) ((a^2+1)*y-a*n) = y := by
  unfold stepN stepY
  constructor <;> ring

/-- In fact the smaller predecessor has nonnegative first coordinate, so the
descent stays in the single forward orbit instead of branching into units. -/
theorem positive_predecessor {a n y : ℤ} (ha : 0 < a) (hn : 0 ≤ n) (hy : 1 < y)
    (h : n^2+2 = (a^2+2)*y^2) :
    ∃ N Z : ℤ, 0 ≤ N ∧ 0 < Z ∧ N < n ∧ N^2+2 = (a^2+2)*Z^2 ∧
      stepN a N Z = n ∧ stepY a N Z = y := by
  let N := (a^2+1)*n-a*(a^2+2)*y
  let Z := (a^2+1)*y-a*n
  obtain ⟨hZ,hlt,he⟩ := norm_two_descent ha hn hy h
  change 0 < Z at hZ
  change |N| < n at hlt
  change |N|^2+2 = (a^2+2)*Z^2 at he
  have hb := inverse_step a n y
  change stepN a N Z = n ∧ stepY a N Z = y at hb
  have hNZ : a*Z ≤ |N| := by
    by_contra hc
    have hp := mul_pos (show 0 < a*Z-|N| by omega) (show 0 < a*Z+|N| by positivity)
    nlinarith [he]
  have hN : 0 ≤ N := by
    by_contra hc
    have hneg : N < 0 := by omega
    rw [abs_of_neg hneg] at hNZ hlt
    have hp := mul_nonneg (show 0 ≤ a^2+2 by positivity) (show 0 ≤ -N-a*Z by omega)
    have hinv := hb.1
    unfold stepN at hinv
    nlinarith [hp,hinv]
  rw [abs_of_nonneg hN] at he hlt
  exact ⟨N,Z,hN,hZ,hlt,he,hb⟩


end Tetrahedral.SpecialPell
