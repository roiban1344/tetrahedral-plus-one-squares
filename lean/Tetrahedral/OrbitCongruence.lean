import Mathlib.Tactic

namespace Tetrahedral.OrbitCongruence

/-- A constant residue of successive differences fixes a two-sided sequence. -/
theorem of_difference (P : ℤ → ℤ) (N : ℤ)
    (hstep : ∀ i, N ∣ P (i+1)-P i) (i : ℤ) : N ∣ P i-P 0 := by
  have forward (n : ℤ) (ih : N ∣ P n-P 0) : N ∣ P (n+1)-P 0 := by
    convert (hstep n).add ih using 1 <;> ring
  have backward (n : ℤ) (ih : N ∣ P n-P 0) : N ∣ P (n-1)-P 0 := by
    have hh := hstep (n-1)
    simp only [sub_add_cancel] at hh
    convert ih.sub hh using 1 <;> ring
  induction i using Int.induction_on with
  | zero => simp
  | succ n ih => exact forward n ih
  | pred n ih => exact backward (-(n:ℤ)) ih

/-- A residue fixed by one step is fixed by every positive or negative step. -/
theorem invariant {M : Type*} [Monoid M] (u : Mˣ) (P : M → ℤ) (N : ℤ)
    (hstep : ∀ x, N ∣ P (x*(u:M))-P x) (x : M) (i : ℤ) :
    N ∣ P (x*(↑(u^i):M))-P x := by
  have hh (n : ℤ) : N ∣ P (x*(↑(u^(n+1)):M))-P (x*(↑(u^n):M)) := by
    rw [zpow_add_one,Units.val_mul,←mul_assoc]
    exact hstep _
  simpa only [zpow_zero,Units.val_one,mul_one] using
    of_difference (fun n => P (x*(↑(u^n):M))) N hh i

end Tetrahedral.OrbitCongruence
