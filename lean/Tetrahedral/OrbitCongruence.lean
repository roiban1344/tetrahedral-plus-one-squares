import Mathlib.Tactic

namespace Tetrahedral.OrbitCongruence

/-- A residue fixed by one step is fixed by every positive or negative step. -/
theorem invariant {M : Type*} [Monoid M] (u : Mˣ) (P : M → ℤ) (N : ℤ)
    (hstep : ∀ x, N ∣ P (x*(u:M))-P x) (x : M) (i : ℤ) :
    N ∣ P (x*(↑(u^i):M))-P x := by
  have he (n : ℤ) : (x*(↑(u^n):M))*(u:M)=x*(↑(u^(n+1)):M) := by
    rw [zpow_add_one,Units.val_mul,mul_assoc]
  have forward (n : ℤ) (ih : N ∣ P (x*(↑(u^n):M))-P x) :
      N ∣ P (x*(↑(u^(n+1)):M))-P x := by
    have hh := hstep (x*(↑(u^n):M))
    rw [he] at hh
    convert hh.add ih using 1 <;> ring
  have backward (n : ℤ) (ih : N ∣ P (x*(↑(u^n):M))-P x) :
      N ∣ P (x*(↑(u^(n-1)):M))-P x := by
    have hh := hstep (x*(↑(u^(n-1)):M))
    rw [he] at hh
    simp only [sub_add_cancel] at hh
    convert ih.sub hh using 1 <;> ring
  induction i using Int.induction_on with
  | zero => simp
  | succ n ih => exact forward n ih
  | pred n ih => exact backward (-(n:ℤ)) ih

end Tetrahedral.OrbitCongruence
