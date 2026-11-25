import Mathlib.Tactic

namespace Tetrahedral.FiniteDifference

/-- Three initial residues and a vanishing third difference determine every
integer index. This uses only addition and subtraction of divisibilities. -/
theorem zero_mod (g : ℤ → ℤ) (N : ℤ)
    (hinit : ∀ j : Fin 3, N ∣ g j.val)
    (hthird : ∀ i : ℤ, N ∣ g (i+3)-3*g (i+2)+3*g (i+1)-g i)
    (i : ℤ) : N ∣ g i := by
  let H (i : ℤ) := N ∣ g i ∧ N ∣ g (i+1) ∧ N ∣ g (i+2)
  have forward (n : ℤ) (ih : H n) : H (n+1) := by
    obtain ⟨h0,h1,h2⟩ := ih
    have h3 : N ∣ g (n+3) := by
      have hh := (((hthird n).add (h2.mul_left 3)).sub (h1.mul_left 3)).add h0
      convert hh using 1 <;> ring
    exact ⟨h1,by simpa only [add_assoc,Int.reduceAdd] using h2,
      by simpa only [add_assoc,Int.reduceAdd] using h3⟩
  have backward (n : ℤ) (ih : H n) : H (n-1) := by
    obtain ⟨h0,h1,h2⟩ := ih
    have hh := hthird (n-1)
    rw [show n-1+3=n+2 by omega,show n-1+2=n+1 by omega,sub_add_cancel] at hh
    have hp : N ∣ g (n-1) := by
      have hd := ((hh.sub h2).add (h1.mul_left 3)).sub (h0.mul_left 3)
      apply dvd_neg.mp
      convert hd using 1 <;> ring
    exact ⟨hp,by simpa only [sub_add_cancel] using h0,
      by simpa only [show n-1+2=n+1 by omega] using h1⟩
  have ht : H i := by
    induction i using Int.induction_on with
    | zero => exact ⟨hinit 0,hinit 1,hinit 2⟩
    | succ n ih => exact forward n ih
    | pred n ih => exact backward (-(n:ℤ)) ih
  exact ht.1

end Tetrahedral.FiniteDifference
