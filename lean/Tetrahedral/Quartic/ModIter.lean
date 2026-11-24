import Mathlib.Tactic

/-!
# A linear checker for orbit tables

Residues of an orbit `z·ρ^k` modulo `M` are computed by iterating one step
"multiply by `ρ` modulo `M`". `check P st n k x` evaluates `P` at the `n` successive iterates
and compares the last state with a target, in time linear in `n`, which the kernel can do for
thousands of steps; `check_spec` turns a successful check into the statements about
`st^[i] x`.
-/

namespace Tetrahedral.ModIter

def check {α : Type} [DecidableEq α] (P : ℕ → α → Bool) (st : α → α) (target : α) :
    ℕ → ℕ → α → Bool
  | 0, _, x => decide (x=target)
  | n+1, k, x => P k x && check P st target n (k+1) (st x)

theorem check_spec {α : Type} [DecidableEq α] (P : ℕ → α → Bool) (st : α → α) (target : α) :
    ∀ n k x, check P st target n k x=true →
      (∀ i < n, P (k+i) (st^[i] x)=true) ∧ st^[n] x=target := by
  intro n
  induction n with
  | zero => intro k x h; simp [check] at h; exact ⟨by simp,by simpa using h⟩
  | succ n ih =>
    intro k x h
    simp only [check,Bool.and_eq_true] at h
    obtain ⟨h1,h2⟩ := ih (k+1) (st x) h.2
    refine ⟨?_,by rw [Function.iterate_succ_apply]; exact h2⟩
    intro i hi
    rcases i with _|i
    · simpa using h.1
    · rw [Function.iterate_succ_apply,show k+(i+1)=k+1+i by omega]; exact h1 i (by omega)

end Tetrahedral.ModIter
