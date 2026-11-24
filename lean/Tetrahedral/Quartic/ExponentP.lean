import Tetrahedral.Binomial
import Mathlib.Data.Nat.Choose.Dvd

/-!
# A `p`-adic exponent lemma for an odd prime `p`

The lemma of `Exponent3.lean` for any prime `p ≥ 3`. If `w = 1 + p^t·U` with `t ≥ 1`,
`f(y + n•z) = n·L(z) + n²·Q(z)` with `L` linear, and `p ∤ L(y·U)`, then `f(y·w^i) = 0` forces
`i = 0`: with `i = p^k·a`, `p ∤ a`, one has `w^i = 1 + p^{k+t}(a·U + pE)`, and the linear term
modulo `p` gives `p ∣ a·L(yU)`. No descent is needed.
-/

namespace Tetrahedral

section
variable {R : Type*} [CommRing R]

/-- `(1 + p^s x)^p = 1 + p^{s+1}(x + pE)` for an odd prime `p` and `s ≥ 1`. -/
theorem prime_precision (p : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p) (s : ℕ) (hs : 1 ≤ s) (x : R) :
    ∃ E : R, (1+(p:R)^s*x)^p=1+(p:R)^(s+1)*(x+p*E) := by
  obtain ⟨r,hr⟩ : ∃ r, p=r+2 := ⟨p-2,by omega⟩
  have hterm : ∀ j ∈ Finset.range (r+1),
      (p:R)^(s+2) ∣ ((p:R)^s*x)^(j+2)*1^(p-(j+2))*(p.choose (j+2):R) := by
    intro j hj
    rw [Finset.mem_range] at hj
    rw [one_pow,mul_one,mul_pow,← pow_mul]
    by_cases hjp : j+2 < p
    · obtain ⟨c,hc⟩ := Nat.Prime.dvd_choose_self hp (by omega) hjp
      rw [hc]; push_cast
      have : (p:R)^(s+2) ∣ (p:R)^(s*(j+2))*p := by
        rw [← pow_succ]; exact pow_dvd_pow _ (by nlinarith)
      rw [show (p:R)^(s*(j+2))*x^(j+2)*((p:R)*c)=((p:R)^(s*(j+2))*p)*(x^(j+2)*c) by ring]
      exact this.mul_right _
    · have : (p:R)^(s+2) ∣ (p:R)^(s*(j+2)) := pow_dvd_pow _ (by nlinarith)
      exact Dvd.dvd.mul_right (Dvd.dvd.mul_right this _) _
  obtain ⟨E,hE⟩ := Finset.dvd_sum hterm
  refine ⟨E,?_⟩
  rw [add_comm,add_pow,hr,Finset.sum_range_succ',Finset.sum_range_succ',← hr,hE]
  simp only [pow_zero,pow_one,one_pow,mul_one,Nat.choose_zero_right,Nat.choose_one_right,
    Nat.cast_one,zero_add,Nat.sub_zero]
  ring

theorem powp_precision (p : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p) (t : ℕ) (ht : 1 ≤ t) (w : Rˣ) (U : R)
    (hw : (w:R)=1+(p:R)^t*U) :
    ∀ k : ℕ, ∃ E : R, (↑(w^(p^k)):R)=1+(p:R)^(k+t)*(U+p*E) := by
  intro k
  induction k with
  | zero => exact ⟨0,by simp [hw]⟩
  | succ k ih =>
    obtain ⟨E,hE⟩ := ih
    obtain ⟨F,hF⟩ := prime_precision p hp hp3 (k+t) (by omega) (U+p*E)
    refine ⟨E+F,?_⟩
    rw [pow_succ,pow_mul,Units.val_pow_eq_pow_val,hE,hF]
    rw [show k+1+t=k+t+1 by omega]; ring

theorem exponentp_unique (f : R → ℤ) (L : R →ₗ[ℤ] ℤ) (Q : R → ℤ) (y : R) (w : Rˣ)
    (p : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p)
    (t : ℕ) (ht : 1 ≤ t) (U : R) (hw : (w:R)=1+(p:R)^t*U)
    (hquad : ∀ z (n : ℤ), f (y+n • z)=n*L z+n^2*Q z)
    (hkernel : ¬ (p:ℤ) ∣ L (y*U)) (i : ℤ) (hi : f (y*(↑(w^i):R))=0) : i=0 := by
  by_contra hne
  obtain ⟨k,a',ha',hka⟩ := Nat.exists_eq_pow_mul_and_not_dvd (n:=i.natAbs)
    (Int.natAbs_ne_zero.mpr hne) p hp.one_lt.ne'
  -- `i = p^k a` with `p ∤ a`
  obtain ⟨a,hia,ha⟩ : ∃ a : ℤ, i=(p:ℤ)^k*a ∧ ¬ (p:ℤ) ∣ a := by
    rcases Int.natAbs_eq i with h|h
    · refine ⟨a',?_,?_⟩
      · rw [h,hka]; push_cast; ring
      · exact_mod_cast ha'
    · refine ⟨-(a':ℤ),?_,?_⟩
      · rw [h,hka]; push_cast; ring
      · rw [Int.dvd_neg]; exact_mod_cast ha'
  obtain ⟨E,hE⟩ := powp_precision p hp hp3 t ht w U hw k
  obtain ⟨G,hG⟩ := first_order_zpow (w^(p^k)) ((p:R)^(k+t)) (U+p*E) hE a
  have hw' : w^i=(w^(p^k))^a := by rw [hia,zpow_mul]; norm_cast
  rw [hw',hG] at hi
  set c : ℤ := (p:ℤ)^(k+t) with hc
  let Z : R := a • (y*U)+(p:ℤ) • (a • (y*E))+c • (y*G)
  have hy : y*(1+(a:R)*(p:R)^(k+t)*(U+p*E)+((p:R)^(k+t))^2*G)=y+c • Z := by
    simp only [Z,hc,zsmul_eq_mul]; push_cast; ring
  rw [hy,hquad] at hi
  have hcne : c≠0 := by rw [hc]; positivity
  have h1 : L Z+c*Q Z=0 := by
    have : c*(L Z+c*Q Z)=0 := by linear_combination hi
    exact (mul_eq_zero.mp this).resolve_left hcne
  have h3c : (p:ℤ) ∣ c := by rw [hc]; exact dvd_pow_self (p:ℤ) (by omega)
  obtain ⟨c',hc'⟩ := h3c
  have hLZ : L Z=a*L (y*U)+(p:ℤ)*(a*L (y*E)+c'*L (y*G)) := by
    simp only [Z,map_add,map_smul,smul_eq_mul,hc']; ring
  have : (p:ℤ) ∣ a*L (y*U) :=
    ⟨-(a*L (y*E)+c'*L (y*G))-c'*Q Z,by rw [hLZ,hc'] at h1; linear_combination h1⟩
  rcases (Nat.prime_iff_prime_int.mp hp).dvd_or_dvd this with h|h
  · exact ha h
  · exact hkernel h

end
end Tetrahedral
