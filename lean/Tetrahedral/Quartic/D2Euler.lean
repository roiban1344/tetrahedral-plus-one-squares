import Tetrahedral.Quartic.D2

/-!
# The classification of relative norm 11 for d=2, by the places above 11

`11` splits in `F = ℚ(√3)` (`√3 ≡ ±5 mod 11`; we use the lifts `27, 94` of `√3` modulo `121`).
At each prime `𝔭` above `11`, `s` has the two values `±δ` (`δ = 6` for `√3 ↦ 27`, `δ = 2` for
`√3 ↦ 94`), giving four ring maps `χ : R → ZMod 11`. An element of relative norm `11` vanishes under
exactly one of the two maps at each `𝔭` (its *type*); the four representatives `ξ₀, ξ₁, τξ₀, τξ₁`
realise the four types, and two elements of the same type differ by a relative unit.
This avoids a check of all `11⁴` residues.
-/

namespace Tetrahedral.Quartic2
open R

/-- `A + B s ↦ Ā + B̄·δ` at the place `√3 ↦ r`, `s ↦ δ`. -/
def chi (r δ : ℤ) (x : R) : ZMod 11 := ((x 0+r*x 1+δ*(x 2+r*x 3) : ℤ) : ZMod 11)

theorem chi_mul (r δ : ℤ) (h : (r=27 ∧ (δ=6 ∨ δ= -6)) ∨ (r=94 ∧ (δ=2 ∨ δ= -2))) (x y : R) :
    chi r δ (x*y)=chi r δ x*chi r δ y := by
  rcases h with ⟨rfl,rfl|rfl⟩|⟨rfl,rfl|rfl⟩ <;>
    simp only [chi,mul_apply0,mul_apply1,mul_apply2,mul_apply3] <;> push_cast <;> ring_nf <;>
    reduce_mod_char

theorem chi_tau (r δ : ℤ) (x : R) : chi r (-δ) x=chi r δ (tau x) := by
  simp only [chi,tau_apply0,tau_apply1,tau_apply2,tau_apply3]; push_cast; ring

/-- The two values at one place multiply to the relative norm. -/
theorem chi_norm (r δ : ℤ) (h : (r=27 ∧ δ=6) ∨ (r=94 ∧ δ=2)) (x : R) :
    chi r δ x*chi r (-δ) x=((relH x+r*relK x : ℤ) : ZMod 11) := by
  rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> simp only [chi,relH,relK] <;> push_cast <;> ring_nf <;>
    reduce_mod_char

/-- The norm modulo `121` at the place `√3 ↦ r`. -/
theorem psi_norm (r : ℤ) (h : r=27 ∨ r=94) (x : R) :
    (((x 0+r*x 1)^2-(20+12*r)*(x 2+r*x 3)^2 : ℤ) : ZMod 121)=((relH x+r*relK x : ℤ) : ZMod 121) := by
  rcases h with rfl|rfl <;> simp only [relH,relK] <;> push_cast <;> ring_nf <;> reduce_mod_char

instance fact11 : Fact (Nat.Prime 11) := ⟨by norm_num⟩

theorem split11 (A B δ : ℤ) (hδ : δ=6 ∨ δ=2) (h1 : (11:ℤ) ∣ A+δ*B) (h2 : (11:ℤ) ∣ A+(-δ)*B) :
    (11:ℤ) ∣ A ∧ (11:ℤ) ∣ B := by
  rcases hδ with rfl|rfl <;> constructor <;> omega

theorem split2 (u v : ℤ) (h1 : (11:ℤ) ∣ u+27*v) (h2 : (11:ℤ) ∣ u+94*v) :
    (11:ℤ) ∣ u ∧ (11:ℤ) ∣ v := by
  constructor <;> omega

theorem dvd11 (z : ℤ) (h : ((z:ℤ):ZMod 11)=0) : (11:ℤ) ∣ z := (ZMod.intCast_zmod_eq_zero_iff_dvd z 11).mp h

/-- An element of relative norm `11` does not vanish at both values over one place. -/
theorem not_both (r δ : ℤ) (h : (r=27 ∧ δ=6) ∨ (r=94 ∧ δ=2)) (x : R) (hH : relH x=11) (hK : relK x=0)
    (h1 : chi r δ x=0) (h2 : chi r (-δ) x=0) : False := by
  have hr : r=27 ∨ r=94 := by rcases h with ⟨rfl,_⟩|⟨rfl,_⟩ <;> simp
  unfold chi at h1 h2
  have hδ : δ=6 ∨ δ=2 := by rcases h with ⟨_,rfl⟩|⟨_,rfl⟩ <;> simp
  obtain ⟨hA,hB⟩ := split11 _ _ δ hδ (dvd11 _ h1) (dvd11 _ h2)
  obtain ⟨a,ha⟩ := hA; obtain ⟨b,hb⟩ := hB
  have := psi_norm r hr x
  rw [ha,hb,hH,hK,ZMod.intCast_eq_intCast_iff_dvd_sub] at this
  obtain ⟨c,hc⟩ := this
  push_cast at hc
  have key : (11:ℤ)=121*(c+a^2-(20+12*r)*b^2) := by linear_combination hc
  generalize c+a^2-(20+12*r)*b^2=w at key
  omega

/-- All four values vanish only on `11R`. -/
theorem all_zero (z : R) (h1 : chi 27 6 z=0) (h2 : chi 27 (-6) z=0) (h3 : chi 94 2 z=0)
    (h4 : chi 94 (-2) z=0) : ∀ i, (11:ℤ) ∣ z i := by
  unfold chi at h1 h2 h3 h4
  obtain ⟨a1,b1⟩ := split11 _ _ 6 (Or.inl rfl) (dvd11 _ h1) (dvd11 _ h2)
  obtain ⟨a2,b2⟩ := split11 _ _ 2 (Or.inr rfl) (dvd11 _ h3) (dvd11 _ h4)
  obtain ⟨g0,g1⟩ := split2 _ _ a1 a2
  obtain ⟨g2,g3⟩ := split2 _ _ b1 b2
  intro i; fin_cases i
  · exact g0
  · exact g1
  · exact g2
  · exact g3

theorem euler_type (x : R) (hH : relH x=11) (hK : relK x=0) :
    ∃ u : R, relH u=1 ∧ relK u=0 ∧
      (x=u*tau xi0 ∨ x=u*xi0 ∨ x=u*tau xi1 ∨ x=u*xi1) := by
  have divide : ∀ y : R, (∀ i, (11:ℤ) ∣ y i) → ∃ u : R, (11:ℤ) • u=y := by
    intro y hy
    refine ⟨⟨fun i => y i/11⟩,?_⟩
    ext i; simp only [zsmul_apply]; exact Int.mul_ediv_cancel' (hy i)
  have unit_of : ∀ (z : R) (u : R), relH z=11 → relK z=0 → (11:ℤ) • u=x*z →
      relH u=1 ∧ relK u=0 := by
    intro z u hz1 hz2 hu
    have e1 := congrArg relH hu; have e2 := congrArg relK hu
    rw [relH_smul,relH_mul,hH,hK,hz1,hz2] at e1
    rw [relK_smul,relK_mul,hH,hK,hz1,hz2] at e2
    constructor <;> nlinarith
  have cancel : ∀ (z : R) (u : R), z*tau z=(11:ℤ) • (1:R) → (11:ℤ) • u=x*tau z → x=u*z := by
    intro z u hz hu
    have h11 : (11:ℤ) • (u*z)=(11:ℤ) • x := by
      rw [← smul_mul_assoc,hu,mul_assoc,mul_comm (tau z) z,hz,mul_smul_comm,mul_one]
    ext i
    have := congrArg (fun w : R => w i) h11
    simp only [zsmul_apply] at this
    omega
  -- `x` has the type of `π`; then `x·τπ ∈ 11R`
  have finish : ∀ π : R, relH π=11 → relK π=0 → π*tau π=(11:ℤ) • (1:R) →
      (∀ i, (11:ℤ) ∣ (x*tau π) i) → ∃ u : R, relH u=1 ∧ relK u=0 ∧ x=u*π := by
    intro π h1 h2 h3 hdiv
    obtain ⟨u,hu⟩ := divide _ hdiv
    have ht1 : relH (tau π)=11 := by simp only [relH,tau_apply0,tau_apply1,tau_apply2,tau_apply3] at h1 ⊢; linarith
    have ht2 : relK (tau π)=0 := by simp only [relK,tau_apply0,tau_apply1,tau_apply2,tau_apply3] at h2 ⊢; linarith
    obtain ⟨e1,e2⟩ := unit_of _ u ht1 ht2 hu
    exact ⟨u,e1,e2,cancel π u h3 hu⟩
  have p5 : ((27:ℤ)=27 ∧ (6:ℤ)=6) ∨ ((27:ℤ)=94 ∧ (6:ℤ)=2) := Or.inl ⟨rfl,rfl⟩
  have p6 : ((94:ℤ)=27 ∧ (2:ℤ)=6) ∨ ((94:ℤ)=94 ∧ (2:ℤ)=2) := Or.inr ⟨rfl,rfl⟩
  have n5 := chi_norm 27 6 p5 x
  have n6 := chi_norm 94 2 p6 x
  rw [hH,hK] at n5 n6
  have z11 : ((11+27*0 : ℤ) : ZMod 11)=0 := by decide
  have z11' : ((11+94*0 : ℤ) : ZMod 11)=0 := by decide
  rw [z11] at n5; rw [z11'] at n6
  have m : ∀ r δ, ((r=27 ∧ (δ=6 ∨ δ= -6)) ∨ (r=94 ∧ (δ=2 ∨ δ= -2))) → ∀ π : R,
      chi r δ (x*tau π)=chi r δ x*chi r (-δ) π := by
    intro r δ h π; rw [chi_mul r δ h,← chi_tau]
  have h56 : ((27:ℤ)=27 ∧ ((6:ℤ)=6 ∨ (6:ℤ)= -6)) ∨ ((27:ℤ)=94 ∧ ((6:ℤ)=2 ∨ (6:ℤ)= -2)) := by decide
  have h5m : ((27:ℤ)=27 ∧ ((-6:ℤ)=6 ∨ (-6:ℤ)= -6)) ∨ ((27:ℤ)=94 ∧ ((-6:ℤ)=2 ∨ (-6:ℤ)= -2)) := by decide
  have h62 : ((94:ℤ)=27 ∧ ((2:ℤ)=6 ∨ (2:ℤ)= -6)) ∨ ((94:ℤ)=94 ∧ ((2:ℤ)=2 ∨ (2:ℤ)= -2)) := by decide
  have h6m : ((94:ℤ)=27 ∧ ((-2:ℤ)=6 ∨ (-2:ℤ)= -6)) ∨ ((94:ℤ)=94 ∧ ((-2:ℤ)=2 ∨ (-2:ℤ)= -2)) := by decide
  have pi0 : xi0*tau xi0=(11:ℤ) • (1:R) := by ext i; fin_cases i <;> rfl
  have pi1 : xi1*tau xi1=(11:ℤ) • (1:R) := by ext i; fin_cases i <;> rfl
  have tt0 : tau (tau xi0)=xi0 := by decide
  have tt1 : tau (tau xi1)=xi1 := by decide
  have pi0' : tau xi0*tau (tau xi0)=(11:ℤ) • (1:R) := by ext i; fin_cases i <;> rfl
  have pi1' : tau xi1*tau (tau xi1)=(11:ℤ) • (1:R) := by ext i; fin_cases i <;> rfl
  rcases mul_eq_zero.mp n5 with a|a <;> rcases mul_eq_zero.mp n6 with b|b
  · -- type `(+,+)`: that of `ξ₀`
    obtain ⟨u,e1,e2,e3⟩ := finish xi0 (by decide) (by decide) pi0 (all_zero _
      (by rw [m 27 6 h56,a,zero_mul])
      (by rw [m 27 (-6) h5m,neg_neg,show chi 27 6 xi0=0 by decide,mul_zero])
      (by rw [m 94 2 h62,b,zero_mul])
      (by rw [m 94 (-2) h6m,neg_neg,show chi 94 2 xi0=0 by decide,mul_zero]))
    exact ⟨u,e1,e2,Or.inr (Or.inl e3)⟩
  · -- type `(+,−)`: that of `τξ₁`
    obtain ⟨u,e1,e2,e3⟩ := finish (tau xi1) (by decide) (by decide) pi1' (all_zero _
      (by rw [m 27 6 h56,a,zero_mul])
      (by rw [m 27 (-6) h5m,neg_neg,show chi 27 6 (tau xi1)=0 by decide,mul_zero])
      (by rw [m 94 2 h62,show chi 94 (-2) (tau xi1)=0 by decide,mul_zero])
      (by rw [m 94 (-2) h6m,b,zero_mul]))
    exact ⟨u,e1,e2,Or.inr (Or.inr (Or.inl e3))⟩
  · -- type `(−,+)`: that of `ξ₁`
    obtain ⟨u,e1,e2,e3⟩ := finish xi1 (by decide) (by decide) pi1 (all_zero _
      (by rw [m 27 6 h56,show chi 27 (-6) xi1=0 by decide,mul_zero])
      (by rw [m 27 (-6) h5m,a,zero_mul])
      (by rw [m 94 2 h62,b,zero_mul])
      (by rw [m 94 (-2) h6m,neg_neg,show chi 94 2 xi1=0 by decide,mul_zero]))
    exact ⟨u,e1,e2,Or.inr (Or.inr (Or.inr e3))⟩
  · -- type `(−,−)`: that of `τξ₀`
    obtain ⟨u,e1,e2,e3⟩ := finish (tau xi0) (by decide) (by decide) pi0' (all_zero _
      (by rw [m 27 6 h56,show chi 27 (-6) (tau xi0)=0 by decide,mul_zero])
      (by rw [m 27 (-6) h5m,a,zero_mul])
      (by rw [m 94 2 h62,show chi 94 (-2) (tau xi0)=0 by decide,mul_zero])
      (by rw [m 94 (-2) h6m,b,zero_mul]))
    exact ⟨u,e1,e2,Or.inl e3⟩

end Tetrahedral.Quartic2
