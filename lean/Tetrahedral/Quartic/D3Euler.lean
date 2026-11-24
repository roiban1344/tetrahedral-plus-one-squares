import Tetrahedral.Quartic.D3

/-!
# The classification of relative norm 11 for d=3, by the residue field `𝔽₁₂₁`

`11` is inert in `F = ℚ(√2)`, so `𝔽 = 𝒪_F/11` is a field with `121` elements, written as pairs
`a + b√2` modulo `11`. With `δ = −Ā₀/B̄₀` for `ξ₀ = A₀ + B₀ s`, the two maps `χ± : R → 𝔽`,
`A + Bs ↦ Ā ± B̄δ`, are ring maps; an element of relative norm `11` vanishes under exactly one of them
(its type), and `ξ₀`, `τξ₀` have the two types. This is the argument of §6 of the paper.
-/

namespace Tetrahedral.Quartic3
open R

instance fact11 : Fact (Nat.Prime 11) := ⟨by norm_num⟩

abbrev F11 := ZMod 11 × ZMod 11
def mulF (a b : F11) : F11 := (a.1*b.1+2*a.2*b.2,a.1*b.2+a.2*b.1)
def normF (a : F11) : ZMod 11 := a.1^2-2*a.2^2

/-- `χ₊`: `s ↦ δ`. -/
def chiP (x : R) : F11 := (((x 0-3*x 2-2*x 3 : ℤ) : ZMod 11),((x 1-1*x 2-3*x 3 : ℤ) : ZMod 11))
/-- `χ₋`: `s ↦ −δ`. -/
def chiM (x : R) : F11 := (((x 0+3*x 2+2*x 3 : ℤ) : ZMod 11),((x 1+1*x 2+3*x 3 : ℤ) : ZMod 11))

theorem chiP_mul (x y : R) : chiP (x*y)=mulF (chiP x) (chiP y) := by
  simp only [chiP,mulF,mul_apply0,mul_apply1,mul_apply2,mul_apply3,Prod.mk.injEq]; push_cast
  constructor <;> ring_nf <;> reduce_mod_char
theorem chiM_mul (x y : R) : chiM (x*y)=mulF (chiM x) (chiM y) := by
  simp only [chiM,mulF,mul_apply0,mul_apply1,mul_apply2,mul_apply3,Prod.mk.injEq]; push_cast
  constructor <;> ring_nf <;> reduce_mod_char
theorem chiM_tau (x : R) : chiM x=chiP (tau x) := by
  simp only [chiM,chiP,tau_apply0,tau_apply1,tau_apply2,tau_apply3,Prod.mk.injEq]; push_cast
  constructor <;> ring
theorem chi_norm (x : R) : mulF (chiP x) (chiM x)=(((relH x:ℤ):ZMod 11),((relK x:ℤ):ZMod 11)) := by
  simp only [chiP,chiM,mulF,relH,relK,Prod.mk.injEq]; push_cast
  constructor <;> ring_nf <;> reduce_mod_char

theorem normF_mul (a b : F11) : normF (mulF a b)=normF a*normF b := by
  simp only [normF,mulF]; ring

theorem normF_zero (a : F11) (h : normF a=0) : a=0 := by
  obtain ⟨a1,a2⟩ := a
  have := qnr11 a1 a2 h
  simp only [Prod.mk_eq_zero]; exact this

theorem field (a b : F11) (h : mulF a b=0) : a=0 ∨ b=0 := by
  have h2 := congrArg normF h
  rw [normF_mul] at h2
  have : normF 0=0 := by simp [normF]
  rw [this] at h2
  rcases mul_eq_zero.mp h2 with h3|h3
  · exact Or.inl (normF_zero a h3)
  · exact Or.inr (normF_zero b h3)

theorem dvd11' (z : ℤ) (h : ((z:ℤ):ZMod 11)=0) : (11:ℤ) ∣ z := (ZMod.intCast_zmod_eq_zero_iff_dvd z 11).mp h

/-- Both maps vanish only on `11R`. -/
theorem both_zero (z : R) (hP : chiP z=0) (hM : chiM z=0) : ∀ i, (11:ℤ) ∣ z i := by
  simp only [chiP,chiM,Prod.mk_eq_zero] at hP hM
  have e1 := dvd11' _ hP.1; have e2 := dvd11' _ hP.2
  have e3 := dvd11' _ hM.1; have e4 := dvd11' _ hM.2
  have g2 : (11:ℤ) ∣ z 2 := by omega
  have g3 : (11:ℤ) ∣ z 3 := by omega
  have g0 : (11:ℤ) ∣ z 0 := by omega
  have g1 : (11:ℤ) ∣ z 1 := by omega
  intro i; fin_cases i
  · exact g0
  · exact g1
  · exact g2
  · exact g3

theorem euler_type (x : R) (hH : relH x=11) (hK : relK x=0) :
    ∃ u : R, relH u=1 ∧ relK u=0 ∧ (x=u*xi0 ∨ x=u*tau xi0) := by
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
  have hn := chi_norm x
  rw [hH,hK] at hn
  have h0 : ((((11:ℤ):ZMod 11),((0:ℤ):ZMod 11)) : F11)=0 := by decide
  rw [h0] at hn
  have tP : chiP xi0=0 := by decide
  have tM : chiM (tau xi0)=0 := by rw [chiM_tau,show tau (tau xi0)=xi0 by decide]; exact tP
  have pi0 : xi0*tau xi0=(11:ℤ) • (1:R) := by ext i; fin_cases i <;> rfl
  have pi0' : tau xi0*tau (tau xi0)=(11:ℤ) • (1:R) := by ext i; fin_cases i <;> rfl
  have hr1 : relH xi0=11 := by decide
  have hr2 : relK xi0=0 := by decide
  have hr3 : relH (tau xi0)=11 := by decide
  have hr4 : relK (tau xi0)=0 := by decide
  rcases field _ _ hn with a|a
  · -- the type of `ξ₀`: `x·τξ₀ ∈ 11R`
    obtain ⟨u,hu⟩ := divide (x*tau xi0) (both_zero _
      (by rw [chiP_mul,a]; simp [mulF]) (by rw [chiM_mul,chiM_tau (tau xi0),show tau (tau xi0)=xi0 by decide,tP]; simp [mulF]))
    obtain ⟨e1,e2⟩ := unit_of _ u hr3 hr4 hu
    exact ⟨u,e1,e2,Or.inl (cancel xi0 u pi0 hu)⟩
  · -- the type of `τξ₀`: `x·ξ₀ ∈ 11R`
    have hx : x*tau (tau xi0)=x*xi0 := by rw [show tau (tau xi0)=xi0 by decide]
    obtain ⟨u,hu⟩ := divide (x*tau (tau xi0)) (both_zero _
      (by rw [hx,chiP_mul,tP]; simp [mulF]) (by rw [hx,chiM_mul,a]; simp [mulF]))
    obtain ⟨e1,e2⟩ := unit_of _ u hr1 hr2 (by rw [← hx]; exact hu)
    exact ⟨u,e1,e2,Or.inr (cancel (tau xi0) u pi0' hu)⟩

end Tetrahedral.Quartic3
