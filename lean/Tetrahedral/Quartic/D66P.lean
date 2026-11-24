import Tetrahedral.Quartic.D66

/-!
# The exponents for d=66 at the single prime 89

`ρ` has order 44 modulo 89. The norm condition on `±√11·ρ^m` vanishes modulo 89 only for
`m ≡ 0, ±1 (mod 44)` (sign `+`) and `m ≡ 0` (sign `−`), which are the classes of the known zeros.
In each class the zero is unique 89-adically:

* at `m = ±1` (`n = 63`) the zero is simple: the first-order term is a unit (`exponentp_unique`);
* at `m = 0` the base point `√11` is fixed by `τ`, so the zero is double. For a relative unit
  `z = 1 + c·V` one has `2(z_F − 1) = −c²·N_{K/F}(V)`, and the condition becomes
  `44c²(H + 3K) + c⁴(…)` with `(H, K)` the coordinates of `N_{K/F}(V)`; the second-order term
  `H + 3K` is a unit (`double_zero`).
-/

namespace Tetrahedral.Quartic66
open R ModIter

theorem relH_one_add (c : ℤ) (V : R) : relH (1+c • V)=1+2*c*V 0+c^2*relH V := by
  simp only [relH,add_apply,zsmul_apply,one_apply]; simp; ring
theorem relK_one_add (c : ℤ) (V : R) : relK (1+c • V)=2*c*V 1+c^2*relK V := by
  simp only [relK,add_apply,zsmul_apply,one_apply]; simp; ring

/-- The `p`-adic lemma at a `τ`-fixed base point: the second-order term decides. -/
theorem double_zero (p : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p) (hp11 : p≠11)
    (sg : ℤ) (hsg : sg=1 ∨ sg= -1) (w : Rˣ) (t : ℕ) (ht : 1 ≤ t) (U : R)
    (hw : (w:R)=1+(p:R)^t*U) (hker : ¬ (p:ℤ) ∣ relH U+3*sg*relK U) (i : ℤ)
    (hrel : relH (↑(w^i):R)=1 ∧ relK (↑(w^i):R)=0)
    (hi : phi sg ((↑(w^i):R) 0) ((↑(w^i):R) 1)=0) : i=0 := by
  haveI := Fact.mk hp
  by_contra hne
  obtain ⟨k,a',ha',hka⟩ := Nat.exists_eq_pow_mul_and_not_dvd (n:=i.natAbs)
    (Int.natAbs_ne_zero.mpr hne) p hp.one_lt.ne'
  obtain ⟨a,hia,ha⟩ : ∃ a : ℤ, i=(p:ℤ)^k*a ∧ ¬ (p:ℤ) ∣ a := by
    rcases Int.natAbs_eq i with h|h
    · exact ⟨a',by rw [h,hka]; push_cast; ring,by exact_mod_cast ha'⟩
    · exact ⟨-(a':ℤ),by rw [h,hka]; push_cast; ring,by rw [Int.dvd_neg]; exact_mod_cast ha'⟩
  obtain ⟨E,hE⟩ := powp_precision p hp hp3 t ht w U hw k
  obtain ⟨G,hG⟩ := first_order_zpow (w^(p^k)) ((p:R)^(k+t)) (U+p*E) hE a
  have hw' : w^i=(w^(p^k))^a := by rw [hia,zpow_mul]; norm_cast
  obtain ⟨t',rfl⟩ : ∃ t', t=t'+1 := ⟨t-1,by omega⟩
  set c : ℤ := (p:ℤ)^(k+t'+1) with hc
  set X : R := a • E+((p:ℤ)^(k+t')) • G
  set V : R := a • U+(p:ℤ) • X
  have hz : (↑(w^i):R)=1+c • V := by
    rw [hw',hG]; simp only [V,X,hc,zsmul_eq_mul]; push_cast; ring
  rw [hz] at hrel hi
  obtain ⟨hH,hK⟩ := hrel
  rw [relH_one_add] at hH; rw [relK_one_add] at hK
  have hcne : c≠0 := by rw [hc]; exact pow_ne_zero _ (by exact_mod_cast hp.ne_zero)
  have h0 : 2*V 0= -c*relH V := by
    have : c*(2*V 0+c*relH V)=0 := by linear_combination hH
    have := (mul_eq_zero.mp this).resolve_left hcne; linarith
  have h1 : 2*V 1= -c*relK V := by
    have : c*(2*V 1+c*relK V)=0 := by linear_combination hK
    have := (mul_eq_zero.mp this).resolve_left hcne; linarith
  have hz0 : (1+c • V) 0=1+c*V 0 := by rw [R.add_apply,R.zsmul_apply]; rfl
  have hz1 : (1+c • V) 1=c*V 1 := by rw [R.add_apply,R.zsmul_apply]; simp
  rw [hz0,hz1] at hi
  -- `4φ = c²(44(H+3sgK) + c²(121K²−11H²))`
  have h4 : c^2*(44*(relH V+3*sg*relK V)+c^2*(121*(relK V)^2-11*(relH V)^2))=0 := by
    rcases hsg with rfl|rfl <;> simp only [phi] at hi
    · linear_combination 4*hi-(121*c^2*(2*V 1-c*relK V)-132*c)*h1-(-44*c-11*c^2*(2*V 0-c*relH V))*h0
    · linear_combination 4*hi-(121*c^2*(2*V 1-c*relK V)+132*c)*h1-(-44*c-11*c^2*(2*V 0-c*relH V))*h0
  have h5 : 44*(relH V+3*sg*relK V)+c^2*(121*(relK V)^2-11*(relH V)^2)=0 :=
    (mul_eq_zero.mp h4).resolve_left (pow_ne_zero _ hcne)
  -- modulo `p`
  have hcp : ((c:ℤ):ZMod p)=0 := by
    rw [hc]; push_cast; rw [ZMod.natCast_self]; simp
  have hHV : ((relH V:ℤ):ZMod p)=(a:ZMod p)^2*((relH U:ℤ):ZMod p) := by
    simp only [V,relH,R.add_apply,R.zsmul_apply]; push_cast; rw [ZMod.natCast_self]; ring
  have hKV : ((relK V:ℤ):ZMod p)=(a:ZMod p)^2*((relK U:ℤ):ZMod p) := by
    simp only [V,relK,R.add_apply,R.zsmul_apply]; push_cast; rw [ZMod.natCast_self]; ring
  have h6 := congrArg (fun z : ℤ => (z:ZMod p)) h5
  push_cast at h6
  rw [hcp,hHV,hKV] at h6
  have h7 : (44:ZMod p)*((a:ZMod p)^2*(((relH U+3*sg*relK U:ℤ)):ZMod p))=0 := by
    push_cast; linear_combination h6
  have h44 : (44:ZMod p)≠0 := by
    intro h
    have hd : p ∣ 44 := (ZMod.natCast_eq_zero_iff 44 p).mp (by exact_mod_cast h)
    rw [show (44:ℕ)=2^2*11 by norm_num] at hd
    rcases (Nat.Prime.dvd_mul hp).mp hd with h2|h11
    · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h2); omega
    · exact hp11 ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h11)
  have ha0 : (a:ZMod p)≠0 := by rwa [Ne,ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hk0 : (((relH U+3*sg*relK U:ℤ)):ZMod p)≠0 := by rwa [Ne,ZMod.intCast_zmod_eq_zero_iff_dvd]
  exact h44 ((mul_eq_zero.mp h7).resolve_right (mul_ne_zero (pow_ne_zero _ ha0) hk0))

/-! ## The certificate at 89 -/

theorem rho44 : ∃ V : R, (↑(rhoU^44):R)=1+((89:ℕ):ℤ) • V :=
  period_of_check 89 44 (by decide +kernel)

def predP89 (k : ℕ) (v : VZ 89) : Bool := if k=0 ∨ k=1 ∨ k=43 then true else fZ v != 0
def predM89 (k : ℕ) (v : VZ 89) : Bool := if k=0 then true else fZ v != 0

/-- Modulo 89 the condition vanishes only at `m ≡ 0, ±1 (mod 44)` (sign `+`)… -/
theorem tabP89 : check predP89 (stepZ 89) (0,1,0,0) 44 0 (0,1,0,0)=true := by decide +kernel
/-- … and only at `m ≡ 0 (mod 44)` (sign `−`). -/
theorem tabM89 : check predM89 (stepZ 89) (0,-1,0,0) 44 0 (0,-1,0,0)=true := by decide +kernel

theorem hw44 (V : R) (hV : (↑(rhoU^44):R)=1+((89:ℕ):ℤ) • V) :
    (↑(rhoU^44):R)=1+((89:ℕ):R)^1*V := by rw [hV,zsmul_eq_mul]; norm_num

theorem rho44_sub (V : R) (hV : (↑(rhoU^44):R)=1+((89:ℕ):ℤ) • V) : rho^44-1=(89:ℤ) • V := by
  rw [Units.val_pow_eq_pow_val,show (↑rhoU:R)=rho from rfl] at hV
  rw [hV,add_sub_cancel_left]; norm_num

/-- A simple zero at `y`, unique in its class modulo 44. -/
theorem centre89 (y : R) (hy : f y=0) (hL : ¬ (7921:ℤ) ∣ Lf y (y*(rho^44-1)))
    (i : ℤ) (hi : f (y*(↑((rhoU^44)^i):R))=0) : i=0 := by
  obtain ⟨V,hV⟩ := rho44
  refine exponentp_unique f (Lf y) Qf y (rhoU^44) 89 (by norm_num) (by norm_num) 1 le_rfl V
    (hw44 V hV) (by intro z n; rw [f_expand,hy]; ring) ?_ i hi
  intro h
  apply hL
  rw [rho44_sub V hV,mul_smul_comm,map_zsmul,smul_eq_mul]
  obtain ⟨c,hc⟩ := h
  exact ⟨c,by push_cast at hc ⊢; rw [hc]; ring⟩

theorem rel44 (t : ℤ) : relH (↑((rhoU^44)^t):R)=1 ∧ relK (↑((rhoU^44)^t):R)=0 := by
  have := rel_rho (44*t); rwa [zpow_mul,zpow_ofNat] at this

/-- The double zero at `m = 0`, unique in its class modulo 44. -/
theorem double89 (sg : ℤ) (hsg : sg=1 ∨ sg= -1)
    (hker : ¬ (704969:ℤ) ∣ relH (rho^44-1)+3*sg*relK (rho^44-1))
    (t : ℤ) (hi : phi sg ((↑((rhoU^44)^t):R) 0) ((↑((rhoU^44)^t):R) 1)=0) : t=0 := by
  obtain ⟨V,hV⟩ := rho44
  refine double_zero 89 (by norm_num) (by norm_num) (by norm_num) sg hsg (rhoU^44) 1 le_rfl V
    (hw44 V hV) ?_ t (rel44 t) hi
  intro h
  apply hker
  rw [rho44_sub V hV,relH_smul,relK_smul]
  obtain ⟨c,hc⟩ := h
  exact ⟨c,by push_cast at hc ⊢; linear_combination (7921:ℤ)*hc⟩

theorem exponents89 (m : ℤ) (hm : f (xi0*(↑(rhoU^m):R))=0) : m=0 ∨ m=1 ∨ m= -1 := by
  obtain ⟨V,hV⟩ := rho44
  have ht := table_eval 89 44 (by norm_num) V hV xi0 m
  simp only [Nat.cast_ofNat,castV_xi0] at ht
  set k := (m%44).toNat with hkdef
  have hkk : (k:ℤ)=m%44 := Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num))
  have hklt : k < 44 := by omega
  have hp := (check_spec _ _ _ _ _ _ tabP89).1 k hklt
  rw [zero_add,predP89] at hp
  by_cases hc : k=0 ∨ k=1 ∨ k=43
  · rcases hc with hc|hc|hc
    · left
      obtain ⟨t,rfl⟩ : ∃ t, m=44*t := ⟨m/44,by omega⟩
      rw [zpow_mul,zpow_ofNat,f_xi0] at hm
      have := double89 1 (Or.inl rfl) (by decide +kernel) t hm; omega
    · right; left
      obtain ⟨t,rfl⟩ : ∃ t, m=1+44*t := ⟨(m-1)/44,by omega⟩
      have : xi0*(↑(rhoU^(1+44*t)):R)=xi0*rho*(↑((rhoU^44)^t):R) := by
        rw [zpow_add,zpow_one,zpow_mul,zpow_ofNat,Units.val_mul,← mul_assoc]; rfl
      rw [this] at hm
      have := centre89 _ (by decide +kernel) (by decide +kernel) t hm; omega
    · right; right
      obtain ⟨t,rfl⟩ : ∃ t, m= -1+44*t := ⟨(m+1)/44,by omega⟩
      have : xi0*(↑(rhoU^(-1+44*t)):R)=xi0*rhoInv*(↑((rhoU^44)^t):R) := by
        rw [zpow_add,zpow_neg_one,zpow_mul,zpow_ofNat,Units.val_mul,← mul_assoc]; rfl
      rw [this] at hm
      have := centre89 _ (by decide +kernel) (by decide +kernel) t hm; omega
  · exfalso
    rw [if_neg hc,← ht,hm] at hp; simp at hp

theorem exponents89_neg (m : ℤ) (hm : f (-(xi0*(↑(rhoU^m):R)))=0) : m=0 := by
  obtain ⟨V,hV⟩ := rho44
  have ht := table_eval 89 44 (by norm_num) V hV (-xi0) m
  simp only [Nat.cast_ofNat,castV_negxi0] at ht
  set k := (m%44).toNat with hkdef
  have hkk : (k:ℤ)=m%44 := Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num))
  have hklt : k < 44 := by omega
  have hp := (check_spec _ _ _ _ _ _ tabM89).1 k hklt
  rw [zero_add,predM89] at hp
  by_cases hc : k=0
  · obtain ⟨t,rfl⟩ : ∃ t, m=44*t := ⟨m/44,by omega⟩
    rw [zpow_mul,zpow_ofNat,f_neg_xi0] at hm
    have := double89 (-1) (Or.inr rfl) (by decide +kernel) t hm; omega
  · exfalso
    rw [if_neg hc,← ht,neg_mul,hm] at hp; simp at hp

end Tetrahedral.Quartic66
