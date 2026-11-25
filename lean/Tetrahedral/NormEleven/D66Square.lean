import Tetrahedral.Quartic.D66
import Tetrahedral.Binomial

namespace Tetrahedral.NormEleven.Square66
open Quartic66 R
abbrev step : R := ⟨![756,228,19,6]⟩
theorem step_eq : (↑(rhoU^2):R)=1+2*step := by
  have h : (↑(rhoU^2):R)=1+(2:ℤ) • step := by
    ext i; fin_cases i <;> decide +kernel
  simpa only [zsmul_eq_mul,Int.cast_ofNat] using h

def square : R := ⟨![2287476,689700,58824,17736]⟩
theorem square_eq : step^2=square := by decide +kernel

theorem direction (a : ℤ) (E : R) :
    let V : R := a • step+step^2*E
    (48:ℤ) ∣ relK V-12*a^2 := by
  dsimp only
  rw [square_eq]
  simp only [relK,add_apply,zsmul_apply,mul_apply0,mul_apply1,mul_apply2,mul_apply3]
  norm_num [step,square]
  ring_nf; omega

/-- A sum of two squares divisible by four has both variables even. -/
theorem scaled_even (c a r j : ℤ) (hc : c≠0)
    (hr : r^2= -c^2*j) (hj : (4:ℤ) ∣ j-a^2) : 2 ∣ a := by
  have hd : c ∣ r := (UniqueFactorizationMonoid.pow_dvd_pow_iff_dvd (by decide : 2≠0)).mp
    ⟨-j,by rw [hr]; ring⟩
  obtain ⟨s,hs⟩ := hd
  have he : c^2*(s^2+j)=0 := by rw [hs] at hr; linear_combination hr
  have hsj := (mul_eq_zero.mp he).resolve_left (pow_ne_zero _ hc)
  have h4 : (4:ℤ) ∣ s^2+a^2 := by
    convert dvd_neg.mpr hj using 1 <;> linarith
  have hh := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).mpr h4
  push_cast at hh
  have cert : ∀ x y : ZMod 4, x^2+y^2=0 → y^2=0 := by decide +kernel
  have ha := (ZMod.intCast_zmod_eq_zero_iff_dvd (a^2) 4).mp (by
    push_cast; exact cert s a hh)
  have h2 : (2:ℤ) ∣ a^2 := dvd_trans (by decide : (2:ℤ) ∣ 4) ha
  exact (show Prime (2:ℤ) by norm_num).dvd_of_dvd_pow h2

/-- In the identity phase, the original square coordinate forces descent
without using the quadratic condition f at all. -/
theorem zero_phase (i r : ℤ)
    (hi : (↑((rhoU^2)^i):R) 1=6*r^2) : i=0 := by
  have parity (k : ℕ) (a : ℤ)
      (ha : (↑((rhoU^2)^((2:ℤ)^k*a)):R) 1=6*r^2) : 2 ∣ a := by
    obtain ⟨E,hE⟩ := dyadic_zpow_precision_factored (rhoU^2) 0 k step
      (by convert step_eq using 1 <;> ring) a
    let F : R := E
    let c : ℤ := 2^(k+1)
    let V : R := a • step+step^2*F
    have hz : (↑((rhoU^2)^((2:ℤ)^k*a)):R)=1+c • V := by
      rw [hE]; simp only [c,V,F,zsmul_eq_mul]; push_cast; ring
    have hr := (rel_rho (2*((2:ℤ)^k*a))).2
    rw [zpow_mul,zpow_ofNat,hz] at hr
    have hn : relK (1+c • V)=2*c*V 1+c^2*relK V := by
      simp only [relK,add_apply,zsmul_apply,one_apply]; simp; ring
    rw [hn] at hr
    rw [hz] at ha
    have hcoord : c*V 1=6*r^2 := by
      simpa only [add_apply,zsmul_apply,one_apply,show (1:Fin 4)≠0 by decide,
        if_false,zero_add] using ha
    obtain ⟨e,he⟩ := direction a F
    have hj : relK V=12*(a^2+4*e) := by
      change relK V-12*a^2=48*e at he
      omega
    have hsq : r^2= -c^2*(a^2+4*e) := by
      rw [hj] at hr
      have he : 12*(r^2+c^2*(a^2+4*e))=0 := by linear_combination hr-2*hcoord
      have := (mul_eq_zero.mp he).resolve_left (by decide : (12:ℤ)≠0)
      linarith
    exact scaled_even c a r (a^2+4*e) (by dsimp [c]; positivity) hsq ⟨e,by ring⟩
  have hd (k : ℕ) : (2:ℤ)^k ∣ i := by
    induction k with
    | zero => simp
    | succ k ih =>
      obtain ⟨a,ha⟩ := ih
      obtain ⟨b,hb⟩ := parity k a (by rwa [← ha])
      exact ⟨b,by rw [ha,hb,pow_succ]; ring⟩
  apply Int.eq_zero_of_dvd_of_natAbs_lt_natAbs (hd i.natAbs)
  simpa only [Int.natAbs_pow,show (2:ℤ).natAbs=2 from rfl] using i.natAbs.lt_two_pow_self

end Tetrahedral.NormEleven.Square66
