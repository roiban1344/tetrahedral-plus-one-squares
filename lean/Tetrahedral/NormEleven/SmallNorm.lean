import Tetrahedral.NormWindow
import Tetrahedral.Quartic.D1
import Tetrahedral.Quartic.D2
import Tetrahedral.Quartic.D3
import Tetrahedral.Quartic.D11
import Tetrahedral.Quartic.D66

/-! The small norm-eleven elements. Parity, size, and elementary factorizations
give the representatives; there is no enumeration of a large coordinate box. -/

namespace Tetrahedral.Quartic2
open R
def shiftedSeed : R := ⟨![4,1,1,-1]⟩
theorem small_norm_eleven (x : R) (hH : relH x=11) (hK : relK x=0)
    (ha0 : 0≤x 0) (hb0 : 0≤x 1)
    (hA : 4*((x 0:ℝ)+(x 1:ℝ)*cR)^2<187) :
    x=xi0 ∨x=tau xi0 ∨x=shiftedSeed ∨x=tau shiftedSeed := by
  have hh := hH; simp only [relH] at hh
  have hk := hK; simp only [relK] at hk
  have h4 : (4:ℤ) ∣ (x 0)^2+3*(x 1)^2-11 :=
    ⟨5*(x 2)^2+18*x 2*x 3+15*(x 3)^2,by nlinarith only [hh]⟩
  obtain ⟨hae,hbo⟩ := NormWindow.parity_three _ _ h4
  have hc : 3/2<cR := by nlinarith [cR_sq,cR_pos]
  have haR : (0:ℝ)≤x 0 := by exact_mod_cast ha0
  have hbR : (0:ℝ)≤x 1 := by exact_mod_cast hb0
  have hlin : 2*x 0+3*x 1<14 := by
    have hp := mul_nonneg hbR (sub_nonneg.mpr hc.le)
    have hsum : 0≤(x 0:ℝ)+(x 1:ℝ)*cR := by positivity
    have hlin : 2*(x 0:ℝ)+3*(x 1:ℝ)<14 := by nlinarith only [hA,hp,hsum]
    exact_mod_cast hlin
  have hs : 2*((3*x 2+5*x 3)^2+2*(x 3)^2)=3*(x 0*x 1) := by
    nlinarith only [hk]
  have han : x 0≠0 := by
    intro haz
    rw [haz] at hs
    have htz : x 3=0 := by nlinarith [sq_nonneg (3*x 2+5*x 3)]
    have hcz : x 2=0 := by rw [htz] at hs; nlinarith
    rw [haz,hcz,htz] at hh
    omega
  have hcases : (x 0=2 ∧x 1=1) ∨(x 0=4 ∧x 1=1) ∨(x 0=2 ∧x 1=3) := by omega
  rcases hcases with ⟨ha,hb⟩|⟨ha,hb⟩|⟨ha,hb⟩
  · rw [ha,hb] at hh hk
    have hp : x 2*x 3= -2 := by nlinarith only [hh,hk]
    have hn : (x 2)^2+3*(x 3)^2=7 := by nlinarith only [hh,hk,hp]
    have hf : ((x 3)^2-1)*(3*(x 3)^2-4)=0 := by
      nlinarith only [congrArg (fun z : ℤ => z^2) hp,
        congrArg (fun z : ℤ => z*(x 3)^2) hn]
    have ht : (x 3)^2=1 := by rcases mul_eq_zero.mp hf with h|h <;> omega
    have htf : (x 3-1)*(x 3+1)=0 := by nlinarith only [ht]
    rcases mul_eq_zero.mp htf with h|h
    · have htz : x 3=1 := by omega
      have hcz : x 2= -2 := by rw [htz] at hp; omega
      right; left; ext i; fin_cases i <;> simp [xi0,tau,ha,hb,htz,hcz]
    · have htz : x 3= -1 := by omega
      have hcz : x 2=2 := by rw [htz] at hp; omega
      left; ext i; fin_cases i <;> simp [xi0,ha,hb,htz,hcz]
  · rw [ha,hb] at hh hk
    have hp : x 2*x 3= -1 := by nlinarith only [hh,hk]
    have hn : (x 2)^2+3*(x 3)^2=4 := by nlinarith only [hh,hk,hp]
    have hf : ((x 3)^2-1)*(3*(x 3)^2-1)=0 := by
      nlinarith only [congrArg (fun z : ℤ => z^2) hp,
        congrArg (fun z : ℤ => z*(x 3)^2) hn]
    have ht : (x 3)^2=1 := by rcases mul_eq_zero.mp hf with h|h <;> omega
    have htf : (x 3-1)*(x 3+1)=0 := by nlinarith only [ht]
    rcases mul_eq_zero.mp htf with h|h
    · have htz : x 3=1 := by omega
      have hcz : x 2= -1 := by rw [htz] at hp; omega
      right; right; right; ext i; fin_cases i <;> simp [shiftedSeed,tau,ha,hb,htz,hcz]
    · have htz : x 3= -1 := by omega
      have hcz : x 2=1 := by rw [htz] at hp; omega
      right; right; left; ext i; fin_cases i <;> simp [shiftedSeed,ha,hb,htz,hcz]
  · have he : ((x 0:ℝ)+(x 1:ℝ)*cR)^2=31+12*cR := by
      rw [ha,hb]; norm_num
      linear_combination 9*cR_sq
    nlinarith only [hA,he,hc]
end Tetrahedral.Quartic2

namespace Tetrahedral.Quartic1
open R
theorem small_norm_eleven (x : R) (hH : relH x=11) (hK : relK x=0)
    (ha0 : 0≤x 0) (hb0 : 0≤x 1)
    (hA : 4*((x 0:ℝ)+(x 1:ℝ)*cR)^2<473) : x=xi0 ∨x=tau xi0 := by
  have hh := hH; simp only [relH] at hh
  have hk := hK; simp only [relK] at hk
  have h4 : (4:ℤ) ∣ (x 0)^2+2*(x 1)^2-11 :=
    ⟨-(x 1)^2+11*(x 2)^2+54*x 2*x 3+66*(x 3)^2,by nlinarith only [hh]⟩
  obtain ⟨hao,hbo⟩ := NormWindow.parity_two _ _ h4
  have hc : 2<cR := by nlinarith [cR_sq,cR_pos]
  have haR : (0:ℝ)≤x 0 := by exact_mod_cast ha0
  have hbR : (0:ℝ)≤x 1 := by exact_mod_cast hb0
  have hlin : x 0+2*x 1<11 := by
    have hp := mul_nonneg hbR (sub_nonneg.mpr hc.le)
    have hsum : 0≤(x 0:ℝ)+(x 1:ℝ)*cR := by positivity
    have hlin : (x 0:ℝ)+2*(x 1:ℝ)<11 := by nlinarith only [hA,hp,hsum]
    exact_mod_cast hlin
  have hcases : (x 0=1 ∧x 1=1) ∨(x 0=3 ∧x 1=1) ∨(x 0=5 ∧x 1=1) ∨
      (x 0=7 ∧x 1=1) ∨(x 0=1 ∧x 1=3) ∨(x 0=3 ∧x 1=3) := by omega
  rcases hcases with ⟨ha,hb⟩|⟨ha,hb⟩|⟨ha,hb⟩|⟨ha,hb⟩|⟨ha,hb⟩|⟨ha,hb⟩
  · rw [ha,hb] at hh hk
    have hp : x 2*x 3=-10 := by nlinarith only [hh,hk]
    have hn : (x 2)^2+6*(x 3)^2=49 := by nlinarith only [hh,hk,hp]
    have hf : ((x 3)^2-4)*(6*(x 3)^2-25)=0 := by
      nlinarith only [congrArg (fun z : ℤ => z^2) hp,
        congrArg (fun z : ℤ => z*(x 3)^2) hn]
    have ht : (x 3)^2=4 := by rcases mul_eq_zero.mp hf with h|h <;> omega
    have htf : (x 3-2)*(x 3+2)=0 := by nlinarith only [ht]
    rcases mul_eq_zero.mp htf with h|h
    · have htz : x 3=2 := by omega
      have hcz : x 2= -5 := by rw [htz] at hp; omega
      right; ext i; fin_cases i <;> simp [xi0,tau,ha,hb,htz,hcz]
    · have htz : x 3= -2 := by omega
      have hcz : x 2=5 := by rw [htz] at hp; omega
      left; ext i; fin_cases i <;> simp [xi0,ha,hb,htz,hcz]
  · rw [ha,hb] at hh hk
    have hp : x 2*x 3=-12 := by nlinarith only [hh,hk]
    have hn : (x 2)^2+6*(x 3)^2=59 := by nlinarith only [hh,hk,hp]
    have hf : (2*(x 3)^2-9)*(3*(x 3)^2-16)=0 := by
      nlinarith only [congrArg (fun z : ℤ => z^2) hp,
        congrArg (fun z : ℤ => z*(x 3)^2) hn]
    rcases mul_eq_zero.mp hf with h|h <;> omega
  · rw [ha,hb] at hh hk
    have hp : x 2*x 3=-5 := by nlinarith only [hh,hk]
    have hn : (x 2)^2+6*(x 3)^2=25 := by nlinarith only [hh,hk,hp]
    have hf : (2*(x 3)^2-5)*(3*(x 3)^2-5)=0 := by
      nlinarith only [congrArg (fun z : ℤ => z^2) hp,
        congrArg (fun z : ℤ => z*(x 3)^2) hn]
    rcases mul_eq_zero.mp hf with h|h <;> omega
  · rw [ha,hb] at hh hk
    have hp : x 2*x 3=11 := by nlinarith only [hh,hk]
    have hn : (x 2)^2+6*(x 3)^2=-53 := by nlinarith only [hh,hk,hp]
    nlinarith [sq_nonneg (x 2),sq_nonneg (x 3)]
  · rw [ha,hb] at hh hk
    have hp : x 2*x 3=33 := by nlinarith only [hh,hk]
    have hn : (x 2)^2+6*(x 3)^2=-161 := by nlinarith only [hh,hk,hp]
    nlinarith [sq_nonneg (x 2),sq_nonneg (x 3)]
  · rw [ha,hb] at hh hk
    have hp : x 2*x 3=9 := by nlinarith only [hh,hk]
    have hn : (x 2)^2+6*(x 3)^2=-43 := by nlinarith only [hh,hk,hp]
    nlinarith [sq_nonneg (x 2),sq_nonneg (x 3)]
end Tetrahedral.Quartic1

namespace Tetrahedral.Quartic3
open R
theorem small_norm_eleven (x : R) (hH : relH x=11) (hK : relK x=0)
    (ha0 : 0≤x 0) (hb0 : 0≤x 1)
    (hA : 4*((x 0:ℝ)+(x 1:ℝ)*cR)^2<825) : x=xi0 ∨x=tau xi0 := by
  have hh := hH; simp only [relH] at hh
  have hk := hK; simp only [relK] at hk
  have h4 : (4:ℤ) ∣ (x 0)^2+2*(x 1)^2-11 :=
    ⟨6*x 2*x 3,by nlinarith only [hh]⟩
  obtain ⟨hao,hbo⟩ := NormWindow.parity_two _ _ h4
  have h3 : ∀ a b : ZMod 3, a^2+2*b^2=2 → a=0 ∧b≠0 := by decide +kernel
  have hd3 : (3:ℤ) ∣ (x 0)^2+2*(x 1)^2-11 :=
    ⟨8*x 2*x 3,by nlinarith only [hh]⟩
  have hm := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mpr hd3
  have hm' : (x 0:ZMod 3)^2+2*(x 1:ZMod 3)^2=2 := by
    push_cast at hm
    rw [show (11:ZMod 3)=2 by decide] at hm
    exact sub_eq_zero.mp hm
  obtain ⟨had,hbn⟩ := h3 _ _ hm'
  have had' : (3:ℤ) ∣ x 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp had
  have hbn' : ¬(3:ℤ) ∣ x 1 := by
    intro h; exact hbn ((ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mpr h)
  have hc : 4/3<cR := by nlinarith [cR_sq,cR_pos]
  have haR : (0:ℝ)≤x 0 := by exact_mod_cast ha0
  have hbR : (0:ℝ)≤x 1 := by exact_mod_cast hb0
  have hlin : 3*x 0+4*x 1<45 := by
    have hp := mul_nonneg hbR (sub_nonneg.mpr hc.le)
    have hsum : 0≤(x 0:ℝ)+(x 1:ℝ)*cR := by positivity
    have hlin : 3*(x 0:ℝ)+4*(x 1:ℝ)<45 := by nlinarith only [hA,hp,hsum]
    exact_mod_cast hlin
  have hcases : (x 0=3 ∧x 1=1) ∨(x 0=3 ∧x 1=5) ∨
      (x 0=3 ∧x 1=7) ∨(x 0=9 ∧x 1=1) := by
    obtain ⟨k,hk⟩ := had'
    have hkC : k=1 ∨k=3 := by omega
    rcases hkC with hkC|hkC
    · have ha : x 0=3 := by omega
      have hb : x 1=1 ∨x 1=5 ∨x 1=7 := by omega
      rcases hb with hb|hb|hb
      · exact Or.inl ⟨ha,hb⟩
      · exact Or.inr (Or.inl ⟨ha,hb⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨ha,hb⟩))
    · have ha : x 0=9 := by omega
      have hb : x 1=1 := by omega
      exact Or.inr (Or.inr (Or.inr ⟨ha,hb⟩))
  rcases hcases with ⟨ha,hb⟩|⟨ha,hb⟩|⟨ha,hb⟩|⟨ha,hb⟩
  · rw [ha,hb] at hh hk
    have hp : x 2*x 3=0 := by nlinarith only [hh]
    have hn : (x 2)^2+2*(x 3)^2=1 := by nlinarith only [hk]
    have htz : x 3=0 := by
      by_contra h
      have hi := Int.one_le_abs h
      nlinarith [sq_abs (x 3),sq_nonneg (x 2)]
    have hf : (x 2-1)*(x 2+1)=0 := by rw [htz] at hn; nlinarith only [hn]
    rcases mul_eq_zero.mp hf with h|h
    · left; have hcz : x 2=1 := by omega
      ext i; fin_cases i <;> simp [xi0,ha,hb,htz,hcz]
    · right; have hcz : x 2= -1 := by omega
      ext i; fin_cases i <;> simp [xi0,tau,ha,hb,htz,hcz]
  · rw [ha,hb] at hh hk
    have hp : x 2*x 3=2 := by nlinarith only [hh]
    have hn : (x 2)^2+2*(x 3)^2=5 := by nlinarith only [hk]
    nlinarith only [congrArg (fun z : ℤ => z^2) hp,
      congrArg (fun z : ℤ => z^2) hn,sq_nonneg ((x 2)^2-2*(x 3)^2)]
  · rw [ha,hb] at hh hk
    have hp : x 2*x 3=4 := by nlinarith only [hh]
    have hn : (x 2)^2+2*(x 3)^2=7 := by nlinarith only [hk]
    nlinarith only [congrArg (fun z : ℤ => z^2) hp,
      congrArg (fun z : ℤ => z^2) hn,sq_nonneg ((x 2)^2-2*(x 3)^2)]
  · rw [ha,hb] at hh hk
    have hp : x 2*x 3=3 := by nlinarith only [hh]
    have hn : (x 2)^2+2*(x 3)^2=3 := by nlinarith only [hk]
    nlinarith only [congrArg (fun z : ℤ => z^2) hp,
      congrArg (fun z : ℤ => z^2) hn,sq_nonneg ((x 2)^2-2*(x 3)^2)]
end Tetrahedral.Quartic3
namespace Tetrahedral.Quartic11
open R
theorem small_norm_eleven (x : R) (hH : relH x=11) (hK : relK x=0)
    (ha0 : 0≤x 0) (hb0 : 0≤x 1)
    (hA : 4*((x 0:ℝ)+(x 1:ℝ)*cR)^2<1595) : x=xi0 ∨x=tau xi0 := by
  have hd : (11:ℤ) ∣ (x 0)^2-96*(x 3)^2 :=
    ⟨1-6*(x 1)^2+16*(x 2)^2+24*x 2*x 3,by simp only [relH] at hH; linarith⟩
  rw [←cast_zero_iff] at hd; push_cast at hd
  obtain ⟨ha,ht⟩ := qnr8 _ _ hd
  rw [cast_zero_iff] at ha ht
  have hk := hK; simp only [relK] at hk
  have hs : (11*x 2+8*x 3)^2+2*(x 3)^2=11*(x 0*x 1) := by nlinarith only [hk]
  have haR : (0:ℝ)≤x 0 := by exact_mod_cast ha0
  have hbR : (0:ℝ)≤x 1 := by exact_mod_cast hb0
  have hc : 8<cR := by nlinarith [cR_sq,cR_pos]
  have hb : (x 0:ℝ)+8*(x 1:ℝ)<20 := by
    have hp := mul_nonneg hbR (sub_nonneg.mpr hc.le)
    have hsum : 0≤(x 0:ℝ)+(x 1:ℝ)*cR := by positivity
    nlinarith only [hA,hp,hsum]
  have hbi : x 0+8*x 1<20 := by exact_mod_cast hb
  have haz : x 0=0 ∨x 0=11 := by omega
  rcases haz with haz|haz
  · rw [haz] at hs
    have htz : x 3=0 := by nlinarith [sq_nonneg (11*x 2+8*x 3)]
    have hcz : x 2=0 := by rw [htz] at hs; nlinarith
    norm_num [relH,haz,htz,hcz] at hH
    omega
  · have hb : x 1=1 := by
      by_contra hn
      have hbz : x 1=0 := by omega
      rw [hbz] at hs
      have htz : x 3=0 := by nlinarith [sq_nonneg (11*x 2+8*x 3)]
      have hcz : x 2=0 := by rw [htz] at hs; nlinarith
      norm_num [relH,haz,hbz,htz,hcz] at hH
    rw [haz,hb] at hs
    have htb : -8≤x 3 ∧x 3≤8 := by
      constructor <;> nlinarith [sq_nonneg (11*x 2+8*x 3)]
    have htz : x 3=0 := by omega
    rw [htz] at hs
    have hf : (x 2-1)*(x 2+1)=0 := by nlinarith only [hs]
    rcases mul_eq_zero.mp hf with hc|hc
    · left; have hcz : x 2=1 := by omega
      ext i; fin_cases i <;> simp [xi0,haz,hb,hcz,htz]
    · right; have hcz : x 2= -1 := by omega
      ext i; fin_cases i <;> simp [xi0,tau,haz,hb,hcz,htz]
end Tetrahedral.Quartic11

namespace Tetrahedral.Quartic66
open R
theorem small_norm_eleven (x : R) (hH : relH x=11) (hK : relK x=0)
    (ha0 : 0≤x 0) (hb0 : 0≤x 1)
    (hA : 4*((x 0:ℝ)+(x 1:ℝ)*cR)^2<891) : x=xi0 := by
  have hd : (11:ℤ) ∣ (x 0)^2-756*(x 2)^2 :=
    ⟨1-(x 1)^2+456*x 2*x 3+756*(x 3)^2,by simp only [relH] at hH; linarith⟩
  rw [←cast_zero_iff] at hd; push_cast at hd
  obtain ⟨ha,hc⟩ := qnr8 _ _ hd
  rw [cast_zero_iff] at ha hc
  have hh := hH; simp only [relH] at hh
  have h4 : (4:ℤ) ∣ (x 0)^2+3*(x 1)^2-11 :=
    ⟨-2*(x 1)^2+189*(x 2)^2+1254*x 2*x 3+2079*(x 3)^2,by nlinarith only [hh]⟩
  obtain ⟨hae,hbo⟩ := NormWindow.parity_three _ _ h4
  have haR : (0:ℝ)≤x 0 := by exact_mod_cast ha0
  have hbR : (0:ℝ)≤x 1 := by exact_mod_cast hb0
  have hal : x 0<15 := by
    have hp := mul_nonneg hbR cR_pos.le
    have hsum : 0≤(x 0:ℝ)+(x 1:ℝ)*cR := by positivity
    have hal : (x 0:ℝ)<15 := by nlinarith only [hA,hp,hsum]
    exact_mod_cast hal
  have haz : x 0=0 := by omega
  have hk := hK; simp only [relK] at hk
  have hs : (19*x 2+63*x 3)^2+2*(x 3)^2=0 := by
    rw [haz] at hk; nlinarith only [hk]
  have htz : x 3=0 := by nlinarith [sq_nonneg (19*x 2+63*x 3)]
  have hcz : x 2=0 := by rw [htz] at hs; nlinarith
  norm_num [relH,haz,hcz,htz] at hH
  have hb : x 1=1 := by nlinarith
  ext i; fin_cases i <;> simp [xi0,haz,hb,hcz,htz]
end Tetrahedral.Quartic66

