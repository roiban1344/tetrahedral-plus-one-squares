import Tetrahedral.NormEleven.SmallNorm

/-! Direct classification of the required norm-eleven orbits. -/

namespace Tetrahedral.NormEleven.Window1
open Quartic1 R
theorem norm_eleven_positive (x : R) (hH : relH x=11) (hK : relK x=0) (hx : 0<sig x) :
    ∃ m : ℤ, x=xi0*(↑(rhoU^m):R) ∨x=(tau xi0)*(↑(rhoU^m):R) := by
  obtain ⟨v,i,hv,hback,hpos,hlo,hhi⟩ :=
    NormWindow.centered_positive sigHom rhoU one_lt_Lam 11 (by norm_num) x hx
  have hN := relN_rho_zpow (-i)
  have hvH : relH v=11 := by rw [hv,relH_mul,hH,hK,hN.1,hN.2]; ring
  have hvK : relK v=0 := by rw [hv,relK_mul,hH,hK,hN.1,hN.2]; ring
  change 11≤(sig v)^2*Lam at hlo
  change (sig v)^2<11*Lam at hhi
  have hp : sig v*sig (tau v)=11 := by rw [sig_tau,hvH,hvK]; norm_num
  have ht : 2*((v 0:ℝ)+(v 1:ℝ)*cR)=sig v+sig (tau v) := by
    simp only [sig,tau_apply0,tau_apply1,tau_apply2,tau_apply3]; push_cast; ring
  obtain ⟨hAp,hA⟩ := NormWindow.trace_window _ _ _ 11 Lam hp hpos (by norm_num) ht hlo hhi.le
  have hQ := NormWindow.norm_minus_two_nonnegative 22 9 6 (v 2) (v 3)
    (by norm_num) (by norm_num)
  have hab : 0≤v 0*v 1 := by
    have hk := hvK; simp only [relK] at hk; nlinarith only [hk,hQ]
  obtain ⟨ha,hb⟩ := NormWindow.coefficients_nonnegative _ _ cR cR_pos hab hAp
  have hsmall := Quartic1.small_norm_eleven v hvH hvK ha hb (by nlinarith [hA,Lam_coarse])
  rcases hsmall with he|he
  · exact ⟨i,Or.inl (by rw [hback,he])⟩
  · exact ⟨i,Or.inr (by rw [hback,he])⟩
end Tetrahedral.NormEleven.Window1

namespace Tetrahedral.NormEleven.Window2
open Quartic2 R
theorem norm_eleven_positive (x : R) (hH : relH x=11) (hK : relK x=0) (hx : 0<sig x) :
    ∃ m : ℤ, x=(tau xi0)*(↑(rhoU^m):R) ∨x=xi0*(↑(rhoU^m):R) ∨x=(tau xi1)*(↑(rhoU^m):R) ∨x=xi1*(↑(rhoU^m):R) := by
  obtain ⟨v,i,hv,hback,hpos,hlo,hhi⟩ :=
    NormWindow.centered_positive sigHom rhoU one_lt_Lam 11 (by norm_num) x hx
  have hN := relN_rho_zpow (-i)
  have hvH : relH v=11 := by rw [hv,relH_mul,hH,hK,hN.1,hN.2]; ring
  have hvK : relK v=0 := by rw [hv,relK_mul,hH,hK,hN.1,hN.2]; ring
  change 11≤(sig v)^2*Lam at hlo
  change (sig v)^2<11*Lam at hhi
  have hp : sig v*sig (tau v)=11 := by rw [sig_tau,hvH,hvK]; norm_num
  have ht : 2*((v 0:ℝ)+(v 1:ℝ)*cR)=sig v+sig (tau v) := by
    simp only [sig,tau_apply0,tau_apply1,tau_apply2,tau_apply3]; push_cast; ring
  obtain ⟨hAp,hA⟩ := NormWindow.trace_window _ _ _ 11 Lam hp hpos (by norm_num) ht hlo hhi.le
  have hQ := NormWindow.norm_minus_two_nonnegative 5 3 3 (v 2) (v 3)
    (by norm_num) (by norm_num)
  have hab : 0≤v 0*v 1 := by
    have hk := hvK; simp only [relK] at hk; nlinarith only [hk,hQ]
  obtain ⟨ha,hb⟩ := NormWindow.coefficients_nonnegative _ _ cR cR_pos hab hAp
  have hsmall := Quartic2.small_norm_eleven v hvH hvK ha hb (by nlinarith [hA,Lam_coarse])
  rcases hsmall with he|he|he|he
  · exact ⟨i,Or.inr (Or.inl (by rw [hback,he]))⟩
  · exact ⟨i,Or.inl (by rw [hback,he])⟩
  · refine ⟨i-1,Or.inr (Or.inr (Or.inr ?_))⟩
    have hs : shiftedSeed=xi1*(↑(rhoU^(-1:ℤ)):R) := by rw [zpow_neg_one]; decide +kernel
    rw [hback,he,hs,mul_assoc,←Units.val_mul,←zpow_add]
    rw [show (-1:ℤ)+i=i-1 by omega]
  · refine ⟨i+1,Or.inr (Or.inr (Or.inl ?_))⟩
    have hs : tau shiftedSeed=(tau xi1)*(rhoU:R) := by decide +kernel
    rw [hback,he,hs,mul_assoc,←Units.val_mul]
    have hh : rhoU*rhoU^i=rhoU^(i+1) := by rw [zpow_add]; simp [mul_comm]
    rw [hh]
end Tetrahedral.NormEleven.Window2

namespace Tetrahedral.NormEleven.Window3
open Quartic3 R
theorem norm_eleven_positive (x : R) (hH : relH x=11) (hK : relK x=0) (hx : 0<sig x) :
    ∃ m : ℤ, x=xi0*(↑(rhoU^m):R) ∨x=(tau xi0)*(↑(rhoU^m):R) := by
  obtain ⟨v,i,hv,hback,hpos,hlo,hhi⟩ :=
    NormWindow.centered_positive sigHom rhoU one_lt_Lam 11 (by norm_num) x hx
  have hN := relN_rho_zpow (-i)
  have hvH : relH v=11 := by rw [hv,relH_mul,hH,hK,hN.1,hN.2]; ring
  have hvK : relK v=0 := by rw [hv,relK_mul,hH,hK,hN.1,hN.2]; ring
  change 11≤(sig v)^2*Lam at hlo
  change (sig v)^2<11*Lam at hhi
  have hp : sig v*sig (tau v)=11 := by rw [sig_tau,hvH,hvK]; norm_num
  have ht : 2*((v 0:ℝ)+(v 1:ℝ)*cR)=sig v+sig (tau v) := by
    simp only [sig,tau_apply0,tau_apply1,tau_apply2,tau_apply3]; push_cast; ring
  obtain ⟨hAp,hA⟩ := NormWindow.trace_window _ _ _ 11 Lam hp hpos (by norm_num) ht hlo hhi.le
  have hQ := NormWindow.norm_minus_two_nonnegative 0 1 2 (v 2) (v 3)
    (by norm_num) (by norm_num)
  have hab : 0≤v 0*v 1 := by
    have hk := hvK; simp only [relK] at hk; nlinarith only [hk,hQ]
  obtain ⟨ha,hb⟩ := NormWindow.coefficients_nonnegative _ _ cR cR_pos hab hAp
  have hsmall := Quartic3.small_norm_eleven v hvH hvK ha hb (by nlinarith [hA,Lam_coarse])
  rcases hsmall with he|he
  · exact ⟨i,Or.inl (by rw [hback,he])⟩
  · exact ⟨i,Or.inr (by rw [hback,he])⟩
end Tetrahedral.NormEleven.Window3

namespace Tetrahedral.NormEleven.Window11
open Quartic11 R
theorem norm_eleven_positive (x : R) (hH : relH x=11) (hK : relK x=0) (hx : 0<sig x) :
    ∃ m : ℤ, x=xi0*(↑(rhoU^m):R) := by
  obtain ⟨v,i,hv,hback,hpos,hlo,hhi⟩ :=
    NormWindow.centered_positive sigHom rhoU one_lt_Lam 11 (by norm_num) x hx
  have hN := relN_rho_zpow (-i)
  have hvH : relH v=11 := by rw [hv,relH_mul,hH,hK,hN.1,hN.2]; ring
  have hvK : relK v=0 := by rw [hv,relK_mul,hH,hK,hN.1,hN.2]; ring
  change 11≤(sig v)^2*Lam at hlo
  change (sig v)^2<11*Lam at hhi
  have hp : sig v*sig (tau v)=11 := by rw [sig_tau,hvH,hvK]; norm_num
  have ht : 2*((v 0:ℝ)+(v 1:ℝ)*cR)=sig v+sig (tau v) := by
    simp only [sig,tau_apply0,tau_apply1,tau_apply2,tau_apply3]; push_cast; ring
  obtain ⟨hAp,hA⟩ := NormWindow.trace_window _ _ _ 11 Lam hp hpos (by norm_num) ht hlo hhi.le
  have hQ := NormWindow.norm_minus_two_nonnegative 8 1 66 (11*v 2) (v 3)
    (by norm_num) (by norm_num)
  have hab : 0≤v 0*v 1 := by
    have hk := hvK; simp only [relK] at hk; nlinarith only [hk,hQ]
  obtain ⟨ha,hb⟩ := NormWindow.coefficients_nonnegative _ _ cR cR_pos hab hAp
  have hsmall := Quartic11.small_norm_eleven v hvH hvK ha hb (by nlinarith [hA,Lam_coarse])
  rcases hsmall with he|he
  · exact ⟨i,by rw [hback,he]⟩
  · refine ⟨i-1,?_⟩
    rw [hback,he,←y1_eq,mul_assoc,←Units.val_mul,←zpow_add]
    rw [show (-1:ℤ)+i=i-1 by omega]
end Tetrahedral.NormEleven.Window11

namespace Tetrahedral.NormEleven.Window66
open Quartic66 R
theorem norm_eleven_positive (x : R) (hH : relH x=11) (hK : relK x=0) (hx : 0<sig x) :
    ∃ m : ℤ, x=xi0*(↑(rhoU^m):R) := by
  obtain ⟨v,i,hv,hback,hpos,hlo,hhi⟩ :=
    NormWindow.centered_positive sigHom rhoU one_lt_Lam 11 (by norm_num) x hx
  have hN := relN_rho_zpow (-i)
  have hvH : relH v=11 := by rw [hv,relH_mul,hH,hK,hN.1,hN.2]; ring
  have hvK : relK v=0 := by rw [hv,relK_mul,hH,hK,hN.1,hN.2]; ring
  change 11≤(sig v)^2*Lam at hlo
  change (sig v)^2<11*Lam at hhi
  have hp : sig v*sig (tau v)=11 := by rw [sig_tau,hvH,hvK]; norm_num
  have ht : 2*((v 0:ℝ)+(v 1:ℝ)*cR)=sig v+sig (tau v) := by
    simp only [sig,tau_apply0,tau_apply1,tau_apply2,tau_apply3]; push_cast; ring
  obtain ⟨hAp,hA⟩ := NormWindow.trace_window _ _ _ 11 Lam hp hpos (by norm_num) ht hlo hhi.le
  have hQ := NormWindow.norm_minus_two_nonnegative 63 19 11 (v 2) (v 3)
    (by norm_num) (by norm_num)
  have hab : 0≤v 0*v 1 := by
    have hk := hvK; simp only [relK] at hk; nlinarith only [hk,hQ]
  obtain ⟨ha,hb⟩ := NormWindow.coefficients_nonnegative _ _ cR cR_pos hab hAp
  have hsmall := Quartic66.small_norm_eleven v hvH hvK ha hb (by nlinarith [hA,Lam_coarse])
  exact ⟨i,by rw [hback,hsmall]⟩
end Tetrahedral.NormEleven.Window66

