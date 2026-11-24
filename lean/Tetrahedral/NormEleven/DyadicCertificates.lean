import Tetrahedral.NormEleven.DyadicSimple

/-! Kernel-checked small dyadic certificates for the three simple pairs.
The same period 8 and precision 128 work for d=1,3,11. -/
set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Tetrahedral.NormEleven

namespace Dyadic1
open Quartic1 R
def step : R := ⟨fun i => ((rho^8-1 : R) i)/16⟩
theorem step_eq : (↑(rhoU^8):R)=1+16*step := by
  have h : (↑(rhoU^8):R)=1+(16:ℤ) • step := by
    ext i; fin_cases i <;> decide +kernel
  simpa only [zsmul_eq_mul,Int.cast_ofNat] using h
theorem roots (m : ℤ) (hm : f (xi0*(↑(rhoU^m):R))=0) : m=0 ∨ m= -1 :=
  DyadicSimple.pair f Lf Qf f_expand (by
    intro x z
    refine ⟨(x 0-3)*z 0-6*x 1*z 1,?_⟩
    simp only [Lf,LinearMap.coe_mk,AddHom.coe_mk]; ring) rhoU xi0 step step_eq
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) m hm
theorem negative (m : ℤ) : f (-(xi0*(↑(rhoU^m):R)))≠0 :=
  DyadicSimple.negative f Lf Qf f_expand rhoU xi0 step step_eq
    (by decide +kernel) (by decide +kernel) m
end Dyadic1

namespace Dyadic3
open Quartic3 R
def step : R := ⟨fun i => ((rho^8-1 : R) i)/16⟩
theorem step_eq : (↑(rhoU^8):R)=1+16*step := by
  have h : (↑(rhoU^8):R)=1+(16:ℤ) • step := by
    ext i; fin_cases i <;> decide +kernel
  simpa only [zsmul_eq_mul,Int.cast_ofNat] using h
theorem roots (m : ℤ) (hm : f (xi0*(↑(rhoU^m):R))=0) : m=0 ∨ m= -1 :=
  DyadicSimple.pair f Lf Qf f_expand (by
    intro x z
    refine ⟨(x 0-3)*z 0-2*x 1*z 1,?_⟩
    simp only [Lf,LinearMap.coe_mk,AddHom.coe_mk]; ring) rhoU xi0 step step_eq
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) m hm
theorem negative (m : ℤ) : f (-(xi0*(↑(rhoU^m):R)))≠0 :=
  DyadicSimple.negative f Lf Qf f_expand rhoU xi0 step step_eq
    (by decide +kernel) (by decide +kernel) m
end Dyadic3

namespace Dyadic11
open Quartic11 R
def step : R := ⟨fun i => ((rho^8-1 : R) i)/16⟩
theorem step_eq : (↑(rhoU^8):R)=1+16*step := by
  have h : (↑(rhoU^8):R)=1+(16:ℤ) • step := by
    ext i; fin_cases i <;> decide +kernel
  simpa only [zsmul_eq_mul,Int.cast_ofNat] using h
theorem roots (m : ℤ) (hm : f (xi0*(↑(rhoU^m):R))=0) : m=0 ∨ m= -1 :=
  DyadicSimple.pair f Lf Qf f_expand (by
    intro x z
    refine ⟨(x 0-3)*z 0-66*x 1*z 1,?_⟩
    simp only [Lf,LinearMap.coe_mk,AddHom.coe_mk]; ring) rhoU xi0 step step_eq
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) m hm
theorem negative (m : ℤ) : f (-(xi0*(↑(rhoU^m):R)))≠0 :=
  DyadicSimple.negative f Lf Qf f_expand rhoU xi0 step step_eq
    (by decide +kernel) (by decide +kernel) m
end Dyadic11

end Tetrahedral.NormEleven
