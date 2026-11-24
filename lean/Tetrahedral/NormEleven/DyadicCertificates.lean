import Tetrahedral.NormEleven.DyadicSimple

/-! Kernel-checked small dyadic certificates for the three simple pairs.
The same period 16 and precision 256 work for d=1,3,11. -/
set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Tetrahedral.NormEleven

namespace Dyadic1
open Quartic1 R
def step : R := ⟨fun i => ((rho^16-1 : R) i)/32⟩
theorem step_eq : (↑(rhoU^16):R)=1+32*step := by
  have h : (↑(rhoU^16):R)=1+(32:ℤ) • step := by
    ext i; fin_cases i <;> decide +kernel
  simpa only [zsmul_eq_mul,Int.cast_ofNat] using h
theorem roots (m : ℤ) (hm : f (xi0*(↑(rhoU^m):R))=0) : m=0 ∨ m= -1 :=
  DyadicSimple.pair f Lf Qf f_expand rhoU xi0 step step_eq
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) m hm
theorem negative (m : ℤ) : f (-(xi0*(↑(rhoU^m):R)))≠0 :=
  DyadicSimple.negative f Lf Qf f_expand rhoU xi0 step step_eq
    (by decide +kernel) (by decide +kernel) m
end Dyadic1

namespace Dyadic3
open Quartic3 R
def step : R := ⟨fun i => ((rho^16-1 : R) i)/32⟩
theorem step_eq : (↑(rhoU^16):R)=1+32*step := by
  have h : (↑(rhoU^16):R)=1+(32:ℤ) • step := by
    ext i; fin_cases i <;> decide +kernel
  simpa only [zsmul_eq_mul,Int.cast_ofNat] using h
theorem roots (m : ℤ) (hm : f (xi0*(↑(rhoU^m):R))=0) : m=0 ∨ m= -1 :=
  DyadicSimple.pair f Lf Qf f_expand rhoU xi0 step step_eq
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) m hm
theorem negative (m : ℤ) : f (-(xi0*(↑(rhoU^m):R)))≠0 :=
  DyadicSimple.negative f Lf Qf f_expand rhoU xi0 step step_eq
    (by decide +kernel) (by decide +kernel) m
end Dyadic3

namespace Dyadic11
open Quartic11 R
def step : R := ⟨fun i => ((rho^16-1 : R) i)/32⟩
theorem step_eq : (↑(rhoU^16):R)=1+32*step := by
  have h : (↑(rhoU^16):R)=1+(32:ℤ) • step := by
    ext i; fin_cases i <;> decide +kernel
  simpa only [zsmul_eq_mul,Int.cast_ofNat] using h
theorem roots (m : ℤ) (hm : f (xi0*(↑(rhoU^m):R))=0) : m=0 ∨ m= -1 :=
  DyadicSimple.pair f Lf Qf f_expand rhoU xi0 step step_eq
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) m hm
theorem negative (m : ℤ) : f (-(xi0*(↑(rhoU^m):R)))≠0 :=
  DyadicSimple.negative f Lf Qf f_expand rhoU xi0 step step_eq
    (by decide +kernel) (by decide +kernel) m
end Dyadic11

end Tetrahedral.NormEleven
