import Tetrahedral.NormEleven.Parameters
import Tetrahedral.Quartic.D1
import Tetrahedral.Quartic.D2
import Tetrahedral.Quartic.D3
import Tetrahedral.Quartic.D11
import Tetrahedral.Quartic.D66

namespace Tetrahedral.NormEleven.Certificates

section D1
open Tetrahedral.Quartic1 R
theorem d1 (n r y : ℕ) (hr : n+3=r^2) (hy : n^2+2=6*y^2) :
    ∃ ξ : R, relH ξ=11 ∧ relK ξ=0 ∧ f ξ=0 ∧ ξ 0=(n:ℤ)+3 := by
  obtain ⟨u,v,hn,hY⟩ := NormEleven.d1_parameters n r y hr hy
  have hh := norm_eleven 1 6 22 9 n y r u v
    (by nlinarith only [hn]) (by nlinarith only [hY])
    (by norm_num; exact_mod_cast hr) (by exact_mod_cast hy)
  let ξ : R := ⟨![(n:ℤ)+3,y,r*u,r*v]⟩
  refine ⟨ξ,?_,?_,?_,rfl⟩
  · norm_num [relH,ξ]; linear_combination hh.1
  · norm_num [relK,ξ]; linear_combination hh.2
  · norm_num [f,ξ]
    have hyZ : (n:ℤ)^2+2=6*(y:ℤ)^2 := by exact_mod_cast hy
    linear_combination hyZ
end D1

section D2
open Tetrahedral.Quartic2 R
theorem d2 (n r y : ℕ) (hr : n+3=2*r^2) (hy : n^2+2=3*y^2) :
    ∃ ξ : R, relH ξ=11 ∧ relK ξ=0 ∧ f ξ=0 ∧ ξ 0=(n:ℤ)+3 := by
  obtain ⟨u,v,hn,hY⟩ := NormEleven.d2_parameters n r y hr hy
  have hh := norm_eleven 2 3 5 3 n y r u v
    (by nlinarith only [hn]) (by nlinarith only [hY])
    (by norm_num; exact_mod_cast hr) (by exact_mod_cast hy)
  let ξ : R := ⟨![(n:ℤ)+3,y,r*u,r*v]⟩
  refine ⟨ξ,?_,?_,?_,rfl⟩
  · norm_num [relH,ξ]; linear_combination hh.1
  · norm_num [relK,ξ]; linear_combination hh.2
  · norm_num [f,ξ]
    have hyZ : (n:ℤ)^2+2=3*(y:ℤ)^2 := by exact_mod_cast hy
    linear_combination hyZ
end D2

section D3
open Tetrahedral.Quartic3 R
theorem d3 (n r y : ℕ) (hr : n+3=3*r^2) (hy : n^2+2=2*y^2) :
    ∃ ξ : R, relH ξ=11 ∧ relK ξ=0 ∧ f ξ=0 ∧ ξ 0=(n:ℤ)+3 := by
  obtain ⟨u,v,hn,hY⟩ := NormEleven.d3_parameters n r y hr hy
  have hh := norm_eleven 3 2 0 1 n y r u v
    (by nlinarith only [hn]) (by nlinarith only [hY])
    (by norm_num; exact_mod_cast hr) (by exact_mod_cast hy)
  let ξ : R := ⟨![(n:ℤ)+3,y,r*u,r*v]⟩
  refine ⟨ξ,?_,?_,?_,rfl⟩
  · norm_num [relH,ξ]; linear_combination hh.1
  · norm_num [relK,ξ]; linear_combination hh.2
  · norm_num [f,ξ]
    have hyZ : (n:ℤ)^2+2=2*(y:ℤ)^2 := by exact_mod_cast hy
    linear_combination hyZ
end D3

section D11
open Tetrahedral.Quartic11 R
theorem d11 (n r y : ℕ) (hr : n+3=11*r^2) (hy : n^2+2=66*y^2) :
    ∃ ξ : R, relH ξ=11 ∧ relK ξ=0 ∧ f ξ=0 ∧ ξ 0=(n:ℤ)+3 := by
  obtain ⟨u,v,hn,hY⟩ := NormEleven.d11_parameters n r y hr hy
  have hh := norm_eleven 11 66 8 1 n y r u v
    (by nlinarith only [hn]) (by nlinarith only [hY])
    (by norm_num; exact_mod_cast hr) (by exact_mod_cast hy)
  let ξ : R := ⟨![(n:ℤ)+3,y,r*u,11*r*v]⟩
  refine ⟨ξ,?_,?_,?_,rfl⟩
  · norm_num [relH,ξ]; linear_combination hh.1
  · norm_num [relK,ξ]; linear_combination hh.2
  · norm_num [f,ξ]
    have hyZ : (n:ℤ)^2+2=66*(y:ℤ)^2 := by exact_mod_cast hy
    linear_combination hyZ
end D11

section D66
open Tetrahedral.Quartic66 R
theorem d66 (n r y : ℕ) (hr : n+3=66*r^2) (hy : n^2+2=11*y^2) :
    ∃ ξ : R, relH ξ=11 ∧ relK ξ=0 ∧ f ξ=0 ∧ ξ 0=(n:ℤ)+3 := by
  obtain ⟨u,v,hn,hY⟩ := NormEleven.d66_parameters n r y hr hy
  have hh := norm_eleven 66 11 63 19 n y r u v
    (by nlinarith only [hn]) (by nlinarith only [hY])
    (by norm_num; exact_mod_cast hr) (by exact_mod_cast hy)
  let ξ : R := ⟨![(n:ℤ)+3,y,11*r*v,r*u]⟩
  refine ⟨ξ,?_,?_,?_,rfl⟩
  · norm_num [relH,ξ]; linear_combination hh.1
  · norm_num [relK,ξ]; linear_combination hh.2
  · norm_num [f,ξ]
    have hyZ : (n:ℤ)^2+2=11*(y:ℤ)^2 := by exact_mod_cast hy
    linear_combination hyZ
end D66

end Tetrahedral.NormEleven.Certificates
