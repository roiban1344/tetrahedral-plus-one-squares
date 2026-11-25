import Mathlib.Tactic
import Tetrahedral.IntegerParity

namespace Tetrahedral.RelativeDirection

/-- The norm-one equation for 1+4qU determines the base coordinates of U. -/
theorem trace (q a N : ℤ) (hq : q≠0)
    (h : 1+8*q*a+16*q^2*N=1) : a= -2*q*N := by
  have he : q*(a+2*q*N)=0 := by nlinarith only [h]
  have := (mul_eq_zero.mp he).resolve_left hq
  linarith

/-- The square of a relative unit direction is its norm times minus the unit. -/
theorem square {R : Type*} [CommRing R] (U V N : R) (c : ℤ)
    (hN : U*V=N) (htrace : U+V= -c • N) :
    U^2= -(1+c • U)*N := by
  simp only [zsmul_eq_mul] at htrace ⊢
  push_cast at htrace
  linear_combination U*htrace-hN

theorem norm_two (a b H K q e : ℤ)
    (ha : a= -2*q*H) (hb : b= -2*q*K)
    (hH : 4 ∣ H-a^2-e*b^2) (hK : 2 ∣ K-2*a*b) :
    4 ∣ H ∧ 2 ∣ K := by
  obtain ⟨p,hp⟩ := hH; obtain ⟨r,hr⟩ := hK
  constructor
  · refine ⟨q^2*(H^2+e*K^2)+p,?_⟩
    rw [ha,hb] at hp; linear_combination hp
  · refine ⟨4*q^2*H*K+r,?_⟩
    rw [ha,hb] at hr; linear_combination hr

theorem norm_four (a b H K q e : ℤ)
    (ha : a= -2*q*H) (hb : b= -2*q*K)
    (hH : 4 ∣ H-a^2-e*b^2) (hK : 4 ∣ K-2*a*b) :
    4 ∣ H ∧ 4 ∣ K := by
  obtain ⟨p,hp⟩ := hH; obtain ⟨r,hr⟩ := hK
  constructor
  · refine ⟨q^2*(H^2+e*K^2)+p,?_⟩
    rw [ha,hb] at hp; linear_combination hp
  · refine ⟨2*q^2*H*K+r,?_⟩
    rw [ha,hb] at hr; linear_combination hr

/-- Away from an exact root the only error is twice H times the value.
Vanishing modulo the width therefore suffices for the scalar estimate. -/
theorem base_differential (a b H K e h : ℤ)
    (hy : h ∣ (a-3)^2-e*b^2+2) (hH : h ∣ H)
    (hmain : 2*h^2 ∣ 2*((3*a-11)*H-3*e*b*K)) :
    2*h^2 ∣ 2*(a-3)*(a*H+e*b*K)-2*e*b*(a*K+b*H) := by
  have he : 2*(a-3)*(a*H+e*b*K)-2*e*b*(a*K+b*H)=
      2*((3*a-11)*H-3*e*b*K)+2*H*((a-3)^2-e*b^2+2) := by ring
  obtain ⟨u,hu⟩ := hH; obtain ⟨v,hv⟩ := hy
  rw [he]
  exact hmain.add ⟨u*v,by rw [hu,hv]; ring⟩

/-- Coordinate congruences already determine a quadratic value modulo h. -/
theorem value_congruence (a b A B e h : ℤ)
    (ha : h ∣ a-A) (hb : h ∣ b-B) (hv : h ∣ (A-3)^2-e*B^2+2) :
    h ∣ (a-3)^2-e*b^2+2 := by
  convert ((ha.mul_right (a+A-6)).sub (hb.mul_right (e*(b+B)))).add hv using 1; ring

theorem product_differential (a b e p q H K h : ℤ)
    (hp : h ∣ p) (hq : h ∣ q) (hH : h ∣ H) (hK : h ∣ K) :
    2*h^2 ∣ 2*a*(p*H+e*q*K)-2*b*(p*K+q*H) := by
  obtain ⟨u,rfl⟩ := hp; obtain ⟨v,rfl⟩ := hq
  obtain ⟨w,rfl⟩ := hH; obtain ⟨z,rfl⟩ := hK
  exact ⟨a*(u*w+e*v*z)-b*(u*z+v*w),by ring⟩

/-- Width two has a stronger factor four in H, so the base differential
is divisible by eight at every point, without a root or parity hypothesis. -/
theorem scalar_two (a b H K e : ℤ)
    (he : 2 ∣ e) (hH : 4 ∣ H) (hK : 2 ∣ K) :
    8 ∣ 2*(a-3)*(a*H+e*b*K)-2*e*b*(a*K+b*H) := by
  obtain ⟨v,rfl⟩ := he; obtain ⟨w,rfl⟩ := hH; obtain ⟨z,rfl⟩ := hK
  exact ⟨(a*(a-3)-2*v*b^2)*w-3*v*b*z,by ring⟩

/-- For width four, the matching norm character and orbit character give
the extra bit; no particular unit or centre appears. -/
theorem scalar_four (a b H K e s : ℤ)
    (hs : s=1 ∨ s= -1) (he : 4 ∣ e+1)
    (ha : 4 ∣ a+s*b-1) (hH : 4 ∣ H) (hN : 16 ∣ H-s*K) :
    32 ∣ 2*((3*a-11)*H-3*e*b*K) := by
  obtain ⟨u,hu⟩ := ha; obtain ⟨v,hv⟩ := he
  obtain ⟨w,hw⟩ := hH; obtain ⟨z,hz⟩ := hN
  have hee : e=4*v-1 := by omega
  rcases hs with rfl|rfl
  · have haa : a=1-b+4*u := by omega
    have hkk : K=4*w-16*z := by omega
    exact ⟨(-2+3*u-3*v*b)*w+3*(4*v-1)*b*z,by rw [haa,hee,hw,hkk]; ring⟩
  · have haa : a=1+b+4*u := by omega
    have hkk : K= -4*w+16*z := by omega
    exact ⟨(-2+3*u+3*v*b)*w-3*(4*v-1)*b*z,by rw [haa,hee,hw,hkk]; ring⟩

/-- U²=-WN reduces the scalar term to a base-field term and a product
whose two factors already have the required width. -/
theorem scalar_of_norm {R : Type*} [CommRing R] (L : R →ₗ[ℤ] ℤ)
    (y U N : R) (c h : ℤ) (hs : U^2= -(1+c • U)*N)
    (hN : 2*h^2 ∣ L (y*N)) (herror : 2*h^2 ∣ L ((y*U)*N)) :
    2*h^2 ∣ L (y*U^2) := by
  have hr : y*U^2= -(y*N)-c • ((y*U)*N) := by
    rw [hs]; simp only [zsmul_eq_mul]; ring
  rw [hr,map_sub,map_neg,map_smul,smul_eq_mul]
  exact (dvd_neg.mpr hN).sub (herror.mul_left c)


/-- For e=2 modulo four, a shifted norm vanishing modulo four
already forces two odd base coordinates. -/
theorem root_two (a b e : ℤ) (he : 4 ∣ e-2)
    (hy : 4 ∣ (a-3)^2-e*b^2+2) : 2 ∣ a-1 ∧ 2 ∣ b-1 := by
  have hs : (4:ℤ) ∣ (a-3)^2-2*b^2+2 := by
    convert hy.add (he.mul_right (b^2)) using 1; ring
  have hn2 : (2:ℤ) ∣ (a-3)^2 := by omega
  have hn4 : (4:ℤ) ∣ (a-3)^2 := by
    simpa using IntegerParity.square_difference_four (a-3) 0 (by simpa using hn2)
  have hpa := IntegerParity.square_sub_self_even (a-3)
  have hpb := IntegerParity.square_sub_self_even b
  exact ⟨by omega,by omega⟩

/-- An odd product congruent to a square forces its square root to be odd. -/
theorem odd_of_product_square (a b c : ℤ)
    (ha : 2 ∣ a-1) (hb : 2 ∣ b-1) (h : 2 ∣ a*b-c^2) : 2 ∣ c-1 := by
  have hp : (2:ℤ) ∣ a*b-1 := by
    convert (ha.mul_right b).add hb using 1; ring
  have hs := IntegerParity.square_sub_self_even c
  omega

/-- Primitive off-base direction and odd root coordinates force the
normalized derivative to be odd. -/
theorem derivative_two (a b c u p q e : ℤ)
    (he : 4 ∣ e-2) (ha : 2 ∣ a-1) (hb : 2 ∣ b-1)
    (hc : 2 ∣ c-1) (hu : 2 ∣ u-1) (hp : 4 ∣ p)
    (hq : 4 ∣ q-2*c*u) :
    16 ∣ 2*(a-3)*p-2*e*b*q-8 := by
  obtain ⟨E,hE⟩ := he; obtain ⟨A,hA⟩ := ha; obtain ⟨B,hB⟩ := hb
  obtain ⟨C,hC⟩ := hc; obtain ⟨U,hU⟩ := hu; obtain ⟨P,hP⟩ := hp
  obtain ⟨Q,hQ⟩ := hq
  have hee : e=2+4*E := by omega
  have haa : a=1+2*A := by omega
  have hbb : b=1+2*B := by omega
  have hcc : c=1+2*C := by omega
  have huu : u=1+2*U := by omega
  have hqq : q=2*c*u+4*Q := by omega
  rw [hee,haa,hbb,hP,hqq,hcc,huu]
  ring_nf; omega


end Tetrahedral.RelativeDirection
