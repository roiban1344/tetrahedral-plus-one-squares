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
    (hH : 2 ∣ H-a^2-e*b^2) (hK : 2 ∣ K-2*a*b) :
    2 ∣ H ∧ 2 ∣ K := by
  obtain ⟨p,hp⟩ := hH; obtain ⟨r,hr⟩ := hK
  constructor
  · refine ⟨2*q^2*(H^2+e*K^2)+p,?_⟩
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

/-- The differential on a base-field multiple, evaluated at a root. -/
theorem at_root (a b H K e : ℤ) (hy : (a-3)^2-e*b^2+2=0) :
    2*(a-3)*(a*H+e*b*K)-2*e*b*(a*K+b*H)=
      2*((3*a-11)*H-3*e*b*K) := by
  linear_combination 2*H*hy

theorem product_differential (a b e p q H K h : ℤ)
    (hp : h ∣ p) (hq : h ∣ q) (hH : h ∣ H) (hK : h ∣ K) :
    2*h^2 ∣ 2*a*(p*H+e*q*K)-2*b*(p*K+q*H) := by
  obtain ⟨u,rfl⟩ := hp; obtain ⟨v,rfl⟩ := hq
  obtain ⟨w,rfl⟩ := hH; obtain ⟨z,rfl⟩ := hK
  exact ⟨a*(u*w+e*v*z)-b*(u*z+v*w),by ring⟩

theorem scalar_two (a b H K e : ℤ)
    (ha : 2 ∣ a-1) (he : 2 ∣ e) (hH : 2 ∣ H) (hK : 2 ∣ K) :
    8 ∣ 2*((3*a-11)*H-3*e*b*K) := by
  obtain ⟨u,hu⟩ := ha; obtain ⟨v,rfl⟩ := he
  obtain ⟨w,rfl⟩ := hH; obtain ⟨z,rfl⟩ := hK
  have haa : a=1+2*u := by omega
  exact ⟨(-4+3*u)*w-3*v*b*z,by rw [haa]; ring⟩

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


/-- For e=2 modulo four, the shifted norm root has two odd base coordinates. -/
theorem root_two (a b e : ℤ) (he : 4 ∣ e-2) (hy : (a-3)^2-e*b^2+2=0) :
    2 ∣ a-1 ∧ 2 ∣ b-1 := by
  obtain ⟨k,hk⟩ := he
  have hee : e=2+4*k := by omega
  have hs : (2:ℤ) ∣ (a-3)^2 := ⟨(1+2*k)*b^2-1,by rw [hee] at hy; nlinarith only [hy]⟩
  have hpa := IntegerParity.square_sub_self_even (a-3)
  have ha : (2:ℤ) ∣ a-1 := by omega
  obtain ⟨u,hu⟩ := ha
  have haa : a=1+2*u := by omega
  have hb : (2:ℤ) ∣ b^2-1 :=
    ⟨(u-1)^2-k*b^2,by rw [hee,haa] at hy; nlinarith only [hy]⟩
  have hpb := IntegerParity.square_sub_self_even b
  exact ⟨⟨u,hu⟩,by omega⟩

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
