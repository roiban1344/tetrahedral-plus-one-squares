import Mathlib.Tactic

/-!
# The ring `ℤ[q][s]` for the branch d=3

`q² = 2` and `s² = 6q`. An element `(a₀,a₁,b₀,b₁)` stands for `(a₀+a₁q)+(b₀+b₁q)s`.
The field is `K = F(√(6q))` with `F = ℚ(√2)`; it is the quartic field of the branch d=3.

The relative norm to `ℤ[q]` is `A² − 6qB²`, recorded by its two coordinates `relH`, `relK`.
-/

namespace Tetrahedral.Quartic3

structure R where
  coeff : Fin 4 → ℤ
  deriving DecidableEq

namespace R
instance : CoeFun R (fun _ => Fin 4 → ℤ) := ⟨coeff⟩
@[ext] theorem ext {x y : R} (h : ∀ i,x i=y i) : x=y := by
  cases x;cases y;congr;exact funext h
def equiv : R ≃ (Fin 4 → ℤ) := ⟨coeff,mk,by intro x;cases x;rfl,by intro x;rfl⟩
instance : AddCommGroup R := equiv.addCommGroup
@[simp] theorem zero_apply (i : Fin 4) : (0:R) i=0 := rfl
@[simp] theorem add_apply (x y : R) (i : Fin 4) : (x+y) i=x i+y i := rfl
@[simp] theorem neg_apply (x : R) (i : Fin 4) : (-x) i= -x i := rfl
@[simp] theorem sub_apply (x y : R) (i : Fin 4) : (x-y) i=x i-y i := rfl
@[simp] theorem zsmul_apply (k : ℤ) (x : R) (i : Fin 4) : (k • x) i=k*x i := rfl
def one : R := ⟨![1,0,0,0]⟩
def mul (x y : R) : R :=
  ⟨![x 0*y 0+2*x 1*y 1+12*(x 2*y 3+x 3*y 2),
     x 0*y 1+x 1*y 0+6*(x 2*y 2+2*x 3*y 3),
     x 0*y 2+x 2*y 0+2*(x 1*y 3+x 3*y 1),
     x 0*y 3+x 3*y 0+x 1*y 2+x 2*y 1]⟩
instance : CommRing R :=
  { (inferInstance : AddCommGroup R) with
    one := one
    mul := mul
    mul_assoc := by
      intro x y z;change mul (mul x y) z=mul x (mul y z)
      ext i;fin_cases i <;> simp [mul] <;> ring
    one_mul := by intro x;change mul one x=x;ext i;fin_cases i <;> simp [mul,one]
    mul_one := by intro x;change mul x one=x;ext i;fin_cases i <;> simp [mul,one]
    left_distrib := by
      intro x y z;change mul x (y+z)=mul x y+mul x z
      ext i;fin_cases i <;> simp [mul] <;> ring
    right_distrib := by
      intro x y z;change mul (x+y) z=mul x z+mul y z
      ext i;fin_cases i <;> simp [mul] <;> ring
    mul_comm := by
      intro x y;change mul x y=mul y x;ext i;fin_cases i <;> simp [mul] <;> ring
    zero_mul := by intro x;change mul 0 x=0;ext i;fin_cases i <;> simp [mul]
    mul_zero := by intro x;change mul x 0=0;ext i;fin_cases i <;> simp [mul] }
@[simp] theorem one_apply (i : Fin 4) : (1:R) i=if i=0 then 1 else 0 := by fin_cases i <;> rfl
theorem mul_apply (x y : R) : x*y=mul x y := rfl
@[simp] theorem mul_apply0 (x y : R) : (x*y) 0=x 0*y 0+2*x 1*y 1+12*(x 2*y 3+x 3*y 2) := rfl
@[simp] theorem mul_apply1 (x y : R) : (x*y) 1=x 0*y 1+x 1*y 0+6*(x 2*y 2+2*x 3*y 3) := rfl
@[simp] theorem mul_apply2 (x y : R) : (x*y) 2=x 0*y 2+x 2*y 0+2*(x 1*y 3+x 3*y 1) := rfl
@[simp] theorem mul_apply3 (x y : R) : (x*y) 3=x 0*y 3+x 3*y 0+x 1*y 2+x 2*y 1 := rfl

/-- Relative norm `A² − 6qB²`, first coordinate. -/
def relH (x : R) : ℤ := (x 0)^2+2*(x 1)^2-24*x 2*x 3
/-- Relative norm, coefficient of `q`. -/
def relK (x : R) : ℤ := 2*x 0*x 1-6*((x 2)^2+2*(x 3)^2)

theorem relH_mul (x y : R) : relH (x*y)=relH x*relH y+2*relK x*relK y := by
  simp only [relH,relK,mul_apply0,mul_apply1,mul_apply2,mul_apply3]; ring
theorem relK_mul (x y : R) : relK (x*y)=relH x*relK y+relK x*relH y := by
  simp only [relH,relK,mul_apply0,mul_apply1,mul_apply2,mul_apply3]; ring

/-- The conjugation `s ↦ −s` of `K/F`. -/
def tau (x : R) : R := ⟨![x 0,x 1,-x 2,-x 3]⟩
@[simp] theorem tau_apply0 (x : R) : tau x 0=x 0 := rfl
@[simp] theorem tau_apply1 (x : R) : tau x 1=x 1 := rfl
@[simp] theorem tau_apply2 (x : R) : tau x 2= -x 2 := rfl
@[simp] theorem tau_apply3 (x : R) : tau x 3= -x 3 := rfl
theorem tau_mul (x y : R) : tau (x*y)=tau x*tau y := by
  ext i;fin_cases i <;> simp <;> ring
theorem mul_tau (x : R) : x*tau x=⟨![relH x,relK x,0,0]⟩ := by
  ext i;fin_cases i <;> simp [relH,relK] <;> ring

end R

open R
def rho : R := ⟨![17,12,6,4]⟩
def rhoInv : R := ⟨![17,12,-6,-4]⟩
def rhoU : Rˣ := ⟨rho,rhoInv,by decide,by decide⟩

end Tetrahedral.Quartic3
