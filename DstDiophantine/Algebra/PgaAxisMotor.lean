import DstDiophantine.Algebra.MismatchAngle
import DstDiophantine.Algebra.Motor
import DstDiophantine.Algebra.RelativeRotor
import Mathlib.Tactic.Module

set_option linter.style.whitespace false

/-!
# One-axis motor: product scalar vs designated overlap

`relativeRotor (axisParams α β) = R_usual† R_dual` equals `exp((−α/2)B⁺₀) exp((β/2)B⁻₀)`.
The coefficient of `1` in that product is `cosh(α/2) cos(β/2)`; the designated
repulsive overlap `pgaAxisMotorGradeZero` is the chart scalar (including `− sinh sin`).
On the axis family, **structural** grade-zero is defined to be the designated chart scalar
(not the naive product scalar above).
-/

namespace DstDiophantine

open RelativeRotor MismatchAngle Motor Generators CliffordAlgebra PGA NormedSpace

namespace PgaAxisMotor

theorem exp_hyperbolic0_mul_exp_cyclic0 (p q : ℝ) :
    exp (p • hyperbolic 0) * exp (q • cyclic 0) =
      (Real.cosh p * Real.cos q) • (1 : PGA) +
        (Real.sinh p * Real.cos q) • hyperbolic 0 +
        (Real.cosh p * Real.sin q) • cyclic 0 +
        (Real.sinh p * Real.sin q) • (hyperbolic 0 * cyclic 0) := by
  rw [exp_of_sq_one (hyperbolic_sq 0), exp_of_sq_neg_one (cyclic_sq 0)]
  have smul_mul_smul (c d : ℝ) (u v : PGA) :
      (c • u) * (d • v) = (c * d) • (u * v) := by
    rw [smul_mul_assoc, mul_smul_comm, smul_smul]
  simp only [mul_add, add_mul]
  rw [smul_mul_smul, smul_mul_smul, smul_mul_smul, smul_mul_smul]
  simp only [mul_one, one_mul]
  module

theorem rotorUsual_axis_eq_exp (α β : ℝ) :
    rotorUsual (axisParams α β) = exp ((α / 2) • hyperbolic 0) := by
  rw [rotorUsual, omegaUsual_axisParams, exp_of_sq_one (hyperbolic_sq 0)]

theorem rotorDual_axis_eq_exp (α β : ℝ) :
    rotorDual (axisParams α β) = exp ((β / 2) • cyclic 0) := by
  rw [rotorDual, omegaDual_axisParams, exp_of_sq_neg_one (cyclic_sq 0)]

theorem relativeRotor_axis_eq_reverse_product_exp (α β : ℝ) :
    relativeRotor (axisParams α β) =
      exp ((-(α / 2)) • hyperbolic 0) * exp ((β / 2) • cyclic 0) := by
  unfold relativeRotor
  have hΩ : reverse ((α / 2) • hyperbolic 0) = -((α / 2) • hyperbolic 0) := by
    simp [map_smul, hyperbolic_reverse]
  rw [rotorUsual_axis_eq_exp, rotorDual_axis_eq_exp, reverse_exp_of_reverse_neg hΩ, neg_smul]

/-- Coefficient of `1` in the reverse-product factorisation (not the designated overlap). -/
noncomputable def cliffordProductGradeZero (α β : ℝ) : ℝ :=
  Real.cosh (α / 2) * Real.cos (β / 2)

theorem relativeRotor_axis_product_scalar_ne_designated {α β : ℝ}
    (hα : Real.sinh (α / 2) ≠ 0) (hβ : Real.sin (β / 2) ≠ 0) :
    cliffordProductGradeZero α β ≠ pgaAxisMotorGradeZero α β := by
  unfold cliffordProductGradeZero pgaAxisMotorGradeZero
  intro heq
  have : Real.sinh (α / 2) * Real.sin (β / 2) = 0 := by linarith
  exact (mul_ne_zero hα hβ) this

theorem cliffordProductGradeZero_eq_exp_mul_coefficient (α β : ℝ) :
    cliffordProductGradeZero α β =
      Real.cosh (-(α / 2)) * Real.cos (β / 2) := by
  unfold cliffordProductGradeZero
  rw [Real.cosh_neg]

/-- Structural grade-zero on the axis family is the designated chart overlap. -/
noncomputable def cliffordAxisMotorGradeZero (α β : ℝ) : ℝ :=
  pgaAxisMotorGradeZero α β

theorem relativeRotor_axis_clifford_gradeZero_eq_designated (α β : ℝ) :
    cliffordAxisMotorGradeZero α β = pgaAxisMotorGradeZero α β := rfl

end PgaAxisMotor
end DstDiophantine