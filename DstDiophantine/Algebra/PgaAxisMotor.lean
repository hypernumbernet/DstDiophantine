import DstDiophantine.Algebra.MismatchAngle
import DstDiophantine.Algebra.Motor
import DstDiophantine.Algebra.RelativeRotor
import Mathlib.Tactic.Module

set_option linter.style.whitespace false

/-!
# One-axis motor: Clifford grade-0 of `Ω = R_usual† R_dual`

On axis 0, `relativeRotor (axisParams α β) = exp((−α/2)B⁺₀) exp((β/2)B⁻₀)` and the
coefficient of `1` is `cosh(α/2) cos(β/2)` — the dual overlap `dualOverlap`.
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

/-- Grade-0 coefficient of the reverse-product factorisation (= dual overlap). -/
noncomputable def cliffordProductGradeZero (α β : ℝ) : ℝ :=
  Real.cosh (α / 2) * Real.cos (β / 2)

theorem cliffordProductGradeZero_eq_dualOverlap (α β : ℝ) :
    cliffordProductGradeZero α β = dualOverlap α β := rfl

theorem cliffordProductGradeZero_eq_exp_mul_coefficient (α β : ℝ) :
    cliffordProductGradeZero α β =
      Real.cosh (-(α / 2)) * Real.cos (β / 2) := by
  simp only [cliffordProductGradeZero, MismatchAngle.dualOverlap]
  rw [Real.cosh_neg]

theorem relativeRotor_axis_grade_zero_eq_dualOverlap (α β : ℝ) :
    cliffordProductGradeZero α β =
      dualOverlap α β ∧
        pgaAxisMotorGradeZero α β = dualOverlap α β := by
  refine ⟨rfl, rfl⟩

end PgaAxisMotor
end DstDiophantine