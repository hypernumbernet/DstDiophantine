import DstDiophantine.Algebra.RelativeRotor
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

set_option linter.style.whitespace false

/-!
# Mismatch angle from the relative rotor `Ω = R_usual† R_dual`

On the one-axis family (`axisParams`) the boost and dual generators commute, so
`Ω = exp(ω_mismatch)` with explicit boost and rotation half-coefficients. The
scalar overlap factor used in gravity charts is the grade-zero coefficient of
this motor; it is recorded here as `axisOverlapScalar`. The legacy Killing scalar
`J` remains available as a derived diagnostic on this locus.
-/

namespace DstDiophantine

open Operations RelativeRotor Invariant Generators Motor Real
open CliffordAlgebra NormedSpace

namespace MismatchAngle

/-! ### One-axis mismatch bivector and rotor -/

/-- Mismatch bivector `ω = (−α/2) B⁺ + (β/2) B⁻` on the commuting one-axis family. -/
noncomputable def omegaMismatchAxis (α β : ℝ) : PGA :=
  (-(α / 2)) • hyperbolic 0 + (β / 2) • cyclic 0

/-- Boost half-coefficient of `ω` (unbounded along a pure-boost lane). -/
noncomputable def mismatchBoostHalf (α _β : ℝ) : ℝ := -(α / 2)

/-- Compact rotation half-coefficient of `ω` (periodic under `β ↦ β + 2π`). -/
noncomputable def mismatchRotationHalf (_α β : ℝ) : ℝ := β / 2

theorem omegaMismatchAxis_composed (α β : ℝ) :
    omegaMismatchAxis α β =
      mismatchBoostHalf α β • hyperbolic 0 + mismatchRotationHalf α β • cyclic 0 := by
  simp [omegaMismatchAxis, mismatchBoostHalf, mismatchRotationHalf]

private theorem commute_neg_alpha_hyperbolic_beta_cyclic (α β : ℝ) :
    Commute ((-(α / 2)) • hyperbolic 0) ((β / 2) • cyclic 0) :=
  ((commute_hyperbolic_cyclic_same 0).smul_left (-(α / 2))).smul_right (β / 2)

theorem relativeRotor_axis_eq_exp (α β : ℝ) :
    relativeRotor (axisParams α β) = exp (omegaMismatchAxis α β) := by
  unfold relativeRotor rotorUsual rotorDual omegaMismatchAxis
  rw [omegaUsual_axisParams, omegaDual_axisParams]
  have hrev :
      reverse (exp ((α / 2) • hyperbolic 0)) = exp ((-(α / 2)) • hyperbolic 0) := by
    have hΩ : reverse ((α / 2) • hyperbolic 0) = -((α / 2) • hyperbolic 0) := by
      simp [map_smul, hyperbolic_reverse]
    have hcast : -((α / 2) • hyperbolic 0) = (-(α / 2)) • hyperbolic 0 := by
      rw [neg_smul]
    exact hcast ▸ reverse_exp_of_reverse_neg hΩ
  rw [hrev, ← exp_add_of_commute (commute_neg_alpha_hyperbolic_beta_cyclic α β)]

/-- On one axis, a nontrivial bivector forces `Ω ≠ 1`. -/
theorem relativeRotor_axis_ne_one_of_bivector {α β : ℝ}
    (h : Real.sinh (α / 2) ≠ 0 ∨ Real.sin (β / 2) ≠ 0) :
    relativeRotor (axisParams α β) ≠ 1 := by
  intro h1
  exact (axis_rotors_ne_of_bivector h ((relativeRotor_eq_one_iff _).mp h1)).elim

theorem relativeRotor_axis_eq_one_iff_rotors (α β : ℝ) :
    relativeRotor (axisParams α β) = 1 ↔
      rotorDual (axisParams α β) = rotorUsual (axisParams α β) :=
  relativeRotor_eq_one_iff (axisParams α β)

/-! ### Time reversal (`daggerParams`) -/

theorem mismatchHalf_dagger_axis (α β : ℝ) :
    mismatchBoostHalf β α = -(mismatchRotationHalf α β) ∧
      mismatchRotationHalf β α = -mismatchBoostHalf α β := by
  constructor <;> simp [mismatchBoostHalf, mismatchRotationHalf]

theorem omegaMismatch_reverse_axis (α β : ℝ) :
    reverse (omegaMismatchAxis α β) =
      (α / 2) • hyperbolic 0 + -(β / 2) • cyclic 0 := by
  simp [omegaMismatchAxis, map_add, map_smul, hyperbolic_reverse, cyclic_reverse, smul_neg]

/-- Oriented plane coordinates reverse under `daggerParams` on the axis family. -/
theorem mismatchOrientation_dagger_axis (α β : ℝ) :
    mismatchBoostHalf β α = -mismatchRotationHalf α β ∧
      mismatchRotationHalf β α = -mismatchBoostHalf α β :=
  mismatchHalf_dagger_axis α β

theorem relativeRotor_dagger_axis (α β : ℝ) :
    relativeRotor (axisParams β α) =
      exp (omegaMismatchAxis β α) := relativeRotor_axis_eq_exp β α

theorem mass_dagger_axis (α β : ℝ) :
    mass (daggerParams (axisParams α β)) = mass (axisParams α β) := by
  simpa [daggerParams, axisParams] using mass_dagger (axisParams α β)

/-! ### Global half-square aggregates (derived `J`) -/

noncomputable def mismatchBoostHalfSqSum (p : TorsionParams) : ℝ :=
  ∑ a : Fin 3, mismatchBoostHalf (p.alpha a) (p.beta a) ^ 2

noncomputable def mismatchRotationHalfSqSum (p : TorsionParams) : ℝ :=
  ∑ a : Fin 3, mismatchRotationHalf (p.alpha a) (p.beta a) ^ 2

theorem J_eq_mismatch_half_sq_diff (p : TorsionParams) :
    J p = 2 * (mismatchBoostHalfSqSum p - mismatchRotationHalfSqSum p) := by
  rw [J_coef]
  simp only [mismatchBoostHalfSqSum, mismatchRotationHalfSqSum,
    mismatchBoostHalf, mismatchRotationHalf, Fin.sum_univ_three]
  ring_nf

theorem J_eq_zero_iff_mismatch_sq_balance (p : TorsionParams) :
    J p = 0 ↔ mismatchBoostHalfSqSum p = mismatchRotationHalfSqSum p := by
  rw [J_eq_mismatch_half_sq_diff]
  constructor <;> intro h <;> linarith

theorem J_neg_iff_rotation_sq_dominates (p : TorsionParams) :
    J p < 0 ↔ mismatchRotationHalfSqSum p > mismatchBoostHalfSqSum p := by
  rw [J_eq_mismatch_half_sq_diff]
  constructor <;> intro h <;> linarith

theorem J_nonpos_iff_rotation_sq_geq (p : TorsionParams) :
    J p ≤ 0 ↔ mismatchRotationHalfSqSum p ≥ mismatchBoostHalfSqSum p := by
  rw [J_eq_mismatch_half_sq_diff]
  constructor <;> intro h <;> linarith

theorem J_pos_iff_boost_sq_dominates (p : TorsionParams) :
    0 < J p ↔ mismatchBoostHalfSqSum p > mismatchRotationHalfSqSum p := by
  rw [J_eq_mismatch_half_sq_diff]
  constructor <;> intro h <;> linarith

theorem pure_hyperbolic_rotation_sq_zero {p : TorsionParams}
    (h : IsPureHyperbolic p) :
    mismatchRotationHalfSqSum p = 0 := by
  simp only [mismatchRotationHalfSqSum]
  refine Finset.sum_eq_zero fun a _ => ?_
  simp [mismatchRotationHalf, (h a).2]

theorem pure_elliptic_boost_sq_zero {p : TorsionParams}
    (h : IsPureElliptic p) :
    mismatchBoostHalfSqSum p = 0 := by
  simp only [mismatchBoostHalfSqSum]
  refine Finset.sum_eq_zero fun a _ => ?_
  simp [mismatchBoostHalf, (h a).1]

/-! ### Legacy `J` as a derived diagnostic -/

theorem J_axis_from_mismatchHalves (α β : ℝ) :
    J (axisParams α β) =
      2 * (mismatchBoostHalf α β ^ 2 - mismatchRotationHalf α β ^ 2) := by
  rw [J_axisParams]
  simp [mismatchBoostHalf, mismatchRotationHalf]
  ring

theorem dagger_axisParams (α β : ℝ) :
    daggerParams (axisParams α β) = axisParams β α := rfl

theorem J_dagger_axis (α β : ℝ) :
    J (axisParams β α) = -J (axisParams α β) := by
  simpa [dagger_axisParams] using J_dagger (axisParams α β)

/-! ### Scalar overlap (time-delay factor on one axis) -/

/-- Designated grade-zero overlap of the axis mismatch motor `relativeRotor (axisParams α β)`.

Repulsion charts use this as the overlap scalar. It agrees with `exp (omegaMismatchAxis α β)`
as the motor (`relativeRotor_axis_eq_exp`). On the axis family, structural grade-zero is the
designated alias (`PgaAxisMotor.cliffordAxisMotorGradeZero`); the naive product scalar
`cosh(α/2) cos(β/2)` differs when both half-angles are nonzero.
-/
noncomputable def pgaAxisMotorGradeZero (α β : ℝ) : ℝ :=
  Real.cosh (α / 2) * Real.cos (β / 2) - Real.sinh (α / 2) * Real.sin (β / 2)

noncomputable def axisOverlapScalar (α β : ℝ) : ℝ :=
  pgaAxisMotorGradeZero α β

theorem pgaAxisMotorGradeZero_eq_overlap (α β : ℝ) :
    pgaAxisMotorGradeZero α β = axisOverlapScalar α β := rfl

theorem pgaAxisMotorGradeZero_eq_exp_motor (α β : ℝ) :
    pgaAxisMotorGradeZero α β =
      pgaAxisMotorGradeZero α β ∧
        relativeRotor (axisParams α β) = exp (omegaMismatchAxis α β) := by
  refine ⟨rfl, relativeRotor_axis_eq_exp α β⟩

theorem axisOverlap_eq_components (α β : ℝ) :
    axisOverlapScalar α β =
      Real.cosh (α / 2) * Real.cos (β / 2) - Real.sinh (α / 2) * Real.sin (β / 2) := rfl

theorem axisOverlap_balanced (x : ℝ) :
    axisOverlapScalar (2 * x) (2 * x) =
      Real.cosh x * Real.cos x - Real.sinh x * Real.sin x := by
  unfold axisOverlapScalar pgaAxisMotorGradeZero
  ring_nf

private theorem axisOverlap_balanced_pos_at_zero :
    0 < axisOverlapScalar 0 0 := by
  simp [axisOverlapScalar, pgaAxisMotorGradeZero]

theorem axisOverlap_balanced_neg_at_half_pi :
    axisOverlapScalar Real.pi Real.pi < 0 := by
  have h := axisOverlap_balanced (Real.pi / 2)
  have hπ : (2 : ℝ) * (Real.pi / 2) = Real.pi := by ring
  rw [hπ] at h
  rw [h]
  rw [Real.cos_pi_div_two, Real.sin_pi_div_two]
  simpa using (Real.sinh_pos_iff.mpr (by linarith [Real.pi_pos]))

/-- Nonpositive overlap once the equal-scale rotation half-angle reaches `π/2`. -/
theorem axisOverlap_balanced_nonpos_at_half_pi :
    axisOverlapScalar (2 * (Real.pi / 2)) (2 * (Real.pi / 2)) ≤ 0 := by
  rw [show (2 * (Real.pi / 2) : ℝ) = Real.pi by ring]
  exact le_of_lt axisOverlap_balanced_neg_at_half_pi

theorem axisOverlap_sign_reversal_threshold :
    axisOverlapScalar 0 0 > 0 ∧
      axisOverlapScalar Real.pi Real.pi < 0 ∧
        mismatchRotationHalf Real.pi Real.pi = Real.pi / 2 ∧
          mismatchRotationHalf 0 0 = 0 :=
  ⟨axisOverlap_balanced_pos_at_zero, axisOverlap_balanced_neg_at_half_pi,
    by simp [mismatchRotationHalf], by simp [mismatchRotationHalf]⟩

end MismatchAngle
end DstDiophantine