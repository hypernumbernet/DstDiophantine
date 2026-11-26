import DstDiophantine.Algebra.RelativeRotor
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

set_option linter.style.whitespace false

/-!
# Mismatch angle from the relative rotor `Ω = R_usual† R_dual`

On the one-axis family (`axisParams`) the boost and dual generators commute, so
`Ω = exp(ω_mismatch)` with explicit boost and rotation half-coefficients. The
dual overlap factor used in gravity charts is the grade-zero coefficient of
this motor; it is recorded here as `dualOverlap`. The legacy Killing scalar
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

/-! ### Dual overlap: Clifford grade-0 of `Ω` on one axis -/

/-- Dual overlap: grade-zero of `R_usual† R_dual` on the axis family (`cosh·cos`). -/
noncomputable def dualOverlap (α β : ℝ) : ℝ :=
  Real.cosh (α / 2) * Real.cos (β / 2)

/-- Legacy papers / shell charts: full bivector interference factor. -/
noncomputable def axisOverlapLegacy (α β : ℝ) : ℝ :=
  Real.cosh (α / 2) * Real.cos (β / 2) - Real.sinh (α / 2) * Real.sin (β / 2)

/-- Clifford grade-zero of the axis motor (equals `dualOverlap`). -/
noncomputable def pgaAxisMotorGradeZero (α β : ℝ) : ℝ :=
  dualOverlap α β

theorem pgaAxisMotorGradeZero_eq_dualOverlap (α β : ℝ) :
    pgaAxisMotorGradeZero α β = dualOverlap α β := rfl

theorem dualOverlap_factor_cosh_cos (α β : ℝ) :
    dualOverlap α β =
      Real.cosh (α / 2) * Real.cos (β / 2) := rfl

theorem axisOverlapLegacy_eq_components (α β : ℝ) :
    axisOverlapLegacy α β =
      Real.cosh (α / 2) * Real.cos (β / 2) - Real.sinh (α / 2) * Real.sin (β / 2) := rfl

theorem dualOverlap_eq_zero_iff (α β : ℝ) :
    dualOverlap α β = 0 ↔ Real.cos (β / 2) = 0 := by
  simp only [dualOverlap]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with hcosh | hcos
    · linarith [Real.cosh_pos (α / 2), hcosh]
    · exact hcos
  · intro hcos
    simp [hcos]

theorem dualOverlap_nonpos_iff (α β : ℝ) :
    dualOverlap α β ≤ 0 ↔ Real.cos (β / 2) ≤ 0 := by
  simp only [dualOverlap]
  constructor
  · intro h
    rcases mul_nonpos_iff.mp h with h1 | h2
    · exact h1.2
    · linarith [Real.cosh_pos (α / 2)]
  · intro hcos
    exact mul_nonpos_of_nonneg_of_nonpos (Real.cosh_pos (α / 2)).le hcos

theorem dualOverlap_nonneg_iff (α β : ℝ) :
    0 ≤ dualOverlap α β ↔ 0 ≤ Real.cos (β / 2) := by
  simp only [dualOverlap]
  constructor
  · intro h
    rcases mul_nonneg_iff.mp h with h1 | h2
    · exact h1.2
    · linarith [Real.cosh_pos (α / 2)]
  · intro hcos
    exact mul_nonneg (Real.cosh_pos (α / 2)).le hcos

theorem dualOverlap_zero_at_full_rotation (α : ℝ) :
    dualOverlap α Real.pi = 0 := by
  simp [dualOverlap, Real.cos_pi]

theorem dualOverlap_balanced (x : ℝ) :
    dualOverlap (2 * x) (2 * x) = Real.cosh x * Real.cos x := by
  simp [dualOverlap, mul_div_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0)]

theorem dualOverlap_balanced_eq_zero_iff {x : ℝ} :
    dualOverlap (2 * x) (2 * x) = 0 ↔ Real.cos x = 0 := by
  rw [dualOverlap_balanced]
  have hc : 0 < Real.cosh x := Real.cosh_pos x
  simp [hc.ne']

theorem dualOverlap_admissible_nonneg {α β : ℝ}
    (_hα : 0 ≤ α) (hβ : 0 ≤ β) (hβle : β ≤ Real.pi) :
    0 ≤ dualOverlap α β := by
  rw [dualOverlap_nonneg_iff]
  have hhalf : β / 2 ≤ Real.pi / 2 := by linarith [hβle, Real.pi_pos]
  rcases le_iff_eq_or_lt.mp hhalf with heq | hβlt
  · have hcos : Real.cos (β / 2) = 0 := by
      have : β / 2 = Real.pi / 2 := by linarith [heq, Real.pi_pos]
      simp [this, Real.cos_pi_div_two]
    simp [hcos]
  · exact (Real.cos_pos_of_mem_Ioo ⟨by linarith [hβ], by linarith [hβlt, Real.pi_pos]⟩).le

theorem dualOverlap_cone_nonneg {α β : ℝ}
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hβle : β ≤ Real.pi / 2) :
    0 ≤ dualOverlap α β :=
  dualOverlap_admissible_nonneg hα hβ (le_trans hβle (by linarith [Real.pi_pos]))

/-! ### Legacy overlap sign (papers; electron / strong charts) -/

theorem axisOverlapLegacy_balanced (x : ℝ) :
    axisOverlapLegacy (2 * x) (2 * x) =
      Real.cosh x * Real.cos x - Real.sinh x * Real.sin x := by
  simp [axisOverlapLegacy, mul_div_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0)]

private theorem axisOverlapLegacy_balanced_neg_at_pi :
    axisOverlapLegacy Real.pi Real.pi < 0 := by
  have h := axisOverlapLegacy_balanced (Real.pi / 2)
  have hπ : (2 : ℝ) * (Real.pi / 2) = Real.pi := by ring
  rw [hπ] at h
  simp only [Real.cos_pi_div_two, Real.sin_pi_div_two] at h
  have hsinh : 0 < Real.sinh (Real.pi / 2) := by positivity
  linarith

theorem axisOverlapLegacy_sign_reversal_at_pi :
    axisOverlapLegacy 0 0 > 0 ∧
      axisOverlapLegacy Real.pi Real.pi < 0 :=
  ⟨by simp [axisOverlapLegacy], axisOverlapLegacy_balanced_neg_at_pi⟩

theorem dualOverlap_sign_reversal_threshold :
    dualOverlap 0 0 > 0 ∧
      dualOverlap 0 Real.pi = 0 ∧
        dualOverlap Real.pi Real.pi = 0 ∧
        mismatchRotationHalf 0 Real.pi = Real.pi / 2 ∧
          axisOverlapLegacy Real.pi Real.pi < 0 := by
  refine ⟨?_, dualOverlap_zero_at_full_rotation 0, ?_, by simp [mismatchRotationHalf],
    axisOverlapLegacy_sign_reversal_at_pi.2⟩
  · simp [dualOverlap]
  · simp [dualOverlap, Real.cos_pi]

/-- Multi-axis overlap: product of per-axis Clifford grade-zero factors (axis-decoupled chart). -/
noncomputable def relativeRotorOverlap (p : TorsionParams) : ℝ :=
  dualOverlap (p.alpha 0) (p.beta 0) *
    dualOverlap (p.alpha 1) (p.beta 1) *
    dualOverlap (p.alpha 2) (p.beta 2)

theorem relativeRotorOverlap_axisParams (α β : ℝ) :
    relativeRotorOverlap (axisParams α β) = dualOverlap α β := by
  simp only [relativeRotorOverlap, axisParams, dualOverlap,
    Fin.reduceFinMk, Nat.succ_eq_add_one, Nat.add_zero, Nat.zero_eq, one_mul, mul_one]
  simp [Real.cosh_zero, Real.cos_zero]

theorem relativeRotor_axis_dualOverlap_eq_gradeZero (α β : ℝ) :
    dualOverlap α β = pgaAxisMotorGradeZero α β ∧
      relativeRotorOverlap (axisParams α β) = dualOverlap α β ∧
        relativeRotor (axisParams α β) = exp (omegaMismatchAxis α β) := by
  refine ⟨rfl, ⟨relativeRotorOverlap_axisParams α β, relativeRotor_axis_eq_exp α β⟩⟩

end MismatchAngle
end DstDiophantine