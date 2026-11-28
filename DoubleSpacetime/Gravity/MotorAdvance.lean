import DoubleSpacetime.Algebra.Amplification
import DoubleSpacetime.Gravity.MotorForce

/-!
# Time advance of a fixed motor

Position and movement stay on `motorPath`. The field has already selected the generator. Advancing
the motor does not select it again.

The left factor at parameter `t` is the rotor of the torsion scaled by `t`. On axis 0 the
accumulated common rapidity and the accumulated mismatch are therefore linear, and both
accelerations vanish. The body velocity keeps the unscaled torsion: that rate is the generator,
not the accumulated angle.

The written flow agrees on the free mismatch and sources the common rapidity. Those two common
accelerations agree at every parameter only when the lag vanishes. The oscillator and the runaway
leave the common rapidity inertial and accelerate the mismatch. Neither acceleration is a
derivative along the motor.

Reading the advanced rotor back as a torsion rate multiplies the force by `t`. Reading the
advanced rotor and the advanced translator back as a new generator multiplies it by `t²`. The
generator used for the force stays the one the field selected.
-/

namespace DoubleSpacetime.Gravity.MotorAdvance

open Operations Motor Amplification KillingAxis NormedSpace
open MotorForce (boostShift motorBodyVelocity motorForceCoefficient bodyTransCoefficient
  motorPath_factor boostShift_forceCoefficient)

/-! ### Accumulated rapidity, with both channels inertial -/

/-- Common rapidity on axis 0: `α₀ + β₀`. -/
def axisCommon (p : TorsionParams) : ℝ :=
  p.alpha 0 + p.beta 0

/-- Mismatch on axis 0: `α₀ - β₀`. -/
def axisMismatch (p : TorsionParams) : ℝ :=
  p.alpha 0 - p.beta 0

/-- Accumulated common rapidity along the motor: the generator's value times the parameter. -/
def motorCommon (p : TorsionParams) (t : ℝ) : ℝ :=
  axisCommon (scaleTorsion t p)

/-- Accumulated mismatch along the motor. -/
def motorMismatch (p : TorsionParams) (t : ℝ) : ℝ :=
  axisMismatch (scaleTorsion t p)

theorem motorCommon_linear (p : TorsionParams) (t : ℝ) :
    motorCommon p t = t * axisCommon p := by
  simp only [motorCommon, axisCommon, scaleTorsion]
  ring

theorem motorMismatch_linear (p : TorsionParams) (t : ℝ) :
    motorMismatch p t = t * axisMismatch p := by
  simp only [motorMismatch, axisMismatch, scaleTorsion]
  ring

theorem hasDerivAt_motorCommon (p : TorsionParams) (t : ℝ) :
    HasDerivAt (motorCommon p) (axisCommon p) t := by
  have hfun : motorCommon p = fun s => s * axisCommon p := by
    ext s
    exact motorCommon_linear p s
  rw [hfun]
  exact ((hasDerivAt_id t).mul_const (axisCommon p)).congr_deriv (by ring)

theorem hasDerivAt_motorMismatch (p : TorsionParams) (t : ℝ) :
    HasDerivAt (motorMismatch p) (axisMismatch p) t := by
  have hfun : motorMismatch p = fun s => s * axisMismatch p := by
    ext s
    exact motorMismatch_linear p s
  rw [hfun]
  exact ((hasDerivAt_id t).mul_const (axisMismatch p)).congr_deriv (by ring)

theorem deriv_motorCommon (p : TorsionParams) :
    deriv (motorCommon p) = fun _ => axisCommon p := by
  ext t
  exact (hasDerivAt_motorCommon p t).deriv

theorem deriv_motorMismatch (p : TorsionParams) :
    deriv (motorMismatch p) = fun _ => axisMismatch p := by
  ext t
  exact (hasDerivAt_motorMismatch p t).deriv

theorem motorCommon_accel (p : TorsionParams) (t : ℝ) :
    deriv (deriv (motorCommon p)) t = 0 := by
  rw [deriv_motorCommon]
  exact (hasDerivAt_const t (axisCommon p)).deriv

theorem motorMismatch_accel (p : TorsionParams) (t : ℝ) :
    deriv (deriv (motorMismatch p)) t = 0 := by
  rw [deriv_motorMismatch]
  exact (hasDerivAt_const t (axisMismatch p)).deriv

/-- Both channel accelerations vanish along the motor. -/
theorem channels_inertial (p : TorsionParams) (t : ℝ) :
    deriv (deriv (motorCommon p)) t = 0 ∧ deriv (deriv (motorMismatch p)) t = 0 :=
  ⟨motorCommon_accel p t, motorMismatch_accel p t⟩

/-! ### The rotor uses the scaled torsion; the body rate does not -/

theorem omegaTorsion_scale (p : TorsionParams) (t : ℝ) :
    omegaTorsion (scaleTorsion t p) = t • omegaTorsion p := by
  simp only [omegaTorsion, scaleTorsion, Finset.smul_sum, smul_add, smul_smul, mul_div_assoc]

theorem rotor_accumulated (p : TorsionParams) (t : ℝ) :
    rotorTorsion (scaleTorsion t p) = exp (t • omegaTorsion p) := by
  rw [rotorTorsion, omegaTorsion_scale]

theorem motorPath_accumulated (p : OmegaParams) (t : ℝ) :
    motorPath p t =
      rotorTorsion (scaleTorsion t p.torsion) * (1 + t • omegaTrans p.trans) := by
  rw [motorPath_factor, rotor_accumulated]

/-- The torsion summand of the body velocity is the unscaled generator, at every parameter. -/
theorem advance_keeps_torsion (p : OmegaParams) (t : ℝ) :
    motorBodyVelocity p t - omegaTrans ⟨bodyTransCoefficient p t⟩ = omegaTorsion p.torsion := by
  rw [MotorForce.motorBodyVelocity_split, add_sub_cancel_right]

/-! ### Rebuilding a generator from the advance multiplies the force -/

theorem lorentzAct_scale (c : ℝ) (t : TorsionParams) (x : Vec4) :
    lorentzAct (scaleTorsion c t) x = fun μ => c * lorentzAct t x μ := by
  ext μ
  fin_cases μ <;> simp [lorentzAct, scaleTorsion] <;> ring

theorem lorentzAct_smul_vec (c : ℝ) (t : TorsionParams) (x : Vec4) :
    lorentzAct t (fun μ => c * x μ) = fun μ => c * lorentzAct t x μ := by
  ext μ
  fin_cases μ <;> simp [lorentzAct] <;> ring

theorem motorForce_scaledTorsion (p : OmegaParams) (t : ℝ) :
    motorForceCoefficient ⟨scaleTorsion t p.torsion, p.trans⟩ =
      fun μ => t * motorForceCoefficient p μ := by
  rw [motorForceCoefficient, motorForceCoefficient, lorentzAct_scale]

theorem motorForce_scaledState (p : OmegaParams) (t : ℝ) :
    motorForceCoefficient
        ⟨scaleTorsion t p.torsion, ⟨fun μ => t * p.trans.lambda μ⟩⟩ =
      fun μ => t ^ 2 * motorForceCoefficient p μ := by
  ext μ
  rw [motorForceCoefficient, motorForceCoefficient,
    congrFun (lorentzAct_scale t p.torsion (fun ν => t * p.trans.lambda ν)) μ,
    congrFun (lorentzAct_smul_vec t p.torsion p.trans.lambda) μ]
  ring

theorem boostShift_clock_not_generator :
    motorForceCoefficient ⟨scaleTorsion 2 boostShift.torsion, boostShift.trans⟩ =
        ![2, 0, 0, 0] ∧
      motorForceCoefficient
          ⟨scaleTorsion 2 boostShift.torsion, ⟨fun μ => 2 * boostShift.trans.lambda μ⟩⟩ =
        ![4, 0, 0, 0] ∧
        motorForceCoefficient boostShift = ![1, 0, 0, 0] ∧
          motorForceCoefficient ⟨scaleTorsion 2 boostShift.torsion, boostShift.trans⟩ ≠
            motorForceCoefficient boostShift ∧
            motorForceCoefficient
                ⟨scaleTorsion 2 boostShift.torsion,
                  ⟨fun μ => 2 * boostShift.trans.lambda μ⟩⟩ ≠
              motorForceCoefficient boostShift := by
  have htor : motorForceCoefficient ⟨scaleTorsion 2 boostShift.torsion, boostShift.trans⟩ =
      ![2, 0, 0, 0] := by
    rw [motorForce_scaledTorsion, boostShift_forceCoefficient]
    ext μ
    fin_cases μ <;> simp
  have hstate : motorForceCoefficient
      ⟨scaleTorsion 2 boostShift.torsion, ⟨fun μ => 2 * boostShift.trans.lambda μ⟩⟩ =
      ![4, 0, 0, 0] := by
    rw [motorForce_scaledState, boostShift_forceCoefficient]
    ext μ
    fin_cases μ
    · simp
      norm_num
    · simp
    · simp
    · simp
  refine ⟨htor, hstate, boostShift_forceCoefficient, ?_, ?_⟩
  · rw [htor, boostShift_forceCoefficient]
    intro h
    have := congrFun h 0
    simp at this
  · rw [hstate, boostShift_forceCoefficient]
    intro h
    have := congrFun h 0
    simp at this

/-! ### The written cubic is not this advance -/

theorem boostShift_channels (t : ℝ) :
    motorCommon boostShift.torsion t = t ∧ motorMismatch boostShift.torsion t = t := by
  constructor
  · rw [motorCommon_linear, axisCommon]
    simp [boostShift, pureBoost]
  · rw [motorMismatch_linear, axisMismatch]
    simp [boostShift, pureBoost]

theorem boostShift_advance_ne_written :
    motorCommon boostShift.torsion 1 = 1 ∧
      motorMismatch boostShift.torsion 1 = 1 ∧
        motorCommon boostShift.torsion 1 ≠ writtenSigma 0 1 1 0 1 1 ∧
          deriv (deriv (motorCommon boostShift.torsion)) 1 = 0 ∧
            deriv (deriv (writtenSigma 0 1 1 0 1)) 1 = -2 := by
  have hch := boostShift_channels 1
  refine ⟨hch.1, hch.2, ?_, motorCommon_accel _ 1, ?_⟩
  · rw [hch.1, writtenSigma, cubicRapidity]
    norm_num
  · rw [deriv2_writtenSigma, writtenDelta, affineMismatch]
    ring

private theorem affine_accel_ne_zero {m δ₀ ν : ℝ} (hm : m ≠ 0)
    (h : δ₀ ≠ 0 ∨ ν ≠ 0) :
    ∃ t, -2 * m * affineMismatch δ₀ ν t ≠ 0 := by
  rcases h with hδ | hν
  · refine ⟨0, ?_⟩
    simp only [affineMismatch, mul_zero, add_zero]
    exact mul_ne_zero (mul_ne_zero (by norm_num : (-2 : ℝ) ≠ 0) hm) hδ
  · by_cases hδ : δ₀ = 0
    · refine ⟨1, ?_⟩
      simp only [affineMismatch, hδ, zero_add, mul_one]
      exact mul_ne_zero (mul_ne_zero (by norm_num : (-2 : ℝ) ≠ 0) hm) hν
    · refine ⟨0, ?_⟩
      simp only [affineMismatch, mul_zero, add_zero]
      exact mul_ne_zero (mul_ne_zero (by norm_num : (-2 : ℝ) ≠ 0) hm) hδ

/-- A nonzero lag makes the written common acceleration leave the motor. -/
theorem written_common_ne_motor {m δ₀ ν : ℝ} (p : TorsionParams) (hm : m ≠ 0)
    (h : δ₀ ≠ 0 ∨ ν ≠ 0) :
    ∃ t, deriv (deriv (writtenSigma 0 0 m δ₀ ν)) t ≠ deriv (deriv (motorCommon p)) t := by
  obtain ⟨t, ht⟩ := affine_accel_ne_zero hm h
  refine ⟨t, ?_⟩
  rw [deriv2_writtenSigma, motorCommon_accel, writtenDelta]
  exact ht

/-- The free mismatch is the part the written flow and the motor share. -/
theorem mismatch_accel_agrees (p : TorsionParams) (δ₀ ν t : ℝ) :
    deriv (deriv (motorMismatch p)) t = deriv (deriv (writtenDelta δ₀ ν)) t := by
  rw [motorMismatch_accel, deriv2_writtenDelta]

/-! ### Oscillator and runaway accelerate the other channel -/

/-- The same-sign model and the runaway keep the common rapidity inertial, as the motor does. -/
theorem inertial_common_matches_motor (p : TorsionParams) (σ₀ σd₀ t : ℝ) :
    deriv (deriv (inertialRapidity σ₀ σd₀)) t = deriv (deriv (motorCommon p)) t := by
  rw [deriv2_inertialRapidity, motorCommon_accel]

theorem harmonic_accel_ne_motor {A B ω : ℝ} (p : TorsionParams) (hω : ω ≠ 0)
    (hAB : A ≠ 0 ∨ B ≠ 0) :
    ∃ t, deriv (deriv (harmonicMismatch A B ω)) t ≠ deriv (deriv (motorMismatch p)) t := by
  have hz : ∀ s, deriv (deriv (motorMismatch p)) s = 0 := motorMismatch_accel p
  rcases hAB with hA | hB
  · refine ⟨0, ?_⟩
    rw [hz, deriv2_harmonicMismatch]
    simp only [harmonicMismatch, Real.sin_zero, Real.cos_zero, mul_zero, mul_one, add_zero]
    exact mul_ne_zero (neg_ne_zero.mpr (pow_ne_zero 2 hω)) hA
  · by_cases hA : A = 0
    · refine ⟨Real.pi / (2 * ω), ?_⟩
      rw [hz, deriv2_harmonicMismatch]
      have harg : ω * (Real.pi / (2 * ω)) = Real.pi / 2 := by
        field_simp [hω]
      rw [harmonicMismatch, harg, hA, Real.sin_pi_div_two, Real.cos_pi_div_two]
      have : -(ω ^ 2) * (0 * 0 + B * 1) = -(ω ^ 2) * B := by ring
      rw [this]
      exact mul_ne_zero (neg_ne_zero.mpr (pow_ne_zero 2 hω)) hB
    · refine ⟨0, ?_⟩
      rw [hz, deriv2_harmonicMismatch]
      simp only [harmonicMismatch, Real.sin_zero, Real.cos_zero, mul_zero, mul_one, add_zero]
      exact mul_ne_zero (neg_ne_zero.mpr (pow_ne_zero 2 hω)) hA

theorem hyperbolic_accel_ne_motor {A B κ : ℝ} (p : TorsionParams) (hκ : κ ≠ 0)
    (hAB : A ≠ 0 ∨ B ≠ 0) :
    ∃ t, deriv (deriv (hyperbolicMismatch A B κ)) t ≠
      deriv (deriv (motorMismatch p)) t := by
  have hz : ∀ s, deriv (deriv (motorMismatch p)) s = 0 := motorMismatch_accel p
  rcases hAB with hA | hB
  · refine ⟨0, ?_⟩
    rw [hz, deriv2_hyperbolicMismatch]
    simp only [hyperbolicMismatch, Real.sinh_zero, Real.cosh_zero, mul_zero, mul_one, add_zero]
    exact mul_ne_zero (pow_ne_zero 2 hκ) hA
  · by_cases hA : A = 0
    · refine ⟨1, ?_⟩
      rw [hz, deriv2_hyperbolicMismatch, hyperbolicMismatch, hA]
      simp only [mul_one]
      have : κ ^ 2 * (0 * Real.cosh κ + B * Real.sinh κ) = κ ^ 2 * (B * Real.sinh κ) := by
        ring
      rw [this]
      have hsinh : Real.sinh κ ≠ 0 := by
        intro hzero
        exact hκ (Real.sinh_eq_zero.mp hzero)
      exact mul_ne_zero (pow_ne_zero 2 hκ) (mul_ne_zero hB hsinh)
    · refine ⟨0, ?_⟩
      rw [hz, deriv2_hyperbolicMismatch]
      simp only [hyperbolicMismatch, Real.sinh_zero, Real.cosh_zero, mul_zero, mul_one, add_zero]
      exact mul_ne_zero (pow_ne_zero 2 hκ) hA

end DoubleSpacetime.Gravity.MotorAdvance
