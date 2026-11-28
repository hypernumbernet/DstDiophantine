import DoubleSpacetime.Gravity.LayerForce
import DoubleSpacetime.Gravity.RelationalMotor

/-!
# Position, momentum, and the repulsive layer

Space between two particles on one torsion is the relative motor. Its position is the separation
coefficient, and its momentum is the body velocity, the translator of the velocity difference.
That momentum does not depend on the flow parameter, so the separation accelerates by zero.

The chart term `gravityLayerTerm` reads an input length `ℓ` against that coefficient. On the
sample below the coefficient is `2t`. With `ℓ = 4` the phase is `1/t`. At `t = 1` the phase sits
on the repulsive side of the first node, and at `t = 2` it sits on the attractive side. The
relational momentum has Minkowski square `4` at both parameters. The difference of the body
momenta against the unit adds the commutator of the cancelled torsion with the relative velocity.
That commutator is a time translation: its spatial coefficient is zero, while the chart term at
the repulsive sample is positive.

The repulsive layer remains the sign of `γ_s` on the equal-scale locus. It is the chart reading
of the separation coefficient. The motor does not accelerate that coefficient, and no angular
momentum is assigned. `ℓ` stays an input.
-/

namespace DoubleSpacetime.Gravity.RepulsionMomentum

open CliffordAlgebra
open PGA Generators Operations Motor Amplification
open RelationalMotor MotorForce
open Real Set

/-- Input length for the sample. The phase of coefficient `2t` is `1/t`. -/
def sampleLength : ℝ := 4

/-- Translational coefficient of the witness momentum difference for speeds `1` and `3`. -/
def witnessMomentum (t : ℝ) : Vec4 :=
  fun μ =>
    (separationVelocity (along1 1) (along1 3)).lambda μ +
      t * motorForceCoefficient ⟨pureBoost 1, separationVelocity (along1 1) (along1 3)⟩ μ

theorem sample_velocity :
    (separationVelocity (along1 1) (along1 3)).lambda = (along1 2).lambda := by
  ext μ
  fin_cases μ
  · simp [separationVelocity, along1]
  · norm_num [separationVelocity, along1]
  · simp [separationVelocity, along1]
  · simp [separationVelocity, along1]

theorem sample_force :
    motorForceCoefficient ⟨pureBoost 1, separationVelocity (along1 1) (along1 3)⟩ =
      ![2, 0, 0, 0] := by
  rw [motorForceCoefficient, sample_velocity]
  exact boostVelocity_force 2

theorem sample_position (t : ℝ) :
    separationCoefficient zeroTrans zeroTrans (along1 1) (along1 3) t 1 = 2 * t := by
  have hΔ : (along1 3).lambda 1 - (along1 1).lambda 1 = 2 := by
    norm_num [along1]
  simp only [separationCoefficient, zeroTrans, hΔ]
  ring

theorem sample_phase (t : ℝ) (ht : t ≠ 0) :
    sampleLength / (2 * separationCoefficient zeroTrans zeroTrans (along1 1) (along1 3) t 1) =
      1 / t := by
  rw [sample_position]
  unfold sampleLength
  field_simp [ht]
  ring

theorem witnessMomentum_coord (t : ℝ) : witnessMomentum t = ![2 * t, 2, 0, 0] := by
  ext μ
  unfold witnessMomentum
  rw [sample_force, sample_velocity]
  fin_cases μ
  all_goals
    simp [along1, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three]
  ring

theorem pairMomentum_square :
    Q31 (separationVelocity (along1 1) (along1 3)).lambda = 4 := by
  rw [sample_velocity, Q31_eq_minkowskiDot, minkowskiDot]
  simp [along1]
  norm_num

theorem witnessMomentum_square (t : ℝ) :
    Q31 (witnessMomentum t) = 4 - 4 * t ^ 2 := by
  rw [witnessMomentum_coord, Q31_eq_minkowskiDot, minkowskiDot]
  simp
  ring

theorem witnessMomentum_eq_body (t : ℝ) :
    motorBodyVelocity ⟨pureBoost 1, along1 3⟩ t -
        motorBodyVelocity ⟨pureBoost 1, along1 1⟩ t =
      omegaTrans ⟨witnessMomentum t⟩ := by
  rw [witness_body_difference]
  rw [show commutator (omegaTorsion (pureBoost 1))
        (omegaTrans (separationVelocity (along1 1) (along1 3))) =
      motorForceBivector ⟨pureBoost 1, separationVelocity (along1 1) (along1 3)⟩ from rfl]
  rw [motorForceBivector_eq, omegaTrans_smul_lambda, omegaTrans_add]
  exact omegaTrans_eq_of_lambda fun _ => rfl

/-- Speeds `1` and `3` on one boost, released from the unit. The separation coefficient is `2`
at parameter `1` and `4` at parameter `2`. With `ℓ = 4` those coefficients are the phases `1`
and `1/2`. The first phase is repulsive and the second is attractive, so the chart term changes
sign. The relational momentum keeps square `4`, and its derivative vanishes at both parameters.
The separation coefficient accelerates by zero. The witness momentum difference is the body
difference. Its square is `0` on the repulsive sample and `-12` on the attractive sample. The
spatial coefficient of that difference's derivative is `0`, and the chart term on the repulsive
sample is a different number.
-/
theorem pair_momentum_across_chart_layer :
    separationCoefficient zeroTrans zeroTrans (along1 1) (along1 3) 1 1 = 2 ∧
      separationCoefficient zeroTrans zeroTrans (along1 1) (along1 3) 2 1 = 4 ∧
        sampleLength / (2 * separationCoefficient zeroTrans zeroTrans (along1 1) (along1 3) 1 1) =
          1 ∧
          sampleLength /
              (2 * separationCoefficient zeroTrans zeroTrans (along1 1) (along1 3) 2 1) =
            1 / 2 ∧
            gammaSEqual 1 < 0 ∧
              0 < gammaSEqual (1 / 2) ∧
                0 < gravityLayerTerm 1 sampleLength 2 ∧
                  gravityLayerTerm 1 sampleLength 4 < 0 ∧
                    Q31 (separationVelocity (along1 1) (along1 3)).lambda = 4 ∧
                      deriv (fun _ : ℝ =>
                          omegaTrans (separationVelocity (along1 1) (along1 3))) 1 = 0 ∧
                        deriv (fun _ : ℝ =>
                            omegaTrans (separationVelocity (along1 1) (along1 3))) 2 = 0 ∧
                          deriv (deriv (fun s => separationCoefficient zeroTrans zeroTrans
                            (along1 1) (along1 3) s 1)) 1 = 0 ∧
                            deriv (deriv (fun s => separationCoefficient zeroTrans zeroTrans
                              (along1 1) (along1 3) s 1)) 2 = 0 ∧
                              motorBodyVelocity ⟨pureBoost 1, along1 3⟩ 1 -
                                  motorBodyVelocity ⟨pureBoost 1, along1 1⟩ 1 =
                                omegaTrans ⟨witnessMomentum 1⟩ ∧
                                Q31 (witnessMomentum 1) = 0 ∧
                                  Q31 (witnessMomentum 2) = -12 ∧
                                    motorForceCoefficient ⟨pureBoost 1,
                                        separationVelocity (along1 1) (along1 3)⟩ 1 = 0 ∧
                                      gravityLayerTerm 1 sampleLength 2 ≠
                                        motorForceCoefficient ⟨pureBoost 1,
                                          separationVelocity (along1 1) (along1 3)⟩ 1 := by
  have hpos1 : separationCoefficient zeroTrans zeroTrans (along1 1) (along1 3) 1 1 = 2 := by
    simpa using sample_position 1
  have hpos2 : separationCoefficient zeroTrans zeroTrans (along1 1) (along1 3) 2 1 = 4 := by
    rw [sample_position]
    norm_num
  have hphase1 :
      sampleLength / (2 * separationCoefficient zeroTrans zeroTrans (along1 1) (along1 3) 1 1) =
        1 := by
    rw [sample_phase 1 one_ne_zero]
    norm_num
  have hphase2 :
      sampleLength / (2 * separationCoefficient zeroTrans zeroTrans (along1 1) (along1 3) 2 1) =
        1 / 2 := by
    rw [sample_phase 2 (by norm_num)]
  have hrepulsive_phase : (1 : ℝ) ∈ Ioo resonanceRoot1 π := by
    refine ⟨resonanceRoot1_sharp_bounds.2, ?_⟩
    linarith [pi_gt_three]
  have hattractive_phase : (1 / 2 : ℝ) ∈ Ioo 0 resonanceRoot1 := by
    refine ⟨by norm_num, ?_⟩
    have hhalf : (1 / 2 : ℝ) < π / 4 := by linarith [pi_gt_three]
    exact lt_trans hhalf resonanceRoot1_sharp_bounds.1
  have hread1 : sampleLength / (2 * 2) = 1 := by
    unfold sampleLength
    norm_num
  have hread2 : sampleLength / (2 * 4) = 1 / 2 := by
    unfold sampleLength
    norm_num
  have hγ1 : gammaSEqual (sampleLength / (2 * 2)) < 0 := by
    rw [hread1]
    exact gammaSEqual_neg_right_of_first_node hrepulsive_phase
  have hγ2 : 0 < gammaSEqual (sampleLength / (2 * 4)) := by
    rw [hread2]
    exact gammaSEqual_pos_left_of_first_node hattractive_phase
  have hpush : 0 < gravityLayerTerm 1 sampleLength 2 :=
    gravityLayerTerm_pos_of_repulsive (by norm_num) (by norm_num) hγ1
  have hpull : gravityLayerTerm 1 sampleLength 4 < 0 :=
    gravityLayerTerm_neg_of_attractive (by norm_num) (by norm_num) hγ2
  have hspatial : motorForceCoefficient
      ⟨pureBoost 1, separationVelocity (along1 1) (along1 3)⟩ 1 = 0 := by
    rw [sample_force]
    simp
  refine ⟨hpos1, hpos2, hphase1, hphase2,
    gammaSEqual_neg_right_of_first_node hrepulsive_phase,
    gammaSEqual_pos_left_of_first_node hattractive_phase, hpush, hpull, pairMomentum_square,
    sharedSpace_body_accel (along1 1) (along1 3) 1,
    sharedSpace_body_accel (along1 1) (along1 3) 2,
    separationCoefficient_accel zeroTrans zeroTrans (along1 1) (along1 3) 1 1,
    separationCoefficient_accel zeroTrans zeroTrans (along1 1) (along1 3) 1 2,
    witnessMomentum_eq_body 1, ?_, ?_, hspatial, ?_⟩
  · rw [witnessMomentum_square]
    norm_num
  · rw [witnessMomentum_square]
    norm_num
  · rw [hspatial]
    exact hpush.ne'

end DoubleSpacetime.Gravity.RepulsionMomentum
