import DoubleSpacetime.Gravity.LayerForce
import DoubleSpacetime.Gravity.RelationalMotor

/-!
# Position, momentum, and the repulsive layer

Space between two particles on one torsion is the relative motor. The translator that remains is
the separation coefficient. It is not an areal radius. The momentum is the body velocity, the
translator of the velocity difference. That momentum does not depend on the flow parameter, so the
separation accelerates by zero.

The chart term `gravityLayerTerm` reads an input length `ℓ` against that coefficient. On the
sample below the coefficient is `2t`. With `ℓ = 4` the phase is `1/t`. At `t = 1` the phase sits
on the repulsive side of the first node, and at `t = 2` it sits on the attractive side. The
relational momentum has Minkowski square `4` at both parameters. The difference of the body
momenta against the unit adds the commutator of the cancelled torsion with the relative velocity.
That commutator is a time translation: its spatial coefficient is zero, while the chart term at
the repulsive sample is positive.

The repulsive layer remains the sign of `γ_s` on the equal-scale locus. The chart may be fed the
separation coefficient, and that reading is not the motor acceleration. On a torsion star the same
sign is read at an areal radius. Two comoving particles on the shared one-axis freeze have a
translator that is not the gap of those radii, and their body velocity is zero. Distinct admissible
boosts, one on each shell, leave a rotor. That rotor is not a translator, and its mismatch does not
have the sign of `γ_s`. No angular momentum is assigned, no shell mass is fixed, and `ℓ` stays an
input.
-/

namespace DoubleSpacetime.Gravity.RepulsionMomentum

open CliffordAlgebra
open PGA Generators Operations Motor Amplification
open RelationalMotor MotorForce
open Sandwich Admissible Invariant
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

/-! ### A torsion star reads the areal radius -/

/-- Inner sample shell. With `sampleLength = 4` the phase is `1`. -/
def innerShell : ℝ := 2

/-- Outer sample shell. With `sampleLength = 4` the phase is `1/2`. -/
def outerShell : ℝ := 4

private theorem null01_ne_zero : null 0 + null 1 ≠ 0 := by
  intro h
  let l : Fin 4 → ℝ := fun μ =>
    match μ with
    | 0 => 1
    | 1 => 1
    | _ => 0
  have hsum : ∑ μ : Fin 4, l μ • null μ = 0 := by
    rw [Fin.sum_univ_four]
    simpa [l] using h
  have hli := Fintype.linearIndependent_iff.mp BivectorBasis.linearIndependent_null l hsum
  have : (1 : ℝ) = 0 := by simpa [l] using hli 0
  norm_num at this

private theorem sandwich_translator_on_null01 (p : TransParams) :
    sandwich (1 + omegaTrans p) (null 0 + null 1) = null 0 + null 1 := by
  have hv : null 0 + null 1 ∈ nullSpan :=
    add_mem (mem_nullSpan 0) (mem_nullSpan 1)
  have hT : omegaTrans p ∈ nullSpan := omegaTrans_mem_nullSpan p
  have hTv : omegaTrans p * (null 0 + null 1) = 0 := nullSpan_mul hT hv
  have hvT : (null 0 + null 1) * omegaTrans p = 0 := nullSpan_mul hv hT
  have hrev : reverse (1 + omegaTrans p) = 1 - omegaTrans p := by
    rw [CliffordAlgebra.reverse.map_add, CliffordAlgebra.reverse.map_one, reverse_omegaTrans,
      sub_eq_add_neg]
  rw [sandwich, hrev]
  calc
    (1 + omegaTrans p) * (null 0 + null 1) * (1 - omegaTrans p)
        = (1 + omegaTrans p) * ((null 0 + null 1) * (1 - omegaTrans p)) := by rw [mul_assoc]
    _ = (1 + omegaTrans p) * ((null 0 + null 1) - (null 0 + null 1) * omegaTrans p) := by
          rw [mul_sub, mul_one]
    _ = (1 + omegaTrans p) * (null 0 + null 1) := by rw [hvT, sub_zero]
    _ = null 0 + null 1 + omegaTrans p * (null 0 + null 1) := by rw [add_mul, one_mul]
    _ = null 0 + null 1 := by rw [hTv, add_zero]

/-- A positive boost rotor scales `N₀ + N₁`. A pure translator does not, so the rotor is not one. -/
private theorem rotor_ne_translator {φ : ℝ} (hφ : 0 < φ) (p : TransParams) :
    rotorTorsion (pureBoost φ) ≠ 1 + omegaTrans p := by
  intro h
  have hs := sandwich_pureBoost_null_plus φ
  rw [h, sandwich_translator_on_null01] at hs
  have hzero : (Real.exp φ - 1) • (null 0 + null 1) = 0 := by
    rw [sub_smul, one_smul]
    exact sub_eq_zero.mpr hs.symm
  have hexp : Real.exp φ ≠ 1 := by
    intro he
    have hgt : Real.exp 0 < Real.exp φ := Real.exp_strictMono hφ
    rw [Real.exp_zero, he] at hgt
    exact lt_irrefl (1 : ℝ) hgt
  have hc0 : Real.exp φ - 1 ≠ 0 := sub_ne_zero.mpr hexp
  have hv0 : null 0 + null 1 = 0 := by
    calc
      null 0 + null 1 = (Real.exp φ - 1)⁻¹ • ((Real.exp φ - 1) • (null 0 + null 1)) := by
        rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]
      _ = (Real.exp φ - 1)⁻¹ • 0 := by rw [hzero]
      _ = 0 := smul_zero _
  exact null01_ne_zero hv0

theorem shell_phase_inner : sampleLength / (2 * innerShell) = 1 := by
  unfold sampleLength innerShell
  norm_num

theorem shell_phase_outer : sampleLength / (2 * outerShell) = 1 / 2 := by
  unfold sampleLength outerShell
  norm_num

theorem inner_phase_repulsive : (1 : ℝ) ∈ Ioo resonanceRoot1 π := by
  refine ⟨resonanceRoot1_sharp_bounds.2, ?_⟩
  linarith [pi_gt_three]

theorem outer_phase_attractive : (1 / 2 : ℝ) ∈ Ioo 0 resonanceRoot1 := by
  refine ⟨by norm_num, ?_⟩
  have hhalf : (1 / 2 : ℝ) < π / 4 := by linarith [pi_gt_three]
  exact lt_trans hhalf resonanceRoot1_sharp_bounds.1

theorem inner_gamma_neg : gammaSEqual (sampleLength / (2 * innerShell)) < 0 := by
  rw [shell_phase_inner]
  exact gammaSEqual_neg_right_of_first_node inner_phase_repulsive

theorem outer_gamma_pos : 0 < gammaSEqual (sampleLength / (2 * outerShell)) := by
  rw [shell_phase_outer]
  exact gammaSEqual_pos_left_of_first_node outer_phase_attractive

theorem inner_chart_pos : 0 < gravityLayerTerm 1 sampleLength innerShell :=
  gravityLayerTerm_pos_of_repulsive (by norm_num) (by unfold innerShell; norm_num) inner_gamma_neg

theorem outer_chart_neg : gravityLayerTerm 1 sampleLength outerShell < 0 :=
  gravityLayerTerm_neg_of_attractive (by norm_num) (by unfold outerShell; norm_num) outer_gamma_pos

/-- Both shell boosts lie on the one-axis admissible cone. The inner boost is the ceiling. -/
theorem shell_boosts_admissible :
    Discrete.IsAdmissibleContinuous (pureBoost (Real.pi / 2)) ∧
      Discrete.IsAdmissibleContinuous (pureBoost (Real.pi / 4)) := by
  constructor
  · rw [isAdmissibleContinuous_pureBoost_iff]
    exact ⟨by positivity, le_refl _⟩
  · rw [isAdmissibleContinuous_pureBoost_iff]
    exact ⟨by positivity, by linarith [Real.pi_pos]⟩

theorem comoving_component (t : ℝ) :
    separationCoefficient zeroTrans (along1 1) zeroTrans zeroTrans t 1 = 1 := by
  have hΔ : (along1 1).lambda 1 - zeroTrans.lambda 1 = 1 := by
    norm_num [along1, zeroTrans]
  simp only [separationCoefficient, hΔ]
  ring

theorem comoving_translator_ne_gap (t : ℝ) :
    separationCoefficient zeroTrans (along1 1) zeroTrans zeroTrans t 1 ≠
      outerShell - innerShell := by
  rw [comoving_component]
  unfold outerShell innerShell
  norm_num

/-- On the shared freeze the rotors cancel. The translator is the placement, not the areal gap. -/
theorem freeze_pair_motor (t : ℝ) :
    between (placedPath ⟨pureBoost (Real.pi / 2), zeroTrans⟩ zeroTrans t)
        (placedPath ⟨pureBoost (Real.pi / 2), zeroTrans⟩ (along1 1) t) =
      1 + omegaTrans (along1 1) := by
  rw [between_shared]
  refine congrArg (fun z => (1 : PGA) + z) ?_
  apply omegaTrans_eq_of_lambda
  intro μ
  have h := congrFun
    (separation_fixed_of_shared_velocity zeroTrans (along1 1) zeroTrans t) μ
  simpa [zeroTrans, along1] using h

/-- Comoving particles on the freeze. The body velocity of the space between them is zero. -/
theorem freeze_pair_body (t : ℝ) :
    reverse (between (placedPath ⟨pureBoost (Real.pi / 2), zeroTrans⟩ zeroTrans t)
          (placedPath ⟨pureBoost (Real.pi / 2), zeroTrans⟩ (along1 1) t)) *
        deriv (fun s => between (placedPath ⟨pureBoost (Real.pi / 2), zeroTrans⟩ zeroTrans s)
          (placedPath ⟨pureBoost (Real.pi / 2), zeroTrans⟩ (along1 1) s)) t = 0 := by
  rw [sharedSpace_body, ← omegaTrans_zero]
  apply omegaTrans_eq_of_lambda
  intro μ
  simp [zeroTrans]

theorem translator_phase (t : ℝ) :
    sampleLength / (2 * separationCoefficient zeroTrans (along1 1) zeroTrans zeroTrans t 1) =
      2 := by
  rw [comoving_component]
  unfold sampleLength
  norm_num

theorem translator_phase_repulsive (t : ℝ) :
    separationCoefficient zeroTrans (along1 1) zeroTrans zeroTrans t 1 ≠ 0 ∧
      sampleLength / (2 * separationCoefficient zeroTrans (along1 1) zeroTrans zeroTrans t 1) ∈
        Ioo resonanceRoot1 π := by
  refine ⟨by rw [comoving_component]; norm_num, ?_⟩
  rw [translator_phase]
  refine ⟨lt_trans resonanceRoot1_sharp_bounds.2 (by norm_num), ?_⟩
  linarith [pi_gt_three]

/-- The chart read of the translator coefficient is positive. The outer shell's term is negative. -/
theorem translator_chart_ne_outer (t : ℝ) :
    0 < gravityLayerTerm 1 sampleLength
        (separationCoefficient zeroTrans (along1 1) zeroTrans zeroTrans t 1) ∧
      gravityLayerTerm 1 sampleLength outerShell < 0 := by
  have hcomp := comoving_component t
  have hphase := (translator_phase_repulsive t).2
  rw [translator_phase t] at hphase
  have hγ : gammaSEqual (sampleLength / (2 *
      separationCoefficient zeroTrans (along1 1) zeroTrans zeroTrans t 1)) < 0 := by
    rw [translator_phase]
    exact gammaSEqual_neg_right_of_first_node hphase
  have hr : 0 < separationCoefficient zeroTrans (along1 1) zeroTrans zeroTrans t 1 := by
    rw [hcomp]
    norm_num
  exact ⟨gravityLayerTerm_pos_of_repulsive (by norm_num) hr hγ, outer_chart_neg⟩

/-- Shell boosts `π/4` and `π/2`. The motor between them is the rotor of the rapidity difference. -/
theorem between_shell_boosts (t : ℝ) :
    between (placedPath ⟨pureBoost (Real.pi / 4), zeroTrans⟩ zeroTrans t)
        (placedPath ⟨pureBoost (Real.pi / 2), zeroTrans⟩ zeroTrans t) =
      rotorTorsion (pureBoost (t * (Real.pi / 4))) := by
  rw [placed_pureBoost, placed_pureBoost, between, reverse_rotorTorsion_pureBoost_eq,
    rotorTorsion_pureBoost_mul]
  have hsum : -(t * (Real.pi / 4)) + t * (Real.pi / 2) = t * (Real.pi / 4) := by ring
  rw [hsum]

theorem shell_motor_not_translator (p : TransParams) :
    between (placedPath ⟨pureBoost (Real.pi / 4), zeroTrans⟩ zeroTrans 1)
        (placedPath ⟨pureBoost (Real.pi / 2), zeroTrans⟩ zeroTrans 1) ≠
      1 + omegaTrans p := by
  rw [between_shell_boosts]
  have hscale : (1 : ℝ) * (Real.pi / 4) = Real.pi / 4 := by ring
  rw [hscale]
  exact rotor_ne_translator (by positivity) p

theorem relative_mismatch : J (pureBoost (Real.pi / 4)) = Real.pi ^ 2 / 32 := by
  rw [J_pureBoost]
  ring

theorem mismatch_gap :
    J (pureBoost (Real.pi / 2)) - J (pureBoost (Real.pi / 4)) = 3 * Real.pi ^ 2 / 32 := by
  rw [J_pureBoost, J_pureBoost]
  ring

theorem relative_mismatch_ne_gap :
    J (pureBoost (Real.pi / 4)) ≠
      J (pureBoost (Real.pi / 2)) - J (pureBoost (Real.pi / 4)) := by
  rw [mismatch_gap, relative_mismatch]
  exact ne_of_lt (by
    have hπ : (0 : ℝ) < Real.pi ^ 2 := by positivity
    linarith)

theorem inner_gamma_ne_relative_mismatch :
    gammaSEqual (sampleLength / (2 * innerShell)) ≠ J (pureBoost (Real.pi / 4)) := by
  refine ne_of_lt ?_
  rw [relative_mismatch]
  have hJ : 0 < Real.pi ^ 2 / 32 := by positivity
  exact lt_trans inner_gamma_neg hJ

/-- Two shells of a torsion star. The chart term is positive on the inner radius and negative on
the outer radius. Both boosts are admissible. Particles that share the freeze and the velocity
keep a translator of coefficient `1`, not the areal gap `2`, and the body velocity is zero.
Reading the chart on that coefficient stays positive, so it is not the outer shell. Distinct
boosts leave a rotor, not the translator of the areal gap. The mismatch of the rotor is not the
difference of the shell mismatches, and it does not equal `γ_s` on the inner shell.
-/
theorem torsionStar_repulsive_layer :
    sampleLength / (2 * innerShell) = 1 ∧
      sampleLength / (2 * outerShell) = 1 / 2 ∧
        gammaSEqual (sampleLength / (2 * innerShell)) < 0 ∧
          0 < gammaSEqual (sampleLength / (2 * outerShell)) ∧
            0 < gravityLayerTerm 1 sampleLength innerShell ∧
              gravityLayerTerm 1 sampleLength outerShell < 0 ∧
                Discrete.IsAdmissibleContinuous (pureBoost (Real.pi / 2)) ∧
                  Discrete.IsAdmissibleContinuous (pureBoost (Real.pi / 4)) ∧
                    separationCoefficient zeroTrans (along1 1) zeroTrans zeroTrans 1 1 ≠
                      outerShell - innerShell ∧
                      reverse (between
                            (placedPath ⟨pureBoost (Real.pi / 2), zeroTrans⟩ zeroTrans 1)
                            (placedPath ⟨pureBoost (Real.pi / 2), zeroTrans⟩ (along1 1) 1)) *
                          deriv (fun s => between
                            (placedPath ⟨pureBoost (Real.pi / 2), zeroTrans⟩ zeroTrans s)
                            (placedPath ⟨pureBoost (Real.pi / 2), zeroTrans⟩ (along1 1) s)) 1 =
                        0 ∧
                        0 < gravityLayerTerm 1 sampleLength
                            (separationCoefficient zeroTrans (along1 1) zeroTrans zeroTrans 1 1) ∧
                          gravityLayerTerm 1 sampleLength outerShell < 0 ∧
                            between
                                (placedPath ⟨pureBoost (Real.pi / 4), zeroTrans⟩ zeroTrans 1)
                                (placedPath ⟨pureBoost (Real.pi / 2), zeroTrans⟩ zeroTrans 1) ≠
                              1 + omegaTrans (along1 (outerShell - innerShell)) ∧
                              J (pureBoost (Real.pi / 4)) ≠
                                J (pureBoost (Real.pi / 2)) - J (pureBoost (Real.pi / 4)) ∧
                                gammaSEqual (sampleLength / (2 * innerShell)) ≠
                                  J (pureBoost (Real.pi / 4)) :=
  ⟨shell_phase_inner, shell_phase_outer, inner_gamma_neg, outer_gamma_pos, inner_chart_pos,
    outer_chart_neg, shell_boosts_admissible.1, shell_boosts_admissible.2,
    comoving_translator_ne_gap 1, freeze_pair_body 1, (translator_chart_ne_outer 1).1,
    (translator_chart_ne_outer 1).2,
    shell_motor_not_translator (along1 (outerShell - innerShell)), relative_mismatch_ne_gap,
    inner_gamma_ne_relative_mismatch⟩

end DoubleSpacetime.Gravity.RepulsionMomentum
