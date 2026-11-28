import DoubleSpacetime.Algebra.RelativeRotor
import DoubleSpacetime.Gravity.TorsionalLayer
import DoubleSpacetime.Logic.Quantum.PositionLaw

/-!
# The equal-scale shell is a rotor, and the packet reads the translator

An electron shell in DST is the equal-scale node `gammaSEqual x = 0`, that is
`tanh x · tan x = 1`. On one axis that node is a torsion rotor with equal usual
and dual rapidities, so `J = 0` and the unsigned mass is the square of the
rapidity. The length `ℓ` is not derived, and the node is not a Bohr radius.

A motor is that rotor times a null translator. The mass-3 mean-rest packet has
relative momentum on axis `1`, the same axis as the shell. It reads a translator
through the Euclidean sum, which on this packet is `-8` times the `N₁` coefficient.

The dual factor of the shell is a rotation in the `(N₂, N₃)` plane. It fixes `N₀`
and `N₁`, so it does not change the positional scalar of any translator. The usual
factor is the boost in the `(N₀, N₁)` plane. It does. The full equal-scale motor
is the boost after that rotation, and the positional scalar is the boost's scalar:
the dual angle, including the angle the node sets equal to the usual rapidity, does
not enter.

Vanishing `J` is not agreement of the two sectors on position. At the first node
the rapidity `α = 2 x₁` is nonzero. The unit `N₁` translator is read as `-8` by
the dual factor and as `-8 cosh α` by the usual factor and by the shell motor.
A pure time translator is unread, scalar `0`, and the shell motor reads it as
`-8 sinh α`. Neither scalar is the node, and neither is a coordinate of the chart.
-/

namespace DoubleSpacetime

namespace Logic

open Motor Amplification Invariant Operations Real Sandwich Gravity RelativeRotor

/-! ### The first equal-scale node, as one axis -/

/-- Rapidity of the first equal-scale node: both sectors carry `2 x₁`. -/
noncomputable def shellRapidity : ℝ :=
  2 * resonanceRoot1

theorem shellRapidity_bounds :
    π / 2 < shellRapidity ∧ shellRapidity < 2 := by
  unfold shellRapidity
  have h := resonanceRoot1_sharp_bounds
  constructor
  · linarith
  · linarith

theorem shellRapidity_pos : 0 < shellRapidity :=
  lt_trans (div_pos pi_pos (by norm_num : (0 : ℝ) < 2)) shellRapidity_bounds.1

theorem shellNode_rotor :
    gammaSEqual resonanceRoot1 = 0 ∧
      J (axisParams shellRapidity shellRapidity) = 0 ∧
        mass (axisParams shellRapidity shellRapidity) = shellRapidity ^ 2 ∧
          shellRapidity ≠ 0 := by
  refine ⟨resonanceRoot1_gammaSEqual_zero, J_axisParams_balanced _, ?_, shellRapidity_pos.ne'⟩
  · rw [mass_axisParams]
    ring

/-! ### What the mean-rest packet can see -/

theorem shellRest_phase_coord (v : Vec4) :
    wavePhase (shellRestQ - shellRestP) v = -8 * v 1 := by
  rw [wavePhase_expand]
  have h := shellRest_relative
  rw [h.1, h.2.1, h.2.2.1, h.2.2.2]
  ring

theorem boostConjLambda_coord1 (φ : ℝ) (lam : Vec4) :
    boostConjLambda φ lam 1 = lam 0 * sinh φ + lam 1 * cosh φ := by
  simp [boostConjLambda]

/-- The positional scalar after the shell boost depends on `λ⁰` and `λ¹` only. -/
theorem shellRest_phase_boost (φ : ℝ) (lam : Vec4) :
    wavePhase (shellRestQ - shellRestP) (boostConjLambda φ lam) =
      -8 * (lam 0 * sinh φ + lam 1 * cosh φ) := by
  rw [shellRest_phase_coord, boostConjLambda_coord1]

/-- The dual angle on the shell axis does not change the positional scalar. -/
theorem shellRest_phase_dual (θ : ℝ) (lam : Vec4) :
    wavePhase (shellRestQ - shellRestP) (rotation0ConjLambda θ lam) =
      wavePhase (shellRestQ - shellRestP) lam := by
  rw [shellRest_phase_coord, shellRest_phase_coord, (rotation0ConjLambda_coord01 θ lam).2]

/-- The shell motor's positional scalar is the usual sector's scalar. -/
theorem shellRest_phase_motor (α β : ℝ) (lam : Vec4) :
    wavePhase (shellRestQ - shellRestP)
        (boostConjLambda α (rotation0ConjLambda β lam)) =
      wavePhase (shellRestQ - shellRestP) (boostConjLambda α lam) := by
  rw [shellRest_phase_boost, shellRest_phase_boost, (rotation0ConjLambda_coord01 β lam).1,
    (rotation0ConjLambda_coord01 β lam).2]

theorem shell_motor_is_boost_after_dual (α β : ℝ) (p : TransParams) :
    sandwich (rotorTorsion (axisParams α β)) (expTrans p) =
      expTrans ⟨boostConjLambda α (rotation0ConjLambda β p.lambda)⟩ := by
  rw [rotorTorsion_axis_factor, sandwich_comp]
  have hU : rotorUsual (axisParams α β) = rotorTorsion (pureBoost α) := by
    rw [rotorUsual_axis_closed, rotorTorsion_pureBoost_closed]
  have hD : rotorDual (axisParams α β) = rotorTorsion (pureRotation0 β) := by
    rw [rotorDual_axis_closed, rotorTorsion_pureRotation0_closed]
  rw [hU, hD, sandwich_pureRotation0_expTrans, sandwich_pureBoost_expTrans]

/-! ### Pure time, unread until the usual sector acts -/

/-- Unit coefficient of `N₀`. -/
def timeTranslator : TransParams where
  lambda := Pi.single 0 1

theorem timeTranslator_phase :
    wavePhase (shellRestQ - shellRestP) timeTranslator.lambda = 0 := by
  rw [shellRest_phase_coord]
  simp [timeTranslator]

theorem read_boost_phase (φ : ℝ) :
    wavePhase (shellRestQ - shellRestP) (boostConjLambda φ readTranslator.lambda) =
      -8 * cosh φ := by
  rw [shellRest_phase_boost]
  simp [readTranslator]

theorem time_boost_phase (φ : ℝ) :
    wavePhase (shellRestQ - shellRestP) (boostConjLambda φ timeTranslator.lambda) =
      -8 * sinh φ := by
  rw [shellRest_phase_boost]
  simp [timeTranslator]

theorem read_dual_phase (θ : ℝ) :
    wavePhase (shellRestQ - shellRestP) (rotation0ConjLambda θ readTranslator.lambda) =
      -8 := by
  rw [shellRest_phase_dual, shellRest_read_phase]

theorem time_dual_phase (θ : ℝ) :
    wavePhase (shellRestQ - shellRestP) (rotation0ConjLambda θ timeTranslator.lambda) =
      0 := by
  rw [shellRest_phase_dual, timeTranslator_phase]

private theorem one_lt_cosh_of_pos {x : ℝ} (hx : 0 < x) : 1 < cosh x := by
  have hmono : StrictMonoOn cosh (Set.Ici 0) := cosh_strictMonoOn
  have hlt := hmono (by simp) hx.le hx
  simpa [cosh_zero] using hlt

theorem shellNode_sectors_disagree :
    wavePhase (shellRestQ - shellRestP)
        (boostConjLambda shellRapidity readTranslator.lambda) =
      -8 * cosh shellRapidity ∧
      wavePhase (shellRestQ - shellRestP)
          (rotation0ConjLambda shellRapidity readTranslator.lambda) = -8 ∧
        -8 * cosh shellRapidity < (-8 : ℝ) ∧
          wavePhase (shellRestQ - shellRestP)
              (boostConjLambda shellRapidity timeTranslator.lambda) =
            -8 * sinh shellRapidity ∧
            -8 * sinh shellRapidity < 0 ∧
              wavePhase (shellRestQ - shellRestP)
                  (rotation0ConjLambda shellRapidity timeTranslator.lambda) = 0 := by
  have hcosh : 1 < cosh shellRapidity := one_lt_cosh_of_pos shellRapidity_pos
  have hsinh : 0 < sinh shellRapidity := sinh_pos_iff.mpr shellRapidity_pos
  refine ⟨read_boost_phase _, read_dual_phase _, ?_, time_boost_phase _, ?_, time_dual_phase _⟩
  · linarith
  · linarith

/-! ### Information at the node -/

/-- Image of a translator under the shell's usual boost. -/
noncomputable def boostedTranslator (φ : ℝ) (p : TransParams) : TransParams where
  lambda := boostConjLambda φ p.lambda

theorem shellNode_information :
    ∃ θ : ℝ,
      phaseFisher 1 1 shellParticleP shellParticleQ θ = 544 / 625 ∧
        translatorInformation 1 1 θ shellRestP shellRestQ shellParticleP shellParticleQ 0
            readTranslator = 34816 / 625 ∧
          translatorInformation 1 1 θ shellRestP shellRestQ shellParticleP shellParticleQ 0
              (boostedTranslator shellRapidity readTranslator) >
            34816 / 625 ∧
            translatorInformation 1 1 θ shellRestP shellRestQ shellParticleP shellParticleQ 0
                timeTranslator = 0 ∧
              translatorInformation 1 1 θ shellRestP shellRestQ shellParticleP shellParticleQ 0
                  (boostedTranslator shellRapidity timeTranslator) > 0 ∧
                translatorInformation 1 1 θ shellRestP shellRestQ shellParticleP shellParticleQ 0
                    ⟨rotation0ConjLambda shellRapidity readTranslator.lambda⟩ =
                  34816 / 625 := by
  obtain ⟨θ, hF, _, _, _, _, _⟩ := shellRest_translationFisher
  have hψ := shellRest_packet_ne_zero θ (0 : Vec4)
  have hread : translatorInformation 1 1 θ shellRestP shellRestQ shellParticleP shellParticleQ 0
      readTranslator = 34816 / 625 := by
    rw [translatorInformation_eq_phase 1 1 θ shellRestP shellRestQ shellParticleP shellParticleQ
        0 readTranslator hψ, wavePhase_zero, zero_add, hF, shellRest_read_phase]
    norm_num
  have hcosh : 1 < cosh shellRapidity := one_lt_cosh_of_pos shellRapidity_pos
  have hboost : translatorInformation 1 1 θ shellRestP shellRestQ shellParticleP shellParticleQ 0
      (boostedTranslator shellRapidity readTranslator) =
        (544 / 625) * (8 * cosh shellRapidity) ^ 2 := by
    rw [translatorInformation_eq_phase 1 1 θ shellRestP shellRestQ shellParticleP shellParticleQ
        0 (boostedTranslator shellRapidity readTranslator) hψ, wavePhase_zero, zero_add, hF,
      show (boostedTranslator shellRapidity readTranslator).lambda =
        boostConjLambda shellRapidity readTranslator.lambda from rfl, read_boost_phase]
    ring
  have hboost_gt : (544 / 625) * (8 * cosh shellRapidity) ^ 2 > 34816 / 625 := by
    have hsq : (1 : ℝ) < cosh shellRapidity ^ 2 := by nlinarith [hcosh]
    have hpos : (0 : ℝ) < 544 / 625 := by norm_num
    have hscale : (544 / 625) * 64 * 1 < (544 / 625) * 64 * cosh shellRapidity ^ 2 :=
      mul_lt_mul_of_pos_left hsq (mul_pos hpos (by norm_num))
    have h64 : (8 * cosh shellRapidity) ^ 2 = 64 * cosh shellRapidity ^ 2 := by ring
    have hbase : (544 : ℝ) / 625 * 64 = 34816 / 625 := by norm_num
    rw [h64]
    linarith
  have htime : translatorInformation 1 1 θ shellRestP shellRestQ shellParticleP shellParticleQ 0
      timeTranslator = 0 := by
    rw [translatorInformation_eq_phase 1 1 θ shellRestP shellRestQ shellParticleP shellParticleQ
        0 timeTranslator hψ, wavePhase_zero, zero_add, timeTranslator_phase, zero_pow (by norm_num),
      mul_zero]
  have htimeBoost : translatorInformation 1 1 θ shellRestP shellRestQ shellParticleP
      shellParticleQ 0 (boostedTranslator shellRapidity timeTranslator) =
        (544 / 625) * (8 * sinh shellRapidity) ^ 2 := by
    rw [translatorInformation_eq_phase 1 1 θ shellRestP shellRestQ shellParticleP shellParticleQ
        0 (boostedTranslator shellRapidity timeTranslator) hψ, wavePhase_zero, zero_add, hF,
      show (boostedTranslator shellRapidity timeTranslator).lambda =
        boostConjLambda shellRapidity timeTranslator.lambda from rfl, time_boost_phase]
    ring
  have hsinh : sinh shellRapidity ≠ 0 := (sinh_pos_iff.mpr shellRapidity_pos).ne'
  have htime_gt : (544 / 625) * (8 * sinh shellRapidity) ^ 2 > 0 := by
    have hsq : (0 : ℝ) < sinh shellRapidity ^ 2 := sq_pos_of_ne_zero hsinh
    positivity
  have hdual : translatorInformation 1 1 θ shellRestP shellRestQ shellParticleP shellParticleQ 0
      ⟨rotation0ConjLambda shellRapidity readTranslator.lambda⟩ = 34816 / 625 := by
    rw [translatorInformation_eq_phase 1 1 θ shellRestP shellRestQ shellParticleP shellParticleQ
        0 ⟨rotation0ConjLambda shellRapidity readTranslator.lambda⟩ hψ, wavePhase_zero, zero_add,
      hF, read_dual_phase]
    norm_num
  exact ⟨θ, hF, hread, hboost_gt.trans_eq hboost.symm, htime, htime_gt.trans_eq htimeBoost.symm,
    hdual⟩

/-- At the first node the shell is `J = 0` and `γ_s = 0`, and the positional scalar of `N₁`
is the usual sector's number. The dual sector keeps `-8`. The two informations at quadrature
are not equal, and the unread time translator becomes readable. -/
theorem shellNode_position :
    gammaSEqual resonanceRoot1 = 0 ∧
      J (axisParams shellRapidity shellRapidity) = 0 ∧
        mass (axisParams shellRapidity shellRapidity) = shellRapidity ^ 2 ∧
          (∀ β : ℝ, ∀ lam : Vec4,
            wavePhase (shellRestQ - shellRestP)
                (boostConjLambda shellRapidity (rotation0ConjLambda β lam)) =
              wavePhase (shellRestQ - shellRestP)
                (boostConjLambda shellRapidity lam)) ∧
            wavePhase (shellRestQ - shellRestP)
                (boostConjLambda shellRapidity readTranslator.lambda) <
              wavePhase (shellRestQ - shellRestP) readTranslator.lambda ∧
              (∃ θ : ℝ,
                translatorInformation 1 1 θ shellRestP shellRestQ shellParticleP shellParticleQ 0
                    readTranslator = 34816 / 625 ∧
                  translatorInformation 1 1 θ shellRestP shellRestQ shellParticleP
                      shellParticleQ 0 (boostedTranslator shellRapidity readTranslator) >
                    34816 / 625 ∧
                    translatorInformation 1 1 θ shellRestP shellRestQ shellParticleP
                        shellParticleQ 0 timeTranslator = 0 ∧
                      0 < translatorInformation 1 1 θ shellRestP shellRestQ shellParticleP
                          shellParticleQ 0
                            (boostedTranslator shellRapidity timeTranslator)) := by
  obtain ⟨hγ, hJ, hM, _⟩ := shellNode_rotor
  obtain ⟨hboost, hdual, hlt, _, _, _⟩ := shellNode_sectors_disagree
  obtain ⟨θ, _, hread, hinfo, htime, htimeInfo, _⟩ := shellNode_information
  refine ⟨hγ, hJ, hM, fun β lam => shellRest_phase_motor shellRapidity β lam, ?_,
    ⟨θ, hread, hinfo, htime, htimeInfo⟩⟩
  rw [hboost, shellRest_read_phase]
  exact hlt

end Logic

end DoubleSpacetime
