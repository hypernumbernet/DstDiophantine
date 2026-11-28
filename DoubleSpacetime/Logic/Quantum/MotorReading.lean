import DoubleSpacetime.Algebra.Invariant
import DoubleSpacetime.Algebra.Sandwich
import DoubleSpacetime.Logic.Quantum.TranslatorInformation
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Arcosh

/-!
# What a rotor preserves, and what a packet reads

A motor is a torsion rotor times a null translator. The rotor acts on the translator by
sandwich. On a pure boost that action is the Lorentz transformation `boost01` of the
coefficients. It preserves the Minkowski contraction `η(δ, λ)` of a co-transformed pair, and
it preserves `Q(λ)`.

A shell packet does not read that contraction. Its phase is the Euclidean sum `∑ δ_μ λ^μ`,
and `translatorInformation` is `phaseFisher` times the square of that sum. The signed scalars
agree for every translator exactly when the time slot `δ⁰ λ⁰` vanishes. The squares, and
therefore the two informations, agree exactly when that slot vanishes or the spatial
contraction vanishes. Off both of those cases the packet's number and the rotor's number
differ by `phaseFisher` times `4 δ⁰ λ⁰ (δ_spatial · λ_spatial)`.

The torsional scalar `J` and the unsigned mass `M` of the rotor are not either number. One
rapidity, `cosh = 5/3` and `sinh = -4/3`, has `J = M = φ²/2 < 2`. Its sandwich sends the
unit translator along `N_1` to `(-4/3, 5/3)`. The mean-rest packet reads `34816/625` before
the sandwich and `34816/225` after it. Both are larger than `2`. In that frame the relative
energy vanishes, so the packet is reading the Minkowski scalar, and the change is the change
of `λ`. The co-boosted pair keeps the Minkowski scalar at `-8` and moves the Euclidean scalar
to `-328/9`.

Rest against `(5, 4, 0, 0)` has relative energy `-2`. The same sandwiched translator is read
as `-4`, information `1296/25`, while the invariant scalar is `-28/3` and its quadratic form
at the same projective scalar is `7056/25`. A pure time translator on that packet has
opposite signs, `-2` and `2`, and equal squares: agreement of the informations is not
agreement of the scalars. The position reading at time `-π/2` is `-π/2`.
-/

namespace DoubleSpacetime

namespace Logic

open Motor Amplification Sandwich Invariant Operations Real

/-! ### The two scalars -/

/-- Coordinate form of `minkowskiPolar`. A boost preserves this contraction, not `wavePhase`. -/
theorem minkowskiPolar_eq (a b : Vec4) :
    minkowskiPolar a b = -(a 0 * b 0) + a 1 * b 1 + a 2 * b 2 + a 3 * b 3 := by
  unfold minkowskiPolar
  simp [minkowskiEta, w31, Fin.sum_univ_four]

theorem minkowskiPolar_self (p : Vec4) : minkowskiPolar p p = minkowskiQ p := rfl

theorem wavePhase_expand (a b : Vec4) :
    wavePhase a b = a 0 * b 0 + a 1 * b 1 + a 2 * b 2 + a 3 * b 3 := by
  unfold wavePhase
  simp [Fin.sum_univ_four]

theorem wavePhase_sub_minkowskiPolar (a b : Vec4) :
    wavePhase a b - minkowskiPolar a b = 2 * a 0 * b 0 := by
  rw [wavePhase_expand, minkowskiPolar_eq]
  ring

theorem wavePhase_eq_minkowskiPolar_iff (a b : Vec4) :
    wavePhase a b = minkowskiPolar a b ↔ a 0 * b 0 = 0 := by
  rw [← sub_eq_zero, wavePhase_sub_minkowskiPolar]
  constructor
  · intro h
    nlinarith
  · intro h
    calc
      (2 : ℝ) * a 0 * b 0 = 2 * (a 0 * b 0) := by ring
      _ = 2 * 0 := by rw [h]
      _ = 0 := by ring

theorem wave_sq_sub_minkowski_sq (a b : Vec4) :
    wavePhase a b ^ 2 - minkowskiPolar a b ^ 2 =
      4 * (a 0 * b 0) * (a 1 * b 1 + a 2 * b 2 + a 3 * b 3) := by
  rw [wavePhase_expand, minkowskiPolar_eq]
  ring

/-- Active boost in the `(t, x)` plane preserves the Minkowski contraction. -/
theorem boost01_minkowskiPolar {ch sh : ℝ} (h : ch ^ 2 - sh ^ 2 = 1) (a b : Vec4) :
    minkowskiPolar (boost01 ch sh a) (boost01 ch sh b) = minkowskiPolar a b := by
  rw [minkowskiPolar_eq, minkowskiPolar_eq]
  have hplane :
      -((ch * a 0 + sh * a 1) * (ch * b 0 + sh * b 1)) +
          (sh * a 0 + ch * a 1) * (sh * b 0 + ch * b 1) =
        (ch ^ 2 - sh ^ 2) * (-(a 0 * b 0) + a 1 * b 1) := by ring
  simp only [boost01]
  rw [hplane, h]
  ring

/-! ### The quadratic form the rotor preserves -/

/-- `phaseFisher` times the square of the Minkowski contraction. Not the packet's reading. -/
noncomputable def invariantInformation (r s α : ℝ) (p q : Vec4) (u v : DiracSpinor)
    (x : Vec4) (lam : TransParams) : ℝ :=
  phaseFisher r s u v (wavePhase (q - p) x + α) *
    minkowskiPolar (q - p) lam.lambda ^ 2

theorem information_sub_invariant (r s α : ℝ) (p q : Vec4) (u v : DiracSpinor) (x : Vec4)
    (lam : TransParams) (hψ : shellPacket r s α p q u v x ≠ 0) :
    translatorInformation r s α p q u v x lam - invariantInformation r s α p q u v x lam =
      phaseFisher r s u v (wavePhase (q - p) x + α) *
        (wavePhase (q - p) lam.lambda ^ 2 - minkowskiPolar (q - p) lam.lambda ^ 2) := by
  rw [translatorInformation_eq_phase r s α p q u v x lam hψ, invariantInformation]
  ring

/-- The two informations agree exactly when the time slot or the spatial contraction vanishes. -/
theorem information_eq_invariant_iff (r s α : ℝ) (p q : Vec4) (u v : DiracSpinor) (x : Vec4)
    (lam : TransParams) (hψ : shellPacket r s α p q u v x ≠ 0)
    (hF : phaseFisher r s u v (wavePhase (q - p) x + α) ≠ 0) :
    translatorInformation r s α p q u v x lam =
        invariantInformation r s α p q u v x lam ↔
      (q - p) 0 * lam.lambda 0 = 0 ∨
        (q - p) 1 * lam.lambda 1 + (q - p) 2 * lam.lambda 2 + (q - p) 3 * lam.lambda 3 = 0 := by
  rw [translatorInformation_eq_phase r s α p q u v x lam hψ, invariantInformation]
  set scale := phaseFisher r s u v (wavePhase (q - p) x + α)
  set a := q - p
  set b := lam.lambda
  have hsub : wavePhase a b ^ 2 - minkowskiPolar a b ^ 2 =
      4 * (a 0 * b 0) * (a 1 * b 1 + a 2 * b 2 + a 3 * b 3) :=
    wave_sq_sub_minkowski_sq a b
  constructor
  · intro h
    have hsq : wavePhase a b ^ 2 = minkowskiPolar a b ^ 2 := mul_left_cancel₀ hF h
    have hzero : wavePhase a b ^ 2 - minkowskiPolar a b ^ 2 = 0 := sub_eq_zero.mpr hsq
    rw [hsub] at hzero
    have hprod : (4 : ℝ) * ((a 0 * b 0) * (a 1 * b 1 + a 2 * b 2 + a 3 * b 3)) = 0 := by
      simpa [mul_assoc] using hzero
    have hfour : (4 : ℝ) ≠ 0 := by norm_num
    have hTS : (a 0 * b 0) * (a 1 * b 1 + a 2 * b 2 + a 3 * b 3) = 0 :=
      (mul_eq_zero.mp hprod).resolve_left hfour
    exact mul_eq_zero.mp hTS
  · intro h
    rcases h with hT | hS
    · have heq : wavePhase a b = minkowskiPolar a b :=
        (wavePhase_eq_minkowskiPolar_iff a b).mpr hT
      rw [heq]
    · have hzero : wavePhase a b ^ 2 - minkowskiPolar a b ^ 2 = 0 := by
        rw [hsub, hS, mul_zero]
      rw [sub_eq_zero.mp hzero]

/-! ### The boost as a sandwich -/

/-- Image of a translator under the `(t, x)` boost with the given `cosh` and `sinh`. -/
def boostTranslator (ch sh : ℝ) (p : TransParams) : TransParams where
  lambda := boost01 ch sh p.lambda

theorem transParams_lambda_ext {p q : TransParams} (h : p.lambda = q.lambda) : p = q := by
  cases p
  cases q
  simpa using h

theorem boostTranslator_eq_conj (φ : ℝ) (p : TransParams) :
    boostTranslator (cosh φ) (sinh φ) p = ⟨boostConjLambda φ p.lambda⟩ := by
  apply transParams_lambda_ext
  funext μ
  fin_cases μ
  · simp [boostTranslator, boost01, boostConjLambda]
    ring
  · simp [boostTranslator, boost01, boostConjLambda]
    ring
  · simp [boostTranslator, boost01, boostConjLambda]
  · simp [boostTranslator, boost01, boostConjLambda]

theorem sandwich_boostTranslator (φ : ℝ) (p : TransParams) :
    sandwich (rotorTorsion (pureBoost φ)) (expTrans p) =
      expTrans (boostTranslator (cosh φ) (sinh φ) p) := by
  rw [sandwich_pureBoost_expTrans]
  congr 1
  exact (boostTranslator_eq_conj φ p).symm

theorem mass_pureBoost (φ : ℝ) : mass (pureBoost φ) = (1 / 2) * φ ^ 2 := by
  rw [mass_coef]
  simp only [pureBoost, Fin.sum_univ_three, zero_pow two_ne_zero, add_zero, mul_zero, pow_two]

theorem pureBoost_mass_eq_J (φ : ℝ) : mass (pureBoost φ) = J (pureBoost φ) := by
  rw [mass_pureBoost, J_pureBoost]

private theorem cosh_two_gt_five_thirds : (5 / 3 : ℝ) < cosh 2 := by
  rw [cosh_eq]
  have hmul : exp 2 = exp 1 * exp 1 := by
    rw [← exp_add]
    norm_num
  have hgt : (2 : ℝ) < exp 1 := exp_one_gt_two
  have hpos : 0 < exp (-2) := exp_pos _
  nlinarith

/-- The rapidity `cosh = 5/3`, `sinh = -4/3` is one pure boost. Its `J` equals its mass and
lies strictly below `2`, hence below both mean-rest readings of its translator images. -/
theorem labRapidity_below_two :
    ∃ φ : ℝ, cosh φ = 5 / 3 ∧ sinh φ = -4 / 3 ∧
      J (pureBoost φ) = (1 / 2) * φ ^ 2 ∧
        mass (pureBoost φ) = J (pureBoost φ) ∧
          J (pureBoost φ) < 2 ∧
            sandwich (rotorTorsion (pureBoost φ)) (expTrans readTranslator) =
              expTrans (boostTranslator (5 / 3) (-4 / 3) readTranslator) := by
  let φ : ℝ := -arcosh (5 / 3)
  have hle : (1 : ℝ) ≤ 5 / 3 := by norm_num
  have hcosh : cosh φ = 5 / 3 := by
    rw [show φ = -arcosh (5 / 3) from rfl, cosh_neg, cosh_arcosh hle]
  have hsqrt : √((5 / 3 : ℝ) ^ 2 - 1) = 4 / 3 := by
    have hsq : (5 / 3 : ℝ) ^ 2 - 1 = (4 / 3) ^ 2 := by norm_num
    rw [hsq, sqrt_sq (by norm_num : (0 : ℝ) ≤ 4 / 3)]
  have hsinh : sinh φ = -4 / 3 := by
    rw [show φ = -arcosh (5 / 3) from rfl, sinh_neg, sinh_arcosh hle, hsqrt]
    ring
  have hnn : 0 ≤ arcosh (5 / 3) := arcosh_nonneg hle
  have habs : |φ| < 2 := by
    rw [show φ = -arcosh (5 / 3) from rfl, abs_neg, abs_of_nonneg hnn]
    have hcmp : cosh (arcosh (5 / 3)) < cosh 2 := by
      rw [cosh_arcosh hle]
      exact cosh_two_gt_five_thirds
    have hlt : |arcosh (5 / 3)| < |(2 : ℝ)| := cosh_lt_cosh.mp hcmp
    simpa [abs_of_nonneg hnn, abs_of_pos (by norm_num : (0 : ℝ) < 2)] using hlt
  have hJ : J (pureBoost φ) < 2 := by
    rw [J_pureBoost]
    have hsq : φ ^ 2 < 2 ^ 2 := by
      rw [sq_lt_sq]
      simpa [abs_of_pos (by norm_num : (0 : ℝ) < 2)] using habs
    nlinarith
  refine ⟨φ, hcosh, hsinh, J_pureBoost φ, pureBoost_mass_eq_J φ, hJ, ?_⟩
  rw [sandwich_boostTranslator, hcosh, hsinh]

/-! ### Mass 3, mean rest -/

theorem boostedRead_coords :
    (boostTranslator (5 / 3) (-4 / 3) readTranslator).lambda 0 = -4 / 3 ∧
      (boostTranslator (5 / 3) (-4 / 3) readTranslator).lambda 1 = 5 / 3 ∧
        (boostTranslator (5 / 3) (-4 / 3) readTranslator).lambda 2 = 0 ∧
          (boostTranslator (5 / 3) (-4 / 3) readTranslator).lambda 3 = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [boostTranslator, readTranslator, boost01,
      Pi.single_eq_of_ne (show (0 : Fin 4) ≠ 1 by decide), Pi.single_eq_same]
    norm_num
  · simp only [boostTranslator, readTranslator, boost01,
      Pi.single_eq_of_ne (show (0 : Fin 4) ≠ 1 by decide), Pi.single_eq_same]
    norm_num
  · simp [boostTranslator, readTranslator, boost01]
  · simp [boostTranslator, readTranslator, boost01]

theorem meanRest_reads_invariant (b : Vec4) :
    wavePhase (shellRestQ - shellRestP) b =
      minkowskiPolar (shellRestQ - shellRestP) b :=
  (wavePhase_eq_minkowskiPolar_iff (shellRestQ - shellRestP) b).mpr <| by
    rw [shellRest_relative.1, zero_mul]

theorem shellRest_read_minkowski :
    minkowskiPolar (shellRestQ - shellRestP) readTranslator.lambda = -8 := by
  rw [← meanRest_reads_invariant readTranslator.lambda, shellRest_read_phase]

theorem shellRest_boosted_phase :
    wavePhase (shellRestQ - shellRestP)
        (boostTranslator (5 / 3) (-4 / 3) readTranslator).lambda = -40 / 3 ∧
      minkowskiPolar (shellRestQ - shellRestP)
          (boostTranslator (5 / 3) (-4 / 3) readTranslator).lambda = -40 / 3 := by
  have hδ := shellRest_relative
  have hlam := boostedRead_coords
  have hwave :
      wavePhase (shellRestQ - shellRestP)
          (boostTranslator (5 / 3) (-4 / 3) readTranslator).lambda = -40 / 3 := by
    rw [wavePhase_expand, hδ.1, hδ.2.1, hδ.2.2.1, hδ.2.2.2, hlam.1, hlam.2.1, hlam.2.2.1,
      hlam.2.2.2]
    norm_num
  exact ⟨hwave, (meanRest_reads_invariant _).symm.trans hwave⟩

theorem read_Q31 : Q31 readTranslator.lambda = 1 := by
  rw [Q31_eq_minkowskiDot]
  simp [minkowskiDot, readTranslator, Pi.single_eq_same]

theorem boosted_Q31 :
    Q31 (boostTranslator (5 / 3) (-4 / 3) readTranslator).lambda = 1 := by
  rw [Q31_eq_minkowskiDot, minkowskiDot]
  have hlam := boostedRead_coords
  rw [hlam.1, hlam.2.1, hlam.2.2.1, hlam.2.2.2]
  norm_num

theorem boosted_motor_ne :
    expTrans (boostTranslator (5 / 3) (-4 / 3) readTranslator) ≠ expTrans readTranslator := by
  apply expTrans_ne_of_lambda
  intro h
  have h0 := congrFun h 0
  rw [boostedRead_coords.1] at h0
  have hright : readTranslator.lambda 0 = 0 := by
    simp [readTranslator]
  rw [hright] at h0
  norm_num at h0

theorem shellRest_joint_scalars :
    wavePhase (boost01 (5 / 3) (-4 / 3) (shellRestQ - shellRestP))
        (boostTranslator (5 / 3) (-4 / 3) readTranslator).lambda = -328 / 9 ∧
      minkowskiPolar (boost01 (5 / 3) (-4 / 3) (shellRestQ - shellRestP))
          (boostTranslator (5 / 3) (-4 / 3) readTranslator).lambda = -8 ∧
        -328 / 9 ≠ (-8 : ℝ) := by
  have hhyp : ((5 : ℝ) / 3) ^ 2 - (-4 / 3) ^ 2 = 1 := by norm_num
  have hmink : minkowskiPolar (boost01 (5 / 3) (-4 / 3) (shellRestQ - shellRestP))
      (boostTranslator (5 / 3) (-4 / 3) readTranslator).lambda = -8 := by
    have htr : (boostTranslator (5 / 3) (-4 / 3) readTranslator).lambda =
        boost01 (5 / 3) (-4 / 3) readTranslator.lambda := rfl
    rw [htr, boost01_minkowskiPolar hhyp, shellRest_read_minkowski]
  have hδ := shellRest_relative
  have hlam := boostedRead_coords
  have hD0 : boost01 (5 / 3) (-4 / 3) (shellRestQ - shellRestP) 0 = 32 / 3 := by
    simp only [boost01, hδ.1, hδ.2.1]
    norm_num
  have hD1 : boost01 (5 / 3) (-4 / 3) (shellRestQ - shellRestP) 1 = -40 / 3 := by
    simp only [boost01, hδ.1, hδ.2.1]
    norm_num
  have hD2 : boost01 (5 / 3) (-4 / 3) (shellRestQ - shellRestP) 2 = 0 := by
    simp [boost01, hδ.2.2.1]
  have hD3 : boost01 (5 / 3) (-4 / 3) (shellRestQ - shellRestP) 3 = 0 := by
    simp [boost01, hδ.2.2.2]
  refine ⟨?_, hmink, by norm_num⟩
  rw [wavePhase_expand, hD0, hD1, hD2, hD3, hlam.1, hlam.2.1, hlam.2.2.1, hlam.2.2.2]
  norm_num

theorem shellRest_rotor_reading :
    ∃ θ : ℝ,
      translatorInformation 1 1 θ shellRestP shellRestQ shellParticleP shellParticleQ 0
          readTranslator = 34816 / 625 ∧
        translatorInformation 1 1 θ shellRestP shellRestQ shellParticleP shellParticleQ 0
            (boostTranslator (5 / 3) (-4 / 3) readTranslator) = 34816 / 225 ∧
          34816 / 625 ≠ 34816 / 225 ∧
            (2 : ℝ) < 34816 / 625 ∧
              (2 : ℝ) < 34816 / 225 ∧
                precisionFloor
                    (shellPacket 1 1 θ shellRestP shellRestQ shellParticleP shellParticleQ) 0
                    (boostTranslator (5 / 3) (-4 / 3) readTranslator).lambda = 225 / 34816 ∧
                  Q31 readTranslator.lambda = 1 ∧
                    Q31 (boostTranslator (5 / 3) (-4 / 3) readTranslator).lambda = 1 ∧
                      (inner ℂ (shellPacket 1 1 θ shellRestP shellRestQ shellParticleP
                          shellParticleQ 0)
                        (positionOp 1 (shellPacket 1 1 θ shellRestP shellRestQ shellParticleP
                          shellParticleQ) 0)).re /
                      ‖shellPacket 1 1 θ shellRestP shellRestQ shellParticleP
                        shellParticleQ 0‖ ^ 2 = 0 := by
  obtain ⟨θ, hF, _, _, _, _, _⟩ := shellRest_translationFisher
  refine ⟨θ, ?_, ?_, by norm_num, by norm_num, by norm_num, ?_, read_Q31, boosted_Q31, ?_⟩
  · have hψ := shellRest_packet_ne_zero θ (0 : Vec4)
    rw [translatorInformation_eq_phase 1 1 θ shellRestP shellRestQ shellParticleP shellParticleQ
        0 readTranslator hψ, wavePhase_zero, zero_add, hF, shellRest_read_phase]
    norm_num
  · have hψ := shellRest_packet_ne_zero θ (0 : Vec4)
    rw [translatorInformation_eq_phase 1 1 θ shellRestP shellRestQ shellParticleP shellParticleQ
        0 (boostTranslator (5 / 3) (-4 / 3) readTranslator) hψ, wavePhase_zero, zero_add, hF,
      shellRest_boosted_phase.1]
    norm_num
  · have hψ := shellRest_packet_ne_zero θ (0 : Vec4)
    have hinfo : translatorInformation 1 1 θ shellRestP shellRestQ shellParticleP shellParticleQ 0
        (boostTranslator (5 / 3) (-4 / 3) readTranslator) = 34816 / 225 := by
      rw [translatorInformation_eq_phase 1 1 θ shellRestP shellRestQ shellParticleP shellParticleQ
          0 (boostTranslator (5 / 3) (-4 / 3) readTranslator) hψ, wavePhase_zero, zero_add, hF,
        shellRest_boosted_phase.1]
      norm_num
    have heq : displacementInformation
        (shellPacket 1 1 θ shellRestP shellRestQ shellParticleP shellParticleQ) 0
        (boostTranslator (5 / 3) (-4 / 3) readTranslator).lambda =
      translatorInformation 1 1 θ shellRestP shellRestQ shellParticleP shellParticleQ 0
        (boostTranslator (5 / 3) (-4 / 3) readTranslator) := rfl
    rw [precisionFloor, heq, hinfo]
    norm_num
  · have hψ := shellRest_packet_ne_zero θ (0 : Vec4)
    rw [position_reading (Ψ := shellPacket 1 1 θ shellRestP shellRestQ shellParticleP
        shellParticleQ) (μ := 1) (x := 0) hψ]
    simp

/-! ### Off mean rest the two forms split -/

/-- Unit coefficient of `N₀`. -/
def timeTranslator : TransParams where
  lambda := Pi.single 0 1

theorem shellLab_time_sign :
    wavePhase (restMomentum 3 - shellRestP) timeTranslator.lambda = -2 ∧
      minkowskiPolar (restMomentum 3 - shellRestP) timeTranslator.lambda = 2 ∧
        -2 ≠ (2 : ℝ) ∧
          wavePhase (restMomentum 3 - shellRestP) timeTranslator.lambda ^ 2 =
            minkowskiPolar (restMomentum 3 - shellRestP) timeTranslator.lambda ^ 2 := by
  have hδ : (restMomentum 3 - shellRestP) 0 = -2 := shellLab_relative.1
  have hwave : wavePhase (restMomentum 3 - shellRestP) timeTranslator.lambda = -2 := by
    rw [show timeTranslator.lambda = Pi.single 0 1 from rfl, wavePhase_single, hδ]
  have hmink : minkowskiPolar (restMomentum 3 - shellRestP) timeTranslator.lambda = 2 := by
    rw [minkowskiPolar_eq]
    simp only [timeTranslator, Pi.single_eq_same,
      Pi.single_eq_of_ne (show (1 : Fin 4) ≠ 0 by decide),
      Pi.single_eq_of_ne (show (2 : Fin 4) ≠ 0 by decide),
      Pi.single_eq_of_ne (show (3 : Fin 4) ≠ 0 by decide), hδ]
    norm_num
  refine ⟨hwave, hmink, by norm_num, ?_⟩
  rw [hwave, hmink]
  norm_num

theorem lab_boosted_scalars :
    wavePhase (restMomentum 3 - shellRestP)
        (boostTranslator (5 / 3) (-4 / 3) readTranslator).lambda = -4 ∧
      minkowskiPolar (restMomentum 3 - shellRestP)
          (boostTranslator (5 / 3) (-4 / 3) readTranslator).lambda = -28 / 3 ∧
        -4 ≠ (-28 / 3 : ℝ) := by
  have hδ := shellLab_relative
  have hlam := boostedRead_coords
  refine ⟨?_, ?_, by norm_num⟩
  · rw [wavePhase_expand, hδ.1, hδ.2.1, hδ.2.2.1, hδ.2.2.2, hlam.1, hlam.2.1, hlam.2.2.1,
      hlam.2.2.2]
    norm_num
  · rw [minkowskiPolar_eq, hδ.1, hδ.2.1, hδ.2.2.1, hδ.2.2.2, hlam.1, hlam.2.1, hlam.2.2.1,
      hlam.2.2.2]
    norm_num

theorem shellLab_reading_split :
    let Ψ := shellPacket 1 1 0 shellRestP (restMomentum 3) shellParticleP shellLabSpinor
    let x := timeShift (-Real.pi / 2)
    translatorInformation 1 1 0 shellRestP (restMomentum 3) shellParticleP shellLabSpinor x
        (boostTranslator (5 / 3) (-4 / 3) readTranslator) = 1296 / 25 ∧
      invariantInformation 1 1 0 shellRestP (restMomentum 3) shellParticleP shellLabSpinor x
          (boostTranslator (5 / 3) (-4 / 3) readTranslator) = 7056 / 25 ∧
        1296 / 25 ≠ 7056 / 25 ∧
          (inner ℂ (Ψ x) (positionOp 0 Ψ x)).re / ‖Ψ x‖ ^ 2 = -Real.pi / 2 ∧
            -Real.pi / 2 ≠ (1296 / 25 : ℝ) := by
  let Ψ := shellPacket 1 1 0 shellRestP (restMomentum 3) shellParticleP shellLabSpinor
  let x := timeShift (-Real.pi / 2)
  have hden : bornDensity Ψ x = 20 / 9 := shellLab_time_density.2.1
  have hψ : Ψ x ≠ 0 := by
    intro hz
    have hzero : bornDensity Ψ x = 0 := by rw [bornDensity, hz, norm_zero]; simp
    rw [hden] at hzero
    norm_num at hzero
  have hF : phaseFisher 1 1 shellParticleP shellLabSpinor
      (wavePhase (restMomentum 3 - shellRestP) x) = 81 / 25 := by
    simpa [x] using shellLab_phaseFisher.2.1
  refine ⟨?_, ?_, by norm_num, ?_, ?_⟩
  · rw [translatorInformation_eq_phase 1 1 0 shellRestP (restMomentum 3) shellParticleP
        shellLabSpinor x (boostTranslator (5 / 3) (-4 / 3) readTranslator) hψ, add_zero, hF,
      lab_boosted_scalars.1]
    norm_num
  · rw [invariantInformation, add_zero, hF, lab_boosted_scalars.2.1]
    norm_num
  · have hpos := shellLab_translationFisher.2.2.2.2.1
    simpa [Ψ, x] using hpos
  · intro h
    have hπ : Real.pi = -2592 / 25 := by linarith
    have hneg : Real.pi < 0 := by
      rw [hπ]
      norm_num
    exact absurd hneg (not_lt_of_gt Real.pi_pos)

end Logic

end DoubleSpacetime
