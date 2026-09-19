import DstDiophantine.Algebra.Admissible
import DstDiophantine.Algebra.Amplification
import DstDiophantine.Algebra.Cl31
import DstDiophantine.Algebra.Cl91
import DstDiophantine.Algebra.Continuum
import DstDiophantine.Algebra.Discrete
import DstDiophantine.Algebra.DirichletKernel
import DstDiophantine.Algebra.RelativeRotor
import DstDiophantine.Algebra.Generators
import DstDiophantine.Algebra.Invariant
import DstDiophantine.Algebra.LorentzDim
import DstDiophantine.Algebra.LorentzLie
import DstDiophantine.Algebra.ModularAmplification
import DstDiophantine.Algebra.Motor
import DstDiophantine.Algebra.MotorGroup
import DstDiophantine.Algebra.Operations
import DstDiophantine.Algebra.Periodicity
import DstDiophantine.Algebra.PGA
import DstDiophantine.Algebra.QuadraticForm
import DstDiophantine.Algebra.Sandwich
import DstDiophantine.Algebra.UnitGroup

/-!
# DST algebraic core barrel

Re-exports the PGA / biquaternion / discrete-torus layer used by the main paper
and the discrete companion. Diophantine theorems and Gravity chart modules are
**not** imported here.
-/

namespace DstDiophantine

export PGA (ι e4Index e4_sq_zero e4_anticomm e4_inner_anticomm)
export Cl31 (ι toPGA toPGA_ι)
-- `Cl91` / `Q91` / `Cl31.toCl91` / finrank facts are available via the import
-- above; they are not re-exported here to avoid clashing with `PGA`/`Cl31` `ι`.
export LorentzDim (soDim isoDim so31Dim so91Dim so8Dim iso31Dim iso91Dim
  so31Dim_eq so91Dim_eq so8Dim_eq iso31Dim_eq iso91Dim_eq
  so31Dim_ne_so91Dim iso31Dim_ne_iso91Dim
  pgaGeneratorCount_eq_iso31Dim pgaGeneratorCount_ne_iso91Dim
  lightCone_ne_torsionGenerators)
export Generators (hyperbolic cyclic null null_sq null_mul_null hyperbolic_sq cyclic_sq
  hyperbolic_smul_mul commutator commutator_null_null null_commute
  commutator_hyperbolic_cyclic_same commutator_hyperbolic0_cyclic1_ne_zero
  commutator_hyperbolic_hyperbolic commutator_cyclic_cyclic commutator_hyperbolic_cyclic
  commutator_hyperbolic0_null commutator_hyperbolic0_null_mem_span
  commutator_cyclic0_null commutator_cyclic0_null_mem_span
  nullSpan commutator_hyperbolic_null commutator_hyperbolic_null_mem_span
  commutator_cyclic_null commutator_cyclic_null_mem_span)
export LorentzLie (cyclicSpan lorentzSpan poincareSpan
  hyperbolic_mem_lorentzSpan cyclic_mem_lorentzSpan null_mem_poincareSpan
  commute_pseudoscalar_hyperbolic commute_pseudoscalar_cyclic
  commute_pseudoscalar_of_mem_lorentzSpan
  hyperbolic_eq_dual_cyclic dual_dual dual_mem_lorentzSpan
  commutator_dual_left commutator_dual_right commutator_dual_dual
  commutator_hyperbolic_hyperbolic_eq_neg commutator_hyperbolic_cyclic_eq_dual
  commutator_hyperbolic_hyperbolic_cyclic lorentzSpan_eq_sup mem_lorentzSpan_iff
  commutator_mem_lorentzSpan commutator_lorentz_null_mem_nullSpan
  commutator_null_null_eq_zero commutator_poincare_null_mem_nullSpan
  commutator_mem_poincareSpan commutator_hyperbolic0_null0_ne_zero
  dualParams dual_omegaTorsion omegaTorsion_mem_lorentzSpan
  J_dualParams mass_dualParams JNormalized_dualParams)
export Operations (pseudoscalar dual TorsionParams daggerParams
  e4_commute_pseudoscalar dual_null
  pseudoscalar_sq ι_anticomm_pseudoscalar minkowskiVector minkowskiVector_sq
  Q31_eq_minkowskiDot minkowskiVector_anticomm_pseudoscalar
  dual_minkowskiVector_sq dual_time)
export Admissible (IsPrincipalBranch IsAdmissibleContinuous
  admissibleContinuous_implies_principalBranch)
export Discrete (DiscreteTorsion toTorsionParams IsAdmissible
  toTorsionParams_alpha_nonneg toTorsionParams_beta_nonneg
  toTorsionParams_alpha_lt_two_pi toTorsionParams_beta_lt_two_pi
  card_discreteTorsion
  isAdmissible_iff_admissibleContinuous isAdmissible_iff_principalBranch
  admissible_continuous_of_discrete admissible_sum_le admissible_alpha_le_half_pi
  admissible_beta_le_half_pi)
export DirichletKernel (dirichletKernel abs_dirichletKernel_le_one
  dirichletKernel_two_pi abs_dirichletKernel_lattice)
export Motor (TransParams OmegaParams omegaTorsion omegaTrans omegaBiv expTrans rotorTorsion motor
  omegaTrans_sq omegaTorsion_reverse expTrans_unitary rotor_unitary motor_unitary
  reverse_mul_of_mul_reverse exp_of_sq_one exp_of_sq_neg_one
  exp_omegaTrans expTrans_mul exp_omegaBiv_eq_motor_of_commute
  commutator_omegaTorsion_omegaTrans_mem_span
  commutator_omegaTrans_commutator_torsion_trans
  motorPath bch2Path bch3Path motor_bch2_jet motor_bch3_jet exists_omegaBiv_ne_motor)
export MotorGroup (adL adL_apply exp_apply_mem_of_forall_mem exp_smul_mul_mul_exp_neg_smul
  exp_mul_mul_exp_neg_mem sandwich_exp_mem
  sandwich_exp_smul_eq_exp_ad hasDerivAt_sandwich_exp_smul
  sandwich_rotorTorsion_mem_nullSpan sandwich_rotorTorsion_mem_lorentzSpan
  sandwich_rotorTorsion_mem_poincareSpan
  exists_omegaTrans_eq_of_mem_nullSpan exists_omegaTorsion_eq_of_mem_lorentzSpan
  exists_sandwich_rotorTorsion_omegaTrans exists_sandwich_rotorTorsion_expTrans
  sandwichAlgHom sandwich_exp exists_sandwich_rotorTorsion_rotorTorsion
  reverse_rotorTorsion exists_motor_mul exists_expTrans_mul_rotorTorsion expTrans_zero
  exists_motor_pow
  conjPath nullDress exists_exp_add_eq_exp_mul_one_add
  exists_exp_omegaBiv_eq_rotorTorsion_mul_expTrans exists_dressed_translation_ne
  exp_omegaBiv_unitary
  smul_mul_smul_comm_of_commute cyclic_smul_mul hyperbolic_smul_cyclic_smul_same)
export Sandwich (sandwich sandwich_one sandwich_smul sandwich_add sandwich_comp sandwich_reverse
  sandwich_mul sandwich_sq sandwich_minkowskiVector_sq
  rotorTorsion_pureBoost_closed sandwich_pureBoost_ι0 sandwich_pureBoost_ι1
  sandwich_pureBoost_ι2 sandwich_pureBoost_lightlike_plus sandwich_pureBoost_lightlike_minus
  rotorTorsion_pureRotation_closed sandwich_pureBoost_null0 sandwich_pureBoost_null3
  sandwich_pureBoost_expTrans
  reverse_rotorTorsion_pureBoost_eq rotorTorsion_pureBoost_mul boostConjLambda
  sandwich_pureRotation1_null3 sandwich_pureRotation1_expTrans
  sandwich_pureRotation1_null3_ne_of_sin)
export UnitGroup (discreteRotor DiscreteUnit DiscreteRotorImage discreteUnit_finite
  discreteRotorImage_finite reverse_discreteRotor discreteRotor_mul_reverse
  negTorsionParams AdmissibleRotorImage admissibleRotorImage_subset_discrete
  admissibleRotorImage_finite)
export Invariant (J J5 JNormalized counterExampleParams J_coef JNormalized_coef J5_eq killingForm
  omegaTorsionGeneratorKilling omegaTorsionGeneratorKilling_eq
  omegaTorsion_killing_vs_param paper_appendix_killing_coeff_false
  one_sixteenth_omegaKilling_eq J_eq_four_times_one_sixteenth_omegaKilling
  axis_sq_diff_eq sq_diff_le_half_pi_sq sq_diff_eq_half_pi_sq_iff
  euclideanForm mass massNormalized mass_coef mass_nonneg mass_eq_zero_iff
  J_eq_zero_of_mass_eq_zero J_dagger JNormalized_dagger mass_dagger
  massNormalized_coef massNormalized_nonneg
  massNormalized_eq_zero_iff JNormalized_eq_zero_of_massNormalized_eq_zero
  abs_J_le_mass abs_J_eq_mass_iff J_add_mass mass_sub_J
  J_eq_mass_of_forall_beta_eq_zero abs_JNormalized_le_massNormalized
  sq_sum_le_half_pi_sq sq_sum_eq_half_pi_sq_iff
  mass_bound_raw_continuous massNormalized_bound_continuous
  balancedRay JNormalized_balancedRay mass_balancedRay massNormalized_balancedRay
  mass_balancedRay_pos isAdmissibleContinuous_balancedRay
  not_admissible_balancedRay_of_one_lt JNormalized_zero_not_implies_vacuum
  IsPureHyperbolic IsPureElliptic
  IsSpatialTrans IsBoundedTrans J5_unbounded J5_bound_spatial
  torsion_bound_raw torsion_bound_raw_continuous_pi_sq torsion_bound_raw_pi_sq
  torsion_bound torsion_bound_continuous JNormalized_extremal JNormalized_extremal_neg
  abs_JNormalized_eq_one_iff exists_admissible_JNormalized
  torsion_bound_naive_false)
export Amplification (scaleTorsion pureBoost pureRotation1 pureBoost_scale_real pureBoost_scale
  omegaTorsion_pureRotation1 rotorTorsion_pureRotation1
  J_scale JNormalized_scale mass_scale massNormalized_scale scaleTorsion_balancedRay
  J_pureBoost JNormalized_pureBoost JNormalized_pureBoost_nonneg
  J_pow_amplify JNormalized_pow_amplify rotorTorsion_pureBoost_pow
  isAdmissibleContinuous_pureBoost_iff)
export ModularAmplification (windingCoord amplifyDiscrete windingTotal amplifiedParams
  ModularAmplificationWitness modularWitness_example
  modularWitness_of_pureBoost modularWitness_of_pureBoost_winding
  modularWitness_four_le modularWitness_empty_of_lt_four modularWitness_empty_of_eq_three
  latticeMismatch_pureBoost latticeMismatch_ne_zero_of_winding_pureBoost
  isAdmissible_of_pureBoost_n0_le isAdmissible_amplifyDiscrete_of_pureBoost_smul_n0
  mul_val_eq_val_add_winding scale_angle_eq_mod_plus_winding
  J_scale_eq_J_amplified_add_error JNormalized_scale_eq_JNormalized_amplified_add_error
  windingCoord_lt windingCoord_pos_iff
  admissible_scale_implies_windingTotal_eq_zero
  windingTotal_ne_zero_implies_not_admissible_scale
  ModularAmplificationWitness.not_admissible_real_scale
  ConformalGaugeAdmissible IsPureBoostSeed
  windingTotal_pureBoost windingTotal_pureBoost_ne_zero_iff
  pureBoostSeedOfRapidity pureBoostSeedOfRapidity_isPureBoost
  quantizeRapidity_of_lt_two_pi windingTotal_ne_zero_of_rapidity_ge
  windingTotal_eq_zero_of_rapidity_lt
  not_exists_modularWitness_of_rapidity_lt
  not_exists_modularWitness_of_balanced_gap)
export Periodicity (exp_cyclic_add_int_mul_two_pi exp_cyclic_two_pi
  exp_hyperbolic_add_two_pi_ne exp_hyperbolic_two_pi_ne_one hyperbolic_ne_zero)
export Continuum (AdmissibleContinuous exists_discrete_approx exists_discrete_approx_J
  lattice_in_interval dense_discrete_JNormalized)
export RelativeRotor (omegaUsual omegaDual rotorUsual rotorDual relativeRotor
  omegaTorsion_eq_add rotorUsual_unitary rotorDual_unitary relativeRotor_eq_one_iff
  axisParams rotorTorsion_axis_factor commute_hyperbolic_cyclic_same
  paper_unrestricted_commutator_false PaperVacuumSync
  relativeRotor_of_paperVacuumSync paperVacuumSync_axis
  not_paperVacuumSync_pureBoost J_axisParams_balanced
  J_zero_not_relativeRotor_one)

/-- Regression: normalised Dirichlet kernel is bounded by 1. -/
example {N : ℕ} (hN : N ≠ 0) (θ : ℝ) :
    |dirichletKernel N θ| ≤ 1 :=
  abs_dirichletKernel_le_one hN θ

/-- Regression: the relative rotor is the identity iff the two rotors coincide. -/
example (p : Operations.TorsionParams) :
    relativeRotor p = 1 ↔ rotorDual p = rotorUsual p :=
  relativeRotor_eq_one_iff p

/-- Regression: vanishing \(J\) does not force \(\Omega=1\). -/
example : ∃ p : Operations.TorsionParams,
    Invariant.J p = 0 ∧ 0 < Invariant.mass p ∧ relativeRotor p ≠ 1 :=
  J_zero_not_relativeRotor_one

/-- Regression: cyclic generators give a \(2\pi\)-periodic exponential. -/
example (a : Fin 3) :
    NormedSpace.exp ((2 * Real.pi) • hyperbolic a) ≠ (1 : PGA) ∧
      NormedSpace.exp ((2 * Real.pi) • cyclic a) = 1 :=
  ⟨exp_hyperbolic_two_pi_ne_one a, exp_cyclic_two_pi a⟩

/-- Regression: the Banach exponential of a null generator truncates. -/
example (p : Motor.TransParams) :
    NormedSpace.exp (omegaTrans p) = expTrans p :=
  exp_omegaTrans p

/-- Regression: translators multiply by adding coefficients. -/
example (p q : Motor.TransParams) :
    expTrans p * expTrans q = expTrans ⟨fun μ => p.lambda μ + q.lambda μ⟩ :=
  expTrans_mul p q

/-- Regression: null translations are ad-invariant under the radial boost. -/
example (μ : Fin 4) :
    commutator (hyperbolic 0) (null μ) ∈
      Submodule.span ℝ (Set.range (null : Fin 4 → PGA)) :=
  commutator_hyperbolic0_null_mem_span μ

/-- Regression: a pure boost conjugates a translator to a translator. -/
example (φ : ℝ) (p : Motor.TransParams) :
    sandwich (rotorTorsion (pureBoost φ)) (expTrans p) =
      expTrans ⟨boostConjLambda φ p.lambda⟩ :=
  sandwich_pureBoost_expTrans φ p

/-- Regression: commuting torsion and translation give \(\exp(\Omega_{\mathrm{biv}})=RT\). -/
example (p : Motor.OmegaParams)
    (h : Commute (omegaTorsion p.torsion) (omegaTrans p.trans)) :
    NormedSpace.exp (omegaBiv p) = motor p :=
  exp_omegaBiv_eq_motor_of_commute p h

/-- Regression: every Lorentz–null bracket remains translational. -/
example (a : Fin 3) (μ : Fin 4) :
    commutator (hyperbolic a) (null μ) ∈ nullSpan ∧
      commutator (cyclic a) (null μ) ∈ nullSpan :=
  ⟨commutator_hyperbolic_null_mem_span a μ, commutator_cyclic_null_mem_span a μ⟩

/-- Regression: same-axis Lorentz generators commute; adjacent axes close. -/
example (a : Fin 3) :
    commutator (hyperbolic a) (hyperbolic a) = 0 ∧
      commutator (cyclic a) (cyclic (a + 1)) = (2 : ℝ) • cyclic (a + 2) ∧
        commutator (hyperbolic a) (cyclic (a + 1)) =
          (2 : ℝ) • hyperbolic (a + 2) := by
  have hne : a ≠ a + 1 := by fin_cases a <;> decide
  refine ⟨?_, ?_, ?_⟩
  · simp [commutator_hyperbolic_hyperbolic]
  · simp [commutator_cyclic_cyclic, hne]
  · simp [commutator_hyperbolic_cyclic, hne]

/-- Regression: the Lorentz span and the Poincaré span are closed under the bracket,
and the null span is an abelian ideal of the latter. -/
example {x y : PGA} (hx : x ∈ poincareSpan) (hy : y ∈ poincareSpan) (hn : y ∈ nullSpan) :
    commutator x y ∈ poincareSpan ∧ commutator x y ∈ nullSpan :=
  ⟨commutator_mem_poincareSpan hx hy, commutator_poincare_null_mem_nullSpan hx hn⟩

example {x y : PGA} (hx : x ∈ lorentzSpan) (hy : y ∈ lorentzSpan) :
    commutator x y ∈ lorentzSpan :=
  commutator_mem_lorentzSpan hx hy

/-- Regression: duality is a complex structure on the Lorentz sector and the bracket is
complex-bilinear for it; hence boosts bracket to minus the rotation bracket. -/
example {x y : PGA} (hx : x ∈ lorentzSpan) (hy : y ∈ lorentzSpan) :
    dual (dual x) = -x ∧ dual x ∈ lorentzSpan ∧
      commutator (dual x) (dual y) = -commutator x y :=
  ⟨dual_dual x, dual_mem_lorentzSpan hx, commutator_dual_dual hx hy⟩

example (a : Fin 3) :
    commutator (hyperbolic a) (hyperbolic (a + 1)) = -((2 : ℝ) • cyclic (a + 2)) := by
  have hne : a ≠ a + 1 := by fin_cases a <;> decide
  simp [commutator_hyperbolic_hyperbolic_cyclic, hne]

/-- Regression: every Lorentz element is a rotation plus a dualised rotation. -/
example {x : PGA} (hx : x ∈ lorentzSpan) :
    ∃ u ∈ cyclicSpan, ∃ v ∈ cyclicSpan, x = u + dual v :=
  mem_lorentzSpan_iff.mp hx

/-- Regression: duality acts on torsion parameters as the quarter-turn `(α,β) ↦ (β,-α)`,
reversing `J` and preserving the mass. -/
example (p : Operations.TorsionParams) :
    dual (omegaTorsion p) = omegaTorsion (dualParams p) ∧
      Invariant.J (dualParams p) = -Invariant.J p ∧
        Invariant.mass (dualParams p) = Invariant.mass p :=
  ⟨dual_omegaTorsion p, J_dualParams p, mass_dualParams p⟩

/-- Regression: boost scalars on every axis commute. -/
example (a : Fin 3) (x y : ℝ) :
    (x • hyperbolic a) * (y • hyperbolic a) =
      (y • hyperbolic a) * (x • hyperbolic a) :=
  hyperbolic_smul_mul a x y

/-- Regression: mixed motors are not the Banach exponential of \(\Omega_{\mathrm{biv}}\). -/
example : ∃ p : Motor.OmegaParams, NormedSpace.exp (omegaBiv p) ≠ motor p :=
  exists_omegaBiv_ne_motor

/-- Regression: the ordered product and the second-order BCH exponential share a 2-jet. -/
example (p : Motor.OmegaParams) :
    motorPath p 0 = bch2Path p 0 ∧
      deriv (motorPath p) 0 = deriv (bch2Path p) 0 ∧
      iteratedDeriv 2 (motorPath p) 0 = iteratedDeriv 2 (bch2Path p) 0 :=
  motor_bch2_jet p

/-- Regression: the ordered product and the third-order BCH exponential share a 3-jet. -/
example (p : Motor.OmegaParams) :
    iteratedDeriv 3 (motorPath p) 0 = iteratedDeriv 3 (bch3Path p) 0 :=
  (motor_bch3_jet p).2.2.2

/-- Regression: conjugation by `exp(tΩ)` is `exp(t · ad Ω)`; hence `ad`-invariant subspaces
are invariant under the sandwich. -/
example (Ω x : PGA) (t : ℝ) :
    NormedSpace.exp (t • Ω) * x * NormedSpace.exp ((-t) • Ω) =
      NormedSpace.exp (t • adL Ω) x :=
  exp_smul_mul_mul_exp_neg_smul Ω x t

/-- Regression: every torsion rotor conjugates a null translator to a null translator,
and a torsion rotor to a torsion rotor. -/
example (t : Operations.TorsionParams) (p : Motor.TransParams) (s : Operations.TorsionParams) :
    (∃ q : Motor.TransParams, sandwich (rotorTorsion t) (expTrans p) = expTrans q) ∧
      ∃ s' : Operations.TorsionParams,
        sandwich (rotorTorsion t) (rotorTorsion s) = rotorTorsion s' :=
  ⟨exists_sandwich_rotorTorsion_expTrans t p, exists_sandwich_rotorTorsion_rotorTorsion t s⟩

/-- Regression: the motor product law in semidirect form. -/
example (p q : Motor.OmegaParams) :
    ∃ r : Motor.TransParams,
      motor p * motor q = rotorTorsion p.torsion * rotorTorsion q.torsion * expTrans r :=
  exists_motor_mul p q

/-- Regression: powers of a mixed motor amplify only through the torsion rotor. -/
example (p : Motor.OmegaParams) (n : ℕ) :
    ∃ r : Motor.TransParams, motor p ^ n = rotorTorsion p.torsion ^ n * expTrans r :=
  exists_motor_pow p n

/-- Regression: `exp(Ω_biv)` is a motor with the same rotor and a dressed translation, and
the dressed translation differs from `Ω_trans` in general. -/
example (p : Motor.OmegaParams) :
    ∃ q : Motor.TransParams,
      NormedSpace.exp (omegaBiv p) = rotorTorsion p.torsion * expTrans q :=
  exists_exp_omegaBiv_eq_rotorTorsion_mul_expTrans p

example : ∃ (p : Motor.OmegaParams) (q : Motor.TransParams),
    NormedSpace.exp (omegaBiv p) = rotorTorsion p.torsion * expTrans q ∧ q ≠ p.trans :=
  exists_dressed_translation_ne

/-- Regression: same-axis boost/rotation scalars commute on every axis. -/
example (a : Fin 3) (x y : ℝ) :
    (x • hyperbolic a) * (y • cyclic a) = (y • cyclic a) * (x • hyperbolic a) ∧
      (x • cyclic a) * (y • cyclic a) = (y • cyclic a) * (x • cyclic a) :=
  ⟨hyperbolic_smul_cyclic_smul_same a x y, cyclic_smul_mul a x y⟩

end DstDiophantine
