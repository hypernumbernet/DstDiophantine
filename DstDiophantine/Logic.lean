import DstDiophantine.Logic.TruthValue
import DstDiophantine.Logic.Connective
import DstDiophantine.Logic.Interpretation
import DstDiophantine.Logic.Amplitude
import DstDiophantine.Logic.Order
import DstDiophantine.Logic.Geometric
import DstDiophantine.Logic.Formula
import DstDiophantine.Logic.Valuation
import DstDiophantine.Logic.Consequence
import DstDiophantine.Logic.Example.FixedPoint
import DstDiophantine.Logic.Example.Explosion
import DstDiophantine.Logic.Example.NotFalse
import DstDiophantine.Logic.Regime
import DstDiophantine.Logic.Example.Regime
import DstDiophantine.Logic.Example.BealRegime
import DstDiophantine.Logic.Example.FermatRegime
import DstDiophantine.Logic.DiscreteAmplitude
import DstDiophantine.Logic.Dynamics
import DstDiophantine.Logic.Winding
import DstDiophantine.Logic.MotorProp
import DstDiophantine.Logic.BalancedResidual
import DstDiophantine.Logic.Quantum.Separation
import DstDiophantine.Logic.Quantum.DualSector
import DstDiophantine.Logic.Quantum.Quaternion
import DstDiophantine.Logic.Quantum.Spinor
import DstDiophantine.Logic.Quantum.DualRodrigues
import DstDiophantine.Logic.Quantum.UsualRodrigues
import DstDiophantine.Logic.Quantum.UsualRotor
import DstDiophantine.Logic.Quantum.QuantumLogic
import DstDiophantine.Logic.Quantum.Dictionary
import DstDiophantine.Logic.Quantum.Spinor10
import DstDiophantine.Logic.Quantum.StringSpectrum
import DstDiophantine.Logic.Quantum.MinimalIdeal
import DstDiophantine.Logic.Quantum.CompositeProjector
import DstDiophantine.Logic.Quantum.LeftIdealDim
import DstDiophantine.Logic.Quantum.Dirac
import DstDiophantine.Logic.Quantum.DiracSpinor
import DstDiophantine.Logic.Quantum.DiracEquation
import DstDiophantine.Logic.Quantum.DeBroglie
import DstDiophantine.Logic.Quantum.LevelMatch
import DstDiophantine.Logic.Quantum.StringCompare
import DstDiophantine.Algebra.Invariant
import DstDiophantine.Algebra.Cl91
import DstDiophantine.Algebra.LorentzDim
import Mathlib.Data.Matrix.Basic

/-!
# Dual Spacetime 4-valued logic (D4L) — parallel track

The project's logic. A proposition is an admissible torsion configuration.
Measurement is the already-proved PGA invariant `JNormalized`; collapse
yields four labels. The amplitude layer (connectives, orders, Killing
geometry) and the dual Hilbert layer (`Logic.Quantum`) belong to the
same logic.

**Not** re-exported from `DstDiophantine.Basic`, so the Diophantine path
does not depend on these modules (same policy as `DstDiophantine.Gravity`
and `DstDiophantine.CGA`).

## Contents

* `Logic.Amplitude` — admissible configuration as the primary carrier;
  second observable `mass`; predicates `IsVacuum` / `IsBalancedMassive`
  (not a fifth label)
* `Logic.TruthValue` — four states from `JNormalized ∈ [-1,1]`
* `Logic.Connective` — min/max/neg, non-explosion
* `Logic.Interpretation` — usual–dual swap is signed negation
* `Logic.Order` — height and information preorders (not Belnap FOUR)
* `Logic.Geometric` — Killing overlap, bivector commutator, rotor composition
* `Logic.Quantum` — dual Hilbert layer of D4L (sectors, quaternion table,
  `ℂ²`, subspace lattice, internal dictionary, Dirac `ℂ⁴` representation,
  usual-sector hyperbolic Rodrigues, Weyl chirality, momentum-space Dirac
  equation as the Clifford square of the Minkowski quadratic,
  on-shell Weyl construction recovering the rest pair \((u,iu)\),
  longitudinal boost of that pair, dual-rotor character, spinor
  amplitude, relative dual-rotor composition and noncommutative
  interference)
  plus the string-comparison slice (`Cl91`, MW16, spectrum labels,
  level-match dictionary)
* `Logic.Formula` / `Valuation` / `Consequence` — syntax, designated
  `HoldsT` / `HoldsNotF`, two-valued fragments, entailment
* `Logic.Regime` — discrete proof-status algebra and implication table
* `Logic.Example` — fixed-point, non-explosion, `Jnorm < 1`,
  Diophantine regimes, Beal residual atlas, dual-axis FLT atlas
  (complementarity is the existing `ℂ²` lattice theorems)
* `Logic.DiscreteAmplitude` — torus amplitudes; `¬4 ∣ N` forbids `F`
* `Logic.Dynamics` — amplification as a partial map on labels;
  vacuum is a fixed point; balanced massive can stay `T` or leave the cone
  invisibly to `classify?`
* `Logic.Winding` — height and winding are incompatible measurements
* `Logic.MotorProp` — L2: additive motor ≠ multiplicative amplitude
* `Logic.BalancedResidual` — L3: `BalancedResidualClass` vs window seeds

Unconditional FLT / Beal / a Gödel-refutation are **not** claimed.
The amplitude layer is not a Hilbert space, a Born rule, or an
orthomodular lattice. `DualSpinor ≃ ℂ²` and its subspace lattice belong
to the same logic; their operations are not identified with the four
labels or with `min`/`max`. See `Logic.Quantum.Separation` and
`Logic.Quantum.Dictionary`.
-/

namespace DstDiophantine

namespace Logic

open Invariant Operations Generators Submodule

/-- Regression: every D4L state is realised by an admissible configuration. -/
example (tv : TruthValue) :
    ∃ (p : TorsionParams) (h : Admissible.IsAdmissibleContinuous p), ofParams p h = tv :=
  exists_ofParams tv

/-- Regression: dual-swap flips `JNormalized`. -/
example (p : TorsionParams) : JNormalized (daggerParams p) = -JNormalized p :=
  JNormalized_dagger p

/-- Regression: conjunction with negation never saturates `F`. -/
example {j : ℝ} (hj : |j| ≤ 1) :
    classifyOfMem (conjJ j (negJ j)) (abs_conj_neg_le hj) ≠ .F :=
  classify_conj_neg_ne_F hj

/-- Regression: every label is realised by an amplitude. -/
example (tv : TruthValue) : ∃ a : Amplitude, a.collapse = tv :=
  exists_amplitude tv

/-- Regression: adjoint is involutive and flips the observable. -/
example (a : Amplitude) : a.adjoint.adjoint = a :=
  a.adjoint_involutive

example (a : Amplitude) : a.adjoint.measure = -a.measure :=
  a.measure_adjoint

/-- Regression: information bottom is `T`; tops are the walls `±1`. -/
example {j : ℝ} (hj : |j| ≤ 1) :
    classifyOfMem j hj = .T ↔ ∀ k : ℝ, |k| ≤ 1 → InfoLE j k :=
  classify_T_iff_info_bottom hj

example {j : ℝ} (hj : |j| ≤ 1) :
    (∀ k : ℝ, |k| ≤ 1 → InfoLE k j) ↔ j = 1 ∨ j = -1 :=
  info_top_iff hj

/-- Regression: Killing overlap is symmetric; self-overlap is `16 J`. -/
example (p q : TorsionParams) : overlap p q = overlap q p :=
  overlap_symm p q

example (p : TorsionParams) : overlap p p = 16 * J p :=
  overlap_self p

/-- Regression: distinct-axis torsion bivectors need not commute. -/
example : interfere axis0Boost axis1Rotation ≠ 0 :=
  interfere_axis0_axis1_ne_zero

/-- Regression: state-level negation is not a function of the four labels. -/
example :
    ∃ j₁ j₂ : ℝ, ∃ h₁ : |j₁| ≤ 1, ∃ h₂ : |j₂| ≤ 1,
      classifyOfMem j₁ h₁ = .B ∧ classifyOfMem j₂ h₂ = .B ∧
        classifyOfMem (negJ j₁) (by simpa [negJ, abs_neg] using h₁) ≠
          classifyOfMem (negJ j₂) (by simpa [negJ, abs_neg] using h₂) :=
  neg_not_a_function_of_TruthValue

/-- Regression: Killing form is indefinite, hence not a Hilbert inner product. -/
example :
    (∃ p : TorsionParams, 0 < killingForm p p) ∧
      (∃ q : TorsionParams, killingForm q q < 0) :=
  killingForm_indefinite

/-- Regression: self-overlap is not a Born probability. -/
example : ¬ ∀ p : TorsionParams, 0 ≤ overlap p p :=
  overlap_self_not_born_probability

/-- Regression: dual-sector cyclic generators satisfy `I J = K`. -/
example : cyclic 0 * cyclic 1 = cyclic 2 :=
  cyclic_zero_mul_one

/-- Regression: dual-sector pairing is negative definite. -/
example {β : DualRapidity} (h : killingForm (ofDual β) (ofDual β) = 0) : β = 0 :=
  killingForm_ofDual_neg_def h

/-- Regression: `ℂ²` subspace lattice is orthomodular and not distributive. -/
example {A B : QProp} (h : A ≤ B) : A ⊔ Aᗮ ⊓ B = B :=
  orthomodular h

example :
    (lineE0 ⊓ (lineE1 ⊔ lineD) : QProp) ≠
      ((lineE0 ⊓ lineE1) ⊔ (lineE0 ⊓ lineD) : QProp) :=
  not_distributive

/-- Regression: four D4L labels are not four orthogonal rays in `ℂ²`. -/
example :
    ¬ ∃ L : TruthValue → QProp,
        (∀ tv, Module.finrank ℂ (L tv) = 1) ∧
          (∀ tv₁ tv₂, tv₁ ≠ tv₂ → L tv₁ ⟂ L tv₂) :=
  four_labels_not_orthogonal_pvm

/-- Regression: wall two-valued logic cannot host `P = ¬P`. -/
example : ¬ ∃ v : Valuation,
    IsWallTwo (v.assign 0) ∧
      IsNegFixed ((Formula.atom 0).eval v.assign) :=
  not_exists_wall_negFixed

/-- Regression: D4L realises the negation fixed point at `T`. -/
example : ∃ v : Valuation, IsNegFixed ((Formula.atom 0).eval v.assign) :=
  exists_negFixed_valuation

/-- Regression: `{P, ¬P}` does not explode to an unrelated atom. -/
example : ¬ EntailsT (contradict (Formula.atom 0)) (Formula.atom 1) :=
  contradict_not_entailsT_atom

example : ¬ EntailsNotF (contradict (Formula.atom 0)) (Formula.atom 1) :=
  contradict_not_entailsNotF_atom

/-- Regression: named two-valued ∩ not-`F` is only `T`; D4L has three labels. -/
example {j : ℝ} : IsNamedTwo j ∧ HoldsNotF j ↔ j = 0 :=
  namedTwo_notF_only_T

example :
    (∃ (j : ℝ) (hj : |j| ≤ 1), classifyOfMem j hj = .T ∧ HoldsNotF j) ∧
      (∃ (j : ℝ) (hj : |j| ≤ 1), classifyOfMem j hj = .U ∧ HoldsNotF j) ∧
        (∃ (j : ℝ) (hj : |j| ≤ 1), classifyOfMem j hj = .B ∧ HoldsNotF j) :=
  exists_three_notF_labels

/-- Regression: named two-valued logic cannot host the three-layer split. -/
example :
    ¬ ∃ v : RegimeValuation,
        IsNamedRegime (v.assign 0) ∧
          IsNamedRegime (v.assign 1) ∧
            IsNamedRegime (v.assign 2) ∧
              (RegimeFormula.atom 2).eval v.assign = .U :=
  not_exists_named_three_layer

/-- Regression: D4L realises core `T`, diagnostic `F`, live `U`. -/
example :
    ∃ v : RegimeValuation,
      (RegimeFormula.atom 0).eval v.assign = .T ∧
        (RegimeFormula.atom 1).eval v.assign = .F ∧
          (RegimeFormula.atom 2).eval v.assign = .U ∧
            (RegimeFormula.atom 3).eval v.assign = .U :=
  exists_three_layer_valuation

/-- Regression: core does not T-entail a classical conjecture. -/
example : ¬ EntailsTR {RegimeFormula.atom 0} (RegimeFormula.atom 3) :=
  core_not_entailsTR_conjecture

/-- Regression: window ∧ ill-posed NoGo does not force the conjecture. -/
example :
    ¬ EntailsNotFR {RegimeFormula.atom 0, RegimeFormula.atom 1}
        (RegimeFormula.atom 3) :=
  window_nogo_not_entailsNotFR_conjecture

/-- Regression: Beal atlas realises closed `T`, diagnostic `F`, bookkeeping `B`, live `U`. -/
example :
    ∃ v : RegimeValuation,
      sliceFLT.eval v.assign = .T ∧
        diagModular.eval v.assign = .F ∧
          bookRealization.eval v.assign = .B ∧
            liveMordell.eval v.assign = .U ∧
              liveOdd.eval v.assign = .U ∧
                liveAllDistinct.eval v.assign = .U ∧
                  liveUnequalOdd.eval v.assign = .U ∧
                    bealConjecture.eval v.assign = .U ∧
                      sliceNN5.eval v.assign = .T :=
  exists_beal_atlas_valuation

/-- Regression: closed Beal slices do not T-entail classical Beal. -/
example :
    ¬ EntailsTR {sliceFLT, sliceDM, sliceAbsOne, sliceFourth, sliceNN5}
        bealConjecture :=
  closed_slices_not_entailsTR_beal

/-- Regression: promoting one live residual, or every artefact, still fails. -/
example :
    ¬ EntailsTR (bealClosedSliceAtomSet ∪ {liveMordell}) bealConjecture ∧
      ¬ EntailsTR bealArtefactAtomSet bealConjecture :=
  ⟨promote_liveMordell_not_entailsTR_beal, artefacts_not_entailsTR_beal⟩

/-- Regression: FLT atlas realises closed `T`, diagnostic `F`, live `U`. -/
example :
    ∃ v : RegimeValuation,
      sliceCore.eval v.assign = .T ∧
        sliceLp.eval v.assign = .T ∧
          diagSingleAxisModular.eval v.assign = .F ∧
            diagBalancedSeed.eval v.assign = .F ∧
              liveMixedMotor.eval v.assign = .U ∧
                fltConjecture.eval v.assign = .U :=
  exists_fermat_atlas_valuation

/-- Regression: closed FLT slices do not T-entail classical FLT. -/
example : ¬ EntailsTR {sliceCore, sliceLp} fltConjecture :=
  closed_slices_not_entailsTR_flt

/-- Regression: closed slices packaged with a live residual stay live. -/
example : meetRList (closedSliceStatuses ++ [.U]) = .U :=
  meetRList_closed_with_live

/-- Regression: L2 pure-translation torsion amplitude is vacuum. -/
example :
    (⟨zeroTorsion, isAdmissibleContinuous_zeroTorsion⟩ : Amplitude).IsVacuum :=
  pure_translation_torsion_isVacuum

/-- Regression: L2 additive vacuum ≠ multiplicative balanced massive. -/
example :
    vacuumAmplitude.IsVacuum ∧ balancedAmplitude.IsBalancedMassive ∧
      ¬ vacuumAmplitude.IsBalancedMassive ∧ ¬ balancedAmplitude.IsVacuum :=
  additive_vacuum_ne_multiplicative_balanced

/-- Regression: L3 balanced residual class excludes window seeds. -/
example : BalancedResidualClass balancedAmplitude ∧ ¬ BalancedResidualClass halfWindowSeed :=
  ⟨balancedAmplitude_mem_balancedResidualClass, halfWindowSeed_not_balanced⟩

/-- Regression: `U → T` is not designated. -/
example : impR .U .T = .U :=
  impR_U_T

/-- Regression: regime `s ∧ ¬s` never saturates `F`. -/
example (s : TruthValue) : conjR s (negR s) ≠ .F :=
  conjR_negR_ne_F s

/-- Regression: `¬ 4 ∣ N` forbids discrete `F`. -/
example {N : ℕ} [NeZero N] (h4 : ¬ 4 ∣ N) (a : DiscreteAmplitude N) :
    a.collapse ≠ .F :=
  DiscreteAmplitude.collapse_ne_F_of_not_four_dvd h4 a

/-- Regression: a `U` seed can be scaled onto `F`. -/
example {k : ℕ} (hk : 2 ≤ k) :
    (⟨Amplification.scaleTorsion (k : ℝ) (seedU_to_F hk).params,
        seedU_to_F_scale_admissible hk⟩ : Amplitude).collapse = .F :=
  seedU_to_F_scales_to_F hk

/-- Regression: label `T` splits into vacuum and balanced massive. -/
example :
    (∃ a : Amplitude, a.collapse = .T ∧ a.IsVacuum) ∧
      (∃ b : Amplitude, b.collapse = .T ∧ b.IsBalancedMassive) :=
  T_splits_vacuum_and_balancedMassive

/-- Regression: height cannot exceed mass. -/
example (a : Amplitude) : |a.measure| ≤ a.massNormalized :=
  a.abs_measure_le_massNormalized

/-- Regression: vanishing height is not axiswise balance. -/
example :
    ∃ a : Amplitude, a.collapse = .T ∧ 0 < a.mass ∧ ¬ IsAxiswiseBalanced a.params :=
  T_has_cross_axis_cancellation

/-- Regression: Gödel residuum of `min` designates `U → T` as `T`. -/
example : HoldsT (residuumJ (1 / 2 : ℝ) 0) :=
  residuumJ_U_T_holdsT

/-- Regression: Gödel residuum of `min` sends `B → T` to `F`. -/
example :
    classifyOfMem (residuumJ (-1 / 2 : ℝ) 0) (by simp [residuumJ_B_T]) = .F :=
  residuumJ_B_T_eq_F

/-- Regression: regime implication disagrees with the residuum at `U → T` and `B → T`. -/
example :
    residuumJ (amplitudeRep .U) (amplitudeRep .T) = 0 ∧ impR .U .T = .U ∧
      residuumJ (amplitudeRep .B) (amplitudeRep .T) = 1 ∧ impR .B .T = .U :=
  ⟨residuum_U_T_ne_impR.1, residuum_U_T_ne_impR.2,
    residuum_B_T_ne_impR.1, residuum_B_T_ne_impR.2⟩

/-- Regression: when `4 ∣ N`, both discrete walls are attained. -/
example : (discreteF (by decide : 4 ∣ 4)).collapse = .F ∧
    (discreteB (by decide : 4 ∣ 4)).collapse = .B :=
  ⟨discreteF_collapse (by decide), discreteB_collapse (by decide)⟩

/-- Regression: complementary rays exist in `ℂ²`. -/
example : lineE0 ⟂ lineE1 :=
  lineE0_isOrtho_lineE1

/-- Regression: the dual Hilbert layer has infinitely many atoms. -/
example : Infinite {A : QProp // Module.finrank ℂ A = 1} :=
  infinite_one_dim_subspaces

/-- Regression: vacuum stays vacuum under admissible scaling. -/
example {k : ℕ} (h : Admissible.IsAdmissibleContinuous
    (Amplification.scaleTorsion (k : ℝ) vacuumAmplitude.params)) :
    (⟨Amplification.scaleTorsion (k : ℝ) vacuumAmplitude.params, h⟩ : Amplitude).IsVacuum :=
  scale_vacuum_stays_vacuum vacuumAmplitude_isVacuum h

/-- Regression: a small balanced seed stays balanced massive after `k`-fold scaling. -/
example {k : ℕ} (hk : 1 ≤ k) :
    (⟨Amplification.scaleTorsion (k : ℝ) (seedBalanced_stays hk).params,
        seedBalanced_stays_scale_admissible hk⟩ : Amplitude).IsBalancedMassive :=
  seedBalanced_stays_scales_balanced hk

/-- Regression: full balanced ray exits the cone under 2-fold scaling. -/
example :
    ¬ Admissible.IsAdmissibleContinuous
        (Amplification.scaleTorsion (2 : ℝ) balancedAmplitude.params) :=
  balancedAmplitude_exits_not_admissible

/-- Regression: that cone exit is invisible to the signed-height classifier. -/
example :
    classify? (JNormalized (Amplification.scaleTorsion (2 : ℝ) balancedAmplitude.params)) =
      some .T :=
  balancedAmplitude_scale_classify_T

/-- Regression: height and winding are incompatible measurements. -/
example {N : ℕ} [NeZero N] (k : ℕ) (t : Discrete.DiscreteTorsion N) :
    ¬ (Admissible.IsAdmissibleContinuous
          (Amplification.scaleTorsion (k : ℝ) (Discrete.toTorsionParams t)) ∧
        ModularAmplification.windingTotal k t ≠ 0) :=
  not_both_admissibleScale_and_winding k t

/-- Regression: Cl(3,1) and Cl(9,1) have different real dimensions. -/
example : Module.finrank ℝ Cl31 = 16 ∧ Module.finrank ℝ Cl91 = 1024 :=
  ⟨Cl91.finrank_cl31, Cl91.finrank_cl91⟩

/-- Regression: the algebras are not isomorphic. -/
example : ¬ Nonempty (Cl31 ≃ₐ[ℝ] Cl91) :=
  not_cl31_algEquiv_cl91

/-- Regression: working chirality / spinor projectors are idempotent. -/
example : chiralityL * chiralityL = chiralityL ∧
    chiralityR * chiralityR = chiralityR ∧
      spinorIdem * spinorIdem = spinorIdem :=
  ⟨chiralityL_sq, chiralityR_sq, spinorIdem_sq⟩

/-- Regression: paper `(1-i)/2` is not idempotent when `i² = -1`. -/
example : paperChiralityL * paperChiralityL ≠ paperChiralityL :=
  paper_chirality_rejected

/-- Regression: paper composite `P_spin P_R` is not idempotent. -/
example : (spinorIdem * chiralityR) * (spinorIdem * chiralityR) ≠
    spinorIdem * chiralityR :=
  paperComposite_not_idempotent

/-- Regression: commuting square-+1 pair yields an idempotent composite. -/
example : (chiralityR * spinorIdemAxis1) * (chiralityR * spinorIdemAxis1) =
    chiralityR * spinorIdemAxis1 :=
  chiralityR_mul_spinorIdemAxis1_sq

/-- Regression: Cl(3,1) Dirac gammas obey `{γ^μ,γ^ν}=2η^{μν}`. -/
example (μ ν : Fin 4) :
    diracGamma μ * diracGamma ν + diracGamma ν * diracGamma μ =
      algebraMap ℝ Cl31 (2 * minkowskiEta μ ν) :=
  diracGamma_clifford μ ν

/-- Regression: `γ⁰` is not the hyperbolic generator `j`. -/
example : Cl31.toPGA (diracGamma 0) ≠ Generators.hyperbolic 0 :=
  paper_gamma0_not_hyperbolic

/-- Regression: axis-0 dual rotor is the Rodrigues SU(2) matrix. -/
example (θ : ℝ) :
    dualRotorMat (EuclideanSpace.single 0 θ) =
      Real.cos (θ / 2) • (1 : Matrix (Fin 2) (Fin 2) ℂ) +
        Real.sin (θ / 2) • cyclicRep 0 :=
  dualRotorMat_axis0_rodrigues θ

/-- Regression: axis-0 dual rotor is unitary with determinant 1. -/
example (θ : ℝ) :
    (dualRotorMat (EuclideanSpace.single 0 θ)).conjTranspose *
        dualRotorMat (EuclideanSpace.single 0 θ) = 1 ∧
      (dualRotorMat (EuclideanSpace.single 0 θ)).det = 1 :=
  ⟨dualRotorMat_axis0_unitary θ, dualRotorMat_axis0_det θ⟩

/-- Regression: three-axis dual rotor is SU(2). -/
example (β : DualRapidity) :
    (dualRotorMat β).conjTranspose * dualRotorMat β = 1 ∧
      (dualRotorMat β).det = 1 :=
  ⟨dualRotorMat_unitary β, dualRotorMat_det β⟩

/-- Regression: dual-rotor character is the real half-angle cosine. -/
example (β : DualRapidity) :
    (dualRotorMat β).trace = 2 * (Real.cos (‖β‖ / 2) : ℂ) :=
  dualRotorMat_trace β

/-- Regression: along \(\sigma_z\) the spinor amplitude is \(e^{-i\theta/2}\). -/
example (θ : ℝ) :
    dualRotorAmplitude (EuclideanSpace.single 2 θ) spinUp =
      Complex.exp (-(θ / 2 : ℂ) * Complex.I) :=
  dualRotorAmplitude_axis2 θ

/-- Regression: along \(\sigma_x\) the spinor amplitude is the real cosine. -/
example (θ : ℝ) :
    dualRotorAmplitude (EuclideanSpace.single 0 θ) spinUp =
      (Real.cos (θ / 2) : ℂ) :=
  dualRotorAmplitude_axis0 θ

/-- Regression: observer–particle pairing is the relative-rotor matrix element. -/
example (βO βA : DualRapidity) (χ : DualSpinor) :
    inner ℂ (applyMat (dualRotorMat βO) χ) (applyMat (dualRotorMat βA) χ) =
      inner ℂ χ
        (applyMat ((dualRotorMat βO).conjTranspose * dualRotorMat βA) χ) :=
  dualRotor_relative_overlap βO βA χ

/-- Regression: same-axis dual rotors compose by adding angles. -/
example (θ φ : ℝ) :
    dualRotorMat (EuclideanSpace.single 2 (θ + φ)) =
      dualRotorMat (EuclideanSpace.single 2 θ) *
        dualRotorMat (EuclideanSpace.single 2 φ) :=
  dualRotorMat_axis2_add θ φ

/-- Regression: the character is the sum of opposite computational amplitudes. -/
example (β : DualRapidity) :
    (dualRotorMat β).trace =
      dualRotorAmplitude β spinUp + dualRotorAmplitude β spinDown :=
  dualRotorMat_trace_eq_amplitudes β

/-- Regression: half-trace character is the real part of the spin-up element. -/
example (β : DualRapidity) :
    (dualRotorAmplitude β spinUp).re = Real.cos (‖β‖ / 2) :=
  dualRotorAmplitude_spinUp_re β

/-- Regression: \(2\pi\) dual rotation about the observer axis is \(-I\). -/
example : dualRotorMat (EuclideanSpace.single 2 (2 * Real.pi)) = -1 :=
  dualRotorMat_axis2_two_pi

/-- Regression: the relative dual rotor is unitary of determinant \(1\). -/
example (βO βA : DualRapidity) :
    ((dualRotorMat βO).conjTranspose * dualRotorMat βA).conjTranspose *
        ((dualRotorMat βO).conjTranspose * dualRotorMat βA) = 1 ∧
      ((dualRotorMat βO).conjTranspose * dualRotorMat βA).det = 1 :=
  ⟨dualRotor_relative_unitary βO βA, dualRotor_relative_det βO βA⟩

/-- Regression: distinct-axis dual rotors need not commute. -/
example :
    dualRotorMat (EuclideanSpace.single 0 Real.pi) *
        dualRotorMat (EuclideanSpace.single 2 Real.pi) ≠
      dualRotorMat (EuclideanSpace.single 2 Real.pi) *
        dualRotorMat (EuclideanSpace.single 0 Real.pi) :=
  dualRotorMat_axes_not_commute

/-- Regression: inverse dual rotor is the opposite rapidity. -/
example (β : DualRapidity) :
    dualRotorMat (-β) = (dualRotorMat β).conjTranspose :=
  dualRotorMat_neg β

/-- Regression: dual rotors along a common ray compose by adding the scale. -/
example (s t : ℝ) (β : DualRapidity) :
    dualRotorMat ((s + t) • β) =
      dualRotorMat (s • β) * dualRotorMat (t • β) :=
  dualRotorMat_ray_add s t β

/-- Regression: on a common ray the relative dual rotor is a single difference. -/
example (s t : ℝ) (β : DualRapidity) :
    (dualRotorMat (s • β)).conjTranspose * dualRotorMat (t • β) =
      dualRotorMat ((t - s) • β) :=
  dualRotor_relative_ray s t β

/-- Regression: character of a composite records dual-axis alignment. -/
example (β γ : DualRapidity) :
    (dualRotorMat β * dualRotorMat γ).trace =
      2 * ((Real.cos (‖β‖ / 2) : ℂ) * Real.cos (‖γ‖ / 2) -
        (dualAxisInner β γ : ℂ) * Real.sin (‖β‖ / 2) * Real.sin (‖γ‖ / 2)) :=
  dualRotorMat_mul_trace β γ

/-- Regression: relative-rotor character is the aligned half-angle cosine. -/
example (βO βA : DualRapidity) :
    ((dualRotorMat βO).conjTranspose * dualRotorMat βA).trace =
      2 * ((Real.cos (‖βO‖ / 2) : ℂ) * Real.cos (‖βA‖ / 2) +
        (dualAxisInner βO βA : ℂ) * Real.sin (‖βO‖ / 2) * Real.sin (‖βA‖ / 2)) :=
  dualRotor_relative_trace βO βA

/-- Regression: group commutator of perpendicular π dual rotations is -I. -/
example :
    dualRotorMat (EuclideanSpace.single 0 Real.pi) *
        dualRotorMat (EuclideanSpace.single 2 Real.pi) *
          (dualRotorMat (EuclideanSpace.single 0 Real.pi)).conjTranspose *
            (dualRotorMat (EuclideanSpace.single 2 Real.pi)).conjTranspose =
      -1 :=
  dualRotorMat_axes_group_commutator

/-- Regression: commuting projector is nonzero and generates a nonzero left ideal. -/
example :
    commutingSpinorIdem ≠ 0 ∧
      ∃ x ∈ leftIdealOf commutingSpinorIdem, x ≠ 0 :=
  ⟨commutingSpinorIdem_ne_zero, leftIdeal_commutingSpinorIdem_nontrivial⟩

/-- Regression: vanishing interference does not force a common single axis. -/
example : ∃ p q : TorsionParams, interfere p q = 0 ∧ ¬ SameAxis p q :=
  compatible_not_implies_same_axis

/-- Regression: Dirac \(\mathbb{C}^4\) matrices obey the Clifford relations. -/
example (μ ν : Fin 4) :
    diracMat μ * diracMat ν + diracMat ν * diracMat μ =
      (2 * minkowskiEta μ ν : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) :=
  diracMat_clifford μ ν

/-- Regression: dual \(\mathbb{C}^2\) is not the Dirac \(\mathbb{C}^4\). -/
example : Module.finrank ℂ DualSpinor ≠ Module.finrank ℂ DiracSpinor :=
  dualSpinor_ne_diracSpinor

/-- Regression: commuting left ideal has real dimension exactly eight. -/
example : Module.finrank ℝ (leftIdealSub commutingSpinorIdem) = 8 :=
  finrank_leftIdeal_commuting

/-- Regression: Dirac spinor has real dimension eight (matches the left ideal). -/
example : Module.finrank ℝ DiracSpinor = 8 :=
  diracSpinor_finrank_real

/-- Regression: dual-sector PGA exponential is the Rodrigues formula. -/
example (β : DualRapidity) :
    Motor.rotorTorsion (ofDual β) =
      Real.cos (‖β‖ / 2) • (1 : PGA) +
        (if h : β = 0 then (0 : PGA)
          else Real.sin (‖β‖ / 2) • cyclicUnit β h) :=
  rotorTorsion_ofDual β

/-- Regression: matrix dual rotor is the Rodrigues formula along β. -/
example (β : DualRapidity) :
    dualRotorMat β =
      Real.cos (‖β‖ / 2) • (1 : Matrix (Fin 2) (Fin 2) ℂ) +
        (if _h : β = 0 then (0 : Matrix (Fin 2) (Fin 2) ℂ)
          else Real.sin (‖β‖ / 2) • cyclicRepComb (fun a => β a / ‖β‖)) :=
  dualRotorMat_rodrigues β

/-- Regression: usual-sector PGA exponential is the hyperbolic Rodrigues formula. -/
example (α : UsualRapidity) :
    Motor.rotorTorsion (ofUsual α) =
      Real.cosh (‖α‖ / 2) • (1 : PGA) +
        (if h : α = 0 then (0 : PGA)
          else Real.sinh (‖α‖ / 2) • hyperbolicUnit α h) :=
  rotorTorsion_ofUsual α

/-- Regression: axis-0 usual rotor is \(\cosh(\theta/2)I+\sinh(\theta/2)B^+_0\). -/
example (θ : ℝ) :
    Motor.rotorTorsion (ofUsual (EuclideanSpace.single 0 θ)) =
      Real.cosh (θ / 2) • (1 : PGA) + Real.sinh (θ / 2) • Generators.hyperbolic 0 :=
  rotorTorsion_ofUsual_axis0 θ

/-- Regression: usual matrix rotor is Hermitian of determinant 1. -/
example (α : UsualRapidity) :
    (usualRotorMat α).IsHermitian ∧ (usualRotorMat α).det = 1 :=
  ⟨usualRotorMat_isHermitian α, usualRotorMat_det α⟩

/-- Regression: a nonzero usual boost is not unitary. -/
example :
    (usualRotorMat (EuclideanSpace.single 0 (2 : ℝ))).conjTranspose *
      usualRotorMat (EuclideanSpace.single 0 (2 : ℝ)) ≠ 1 :=
  usualRotorMat_axis0_not_unitary

/-- Regression: matrix usual rotor is the hyperbolic Rodrigues formula along α. -/
example (α : UsualRapidity) :
    usualRotorMat α =
      Real.cosh (‖α‖ / 2) • (1 : Matrix (Fin 2) (Fin 2) ℂ) +
        (if _h : α = 0 then (0 : Matrix (Fin 2) (Fin 2) ℂ)
          else Real.sinh (‖α‖ / 2) • pauliComb (fun a => α a / ‖α‖)) :=
  usualRotorMat_rodrigues α

/-- Regression: every Dirac spinor decomposes into Weyl blocks. -/
example (Ψ : DiracSpinor) :
    weylUpper (WithLp.toLp 2 ![WithLp.ofLp Ψ 0, WithLp.ofLp Ψ 1]) +
      weylLower (WithLp.toLp 2 ![WithLp.ofLp Ψ 2, WithLp.ofLp Ψ 3]) = Ψ :=
  weyl_decompose Ψ

/-- Regression: \(\gamma^5\) squares to the identity. -/
example : diracMat5 * diracMat5 = 1 :=
  diracMat5_sq

/-- Regression: Weyl projectors are complementary idempotents. -/
example : weylProjPlus * weylProjPlus = weylProjPlus ∧
    weylProjMinus * weylProjMinus = weylProjMinus ∧
      weylProjPlus + weylProjMinus = 1 :=
  ⟨weylProjPlus_sq, weylProjMinus_sq, weylProjPlus_add_minus⟩

/-- Regression: upper Weyl block is the \(+1\) eigenspace of \(\gamma^5\). -/
example (ψ : DualSpinor) :
    applyDiracMat diracMat5 (weylUpper ψ) = weylUpper ψ :=
  applyDiracMat5_weylUpper ψ

/-- Regression: lower Weyl block is the \(-1\) eigenspace of \(\gamma^5\). -/
example (ψ : DualSpinor) :
    applyDiracMat diracMat5 (weylLower ψ) = -weylLower ψ :=
  applyDiracMat5_weylLower ψ

/-- Regression: Clifford slash squares to the Minkowski quadratic. -/
example (p : Vec4) :
    slashCl p * slashCl p = algebraMap ℝ Cl31 (minkowskiQ p) :=
  slashCl_sq p

/-- Regression: matrix slash squares to \(Q(p)\,I\). -/
example (p : Vec4) :
    slashMat p * slashMat p = (minkowskiQ p : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) :=
  slashMat_sq p

/-- Regression: a nonzero Dirac eigenspinor lies on the mass shell. -/
example {m : ℝ} {p : Vec4} {Ψ : DiracSpinor}
    (hΨ : Ψ ≠ 0) (h : DiracMomentum m p Ψ) :
    minkowskiQ p = -m ^ 2 :=
  diracMomentum_implies_mass_shell hΨ h

/-- Regression: rest-frame particle solutions exist. -/
example (m : ℝ) :
    ∃ Ψ : DiracSpinor, Ψ ≠ 0 ∧ DiracMomentum m (restMomentum m) Ψ :=
  exists_rest_particle m

/-- Regression: chiral slashes multiply to the Minkowski quadratic. -/
example (p : Vec4) :
    pauliSlash p * pauliSlashBar p = (minkowskiQ p : ℂ) • 1 :=
  pauliSlash_mul_pauliSlashBar p

/-- Regression: the on-shell Weyl construction recovers the rest pair \((u,iu)\). -/
example {m : ℝ} (hm : m ≠ 0) (u : DualSpinor) :
    onShellParticleSpinor m (restMomentum m) u = restParticleSpinor u :=
  onShellParticleSpinor_rest hm u

/-- Regression: a massive on-shell four-momentum carries a Dirac solution. -/
example {m : ℝ} {p : Vec4} (hm : m ≠ 0) (hQ : minkowskiQ p = -m ^ 2)
    (u : DualSpinor) :
    DiracMomentum m p (onShellParticleSpinor m p u) :=
  onShellParticle_dirac hm hQ u

/-- Regression: a longitudinal boost of rest momentum lies on the mass shell. -/
example (m α : ℝ) : minkowskiQ (boostZMomentum m α) = -m ^ 2 :=
  minkowskiQ_boostZ m α

/-- Regression: a longitudinal Dirac boost of the rest pair is the on-shell
Weyl construction after a chiral factor on the Weyl parameter. -/
example {m α : ℝ} (hm : m ≠ 0) (u : DualSpinor) :
    applyDiracBoostZ α (restParticleSpinor u) =
      onShellParticleSpinor m (boostZMomentum m α)
        (applyMat (chiralBoostZ α) u) :=
  applyDiracBoostZ_rest hm u

/-- Regression: dual rotation about the boost axis commutes with the chiral
boost factor. -/
example (α θ : ℝ) :
    chiralBoostZ α * dualRotorMat (EuclideanSpace.single 2 θ) =
      dualRotorMat (EuclideanSpace.single 2 θ) * chiralBoostZ α :=
  chiralBoostZ_comm_dualRotor_axis2 α θ

/-- Regression: dual rotation about a perpendicular axis need not commute
with the chiral boost factor. -/
example :
    chiralBoostZ 2 * dualRotorMat (EuclideanSpace.single 0 Real.pi) ≠
      dualRotorMat (EuclideanSpace.single 0 Real.pi) * chiralBoostZ 2 :=
  chiralBoostZ_not_comm_dualRotor_axis0

/-- Regression: rest-frame Dirac overlap is twice the dual-rotor amplitude. -/
example (β : DualRapidity) (u : DualSpinor) :
    inner ℂ (restParticleSpinor u)
        (restParticleSpinor (applyMat (dualRotorMat β) u)) =
      2 * dualRotorAmplitude β u :=
  restParticle_dualRotor_overlap β u

/-- Regression: massless Dirac decouples into Weyl equations. -/
example {p : Vec4} {Ψ : DiracSpinor} (h : DiracMomentum 0 p Ψ) :
    applyMat (pauliSlash p) (diracLower Ψ) = 0 ∧
      applyMat (pauliSlashBar p) (diracUpper Ψ) = 0 :=
  dirac_massless_decouple h

/-- Regression: \(\gamma^5\) sends mass \(m\) to mass \(-m\). -/
example {m : ℝ} {p : Vec4} {Ψ : DiracSpinor} (h : DiracMomentum m p Ψ) :
    DiracMomentum (-m) p (applyDiracMat diracMat5 Ψ) :=
  diracMat5_flips_mass h

/-- Regression: MW real 16 matches WeylSU4 real 16 (no Spin equivariance). -/
example : Module.finrank ℝ MajoranaWeyl10 = Module.finrank ℝ WeylSU4 :=
  majorana_dim_eq_weylSU4_real

/-- Regression: light-cone 8+8 ≠ DST torsion 6; Super-Poincaré ≠ PGA 10. -/
example : 8 + 8 ≠ 6 ∧ StringSpectrum.superPoincareN1Dim ≠ LorentzDim.pgaGeneratorCount :=
  ⟨LorentzDim.lightCone_ne_torsionGenerators, superPoincare_ne_pga⟩

/-- Regression: balanced ray is level-matched (`J = 0`). -/
example : IsLevelMatched (Invariant.balancedRay 1) :=
  isLevelMatched_balancedRay 1

/-- Regression: discrete rotor image is finite (not a generation count). -/
example {N : ℕ} [NeZero N] : (UnitGroup.DiscreteRotorImage N).Finite :=
  discreteRotorImage_finite_not_generations

end Logic

end DstDiophantine
