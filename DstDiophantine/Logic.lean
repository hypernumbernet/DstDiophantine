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
import DstDiophantine.Logic.Quantum.QuantumLogic
import DstDiophantine.Logic.Quantum.Dictionary
import DstDiophantine.Logic.Quantum.Spinor10
import DstDiophantine.Logic.Quantum.StringSpectrum
import DstDiophantine.Logic.Quantum.MinimalIdeal
import DstDiophantine.Logic.Quantum.CompositeProjector
import DstDiophantine.Logic.Quantum.Dirac
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
  `ℂ²`, subspace lattice, internal dictionary) plus the string-comparison
  slice (`Cl91`, MW16, spectrum labels, level-match dictionary)
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
