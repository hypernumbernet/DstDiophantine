import DoubleSpacetime.Logic.TruthValue
import DoubleSpacetime.Logic.Connective
import DoubleSpacetime.Logic.Interpretation
import DoubleSpacetime.Logic.Amplitude
import DoubleSpacetime.Logic.Order
import DoubleSpacetime.Logic.Geometric
import DoubleSpacetime.Logic.Formula
import DoubleSpacetime.Logic.Valuation
import DoubleSpacetime.Logic.Consequence
import DoubleSpacetime.Logic.Implication
import DoubleSpacetime.Logic.ClassicalCore
import DoubleSpacetime.Logic.HeightIdentity
import DoubleSpacetime.Logic.WallRule
import DoubleSpacetime.Logic.Example.FixedPoint
import DoubleSpacetime.Logic.Example.Explosion
import DoubleSpacetime.Logic.Example.NotFalse
import DoubleSpacetime.Logic.Regime
import DoubleSpacetime.Logic.Example.Regime
import DoubleSpacetime.Logic.Example.BealRegime
import DoubleSpacetime.Logic.Example.FermatRegime
import DoubleSpacetime.Logic.DiscreteAmplitude
import DoubleSpacetime.Logic.Dynamics
import DoubleSpacetime.Logic.Winding
import DoubleSpacetime.Logic.MotorProp
import DoubleSpacetime.Logic.BalancedResidual
import DoubleSpacetime.Logic.Quantum.Separation
import DoubleSpacetime.Logic.Quantum.DualSector
import DoubleSpacetime.Logic.Quantum.Quaternion
import DoubleSpacetime.Logic.Quantum.Spinor
import DoubleSpacetime.Logic.Quantum.DualRodrigues
import DoubleSpacetime.Logic.Quantum.UsualRodrigues
import DoubleSpacetime.Logic.Quantum.UsualRotor
import DoubleSpacetime.Logic.Quantum.QuantumLogic
import DoubleSpacetime.Logic.Quantum.Sasaki
import DoubleSpacetime.Logic.Quantum.BooleanIsland
import DoubleSpacetime.Logic.Quantum.BlockReading
import DoubleSpacetime.Logic.Quantum.Dictionary
import DoubleSpacetime.Logic.Quantum.Spinor10
import DoubleSpacetime.Logic.Quantum.StringSpectrum
import DoubleSpacetime.Logic.Quantum.MinimalIdeal
import DoubleSpacetime.Logic.Quantum.CompositeProjector
import DoubleSpacetime.Logic.Quantum.LeftIdealDim
import DoubleSpacetime.Logic.Quantum.LeftIdealSplit
import DoubleSpacetime.Logic.Quantum.Dirac
import DoubleSpacetime.Logic.Quantum.DiracSpinor
import DoubleSpacetime.Logic.Quantum.DiracEquation
import DoubleSpacetime.Logic.Quantum.DiracCovariance
import DoubleSpacetime.Logic.Quantum.DiracField
import DoubleSpacetime.Logic.Quantum.DiracGauge
import DoubleSpacetime.Logic.Quantum.DiracConjugation
import DoubleSpacetime.Logic.Quantum.DualEntanglement
import DoubleSpacetime.Logic.Quantum.DualObservables
import DoubleSpacetime.Logic.Quantum.LightFilter
import DoubleSpacetime.Logic.Quantum.Complementarity
import DoubleSpacetime.Logic.Quantum.ExternalChart
import DoubleSpacetime.Logic.Quantum.SpinWaveBridge
import DoubleSpacetime.Logic.Quantum.ChartOperators
import DoubleSpacetime.Logic.Quantum.NewtonWigner
import DoubleSpacetime.Logic.Quantum.PositionInformation
import DoubleSpacetime.Logic.Quantum.PhaseInformation
import DoubleSpacetime.Logic.Quantum.ShellInformation
import DoubleSpacetime.Logic.Quantum.FrameInformation
import DoubleSpacetime.Logic.Quantum.CarrierDeficit
import DoubleSpacetime.Logic.Quantum.PhaseFisher
import DoubleSpacetime.Logic.Quantum.ChartFisher
import DoubleSpacetime.Logic.Quantum.ChartScore
import DoubleSpacetime.Logic.Quantum.MomentumReading
import DoubleSpacetime.Logic.Quantum.TranslationFisher
import DoubleSpacetime.Logic.Quantum.TranslatorInformation
import DoubleSpacetime.Logic.Quantum.BornLorentz
import DoubleSpacetime.Logic.Quantum.AngleChart
import DoubleSpacetime.Logic.Quantum.DualExchange
import DoubleSpacetime.Logic.Quantum.DualOccupancy
import DoubleSpacetime.Logic.Quantum.DeBroglie
import DoubleSpacetime.Logic.Quantum.LevelMatch
import DoubleSpacetime.Logic.Quantum.StringCompare
import DoubleSpacetime.Algebra.Invariant
import DoubleSpacetime.Algebra.Cl91
import DoubleSpacetime.Algebra.LorentzDim
import Mathlib.Data.Matrix.Basic

/-!
# Dual Spacetime 4-valued logic

A proposition is an admissible torsion configuration measured by `JNormalized`.
The track is not re-exported from `DoubleSpacetime.Basic`.

* `Logic.Amplitude` — admissible configuration as the primary carrier
* `Logic.TruthValue` — four states from `JNormalized ∈ [-1,1]`
* `Logic.Connective` — min/max/neg, non-explosion
* `Logic.Interpretation` — usual–dual swap is signed negation
* `Logic.Order` — height and information preorders
* `Logic.Geometric` — Killing overlap, bivector commutator, rotor composition
* `Logic.Quantum` — dual Hilbert layer of D4L
* `Logic.Formula` / `Valuation` / `Consequence` — syntax, designated `HoldsT` / `HoldsNotF`,
  two-valued fragments, entailment
* `Logic.Implication` — separate residuals of the two predicates
* `Logic.ClassicalCore` — the wall fragment as a Boolean algebra, with classical truth the positive
  wall
* `Logic.HeightIdentity` — a formula returns one literal
* `Logic.WallRule` — modus ponens, tollens, disjunctive syllogism, and the syllogism preserve the
  positive wall at every real height
* `Logic.Quantum.Sasaki` — the implication carried by orthomodularity detaches for every pair
* `Logic.Quantum.BooleanIsland` — a ray splits along another ray exactly when the two are equal or
  orthogonal
* `Logic.Quantum.BlockReading` — splitting along both arguments distributes in `ℂ²`
* `Logic.Regime` — discrete proof-status algebra and implication table
* `Logic.Example` — fixed-point, non-explosion, `Jnorm < 1`, Diophantine regimes, Beal residual
  atlas, dual-axis FLT atlas
* `Logic.DiscreteAmplitude` — torus amplitudes
* `Logic.Dynamics` — amplification as a partial map on labels
* `Logic.Winding` — height and winding are incompatible measurements
* `Logic.MotorProp` — L2: additive motor ≠ multiplicative amplitude
* `Logic.BalancedResidual` — L3: `BalancedResidualClass` vs window seeds

Unconditional FLT / Beal / a Gödel-refutation are not claimed.
The amplitude layer is not a Hilbert space, a Born rule, or an orthomodular lattice, and the `ℂ²`
operations are not the four labels.
-/

namespace DoubleSpacetime

namespace Logic

open Invariant Operations Generators Submodule

example (tv : TruthValue) :
    ∃ (p : TorsionParams) (h : Admissible.IsAdmissibleContinuous p), ofParams p h = tv :=
  exists_ofParams tv

example (p : TorsionParams) : JNormalized (daggerParams p) = -JNormalized p :=
  JNormalized_dagger p

example {j : ℝ} (hj : |j| ≤ 1) :
    classifyOfMem (conjJ j (negJ j)) (abs_conj_neg_le hj) ≠ .F :=
  classify_conj_neg_ne_F hj

example (tv : TruthValue) : ∃ a : Amplitude, a.collapse = tv :=
  exists_amplitude tv

example (a : Amplitude) : a.adjoint.adjoint = a :=
  a.adjoint_involutive

example (a : Amplitude) : a.adjoint.measure = -a.measure :=
  a.measure_adjoint

example {j : ℝ} (hj : |j| ≤ 1) :
    classifyOfMem j hj = .T ↔ ∀ k : ℝ, |k| ≤ 1 → InfoLE j k :=
  classify_T_iff_info_bottom hj

example {j : ℝ} (hj : |j| ≤ 1) :
    (∀ k : ℝ, |k| ≤ 1 → InfoLE k j) ↔ j = 1 ∨ j = -1 :=
  info_top_iff hj

example (p q : TorsionParams) : overlap p q = overlap q p :=
  overlap_symm p q

example (p : TorsionParams) : overlap p p = 16 * J p :=
  overlap_self p

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

example : ¬ ∃ v : Valuation,
    IsWallTwo (v.assign 0) ∧
      IsNegFixed ((Formula.atom 0).eval v.assign) :=
  not_exists_wall_negFixed

/-- Regression: D4L realises the negation fixed point at `T`. -/
example : ∃ v : Valuation, IsNegFixed ((Formula.atom 0).eval v.assign) :=
  exists_negFixed_valuation

example (j k : ℝ) : HoldsNotF (conjJ j k) ↔ HoldsNotF j ∨ HoldsNotF k :=
  holdsNotF_conj j k

example (j k : ℝ) : HoldsNotF (disjJ j k) ↔ HoldsNotF j ∧ HoldsNotF k :=
  holdsNotF_disj j k

example {k : ℝ} (hk : 0 ≤ k) : conjJ 0 k = 0 :=
  conjJ_zero_of_nonneg hk

example {k : ℝ} (hk : k ≤ 0) : disjJ 0 k = 0 :=
  disjJ_zero_of_nonpos hk

example {j : ℝ} (hj : |j| ≤ 1) :
    ¬ HoldsNotF (disjJ j (negJ j)) ↔ j = 1 ∨ j = -1 :=
  not_holdsNotF_excluded_middle_iff hj

example :
    EntailsT {(Formula.atom 0)} ((Formula.atom 0).disj (Formula.atom 0).neg) :=
  entailsT_excluded_middle (Formula.atom 0)

example (φ : Formula) :
    (∀ b : ℕ → Bool, φ.boolEval b = true) ↔
      ∀ v : ℕ → ℝ, (∀ n, IsWallTwo (v n)) → φ.eval v = 1 :=
  classical_iff_positive_wall φ

/-- Regression: double negation on the height is already the classical law. -/
example (φ : Formula) (b : ℕ → Bool) :
    φ.neg.neg.boolEval b = φ.boolEval b :=
  double_neg_classical φ b

example (b : ℕ → Bool) : syllogismFormula.boolEval b = true :=
  syllogism_classical b

example : syllogismFormula.eval (fun _ => 0) = 0 :=
  syllogism_balance

example {j k : ℝ} (hj : j = 1) (himp : impJ j k = 1) : k = 1 :=
  impJ_detach_wall hj himp

example (j k : ℝ) :
    HoldsNotF (impJ j k) ↔ HoldsNotF (negJ j) ∧ HoldsNotF k :=
  holdsNotF_impJ j k

example {j k : ℝ} (hjk : impJ j k = 1) (hk : k = -1) : j = -1 :=
  impJ_tollens hjk hk

example {j k : ℝ} (h : disjJ j k = 1) (hj : j = -1) : k = 1 :=
  disjJ_tollens h hj

example {j k m : ℝ} (hjk : impJ j k = 1) (hkm : impJ k m = 1) : impJ j m = 1 :=
  impJ_chain hjk hkm

example (φ : Formula) : φ.eval (fun _ => 0) = 0 ∧ ¬ EntailsOne ∅ φ :=
  ⟨eval_balance φ, not_entailsOne_empty φ⟩

example (φ ψ : Formula) :
    (∀ v : ℕ → ℝ, (∀ n, IsWallTwo (v n)) → φ.eval v = 1 → ψ.eval v = 1) ↔
      (∀ v : ℕ → ℝ, (∀ n, IsWallTwo (v n)) → (impF φ ψ).eval v = 1) :=
  discharge_on_walls φ ψ

example :
    EntailsOne {(Formula.atom 0)} (excludedMiddle 0) ∧
      (impF (Formula.atom 0) (excludedMiddle 0)).eval (fun _ => 0) = 0 :=
  ⟨entailsOne_excluded_middle, discharge_excluded_middle_balance⟩

/-- Regression: on the interval, positive-wall consequence is decided by `{-1, 0, 1}`. -/
example (Γ : Set Formula) (ψ : Formula) :
    EntailsWall Γ ψ ↔
      ∀ v : ℕ → ℝ, (∀ n, IsThreeHeight (v n)) →
        (∀ φ ∈ Γ, φ.eval v = 1) → ψ.eval v = 1 :=
  entailsWall_iff_threeHeight Γ ψ

example {k : ℝ} (hk : k ≤ 0) : impJ 0 k = 0 :=
  impJ_zero_of_nonpos hk

example : impJ (-1) 0 = 1 :=
  impJ_neg_wall_balance

example :
    ¬ EntailsNotF {(Formula.atom 0)}
        ((Formula.atom 0).disj (Formula.atom 0).neg) :=
  not_entailsNotF_excluded_middle

example :
    EntailsNotF ∅ ((Formula.atom 0).conj (Formula.atom 0).neg) ∧
      ¬ EntailsT ∅ ((Formula.atom 0).conj (Formula.atom 0).neg) :=
  ⟨entailsNotF_conj_neg _, not_entailsT_conj_neg⟩

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

/-- Regression: a closed slice with bookkeeping does not force the conjecture. -/
example :
    ¬ EntailsNotFR {RegimeFormula.atom 0, RegimeFormula.atom 1}
        (RegimeFormula.atom 3) :=
  window_nogo_not_entailsNotFR_conjecture

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
                      sliceNN5.eval v.assign = .T ∧
                        sliceBruin.eval v.assign = .T :=
  exists_beal_atlas_valuation

/-- Regression: closed Beal slices do not T-entail classical Beal. -/
example :
    ¬ EntailsTR {sliceFLT, sliceDM, sliceAbsOne, sliceFourth, sliceNN5, sliceBruin}
        bealConjecture :=
  closed_slices_not_entailsTR_beal

example :
    ¬ EntailsTR (bealClosedSliceAtomSet ∪ {liveMordell}) bealConjecture ∧
      ¬ EntailsTR bealArtefactAtomSet bealConjecture :=
  ⟨promote_liveMordell_not_entailsTR_beal, artefacts_not_entailsTR_beal⟩

example :
    ∃ v : RegimeValuation,
      sliceCore.eval v.assign = .T ∧
        sliceLp.eval v.assign = .T ∧
          sliceElliptic.eval v.assign = .T ∧
            diagSingleAxisModular.eval v.assign = .F ∧
              diagBalancedSeed.eval v.assign = .F ∧
                liveMixedMotor.eval v.assign = .U ∧
                  fltConjecture.eval v.assign = .U :=
  exists_fermat_atlas_valuation

/-- Regression: closed FLT slices do not T-entail classical FLT. -/
example : ¬ EntailsTR {sliceCore, sliceLp, sliceElliptic} fltConjecture :=
  closed_slices_not_entailsTR_flt

example : meetRList (closedSliceStatuses ++ [.U]) = .U :=
  meetRList_closed_with_live

example :
    (⟨zeroTorsion, isAdmissibleContinuous_zeroTorsion⟩ : Amplitude).IsVacuum :=
  pure_translation_torsion_isVacuum

example :
    vacuumAmplitude.IsVacuum ∧ balancedAmplitude.IsBalancedMassive ∧
      ¬ vacuumAmplitude.IsBalancedMassive ∧ ¬ balancedAmplitude.IsVacuum :=
  additive_vacuum_ne_multiplicative_balanced

example : BalancedResidualClass balancedAmplitude ∧ ¬ BalancedResidualClass halfWindowSeed :=
  ⟨balancedAmplitude_mem_balancedResidualClass, halfWindowSeed_not_balanced⟩

/-- Regression: `U → T` is not designated. -/
example : impR .U .T = .U :=
  impR_U_T

example (s : TruthValue) : conjR s (negR s) ≠ .F :=
  conjR_negR_ne_F s

example {N : ℕ} [NeZero N] (h4 : ¬ 4 ∣ N) (a : DiscreteAmplitude N) :
    a.collapse ≠ .F :=
  DiscreteAmplitude.collapse_ne_F_of_not_four_dvd h4 a

example {k : ℕ} (hk : 2 ≤ k) :
    (⟨Amplification.scaleTorsion (k : ℝ) (seedU_to_F hk).params,
        seedU_to_F_scale_admissible hk⟩ : Amplitude).collapse = .F :=
  seedU_to_F_scales_to_F hk

example :
    (∃ a : Amplitude, a.collapse = .T ∧ a.IsVacuum) ∧
      (∃ b : Amplitude, b.collapse = .T ∧ b.IsBalancedMassive) :=
  T_splits_vacuum_and_balancedMassive

example (a : Amplitude) : |a.measure| ≤ a.massNormalized :=
  a.abs_measure_le_massNormalized

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

example :
    ¬ ∃ imp : ℝ → ℝ → ℝ,
      (∀ j k : ℝ, |j| ≤ 1 → |k| ≤ 1 → |imp j k| ≤ 1) ∧
        (∀ j k : ℝ, |j| ≤ 1 → |k| ≤ 1 →
          (HoldsT (imp j k) ↔ (HoldsT j → HoldsT k)) ∧
            (HoldsNotF (imp j k) ↔ (HoldsNotF j → HoldsNotF k))) :=
  no_common_residual

/-- Regression: boost-dominant implying the wall splits the two residuals. -/
example : syncImp (1 / 2 : ℝ) 1 = 0 ∧ nonrefImp (1 / 2 : ℝ) 1 = 1 :=
  sync_nonref_at_open_wall

/-- Regression: both residuals designate boost-dominant implying synchrony. -/
example : syncImp (1 / 2 : ℝ) 0 = 0 ∧ nonrefImp (1 / 2 : ℝ) 0 = 0 :=
  sync_nonref_agree_open_to_balance

/-- Regression: the Gödel residuum refutes rotation-dominant implying synchrony. -/
example : residuumJ (-1 / 2 : ℝ) 0 = 1 ∧ nonrefImp (-1 / 2 : ℝ) 0 = 0 :=
  residuum_refutes_B_T_nonref_designates

/-- Regression: regime implication residuates non-refutation, not theoremhood. -/
example (a b : TruthValue) :
    HoldsNotFR (impR a b) ↔ (HoldsNotFR a → HoldsNotFR b) :=
  holdsNotFR_impR a b

example : ¬ (HoldsTR (impR .U .T) ↔ (HoldsTR .U → HoldsTR .T)) :=
  impR_not_theoremhood_residual

example :
    residuumJ (amplitudeRep .U) (amplitudeRep .T) = 0 ∧ impR .U .T = .U ∧
      residuumJ (amplitudeRep .B) (amplitudeRep .T) = 1 ∧ impR .B .T = .U :=
  ⟨residuum_U_T_ne_impR.1, residuum_U_T_ne_impR.2,
    residuum_B_T_ne_impR.1, residuum_B_T_ne_impR.2⟩

example : (discreteF (by decide : 4 ∣ 4)).collapse = .F ∧
    (discreteB (by decide : 4 ∣ 4)).collapse = .B :=
  ⟨discreteF_collapse (by decide), discreteB_collapse (by decide)⟩

example {A B : QProp} : sasaki A B = ⊤ ↔ A ≤ B :=
  sasaki_eq_top_iff

example :
    Compatible lineE0 lineE1 ∧ ¬ Compatible lineE0 lineD ∧
      sasaki lineE0 lineD = lineE1 ∧ material lineE0 lineD = ⊤ :=
  ⟨lineE0_compatible_lineE1, diagonal_not_compatible,
    diagonal_classical_overshoots.1, diagonal_classical_overshoots.2⟩

example (A B : QProp) : A ⊓ sasaki A B ≤ B :=
  sasaki_detach A B

example {A B : QProp} : A ⊓ material A B ≤ B ↔ Compatible A B :=
  material_detach_iff_compatible

example : ¬ lineE0 ⊓ material lineE0 lineD ≤ lineD :=
  material_detach_iff_compatible.not.mpr diagonal_not_compatible

example {A B : QProp} (hA : Module.finrank ℂ A = 1) (hB : Module.finrank ℂ B = 1) :
    Compatible A B ↔ A = B ∨ A ⟂ B :=
  compatible_line_iff hA hB

example {L A : QProp} (hL : Module.finrank ℂ L = 1) :
    Compatible A L ↔ A ∈ Island L :=
  compatible_ray_iff_mem_island hL

example {L A B C : QProp} (hA : A ∈ Island L) (hB : B ∈ Island L) (hC : C ∈ Island L) :
    sasaki A B = material A B ∧ A ⊓ (B ⊔ C) = (A ⊓ B) ⊔ (A ⊓ C) :=
  ⟨island_implications_agree hA hB, island_inf_sup_distrib hA hB hC⟩

example {L M : QProp} (hL : Module.finrank ℂ L = 1) (hM : Module.finrank ℂ M = 1)
    (hne : L ≠ M) (hneO : L ≠ Mᗮ) :
    Island L ∩ Island M = ({⊥, ⊤} : Set QProp) :=
  island_inter_trivial hL hM hne hneO

example {A : QProp} : (∀ B : QProp, Compatible A B) ↔ A = ⊥ ∨ A = ⊤ :=
  compatible_all_iff

example {A B C : QProp}
    (hA : Module.finrank ℂ A = 1) (hB : Module.finrank ℂ B = 1)
    (hC : Module.finrank ℂ C = 1) (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C)
    (hABc : Compatible A B) (hACc : Compatible A C) (hBCc : Compatible B C) : False :=
  no_three_pairwise_compatible_lines hA hB hC hAB hAC hBC hABc hACc hBCc

example {A B C : QProp} (hB : Compatible A B) (hC : Compatible A C) :
    A ⊓ (B ⊔ C) = (A ⊓ B) ⊔ (A ⊓ C) :=
  distributes_of_splits hB hC

example {A B C : QProp} (hA : Module.finrank ℂ A = 1)
    (hB : Compatible A B) (hC : Compatible A C) :
    B ∈ Island A ∧ C ∈ Island A ∧ Compatible B C :=
  splits_ray_forces_island hA hB hC

/-- Regression: orthocomplement fixes nothing, and the island does not embed into the height. -/
example (A : QProp) : A ≠ Aᗮ :=
  orthogonal_ne A

example {L : QProp} (hL : Module.finrank ℂ L = 1) :
    ¬ ∃ φ : QProp → ℝ,
      ∀ A B : QProp, A ∈ Island L → B ∈ Island L → (A ≤ B ↔ φ A ≤ φ B) :=
  no_height_order_embedding hL

/-- Regression: island negation is bitwise, and sign flip on heights misses a label. -/
example (L : QProp) (p : Bool × Bool) :
    (ofBits L p)ᗮ = ofBits L (bitComplement p) :=
  ofBits_orthogonal L p

example :
    ¬ ∃ (φ : Bool × Bool → ℝ) (_hφ : ∀ p, |φ p| ≤ 1),
      (∀ p, φ (bitComplement p) = - φ p) ∧
        ∀ tv : TruthValue, ∃ p, classifyOfMem (φ p) (_hφ p) = tv :=
  no_sign_flip_realizes_four_labels

example (j : ℝ) : conjJ j (negJ j) = 0 ↔ j = 0 :=
  height_meet_neg_eq_zero_iff j

example : lineE0 ⟂ lineE1 :=
  lineE0_isOrtho_lineE1

example : Infinite {A : QProp // Module.finrank ℂ A = 1} :=
  infinite_one_dim_subspaces

example {k : ℕ} (h : Admissible.IsAdmissibleContinuous
    (Amplification.scaleTorsion (k : ℝ) vacuumAmplitude.params)) :
    (⟨Amplification.scaleTorsion (k : ℝ) vacuumAmplitude.params, h⟩ : Amplitude).IsVacuum :=
  scale_vacuum_stays_vacuum vacuumAmplitude_isVacuum h

example {k : ℕ} (hk : 1 ≤ k) :
    (⟨Amplification.scaleTorsion (k : ℝ) (seedBalanced_stays hk).params,
        seedBalanced_stays_scale_admissible hk⟩ : Amplitude).IsBalancedMassive :=
  seedBalanced_stays_scales_balanced hk

example :
    ¬ Admissible.IsAdmissibleContinuous
        (Amplification.scaleTorsion (2 : ℝ) balancedAmplitude.params) :=
  balancedAmplitude_exits_not_admissible

/-- Regression: that cone exit is invisible to the signed-height classifier. -/
example :
    classify? (JNormalized (Amplification.scaleTorsion (2 : ℝ) balancedAmplitude.params)) =
      some .T :=
  balancedAmplitude_scale_classify_T

example {N : ℕ} [NeZero N] (k : ℕ) (t : Discrete.DiscreteTorsion N) :
    ¬ (Admissible.IsAdmissibleContinuous
          (Amplification.scaleTorsion (k : ℝ) (Discrete.toTorsionParams t)) ∧
        ModularAmplification.windingTotal k t ≠ 0) :=
  not_both_admissibleScale_and_winding k t

example : Module.finrank ℝ Cl31 = 16 ∧ Module.finrank ℝ Cl91 = 1024 :=
  ⟨Cl91.finrank_cl31, Cl91.finrank_cl91⟩

example : ¬ Nonempty (Cl31 ≃ₐ[ℝ] Cl91) :=
  not_cl31_algEquiv_cl91

example : chiralityL * chiralityL = chiralityL ∧
    chiralityR * chiralityR = chiralityR ∧
      spinorIdem * spinorIdem = spinorIdem :=
  ⟨chiralityL_sq, chiralityR_sq, spinorIdem_sq⟩

/-- Regression: `(1-i)/2` is not idempotent when `i² = -1`. -/
example : paperChiralityL * paperChiralityL ≠ paperChiralityL :=
  paper_chirality_rejected

example : (spinorIdem * chiralityR) * (spinorIdem * chiralityR) ≠
    spinorIdem * chiralityR :=
  paperComposite_not_idempotent

example : (chiralityR * spinorIdemAxis1) * (chiralityR * spinorIdemAxis1) =
    chiralityR * spinorIdemAxis1 :=
  chiralityR_mul_spinorIdemAxis1_sq

example (μ ν : Fin 4) :
    diracGamma μ * diracGamma ν + diracGamma ν * diracGamma μ =
      algebraMap ℝ Cl31 (2 * minkowskiEta μ ν) :=
  diracGamma_clifford μ ν

/-- Regression: `γ⁰` is not the hyperbolic generator `j`. -/
example : Cl31.toPGA (diracGamma 0) ≠ Generators.hyperbolic 0 :=
  paper_gamma0_not_hyperbolic

example (θ : ℝ) :
    dualRotorMat (EuclideanSpace.single 0 θ) =
      Real.cos (θ / 2) • (1 : Matrix (Fin 2) (Fin 2) ℂ) +
        Real.sin (θ / 2) • cyclicRep 0 :=
  dualRotorMat_axis0_rodrigues θ

example (θ : ℝ) :
    (dualRotorMat (EuclideanSpace.single 0 θ)).conjTranspose *
        dualRotorMat (EuclideanSpace.single 0 θ) = 1 ∧
      (dualRotorMat (EuclideanSpace.single 0 θ)).det = 1 :=
  ⟨dualRotorMat_axis0_unitary θ, dualRotorMat_axis0_det θ⟩

example (β : DualRapidity) :
    (dualRotorMat β).conjTranspose * dualRotorMat β = 1 ∧
      (dualRotorMat β).det = 1 :=
  ⟨dualRotorMat_unitary β, dualRotorMat_det β⟩

example (β : DualRapidity) :
    (dualRotorMat β).trace = 2 * (Real.cos (‖β‖ / 2) : ℂ) :=
  dualRotorMat_trace β

example (θ : ℝ) :
    dualRotorAmplitude (EuclideanSpace.single 2 θ) spinUp =
      Complex.exp (-(θ / 2 : ℂ) * Complex.I) :=
  dualRotorAmplitude_axis2 θ

example (θ : ℝ) :
    dualRotorAmplitude (EuclideanSpace.single 0 θ) spinUp =
      (Real.cos (θ / 2) : ℂ) :=
  dualRotorAmplitude_axis0 θ

example (βO βA : DualRapidity) (χ : DualSpinor) :
    inner ℂ (applyMat (dualRotorMat βO) χ) (applyMat (dualRotorMat βA) χ) =
      inner ℂ χ
        (applyMat ((dualRotorMat βO).conjTranspose * dualRotorMat βA) χ) :=
  dualRotor_relative_overlap βO βA χ

example (θ φ : ℝ) :
    dualRotorMat (EuclideanSpace.single 2 (θ + φ)) =
      dualRotorMat (EuclideanSpace.single 2 θ) *
        dualRotorMat (EuclideanSpace.single 2 φ) :=
  dualRotorMat_axis2_add θ φ

example (β : DualRapidity) :
    (dualRotorMat β).trace =
      dualRotorAmplitude β spinUp + dualRotorAmplitude β spinDown :=
  dualRotorMat_trace_eq_amplitudes β

/-- Regression: half-trace character is the real part of the spin-up element. -/
example (β : DualRapidity) :
    (dualRotorAmplitude β spinUp).re = Real.cos (‖β‖ / 2) :=
  dualRotorAmplitude_spinUp_re β

example : dualRotorMat (EuclideanSpace.single 2 (2 * Real.pi)) = -1 :=
  dualRotorMat_axis2_two_pi

example (βO βA : DualRapidity) :
    ((dualRotorMat βO).conjTranspose * dualRotorMat βA).conjTranspose *
        ((dualRotorMat βO).conjTranspose * dualRotorMat βA) = 1 ∧
      ((dualRotorMat βO).conjTranspose * dualRotorMat βA).det = 1 :=
  ⟨dualRotor_relative_unitary βO βA, dualRotor_relative_det βO βA⟩

example :
    dualRotorMat (EuclideanSpace.single 0 Real.pi) *
        dualRotorMat (EuclideanSpace.single 2 Real.pi) ≠
      dualRotorMat (EuclideanSpace.single 2 Real.pi) *
        dualRotorMat (EuclideanSpace.single 0 Real.pi) :=
  dualRotorMat_axes_not_commute

example (β : DualRapidity) :
    dualRotorMat (-β) = (dualRotorMat β).conjTranspose :=
  dualRotorMat_neg β

example (s t : ℝ) (β : DualRapidity) :
    dualRotorMat ((s + t) • β) =
      dualRotorMat (s • β) * dualRotorMat (t • β) :=
  dualRotorMat_ray_add s t β

example (s t : ℝ) (β : DualRapidity) :
    (dualRotorMat (s • β)).conjTranspose * dualRotorMat (t • β) =
      dualRotorMat ((t - s) • β) :=
  dualRotor_relative_ray s t β

example (β γ : DualRapidity) :
    (dualRotorMat β * dualRotorMat γ).trace =
      2 * ((Real.cos (‖β‖ / 2) : ℂ) * Real.cos (‖γ‖ / 2) -
        (dualAxisInner β γ : ℂ) * Real.sin (‖β‖ / 2) * Real.sin (‖γ‖ / 2)) :=
  dualRotorMat_mul_trace β γ

example (βO βA : DualRapidity) :
    ((dualRotorMat βO).conjTranspose * dualRotorMat βA).trace =
      2 * ((Real.cos (‖βO‖ / 2) : ℂ) * Real.cos (‖βA‖ / 2) +
        (dualAxisInner βO βA : ℂ) * Real.sin (‖βO‖ / 2) * Real.sin (‖βA‖ / 2)) :=
  dualRotor_relative_trace βO βA

example :
    dualRotorMat (EuclideanSpace.single 0 Real.pi) *
        dualRotorMat (EuclideanSpace.single 2 Real.pi) *
          (dualRotorMat (EuclideanSpace.single 0 Real.pi)).conjTranspose *
            (dualRotorMat (EuclideanSpace.single 2 Real.pi)).conjTranspose =
      -1 :=
  dualRotorMat_axes_group_commutator

example :
    commutingSpinorIdem ≠ 0 ∧
      ∃ x ∈ leftIdealOf commutingSpinorIdem, x ≠ 0 :=
  ⟨commutingSpinorIdem_ne_zero, leftIdeal_commutingSpinorIdem_nontrivial⟩

example : ∃ p q : TorsionParams, interfere p q = 0 ∧ ¬ SameAxis p q :=
  compatible_not_implies_same_axis

example (μ ν : Fin 4) :
    diracMat μ * diracMat ν + diracMat ν * diracMat μ =
      (2 * minkowskiEta μ ν : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) :=
  diracMat_clifford μ ν

/-- Regression: dual \(\mathbb{C}^2\) is not the Dirac \(\mathbb{C}^4\). -/
example : Module.finrank ℂ DualSpinor ≠ Module.finrank ℂ DiracSpinor :=
  dualSpinor_ne_diracSpinor

example : Module.finrank ℝ (leftIdealSub commutingSpinorIdem) = 8 :=
  finrank_leftIdeal_commuting

example : Module.finrank ℝ minkowskiLeftIdeal = 4 :=
  finrank_minkowskiLeftIdeal

example :
    minkowskiLeftIdeal ⊔ nullSlice = leftIdealSub commutingSpinorIdem ∧
      minkowskiLeftIdeal ⊓ nullSlice = (⊥ : Submodule ℝ PGA) :=
  leftIdeal_directSum_null

/-- Regression: the null copy is a proper left PGA-submodule, so the ideal is reducible. -/
example :
    nullSlice ≠ (⊥ : Submodule ℝ PGA) ∧
      nullSlice ≠ leftIdealSub commutingSpinorIdem :=
  ⟨nullSlice_is_proper_submodule.2.1, nullSlice_is_proper_submodule.2.2.1⟩

/-- Regression: Dirac spinor has real dimension eight (matches the left ideal). -/
example : Module.finrank ℝ DiracSpinor = 8 :=
  diracSpinor_finrank_real

example (β : DualRapidity) :
    Motor.rotorTorsion (ofDual β) =
      Real.cos (‖β‖ / 2) • (1 : PGA) +
        (if h : β = 0 then (0 : PGA)
          else Real.sin (‖β‖ / 2) • cyclicUnit β h) :=
  rotorTorsion_ofDual β

example (β : DualRapidity) :
    dualRotorMat β =
      Real.cos (‖β‖ / 2) • (1 : Matrix (Fin 2) (Fin 2) ℂ) +
        (if _h : β = 0 then (0 : Matrix (Fin 2) (Fin 2) ℂ)
          else Real.sin (‖β‖ / 2) • cyclicRepComb (fun a => β a / ‖β‖)) :=
  dualRotorMat_rodrigues β

example (α : UsualRapidity) :
    Motor.rotorTorsion (ofUsual α) =
      Real.cosh (‖α‖ / 2) • (1 : PGA) +
        (if h : α = 0 then (0 : PGA)
          else Real.sinh (‖α‖ / 2) • hyperbolicUnit α h) :=
  rotorTorsion_ofUsual α

example (θ : ℝ) :
    Motor.rotorTorsion (ofUsual (EuclideanSpace.single 0 θ)) =
      Real.cosh (θ / 2) • (1 : PGA) + Real.sinh (θ / 2) • Generators.hyperbolic 0 :=
  rotorTorsion_ofUsual_axis0 θ

example (α : UsualRapidity) :
    (usualRotorMat α).IsHermitian ∧ (usualRotorMat α).det = 1 :=
  ⟨usualRotorMat_isHermitian α, usualRotorMat_det α⟩

/-- Regression: a nonzero usual boost is not unitary. -/
example :
    (usualRotorMat (EuclideanSpace.single 0 (2 : ℝ))).conjTranspose *
      usualRotorMat (EuclideanSpace.single 0 (2 : ℝ)) ≠ 1 :=
  usualRotorMat_axis0_not_unitary

example (α : UsualRapidity) :
    usualRotorMat α =
      Real.cosh (‖α‖ / 2) • (1 : Matrix (Fin 2) (Fin 2) ℂ) +
        (if α = 0 then (0 : Matrix (Fin 2) (Fin 2) ℂ)
          else Real.sinh (‖α‖ / 2) • pauliComb (fun a => α a / ‖α‖)) :=
  usualRotorMat_rodrigues α

example (Ψ : DiracSpinor) :
    weylUpper (diracUpper Ψ) + weylLower (diracLower Ψ) = Ψ :=
  weyl_decompose Ψ

example : diracMat5 * diracMat5 = 1 :=
  diracMat5_sq

example : weylProjPlus * weylProjPlus = weylProjPlus ∧
    weylProjMinus * weylProjMinus = weylProjMinus ∧
      weylProjPlus + weylProjMinus = 1 :=
  ⟨weylProjPlus_sq, weylProjMinus_sq, weylProjPlus_add_minus⟩

example (ψ : DualSpinor) :
    applyDiracMat diracMat5 (weylUpper ψ) = weylUpper ψ :=
  applyDiracMat5_weylUpper ψ

example (ψ : DualSpinor) :
    applyDiracMat diracMat5 (weylLower ψ) = -weylLower ψ :=
  applyDiracMat5_weylLower ψ

example (p : Vec4) :
    slashCl p * slashCl p = algebraMap ℝ Cl31 (minkowskiQ p) :=
  slashCl_sq p

example (p : Vec4) :
    slashMat p * slashMat p = (minkowskiQ p : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) :=
  slashMat_sq p

example {m : ℝ} {p : Vec4} {Ψ : DiracSpinor}
    (hΨ : Ψ ≠ 0) (h : DiracMomentum m p Ψ) :
    minkowskiQ p = -m ^ 2 :=
  diracMomentum_implies_mass_shell hΨ h

example (m : ℝ) :
    ∃ Ψ : DiracSpinor, Ψ ≠ 0 ∧ DiracMomentum m (restMomentum m) Ψ :=
  exists_rest_particle m

example (p : Vec4) :
    pauliSlash p * pauliSlashBar p = (minkowskiQ p : ℂ) • 1 :=
  pauliSlash_mul_pauliSlashBar p

/-- Regression: the on-shell Weyl construction recovers the rest pair \((u,iu)\). -/
example {m : ℝ} (hm : m ≠ 0) (u : DualSpinor) :
    onShellParticleSpinor m (restMomentum m) u = restParticleSpinor u :=
  onShellParticleSpinor_rest hm u

example {m : ℝ} {p : Vec4} (hm : m ≠ 0) (hQ : minkowskiQ p = -m ^ 2)
    (u : DualSpinor) :
    DiracMomentum m p (onShellParticleSpinor m p u) :=
  onShellParticle_dirac hm hQ u

example (m α : ℝ) : minkowskiQ (boostZMomentum m α) = -m ^ 2 :=
  minkowskiQ_boostZ m α

example {m α : ℝ} (hm : m ≠ 0) (u : DualSpinor) :
    applyDiracBoostZ α (restParticleSpinor u) =
      onShellParticleSpinor m (boostZMomentum m α)
        (applyMat (chiralBoostZ α) u) :=
  applyDiracBoostZ_rest hm u

example (α θ : ℝ) :
    chiralBoostZ α * dualRotorMat (EuclideanSpace.single 2 θ) =
      dualRotorMat (EuclideanSpace.single 2 θ) * chiralBoostZ α :=
  chiralBoostZ_comm_dualRotor_axis2 α θ

example :
    chiralBoostZ 2 * dualRotorMat (EuclideanSpace.single 0 Real.pi) ≠
      dualRotorMat (EuclideanSpace.single 0 Real.pi) * chiralBoostZ 2 :=
  chiralBoostZ_not_comm_dualRotor_axis0

example (β : DualRapidity) (u : DualSpinor) :
    inner ℂ (restParticleSpinor u)
        (restParticleSpinor (applyMat (dualRotorMat β) u)) =
      2 * dualRotorAmplitude β u :=
  restParticle_dualRotor_overlap β u

example (α : ℝ) (β : DualRapidity) (u : DualSpinor) :
    inner ℂ
        (applyDiracBoostZ α (restParticleSpinor u))
        (applyDiracBoostZ α
          (restParticleSpinor (applyMat (dualRotorMat β) u))) =
      (Real.cosh α : ℂ) *
        inner ℂ (restParticleSpinor u)
          (restParticleSpinor (applyMat (dualRotorMat β) u)) :=
  boostedRest_overlap_factor α β u

example (α : ℝ) :
    (∀ (β : DualRapidity) (u : DualSpinor),
      inner ℂ
          (applyDiracBoostZ α (restParticleSpinor u))
          (applyDiracBoostZ α
            (restParticleSpinor (applyMat (dualRotorMat β) u))) =
        inner ℂ (restParticleSpinor u)
          (restParticleSpinor (applyMat (dualRotorMat β) u))) ↔
      α = 0 :=
  boostedRest_overlap_eq_rest_iff α

example {p : Vec4} {Ψ : DiracSpinor} (h : DiracMomentum 0 p Ψ) :
    applyMat (pauliSlash p) (diracLower Ψ) = 0 ∧
      applyMat (pauliSlashBar p) (diracUpper Ψ) = 0 :=
  dirac_massless_decouple h

example {m : ℝ} {p : Vec4} {Ψ : DiracSpinor} (h : DiracMomentum m p Ψ) :
    DiracMomentum (-m) p (applyDiracMat diracMat5 Ψ) :=
  diracMat5_flips_mass h

example {M : Matrix (Fin 2) (Fin 2) ℂ} (hM : M.det = 1) {m : ℝ} {p : Vec4}
    {Ψ : DiracSpinor} (h : DiracMomentum m p Ψ) :
    DiracMomentum m (lorentzAct M p) (rotorDirac M Ψ) :=
  diracMomentum_rotorDirac hM h

example {M : Matrix (Fin 2) (Fin 2) ℂ} (hM : M.det = 1) (Ψ Φ : DiracSpinor) :
    diracScalar (rotorDirac M Ψ) (rotorDirac M Φ) = diracScalar Ψ Φ :=
  diracScalar_rotorDirac hM Ψ Φ

example {M : Matrix (Fin 2) (Fin 2) ℂ} (hM : M.det = 1) :
    ∃ (α : UsualRapidity) (β : DualRapidity), M = usualRotorMat α * dualRotorMat β :=
  totalRotor_factor hM

/-- Regression: the little group of the rest momentum is the dual sector. -/
example {M : Matrix (Fin 2) (Fin 2) ℂ} (hM : M.det = 1) {m : ℝ} (hm : m ≠ 0) :
    lorentzAct M (restMomentum m) = restMomentum m ↔
      ∃ β : DualRapidity, M = dualRotorMat β :=
  lorentzAct_rest_iff_dualRotor hM hm

example (φ θ m : ℝ) (α : UsualRapidity) (β : DualRapidity) {p : Vec4}
    {Ψ : DiracSpinor} (h : DiracMomentum m p Ψ)
    (hturn : m * Real.sinh φ * Real.sin θ ≠ 0) :
    minkowskiQ (lorentzAct (usualRotorMat α * dualRotorMat β) p) = minkowskiQ p ∧
      minkowskiQ (lorentzAct (dualRotorMat β * usualRotorMat α) p) = minkowskiQ p ∧
      DiracMomentum m (lorentzAct (usualRotorMat α * dualRotorMat β) p)
        (rotorDirac (usualRotorMat α * dualRotorMat β) Ψ) ∧
      DiracMomentum m (lorentzAct (dualRotorMat β * usualRotorMat α) p)
        (rotorDirac (dualRotorMat β * usualRotorMat α) Ψ) ∧
      lorentzAct (dualRotorMat (EuclideanSpace.single 2 θ) *
          usualRotorMat (EuclideanSpace.single 0 φ)) (restMomentum m) 0 =
        m * Real.cosh φ ∧
      lorentzAct (dualRotorMat (EuclideanSpace.single 2 θ) *
          usualRotorMat (EuclideanSpace.single 0 φ)) (restMomentum m) ≠
        lorentzAct (usualRotorMat (EuclideanSpace.single 0 φ) *
          dualRotorMat (EuclideanSpace.single 2 θ)) (restMomentum m) := by
  refine ⟨(both_orders_preserve_mass α β p).1, (both_orders_preserve_mass α β p).2,
    (both_orders_send_solution α β h).1, (both_orders_send_solution α β h).2, ?_,
    dualLeft_turns_rest_momentum hturn⟩
  have henergy := orders_same_energy φ θ m
  rw [lorentzAct_factor_rest, axis0_rest_momentum] at henergy
  simpa using henergy

/-- Regression: Thomas–Wigner rotation about the perpendicular axis. -/
example {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    ∃ (α : UsualRapidity) (φ : ℝ),
      usualRotorMat (EuclideanSpace.single 0 a) * usualRotorMat (EuclideanSpace.single 2 b) =
        usualRotorMat α * dualRotorMat (EuclideanSpace.single 1 φ) ∧
      dualRotorMat (EuclideanSpace.single 1 φ) ≠ 1 :=
  usualRotor_perp_wigner ha hb

example {m : ℝ} {p : Vec4} {Ψ Φ : DiracSpinor} (hΨ : DiracMomentum m p Ψ)
    (hΦ : DiracMomentum m p Φ) (μ : Fin 4) :
    (m : ℂ) * diracCurrent μ Ψ Φ =
      -Complex.I * ((minkowskiEta μ μ * p μ : ℝ) : ℂ) * diracScalar Ψ Φ :=
  diracCurrent_gordon hΨ hΦ μ

example {m : ℝ} {p : Vec4} {Ψ : DiracSpinor} (hm : m ≠ 0) (hΨ : Ψ ≠ 0)
    (h : DiracMomentum m p Ψ) :
    minkowskiQ (realCurrent Ψ) = -((diracScalar Ψ Ψ).re) ^ 2 :=
  minkowskiQ_realCurrent hm hΨ h

example (m : ℝ) (p : Vec4) (u : DiracSpinor) :
    DiracField m (planeWave p u) ↔ DiracMomentum m p u :=
  diracField_planeWave_iff m p u

example (p : Vec4) (u : DiracSpinor) (x : Vec4) :
    bornDensity (planeWave p u) x = ‖u‖ ^ 2 :=
  bornDensity_planeWave p u x

example {m : ℝ} {p q : Vec4} {Ψ : DiracSpinor} (hm : m ≠ 0) (hΨ : Ψ ≠ 0)
    (hp : DiracMomentum m p Ψ) (hq : DiracMomentum m q Ψ) : p = q :=
  diracMomentum_unique hm hΨ hp hq

example {p q : Vec4} (hpq : p ≠ q) {u v : DiracSpinor} (hu : u ≠ 0) (hv : v ≠ 0)
    (r : Vec4) : ¬ MomentumEigen r (momentumSum p q u v) :=
  momentumSum_not_eigen hpq hu hv r

example (p q : Vec4) (u : DiracSpinor) (x : Vec4) :
    bornDensity (equalPacket p q u) x =
      4 * Real.cos (wavePhase (q - p) x / 2) ^ 2 * ‖u‖ ^ 2 :=
  bornDensity_equalPacket p q u x

example (k a p : Vec4) (u : DiracSpinor) (x : Vec4) :
    chartTranslate a (momentumKick k (planeWave p u)) x =
      Complex.exp (Complex.I * (wavePhase k a : ℂ)) •
        momentumKick k (chartTranslate a (planeWave p u)) x :=
  weyl_shift_kick k a p u x

example {N : ℕ} [NeZero N] (μ : Fin 4) (f : ZMod N → ℂ) (u : DiracSpinor) (j : ZMod N) :
    angleChartField μ f u (angleChartPoint μ j) = (f j) • u :=
  angleChartField_sample μ f u j

example {N : ℕ} [NeZero N] (μ : Fin 4) (s : ZMod N) (f : ZMod N → ℂ) (u : DiracSpinor) :
    chartTranslate (angleChartPoint μ s) (angleChartField μ f u) =
      angleChartField μ (DualFourier.dualCircleShift (-s) f) u :=
  angleChartField_translate μ s f u

example {m : ℝ} {Ψ Φ : Vec4 → DiracSpinor} (hΨ : DiracField m Ψ) (hΦ : DiracField m Φ)
    (x : Vec4) :
    ∑ μ : Fin 4, fderiv ℝ (currentField Ψ Φ μ) x (Pi.single μ 1) = 0 :=
  currentField_conserved hΨ hΦ x

example (β : DualRapidity) (Ψ : DiracSpinor) :
    ‖rotorDirac (dualRotorMat β) Ψ‖ = ‖Ψ‖ :=
  norm_rotorDirac_dualRotor β Ψ

example {m : ℝ} {M : Matrix (Fin 2) (Fin 2) ℂ} {Ψ : Vec4 → DiracSpinor} (hM : M.det = 1)
    (hΨ : DiracField m Ψ) : DiracField m (rotorField M Ψ) :=
  diracField_rotorField hM hΨ

example {m e : ℝ} {A : Vec4 → Vec4} {χ : Vec4 → ℝ} {Ψ : Vec4 → DiracSpinor}
    (hχ : Differentiable ℝ χ) (hΨ : DiracGaugeField m e A Ψ) :
    DiracGaugeField m e (gaugePot A χ) (gaugePhase e χ Ψ) :=
  diracGaugeField_gauge hχ hΨ

example (m e : ℝ) (a p : Vec4) (u : DiracSpinor) :
    DiracGaugeField m e (fun _ => a) (planeWave p u) ↔ DiracMomentum m (p - e • a) u :=
  diracGaugeField_planeWave_iff m e a p u

example {e : ℝ} {A : Vec4 → Vec4} {Ψ : Vec4 → DiracSpinor} (hA : Differentiable ℝ A)
    (hΨ : ContDiff ℝ 2 Ψ) (μ ν : Fin 4) (x : Vec4) :
    covD e A (covD e A Ψ ν) μ x - covD e A (covD e A Ψ μ) ν x =
      (-(Complex.I * ((e * fieldStrength A x μ ν : ℝ) : ℂ))) • Ψ x :=
  covD_comm e hA hΨ μ ν x

example {m e : ℝ} {A : Vec4 → Vec4} {Ψ : Vec4 → DiracSpinor} (hA : Differentiable ℝ A)
    (hΨ2 : ContDiff ℝ 2 Ψ) (hΨ : DiracGaugeField m e A Ψ) (x : Vec4) :
    diracUpper (∑ μ : Fin 4, (minkowskiEta μ μ : ℂ) • covD e A (covD e A Ψ μ) μ x) +
        applyMat ((e : ℂ) • (pauliComb (magVec (fieldStrength A x)) +
          Complex.I • pauliComb (elecVec (fieldStrength A x)))) (diracUpper (Ψ x)) =
      ((m : ℂ) ^ 2) • diracUpper (Ψ x) :=
  diracGaugeField_pauli_upper hA hΨ2 hΨ x

example (n : Fin 3 → ℝ) : pauliComb n = Complex.I • cyclicRepComb n :=
  pauliComb_eq_I_cyclicRepComb n

example {m : ℝ} {Ψ : Vec4 → DiracSpinor} (hΨ2 : ContDiff ℝ 2 Ψ) (hΨ : DiracField m Ψ)
    (x : Vec4) :
    ∑ μ : Fin 4, (minkowskiEta μ μ : ℂ) • partialD (fun y => partialD Ψ μ y) μ x =
      ((m : ℂ) ^ 2) • Ψ x :=
  diracField_kleinGordon hΨ2 hΨ x

example {m : ℝ} {p : Vec4} {Ψ : DiracSpinor} (h : DiracMomentum m p Ψ) :
    DiracMomentum m (-p) (dualFlip Ψ) :=
  diracMomentum_dualFlip h

example {m e : ℝ} {A : Vec4 → Vec4} {Ψ : Vec4 → DiracSpinor}
    (hΨ : DiracGaugeField m e A Ψ) : DiracGaugeField m (-e) A (conjField Ψ) :=
  diracGaugeField_conjField hΨ

example {m : ℝ} {p : Vec4} {Ψ : DiracSpinor} (h : DiracMomentum m p Ψ) :
    DiracMomentum m p (antiparticle Ψ) :=
  diracMomentum_antiparticle h

/-- Regression: at rest the antiparticle of `(u, iu)` is `-(J u, i J u)`. -/
example (u : DualSpinor) : antiparticle (restParticleSpinor u) = -restParticleSpinor (quatJ u) :=
  antiparticle_restParticle u

example {m e : ℝ} {A : Vec4 → Vec4} {Ψ : Vec4 → DiracSpinor}
    (hΨ : DiracGaugeField m e A Ψ) :
    DiracGaugeField m (-e) (reflectPot A) (antiparticleField Ψ) :=
  diracGaugeField_antiparticleField hΨ

example {Ψ : PairState}
    (h : ∀ β : DualRapidity, pairAct (dualRotorMat β) (dualRotorMat β) Ψ = Ψ) :
    Ψ = Ψ 0 1 • singlet :=
  eq_smul_singlet_of_dualRotor_fixed h

example {u : DualSpinor} (hu : ‖u‖ = 1) :
    pairTensor (quatJ u) u - pairTensor u (quatJ u) = singlet :=
  quatJ_pair_eq_singlet_of_norm hu

example (Ψ : PairState) : (∃ u v : DualSpinor, Ψ = pairTensor u v) ↔ Ψ.det = 0 :=
  exists_pairTensor_iff_det Ψ

example (a b : Fin 3 → ℝ) : singletCorr a b = -axisDot a b :=
  singletCorr_eq a b

example (β : DualRapidity) (B : Matrix (Fin 2) (Fin 2) ℂ) (Ψ : PairState) :
    pairInner (pairAct (dualRotorMat β) 1 Ψ) (pairAct 1 B (pairAct (dualRotorMat β) 1 Ψ)) =
      pairInner Ψ (pairAct 1 B Ψ) :=
  pairInner_local_dualRotor β B Ψ

/-- Regression: the singlet reaches `|S| = 2√2` in the CHSH combination. -/
example : chsh singletCorr ![0, 0, 1] ![1, 0, 0]
    ![1 / Real.sqrt 2, 0, 1 / Real.sqrt 2] ![-(1 / Real.sqrt 2), 0, 1 / Real.sqrt 2] =
      -(2 * Real.sqrt 2) :=
  singletCorr_chsh

example {u : DualSpinor} (hu : ‖u‖ = 1) :
    axisDot (spinVec u) (spinVec u) = 1 :=
  axisDot_spinVec_of_norm hu

example (β : DualRapidity) (u : DualSpinor) :
    ‖u + applyMat (dualRotorMat β) u‖ ^ 2 =
      4 * Real.cos (‖β‖ / 4) ^ 2 * ‖u‖ ^ 2 :=
  norm_add_dualRotor_sq β u

example {u : DualSpinor} (hu : ‖u‖ = 1) (a b : Fin 3 → ℝ) :
    ‖spinExp (pauliComb a * pauliComb b - pauliComb b * pauliComb a) u‖ ^ 2 / 4 ≤
      spinVar a u * spinVar b u :=
  robertson_spin hu a b

example {Ψ : PairState} (hΨ : pairNormSq Ψ = 1) :
    axisDot (leftSpinVec Ψ) (leftSpinVec Ψ) = 1 - (2 * ‖Ψ.det‖) ^ 2 :=
  (axisDot_spinVec_pair_of_norm hΨ).1

example {u : DualSpinor} (hu : u ≠ 0) (c : ℂ) :
    pairTensor u (c • u) - pairTensor (c • u) u = 0 :=
  (pairTensor_sub_swap_eq_zero_iff hu (c • u)).mpr ⟨c, rfl⟩

example (u : DualSpinor) : spinVec (quatJ u) = fun k => -spinVec u k :=
  spinVec_quatJ u

example {u : DualSpinor} (hu : u ≠ 0) (v : DualSpinor) :
    inner ℂ u v = 0 ↔ ∃ c : ℂ, v = c • quatJ u :=
  inner_eq_zero_iff_smul_quatJ hu v

example {u v w : DualSpinor} (hu : u ≠ 0) (hv : v ≠ 0)
    (huv : inner ℂ u v = 0) (huw : inner ℂ u w = 0) (hvw : inner ℂ v w = 0) :
    w = 0 :=
  eq_zero_of_orthogonal_pair hu hv huv huw hvw

example : ∑ k, pairSpin k (pairSpin k singlet) = 0 :=
  sum_pairSpin_sq_singlet

/-- Regression: MW real 16 matches WeylSU4 real 16 (no Spin equivariance). -/
example : Module.finrank ℝ MajoranaWeyl10 = Module.finrank ℝ WeylSU4 :=
  majorana_dim_eq_weylSU4_real

example (u : DualSpinor) : DiracMomentum 0 (manifest u) (weylUpper u) :=
  dirac_upper_manifest u

example (u l : DualSpinor) :
    realCurrent (weylUpper u + weylLower l) = spaceReverse (manifest u) + manifest l :=
  realCurrent_weyl u l

/-- Regression: the rest pair's current is timelike, and the sum of its two filter images is not. -/
example {u : DualSpinor} (hu : u ≠ 0) :
    Q31 (realCurrent (restParticleSpinor u)) < 0 ∧
      realCurrent (restParticleSpinor u) ≠ manifest u + manifest (Complex.I • u) :=
  ⟨Q31_realCurrent_rest_timelike hu, realCurrent_rest_ne_manifest_sum hu⟩

/-- Regression: the spin curve solves the Pauli equation and holds the chart's time component at the
information weight. A nonzero energy makes the de Broglie phase along that axis move. -/
example (ω : DualRapidity) (u : DualSpinor) {p : Vec4} (hp : p 0 ≠ 0) (t : ℝ) :
    Complex.I • deriv (spinCurve ω u) t =
        (1 / 2 : ℂ) • applyMat (pauliComb (fun a => ω a)) (spinCurve ω u t) ∧
      manifest (spinCurve ω u t) 0 = manifest u 0 ∧
      ∃ s : ℝ, wavePhase p (s • (Pi.single 0 (1 : ℝ) : Vec4)) ≠ 0 :=
  ⟨spinCurve_schrodinger ω u t, spinCurve_manifest_time ω u t,
    (spin_parameter_not_chart_time ω u hp).2⟩

example (e m : ℝ) (A : Vec4 → Vec4) (φ : Vec4 → DualSpinor)
    (hA : Differentiable ℝ A) (hφ : ContDiff ℝ 2 φ) (hm : m ≠ 0)
    (B : DualRapidity) (u : DualSpinor) (x : Vec4) (t α : ℝ) :
    sigmaPiSq e A φ x =
      kinSq e A φ x +
        applyMat ((-(e : ℂ)) • pauliComb (magVec (fieldStrength A x))) (φ x) ∧
      Complex.I • deriv (spinCurve (magneticRapidity e m B) u) t =
        applyMat (((-(e / (2 * m)) : ℝ) : ℂ) • pauliComb (fun a => B a))
          (spinCurve (magneticRapidity e m B) u t) ∧
      ‖magneticRapidity e m B‖ = |e| * ‖B‖ / |m| ∧
      ((-(e / (2 * m)) : ℝ) : ℂ) • pauliComb (fun a => B a) ≠ phaseGate α ∧
      (((e : ℂ) • (pauliComb (fun a => B a) + Complex.I • pauliComb (fun a => B a)) =
          (e : ℂ) • (pauliComb (fun a => B a) - Complex.I • pauliComb (fun a => B a))) ↔
        e = 0 ∨ (fun a => B a) = 0) :=
  ⟨sigmaPi_sq_split e (A := A) (φ := φ) hA hφ x, spinCurve_magnetic e m B u hm t,
    magnetic_rapidity_norm e m B hm, magneticSpin_ne_phaseGate e m (fun a => B a) α hm,
    fieldBlocks_eq_iff e (fun a => B a) (fun a => B a)⟩

example (V : ℝ) (p : Vec4) (u : DiracSpinor) (x : Vec4) :
    ((∀ t : ℝ, ∃ β : DualRapidity, dualRotorMat β = phaseGate (-(V * t))) ↔ V = 0) ∧
      Complex.exp (-(Complex.I * (wavePhase p x : ℂ))) • planeWave p u x = u :=
  ⟨constPotential_dualRotor_iff V, planeWave_strip p u x⟩

example {k : Vec4} (hk : k ≠ 0) :
    ∃ a : Vec4, ∀ β : DualRapidity, dualRotorMat β ≠ phaseGate (wavePhase k a) :=
  kick_not_dualRotor hk

/-- Regression: the dual spinor space carries no canonical pair. -/
example (A B : DualSpinor →ₗ[ℂ] DualSpinor) :
    A.comp B - B.comp A ≠ Complex.I • LinearMap.id :=
  no_ccr_dualSpinor A B

/-- Regression: Newton–Wigner position is not a carrier operator. One momentum has no chart-position
information; two momenta do, and the fringe is not boxed. The axis packet has contrast `4`. -/
example (Q P : DiracSpinor →ₗ[ℂ] DiracSpinor) {u : DiracSpinor} (hu : u ≠ 0)
    (p q : Vec4) (hpq : p ≠ q) :
    ¬ NewtonWignerPair Q P ∧
      ¬ ChartPositionInfo (planeWave p u) ∧
      ChartPositionInfo (equalPacket p q u) ∧
      ¬ BoxLocalized (equalPacket p q u) ∧
      chartContrast (equalPacket 0 (Pi.single 1 1) (EuclideanSpace.single 0 1)) 0
          (Pi.single 1 Real.pi) = 4 :=
  ⟨no_newtonWignerPair_dirac Q P, planeWave_no_chartPositionInfo p u,
    equalPacket_chartPositionInfo hpq hu, equalPacket_not_boxLocalized hpq hu,
    axis_fringe_contrast⟩

/-- Regression: fringe visibility and which-momentum distinguishability are complementary.
A definite momentum carries no chart-position information. Equal weights have visibility `1`. -/
example (r s : ℝ) (h : r ^ 2 + s ^ 2 ≠ 0) (α : ℝ) (p q : Vec4) (u : DiracSpinor) :
    whichMomentum r s ^ 2 + fringeVisibility r s ^ 2 = 1 ∧
      whichMomentum 1 (1 / 2) = 3 / 5 ∧
      fringeVisibility 1 (1 / 2) = 4 / 5 ∧
      ¬ ChartPositionInfo (phasedPacket r 0 α p q u) ∧
      fringeVisibility 1 1 = 1 :=
  ⟨whichMomentum_sq_add_fringeVisibility r s h, half_weight_information.1,
    half_weight_information.2.1, phasedPacket_definite_no_chartPositionInfo r α p q u,
    fringeVisibility_equal (by norm_num)⟩

/-- Regression: phase information is `V²`, and complements which-momentum distinguishability.
The weight formula can be `1` with no chart contrast. Distinct momenta read it on one carrier
ray. -/
example (r s : ℝ) (h : r ^ 2 + s ^ 2 ≠ 0) {t : ℝ} (ht : t ≠ 0) (α : ℝ) (p q : Vec4)
    (hpq : p ≠ q) {u : DiracSpinor} (hu : u ≠ 0) :
    whichMomentum r s ^ 2 + phaseInformation r s = 1 ∧
      phaseInformation 1 (1 / 2) = 16 / 25 ∧
      phaseInformation t t = 1 ∧
      ¬ ChartPositionInfo (phasedPacket t t α p p u) ∧
      ChartPositionInfo (phasedPacket t t α p q u) ∧
      (∀ x, ∃ z : ℂ, phasedPacket t t α p q u x = z • u) :=
  ⟨whichMomentum_sq_add_phaseInformation r s h, half_weight_phaseInformation.1,
    phaseInformation_equal ht, (phaseInformation_not_a_location ht α p u).2,
    phasedPacket_equal_chartPositionInfo ht hpq hu α,
    fun x => ⟨_, phasedPacket_eq_smul t t α p q u x⟩⟩

/-- Regression: on one mass shell the information is fidelity squared times the single-carrier
phase information. The mean-rest mass-3 pair has information `81/625`, and its fringe does not
move in time. One spinor cannot carry both shell momenta. -/
example (α : ℝ) :
    shellInformation 1 1 shellParticleP shellParticleQ = 81 / 625 ∧
      carrierFidelity shellParticleP shellParticleQ = 9 / 25 ∧
        (shellRestQ - shellRestP) 0 = 0 ∧
          ¬ (DiracMomentum 3 shellRestP shellParticleP ∧
              DiracMomentum 3 shellRestQ shellParticleP) :=
  ⟨shellRest_regression α |>.2.2.2.1, shellRest_regression α |>.2.2.1,
    shellRest_regression α |>.2.1, shellRest_regression α |>.2.2.2.2.2.2⟩

/-- Regression: the complement of which-momentum splits into shell information and a carrier
deficit. Mean rest leaves `544/625` unread. The time-axis pair has `D = 8/17`, visibility
`12/17`, and deficit `81/289`. The opposite seed puts the whole complement in the deficit. -/
example :
    shellDeficit 1 1 shellParticleP shellParticleQ = 544 / 625 ∧
      whichMomentum ‖shellParticleP‖ ‖shellLabSpinor‖ = 8 / 17 ∧
        shellDeficit 1 1 shellParticleP shellLabSpinor = 81 / 289 ∧
          shellDeficit 1 1 shellParticleP shellOrthQ = 1 ∧
            whichMomentum ‖shellParticleP‖ ‖shellParticleQ‖ ^ 2 +
                shellInformation 1 1 shellParticleP shellParticleQ +
                  shellDeficit 1 1 shellParticleP shellParticleQ =
              1 :=
  ⟨shellRest_split.2.2.1, shellLab_split.1, shellLab_split.2.2.1, shellOrth_deficit.2.2.2,
    shellRest_split.2.2.2⟩

/-- Regression: off the mean rest frame the same mass and seed are read on the time axis.
Equal weights have fidelity `4/5` and information `144/289`, not the mean-rest value `81/625`.
The origin sample lies on neither carrier ray. The opposite Weyl seed carries information `0`. -/
example :
    shellInformation 1 1 shellParticleP shellLabSpinor = 144 / 289 ∧
      carrierFidelity shellParticleP shellLabSpinor = 4 / 5 ∧
        bornDensity (shellPacket 1 1 0 shellRestP (restMomentum 3) shellParticleP shellLabSpinor)
            (timeShift (-Real.pi / 2)) = 20 / 9 ∧
          (∀ z : ℂ, shellPacket 1 1 0 shellRestP (restMomentum 3)
              shellParticleP shellLabSpinor 0 ≠ z • shellParticleP) ∧
            shellInformation 1 1 shellParticleP shellOrthQ = 0 :=
  ⟨shellLab_information.1, shellLab_fidelity, shellLab_time_density.2.1,
    shellLab_sample_leaves_ray.1, shellOrth_silent 0 |>.2.1⟩

/-- Regression: projective Fisher information equals the carrier deficit at a quadrature phase.
Mean rest reads `544/625` there, and `136/289`, `17/8` at the extremes. The time-axis pair reads
`81/841`, `81/25`, and `81/289`. The opposite seed reads `1`. -/
example :
    (∃ θ : ℝ, phaseFisher 1 1 shellParticleP shellParticleQ θ = 544 / 625) ∧
      (∃ θ : ℝ, phaseFisher 1 1 shellParticleP shellParticleQ θ = 136 / 289) ∧
        (∃ θ : ℝ, phaseFisher 1 1 shellParticleP shellParticleQ θ = 17 / 8) ∧
          phaseFisher 1 1 shellParticleP shellLabSpinor
              (wavePhase (restMomentum 3 - shellRestP) (timeShift 0)) = 81 / 841 ∧
            phaseFisher 1 1 shellParticleP shellLabSpinor
                (wavePhase (restMomentum 3 - shellRestP) (timeShift (-Real.pi / 2))) = 81 / 25 ∧
              (∃ t : ℝ,
                phaseFisher 1 1 shellParticleP shellLabSpinor
                    (wavePhase (restMomentum 3 - shellRestP) (timeShift t)) = 81 / 289) ∧
                (∀ θ : ℝ, phaseFisher 1 1 shellParticleP shellOrthQ θ = 1) := by
  refine ⟨?_, ?_, ?_, shellLab_phaseFisher.1, shellLab_phaseFisher.2.1, ?_, ?_⟩
  · obtain ⟨θ, _, h⟩ := shellRest_phaseFisher.1
    exact ⟨θ, h⟩
  · obtain ⟨θ, _, h⟩ := shellRest_phaseFisher.2.1
    exact ⟨θ, h⟩
  · obtain ⟨θ, _, h⟩ := shellRest_phaseFisher.2.2
    exact ⟨θ, h⟩
  · obtain ⟨t, _, _, h⟩ := shellLab_phaseFisher.2.2.1
    exact ⟨t, h⟩
  · intro θ
    exact (shellOrth_phaseFisher θ).1

/-- Regression: chart Fisher information is the phase Fisher information times the squared
momentum split. Mean rest reads `0` on the time axis and `34816/625` on axis `1`. The time-axis
pair reads `324/841` at time `0`. The opposite seed reads `64` on axis `1`. Equal weights on one
momentum have phase information `1` and chart Fisher information `0`. -/
example (θ : ℝ) :
    (∃ η : ℝ,
        chartFisher 1 1 shellParticleP shellParticleQ (shellRestQ - shellRestP) 0 η = 0 ∧
          chartFisher 1 1 shellParticleP shellParticleQ (shellRestQ - shellRestP) 1 η =
            34816 / 625) ∧
      chartFisher 1 1 shellParticleP shellLabSpinor (restMomentum 3 - shellRestP) 0
          (wavePhase (restMomentum 3 - shellRestP) (timeShift 0)) = 324 / 841 ∧
        chartFisher 1 1 shellParticleP shellOrthQ (shellRestQ - shellRestP) 1 θ = 64 ∧
          phaseInformation 1 1 = 1 ∧
            chartFisher 1 1 (EuclideanSpace.single 0 1) (EuclideanSpace.single 0 1)
                (0 - 0) 1 0 = 0 := by
  obtain ⟨η, _, _, h0, h1⟩ := shellRest_chartFisher.1
  have hsame :=
    sameMomentum_chartFisher (r := 1) (hr := by norm_num)
      (u := EuclideanSpace.single (0 : Fin 4) (1 : ℂ)) (p := 0) (μ := 1) (θ := 0)
  refine ⟨⟨η, h0, h1⟩, shellLab_chartFisher.2.1, (shellOrth_chartFisher θ).2, hsame.1, hsame.2⟩

/-- Regression: the displacement score is orthogonal to the state, and its squared length is the
chart Fisher information times the Born density. The position operator multiplies by the
coordinate. Mean rest at the origin reads position `0` and score length squared `139264/225`.
At time `1` the score is `0` and the position reads `1`. Rest against `(5, 4, 0, 0)` at time
`-π/2` reads position `-π/2` and score length squared `144/5`. The opposite seed at the origin
reads position `0` and score length squared `6400/9`. One momentum has score `0` and position
`1`. -/
example :
    (∃ θ : ℝ,
        positionOp 1 (shellPacket 1 1 θ shellRestP shellRestQ shellParticleP shellParticleQ) 0 =
          0 ∧
          ‖packetScore 1 1 θ shellRestP shellRestQ shellParticleP shellParticleQ 1 0‖ ^ 2 =
            139264 / 225) ∧
      (let Ψ := shellPacket 1 1 0 shellRestP shellRestQ shellParticleP shellParticleQ
        let x := timeShift (1 : ℝ)
        packetScore 1 1 0 shellRestP shellRestQ shellParticleP shellParticleQ 0 x = 0 ∧
          (inner ℂ (Ψ x) (positionOp 0 Ψ x)).re / ‖Ψ x‖ ^ 2 = 1) ∧
      (let Ψ := shellPacket 1 1 0 shellRestP (restMomentum 3) shellParticleP shellLabSpinor
        let x := timeShift (-Real.pi / 2)
        (inner ℂ (Ψ x) (positionOp 0 Ψ x)).re / ‖Ψ x‖ ^ 2 = -Real.pi / 2 ∧
          ‖packetScore 1 1 0 shellRestP (restMomentum 3) shellParticleP shellLabSpinor 0 x‖ ^ 2 =
            144 / 5) ∧
        (positionOp 1 (shellPacket 1 1 0 shellRestP shellRestQ shellParticleP shellOrthQ) 0 = 0 ∧
          ‖packetScore 1 1 0 shellRestP shellRestQ shellParticleP shellOrthQ 1 0‖ ^ 2 =
            6400 / 9) ∧
          (let u : DiracSpinor := EuclideanSpace.single 0 1
            let x : Vec4 := Pi.single 1 1
            let Ψ := shellPacket 1 1 0 (0 : Vec4) 0 u u
            packetScore 1 1 0 (0 : Vec4) 0 u u 1 x = 0 ∧
              (inner ℂ (Ψ x) (positionOp 1 Ψ x)).re / ‖Ψ x‖ ^ 2 = 1) := by
  obtain ⟨θ, _, _, hpos, hscore, _⟩ := shellRest_origin_score
  refine ⟨⟨θ, hpos, hscore⟩, ?_, ?_, ?_, ?_⟩
  · have htime := shellRest_time_score (0 : ℝ)
    exact ⟨htime.2.2.1, htime.2.2.2⟩
  · exact ⟨shellLab_score.1, shellLab_score.2.1⟩
  · exact ⟨shellOrth_origin_score.2.1, shellOrth_origin_score.2.2.1⟩
  · have hsame := sameMomentum_score
    exact ⟨hsame.2.2.1, hsame.2.2.2⟩

/-- Regression: on a shell packet the part of `momentumOp` orthogonal to the sample is `-i/2`
times the displacement score. Mean rest, quadrature, origin, axis `1`: real part `0`, imaginary
part squared `(36/25)²`, horizontal length squared `34816/225`. The time axis is the eigen-sample
`5 • Ψ`. Rest against `(5, 4, 0, 0)` at time `-π/2` has quotient `28/5`, horizontal length
squared `36/5`, and position `-π/2`. The opposite seed has quotient `0`, a nonzero momentum
operator, horizontal length squared `1600/9`, and position `0`. The zero-momentum packet has
`momentumOp = 0` and position `1`. -/
example :
    (∃ θ : ℝ,
        let Ψ := shellPacket 1 1 θ shellRestP shellRestQ shellParticleP shellParticleQ;
        (momentumQuotient 1 Ψ 0).re = 0 ∧
          (momentumQuotient 1 Ψ 0).im ^ 2 = (36 / 25) ^ 2 ∧
            ‖momentumHorizontal 1 Ψ 0‖ ^ 2 = 34816 / 225) ∧
      (let Ψ := shellPacket 1 1 0 shellRestP shellRestQ shellParticleP shellParticleQ;
        momentumOp 0 Ψ 0 = (5 : ℂ) • Ψ 0 ∧ momentumHorizontal 0 Ψ 0 = 0) ∧
      (let Ψ := shellPacket 1 1 0 shellRestP (restMomentum 3) shellParticleP shellLabSpinor;
        let x := timeShift (-Real.pi / 2);
        momentumQuotient 0 Ψ x = (28 / 5 : ℂ) ∧
          ‖momentumHorizontal 0 Ψ x‖ ^ 2 = 36 / 5 ∧
            (inner ℂ (Ψ x) (positionOp 0 Ψ x)).re / ‖Ψ x‖ ^ 2 = -Real.pi / 2) ∧
        (let Ψ := shellPacket 1 1 0 shellRestP shellRestQ shellParticleP shellOrthQ;
          momentumQuotient 1 Ψ 0 = 0 ∧
            momentumOp 1 Ψ 0 ≠ 0 ∧
              ‖momentumHorizontal 1 Ψ 0‖ ^ 2 = 1600 / 9 ∧
                positionOp 1 Ψ 0 = 0) ∧
          (let u : DiracSpinor := EuclideanSpace.single 0 1;
            let x : Vec4 := Pi.single 1 1;
            let Ψ := shellPacket 1 1 0 (0 : Vec4) 0 u u;
            momentumOp 1 Ψ x = 0 ∧
              (inner ℂ (Ψ x) (positionOp 1 Ψ x)).re / ‖Ψ x‖ ^ 2 = 1) := by
  obtain ⟨θ, hrest⟩ := shellRest_quadrature_momentum
  refine ⟨⟨θ, hrest⟩, ?_, ?_, ?_, ?_⟩
  · exact shellRest_time_eigen (0 : ℝ) 0
  · exact ⟨shellLab_momentum.1, shellLab_momentum.2.1, shellLab_momentum.2.2⟩
  · exact ⟨shellOrth_momentum.1, shellOrth_momentum.2.1, shellOrth_momentum.2.2.1,
      shellOrth_momentum.2.2.2⟩
  · exact ⟨zeroMomentum_packet.1, zeroMomentum_packet.2⟩

/-- Regression: the Fisher information of translations is the outer product of the relative
momentum. Mean rest at quadrature reads `0` on the time axis and `34816/625` on axis `1`. The
precision floor there is `625/34816`, and the position reading is `0`. The boost with
`cosh = 5/3` and `sinh = -4/3` keeps the contraction `34816/625` and puts `557056/5625` on the
time slot. Rest against `(5, 4, 0, 0)` at time `-π/2` has time floor `25/324`, not the coordinate
`-π/2`. -/
example :
    (∃ θ : ℝ,
        let Ψ := shellPacket 1 1 θ shellRestP shellRestQ shellParticleP shellParticleQ
        translationFisher 0 0 Ψ 0 = 0 ∧
          translationFisher 1 1 Ψ 0 = 34816 / 625 ∧
            precisionFloor Ψ 0 (Pi.single 1 1) = 625 / 34816 ∧
              (inner ℂ (Ψ 0) (positionOp 1 Ψ 0)).re / ‖Ψ 0‖ ^ 2 = 0) ∧
      fisherContraction ((544 : ℝ) / 625) (shellRestQ - shellRestP) = 34816 / 625 ∧
        fisherContraction ((544 : ℝ) / 625)
            (boost01 (5 / 3) (-4 / 3) (shellRestQ - shellRestP)) = 34816 / 625 ∧
          ((544 : ℝ) / 625) * ((32 : ℝ) / 3) * ((32 : ℝ) / 3) = 557056 / 5625 ∧
            (let Ψ := shellPacket 1 1 0 shellRestP (restMomentum 3) shellParticleP shellLabSpinor
              let x := timeShift (-Real.pi / 2)
              precisionFloor Ψ x (Pi.single 0 1) = 25 / 324 ∧
                (inner ℂ (Ψ x) (positionOp 0 Ψ x)).re / ‖Ψ x‖ ^ 2 = -Real.pi / 2) := by
  obtain ⟨θ, _, h0, h1, _, hfloor, hpos⟩ := shellRest_translationFisher
  have hboost := shellRest_boost_fisher
  refine ⟨⟨θ, h0, h1, hfloor, hpos⟩, hboost.2.2.2.2.2.1, hboost.2.2.2.2.2.2.1, ?_, ?_⟩
  · exact hboost.2.2.2.2.2.2.2.1
  · exact ⟨shellLab_translationFisher.2.2.2.1, shellLab_translationFisher.2.2.2.2.1⟩

/-- Regression: the chart Born density is the time component of the current, and the Dirac scalar
is smaller by `p₀/m` off rest. The fixed-seed mass-3 carriers have chart density `50/9` and
scalar `10/3`. Rest has both equal to `2`. The rotor image of that rest spinor at `(5, 4, 0, 0)`
has chart density `10/3`, not `50/9`, and is not a complex multiple of the fixed seed. Invariant
weight information stays `1` in the mean rest frame and is `15/16` against rest, not the chart
value `225/289`. -/
example :
    invariantDensity shellLabSpinor = 2 ∧
      ‖shellLabSpinor‖ ^ 2 = 2 ∧
        invariantDensity shellParticleP = 10 / 3 ∧
          ‖shellParticleP‖ ^ 2 / invariantDensity shellParticleP = 5 / 3 ∧
            (∃ Ψ : DiracSpinor,
              DiracMomentum 3 shellRestP Ψ ∧
                ‖Ψ‖ ^ 2 = 10 / 3 ∧
                  invariantDensity Ψ = 2 ∧
                    ‖shellParticleP‖ ^ 2 ≠ ‖Ψ‖ ^ 2 ∧
                      ¬ ∃ c : ℂ, shellParticleP = c • Ψ) ∧
              phaseInformation (Real.sqrt (invariantDensity shellParticleP))
                  (Real.sqrt (invariantDensity shellParticleQ)) = 1 ∧
                phaseInformation (Real.sqrt (invariantDensity shellParticleP))
                    (Real.sqrt (invariantDensity shellLabSpinor)) = 15 / 16 ∧
                  phaseInformation ‖shellParticleP‖ ‖shellLabSpinor‖ = 225 / 289 ∧
                    (15 / 16 : ℝ) ≠ 225 / 289 := by
  obtain ⟨Ψ, hdir, hn, hinv, -, hne, hray⟩ := shellRest_rotorImage
  exact ⟨shellLab_densities.1, shellLab_densities.2, shellParticle_densities.1,
    shellParticle_densities.2.2.1, ⟨Ψ, hdir, hn, hinv, hne, hray⟩, shellRest_invariantPhase.2,
    shellLab_invariantPhase.2.1, shellLab_invariantPhase.1, shellLab_invariantPhase.2.2.1⟩

example (a b : Fin 3 → ℝ) :
    Matrix.trace (pauliComb a * pauliComb b - pauliComb b * pauliComb a) = 0 :=
  trace_pauliComb_comm a b

example {Ψ : Vec4 → DiracSpinor} (hΨ : Differentiable ℝ Ψ) (ν μ : Fin 4) (x : Vec4) :
    positionOp ν (momentumOp μ Ψ) x - momentumOp μ (positionOp ν Ψ) x =
      (if ν = μ then Complex.I else 0) • Ψ x :=
  position_comm_momentum hΨ ν μ x

example (p : Vec4) (u : DiracSpinor) (μ : Fin 4) (x : Vec4) :
    Complex.exp (-(Complex.I * (wavePhase p x : ℂ))) • momentumOp μ (planeWave p u) x =
      (p μ : ℂ) • u :=
  momentumOp_planeWave_strip p u μ x

example {p : Vec4} {Ψ : Vec4 → DiracSpinor} (hΨ : Differentiable ℝ Ψ) :
    MomentumEigen p Ψ ↔ ∀ μ x, momentumOp μ Ψ x = (p μ : ℂ) • Ψ x :=
  momentumEigen_iff_momentumOp hΨ

example {u : DiracSpinor} (hu : u ≠ 0) (p : Vec4) (ν : Fin 4) (lam : ℂ) :
    ¬ PositionEigen ν lam (planeWave p u) :=
  planeWave_not_positionEigen hu p ν lam

example {Ψ : Vec4 → DiracSpinor} (hΨ : ContDiff ℝ 2 Ψ) (hΨ1 : Differentiable ℝ Ψ)
    (ν μ : Fin 4) (x a : Vec4) (p : Vec4) (lam : ℂ)
    (hP : MomentumEigen p Ψ) (hX : PositionEigen ν lam Ψ)
    (M : Matrix (Fin 2) (Fin 2) ℂ) :
    positionOp ν (positionOp μ Ψ) x = positionOp μ (positionOp ν Ψ) x ∧
      momentumOp μ (momentumOp ν Ψ) x = momentumOp ν (momentumOp μ Ψ) x ∧
      deriv (fun t : ℝ => Ψ (x + t • a)) 0 =
        Complex.I • ∑ κ : Fin 4, (a κ : ℂ) • momentumOp κ Ψ x ∧
      momentumOp μ (fiberRotor M Ψ) x = fiberRotor M (momentumOp μ Ψ) x ∧
      orbitalZ (positionOp 1 Ψ) x - positionOp 1 (orbitalZ Ψ) x =
        Complex.I • positionOp 2 Ψ x ∧
      Ψ x = 0 :=
  ⟨position_comm ν μ Ψ x, momentum_comm hΨ μ ν x,
    translate_deriv_momentum (hΨ1 x) a, fiberRotor_momentum M hΨ1 μ x,
    orbitalZ_comm_position_x hΨ1 x, joint_position_momentum_zero hP hX x⟩

/-- Regression: light-cone 8+8 ≠ DST torsion 6; Super-Poincaré ≠ PGA 10. -/
example : 8 + 8 ≠ 6 ∧ StringSpectrum.superPoincareN1Dim ≠ LorentzDim.pgaGeneratorCount :=
  ⟨LorentzDim.lightCone_ne_torsionGenerators, superPoincare_ne_pga⟩

example : LorentzDim.quaternionTensorDim = 16 ∧
    LorentzDim.quaternionDirectSumDim ≠ LorentzDim.quaternionTensorDim :=
  ⟨LorentzDim.quaternionTensorDim_eq, LorentzDim.quaternionDirectSum_ne_tensor⟩

/-- Regression: balanced ray is level-matched (`J = 0`). -/
example : IsLevelMatched (Invariant.balancedRay 1) :=
  isLevelMatched_balancedRay 1

/-- Regression: discrete rotor image is finite (not a generation count). -/
example {N : ℕ} [NeZero N] : (UnitGroup.DiscreteRotorImage N).Finite :=
  discreteRotorImage_finite_not_generations

end Logic

end DoubleSpacetime
