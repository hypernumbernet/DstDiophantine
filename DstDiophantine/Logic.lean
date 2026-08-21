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
import DstDiophantine.Logic.DiscreteAmplitude
import DstDiophantine.Logic.Dynamics
import DstDiophantine.Logic.Winding
import DstDiophantine.Logic.Quantum.Separation
import DstDiophantine.Logic.Quantum.DualSector
import DstDiophantine.Logic.Quantum.Quaternion
import DstDiophantine.Logic.Quantum.Spinor
import DstDiophantine.Logic.Quantum.QuantumLogic
import DstDiophantine.Logic.Quantum.Dictionary
import DstDiophantine.Algebra.Invariant

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
  `ℂ²`, subspace lattice, internal dictionary)
* `Logic.Formula` / `Valuation` / `Consequence` — syntax, designated
  `HoldsT` / `HoldsNotF`, two-valued fragments, entailment
* `Logic.Regime` — discrete proof-status algebra and implication table
* `Logic.Example` — fixed-point, non-explosion, `Jnorm < 1`,
  Diophantine regimes (complementarity is the existing `ℂ²` lattice theorems)
* `Logic.DiscreteAmplitude` — torus amplitudes; `¬4 ∣ N` forbids `F`
* `Logic.Dynamics` — amplification as a partial map on labels;
  vacuum is a fixed point; balanced massive can stay `T` or leave the cone
  invisibly to `classify?`
* `Logic.Winding` — height and winding are incompatible measurements

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

/-- Regression: real-scale admissibility and nonzero winding are incompatible. -/
example {N : ℕ} [NeZero N] (k : ℕ) (t : Discrete.DiscreteTorsion N) :
    ¬ (Admissible.IsAdmissibleContinuous
          (Amplification.scaleTorsion (k : ℝ) (Discrete.toTorsionParams t)) ∧
        ModularAmplification.windingTotal k t ≠ 0) :=
  not_both_admissibleScale_and_winding k t

end Logic

end DstDiophantine
