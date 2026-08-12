import DstDiophantine.Framework.Amplification
import DstDiophantine.Framework.Representation
import DstDiophantine.Framework.Lattice
import DstDiophantine.Embedding.Height
import DstDiophantine.Algebra.Amplification
import DstDiophantine.Algebra.ModularAmplification
import DstDiophantine.Algebra.Invariant
import DstDiophantine.Algebra.Discrete
import DstDiophantine.Theorems.Fermat
import DstDiophantine.Theorems.Beal
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Public-API / layering regression examples

These examples guard against export and dependency regressions in the shared
amplification core. They import Framework / Algebra / Theorems directly (not
`DstDiophantine.Basic`) to avoid a module cycle.
-/

namespace DstDiophantine.FoundationRegression

open Amplification Discrete Invariant Framework Theorems ModularAmplification
open _root_.DstDiophantine.Embedding

/-- Additive faithfulness. -/
example (a b c : ℤ) (p : ℕ) :
    a ^ p + b ^ p = c ^ p ↔ powerSumMotor (fermatEquation a b c p) = 1 :=
  fermat_solution_iff_motor a b c p

/-- Continuous seed upper bound from `Framework.Amplification`. -/
example (θ : ℝ) {k : ℕ} (hk : 1 ≤ k)
    (hadm : IsAdmissibleContinuous (pureBoost (k * θ))) :
    |JNormalized (pureBoost θ)| ≤ 1 / (k : ℝ) ^ 2 :=
  amplification_implies_seed_le θ hk hadm

/-- Discrete nonzero height lower bound. -/
example {N : ℕ} [NeZero N] (t : DiscreteTorsion N) (hne : latticeMismatch t ≠ 0) :
    (16 : ℝ) / (3 * N ^ 2) ≤ |JNormalized (toTorsionParams t)| :=
  discrete_nonzero_height_lb t hne

/-- Coarse discrete no-go. -/
example {N k : ℕ} [NeZero N] (hk : 1 ≤ k)
    (hcoarse : 3 * N ^ 2 < 16 * k ^ 2) (t : AdmissibleClass N)
    (hne : latticeMismatch t.val ≠ 0)
    (hadm :
      IsAdmissibleContinuous
        (scaleTorsion (k : ℝ) (AdmissibleClass.toParams t))) :
    False :=
  coarse_discrete_contradiction hk hcoarse t hne hadm

/-- Pure-boost closed forms on the algebra surface. -/
example (θ : ℝ) :
    JNormalized (pureBoost θ) = (4 / (3 * Real.pi ^ 2)) * θ ^ 2 :=
  JNormalized_pureBoost θ

example (θ : ℝ) :
    IsAdmissibleContinuous (pureBoost θ) ↔ 0 ≤ θ ∧ θ ≤ Real.pi / 2 :=
  isAdmissibleContinuous_pureBoost_iff θ

/-- Coarse bridge recovers classical FLT conditionally (vacuous payload). -/
example (hbridge : FermatCoarseDiscreteBridge) :
    ∀ (a b c : ℤ) (p : ℕ), 3 ≤ p → a ≠ 0 → b ≠ 0 → c ≠ 0 →
      ¬ (a ^ p + b ^ p = c ^ p) :=
  fermat_last_theorem_of_coarse_discrete_bridge hbridge

/-- Shared witness no-go is available without a problem-specific bridge. -/
example {N k : ℕ} [NeZero N] (hk : 1 ≤ k)
    (hcoarse : 3 * N ^ 2 < 16 * k ^ 2)
    (w : CoarseAmplificationWitness N k) : False :=
  w.false hk hcoarse

/-- Legacy coarse witness is equation-independently empty under coarseness. -/
example {N k : ℕ} [NeZero N] (hk : 1 ≤ k)
    (hcoarse : 3 * N ^ 2 < 16 * k ^ 2)
    (w : CoarseAmplificationWitness N k) : False :=
  CoarseAmplificationWitness.empty_of_coarse hk hcoarse w

/-- Coarseness implies `N < 4k` (feeds the direct emptiness argument). -/
example {N k : ℕ} (hcoarse : 3 * N ^ 2 < 16 * k ^ 2) : N < 4 * k :=
  coarse_implies_lt_four_mul hcoarse

/-- Modular amplification witness is inhabited (non-vacuous replacement). -/
example : Nonempty (ModularAmplificationWitness 16 5) :=
  ModularAmplificationWitness.nonempty_example

/-- Winding identity on a single coordinate. -/
example {N : ℕ} [NeZero N] (k : ℕ) (x : ZMod N) :
    k * x.val = (k • x).val + N * windingCoord k x :=
  mul_val_eq_val_add_winding k x

/-- Balanced continuous obstruction (phase-6 diagnostic). -/
example {p : ℕ} (hp : 1 ≤ p) :
    |JNormalized (pureBoost (Real.log 2 / (p : ℝ)))| < (1 : ℝ) / (p : ℝ) ^ 2 :=
  fermat_balanced_seed_lt_threshold hp

/-- Beal discrete contradiction does not require Fermat as a library. -/
example {N : ℕ} [NeZero N] {x y z : ℕ}
    (hx : 3 ≤ x) (hy : 3 ≤ y) (hz : 3 ≤ z)
    (t : AdmissibleClass N)
    (hlb :
      (1 : ℝ) / (bealMinExp x y z : ℝ) ^ 2 <
        torsionHeight (AdmissibleClass.toParams t))
    (hadm :
      IsAdmissibleContinuous
        (scaleTorsion (bealMinExp x y z : ℝ) (AdmissibleClass.toParams t))) :
    False :=
  beal_discrete_amplification_contradiction hx hy hz t hlb hadm

end DstDiophantine.FoundationRegression
