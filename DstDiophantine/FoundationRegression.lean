import DstDiophantine.Framework.Amplification
import DstDiophantine.Framework.Representation
import DstDiophantine.Framework.Lattice
import DstDiophantine.Embedding.Height
import DstDiophantine.Embedding.RotorClass
import DstDiophantine.Algebra.Amplification
import DstDiophantine.Algebra.ModularAmplification
import DstDiophantine.Algebra.Invariant
import DstDiophantine.Algebra.Discrete
import DstDiophantine.Theorems.Fermat
import DstDiophantine.Theorems.Beal
import DstDiophantine.Theorems.Abc
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
-- CGA probe is intentionally not imported here (same policy as Gravity).

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

/-- Real-scale continuous admissibility forces zero total winding. -/
example {N k : ℕ} [NeZero N] (t : DiscreteTorsion N)
    (hadm : IsAdmissibleContinuous (scaleTorsion (k : ℝ) (toTorsionParams t))) :
    windingTotal k t = 0 :=
  admissible_scale_implies_windingTotal_eq_zero k t hadm

/-- Modular witness with winding is not real-scale admissible. -/
example {N k : ℕ} [NeZero N] (w : ModularAmplificationWitness N k) :
    ¬ IsAdmissibleContinuous (scaleTorsion (k : ℝ) (toTorsionParams w.t.val)) :=
  ModularAmplificationWitness.not_admissible_real_scale w

/-- `|n|=1` quantises to the zero seed. -/
example {N : ℕ} [NeZero N] (n : ℤ) (hn : n ≠ 0) (habs : Int.natAbs n = 1) :
    quantizeInt N n hn = zeroTorsion N :=
  quantizeInt_one n hn habs

/-- Modular bridge recovers classical FLT conditionally (solution-dependent payload). -/
example (hbridge : FermatModularBridge) :
    ∀ (a b c : ℤ) (p : ℕ), 3 ≤ p → a ≠ 0 → b ≠ 0 → c ≠ 0 →
      ¬ (a ^ p + b ^ p = c ^ p) :=
  fermat_last_theorem_of_modular_bridge hbridge

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

/-- Modular Beal bridge recovers classical Beal conditionally. -/
example (hbridge : BealModularBridge) :
    ∀ (A B C : ℤ) (x y z : ℕ),
      3 ≤ x → 3 ≤ y → 3 ≤ z →
      A ≠ 0 → B ≠ 0 → C ≠ 0 →
      A ^ x + B ^ y = C ^ z →
      1 < bealGcd A B C :=
  beal_conjecture_of_modular_bridge hbridge

/-- Equal-exponent Beal fractional gap degenerates to Fermat log-mismatch. -/
example (A C : ℤ) (p : ℕ) (hp : p ≠ 0) :
    bealFracLogGap A C p p p =
      Real.log (Int.natAbs C) - Real.log (Int.natAbs A) :=
  bealFracLogGap_eq_exp A C p hp

/-- Continuous abc quality bridge is false (diagnostic obstruction). -/
example : ¬ AbcAdmissibleBridge :=
  AbcAdmissibleBridge_false

/-- Modular abc bridge recovers classical abc conditionally. -/
example (hbridge : AbcModularBridge) :
    ∀ (ε : ℝ), 0 < ε →
      ∃ C : ℝ, 0 < C ∧
        ∀ (a b c : ℕ), IsAbcTriple a b c →
          (c : ℝ) ≤ C * (abcRadical (a * b * c) : ℝ) ^ (1 + ε) :=
  abc_conjecture_of_modular_bridge hbridge

/-- Pure-boost modular winding criterion. -/
example {N k : ℕ} [NeZero N] (t : DiscreteTorsion N) (hp : IsPureBoostSeed t) :
    windingTotal k t ≠ 0 ↔ N ≤ k * (t.n 0).val :=
  windingTotal_pureBoost_ne_zero_iff k t hp

/-- Pairwise-coprime abc triples multiply radicals. -/
example {a b c : ℕ} (h : IsAbcTriple a b c) :
    abcRadical (a * b * c) = abcRadical a * abcRadical b * abcRadical c :=
  isAbcTriple_radical_mul h

end DstDiophantine.FoundationRegression
