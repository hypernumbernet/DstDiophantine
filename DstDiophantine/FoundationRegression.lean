import DstDiophantine.Framework.Amplification
import DstDiophantine.Framework.Representation
import DstDiophantine.Framework.Lattice
import DstDiophantine.Embedding.Height
import DstDiophantine.Embedding.RotorClass
import DstDiophantine.Algebra.Amplification
import DstDiophantine.Algebra.ModularAmplification
import DstDiophantine.Algebra.Invariant
import DstDiophantine.Algebra.Discrete
import DstDiophantine.Algebra.Operations
import DstDiophantine.Algebra.Continuum
import DstDiophantine.Algebra.UnitGroup
import DstDiophantine.Algebra.Generators
import DstDiophantine.Theorems.Fermat
import DstDiophantine.Theorems.Beal
import DstDiophantine.Theorems.Abc
import DstDiophantine.Embedding.ConformalInteger
import DstDiophantine.Algebra.CGA.NullCone
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Public-API / layering regression examples

These examples guard against export and dependency regressions in the shared
amplification core. They import Framework / Algebra / Theorems directly (not
`DstDiophantine.Basic`) to avoid a module cycle.

Beal critical-path regressions (payload incompatibility, winding threshold,
CGA null gauge) are included; Gravity remains intentionally out of scope.

DST / discrete-companion algebraic core regressions (dual map, Killing
dictionary, admissible bound, finite rotor image, continuum `J` approximation)
are included below.
-/

namespace DstDiophantine.FoundationRegression

open Amplification Discrete Invariant Framework Theorems ModularAmplification
open Operations Continuum UnitGroup Generators
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

/-- Diagnostic modular Beal bridge recovers classical Beal conditionally. -/
example (hbridge : BealModularBridge) :
    ∀ (A B C : ℤ) (x y z : ℕ),
      3 ≤ x → 3 ≤ y → 3 ≤ z →
      A ≠ 0 → B ≠ 0 → C ≠ 0 →
      A ^ x + B ^ y = C ^ z →
      1 < bealGcd A B C :=
  beal_conjecture_of_modular_bridge hbridge

/-- Winding witness and PGA-identified conformal gauge are incompatible. -/
example {N k : ℕ} [NeZero N] (w : ModularAmplificationWitness N k) :
    ¬ ConformalGaugeAdmissible
        (scaleTorsion (k : ℝ) (toTorsionParams w.t.val)) :=
  beal_modular_payload_incompatible w

/-- At `m = 3` the winding threshold sits above the continuous seed cone. -/
example {x y z : ℕ} (hm : bealMinExp x y z = 3) :
    Real.pi / 2 < 2 * Real.pi / (bealMinExp x y z : ℝ) :=
  beal_winding_threshold_gt_half_pi_of_minExp_eq_three hm

/-- Balanced fractional gap misses the modular winding threshold. -/
example {m : ℕ} (hm : 0 < m) :
    Real.log 2 / (m : ℝ) < 2 * Real.pi / (m : ℝ) :=
  beal_balanced_fracGap_lt_winding_threshold hm

/-- Split winding + CGA no-go bridges recover classical Beal conditionally. -/
example (hwind : BealWindingBridge) (hnogo : BealCGANoGo) :
    ∀ (A B C : ℤ) (x y z : ℕ),
      3 ≤ x → 3 ≤ y → 3 ≤ z →
      A ≠ 0 → B ≠ 0 → C ≠ 0 →
      A ^ x + B ^ y = C ^ z →
      1 < bealGcd A B C :=
  beal_conjecture_of_winding_and_cga_nogo hwind hnogo

/-- CGA Beal gauge is null on both fractional-power seeds (not PGA real-scale). -/
example (A C : ℤ) (x z m : ℕ) : BealCGAGauge A C x z m :=
  BealCGAGauge_of_ne_zero A C x z m

/-- Amplification factor below 4 never yields a modular winding witness. -/
example {N : ℕ} [NeZero N] : IsEmpty (ModularAmplificationWitness N 3) :=
  modularWitness_empty_of_eq_three

/-- At `m = 3` the lifted amplification factor is 4. -/
example {x y z : ℕ} (hm : bealMinExp x y z = 3) : bealAmpExp x y z = 4 :=
  bealAmpExp_eq_four_of_minExp_eq_three hm

/-- Wide window constructs a modular winding witness (includes `m = 3` via `k = 4`). -/
example (A C : ℤ) (x z m k : ℕ) (hk4 : 4 ≤ k)
    (hle : 2 * Real.pi / k ≤ bealFracLogGap A C x z m)
    (hlt : bealFracLogGap A C x z m < 4 * Real.pi / k) :
    let N := k
    ∃ (hN : N ≠ 0),
      letI : NeZero N := ⟨hN⟩
      let t := quantizeBealMismatch N A C x z m
      IsAdmissible t ∧ ∃ w : ModularAmplificationWitness N k, w.t.val = t :=
  beal_modularWitness_of_fracGap_window A C x z m k hk4 hle hlt

/-- Torus fold: principal gap in the wide window still yields a witness. -/
example (A C : ℤ) (x z m k : ℕ) (hk4 : 4 ≤ k)
    (hδ0 : 0 ≤ bealFracLogGap A C x z m)
    (hle : 2 * Real.pi / k ≤ principalRapidity (bealFracLogGap A C x z m))
    (hlt : principalRapidity (bealFracLogGap A C x z m) < 4 * Real.pi / k) :
    let N := k
    ∃ (hN : N ≠ 0),
      letI : NeZero N := ⟨hN⟩
      let t := quantizeBealMismatch N A C x z m
      IsAdmissible t ∧ ∃ w : ModularAmplificationWitness N k, w.t.val = t :=
  beal_modularWitness_of_principal_fracGap_window A C x z m k hk4 hδ0 hle hlt

/-- CGA dilation is not `2π`-periodic (contrast with PGA rapidity torus). -/
example {a : ℝ} (ha : 0 < a) (δ : ℝ) :
    CGA.CGA1.pointVec (Real.exp (δ + 2 * Real.pi) * a) ≠
      CGA.CGA1.pointVec (Real.exp δ * a) :=
  conformalPoint_dilation_not_two_pi_periodic ha δ

/-- Normalised CGA points pair with null infinity to `-1`. -/
example (x : ℝ) : CGA.CGA1.bilin21 (CGA.CGA1.pointVec x) CGA.CGA1.nInfVec = -1 :=
  bilin21_conformalPoint_nInf x

/-- Equal-exponent Beal fractional gap degenerates to Fermat log-mismatch. -/
example (A C : ℤ) (p : ℕ) (hp : p ≠ 0) :
    bealFracLogGap A C p p p =
      Real.log (Int.natAbs C) - Real.log (Int.natAbs A) :=
  bealFracLogGap_eq_exp A C p hp

/-- Fractional log-gap equals log-ratio of CGA root magnitudes. -/
example (A C : ℤ) (x z m : ℕ) (hA : A ≠ 0) (hC : C ≠ 0) :
    bealFracLogGap A C x z m =
      Real.log (bealRootMag C z m) - Real.log (bealRootMag A x m) :=
  bealFracLogGap_eq_log_rootMag A C x z m hA hC

/-- Contrast: PGA integer-rotor height is globally unbounded; CGA points stay null. -/
example (M : ℝ) : ∃ (n : ℤ) (hn : n ≠ 0), M < integerHeight n hn :=
  exists_integerHeight_gt M

example (x : ℝ) : conformalPoint x * conformalPoint x = 0 :=
  conformalPoint_sq x

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

/-! ## DST / discrete-companion algebraic core -/

/-- Pseudoscalar squares to `-1`. -/
example : pseudoscalar * pseudoscalar = (-1 : PGA) :=
  pseudoscalar_sq

/-- Dual preserves Minkowski square (paper §2). -/
example (v : Fin 4 → ℝ) :
    dual (minkowskiVector v) * dual (minkowskiVector v) =
      minkowskiVector v * minkowskiVector v :=
  dual_minkowskiVector_sq v

/-- Paper appendix Killing coefficient `8∑(α²-β²)` is false for `Ω = omegaTorsion`. -/
example :
    ∃ p : TorsionParams,
      omegaTorsionGeneratorKilling p ≠
        8 * ∑ a : Fin 3, (p.alpha a ^ 2 - p.beta a ^ 2) :=
  paper_appendix_killing_coeff_false

/-- Same-axis generators commute; off-axis need not. -/
example (a : Fin 3) : commutator (hyperbolic a) (cyclic a) = 0 :=
  commutator_hyperbolic_cyclic_same a

example : commutator (hyperbolic 0) (cyclic 1) ≠ 0 :=
  commutator_hyperbolic0_cyclic1_ne_zero

/-- Discrete admissibility ↔ continuous admissibility of the embedding. -/
example {N : ℕ} [NeZero N] (t : DiscreteTorsion N) :
    IsAdmissible t ↔ IsAdmissibleContinuous (toTorsionParams t) :=
  isAdmissible_iff_admissibleContinuous t

/-- Admissible bound `|JNormalized| ≤ 1`. -/
example (p : TorsionParams) (h : IsAdmissibleContinuous p) :
    |JNormalized p| ≤ 1 :=
  torsion_bound_continuous p h

/-- Naive principal-branch bound remains false. -/
example : ∃ p : TorsionParams, IsPrincipalBranch p ∧ 1 < |J p| :=
  torsion_bound_naive_false

/-- Discrete rotor image is finite (not an integer-order unit group). -/
example {N : ℕ} [NeZero N] : (DiscreteRotorImage N).Finite :=
  discreteRotorImage_finite

/-- Continuum approximation of `J`. -/
example {p : TorsionParams} (h : IsAdmissibleContinuous p) {ε : ℝ} (hε : 0 < ε) :
    ∃ (N : ℕ) (_ : NeZero N),
      ∃ t : DiscreteTorsion N, IsAdmissible t ∧
        |J p - J (toTorsionParams t)| < ε :=
  exists_discrete_approx_J h hε

end DstDiophantine.FoundationRegression
