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
import DstDiophantine.Algebra.Motor
import DstDiophantine.Algebra.Sandwich
import DstDiophantine.Algebra.PGA
import DstDiophantine.Theorems.Fermat
import DstDiophantine.Theorems.Beal
import DstDiophantine.Theorems.BealSlice
import DstDiophantine.Theorems.BealPythagorean
import DstDiophantine.Theorems.BealGaussian
import DstDiophantine.Theorems.BealMixed
import DstDiophantine.Theorems.BealEven
import DstDiophantine.Theorems.BealGaussianCube
import DstDiophantine.Theorems.BealFinite
import DstDiophantine.Theorems.DarmonMerel
import DstDiophantine.Theorems.FermatLast
import DstDiophantine.Theorems.Abc
import DstDiophantine.Embedding.ConformalInteger
import DstDiophantine.Algebra.CGA.NullCone
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.NumberTheory.Zsqrtd.GaussianInt

/-!
# Public-API / layering regression examples

These examples guard against export and dependency regressions in the shared
amplification core. They import Framework / Algebra / Theorems directly (not
`DstDiophantine.Basic`) to avoid a module cycle.

Beal critical-path regressions (payload incompatibility, winding window,
power-lattice descent, phase 7e bookkeeping realisation / Mihăilescu / DST
config, phase 7f exponent-gcd reduction / FLT hypothesis, phase 7g
unconditional FLT slices / Pythagorean classification, phase 7h Pythagorean
UFD slices / mixed-exponent case splits, phase 7i FLT axiom / Gaussian UFD /
equal-odd and even two-equal progress, diagnostic NoGo) are included;
Gravity remains intentionally out of scope.

DST / discrete-companion algebraic core regressions (dual map, Killing
dictionary, admissible bound, finite rotor image, continuum `J` approximation,
sharp discrete `|JNormalized|` range) are included below.

Algebraic sandwich surface regressions (composition, pure-boost `ι 2`
invariance, light-cone eigenvalues) are included; Gravity remains out of scope.
-/

namespace DstDiophantine.FoundationRegression

open Amplification Discrete Invariant Framework Theorems ModularAmplification Motor
open Operations Continuum UnitGroup Generators Sandwich PGA
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

/-- Split winding + diagnostic CGA no-go recover classical Beal conditionally. -/
example (hwind : BealWindingBridge) (hnogo : BealCGANoGo) :
    ∀ (A B C : ℤ) (x y z : ℕ),
      3 ≤ x → 3 ≤ y → 3 ≤ z →
      A ≠ 0 → B ≠ 0 → C ≠ 0 →
      A ^ x + B ^ y = C ^ z →
      1 < bealGcd A B C :=
  beal_conjecture_of_winding_and_cga_nogo hwind hnogo

/-- Live lattice/dilation no-go + winding recover Beal on lattice solutions. -/
example (hwind : BealWindingBridge) (hnogo : BealCGADilationNoGo) :
    ∀ (A B C : ℤ) (x y z : ℕ),
      3 ≤ x → 3 ≤ y → 3 ≤ z →
      A ≠ 0 → B ≠ 0 → C ≠ 0 →
      BealCGALatticeGauge A B C x y z (bealMinExp x y z) →
      A ^ x + B ^ y = C ^ z →
      1 < bealGcd A B C :=
  beal_conjecture_of_winding_and_cga_dilation_nogo hwind hnogo

/-- Bookkeeping discrete closure + unit-base no-go recover classical Beal. -/
example (hclosed : BealCGADiscreteClosed) (hnogo : BealUnitBaseNoGo) :
    ∀ (A B C : ℤ) (x y z : ℕ),
      3 ≤ x → 3 ≤ y → 3 ≤ z →
      A ≠ 0 → B ≠ 0 → C ≠ 0 →
      A ^ x + B ^ y = C ^ z →
      1 < bealGcd A B C :=
  beal_conjecture_of_discreteClosed_and_unitBaseNoGo hclosed hnogo

/-- Phase 7e: k-fold power lattice ↔ `|A| = 1` for coprime solutions. -/
example {A B C : ℤ} {x y z m k : ℕ}
    (hm : m ≠ 0) (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hk : 2 ≤ k)
    (hgcd : bealGcd A B C = 1)
    (hsol : A ^ x + B ^ y = C ^ z) :
    IsCGAPowerLatticePoint (bealCGAKFoldMag A C x z m k) m ↔ A.natAbs = 1 :=
  beal_kFold_powerLattice_iff_natAbs_eq_one hm hA hB hC hx hy hz hk hgcd hsol

/-- Phase 7e: bookkeeping closure ≡ coprime ⇒ `|A| = 1`. -/
example :
    BealCGADiscreteClosed ↔
      ∀ (A B C : ℤ) (x y z : ℕ),
        3 ≤ x → 3 ≤ y → 3 ≤ z →
        A ≠ 0 → B ≠ 0 → C ≠ 0 →
        bealGcd A B C = 1 →
        A ^ x + B ^ y = C ^ z →
          A.natAbs = 1 :=
  BealCGADiscreteClosed_iff_unitAbs

/-- Phase 7e: positive unit base via Mihăilescu axiom. -/
example {A B C : ℤ} {x y z : ℕ}
    (hx : 3 ≤ x) (hy : 3 ≤ y) (hz : 3 ≤ z)
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (hA1 : A.natAbs = 1) :
    ¬ A ^ x + B ^ y = C ^ z :=
  bealUnitBaseNoGo_pos hx hy hz hA hB hC hA1

/-- Phase 7e: realisation + Mihăilescu recover positive classical Beal (bookkeeping). -/
example (hreal : BealCGARealization) :
    ∀ (A B C : ℤ) (x y z : ℕ),
      3 ≤ x → 3 ≤ y → 3 ≤ z →
      0 < A → 0 < B → 0 < C →
      A ^ x + B ^ y = C ^ z →
      1 < bealGcd A B C :=
  beal_conjecture_pos_of_realization hreal

/-- Phase 7f: equal-exponent integer dilation ↔ `|A| = 1` under AC-coprimality. -/
example (A C : ℤ) (p : ℕ) (hp : p ≠ 0) (hA : A ≠ 0) (hC : C ≠ 0)
    (hac : Nat.Coprime A.natAbs C.natAbs) :
    IsCGAIntegerDilation (bealRootMag C p p / bealRootMag A p p) ↔
      A.natAbs = 1 :=
  beal_eq_exp_integerDilation_iff_natAbs_eq_one A C p hp hA hC hac

/-- Phase 7f: Pythagorean `3²+4²=5²` misses integer A–C dilation. -/
example : ¬ IsCGAIntegerDilation (bealRootMag (5 : ℤ) 2 2 / bealRootMag (3 : ℤ) 2 2) :=
  not_beal_eq_exp_integerDilation_three_four_five

/-- Phase 7f: exponent-gcd reduction to Fermat form. -/
example (A B C : ℤ) (x y z : ℕ) :
    let d := bealExpGcd x y z
    A ^ x + B ^ y = C ^ z ↔
      (A ^ (x / d)) ^ d + (B ^ (y / d)) ^ d = (C ^ (z / d)) ^ d :=
  beal_eq_pow_mul_expGcd A B C x y z

/-- Phase 7f: mathlib FLT forbids Beal solutions with `bealExpGcd ≥ 3`. -/
example (hFLT : FermatLastTheorem) {A B C : ℤ} {x y z : ℕ}
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hd : 3 ≤ bealExpGcd x y z) :
    ¬ A ^ x + B ^ y = C ^ z :=
  not_beal_sol_of_expGcd_ge_three_of_FLT hFLT hA hB hC hd

/-- Phase 7f: modular Fermat bridge yields the gcd≥3 Beal slice. -/
example (hbridge : FermatModularBridge) {A B C : ℤ} {x y z : ℕ}
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hd : 3 ≤ bealExpGcd x y z) :
    ¬ A ^ x + B ^ y = C ^ z :=
  not_beal_sol_of_expGcd_ge_three_of_modular_bridge hbridge hA hB hC hd

/-- Phase 7g: trichotomy of the exponent gcd. -/
example {x y z : ℕ} (hx : 3 ≤ x) :
    bealExpGcd x y z = 1 ∨ bealExpGcd x y z = 2 ∨ 3 ≤ bealExpGcd x y z :=
  bealExpGcd_eq_one_or_eq_two_or_ge_three hx

/-- Phase 7g: unconditional — `3 ∣ d` or `4 ∣ d` forbids nonzero solutions. -/
example {A B C : ℤ} {x y z : ℕ}
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hdvd : 3 ∣ bealExpGcd x y z ∨ 4 ∣ bealExpGcd x y z) :
    ¬ A ^ x + B ^ y = C ^ z :=
  not_beal_sol_of_three_or_four_dvd_expGcd hA hB hC hdvd

/-- Phase 7g: unconditional equal-exponent slices p = 3 and p = 4. -/
example {A B C : ℤ} (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0) :
    ¬ A ^ 3 + B ^ 3 = C ^ 3 ∧ ¬ A ^ 4 + B ^ 4 = C ^ 4 :=
  ⟨not_beal_eq_exp_three hA hB hC, not_beal_eq_exp_four hA hB hC⟩

/-- Phase 7g: biquadratic Pythagorean slice via `not_fermat_42`. -/
example {A B C : ℤ} {x y z : ℕ}
    (hx : 3 ≤ x) (hy : 3 ≤ y) (hz : 3 ≤ z)
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hd : bealExpGcd x y z = 2)
    (hx4 : 4 ∣ x) (hy4 : 4 ∣ y) :
    ¬ A ^ x + B ^ y = C ^ z :=
  not_beal_sol_of_expGcd_eq_two_of_four_dvd_xy hx hy hz hA hB hC hd hx4 hy4

/-- Phase 7g: coprime d = 2 solutions admit primitive Pythagorean parameters. -/
example {A B C : ℤ} {x y z : ℕ}
    (hx : 3 ≤ x) (hy : 3 ≤ y) (hz : 3 ≤ z)
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hgcd : bealGcd A B C = 1)
    (hd : bealExpGcd x y z = 2)
    (hsol : A ^ x + B ^ y = C ^ z) :
    ∃ m n : ℤ,
      (A ^ (x / 2) = m ^ 2 - n ^ 2 ∧ B ^ (y / 2) = 2 * m * n ∨
        A ^ (x / 2) = 2 * m * n ∧ B ^ (y / 2) = m ^ 2 - n ^ 2) ∧
        (C ^ (z / 2) = m ^ 2 + n ^ 2 ∨ C ^ (z / 2) = -(m ^ 2 + n ^ 2)) ∧
          Int.gcd m n = 1 ∧
            (m % 2 = 0 ∧ n % 2 = 1 ∨ m % 2 = 1 ∧ n % 2 = 0) :=
  beal_pythagorean_classification_of_expGcd_eq_two hx hy hz hA hB hC hgcd hd hsol

/-- Phase 7g: d = 1 with equal first exponents yields a generalised Fermat form. -/
example {A B C : ℤ} {x y z : ℕ}
    (hx : 3 ≤ x) (hxy : x = y) (hd : bealExpGcd x y z = 1)
    (hsol : A ^ x + B ^ y = C ^ z) :
    Nat.gcd x z = 1 ∧ x ≠ z ∧ A ^ x + B ^ x = C ^ z :=
  beal_eq_two_exp_form_of_expGcd_eq_one hx hxy hd hsol

/-- Phase 7h: d = 2 with `4 ∣ x ∧ 4 ∣ z` is unconditionally closed. -/
example {A B C : ℤ} {x y z : ℕ}
    (hx : 3 ≤ x) (hy : 3 ≤ y) (hz : 3 ≤ z)
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hd : bealExpGcd x y z = 2)
    (hx4 : 4 ∣ x) (hz4 : 4 ∣ z) :
    ¬ A ^ x + B ^ y = C ^ z :=
  not_beal_sol_of_expGcd_eq_two_of_four_dvd_xz hx hy hz hA hB hC hd hx4 hz4

/-- Phase 7h: any two of `{x,y,z}` divisible by 4 forbids a `d = 2` solution. -/
example {A B C : ℤ} {x y z : ℕ}
    (hx : 3 ≤ x) (hy : 3 ≤ y) (hz : 3 ≤ z)
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hd : bealExpGcd x y z = 2)
    (h4 : (4 ∣ x ∧ 4 ∣ y) ∨ (4 ∣ x ∧ 4 ∣ z) ∨ (4 ∣ y ∧ 4 ∣ z)) :
    ¬ A ^ x + B ^ y = C ^ z :=
  not_beal_sol_of_expGcd_eq_two_of_two_four_dvd hx hy hz hA hB hC hd h4

/-- Phase 7h: even-leg UFD — coprime opposite-parity `2mn` a square ⇒ factors squares. -/
example {m n k : ℕ}
    (hcop : Nat.Coprime m n)
    (hpar : (Even m ∧ Odd n) ∨ (Odd m ∧ Even n))
    (heq : 2 * m * n = k ^ 2) :
    (Even m ∧ (∃ u v, n = u ^ 2 ∧ 2 * m = v ^ 2)) ∨
      (Even n ∧ (∃ u v, m = u ^ 2 ∧ 2 * n = v ^ 2)) :=
  exists_sq_of_two_mul_coprime_eq_sq hcop hpar heq

/-- Phase 7h: residual type for `d = 2` outside fourth-divisibility slices. -/
example : Prop := BealPythagoreanResidual

/-- Phase 7h: residual iff at least two reduced exponents are odd. -/
example {x y z : ℕ} (hd : bealExpGcd x y z = 2) :
    (¬ (4 ∣ x ∧ 4 ∣ y) ∧ ¬ (4 ∣ x ∧ 4 ∣ z) ∧ ¬ (4 ∣ y ∧ 4 ∣ z)) ↔
      (Odd (x / 2) ∧ Odd (y / 2)) ∨
        (Odd (x / 2) ∧ Odd (z / 2)) ∨
          (Odd (y / 2) ∧ Odd (z / 2)) :=
  beal_pythagorean_residual_iff_two_odd_reduced hd

/-- Phase 7h: d = 1 with `y = z` yields signature `(x, y, y)`. -/
example {A B C : ℤ} {x y z : ℕ}
    (hy : 3 ≤ y) (hyz : y = z) (hd : bealExpGcd x y z = 1)
    (hsol : A ^ x + B ^ y = C ^ z) :
    Nat.gcd x y = 1 ∧ x ≠ y ∧ A ^ x + B ^ y = C ^ y :=
  beal_eq_two_exp_yz_form_of_expGcd_eq_one hy hyz hd hsol

/-- Phase 7h: d = 1 with `x = z` yields signature `(x, y, x)`. -/
example {A B C : ℤ} {x y z : ℕ}
    (hx : 3 ≤ x) (hxz : x = z) (hd : bealExpGcd x y z = 1)
    (hsol : A ^ x + B ^ y = C ^ z) :
    Nat.gcd x y = 1 ∧ x ≠ y ∧ A ^ x + B ^ y = C ^ x :=
  beal_eq_two_exp_xz_form_of_expGcd_eq_one hx hxz hd hsol

/-- Phase 7h: under d = 1, two exponents agree or all three differ. -/
example {x y z : ℕ} (hd : bealExpGcd x y z = 1) :
    x = y ∨ y = z ∨ x = z ∨ (x ≠ y ∧ y ≠ z ∧ x ≠ z) :=
  beal_expGcd_eq_one_two_equal_or_all_distinct hd

/-- Phase 7i: FLT axiom closes `d ≥ 3` with no extra hypothesis. -/
example {A B C : ℤ} {x y z : ℕ}
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hd : 3 ≤ bealExpGcd x y z)
    (hsol : A ^ x + B ^ y = C ^ z) : False :=
  not_beal_sol_of_expGcd_ge_three hA hB hC hd hsol

/-- Phase 7i: positive classical Beal reduces to the two residuals under FLT. -/
example (hMix : BealMixedExpResidual) (hPyth : BealPythagoreanResidual) :
    ∀ {A B C : ℤ} {x y z : ℕ},
      3 ≤ x → 3 ≤ y → 3 ≤ z →
      0 < A → 0 < B → 0 < C →
      A ^ x + B ^ y = C ^ z →
      1 < bealGcd A B C :=
  beal_conjecture_pos_of_residuals hMix hPyth

/-- Phase 7i: opposite-parity coprime parameters yield a Gaussian associate power. -/
example {m n c : ℤ} {e : ℕ} (he : 0 < e)
    (hcop : Int.gcd m n = 1)
    (hpar : (Even m ∧ Odd n) ∨ (Odd m ∧ Even n))
    (heq : m ^ 2 + n ^ 2 = c ^ e) :
    IsGaussianHypotenusePower m n e :=
  isGaussianHypotenusePower_of_hyp_eq_pow he hcop hpar heq

/-- Phase 7i: equal-odd two-factor residual type. -/
example : Prop := BealEqualOddTwoFactorResidual

/-- Phase 7i: even two-equal `d = 1` progress forces odd `C` and opposite parity. -/
example {A B C : ℤ} {x y z : ℕ}
    (hx : 3 ≤ x) (hz : 3 ≤ z) (hxy : x = y) (hd : bealExpGcd x y z = 1)
    (hxeven : Even x)
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hgcd : bealGcd A B C = 1)
    (hsol : A ^ x + B ^ y = C ^ z) :
    Odd C ∧
      ((Even A ∧ Odd B) ∨ (Odd A ∧ Even B)) ∧
        (A ^ (x / 2)) ^ 2 + (B ^ (x / 2)) ^ 2 = C ^ z :=
  beal_two_equal_xy_even_progress hx hz hxy hd hxeven hA hB hC hgcd hsol

/-- Phase 7j: `d = 1` sub-residuals assemble to `BealMixedExpResidual`. -/
example (hEven : BealTwoEqualEvenResidual) (hOdd : BealTwoEqualOddResidual)
    (hDist : BealAllDistinctExpResidual) : BealMixedExpResidual :=
  beal_mixed_exp_of_subresiduals hEven hOdd hDist

/-- Phase 7j: equal-odd + unequal-odd assemble to `BealPythagoreanResidual`. -/
example (hEq : BealEqualOddTwoFactorResidual)
    (hUneq : BealPythagoreanUnequalOddResidual) : BealPythagoreanResidual :=
  beal_pythagorean_of_subresiduals hEq hUneq

/-- Phase 7j: five fine residuals (+ FLT axiom) imply positive classical Beal. -/
example (hEven : BealTwoEqualEvenResidual) (hOdd : BealTwoEqualOddResidual)
    (hDist : BealAllDistinctExpResidual) (hEq : BealEqualOddTwoFactorResidual)
    (hUneq : BealPythagoreanUnequalOddResidual) :
    ∀ {A B C : ℤ} {x y z : ℕ},
      3 ≤ x → 3 ≤ y → 3 ≤ z →
      0 < A → 0 < B → 0 < C →
      A ^ x + B ^ y = C ^ z →
      1 < bealGcd A B C :=
  beal_conjecture_pos_of_fine_residuals hEven hOdd hDist hEq hUneq

/-- Phase 7j: even two-equal `x = y` lifts to a Gaussian hypotenuse power. -/
example {A B C : ℤ} {x y z : ℕ}
    (hx : 3 ≤ x) (hz : 3 ≤ z) (hxy : x = y) (hd : bealExpGcd x y z = 1)
    (hxeven : Even x)
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hgcd : bealGcd A B C = 1)
    (hsol : A ^ x + B ^ y = C ^ z) :
    IsGaussianHypotenusePower (A ^ (x / 2)) (B ^ (x / 2)) z :=
  (exists_gaussian_hyp_pow_of_two_equal_xy_even hx hz hxy hd hxeven hA hB hC hgcd hsol).2.2.1

/-- Phase 7k: Darmon–Merel cube slice covers all three two-equal positions. -/
example {A B C : ℤ} {x y z : ℕ}
    (hx : 3 ≤ x) (hy : 3 ≤ y) (hz : 3 ≤ z)
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hgcd : bealGcd A B C = 1)
    (hd : bealExpGcd x y z = 1)
    (hpair :
      (x = y ∧ z = 3) ∨
        (y = z ∧ x = 3 ∧ Odd y) ∨
          (x = z ∧ y = 3 ∧ Odd x))
    (hsol : A ^ x + B ^ y = C ^ z) : False :=
  not_beal_two_equal_cube_slice hx hy hz hA hB hC hgcd hd hpair hsol

/-- Phase 7k: even two-equal sum+diff assemble to `BealTwoEqualEvenResidual`. -/
example (hSum : BealTwoEqualEvenSumResidual) (hDiff : BealTwoEqualEvenDiffResidual) :
    BealTwoEqualEvenResidual :=
  beal_two_equal_even_of_sum_diff hSum hDiff

/-- Phase 7k: Gaussian cube expansion. -/
example (a b : ℤ) :
    (⟨a, b⟩ : GaussianInt) ^ 3 =
      ⟨a ^ 3 - 3 * a * b ^ 2, 3 * a ^ 2 * b - b ^ 3⟩ :=
  gaussian_cube_eq a b

/-- Phase 7k: mod-8 forbids `2 * odd = cube`. -/
example {m v : ℕ} (hm : Odd m) : ¬ 2 * m = v ^ 3 :=
  not_two_mul_odd_eq_cube hm

/-- Phase 7k: two-factor `e = 3` with pure-cube abs 1 is impossible. -/
example {m n : ℤ} {c : ℕ}
    (hm0 : m ≠ 0) (hn0 : n ≠ 0)
    (heq : m ^ 2 + n ^ 2 = (c : ℤ) ^ 3)
    (hform :
      (∃ v : ℕ, n.natAbs = 1 ∧ 2 * m.natAbs = v ^ 3) ∨
        (∃ v : ℕ, m.natAbs = 1 ∧ 2 * n.natAbs = v ^ 3)) : False :=
  not_eq_odd_two_factor_of_exp_three_abs_one hm0 hn0 heq hform

/-- Phase 7l: positive-cube residual + e≥5 assemble equal-odd two-factor. -/
example (hCube : BealPosCubeAddTwoCubeResidual)
    (hGe5 : BealEqualOddTwoFactorExpGeFiveResidual) :
    BealEqualOddTwoFactorResidual :=
  BealEqualOddTwoFactorResidual_of_pos_cube_and_ge_five hCube hGe5

/-- Phase 7l: even-difference factorization residual implies Diff residual. -/
example (hFac : BealTwoEqualEvenDiffFactorResidual) :
    BealTwoEqualEvenDiffResidual :=
  BealTwoEqualEvenDiffResidual_of_factor hFac

/-- Phase 7l: sum residual from z=5 and z≥7 splits. -/
example (h5 : BealTwoEqualEvenSumExpFiveResidual)
    (h7 : BealTwoEqualEvenSumExpGeSevenResidual) :
    BealTwoEqualEvenSumResidual :=
  BealTwoEqualEvenSumResidual_of_five_ge_seven h5 h7

/-- Phase 7l: even-power difference factorization. -/
example {C B : ℤ} {y : ℕ} (hyeven : Even y) :
    C ^ y - B ^ y =
      (C ^ (y / 2) - B ^ (y / 2)) * (C ^ (y / 2) + B ^ (y / 2)) :=
  even_pow_sub_eq_mul hyeven

/-- Phase 7j: no coprime Beal solution with bases ≤ 8 and exponents in 3…5. -/
example {A B C x y z : ℕ}
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (hAmax : A ≤ 8) (hBmax : B ≤ 8) (hCmax : C ≤ 8)
    (hx : 3 ≤ x) (hy : 3 ≤ y) (hz : 3 ≤ z)
    (hxE : x ≤ 5) (hyE : y ≤ 5) (hzE : z ≤ 5)
    (hsol : A ^ x + B ^ y = C ^ z)
    (hgcd : Nat.gcd A (Nat.gcd B C) = 1) : False :=
  beal_no_coprime_of_le_eight_five hA hB hC hAmax hBmax hCmax hx hy hz hxE hyE hzE hsol hgcd

/-- Phase 7k: no coprime perfect-power Beal with bases ≤ 12 and exponents 3…6. -/
example {A B C x y z : ℕ}
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (hAmax : A ≤ 12) (hBmax : B ≤ 12)
    (hx : 3 ≤ x) (hy : 3 ≤ y) (hz : 3 ≤ z)
    (hxE : x ≤ 6) (hyE : y ≤ 6) (hzE : z ≤ 6)
    (hsol : A ^ x + B ^ y = C ^ z)
    (hgcd : Nat.gcd A (Nat.gcd B C) = 1) : False :=
  beal_no_coprime_perfect_power_of_le_twelve_six
    hA hB hC hAmax hBmax hx hy hz hxE hyE hzE hsol hgcd

/-- Phase 7l: no coprime perfect-power Beal with bases ≤ 13 and exponents 3…6. -/
example {A B C x y z : ℕ}
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (hAmax : A ≤ 13) (hBmax : B ≤ 13)
    (hx : 3 ≤ x) (hy : 3 ≤ y) (hz : 3 ≤ z)
    (hxE : x ≤ 6) (hyE : y ≤ 6) (hzE : z ≤ 6)
    (hsol : A ^ x + B ^ y = C ^ z)
    (hgcd : Nat.gcd A (Nat.gcd B C) = 1) : False :=
  beal_no_coprime_perfect_power_of_le_thirteen_six
    hA hB hC hAmax hBmax hx hy hz hxE hyE hzE hsol hgcd

/-- Phase 7m: no coprime perfect-power Beal with bases ≤ 14 and exponents 3…6. -/
example {A B C x y z : ℕ}
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (hAmax : A ≤ 14) (hBmax : B ≤ 14)
    (hx : 3 ≤ x) (hy : 3 ≤ y) (hz : 3 ≤ z)
    (hxE : x ≤ 6) (hyE : y ≤ 6) (hzE : z ≤ 6)
    (hsol : A ^ x + B ^ y = C ^ z)
    (hgcd : Nat.gcd A (Nat.gcd B C) = 1) : False :=
  beal_no_coprime_perfect_power_of_le_fourteen_six
    hA hB hC hAmax hBmax hx hy hz hxE hyE hzE hsol hgcd

/-- Phase 7m: Affine residual assembles the positive cube residual. -/
example (hAff : BealAffineCubeAddTwoResidual) :
    BealPosCubeAddTwoCubeResidual :=
  BealPosCubeAddTwoCubeResidual_of_affine hAff

/-- Phase 7m: even-diff conjugate factors have gcd dividing 2. -/
example {B C : ℤ} {k : ℕ} (hcop : Nat.Coprime B.natAbs C.natAbs) :
    Nat.gcd (C ^ k - B ^ k).natAbs (C ^ k + B ^ k).natAbs ∣ 2 :=
  nat_gcd_pow_diff_sum_dvd_two hcop

/-- Phase 7m: `|u|=1` closed for odd `e ≥ 3` via Mihăilescu. -/
example {m n : ℤ} {c e : ℕ}
    (hm0 : m ≠ 0) (hn0 : n ≠ 0) (he : 3 ≤ e)
    (heq : m ^ 2 + n ^ 2 = (c : ℤ) ^ e)
    (hform :
      (∃ v : ℕ, n.natAbs = 1 ∧ 2 * m.natAbs = v ^ e) ∨
        (∃ v : ℕ, m.natAbs = 1 ∧ 2 * n.natAbs = v ^ e)) : False :=
  not_eq_odd_two_factor_of_exp_ge_three_abs_one hm0 hn0 he heq hform

/-- Phase 7j: known non-coprime solution `3³ + 6³ = 3⁵` (not a counterexample). -/
example : (3 : ℤ) ^ 3 + 6 ^ 3 = 3 ^ 5 ∧ bealGcd 3 6 3 = 3 :=
  beal_known_noncoprime_three_six

/-- Phase 7j: known non-coprime solution `2³ + 2³ = 2⁴`. -/
example : (2 : ℤ) ^ 3 + 2 ^ 3 = 2 ^ 4 ∧ bealGcd 2 2 2 = 2 :=
  beal_known_noncoprime_two_two

/-- Phase 7k: known non-coprime sum is a perfect 5th power. -/
example : isNthPower (3 ^ 3 + 6 ^ 3) 5 = true :=
  beal_known_noncoprime_is_perfect_power

/-- Phase 7e: equal-exponent mismatch rotor ↔ CGA log-scale. -/
example (A C : ℤ) (p : ℕ) (hp : p ≠ 0) (hA : A ≠ 0) (hC : C ≠ 0) :
    mismatchRotor A C hA hC =
      rotorTorsion
        (pureBoost
          (2 * Real.log (bealRootMag C p p / bealRootMag A p p))) :=
  beal_eq_exp_mismatchRotor_scale A C p hp hA hC

/-- Three-way coprime Beal solutions are pairwise coprime. -/
example {A B C : ℤ} {x y z : ℕ}
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hgcd : bealGcd A B C = 1)
    (hsol : A ^ x + B ^ y = C ^ z) :
    Nat.Coprime A.natAbs B.natAbs ∧
      Nat.Coprime A.natAbs C.natAbs ∧
        Nat.Coprime B.natAbs C.natAbs :=
  beal_pairwise_coprime hA hB hC hx hy hz hgcd hsol

/-- Beal roots always lie on the m-power null lattice. -/
example (A : ℤ) (x m : ℕ) (hA : A ≠ 0) (hm : m ≠ 0) :
    IsCGAPowerLatticePoint (bealRootMag A x m) m :=
  bealRootMag_isCGAPowerLatticePoint A x m hA hm

/-- Balanced model gap never yields a modular winding witness. -/
example (N : ℕ) [NeZero N] {x y z : ℕ}
    (hx : 3 ≤ x) (hy : 3 ≤ y) (hz : 3 ≤ z) :
    ¬ ∃ w : ModularAmplificationWitness N (bealAmpExp x y z),
      w.t.val = pureBoostSeedOfRapidity N
        (Real.log 2 / (bealMinExp x y z : ℝ)) :=
  beal_balanced_gap_no_modularWitness N hx hy hz

/-- Elementary unit-base fragment: no positive `1 + b³ = c³`. -/
example {b c : ℤ} (hb : 0 < b) (hc : 0 < c) :
    ¬ ((1 : ℤ) + b ^ 3 = c ^ 3) :=
  not_one_add_pow_three_eq_pow_three hb hc

/-- Equal exponents place roots on the DST integer null lattice. -/
example (A B C : ℤ) (p : ℕ) (hp : p ≠ 0)
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0) :
    BealCGALatticeGauge A B C p p p p :=
  BealCGALatticeGauge_of_eq_exp A B C p hp hA hB hC

/-- Mixed-exponent seed misses the integer lattice (Beal-specific diagnostic). -/
example : ¬ BealCGALatticeGauge 2 2 2 4 4 3 3 :=
  not_BealCGALatticeGauge_two_two_two_four_four_three

/-- Window solution yields a modular winding witness. -/
example {A B C : ℤ} {x y z : ℕ}
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (hsol : A ^ x + B ^ y = C ^ z)
    (hle : 2 * Real.pi / bealAmpExp x y z ≤
      bealFracLogGap A C x z (bealMinExp x y z))
    (hlt : bealFracLogGap A C x z (bealMinExp x y z) <
      4 * Real.pi / bealAmpExp x y z) :
    let m := bealMinExp x y z
    let k := bealAmpExp x y z
    let N := k
    ∃ (hN : N ≠ 0),
      letI : NeZero N := ⟨hN⟩
      let t := quantizeBealMismatch N A C x z m
      IsAdmissible t ∧ ∃ w : ModularAmplificationWitness N k, w.t.val = t :=
  beal_winding_of_solution_window hA hB hC hsol hle hlt

/-- Diagnostic NoGo + window ⇒ coprime solutions miss the wide window. -/
example (hnogo : BealCGANoGo) {A B C : ℤ} {x y z : ℕ}
    (hx : 3 ≤ x) (hy : 3 ≤ y) (hz : 3 ≤ z)
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (hcoprime : bealGcd A B C = 1)
    (hsol : A ^ x + B ^ y = C ^ z) :
    ¬ (2 * Real.pi / bealAmpExp x y z ≤
        bealFracLogGap A C x z (bealMinExp x y z) ∧
      bealFracLogGap A C x z (bealMinExp x y z) <
        4 * Real.pi / bealAmpExp x y z) :=
  beal_coprime_not_in_wide_window_of_cga_nogo hnogo hx hy hz hA hB hC hcoprime hsol

/-- Triple root-magnitudes satisfy α^m + β^m = γ^m on a positive solution. -/
example {A B C : ℤ} {x y z m : ℕ} (hm : m ≠ 0)
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (hsol : A ^ x + B ^ y = C ^ z) :
    bealRootMag A x m ^ m + bealRootMag B y m ^ m =
      bealRootMag C z m ^ m :=
  beal_rootMag_pow_sum_of_solution hm hA hB hC hsol

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

/-- Raw admissible ceiling `|J| ≤ 3π²/8`. -/
example (p : TorsionParams) (h : IsAdmissibleContinuous p) :
    |J p| ≤ 3 * Real.pi ^ 2 / 8 :=
  torsion_bound_raw_continuous_pi_sq p h

/-- Equality `|JNormalized| = 1` characterises the two extremals. -/
example (p : TorsionParams) (h : IsAdmissibleContinuous p) :
    |JNormalized p| = 1 ↔ IsPureHyperbolic p ∨ IsPureElliptic p :=
  abs_JNormalized_eq_one_iff p h

/-- Image of `JNormalized` on the admissible cone is all of `[-1, 1]`. -/
example (y : ℝ) (hy : |y| ≤ 1) :
    ∃ p : TorsionParams, IsAdmissibleContinuous p ∧ JNormalized p = y :=
  exists_admissible_JNormalized y hy

/-- Naive principal-branch bound remains false. -/
example : ∃ p : TorsionParams, IsPrincipalBranch p ∧ 1 < |J p| :=
  torsion_bound_naive_false

/-- Unsigned mass is bounded on the admissible cone. -/
example (p : TorsionParams) (h : IsAdmissibleContinuous p) :
    massNormalized p ≤ 1 :=
  massNormalized_bound_continuous p h

/-- Paper Ch.6 step “`J = 0` ⇒ vacuum / trivial bases” is false. -/
example :
    ∃ p : TorsionParams,
      IsAdmissibleContinuous p ∧ JNormalized p = 0 ∧ 0 < mass p :=
  JNormalized_zero_not_implies_vacuum

/-- Discrete rotor image is finite (not an integer-order unit group). -/
example {N : ℕ} [NeZero N] : (DiscreteRotorImage N).Finite :=
  discreteRotorImage_finite

/-- Continuum approximation of `J`. -/
example {p : TorsionParams} (h : IsAdmissibleContinuous p) {ε : ℝ} (hε : 0 < ε) :
    ∃ (N : ℕ) (_ : NeZero N),
      ∃ t : DiscreteTorsion N, IsAdmissible t ∧
        |J p - J (toTorsionParams t)| < ε :=
  exists_discrete_approx_J h hε

/-- Discrete admissible values of `JNormalized` are dense in `[-1, 1]`. -/
example {y ε : ℝ} (hy : |y| ≤ 1) (hε : 0 < ε) :
    ∃ (N : ℕ) (_ : NeZero N),
      ∃ t : DiscreteTorsion N, IsAdmissible t ∧
        |JNormalized (toTorsionParams t) - y| < ε :=
  dense_discrete_JNormalized hy hε

/-- When `4 ∣ N`, the lattice attains `±1`. -/
example : JNormalized (toTorsionParams (pureHyperbolicDiscrete 4)) = 1 :=
  JNormalized_pureHyperbolicDiscrete (by decide : 4 ∣ 4)

example : JNormalized (toTorsionParams (pureEllipticDiscrete 4)) = -1 :=
  JNormalized_pureEllipticDiscrete (by decide : 4 ∣ 4)

/-- When `¬ 4 ∣ N`, the admissible bound is strict. -/
example (t : DiscreteTorsion 3) (h : IsAdmissible t) :
    |JNormalized (toTorsionParams t)| < 1 :=
  torsion_bound_discrete_strict (by decide : ¬ 4 ∣ 3) t h

/-! ### Algebraic sandwich surface (Gravity intentionally out of scope) -/

/-- Sandwich composition law. -/
example (m n v : PGA) :
    sandwich (m * n) v = sandwich m (sandwich n v) :=
  sandwich_comp m n v

/-- Pure boost leaves the orthogonal leg `ι 2` invariant. -/
example (φ : ℝ) :
    sandwich (rotorTorsion (pureBoost φ)) (ι 2) = ι 2 :=
  sandwich_pureBoost_ι2 φ

/-- Lightlike plus eigenvector of a pure boost. -/
example (φ : ℝ) :
    sandwich (rotorTorsion (pureBoost φ)) (ι 0 + ι 1) =
      Real.exp φ • (ι 0 + ι 1) :=
  sandwich_pureBoost_lightlike_plus φ

/-- Lightlike minus eigenvector of a pure boost. -/
example (φ : ℝ) :
    sandwich (rotorTorsion (pureBoost φ)) (ι 0 - ι 1) =
      Real.exp (-φ) • (ι 0 - ι 1) :=
  sandwich_pureBoost_lightlike_minus φ

end DstDiophantine.FoundationRegression
