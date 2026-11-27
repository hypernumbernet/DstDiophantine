import DoubleSpacetime.Framework.Amplification
import DoubleSpacetime.Framework.Representation
import DoubleSpacetime.Framework.Lattice
import DoubleSpacetime.Framework.DiscreteCount
import DoubleSpacetime.Framework.Spectrum
import DoubleSpacetime.Framework.SpectrumSearch
import DoubleSpacetime.Algebra.Periodicity
import DoubleSpacetime.Embedding.Height
import DoubleSpacetime.Embedding.RotorClass
import DoubleSpacetime.Algebra.Amplification
import DoubleSpacetime.Algebra.ModularAmplification
import DoubleSpacetime.Algebra.Invariant
import DoubleSpacetime.Algebra.Discrete
import DoubleSpacetime.Algebra.Operations
import DoubleSpacetime.Algebra.Continuum
import DoubleSpacetime.Algebra.UnitGroup
import DoubleSpacetime.Algebra.Generators
import DoubleSpacetime.Algebra.LorentzLie
import DoubleSpacetime.Algebra.Motor
import DoubleSpacetime.Algebra.MotorGroup
import DoubleSpacetime.Algebra.Sandwich
import DoubleSpacetime.Algebra.PGA
import DoubleSpacetime.Theorems.Fermat
import DoubleSpacetime.Theorems.FermatMixed
import DoubleSpacetime.Theorems.Beal
import DoubleSpacetime.Theorems.BealSlice
import DoubleSpacetime.Theorems.BealPythagorean
import DoubleSpacetime.Theorems.BealGaussian
import DoubleSpacetime.Theorems.BealMixed
import DoubleSpacetime.Theorems.BealEven
import DoubleSpacetime.Theorems.BealGaussianCube
import DoubleSpacetime.Theorems.BealFinite
import DoubleSpacetime.Theorems.BealResidualSearch
import DoubleSpacetime.Theorems.BealRegime
import DoubleSpacetime.Theorems.DarmonMerel
import DoubleSpacetime.Theorems.FermatNN5
import DoubleSpacetime.Theorems.Bruin
import DoubleSpacetime.Theorems.SiksekStoll
import DoubleSpacetime.Theorems.AnniSiksek
import DoubleSpacetime.Theorems.DahmenSiksek
import DoubleSpacetime.Theorems.BennettEllenbergNg
import DoubleSpacetime.Theorems.FermatLast
import DoubleSpacetime.Theorems.Abc
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.Data.Fintype.Card

set_option linter.style.native false

/-!
# Public-API regression examples

These examples guard export and layering of the shared core. Classical conjectures are not claimed
here. `FermatMixedMotorResidual` follows from the open face `FermatMixedMotorOddPrimeResidual`.
-/

namespace DoubleSpacetime.FoundationRegression

open Amplification Discrete Invariant Framework Theorems ModularAmplification Motor
open Operations Continuum UnitGroup Generators Sandwich PGA Periodicity LorentzLie MotorGroup
open CliffordAlgebra (reverse)
open _root_.DoubleSpacetime.Embedding
open _root_.DoubleSpacetime.Logic

example (a b c : ℤ) (p : ℕ) :
    a ^ p + b ^ p = c ^ p ↔ powerSumMotor (fermatEquation a b c p) = 1 :=
  fermat_solution_iff_motor a b c p

example (θ : ℝ) {k : ℕ} (hk : 1 ≤ k)
    (hadm : IsAdmissibleContinuous (pureBoost (k * θ))) :
    |JNormalized (pureBoost θ)| ≤ 1 / (k : ℝ) ^ 2 :=
  amplification_implies_seed_le θ hk hadm

example {N : ℕ} [NeZero N] (t : DiscreteTorsion N) (hne : latticeMismatch t ≠ 0) :
    (16 : ℝ) / (3 * N ^ 2) ≤ |JNormalized (toTorsionParams t)| :=
  discrete_nonzero_height_lb t hne

example {N k : ℕ} [NeZero N] (hk : 1 ≤ k)
    (hcoarse : 3 * N ^ 2 < 16 * k ^ 2) (t : AdmissibleClass N)
    (hne : latticeMismatch t.val ≠ 0)
    (hadm :
      IsAdmissibleContinuous
        (scaleTorsion (k : ℝ) (AdmissibleClass.toParams t))) :
    False :=
  coarse_discrete_contradiction hk hcoarse t hne hadm

example (θ : ℝ) :
    JNormalized (pureBoost θ) = (4 / (3 * Real.pi ^ 2)) * θ ^ 2 :=
  JNormalized_pureBoost θ

example (θ : ℝ) :
    IsAdmissibleContinuous (pureBoost θ) ↔ 0 ≤ θ ∧ θ ≤ Real.pi / 2 :=
  isAdmissibleContinuous_pureBoost_iff θ

/-- Conditional; the coarse payload is vacuous. -/
example (hbridge : FermatCoarseDiscreteBridge) :
    ∀ (a b c : ℤ) (p : ℕ), 3 ≤ p → a ≠ 0 → b ≠ 0 → c ≠ 0 →
      ¬ (a ^ p + b ^ p = c ^ p) :=
  fermat_last_theorem_of_coarse_discrete_bridge hbridge

example {N k : ℕ} [NeZero N] (hk : 1 ≤ k)
    (hcoarse : 3 * N ^ 2 < 16 * k ^ 2)
    (w : CoarseAmplificationWitness N k) : False :=
  w.false hk hcoarse

example {N k : ℕ} [NeZero N] (hk : 1 ≤ k)
    (hcoarse : 3 * N ^ 2 < 16 * k ^ 2)
    (w : CoarseAmplificationWitness N k) : False :=
  CoarseAmplificationWitness.empty_of_coarse hk hcoarse w

example {N k : ℕ} (hcoarse : 3 * N ^ 2 < 16 * k ^ 2) : N < 4 * k :=
  coarse_implies_lt_four_mul hcoarse

example : Nonempty (ModularAmplificationWitness 16 5) :=
  ModularAmplificationWitness.nonempty_example

example {N : ℕ} [NeZero N] (k : ℕ) (x : ZMod N) :
    k * x.val = (k • x).val + N * windingCoord k x :=
  mul_val_eq_val_add_winding k x

example {N k : ℕ} [NeZero N] (t : DiscreteTorsion N)
    (hadm : IsAdmissibleContinuous (scaleTorsion (k : ℝ) (toTorsionParams t))) :
    windingTotal k t = 0 :=
  admissible_scale_implies_windingTotal_eq_zero k t hadm

example {N k : ℕ} [NeZero N] (w : ModularAmplificationWitness N k) :
    ¬ IsAdmissibleContinuous (scaleTorsion (k : ℝ) (toTorsionParams w.t.val)) :=
  ModularAmplificationWitness.not_admissible_real_scale w

example {N : ℕ} [NeZero N] (n : ℤ) (hn : n ≠ 0) (habs : Int.natAbs n = 1) :
    quantizeInt N n hn = zeroTorsion N :=
  quantizeInt_one n hn habs

/-- Diagnostic: geometric larger-base seeds have winding 0. -/
example (hbridge : FermatModularBridge) :
    ∀ (a b c : ℤ) (p : ℕ), 3 ≤ p → a ≠ 0 → b ≠ 0 → c ≠ 0 →
      ¬ (a ^ p + b ^ p = c ^ p) :=
  fermat_last_theorem_of_modular_bridge hbridge

example (N : ℕ) [NeZero N] {a b c : ℤ} {p : ℕ} (hp : 1 ≤ p)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hle : a ≤ b)
    (hsol : a ^ p + b ^ p = c ^ p) :
    ¬ ∃ w : ModularAmplificationWitness N p,
      w.t.val = quantizeMismatch N b c (ne_of_gt hb) (ne_of_gt hc) :=
  fermat_larger_base_no_modularWitness N hp ha hb hc hle hsol

example (hres : FermatMixedMotorResidual) : FermatLastTheorem :=
  FermatLastTheorem_of_mixed_motor_residual hres

example {a b c : ℤ} {n : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a ^ n + b ^ n = c ^ n ↔
      Real.exp (n * fermatBoost a b c (ne_of_gt hc)) *
        (Real.cos (fermatAngle a b (ne_of_gt ha)) ^ n +
          Real.sin (fermatAngle a b (ne_of_gt ha)) ^ n) = 1 :=
  fermat_solution_iff_polar ha hb hc

example {n : ℕ} (hn : 3 ≤ n) :
    let c : ℝ := 2 ^ ((1 : ℝ) / n)
    0 < c ∧ (1 : ℝ) ^ n + (1 : ℝ) ^ n = c ^ n ∧
      0 < Real.log (Real.sqrt 2 / c) :=
  equal_leg_real_boost_pos hn

example {a b c : ℤ} {n : ℕ} (hn : 3 ≤ n) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hdvd : a ∣ b) :
    a ^ n + b ^ n ≠ c ^ n :=
  not_fermat_pos_of_dvd_leg hn ha hb hc hdvd

example {a b c n : ℕ} (hp : Nat.Prime n) (hodd : Odd n)
    (ha : 0 < a) (hb : 0 < b) (hcop : Nat.Coprime a b)
    (hnd : ¬ n ∣ a * b * c) (hsol : a ^ n + b ^ n = c ^ n) :
    ∃ m t : ℕ, 1 < m ∧ 0 < t ∧ Nat.Coprime m t ∧
      a + b = m ^ n ∧ (a ^ n + b ^ n) / (a + b) = t ^ n ∧ c = m * t :=
  fermat_odd_prime_leg_sum_pow hp hodd ha hb hcop hnd hsol

example {a b c : ℤ} {n : ℕ} (hn : 3 ≤ n) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hsol : a ^ n + b ^ n = c ^ n) :
    c ^ 2 < a ^ 2 + b ^ 2 ∧
      fermatBoost a b c (ne_of_gt hc) =
        Real.log (1 + ((a : ℝ) ^ 2 + (b : ℝ) ^ 2 - (c : ℝ) ^ 2) / (c : ℝ) ^ 2) / 2 ∧
      Real.log (1 + 1 / (c : ℝ) ^ 2) / 2 ≤ fermatBoost a b c (ne_of_gt hc) :=
  ⟨fermat_sq_excess_pos hn ha hb hc hsol,
    fermatBoost_eq_half_log_excess ha hb hc,
    fermatBoost_ge_half_log_one_over_sq hn ha hb hc hsol⟩

example {a b c n : ℕ} (hp : Nat.Prime n) (hodd : Odd n)
    (ha : 0 < a) (hb : 0 < b) (hcop : Nat.Coprime a b)
    (hnd : ¬ n ∣ a * b * c) (hsol : a ^ n + b ^ n = c ^ n) :
    ∃ p q r t : ℕ, 1 < p ∧ 0 < q ∧ 0 < r ∧ 1 < t ∧
      Nat.Coprime p q ∧ Nat.Coprime p r ∧ Nat.Coprime q r ∧ Nat.Coprime p t ∧
      a + b = p ^ n ∧ c - a = q ^ n ∧ c - b = r ^ n ∧
      p ^ n + q ^ n + r ^ n = 2 * c ∧
      (a ^ n + b ^ n) / (a + b) = t ^ n ∧ c = p * t :=
  fermat_odd_prime_three_powers hp hodd ha hb hcop hnd hsol

example {a b c n : ℕ} (hp : Nat.Prime n) (hodd : Odd n)
    (ha : 0 < a) (hb : 0 < b) (hcop : Nat.Coprime a b)
    (hnd : ¬ n ∣ a * b * c) (hsol : a ^ n + b ^ n = c ^ n) :
    ¬ Nat.Prime c ∧
      ∃ p q r : ℕ, 1 < p ∧ 0 < q ∧ 0 < r ∧
        a = (p ^ n + r ^ n - q ^ n) / 2 ∧
        b = (p ^ n + q ^ n - r ^ n) / 2 ∧
        c = (p ^ n + q ^ n + r ^ n) / 2 :=
  ⟨fermat_odd_prime_hypotenuse_composite hp hodd ha hb hcop hnd hsol,
    fermat_bases_of_three_powers hp hodd ha hb hcop hnd hsol⟩

example {a b c : ℤ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hE : a ^ 2 + b ^ 2 = c ^ 2 + 1) (n : ℕ) :
    fermatBoost a b c (ne_of_gt hc) = Real.log (1 + 1 / (c : ℝ) ^ 2) / 2 ∧
      Real.exp ((n : ℝ) * fermatBoost a b c (ne_of_gt hc)) *
        ((c : ℝ) ^ 2 / ((c : ℝ) ^ 2 + 1)) ^ ((n : ℝ) / 2) = 1 :=
  ⟨fermatBoost_eq_half_log_of_excess_one ha hb hc hE,
    fermat_excess_one_polar_touches_boost ha hb hc hE⟩

example (hres : FermatMixedMotorOddPrimeResidual) : FermatMixedMotorResidual :=
  FermatMixedMotorResidual_of_oddPrime hres

example (a b c : ℤ) (ha : a ≠ 0) (hc : c ≠ 0) :
    omegaTorsion (fermatTorsion a b c ha hc) =
      (fermatBoost a b c hc / 2) • hyperbolic 0 +
        (fermatAngle a b ha / 2) • cyclic 1 :=
  omegaTorsion_fermatTorsion a b c ha hc

example (a b c : ℤ) (ha : a ≠ 0) (hc : c ≠ 0) :
    fermatInterfere a b c ha hc =
      ((fermatBoost a b c hc * fermatAngle a b ha) / 2) • hyperbolic 2 :=
  fermatInterfere_eq a b c ha hc

example {a b c : ℤ} (ha : a ≠ 0) (hc : c ≠ 0)
    (h : IsMixedFermatMotor a b c ha hc) :
    fermatInterfere a b c ha hc ≠ 0 :=
  fermatInterfere_ne_zero_of_mixed ha hc h

example {a b c : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    fermatInterfere a b c ha hc = 0 ↔ IsPureCyclicFermatMotor a b c hc :=
  fermatInterfere_eq_zero_iff_pureCyclic ha hb hc

example {a b c : ℤ} {n : ℕ}
    (hn : 3 ≤ n) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hsol : a ^ n + b ^ n = c ^ n) :
    IsMixedFermatMotor a b c (ne_of_gt ha) (ne_of_gt hc) :=
  isMixedFermatMotor_of_sol hn ha hb hc hsol

example {a b c : ℤ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    IsPureCyclicFermatMotor a b c (ne_of_gt hc) ↔ a ^ 2 + b ^ 2 = c ^ 2 :=
  fermatBoost_eq_zero_iff_pythagorean ha hb hc

example (a b c : ℤ) (ha : a ≠ 0) (hc : c ≠ 0) :
    Generators.commutator (omegaTorsion (fermatTorsion a b c ha hc)) (null 3) =
      fermatAngle a b ha • null 1 :=
  commutator_fermatTorsion_null3 a b c ha hc

example {a b c : ℤ} (ha : a ≠ 0) (hc : c ≠ 0)
    (hβ : 0 < fermatAngle a b ha) :
    sandwich (rotorTorsion (fermatAngleSeed a b ha)) (null 3) ≠
      sandwich (rotorTorsion (fermatBoostSeed a b c hc)) (null 3) :=
  sandwich_fermatAngle_null3_ne_pureBoost ha hc hβ

example {a b c : ℤ} (ha : a ≠ 0) (hc : c ≠ 0)
    (h : IsMixedFermatMotor a b c ha hc) :
    ∃ t : ℝ,
      sandwich (NormedSpace.exp (t • omegaTorsion (fermatTorsion a b c ha hc)))
          (null 3) ≠
        sandwich (NormedSpace.exp (t • omegaTorsion (fermatBoostSeed a b c hc)))
          (null 3) :=
  exists_sandwich_fermat_ne_pureBoost ha hc h

example (a b c : ℤ) (ha : a ≠ 0) (hc : c ≠ 0) :
    Generators.commutator (omegaTorsion (fermatTorsion a b c ha hc)) (null 1) =
      fermatBoost a b c hc • null 0 - fermatAngle a b ha • null 3 :=
  commutator_fermatTorsion_null1 a b c ha hc

example {a b c : ℤ} (ha : a ≠ 0) (hc : c ≠ 0)
    (h : IsMixedFermatMotor a b c ha hc) :
    ∃ t : ℝ,
      sandwich (NormedSpace.exp (t • omegaTorsion (fermatTorsion a b c ha hc)))
          (null 1) ≠
        sandwich (NormedSpace.exp (t • omegaTorsion (fermatAngleSeed a b ha)))
          (null 1) :=
  exists_sandwich_fermat_ne_cyclic_null1 ha hc h

example (a b c : ℤ) (ha : a ≠ 0) (hc : c ≠ 0) :
    Generators.commutator (omegaTorsion (fermatTorsion a b c ha hc))
      (Generators.commutator (omegaTorsion (fermatTorsion a b c ha hc)) (null 3)) =
      (fermatBoost a b c hc * fermatAngle a b ha) • null 0 -
        (fermatAngle a b ha) ^ 2 • null 3 :=
  commutator_fermatTorsion_null3_two a b c ha hc

example {a b c : ℤ} {n : ℕ}
    (hn : 3 ≤ n) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hsol : a ^ n + b ^ n = c ^ n) :
    fermatBoost a b c (ne_of_gt hc) < fermatAngle a b (ne_of_gt ha) ∧
      0 < fermatMixedFreq a b c (ne_of_gt ha) (ne_of_gt hc) :=
  ⟨fermatBoost_lt_fermatAngle (Nat.le_trans (by decide : 1 ≤ 3) hn) ha hb hc hsol,
    fermatMixedFreq_pos hn ha hb hc hsol⟩

example {a b c : ℤ} (ha : a ≠ 0) (hc : c ≠ 0)
    (hω : 0 < fermatMixedFreq a b c ha hc) (t : ℝ) :
    sandwich (NormedSpace.exp (t • omegaTorsion (fermatTorsion a b c ha hc))) (null 1) =
      Real.cos (fermatMixedFreq a b c ha hc * t) • null 1 +
        (Real.sin (fermatMixedFreq a b c ha hc * t) / fermatMixedFreq a b c ha hc) •
          (fermatBoost a b c hc • null 0 - fermatAngle a b ha • null 3) :=
  sandwich_fermatTorsion_null1_elliptic ha hc hω t

example {a b c : ℤ} {n : ℕ}
    (hn : 3 ≤ n) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hsol : a ^ n + b ^ n = c ^ n) :
    sandwich (fermatMotorRotor a b c (ne_of_gt ha) (ne_of_gt hc)) (null 1) -
        Real.cos (fermatMixedFreq a b c (ne_of_gt ha) (ne_of_gt hc)) • null 1 +
          (Real.sin (fermatMixedFreq a b c (ne_of_gt ha) (ne_of_gt hc)) /
            fermatMixedFreq a b c (ne_of_gt ha) (ne_of_gt hc) *
              fermatAngle a b (ne_of_gt ha)) • null 3 ≠ 0 :=
  sandwich_fermatTorsion_null1_time_ne_zero_of_sol hn ha hb hc hsol

example {p : ℕ} (hp : 1 ≤ p) :
    |JNormalized (pureBoost (Real.log 2 / (p : ℝ)))| < (1 : ℝ) / (p : ℝ) ^ 2 :=
  fermat_balanced_seed_lt_threshold hp

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


example (A B C : ℤ) (x y z : ℕ) :
    let d := bealExpGcd x y z
    A ^ x + B ^ y = C ^ z ↔
      (A ^ (x / d)) ^ d + (B ^ (y / d)) ^ d = (C ^ (z / d)) ^ d :=
  beal_eq_pow_mul_expGcd A B C x y z

example (hFLT : FermatLastTheorem) {A B C : ℤ} {x y z : ℕ}
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hd : 3 ≤ bealExpGcd x y z) :
    ¬ A ^ x + B ^ y = C ^ z :=
  not_beal_sol_of_expGcd_ge_three_of_FLT hFLT hA hB hC hd

example (hbridge : FermatModularBridge) {A B C : ℤ} {x y z : ℕ}
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hd : 3 ≤ bealExpGcd x y z) :
    ¬ A ^ x + B ^ y = C ^ z :=
  not_beal_sol_of_expGcd_ge_three_of_modular_bridge hbridge hA hB hC hd

example {x y z : ℕ} (hx : 3 ≤ x) :
    bealExpGcd x y z = 1 ∨ bealExpGcd x y z = 2 ∨ 3 ≤ bealExpGcd x y z :=
  bealExpGcd_eq_one_or_eq_two_or_ge_three hx

example {A B C : ℤ} {x y z : ℕ}
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hdvd : 3 ∣ bealExpGcd x y z ∨ 4 ∣ bealExpGcd x y z) :
    ¬ A ^ x + B ^ y = C ^ z :=
  not_beal_sol_of_three_or_four_dvd_expGcd hA hB hC hdvd

example {A B C : ℤ} (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0) :
    ¬ A ^ 3 + B ^ 3 = C ^ 3 ∧ ¬ A ^ 4 + B ^ 4 = C ^ 4 :=
  ⟨not_beal_eq_exp_three hA hB hC, not_beal_eq_exp_four hA hB hC⟩

example {A B C : ℤ} {x y z : ℕ}
    (hx : 3 ≤ x) (hy : 3 ≤ y) (hz : 3 ≤ z)
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hd : bealExpGcd x y z = 2)
    (hx4 : 4 ∣ x) (hy4 : 4 ∣ y) :
    ¬ A ^ x + B ^ y = C ^ z :=
  not_beal_sol_of_expGcd_eq_two_of_four_dvd_xy hx hy hz hA hB hC hd hx4 hy4

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

example {A B C : ℤ} {x y z : ℕ}
    (hx : 3 ≤ x) (hxy : x = y) (hd : bealExpGcd x y z = 1)
    (hsol : A ^ x + B ^ y = C ^ z) :
    Nat.gcd x z = 1 ∧ x ≠ z ∧ A ^ x + B ^ x = C ^ z :=
  beal_eq_two_exp_form_of_expGcd_eq_one hx hxy hd hsol

example {A B C : ℤ} {x y z : ℕ}
    (hx : 3 ≤ x) (hy : 3 ≤ y) (hz : 3 ≤ z)
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hd : bealExpGcd x y z = 2)
    (hx4 : 4 ∣ x) (hz4 : 4 ∣ z) :
    ¬ A ^ x + B ^ y = C ^ z :=
  not_beal_sol_of_expGcd_eq_two_of_four_dvd_xz hx hy hz hA hB hC hd hx4 hz4

example {A B C : ℤ} {x y z : ℕ}
    (hx : 3 ≤ x) (hy : 3 ≤ y) (hz : 3 ≤ z)
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hd : bealExpGcd x y z = 2)
    (h4 : (4 ∣ x ∧ 4 ∣ y) ∨ (4 ∣ x ∧ 4 ∣ z) ∨ (4 ∣ y ∧ 4 ∣ z)) :
    ¬ A ^ x + B ^ y = C ^ z :=
  not_beal_sol_of_expGcd_eq_two_of_two_four_dvd hx hy hz hA hB hC hd h4

example {m n k : ℕ}
    (hcop : Nat.Coprime m n)
    (hpar : (Even m ∧ Odd n) ∨ (Odd m ∧ Even n))
    (heq : 2 * m * n = k ^ 2) :
    (Even m ∧ (∃ u v, n = u ^ 2 ∧ 2 * m = v ^ 2)) ∨
      (Even n ∧ (∃ u v, m = u ^ 2 ∧ 2 * n = v ^ 2)) :=
  exists_sq_of_two_mul_coprime_eq_sq hcop hpar heq

example : Prop := BealPythagoreanResidual

example {x y z : ℕ} (hd : bealExpGcd x y z = 2) :
    (¬ (4 ∣ x ∧ 4 ∣ y) ∧ ¬ (4 ∣ x ∧ 4 ∣ z) ∧ ¬ (4 ∣ y ∧ 4 ∣ z)) ↔
      (Odd (x / 2) ∧ Odd (y / 2)) ∨
        (Odd (x / 2) ∧ Odd (z / 2)) ∨
          (Odd (y / 2) ∧ Odd (z / 2)) :=
  beal_pythagorean_residual_iff_two_odd_reduced hd

example {A B C : ℤ} {x y z : ℕ}
    (hy : 3 ≤ y) (hyz : y = z) (hd : bealExpGcd x y z = 1)
    (hsol : A ^ x + B ^ y = C ^ z) :
    Nat.gcd x y = 1 ∧ x ≠ y ∧ A ^ x + B ^ y = C ^ y :=
  beal_eq_two_exp_yz_form_of_expGcd_eq_one hy hyz hd hsol

example {A B C : ℤ} {x y z : ℕ}
    (hx : 3 ≤ x) (hxz : x = z) (hd : bealExpGcd x y z = 1)
    (hsol : A ^ x + B ^ y = C ^ z) :
    Nat.gcd x y = 1 ∧ x ≠ y ∧ A ^ x + B ^ y = C ^ x :=
  beal_eq_two_exp_xz_form_of_expGcd_eq_one hx hxz hd hsol

example {x y z : ℕ} (hd : bealExpGcd x y z = 1) :
    x = y ∨ y = z ∨ x = z ∨ (x ≠ y ∧ y ≠ z ∧ x ≠ z) :=
  beal_expGcd_eq_one_two_equal_or_all_distinct hd

example {A B C : ℤ} {x y z : ℕ}
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hd : 3 ≤ bealExpGcd x y z)
    (hsol : A ^ x + B ^ y = C ^ z) : False :=
  not_beal_sol_of_expGcd_ge_three hA hB hC hd hsol

example (hMix : BealMixedExpResidual) (hPyth : BealPythagoreanResidual) :
    ∀ {A B C : ℤ} {x y z : ℕ},
      3 ≤ x → 3 ≤ y → 3 ≤ z →
      0 < A → 0 < B → 0 < C →
      A ^ x + B ^ y = C ^ z →
      1 < bealGcd A B C :=
  beal_conjecture_pos_of_residuals hMix hPyth

example {m n c : ℤ} {e : ℕ} (he : 0 < e)
    (hcop : Int.gcd m n = 1)
    (hpar : (Even m ∧ Odd n) ∨ (Odd m ∧ Even n))
    (heq : m ^ 2 + n ^ 2 = c ^ e) :
    IsGaussianHypotenusePower m n e :=
  isGaussianHypotenusePower_of_hyp_eq_pow he hcop hpar heq

example : Prop := BealEqualOddTwoFactorResidual

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

example (hEven : BealTwoEqualEvenResidual) (hOdd : BealTwoEqualOddResidual)
    (hDist : BealAllDistinctExpResidual) : BealMixedExpResidual :=
  beal_mixed_exp_of_subresiduals hEven hOdd hDist

example (hEq : BealEqualOddTwoFactorResidual)
    (hUneq : BealPythagoreanUnequalOddResidual) : BealPythagoreanResidual :=
  beal_pythagorean_of_subresiduals hEq hUneq

example (hEven : BealTwoEqualEvenResidual) (hOdd : BealTwoEqualOddResidual)
    (hDist : BealAllDistinctExpResidual) (hEq : BealEqualOddTwoFactorResidual)
    (hUneq : BealPythagoreanUnequalOddResidual) :
    ∀ {A B C : ℤ} {x y z : ℕ},
      3 ≤ x → 3 ≤ y → 3 ≤ z →
      0 < A → 0 < B → 0 < C →
      A ^ x + B ^ y = C ^ z →
      1 < bealGcd A B C :=
  beal_conjecture_pos_of_fine_residuals hEven hOdd hDist hEq hUneq

example {A B C : ℤ} {x y z : ℕ}
    (hx : 3 ≤ x) (hz : 3 ≤ z) (hxy : x = y) (hd : bealExpGcd x y z = 1)
    (hxeven : Even x)
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hgcd : bealGcd A B C = 1)
    (hsol : A ^ x + B ^ y = C ^ z) :
    IsGaussianHypotenusePower (A ^ (x / 2)) (B ^ (x / 2)) z :=
  (exists_gaussian_hyp_pow_of_two_equal_xy_even hx hz hxy hd hxeven hA hB hC hgcd hsol).2.2.1

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

example (hSum : BealTwoEqualEvenSumResidual) (hDiff : BealTwoEqualEvenDiffResidual) :
    BealTwoEqualEvenResidual :=
  beal_two_equal_even_of_sum_diff hSum hDiff

example (a b : ℤ) :
    (⟨a, b⟩ : GaussianInt) ^ 3 =
      ⟨a ^ 3 - 3 * a * b ^ 2, 3 * a ^ 2 * b - b ^ 3⟩ :=
  gaussian_cube_eq a b

example {m v : ℕ} (hm : Odd m) : ¬ 2 * m = v ^ 3 :=
  not_two_mul_odd_eq_cube hm

example {m n : ℤ} {c : ℕ}
    (hm0 : m ≠ 0) (hn0 : n ≠ 0)
    (heq : m ^ 2 + n ^ 2 = (c : ℤ) ^ 3)
    (hform :
      (∃ v : ℕ, n.natAbs = 1 ∧ 2 * m.natAbs = v ^ 3) ∨
        (∃ v : ℕ, m.natAbs = 1 ∧ 2 * n.natAbs = v ^ 3)) : False :=
  not_eq_odd_two_factor_of_exp_three_abs_one hm0 hn0 heq hform

example (hGe5 : BealEqualOddTwoFactorExpGeFiveResidual) :
    BealEqualOddTwoFactorResidual :=
  BealEqualOddTwoFactorResidual_of_ge_five hGe5

example {α β γ : ℕ} (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ) :
    ¬ α ^ 3 + 2 * β ^ 3 = γ ^ 3 :=
  not_pos_cube_add_two_cube hα hβ hγ

example (hFac : BealTwoEqualEvenDiffFactorResidual) :
    BealTwoEqualEvenDiffResidual :=
  BealTwoEqualEvenDiffResidual_of_factor hFac

example (h5 : BealTwoEqualEvenSumExpFiveResidual)
    (h7 : BealTwoEqualEvenSumExpGeSevenResidual) :
    BealTwoEqualEvenSumResidual :=
  BealTwoEqualEvenSumResidual_of_five_ge_seven h5 h7

example (h7 : BealTwoEqualEvenSumExpGeSevenResidual) :
    BealTwoEqualEvenSumResidual :=
  BealTwoEqualEvenSumResidual_of_ge_seven h7

example {B C A : ℤ} {k x : ℕ}
    (hk : 0 < k)
    (hpar : (Even B ∧ Odd C) ∨ (Odd B ∧ Even C))
    (hcop : Nat.Coprime B.natAbs C.natAbs)
    (heq : (C ^ k - B ^ k) * (C ^ k + B ^ k) = A ^ x) :
    ∃ u v : ℕ,
      (2 * C ^ k = (u : ℤ) ^ x + (v : ℤ) ^ x ∨
        2 * C ^ k = (u : ℤ) ^ x + -((v : ℤ) ^ x) ∨
          2 * C ^ k = -((u : ℤ) ^ x) + (v : ℤ) ^ x ∨
            2 * C ^ k = -((u : ℤ) ^ x) + -((v : ℤ) ^ x)) ∧
        (2 * B ^ k = (v : ℤ) ^ x - (u : ℤ) ^ x ∨
          2 * B ^ k = -((v : ℤ) ^ x) - (u : ℤ) ^ x ∨
            2 * B ^ k = (v : ℤ) ^ x - -((u : ℤ) ^ x) ∨
              2 * B ^ k = -((v : ℤ) ^ x) - -((u : ℤ) ^ x)) :=
  exists_two_mul_pow_eq_signed_pow_add_opposite_parity hk hpar hcop heq

example {C B : ℤ} {y : ℕ} (hyeven : Even y) :
    C ^ y - B ^ y =
      (C ^ (y / 2) - B ^ (y / 2)) * (C ^ (y / 2) + B ^ (y / 2)) :=
  even_pow_sub_eq_mul hyeven

example {A B C x y z : ℕ}
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (hAmax : A ≤ 8) (hBmax : B ≤ 8) (hCmax : C ≤ 8)
    (hx : 3 ≤ x) (hy : 3 ≤ y) (hz : 3 ≤ z)
    (hxE : x ≤ 5) (hyE : y ≤ 5) (hzE : z ≤ 5)
    (hsol : A ^ x + B ^ y = C ^ z)
    (hgcd : Nat.gcd A (Nat.gcd B C) = 1) : False :=
  beal_no_coprime_of_le_eight_five hA hB hC hAmax hBmax hCmax hx hy hz hxE hyE hzE hsol hgcd

example {A B C x y z : ℕ}
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (hAmax : A ≤ 24) (hBmax : B ≤ 24)
    (hx : 3 ≤ x) (hy : 3 ≤ y) (hz : 3 ≤ z)
    (hxE : x ≤ 8) (hyE : y ≤ 8) (hzE : z ≤ 8)
    (hsol : A ^ x + B ^ y = C ^ z)
    (hgcd : Nat.gcd A (Nat.gcd B C) = 1) : False :=
  beal_no_coprime_perfect_power_of_le_twentyfour_eight
    hA hB hC hAmax hBmax hx hy hz hxE hyE hzE hsol hgcd

example : findCoprimeBealPerfectPowerUpTo 14 6 = none := by native_decide

example {α β γ : ℕ}
    (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ)
    (hαN : α ≤ 400) (hβN : β ≤ 400)
    (hαodd : α % 2 = 1) (hγodd : γ % 2 = 1)
    (hgcd : Nat.gcd α (Nat.gcd β γ) = 1)
    (heq : α ^ 3 + 2 * β ^ 3 = γ ^ 3) : False :=
  no_pos_cube_add_two_primitive_of_le_fourhundred
    hα hβ hγ hαN hβN hαodd hγodd hgcd heq

example {A B C x y z : ℕ}
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (hAmax : A ≤ 80) (hBmax : B ≤ 80)
    (hx : 3 ≤ x) (hy : 3 ≤ y) (hz : 3 ≤ z)
    (hxE : x ≤ 7) (hyE : y ≤ 7) (hzE : z ≤ 7)
    (hopen : isOpenResidualExponents x y z = true)
    (hsol : A ^ x + B ^ y = C ^ z)
    (hgcd : Nat.gcd A (Nat.gcd B C) = 1) : False :=
  beal_no_open_residual_perfect_power_of_le_eighty_seven
    hA hB hC hAmax hBmax hx hy hz hxE hyE hzE hopen hsol hgcd

example {x y z : ℕ} :
    classifyBealExponents x y z = .U ↔
      isOpenResidualExponents x y z = true :=
  classifyBealExponents_eq_U_iff

example {x y z : ℕ} :
    (classifyBealExponents x y z = .T ↔ IsClosedShapeExponents x y z) ∧
      classifyBealExponents x y z ≠ .B :=
  ⟨classifyBealExponents_eq_T_iff, classifyBealExponents_ne_B x y z⟩

/-- `(3,4,4)` stays open; `(4,4,3)` is Darmon–Merel. -/
example :
    classifyBealExponents 3 4 4 = .U ∧ classifyBealExponents 4 4 3 = .T :=
  ⟨classifyBealExponents_three_four_four, classifyBealExponents_four_four_three⟩

example {A B C : ℤ} {n : ℕ}
    (hn : n = 4 ∨ n = 5) (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hgcd : Nat.gcd A.natAbs (Nat.gcd B.natAbs C.natAbs) = 1) :
    ¬ A ^ 3 + B ^ 3 = C ^ n :=
  bruinSumTwoCubes A B C n hn hA hB hC hgcd

example (hOut : BealTwoEqualOddOutsideBruinResidual) :
    BealTwoEqualOddResidual :=
  BealTwoEqualOddResidual_of_outside_bruin hOut

example :
    classifyBealExponents 3 3 5 = .T ∧ classifyBealExponents 3 3 7 = .T ∧
      classifyBealExponents 3 4 5 = .T ∧ classifyBealExponents 3 5 7 = .U :=
  ⟨classifyBealExponents_three_three_five, classifyBealExponents_three_three_seven,
    classifyBealExponents_three_four_five, classifyBealExponents_three_five_seven⟩

example :
    classifyBealExponents 5 5 7 = .T ∧ classifyBealExponents 7 5 5 = .T ∧
      classifyBealExponents 5 7 5 = .T ∧ classifyBealExponents 5 5 19 = .T ∧
        classifyBealExponents 19 5 5 = .T ∧ classifyBealExponents 5 5 11 = .T :=
  classifyBealExponents_repeated_fifth

example {A B C : ℤ}
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hgcd : bealGcd A B C = 1) :
    ¬ A ^ 5 + B ^ 5 = C ^ 7 ∧ ¬ A ^ 7 + B ^ 5 = C ^ 5 ∧ ¬ A ^ 5 + B ^ 19 = C ^ 5 :=
  ⟨fun h => not_beal_repeated_fifth_shape hA hB hC hgcd (by decide) h,
    fun h => not_beal_repeated_fifth_shape hA hB hC hgcd (by decide) h,
    fun h => not_beal_repeated_fifth_shape hA hB hC hgcd (by decide) h⟩

example (hOut : BealTwoEqualOddOutsideRepeatedFifthResidual) :
    BealTwoEqualOddResidual :=
  BealTwoEqualOddResidual_of_outside_repeated_fifth hOut

example :
    classifyBealExponents 6 6 7 = .T ∧ classifyBealExponents 9 9 4 = .T ∧
      classifyBealExponents 3 6 5 = .T ∧ classifyBealExponents 5 6 6 = .T ∧
        classifyBealExponents 9 9 1000000001 = .T :=
  ⟨classifyBealExponents_six_six_seven, classifyBealExponents_nine_nine_four,
    classifyBealExponents_three_six_five, classifyBealExponents_five_six_six,
    classifyBealExponents_nine_nine_past_bound⟩

/-- A prime hypotenuse past `10^9` leaves the cube-pair shape only when `p ≡ 1 (mod 3)`.
`p ≡ 2 (mod 3)` is Freitas, Theorem 3. -/
example {A B C : ℤ} {p : ℕ}
    (hp : Nat.Prime p) (hgt : 1000000000 < p) (hmod : p % 3 = 2)
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hgcd : bealGcd A B C = 1) :
    ¬ A ^ 3 + B ^ 3 = C ^ p :=
  not_beal_three_three_large_freitas_prime hp hgt hmod hA hB hC hgcd

example {p : ℕ} (hp : Nat.Prime p) (hgt : 1000000000 < p) (hmod : p % 3 = 1) :
    ¬ IsCubePairPowerShape 3 3 p :=
  not_cubePair_three_three_large_prime hp hgt hmod

/-- `(4,7,7)` stays open; it is not a fourth-power sum. -/
example :
    classifyBealExponents 4 4 7 = .T ∧ classifyBealExponents 8 8 7 = .T ∧
      classifyBealExponents 4 4 9 = .T ∧ classifyBealExponents 4 7 7 = .U :=
  ⟨classifyBealExponents_four_four_seven, classifyBealExponents_fourth_sum⟩

example :
    classifyBealExponents 10 10 7 = .T ∧ classifyBealExponents 10 10 19 = .T ∧
      classifyBealExponents 7 10 10 = .T ∧ classifyBealExponents 5 10 7 = .T ∧
        classifyBealExponents 25 25 7 = .T ∧ classifyBealExponents 5 5 21 = .T ∧
          classifyBealExponents 10 10 14 = .T ∧
            classifyBealExponents 10 10 11 = .T ∧
              classifyBealExponents 5 5 11 = .T ∧
                classifyBealExponents 5 5 13 = .T ∧
                  classifyBealExponents 5 5 17 = .T ∧
                    classifyBealExponents 5 10 11 = .T ∧
                      classifyBealExponents 5 5 23 = .U ∧
                        classifyBealExponents 7 7 11 = .U :=
  classifyBealExponents_fifth_pair

example :
    classifyBealExponents 22 22 7 = .T ∧ classifyBealExponents 14 14 11 = .T ∧
      classifyBealExponents 14 14 13 = .T ∧ classifyBealExponents 14 14 17 = .T ∧
        classifyBealExponents 22 22 17 = .T ∧ classifyBealExponents 10 10 23 = .U ∧
          classifyBealExponents 14 14 19 = .U :=
  classifyBealExponents_anni_seventeenth

example :
    classifyBealExponents 10 10 9 = .T ∧ classifyBealExponents 14 14 9 = .T ∧
      classifyBealExponents 14 14 25 = .T ∧ classifyBealExponents 8 12 9 = .T ∧
        classifyBealExponents 9 7 7 = .T ∧ classifyBealExponents 10 10 11 = .T ∧
          classifyBealExponents 5 5 11 = .T ∧ classifyBealExponents 3 5 7 = .U ∧
            classifyBealExponents 22 22 7 = .T :=
  classifyBealExponents_shared_exp

example {A B C : ℤ}
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hgcd : bealGcd A B C = 1) :
    ¬ A ^ 10 + B ^ 10 = C ^ 7 ∧ ¬ A ^ 7 + B ^ 10 = C ^ 10 ∧
      ¬ A ^ 5 + B ^ 5 = C ^ 21 ∧ ¬ A ^ 10 + B ^ 10 = C ^ 9 ∧
        ¬ A ^ 5 + B ^ 5 = C ^ 11 ∧ ¬ A ^ 5 + B ^ 5 = C ^ 13 ∧
          ¬ A ^ 5 + B ^ 5 = C ^ 17 ∧ ¬ A ^ 10 + B ^ 10 = C ^ 11 :=
  ⟨fun h => not_beal_ten_ten_seven hA hB hC hgcd h,
    fun h => not_beal_seven_ten_ten hA hB hC hgcd h,
    fun h => not_beal_five_five_twenty_one hA hB hC hgcd h,
    fun h => not_beal_ten_ten_nine hA hB hC hgcd h,
    fun h => not_beal_five_five_eleven hA hB hC hgcd h,
    fun h => not_beal_five_five_thirteen hA hB hC hgcd h,
    fun h => not_beal_five_five_seventeen hA hB hC hgcd h,
    fun h => not_beal_ten_ten_eleven hA hB hC hgcd h⟩

example (hOut : BealTwoEqualEvenSumExpGeSevenOutsideAnniSeventeenthResidual) :
    BealTwoEqualEvenSumResidual :=
  BealTwoEqualEvenSumResidual_of_ge_seven_outside_anni hOut

example {A B C : ℤ}
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hgcd : bealGcd A B C = 1) :
    ¬ A ^ 22 + B ^ 22 = C ^ 7 ∧ ¬ A ^ 14 + B ^ 14 = C ^ 13 ∧
      ¬ A ^ 14 + B ^ 14 = C ^ 17 :=
  ⟨fun h => not_beal_twenty_two_twenty_two_seven hA hB hC hgcd h,
    fun h => not_beal_fourteen_fourteen_thirteen hA hB hC hgcd h,
    fun h => not_beal_fourteen_fourteen_seventeen hA hB hC hgcd h⟩

example {A B C : ℤ}
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hgcd : bealGcd A B C = 1) :
    ¬ A ^ 4 + B ^ 4 = C ^ 7 ∧ ¬ A ^ 8 + B ^ 8 = C ^ 9 :=
  ⟨fun h => not_beal_fourth_sum_shape (by decide) (by decide) (by decide)
      hA hB hC hgcd (by decide) h,
    fun h => not_beal_fourth_sum_shape (by decide) (by decide) (by decide)
      hA hB hC hgcd (by decide) h⟩

example (hOut : BealTwoEqualEvenSumExpGeSevenOutsideFourthResidual) :
    BealTwoEqualEvenSumResidual :=
  BealTwoEqualEvenSumResidual_of_ge_seven_outside_fourth hOut

example :
    ¬ EntailsTR {sliceFLT, sliceDM, sliceAbsOne, sliceFourth, sliceNN5, sliceBruin}
        bealConjecture :=
  closed_slices_not_entailsTR_beal

example :
    ¬ EntailsTR (bealClosedSliceAtomSet ∪ {liveMordell}) bealConjecture ∧
      ¬ EntailsTR bealArtefactAtomSet bealConjecture :=
  ⟨promote_liveMordell_not_entailsTR_beal, artefacts_not_entailsTR_beal⟩

example : balancedAmplitude.IsBalancedMassive ∧ ¬ balancedAmplitude.IsVacuum :=
  beal_balanced_diagnostic_seat

example (hAff : BealAffineCubeAddTwoResidual) :
    BealPosCubeAddTwoCubeResidual :=
  BealPosCubeAddTwoCubeResidual_of_affine hAff

example {α β γ : ℕ} (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ)
    (heq : α ^ 3 + 2 * β ^ 3 = γ ^ 3) :
    ∃ α' β' γ' : ℕ,
      0 < α' ∧ 0 < β' ∧ 0 < γ' ∧
        Nat.gcd α' (Nat.gcd β' γ') = 1 ∧ Odd α' ∧ Odd γ' ∧
          α' ^ 3 + 2 * β' ^ 3 = γ' ^ 3 :=
  exists_primitive_odd_pos_cube_of_pos hα hβ hγ heq

example :
    BealPosCubeAddTwoCubeResidual ↔
      ∀ (α β γ : ℕ), 0 < α → 0 < β → 0 < γ →
        Nat.gcd α (Nat.gcd β γ) = 1 → Odd α → Odd γ →
          ¬ α ^ 3 + 2 * β ^ 3 = γ ^ 3 :=
  BealPosCubeAddTwoCubeResidual_iff_no_primitive_odd

example {α β γ : ℕ} (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ)
    (hgcd : Nat.gcd α (Nat.gcd β γ) = 1)
    (heq : α ^ 3 + 2 * β ^ 3 = γ ^ 3) :
    (∃ t s τ : ℕ, 0 < t ∧ 0 < s ∧ t ^ 3 < τ ∧
        Nat.Coprime t s ∧ Odd s ∧ ¬ 3 ∣ t ∧ ¬ 3 ∣ s ∧ 3 ∣ τ ∧
          α = τ - t ^ 3 ∧ γ = τ + t ^ 3 ∧ β = t * s ∧
            s ^ 3 = t ^ 6 + 3 * τ ^ 2) ∨
      ∃ k t s τ : ℕ, 0 < k ∧ 0 < t ∧ 0 < s ∧
        3 ^ (3 * k - 1) * t ^ 3 < τ ∧
          Nat.Coprime t s ∧ Odd s ∧ ¬ 3 ∣ t ∧ ¬ 3 ∣ s ∧
            k = padicValNat 3 β ∧
              α = τ - 3 ^ (3 * k - 1) * t ^ 3 ∧
                γ = τ + 3 ^ (3 * k - 1) * t ^ 3 ∧
                  β = 3 ^ k * t * s ∧
                    s ^ 3 = τ ^ 2 + (3 ^ (2 * k - 1) * t ^ 2) ^ 3 :=
  pos_cube_three_descent_dichotomy hα hβ hγ hgcd heq

example {t s τ : ℕ} (h : t ^ 3 ≤ τ) (heq : s ^ 3 = t ^ 6 + 3 * τ ^ 2) :
    (τ - t ^ 3) ^ 3 + 2 * (t * s) ^ 3 = (τ + t ^ 3) ^ 3 :=
  pos_cube_eq_of_gcd_one_params h heq

example {k t s τ : ℕ} (hk : 0 < k)
    (h : 3 ^ (3 * k - 1) * t ^ 3 ≤ τ)
    (heq : s ^ 3 = τ ^ 2 + (3 ^ (2 * k - 1) * t ^ 2) ^ 3) :
    (τ - 3 ^ (3 * k - 1) * t ^ 3) ^ 3 + 2 * (3 ^ k * t * s) ^ 3 =
      (τ + 3 ^ (3 * k - 1) * t ^ 3) ^ 3 :=
  pos_cube_eq_of_gcd_three_params hk h heq

example {α β γ : ℕ} (heq : α ^ 3 + 2 * β ^ 3 = γ ^ 3) :
    α ^ 3 % 13 = 0 ∧ β ^ 3 % 13 = 0 ∨
      α ^ 3 % 13 = 1 ∧ β ^ 3 % 13 = 0 ∨
        α ^ 3 % 13 = 5 ∧ β ^ 3 % 13 = 0 ∨
          α ^ 3 % 13 = 8 ∧ β ^ 3 % 13 = 0 ∨
            α ^ 3 % 13 = 12 ∧ β ^ 3 % 13 = 0 ∨
              α ^ 3 % 13 = 12 ∧ β ^ 3 % 13 = 1 ∨
                α ^ 3 % 13 = 8 ∧ β ^ 3 % 13 = 5 ∨
                  α ^ 3 % 13 = 5 ∧ β ^ 3 % 13 = 8 ∨
                    α ^ 3 % 13 = 1 ∧ β ^ 3 % 13 = 12 :=
  pos_cube_add_two_cube_mod_thirteen_classes heq

example {α β γ : ℕ} (heq : α ^ 3 + 2 * β ^ 3 = γ ^ 3) :
    α ^ 3 % 19 = 0 ∧ β ^ 3 % 19 = 0 ∨
      α ^ 3 % 19 = 1 ∧ β ^ 3 % 19 = 0 ∨
        α ^ 3 % 19 = 7 ∧ β ^ 3 % 19 = 0 ∨
          α ^ 3 % 19 = 8 ∧ β ^ 3 % 19 = 0 ∨
            α ^ 3 % 19 = 11 ∧ β ^ 3 % 19 = 0 ∨
              α ^ 3 % 19 = 12 ∧ β ^ 3 % 19 = 0 ∨
                α ^ 3 % 19 = 18 ∧ β ^ 3 % 19 = 0 ∨
                  α ^ 3 % 19 = 18 ∧ β ^ 3 % 19 = 1 ∨
                    α ^ 3 % 19 = 12 ∧ β ^ 3 % 19 = 7 ∨
                      α ^ 3 % 19 = 11 ∧ β ^ 3 % 19 = 8 ∨
                        α ^ 3 % 19 = 8 ∧ β ^ 3 % 19 = 11 ∨
                          α ^ 3 % 19 = 7 ∧ β ^ 3 % 19 = 12 ∨
                            α ^ 3 % 19 = 1 ∧ β ^ 3 % 19 = 18 :=
  pos_cube_add_two_cube_mod_nineteen_classes heq

example (hMor : BealMordellCubeAddTwoResidual) :
    BealAffineCubeAddTwoResidual :=
  BealAffineCubeAddTwoResidual_of_mordell hMor

example : affineCubeAddTwoToMordell (-1) 1 = (12, 0) :=
  affineCubeAddTwoToMordell_neg_one_one

example (hPow : BealTwoEqualEvenDiffPerfectPowerResidual) :
    BealTwoEqualEvenDiffFactorResidual :=
  BealTwoEqualEvenDiffFactorResidual_of_perfect_power hPow

example {B C A : ℤ} {k x : ℕ}
    (hk : 0 < k)
    (hpar : (Even B ∧ Odd C) ∨ (Odd B ∧ Even C))
    (hcop : Nat.Coprime B.natAbs C.natAbs)
    (heq : (C ^ k - B ^ k) * (C ^ k + B ^ k) = A ^ x) :
    ∃ u v : ℕ,
      (C ^ k - B ^ k).natAbs = u ^ x ∧
        (C ^ k + B ^ k).natAbs = v ^ x :=
  exists_signed_pow_of_diff_sum_mul_eq_pow_opposite_parity hk hpar hcop heq

example {B C : ℤ} {k : ℕ} (hcop : Nat.Coprime B.natAbs C.natAbs) :
    Nat.gcd (C ^ k - B ^ k).natAbs (C ^ k + B ^ k).natAbs ∣ 2 :=
  nat_gcd_pow_diff_sum_dvd_two hcop

example {m n : ℤ} {c e : ℕ}
    (hm0 : m ≠ 0) (hn0 : n ≠ 0) (he : 3 ≤ e)
    (heq : m ^ 2 + n ^ 2 = (c : ℤ) ^ e)
    (hform :
      (∃ v : ℕ, n.natAbs = 1 ∧ 2 * m.natAbs = v ^ e) ∨
        (∃ v : ℕ, m.natAbs = 1 ∧ 2 * n.natAbs = v ^ e)) : False :=
  not_eq_odd_two_factor_of_exp_ge_three_abs_one hm0 hn0 he heq hform

/-- `3³ + 6³ = 3⁵` is not a coprime counterexample. -/
example : (3 : ℤ) ^ 3 + 6 ^ 3 = 3 ^ 5 ∧ bealGcd 3 6 3 = 3 :=
  beal_known_noncoprime_three_six

/-- `2³ + 2³ = 2⁴` is not a coprime counterexample. -/
example : (2 : ℤ) ^ 3 + 2 ^ 3 = 2 ^ 4 ∧ bealGcd 2 2 2 = 2 :=
  beal_known_noncoprime_two_two

/-- `7³ + 7⁴ = 14³` is not a coprime counterexample. -/
example : (7 : ℤ) ^ 3 + 7 ^ 4 = 14 ^ 3 ∧ bealGcd 7 7 14 = 7 :=
  beal_known_noncoprime_seven_fourteen

/-- `2⁵ + 2⁵ = 2⁶` is not a coprime counterexample. -/
example : (2 : ℤ) ^ 5 + 2 ^ 5 = 2 ^ 6 ∧ bealGcd 2 2 2 = 2 :=
  beal_known_noncoprime_two_five

example :
    isCoprimeBeal 3 6 3 3 3 5 = false ∧
      isCoprimeBeal 2 2 2 3 3 4 = false ∧
        isCoprimeBeal 7 7 14 3 4 3 = false ∧
          isCoprimeBeal 2 2 2 5 5 6 = false :=
  known_noncoprime_not_isCoprimeBeal

example : isNthPower (3 ^ 3 + 6 ^ 3) 5 = true :=
  beal_known_noncoprime_is_perfect_power


example {A B C : ℤ} {x y z : ℕ}
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hgcd : bealGcd A B C = 1)
    (hsol : A ^ x + B ^ y = C ^ z) :
    Nat.Coprime A.natAbs B.natAbs ∧
      Nat.Coprime A.natAbs C.natAbs ∧
        Nat.Coprime B.natAbs C.natAbs :=
  beal_pairwise_coprime hA hB hC hx hy hz hgcd hsol


example {N : ℕ} [NeZero N] : IsEmpty (ModularAmplificationWitness N 3) :=
  modularWitness_empty_of_eq_three

example {x y z : ℕ} (hm : bealMinExp x y z = 3) : bealAmpExp x y z = 4 :=
  bealAmpExp_eq_four_of_minExp_eq_three hm


example (M : ℝ) : ∃ (n : ℤ) (hn : n ≠ 0), M < integerHeight n hn :=
  exists_integerHeight_gt M


example : ¬ AbcAdmissibleBridge :=
  AbcAdmissibleBridge_false

example (hbridge : AbcModularBridge) :
    ∀ (ε : ℝ), 0 < ε →
      ∃ C : ℝ, 0 < C ∧
        ∀ (a b c : ℕ), IsAbcTriple a b c →
          (c : ℝ) ≤ C * (abcRadical (a * b * c) : ℝ) ^ (1 + ε) :=
  abc_conjecture_of_modular_bridge hbridge

example {N k : ℕ} [NeZero N] (t : DiscreteTorsion N) (hp : IsPureBoostSeed t) :
    windingTotal k t ≠ 0 ↔ N ≤ k * (t.n 0).val :=
  windingTotal_pureBoost_ne_zero_iff k t hp

example {a b c : ℕ} (h : IsAbcTriple a b c) :
    abcRadical (a * b * c) = abcRadical a * abcRadical b * abcRadical c :=
  isAbcTriple_radical_mul h

example {a b c : ℕ} (h : IsAbcTriple a b c)
    (hadm : IsAdmissibleContinuous (abcMismatchParams a b c)) :
    (c : ℝ) ≤ Real.exp (Real.pi / 4) * (abcRadical (a * b * c) : ℝ) ∧
      abcHeight a b c ≤ 1 / 3 :=
  ⟨abc_c_le_exp_mul_radical_of_admissible h hadm,
    abcHeight_le_one_third_of_admissible h hadm⟩

example {a b c : ℕ} (h : IsAbcTriple a b c) (hc : c ≤ 80) :
    abcLogGap a b c < Real.pi / 4 :=
  abc_logGap_lt_pi_div_four_of_le_eighty h hc

example : Real.pi / 4 < abcLogGap 1 80 81 ∧ abcHeight 1 80 81 < 1 :=
  ⟨pi_div_four_lt_abcLogGap_one_eighty, abcHeight_lt_one_one_eighty⟩

example : 1 < abcHeight 3 125 128 ∧
    ¬ IsAdmissibleContinuous (abcMismatchParams 3 125 128) :=
  ⟨one_lt_abcHeight_three_one_two_five, not_admissible_abc_three_one_two_five⟩

example :
    IsAdmissibleContinuous (abcMismatchParams 1 8 9) ∧
      ¬ IsAdmissibleContinuous (abcTriplePacket 1 8 9) ∧
      (∀ δ : ℝ, IsAdmissibleContinuous (abcLabelPacket δ) ↔
        IsAdmissibleContinuous (pureBoost (18 * δ))) ∧
      JNormalized (abcLabelPacket (Real.pi / 36)) = 98 / 243 :=
  ⟨isAdmissibleContinuous_abc_one_eight_nine,
    not_admissible_abcTriplePacket_one_eight_nine,
    isAdmissibleContinuous_abcLabelPacket_iff_heaviest,
    JNormalized_abcLabelPacket_wall⟩

/-! ## DST / discrete-companion algebraic core -/

example : pseudoscalar * pseudoscalar = (-1 : PGA) :=
  pseudoscalar_sq

example (v : Fin 4 → ℝ) :
    dual (minkowskiVector v) * dual (minkowskiVector v) =
      minkowskiVector v * minkowskiVector v :=
  dual_minkowskiVector_sq v

example :
    ∃ p : TorsionParams,
      omegaTorsionGeneratorKilling p ≠
        8 * ∑ a : Fin 3, (p.alpha a ^ 2 - p.beta a ^ 2) :=
  paper_appendix_killing_coeff_false

example (a : Fin 3) : commutator (hyperbolic a) (cyclic a) = 0 :=
  commutator_hyperbolic_cyclic_same a

example : commutator (hyperbolic 0) (cyclic 1) ≠ 0 :=
  commutator_hyperbolic0_cyclic1_ne_zero

example {x y : PGA} (hx : x ∈ lorentzSpan) (hy : y ∈ lorentzSpan) :
    commutator x y ∈ lorentzSpan :=
  commutator_mem_lorentzSpan hx hy

example {x y : PGA} (hx : x ∈ poincareSpan) (hy : y ∈ nullSpan) :
    commutator x y ∈ nullSpan ∧ commutator x y ∈ poincareSpan :=
  ⟨commutator_poincare_null_mem_nullSpan hx hy,
    commutator_mem_poincareSpan hx (LorentzLie.nullSpan_le_poincareSpan hy)⟩

example (a b : Fin 3) (p : TorsionParams) :
    hyperbolic a = dual (cyclic a) ∧
      commutator (hyperbolic a) (hyperbolic b) = -commutator (cyclic a) (cyclic b) ∧
        dual (omegaTorsion p) = omegaTorsion (dualParams p) ∧
          J (dualParams p) = -J p :=
  ⟨hyperbolic_eq_dual_cyclic a, commutator_hyperbolic_hyperbolic_eq_neg a b,
    dual_omegaTorsion p, J_dualParams p⟩

example {N : ℕ} [NeZero N] (t : DiscreteTorsion N) :
    IsAdmissible t ↔ IsAdmissibleContinuous (toTorsionParams t) :=
  isAdmissible_iff_admissibleContinuous t

example (p : TorsionParams) (h : IsAdmissibleContinuous p) :
    |JNormalized p| ≤ 1 :=
  torsion_bound_continuous p h

example (p : TorsionParams) (h : IsAdmissibleContinuous p) :
    |J p| ≤ 3 * Real.pi ^ 2 / 8 :=
  torsion_bound_raw_continuous_pi_sq p h

example (p : TorsionParams) (h : IsAdmissibleContinuous p) :
    |JNormalized p| = 1 ↔ IsPureHyperbolic p ∨ IsPureElliptic p :=
  abs_JNormalized_eq_one_iff p h

example (y : ℝ) (hy : |y| ≤ 1) :
    ∃ p : TorsionParams, IsAdmissibleContinuous p ∧ JNormalized p = y :=
  exists_admissible_JNormalized y hy

example : ∃ p : TorsionParams, IsPrincipalBranch p ∧ 1 < |J p| :=
  torsion_bound_naive_false

example (p : TorsionParams) (h : IsAdmissibleContinuous p) :
    massNormalized p ≤ 1 :=
  massNormalized_bound_continuous p h

/-- The paper step “`J = 0` ⇒ vacuum” is false. -/
example :
    ∃ p : TorsionParams,
      IsAdmissibleContinuous p ∧ JNormalized p = 0 ∧ 0 < mass p :=
  JNormalized_zero_not_implies_vacuum

/-- Finite; not an integer-order unit group. -/
example {N : ℕ} [NeZero N] : (DiscreteRotorImage N).Finite :=
  discreteRotorImage_finite

example {p : TorsionParams} (h : IsAdmissibleContinuous p) {ε : ℝ} (hε : 0 < ε) :
    ∃ (N : ℕ) (_ : NeZero N),
      ∃ t : DiscreteTorsion N, IsAdmissible t ∧
        |J p - J (toTorsionParams t)| < ε :=
  exists_discrete_approx_J h hε

example {y ε : ℝ} (hy : |y| ≤ 1) (hε : 0 < ε) :
    ∃ (N : ℕ) (_ : NeZero N),
      ∃ t : DiscreteTorsion N, IsAdmissible t ∧
        |JNormalized (toTorsionParams t) - y| < ε :=
  dense_discrete_JNormalized hy hε

example : JNormalized (toTorsionParams (pureHyperbolicDiscrete 4)) = 1 :=
  JNormalized_pureHyperbolicDiscrete (by decide : 4 ∣ 4)

example : JNormalized (toTorsionParams (pureEllipticDiscrete 4)) = -1 :=
  JNormalized_pureEllipticDiscrete (by decide : 4 ∣ 4)

example (t : DiscreteTorsion 3) (h : IsAdmissible t) :
    |JNormalized (toTorsionParams t)| < 1 :=
  torsion_bound_discrete_strict (by decide : ¬ 4 ∣ 3) t h

example (a : Fin 3) (θ : ℝ) (k : ℤ) :
    NormedSpace.exp ((θ + 2 * Real.pi * k) • cyclic a) =
      NormedSpace.exp (θ • cyclic a) :=
  exp_cyclic_add_int_mul_two_pi a θ k

example (a : Fin 3) (θ : ℝ) :
    NormedSpace.exp ((θ + 2 * Real.pi) • hyperbolic a) ≠
      NormedSpace.exp (θ • hyperbolic a) :=
  exp_hyperbolic_add_two_pi_ne a θ

example {N : ℕ} [NeZero N] : Fintype.card (DiscreteTorsion N) = N ^ 6 :=
  card_discreteTorsion

example {N : ℕ} [NeZero N] (t : DiscreteTorsion N) (a : Fin 3) :
    0 ≤ (toTorsionParams t).alpha a ∧ (toTorsionParams t).alpha a < 2 * Real.pi :=
  ⟨toTorsionParams_alpha_nonneg t a, toTorsionParams_alpha_lt_two_pi t a⟩

example (t : DiscreteTorsion 3) (h : IsAdmissible t) :
    JNormalized (toTorsionParams t) = 0 :=
  JNormalized_eq_zero_of_lt_four (by decide : 3 < 4) t h

example : ∃ t : DiscreteTorsion 8, IsAdmissible t ∧ latticeMismatch t = 0 ∧
    0 < mass (toTorsionParams t) :=
  exists_admissible_balanced_massive (by decide : 8 ≤ 8)

example {N : ℕ} [NeZero N] :
    AdmissibleRotorImage N ⊆ DiscreteRotorImage N ∧ (AdmissibleRotorImage N).Finite :=
  ⟨admissibleRotorImage_subset_discrete, admissibleRotorImage_finite⟩

example {N : ℕ} [NeZero N] (t : DiscreteTorsion N) (h : IsAdmissible t) :
    massNormalized (toTorsionParams t) ≤ ((4 * (N / 4 : ℕ) : ℝ) / N) ^ 2 :=
  massNormalized_discrete_sharp t h

example {N : ℕ} [NeZero N] :
    Fintype.card (AdmissibleClass N) = triangleNum (N / 4) ^ 3 :=
  card_admissibleClass

example : Fintype.card (AdmissibleClass 4) = 27 :=
  card_admissibleClass_four

example : Fintype.card (AdmissibleClass 8) = 216 :=
  card_admissibleClass_eight

example : ∃ t : DiscreteTorsion 8, IsAdmissible t ∧
    |JNormalized (toTorsionParams t)| = (16 : ℝ) / (3 * (8 : ℝ) ^ 2) :=
  torsion_gap_attained (by decide : 4 ≤ 8)

example : (10 : ℤ) ∉ threeMismatchSet 2 ∧ (11 : ℤ) ∉ threeMismatchSet 2 :=
  ⟨ten_not_mem_threeMismatchSet_two, eleven_not_mem_threeMismatchSet_two⟩

example : threeMismatchSet 2 ⊂ mismatchInterval 2 :=
  threeMismatchSet_proper_subset_interval_two

example {N : ℕ} [NeZero N] (t : DiscreteTorsion N) (h : IsAdmissible t) :
    |JNormalized (toTorsionParams t)| = ((4 * (N / 4 : ℕ) : ℝ) / N) ^ 2 ↔
      (∀ a, (t.n a).val = N / 4 ∧ (t.m a).val = 0) ∨
        (∀ a, (t.n a).val = 0 ∧ (t.m a).val = N / 4) :=
  JNormalized_eq_sharp_iff t h

example :
    axisMass 2 0 + axisMass 2 0 + axisMass 0 2 = 3 * 2 ^ 2 ∧
      |axisMismatch 2 0 + axisMismatch 2 0 + axisMismatch 0 2| < 3 * (2 : ℤ) ^ 2 :=
  mixed_wall_mass_ceiling_not_torsion (by decide : 1 ≤ 2)

example {N : ℕ} [NeZero N] (t : DiscreteTorsion N) :
    |latticeMismatch t| ≤ (latticeMass t : ℤ) ∧
      latticeMismatch t ≡ (latticeMass t : ℤ) [ZMOD 2] :=
  ⟨abs_latticeMismatch_le_latticeMass t, latticeMismatch_modEq_latticeMass t⟩

example : ∃ t : DiscreteTorsion 8, IsAdmissible t ∧ latticeMismatch t = 0 ∧
    0 < latticeMass t ∧ ¬ (∀ a, t.n a = t.m a) :=
  exists_unbalanced_zeroHeight_massive (by decide : 4 ≤ 8)

example : (1 / 2 + 1) ^ 3 < (zeroHeightTriples 1).card :=
  card_zeroHeight_gt_balanced (by decide : 1 ≤ 1)

example : (zeroHeightTriples 2).card = 32 :=
  zeroHeight_card_two

/-- Distinct axes need not commute. This does not decide the exponential image. -/
example : commutator (hyperbolic 0) (cyclic 1) ≠ 0 :=
  commutator_hyperbolic0_cyclic1_ne_zero

/-! ### Algebraic sandwich surface (Gravity intentionally out of scope) -/

example (m n v : PGA) :
    sandwich (m * n) v = sandwich m (sandwich n v) :=
  sandwich_comp m n v

example (φ : ℝ) :
    sandwich (rotorTorsion (pureBoost φ)) (ι 2) = ι 2 :=
  sandwich_pureBoost_ι2 φ

example (φ : ℝ) :
    sandwich (rotorTorsion (pureBoost φ)) (ι 0 + ι 1) =
      Real.exp φ • (ι 0 + ι 1) :=
  sandwich_pureBoost_lightlike_plus φ

example (φ : ℝ) :
    sandwich (rotorTorsion (pureBoost φ)) (ι 0 - ι 1) =
      Real.exp (-φ) • (ι 0 - ι 1) :=
  sandwich_pureBoost_lightlike_minus φ

example (θ : ℝ) :
    sandwich (rotorTorsion (pureRotation1 θ)) (null 3) =
      Real.sin θ • null 1 + Real.cos θ • null 3 :=
  sandwich_pureRotation1_null3 θ

/-! ### Group-level motor structure (`MotorGroup`) -/

example {W : Submodule ℝ PGA} {Ω : PGA} (hΩ : reverse Ω = -Ω)
    (hW : ∀ y ∈ W, commutator Ω y ∈ W) {x : PGA} (hx : x ∈ W) :
    sandwich (NormedSpace.exp Ω) x ∈ W :=
  sandwich_exp_mem hΩ hW hx

example {Ω : PGA} (hΩ : reverse Ω = -Ω) (t : ℝ) (x : PGA) :
    sandwich (NormedSpace.exp (t • Ω)) x =
      NormedSpace.exp (t • adL Ω) x :=
  sandwich_exp_smul_eq_exp_ad hΩ t x

example (t : TorsionParams) {x : PGA} (hx : x ∈ nullSpan) :
    sandwich (rotorTorsion t) x ∈ nullSpan :=
  sandwich_rotorTorsion_mem_nullSpan t hx

example (t : TorsionParams) {x : PGA} (hx : x ∈ poincareSpan) :
    sandwich (rotorTorsion t) x ∈ poincareSpan :=
  sandwich_rotorTorsion_mem_poincareSpan t hx

example (t : TorsionParams) (p : TransParams) :
    ∃ q : TransParams, sandwich (rotorTorsion t) (expTrans p) = expTrans q :=
  exists_sandwich_rotorTorsion_expTrans t p

example {m : PGA} (hm : m * reverse m = 1) (x : PGA) :
    sandwich m (NormedSpace.exp x) = NormedSpace.exp (sandwich m x) :=
  sandwich_exp hm x

example (p q : OmegaParams) :
    ∃ r : TransParams,
      motor p * motor q = rotorTorsion p.torsion * rotorTorsion q.torsion * expTrans r :=
  exists_motor_mul p q

example (p : OmegaParams) (n : ℕ) :
    ∃ r : TransParams, motor p ^ n = rotorTorsion p.torsion ^ n * expTrans r :=
  exists_motor_pow p n

example (p : OmegaParams) :
    (∃ q : TransParams,
      NormedSpace.exp (omegaBiv p) = rotorTorsion p.torsion * expTrans q) ∧
      NormedSpace.exp (omegaBiv p) * reverse (NormedSpace.exp (omegaBiv p)) = 1 :=
  ⟨exists_exp_omegaBiv_eq_rotorTorsion_mul_expTrans p, exp_omegaBiv_unitary p⟩

example : ∃ (p : OmegaParams) (q : TransParams),
    NormedSpace.exp (omegaBiv p) = rotorTorsion p.torsion * expTrans q ∧ q ≠ p.trans :=
  exists_dressed_translation_ne

end DoubleSpacetime.FoundationRegression
