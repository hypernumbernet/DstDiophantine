import DstDiophantine.Framework.Amplification
import DstDiophantine.Framework.Representation
import DstDiophantine.Framework.Lattice
import DstDiophantine.Embedding.PowerMap
import DstDiophantine.Embedding.Height
import DstDiophantine.Embedding.RotorClass
import DstDiophantine.Embedding.ConformalInteger
import DstDiophantine.Algebra.Amplification
import DstDiophantine.Algebra.ModularAmplification
import DstDiophantine.Algebra.Invariant
import DstDiophantine.Algebra.Discrete
import DstDiophantine.Theorems.Fermat
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Phase 5–7: Beal's conjecture (problem-specific layer)

Amplification vs. admissible bound with minimal exponent `m = min(x,y,z)`,
together with the faithful null-translator encoding of `A^x + B^y - C^z`.
Shared no-go theorems come from `Framework.Amplification` (not from Fermat).

## Paper gap (not closed)

Classical Beal is **not** claimed unconditionally. The live programme splits the
old modular payload into:

* `BealWindingBridge` — solution ⇒ quantised fractional gap carries a
  `ModularAmplificationWitness` (number-theoretic half);
* `BealCGAGauge` / `BealCGANoGo` — CGA fractional-power embedding and residual
  geometric no-go (not identified with the PGA real-scale cone).

The legacy `BealModularBridge` (witness + `ConformalGaugeAdmissible`) is
**diagnostic only**: those conjuncts are equation-independently incompatible
(`beal_modular_payload_incompatible`). Continuous `BealAdmissibleBridge` remains
diagnostic (balanced seeds sit below `1/m²`).

Unbalanced-window construction: for `m ≥ 4` and
`2π/m ≤ δ < 5π/(2m)`, a positive solution yields a modular winding witness
unconditionally (`beal_modularWitness_of_fracGap_window`).
-/

namespace DstDiophantine

namespace Theorems

open Amplification Discrete Invariant Real ModularAmplification Framework
open _root_.DstDiophantine.Embedding
open _root_.DstDiophantine.Framework
open _root_.DstDiophantine.CGA
open CliffordAlgebra

/-! ### Additive sector -/

theorem beal_solution_iff_motor (A B C : ℤ) (x y z : ℕ) :
    A ^ x + B ^ y = C ^ z ↔ powerSumMotor (bealEquation A B C x y z) = 1 :=
  (bealMotor_one_iff A B C x y z).symm

/-! ### Minimal exponent -/

/-- Amplification factor used in Chapter 6: `m = min(x,y,z)`. -/
def bealMinExp (x y z : ℕ) : ℕ :=
  min x (min y z)

theorem bealMinExp_le_left (x y z : ℕ) : bealMinExp x y z ≤ x :=
  min_le_left _ _

theorem bealMinExp_le_mid (x y z : ℕ) : bealMinExp x y z ≤ y :=
  le_trans (min_le_right _ _) (min_le_left _ _)

theorem bealMinExp_le_right (x y z : ℕ) : bealMinExp x y z ≤ z :=
  le_trans (min_le_right _ _) (min_le_right _ _)

theorem bealMinExp_ge_three {x y z : ℕ} (hx : 3 ≤ x) (hy : 3 ≤ y) (hz : 3 ≤ z) :
    3 ≤ bealMinExp x y z :=
  le_min hx (le_min hy hz)

theorem bealMinExp_ge_one {x y z : ℕ} (hx : 3 ≤ x) (hy : 3 ≤ y) (hz : 3 ≤ z) :
    1 ≤ bealMinExp x y z :=
  Nat.le_trans (by decide : 1 ≤ 3) (bealMinExp_ge_three hx hy hz)

theorem bealMinExp_pos {x y z : ℕ} (hx : 3 ≤ x) (hy : 3 ≤ y) (hz : 3 ≤ z) :
    0 < bealMinExp x y z :=
  Nat.zero_lt_of_lt (bealMinExp_ge_one hx hy hz)

/-- Three-way gcd on absolute values (classical Beal coprimality). -/
def bealGcd (A B C : ℤ) : ℕ :=
  Nat.gcd A.natAbs (Nat.gcd B.natAbs C.natAbs)

theorem bealGcd_pos {A B C : ℤ} (hA : A ≠ 0) : 0 < bealGcd A B C :=
  Nat.gcd_pos_of_pos_left _ (Int.natAbs_pos.mpr hA)

theorem bealGcd_dvd_left (A B C : ℤ) : bealGcd A B C ∣ A.natAbs :=
  Nat.gcd_dvd_left _ _

theorem bealGcd_dvd_mid (A B C : ℤ) : bealGcd A B C ∣ B.natAbs :=
  Nat.dvd_trans (Nat.gcd_dvd_right A.natAbs _) (Nat.gcd_dvd_left B.natAbs C.natAbs)

theorem bealGcd_dvd_right (A B C : ℤ) : bealGcd A B C ∣ C.natAbs :=
  Nat.dvd_trans (Nat.gcd_dvd_right A.natAbs _) (Nat.gcd_dvd_right B.natAbs C.natAbs)

/-- Classical Beal conclusion shape: a common prime factor of `|A|,|B|,|C|`. -/
theorem exists_common_prime_of_bealGcd_gt_one {A B C : ℤ}
    (h : 1 < bealGcd A B C) :
    ∃ p : ℕ, Nat.Prime p ∧ p ∣ A.natAbs ∧ p ∣ B.natAbs ∧ p ∣ C.natAbs := by
  obtain ⟨p, hp, hdiv⟩ := Nat.exists_prime_and_dvd (ne_of_gt h)
  refine ⟨p, hp, ?_, ?_, ?_⟩
  · exact Nat.dvd_trans hdiv (bealGcd_dvd_left A B C)
  · exact Nat.dvd_trans hdiv (bealGcd_dvd_mid A B C)
  · exact Nat.dvd_trans hdiv (bealGcd_dvd_right A B C)

/-! ### Fractional-power log gap (magnitude layer; no BCH) -/

/--
Fractional log-gap used as the Beal modular seed:
`δ = (z/m) log|C| − (x/m) log|A|`.
When `m = bealMinExp x y z` and `A^x + B^y = C^z` with positive terms,
`m · δ = log(1 + B^y / A^x)`.
-/
noncomputable def bealFracLogGap (A C : ℤ) (x z m : ℕ) : ℝ :=
  (z : ℝ) / m * Real.log (Int.natAbs C) - (x : ℝ) / m * Real.log (Int.natAbs A)

theorem bealFracLogGap_mul (A C : ℤ) (x z m : ℕ) (hm : m ≠ 0) :
    (m : ℝ) * bealFracLogGap A C x z m =
      (z : ℝ) * Real.log (Int.natAbs C) - (x : ℝ) * Real.log (Int.natAbs A) := by
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm
  unfold bealFracLogGap
  field_simp [hm0]

/-- Positive Beal solutions satisfy `A^x < C^z`. -/
theorem beal_pos_pow_lt {A B C : ℤ} {x y z : ℕ}
    (_hA : 0 < A) (hB : 0 < B) (_hC : 0 < C)
    (hsol : A ^ x + B ^ y = C ^ z) : A ^ x < C ^ z := by
  have hBy : 0 < B ^ y := pow_pos hB y
  have hlt : A ^ x < A ^ x + B ^ y := lt_add_of_pos_right _ hBy
  rwa [hsol] at hlt

theorem bealFracLogGap_eq_log_div (A C : ℤ) (x z m : ℕ) (hm : m ≠ 0)
    (hA : 0 < A) (hC : 0 < C) :
    bealFracLogGap A C x z m =
      (1 / (m : ℝ)) *
        Real.log ((C.natAbs : ℝ) ^ z / (A.natAbs : ℝ) ^ x) := by
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm
  have hAabs : (0 : ℝ) < (A.natAbs : ℝ) :=
    Nat.cast_pos.mpr (Int.natAbs_pos.mpr hA.ne')
  have hCabs : (0 : ℝ) < (C.natAbs : ℝ) :=
    Nat.cast_pos.mpr (Int.natAbs_pos.mpr hC.ne')
  have hApow : (0 : ℝ) < (A.natAbs : ℝ) ^ x := pow_pos hAabs _
  have hCpow : (0 : ℝ) < (C.natAbs : ℝ) ^ z := pow_pos hCabs _
  have hlog :
      Real.log ((C.natAbs : ℝ) ^ z / (A.natAbs : ℝ) ^ x) =
        (z : ℝ) * Real.log (C.natAbs : ℝ) - (x : ℝ) * Real.log (A.natAbs : ℝ) := by
    rw [Real.log_div (ne_of_gt hCpow) (ne_of_gt hApow), Real.log_pow, Real.log_pow]
  have hmul := bealFracLogGap_mul A C x z m hm
  have hmul' :
      (m : ℝ) * bealFracLogGap A C x z m =
        (z : ℝ) * Real.log (C.natAbs : ℝ) - (x : ℝ) * Real.log (A.natAbs : ℝ) := by
    simpa using hmul
  have hgap :
      bealFracLogGap A C x z m =
        (1 / (m : ℝ)) *
          ((z : ℝ) * Real.log (C.natAbs : ℝ) - (x : ℝ) * Real.log (A.natAbs : ℝ)) := by
    field_simp [hm0] at hmul' ⊢
    linarith [hmul']
  rw [hgap, hlog]

/-- On a positive Beal solution, m · δ = log(1 + B^y / A^x). -/
theorem bealFracLogGap_of_solution {A B C : ℤ} {x y z m : ℕ} (hm : m ≠ 0)
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (hsol : A ^ x + B ^ y = C ^ z) :
    (m : ℝ) * bealFracLogGap A C x z m =
      Real.log (1 + (B : ℝ) ^ y / (A : ℝ) ^ x) := by
  have hAposR : (0 : ℝ) < A := Int.cast_pos.mpr hA
  have hApow : (0 : ℝ) < (A : ℝ) ^ x := pow_pos hAposR _
  have hsolR : (A : ℝ) ^ x + (B : ℝ) ^ y = (C : ℝ) ^ z := by exact_mod_cast hsol
  have hAn : (A.natAbs : ℝ) = (A : ℝ) := by
    rw [← Int.cast_natCast A.natAbs, Int.natAbs_of_nonneg hA.le]
  have hCn : (C.natAbs : ℝ) = (C : ℝ) := by
    rw [← Int.cast_natCast C.natAbs, Int.natAbs_of_nonneg hC.le]
  have hratio : (C.natAbs : ℝ) ^ z / (A.natAbs : ℝ) ^ x =
      1 + (B : ℝ) ^ y / (A : ℝ) ^ x := by
    calc (C.natAbs : ℝ) ^ z / (A.natAbs : ℝ) ^ x
        = (C : ℝ) ^ z / (A : ℝ) ^ x := by rw [hAn, hCn]
      _ = ((A : ℝ) ^ x + (B : ℝ) ^ y) / (A : ℝ) ^ x := by rw [← hsolR]
      _ = 1 + (B : ℝ) ^ y / (A : ℝ) ^ x := by field_simp [ne_of_gt hApow]
  have hgap := bealFracLogGap_eq_log_div A C x z m hm hA hC
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm
  calc (m : ℝ) * bealFracLogGap A C x z m
      = (m : ℝ) * ((1 / (m : ℝ)) *
          Real.log ((C.natAbs : ℝ) ^ z / (A.natAbs : ℝ) ^ x)) := by rw [hgap]
    _ = Real.log ((C.natAbs : ℝ) ^ z / (A.natAbs : ℝ) ^ x) := by field_simp [hm0]
    _ = Real.log (1 + (B : ℝ) ^ y / (A : ℝ) ^ x) := by rw [hratio]

/-- Equal exponents specialise the fractional gap to `log|C| − log|A|`. -/
theorem bealFracLogGap_eq_exp (A C : ℤ) (p : ℕ) (hp : p ≠ 0) :
    bealFracLogGap A C p p p =
      Real.log (Int.natAbs C) - Real.log (Int.natAbs A) := by
  have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp
  unfold bealFracLogGap
  field_simp [hp0]

/-- On a positive Beal solution, `δ = log(1 + B^y / A^x) / m`. -/
theorem bealFracLogGap_eq_log_one_add_div {A B C : ℤ} {x y z m : ℕ} (hm : m ≠ 0)
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (hsol : A ^ x + B ^ y = C ^ z) :
    bealFracLogGap A C x z m =
      Real.log (1 + (B : ℝ) ^ y / (A : ℝ) ^ x) / (m : ℝ) := by
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm
  have hmul := bealFracLogGap_of_solution hm hA hB hC hsol
  field_simp [hm0] at hmul ⊢
  linarith [hmul]

/-- Positive Beal solutions have strictly positive fractional log-gap. -/
theorem bealFracLogGap_pos_of_solution {A B C : ℤ} {x y z m : ℕ} (hm : m ≠ 0)
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (hsol : A ^ x + B ^ y = C ^ z) :
    0 < bealFracLogGap A C x z m := by
  have hAposR : (0 : ℝ) < A := Int.cast_pos.mpr hA
  have hBposR : (0 : ℝ) < B := Int.cast_pos.mpr hB
  have hApow : (0 : ℝ) < (A : ℝ) ^ x := pow_pos hAposR _
  have hBpow : (0 : ℝ) < (B : ℝ) ^ y := pow_pos hBposR _
  have hratio : (0 : ℝ) < (B : ℝ) ^ y / (A : ℝ) ^ x := div_pos hBpow hApow
  have hone : (1 : ℝ) < 1 + (B : ℝ) ^ y / (A : ℝ) ^ x := by linarith
  have hlog : 0 < Real.log (1 + (B : ℝ) ^ y / (A : ℝ) ^ x) := Real.log_pos hone
  have hmpos : (0 : ℝ) < m := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm)
  rw [bealFracLogGap_eq_log_one_add_div hm hA hB hC hsol]
  exact div_pos hlog hmpos

/-- Winding threshold sits strictly above the continuous seed cone when `m = 3`. -/
theorem beal_winding_threshold_gt_half_pi_of_minExp_eq_three
    {x y z : ℕ} (hm : bealMinExp x y z = 3) :
    Real.pi / 2 < 2 * Real.pi / (bealMinExp x y z : ℝ) := by
  rw [hm]
  nlinarith [Real.pi_pos]

/-- Balanced model gap `log 2 / m` misses the modular winding threshold `2π / m`. -/
theorem beal_balanced_fracGap_lt_winding_threshold {m : ℕ} (hm : 0 < m) :
    Real.log 2 / (m : ℝ) < 2 * Real.pi / (m : ℝ) := by
  have hm0 : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hlog : Real.log 2 < 2 * Real.pi := by
    have h1 : Real.log 2 < 1 := by
      have h := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) (by norm_num)
      norm_num at h ⊢
      exact h
    have h2 : (1 : ℝ) < 2 * Real.pi := by nlinarith [Real.pi_gt_three]
    exact h1.trans h2
  exact div_lt_div_of_pos_right hlog hm0

/-! ### Amplification vs admissible bound -/

/-- Chapter 6 core: a seed taller than `1/m²` cannot amplify inside the admissible bound. -/
theorem beal_amplification_contradiction
    {A C : ℤ} (hA : A ≠ 0) (hC : C ≠ 0) {x y z : ℕ}
    (hx : 3 ≤ x) (hy : 3 ≤ y) (hz : 3 ≤ z)
    (hadm :
      IsAdmissibleContinuous
        (pureBoost
          ((bealMinExp x y z : ℝ) *
            (Real.log (Int.natAbs C) - Real.log (Int.natAbs A)))))
    (hbig :
      (1 : ℝ) / (bealMinExp x y z : ℝ) ^ 2 <
        |JNormalized (logMismatch A C hA hC)|) :
    False := by
  have hm1 : 1 ≤ bealMinExp x y z := bealMinExp_ge_one hx hy hz
  change (1 : ℝ) / (_ : ℝ) ^ 2 < |JNormalized (pureBoost _)| at hbig
  exact continuous_amplification_contradiction _ hm1 hadm hbig

/-- Discrete torus form via the shared amplification core. -/
theorem beal_discrete_amplification_contradiction {N : ℕ} [NeZero N] {x y z : ℕ}
    (hx : 3 ≤ x) (hy : 3 ≤ y) (hz : 3 ≤ z)
    (t : AdmissibleClass N)
    (hlb :
      (1 : ℝ) / (bealMinExp x y z : ℝ) ^ 2 <
        torsionHeight (AdmissibleClass.toParams t))
    (hadm :
      IsAdmissibleContinuous
        (scaleTorsion (bealMinExp x y z : ℝ) (AdmissibleClass.toParams t))) :
    False := by
  have hm1 : 1 ≤ bealMinExp x y z := bealMinExp_ge_one hx hy hz
  exact discrete_amplification_contradiction hm1 t hlb hadm

/-! ### Continuous bridge (diagnostic) -/

/--
Continuous Beal amplification bridge (**diagnostic**).

* **Assumption (unproved):** a coprime Beal solution yields an admissible powered
  pure-boost mismatch whose seed already exceeds `1/m²`.
* **Proved core:** `beal_amplification_contradiction` /
  `continuous_amplification_contradiction`.
* **Obstruction:** at the balanced scale `θ = log 2 / m` the seed is below
  `1/m²` (`beal_balanced_seed_lt_threshold`).
* **Live programme:** `BealModularBridge` (solution-dependent modular payload).
* **Does not claim:** unconditional classical Beal.
-/
def BealAdmissibleBridge : Prop :=
  ∀ (A B C : ℤ) (x y z : ℕ) (_hx : 3 ≤ x) (_hy : 3 ≤ y) (_hz : 3 ≤ z)
    (hA : A ≠ 0) (_hB : B ≠ 0) (hC : C ≠ 0),
    bealGcd A B C = 1 →
    A ^ x + B ^ y = C ^ z →
      IsAdmissibleContinuous
          (pureBoost
            ((bealMinExp x y z : ℝ) *
              (Real.log (Int.natAbs C) - Real.log (Int.natAbs A)))) ∧
        (1 : ℝ) / (bealMinExp x y z : ℝ) ^ 2 <
          |JNormalized (logMismatch A C hA hC)|

/-- Conditional DST recovery of Beal's conjecture (common prime factor). -/
theorem beal_conjecture_of_bridge (hbridge : BealAdmissibleBridge) :
    ∀ (A B C : ℤ) (x y z : ℕ),
      3 ≤ x → 3 ≤ y → 3 ≤ z →
      A ≠ 0 → B ≠ 0 → C ≠ 0 →
      A ^ x + B ^ y = C ^ z →
      1 < bealGcd A B C := by
  intro A B C x y z hx hy hz hA hB hC hsol
  by_contra hnot
  have hle : bealGcd A B C ≤ 1 := Nat.not_lt.mp hnot
  have hpos : 0 < bealGcd A B C := bealGcd_pos hA
  have hcoprime : bealGcd A B C = 1 := le_antisymm hle (Nat.succ_le_of_lt hpos)
  have ⟨hadm, hbig⟩ := hbridge A B C x y z hx hy hz hA hB hC hcoprime hsol
  exact beal_amplification_contradiction hA hC hx hy hz hadm hbig

/-! ### Balanced-seed diagnostic (continuous obstruction) -/

/-- At `θ = log 2 / m`, the seed height is below the continuous Beal threshold. -/
theorem beal_balanced_seed_lt_threshold {x y z : ℕ}
    (hx : 3 ≤ x) (hy : 3 ≤ y) (hz : 3 ≤ z) :
    |JNormalized (pureBoost (Real.log 2 / (bealMinExp x y z : ℝ)))| <
      (1 : ℝ) / (bealMinExp x y z : ℝ) ^ 2 :=
  fermat_balanced_seed_lt_threshold (bealMinExp_ge_one hx hy hz)

/-- Balanced seed remains admissible after `m`-fold amplification. -/
theorem beal_balanced_amplification_admissible {x y z : ℕ}
    (hx : 3 ≤ x) (hy : 3 ≤ y) (hz : 3 ≤ z) :
    IsAdmissibleContinuous
      (pureBoost
        ((bealMinExp x y z : ℝ) *
          (Real.log 2 / (bealMinExp x y z : ℝ)))) :=
  fermat_balanced_amplification_admissible (bealMinExp_ge_one hx hy hz)

/-! ### Equal-exponent recovery toward FLT -/

/-- Equal exponents specialise Beal's additive motor to Fermat's. -/
theorem beal_eq_exp_motor (A B C : ℤ) (p : ℕ) :
    powerSumMotor (bealEquation A B C p p p) =
      powerSumMotor (fermatEquation A B C p) := by
  rw [bealEquation_eq_fermat]

/--
Under the continuous Beal bridge, an equal-exponent solution with `p ≥ 3` cannot
be primitive (`bealGcd = 1`). Still conditional on the bridge.
-/
theorem beal_eq_exp_not_coprime_of_bridge (hbridge : BealAdmissibleBridge)
    (A B C : ℤ) (p : ℕ) (hp : 3 ≤ p)
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hsol : A ^ p + B ^ p = C ^ p) :
    1 < bealGcd A B C :=
  beal_conjecture_of_bridge hbridge A B C p p p hp hp hp hA hB hC hsol

/-! ### Quantised fractional gap -/

/-- Quantise the Beal fractional log-gap to a pure-boost lattice seed. -/
noncomputable def quantizeBealMismatch (N : ℕ) [NeZero N] (A C : ℤ) (x z m : ℕ) :
    DiscreteTorsion N :=
  pureBoostSeedOfRapidity N (bealFracLogGap A C x z m)

theorem quantizeBealMismatch_pureBoost (N : ℕ) [NeZero N] (A C : ℤ) (x z m : ℕ) :
    IsPureBoostSeed (quantizeBealMismatch N A C x z m) :=
  pureBoostSeedOfRapidity_isPureBoost N _

/-! ### Diagnostic modular bridge (payload-incompatible) -/

/--
**Diagnostic** modular Beal bridge (do not treat as the live programme).

The three conjuncts are equation-independently incompatible: a
`ModularAmplificationWitness` with nonzero winding rules out
`ConformalGaugeAdmissible` under the present PGA real-scale identification
(`beal_modular_payload_incompatible`). Live programme: `BealWindingBridge` +
`BealCGAGauge` / `BealCGANoGo`.
-/
def BealModularBridge : Prop :=
  ∀ (A B C : ℤ) (x y z : ℕ) (_hx : 3 ≤ x) (_hy : 3 ≤ y) (_hz : 3 ≤ z)
    (_hA : A ≠ 0) (_hB : B ≠ 0) (_hC : C ≠ 0),
    bealGcd A B C = 1 →
    A ^ x + B ^ y = C ^ z →
      ∃ (N : ℕ) (hN : N ≠ 0),
        letI : NeZero N := ⟨hN⟩
        let m := bealMinExp x y z
        let t := quantizeBealMismatch N A C x z m
        IsAdmissible t ∧
          (∃ w : ModularAmplificationWitness N m, w.t.val = t) ∧
            ConformalGaugeAdmissible
              (scaleTorsion (m : ℝ) (toTorsionParams t))

/-- Winding witness and PGA-identified conformal gauge cannot hold together. -/
theorem beal_modular_payload_incompatible {N k : ℕ} [NeZero N]
    (w : ModularAmplificationWitness N k) :
    ¬ ConformalGaugeAdmissible
        (scaleTorsion (k : ℝ) (toTorsionParams w.t.val)) :=
  ModularAmplificationWitness.not_admissible_real_scale w

/-- Conditional classical Beal from the diagnostic modular bridge. -/
theorem beal_conjecture_of_modular_bridge (hbridge : BealModularBridge) :
    ∀ (A B C : ℤ) (x y z : ℕ),
      3 ≤ x → 3 ≤ y → 3 ≤ z →
      A ≠ 0 → B ≠ 0 → C ≠ 0 →
      A ^ x + B ^ y = C ^ z →
      1 < bealGcd A B C := by
  intro A B C x y z hx hy hz hA hB hC hsol
  by_contra hnot
  have hle : bealGcd A B C ≤ 1 := Nat.not_lt.mp hnot
  have hpos : 0 < bealGcd A B C := bealGcd_pos hA
  have hcoprime : bealGcd A B C = 1 := le_antisymm hle (Nat.succ_le_of_lt hpos)
  obtain ⟨N, hN, _hadm, ⟨w, hw⟩, hconf⟩ :=
    hbridge A B C x y z hx hy hz hA hB hC hcoprime hsol
  let : NeZero N := ⟨hN⟩
  have hnot' := beal_modular_payload_incompatible w
  rw [hw] at hnot'
  exact hnot' hconf

/-- Equal-exponent specialisation under the diagnostic modular Beal bridge. -/
theorem beal_eq_exp_not_coprime_of_modular_bridge (hbridge : BealModularBridge)
    (A B C : ℤ) (p : ℕ) (hp : 3 ≤ p)
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hsol : A ^ p + B ^ p = C ^ p) :
    1 < bealGcd A B C :=
  beal_conjecture_of_modular_bridge hbridge A B C p p p hp hp hp hA hB hC hsol

/-! ### Partial winding on the principal interval -/

/--
If `2π/m ≤ δ < 2π` and `m ∣ N`, the quantised Beal seed has nonzero total
winding. On a positive solution this is equivalent (via
`bealFracLogGap_of_solution`) to a lower bound
`e^{2π} − 1 ≤ B^y / A^x` on the size ratio — so typical balanced models
`B^y ≈ A^x` (giving `δ = log 2 / m`) miss this principal-interval criterion.
-/
theorem beal_has_winding_of_fracGap_ge (N m : ℕ) [NeZero N] (hm : 0 < m)
    (A C : ℤ) (x z : ℕ)
    (hle : 2 * Real.pi / m ≤ bealFracLogGap A C x z m)
    (hlt : bealFracLogGap A C x z m < 2 * Real.pi)
    (hdvd : m ∣ N) :
    windingTotal m (quantizeBealMismatch N A C x z m) ≠ 0 := by
  have hπk : 0 ≤ 2 * Real.pi / m :=
    div_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) Real.pi_pos.le) (Nat.cast_nonneg _)
  have h0 : 0 ≤ bealFracLogGap A C x z m := le_trans hπk hle
  simpa [quantizeBealMismatch] using
    windingTotal_ne_zero_of_rapidity_ge
      N m hm (bealFracLogGap A C x z m) h0 hle hlt hdvd

/-! ### Live winding bridge (number-theoretic half) -/

/--
**Live** Beal winding bridge (unproved in full generality).

A coprime solution yields some lattice `N` on which the quantised fractional
gap is an admissible modular winding witness. No PGA real-scale /
`ConformalGaugeAdmissible` conjunct — that identification is the diagnostic
obstruction.
-/
def BealWindingBridge : Prop :=
  ∀ (A B C : ℤ) (x y z : ℕ) (_hx : 3 ≤ x) (_hy : 3 ≤ y) (_hz : 3 ≤ z)
    (_hA : A ≠ 0) (_hB : B ≠ 0) (_hC : C ≠ 0),
    bealGcd A B C = 1 →
    A ^ x + B ^ y = C ^ z →
      ∃ (N : ℕ) (hN : N ≠ 0),
        letI : NeZero N := ⟨hN⟩
        let m := bealMinExp x y z
        let t := quantizeBealMismatch N A C x z m
        IsAdmissible t ∧ ∃ w : ModularAmplificationWitness N m, w.t.val = t

/-! ### CGA fractional-power gauge (geometric half) -/

/-- Fractional-power magnitude `|n|^{e/m}` used as a 1D CGA null-cone seed. -/
noncomputable def bealRootMag (n : ℤ) (e m : ℕ) : ℝ :=
  (n.natAbs : ℝ) ^ ((e : ℝ) / m)

theorem bealRootMag_pos {n : ℤ} (hn : n ≠ 0) (e m : ℕ) :
    0 < bealRootMag n e m := by
  unfold bealRootMag
  exact Real.rpow_pos_of_pos (Nat.cast_pos.mpr (Int.natAbs_pos.mpr hn)) _

/-- Fractional log-gap equals the log-ratio of fractional-power magnitudes. -/
theorem bealFracLogGap_eq_log_rootMag (A C : ℤ) (x z m : ℕ) (_hm : m ≠ 0)
    (hA : A ≠ 0) (hC : C ≠ 0) :
    bealFracLogGap A C x z m =
      Real.log (bealRootMag C z m) - Real.log (bealRootMag A x m) := by
  have hAabs : (0 : ℝ) < (A.natAbs : ℝ) :=
    Nat.cast_pos.mpr (Int.natAbs_pos.mpr hA)
  have hCabs : (0 : ℝ) < (C.natAbs : ℝ) :=
    Nat.cast_pos.mpr (Int.natAbs_pos.mpr hC)
  unfold bealFracLogGap bealRootMag
  rw [Real.log_rpow hCabs, Real.log_rpow hAabs]

/--
CGA gauge for Beal fractional powers: both root-magnitudes embed as null points
in `Cl(2,1)`. **Not** identified with `IsAdmissibleContinuous` / PGA real scale.
-/
def BealCGAGauge (A C : ℤ) (x z m : ℕ) : Prop :=
  conformalPoint (bealRootMag A x m) * conformalPoint (bealRootMag A x m) = 0 ∧
    conformalPoint (bealRootMag C z m) * conformalPoint (bealRootMag C z m) = 0

theorem BealCGAGauge_of_ne_zero (A C : ℤ) (x z m : ℕ) :
    BealCGAGauge A C x z m :=
  ⟨conformalPoint_sq _, conformalPoint_sq _⟩

/-- Dilation weights `(1, e^δ, e^{2δ})` relating the two Beal CGA seeds. -/
theorem beal_cga_dilation_weights (A C : ℤ) (x z m : ℕ) (hm : m ≠ 0)
    (hA : A ≠ 0) (hC : C ≠ 0) :
    let δ := bealFracLogGap A C x z m
    let a := bealRootMag A x m
    conformalPoint (bealRootMag C z m) =
      CliffordAlgebra.ι Q21
        (CGA1.n0Vec + Real.exp δ • (a • CGA1.eLineVec)
          + (Real.exp δ) ^ 2 • ((1 / 2 * a ^ 2) • CGA1.nInfVec)) := by
  intro δ a
  have ha : 0 < a := bealRootMag_pos hA x m
  have hδ : δ = Real.log (bealRootMag C z m) - Real.log a :=
    bealFracLogGap_eq_log_rootMag A C x z m hm hA hC
  have hCpos : 0 < bealRootMag C z m := bealRootMag_pos hC z m
  have hexp : Real.exp δ * a = bealRootMag C z m := by
    rw [hδ, Real.exp_sub, Real.exp_log hCpos, Real.exp_log ha]
    field_simp [ne_of_gt ha]
  rw [← hexp, conformalPoint_smul]

/--
Residual geometric no-go (unproved): a coprime solution cannot carry a modular
winding witness once the CGA fractional-power gauge is in force.
Does **not** reuse `ConformalGaugeAdmissible` / PGA real-scale.
-/
def BealCGANoGo : Prop :=
  ∀ (A B C : ℤ) (x y z : ℕ) (_hx : 3 ≤ x) (_hy : 3 ≤ y) (_hz : 3 ≤ z)
    (_hA : A ≠ 0) (_hB : B ≠ 0) (_hC : C ≠ 0),
    bealGcd A B C = 1 →
    A ^ x + B ^ y = C ^ z →
      BealCGAGauge A C x z (bealMinExp x y z) →
        ∀ (N : ℕ) (hN : N ≠ 0),
          letI : NeZero N := ⟨hN⟩
          let m := bealMinExp x y z
          let t := quantizeBealMismatch N A C x z m
          ¬ (IsAdmissible t ∧ ∃ w : ModularAmplificationWitness N m, w.t.val = t)

/-- Conditional classical Beal from the split winding + CGA no-go bridges. -/
theorem beal_conjecture_of_winding_and_cga_nogo
    (hwind : BealWindingBridge) (hnogo : BealCGANoGo) :
    ∀ (A B C : ℤ) (x y z : ℕ),
      3 ≤ x → 3 ≤ y → 3 ≤ z →
      A ≠ 0 → B ≠ 0 → C ≠ 0 →
      A ^ x + B ^ y = C ^ z →
      1 < bealGcd A B C := by
  intro A B C x y z hx hy hz hA hB hC hsol
  by_contra hnot
  have hle : bealGcd A B C ≤ 1 := Nat.not_lt.mp hnot
  have hpos : 0 < bealGcd A B C := bealGcd_pos hA
  have hcoprime : bealGcd A B C = 1 := le_antisymm hle (Nat.succ_le_of_lt hpos)
  obtain ⟨N, hN, hadm, hw⟩ :=
    hwind A B C x y z hx hy hz hA hB hC hcoprime hsol
  let : NeZero N := ⟨hN⟩
  exact hnogo A B C x y z hx hy hz hA hB hC hcoprime hsol
    (BealCGAGauge_of_ne_zero A C x z (bealMinExp x y z)) N hN ⟨hadm, hw⟩

/-! ### Unbalanced fractional-gap window (proved construction) -/

private theorem beal_window_frac_bounds (m : ℕ) (hm : 0 < m) (δ : ℝ)
    (hle : 2 * Real.pi / m ≤ δ) (hlt : δ < 5 * Real.pi / (2 * m)) :
    (4 : ℝ) ≤ δ * (↑(4 * m) : ℝ) / (2 * Real.pi) ∧
      δ * (↑(4 * m) : ℝ) / (2 * Real.pi) < (5 : ℝ) := by
  have hden : (0 : ℝ) < 2 * Real.pi := by positivity
  have hcast : (↑(4 * m) : ℝ) = 4 * (m : ℝ) := by simp [Nat.cast_mul]
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hm)
  constructor
  · have hmul :
        (2 * Real.pi / m) * (↑(4 * m) : ℝ) / (2 * Real.pi) ≤
          δ * (↑(4 * m) : ℝ) / (2 * Real.pi) :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hle (by positivity)) hden.le
    have heq : (2 * Real.pi / m) * (↑(4 * m) : ℝ) / (2 * Real.pi) = (4 : ℝ) := by
      rw [hcast]
      calc (2 * Real.pi / m) * (4 * (m : ℝ)) / (2 * Real.pi)
          = 4 * ((2 * Real.pi) * m / m) / (2 * Real.pi) := by ring
        _ = 4 := by field_simp [hm0]
    rwa [heq] at hmul
  · have hmul :
        δ * (↑(4 * m) : ℝ) / (2 * Real.pi) <
          (5 * Real.pi / (2 * m)) * (↑(4 * m) : ℝ) / (2 * Real.pi) :=
      div_lt_div_of_pos_right
        (mul_lt_mul_of_pos_right hlt (by positivity)) hden
    have heq :
        (5 * Real.pi / (2 * m)) * (↑(4 * m) : ℝ) / (2 * Real.pi) = (5 : ℝ) := by
      rw [hcast]
      calc (5 * Real.pi / (2 * m)) * (4 * (m : ℝ)) / (2 * Real.pi)
          = 5 * (2 * Real.pi * m / m) / (2 * Real.pi) := by ring
        _ = 5 := by field_simp [hm0]
    rwa [heq] at hmul

private theorem beal_window_delta_lt_two_pi (m : ℕ) (hm4 : 4 ≤ m)
    (δ : ℝ) (hlt : δ < 5 * Real.pi / (2 * m)) :
    δ < 2 * Real.pi := by
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have hmR : (4 : ℝ) ≤ m := Nat.cast_le.mpr hm4
  have hupper : 5 * Real.pi / (2 * m) ≤ 5 * Real.pi / 8 := by
    have : (8 : ℝ) ≤ 2 * m := by nlinarith [hmR]
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) this
  have h54 : (5 : ℝ) * Real.pi / 8 < 2 * Real.pi := by nlinarith [hπ]
  linarith [hlt, hupper, h54]

private theorem beal_window_quantize_eq_four (m : ℕ) [NeZero (4 * m)]
    (hm4 : 4 ≤ m) (δ : ℝ)
    (hle : 2 * Real.pi / m ≤ δ) (hlt : δ < 5 * Real.pi / (2 * m)) :
    quantizeRapidity (4 * m) δ = 4 := by
  have hmpos : 0 < m := Nat.zero_lt_of_lt hm4
  have hfrac := beal_window_frac_bounds m hmpos δ hle hlt
  have hle4 : (4 : ℤ) ≤ quantizeRapidity (4 * m) δ := Int.le_floor.mpr hfrac.1
  have hlt5 : quantizeRapidity (4 * m) δ < (5 : ℤ) := Int.floor_lt.mpr hfrac.2
  omega

private theorem beal_window_n0_val_eq_four (m : ℕ) [NeZero (4 * m)]
    (hm4 : 4 ≤ m) (A C : ℤ) (x z : ℕ)
    (hle : 2 * Real.pi / m ≤ bealFracLogGap A C x z m)
    (hlt : bealFracLogGap A C x z m < 5 * Real.pi / (2 * m)) :
    ((quantizeBealMismatch (4 * m) A C x z m).n 0).val = 4 := by
  set N := 4 * m
  set δ := bealFracLogGap A C x z m
  set t := quantizeBealMismatch N A C x z m
  have hδlt2π : δ < 2 * Real.pi := beal_window_delta_lt_two_pi m hm4 δ hlt
  have hδ0 : 0 ≤ δ :=
    le_trans
      (div_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) (Nat.cast_nonneg _)) hle
  have hbounds := quantizeRapidity_of_lt_two_pi N δ hδ0 hδlt2π
  have hfloor : quantizeRapidity N δ = 4 :=
    beal_window_quantize_eq_four m hm4 δ hle hlt
  have hvalZ : ((t.n 0).val : ℤ) = quantizeRapidity N δ := hbounds.2.2
  rw [hfloor] at hvalZ
  exact_mod_cast hvalZ

private theorem beal_window_seed_admissible (m : ℕ) [NeZero (4 * m)]
    (hm4 : 4 ≤ m) (A C : ℤ) (x z : ℕ)
    (hle : 2 * Real.pi / m ≤ bealFracLogGap A C x z m)
    (hlt : bealFracLogGap A C x z m < 5 * Real.pi / (2 * m)) :
    IsAdmissible (quantizeBealMismatch (4 * m) A C x z m) := by
  set N := 4 * m
  set t := quantizeBealMismatch N A C x z m
  have hp : IsPureBoostSeed t := quantizeBealMismatch_pureBoost N A C x z m
  have hval : (t.n 0).val = 4 := beal_window_n0_val_eq_four m hm4 A C x z hle hlt
  rw [AdmissibleClass.isAdmissible_iff_four_le]
  intro a
  fin_cases a
  · have hm0 : t.m 0 = 0 := hp.2 0
    change 4 * ((t.n 0).val + (t.m 0).val) ≤ N
    simp only [hval, hm0, ZMod.val_zero, add_zero]
    exact Nat.mul_le_mul_left 4 hm4
  · change 4 * ((t.n 1).val + (t.m 1).val) ≤ N
    simp [hp.1 1 (by decide), hp.2 1, ZMod.val_zero]
  · change 4 * ((t.n 2).val + (t.m 2).val) ≤ N
    simp [hp.1 2 (by decide), hp.2 2, ZMod.val_zero]

private theorem beal_window_amplified_admissible (m : ℕ) [NeZero (4 * m)]
    (hm4 : 4 ≤ m) (A C : ℤ) (x z : ℕ)
    (hle : 2 * Real.pi / m ≤ bealFracLogGap A C x z m)
    (hlt : bealFracLogGap A C x z m < 5 * Real.pi / (2 * m)) :
    IsAdmissible (amplifyDiscrete m (quantizeBealMismatch (4 * m) A C x z m)) := by
  set N := 4 * m
  set t := quantizeBealMismatch N A C x z m
  have hp : IsPureBoostSeed t := quantizeBealMismatch_pureBoost N A C x z m
  have hval : (t.n 0).val = 4 := beal_window_n0_val_eq_four m hm4 A C x z hle hlt
  have h4lt : 4 < N :=
    Nat.lt_of_lt_of_le (by decide : 4 < 16) (Nat.mul_le_mul_left 4 hm4)
  have hn0 : t.n 0 = (4 : ZMod N) := by
    have h4val : (4 : ZMod N).val = 4 % N := ZMod.val_natCast (n := N) 4
    have h4mod : 4 % N = 4 := Nat.mod_eq_of_lt h4lt
    apply ZMod.val_injective
    rw [hval, h4val, h4mod]
  have hmul0 : m • t.n 0 = (0 : ZMod N) := by
    rw [hn0, nsmul_eq_mul]
    -- `↑m * 4 = ↑(m * 4) = ↑N = 0`
    trans (↑(m * 4) : ZMod N)
    · exact (Nat.cast_mul m 4).symm
    · have : m * 4 = N := by ring
      rw [this, ZMod.natCast_self]
  rw [AdmissibleClass.isAdmissible_iff_four_le]
  intro a
  fin_cases a
  · change 4 * (((amplifyDiscrete m t).n 0).val + ((amplifyDiscrete m t).m 0).val) ≤ N
    simp only [amplifyDiscrete_n, amplifyDiscrete_m, hmul0, hp.2 0, smul_zero,
      ZMod.val_zero, add_zero, mul_zero]
    exact Nat.zero_le _
  · change 4 * (((amplifyDiscrete m t).n 1).val + ((amplifyDiscrete m t).m 1).val) ≤ N
    simp [amplifyDiscrete_n, amplifyDiscrete_m, hp.1 1 (by decide), hp.2 1,
      ZMod.val_zero]
  · change 4 * (((amplifyDiscrete m t).n 2).val + ((amplifyDiscrete m t).m 2).val) ≤ N
    simp [amplifyDiscrete_n, amplifyDiscrete_m, hp.1 2 (by decide), hp.2 2,
      ZMod.val_zero]

/--
Unbalanced window: if `m = bealMinExp ≥ 4` and the fractional gap lies in
`[2π/m, 5π/(2m))`, the quantised seed on `N = 4m` is a modular winding witness.

No coprimality hypothesis — any positive solution in the window works.
The `m = 3` case is empty for this window (`2π/3 > π/2`).
-/
theorem beal_modularWitness_of_fracGap_window
    {A B C : ℤ} {x y z : ℕ}
    (_hx : 3 ≤ x) (_hy : 3 ≤ y) (_hz : 3 ≤ z)
    (_hA : 0 < A) (_hB : 0 < B) (_hC : 0 < C)
    (_hsol : A ^ x + B ^ y = C ^ z)
    (hm4 : 4 ≤ bealMinExp x y z)
    (hle : 2 * Real.pi / (bealMinExp x y z : ℝ) ≤
      bealFracLogGap A C x z (bealMinExp x y z))
    (hlt : bealFracLogGap A C x z (bealMinExp x y z) <
      5 * Real.pi / (2 * (bealMinExp x y z : ℝ))) :
    let m := bealMinExp x y z
    let N := 4 * m
    ∃ (hN : N ≠ 0),
      letI : NeZero N := ⟨hN⟩
      let t := quantizeBealMismatch N A C x z m
      IsAdmissible t ∧ ∃ w : ModularAmplificationWitness N m, w.t.val = t := by
  set m := bealMinExp x y z
  set N := 4 * m
  set δ := bealFracLogGap A C x z m
  have hmpos : 0 < m := Nat.zero_lt_of_lt hm4
  have hNne : N ≠ 0 := Nat.mul_ne_zero (by decide : (4 : ℕ) ≠ 0) (ne_of_gt hmpos)
  refine ⟨hNne, ?_⟩
  let : NeZero N := ⟨hNne⟩
  set t := quantizeBealMismatch N A C x z m
  have hp : IsPureBoostSeed t := quantizeBealMismatch_pureBoost N A C x z m
  have hδlt2π : δ < 2 * Real.pi := beal_window_delta_lt_two_pi m hm4 δ hlt
  have hadm : IsAdmissible t :=
    beal_window_seed_admissible m hm4 A C x z hle hlt
  have hamp : IsAdmissible (amplifyDiscrete m t) :=
    beal_window_amplified_admissible m hm4 A C x z hle hlt
  have hwind : windingTotal m t ≠ 0 := by
    have hdvd : m ∣ N := ⟨4, by ring⟩
    exact beal_has_winding_of_fracGap_ge N m hmpos A C x z hle hδlt2π hdvd
  exact ⟨hadm,
    ModularAmplification.modularWitness_of_pureBoost_winding m t hp hadm hamp hwind, rfl⟩

end Theorems

end DstDiophantine
