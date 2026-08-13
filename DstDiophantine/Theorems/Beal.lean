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

Amplification factor for modular witnesses is `k = bealAmpExp = max(m, 4)`:
`ModularAmplificationWitness` forces `4 ≤ k`, so the old payload with `k = m = 3`
was empty (`modularWitness_empty_of_eq_three`). Wide principal window:
`2π/k ≤ {δ} < 4π/k` on `N = k` yields `n₀ = 1` (includes `m = 3`).
-/

namespace DstDiophantine

namespace Theorems

open Amplification Discrete Invariant Real ModularAmplification Framework
open _root_.DstDiophantine.Embedding
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

/--
Modular amplification factor: `max(m, 4)`. The fractional gap still uses
`m = bealMinExp`, but `ModularAmplificationWitness` requires `4 ≤ k`
(`modularWitness_four_le`), so `m = 3` lifts to `k = 4`.
-/
def bealAmpExp (x y z : ℕ) : ℕ :=
  max (bealMinExp x y z) 4

theorem bealAmpExp_ge_four (x y z : ℕ) : 4 ≤ bealAmpExp x y z :=
  le_max_right _ _

theorem bealMinExp_le_bealAmpExp (x y z : ℕ) : bealMinExp x y z ≤ bealAmpExp x y z :=
  le_max_left _ _

theorem bealAmpExp_eq_of_four_le {x y z : ℕ} (hm : 4 ≤ bealMinExp x y z) :
    bealAmpExp x y z = bealMinExp x y z :=
  max_eq_left hm

theorem bealAmpExp_eq_four_of_minExp_eq_three {x y z : ℕ}
    (hm : bealMinExp x y z = 3) : bealAmpExp x y z = 4 := by
  simp [bealAmpExp, hm]

theorem bealAmpExp_pos (x y z : ℕ) : 0 < bealAmpExp x y z :=
  Nat.lt_of_lt_of_le (by decide : 0 < 4) (bealAmpExp_ge_four x y z)

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
  have hApow : (0 : ℝ) < (A : ℝ) ^ x := pow_pos (Int.cast_pos.mpr hA) _
  have hBpow : (0 : ℝ) < (B : ℝ) ^ y := pow_pos (Int.cast_pos.mpr hB) _
  have hlog :
      0 < Real.log (1 + (B : ℝ) ^ y / (A : ℝ) ^ x) :=
    Real.log_pos (lt_add_of_pos_right 1 (div_pos hBpow hApow))
  rw [bealFracLogGap_eq_log_one_add_div hm hA hB hC hsol]
  exact div_pos hlog (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm))

/-- Winding threshold sits strictly above the continuous seed cone when `m = 3`. -/
theorem beal_winding_threshold_gt_half_pi_of_minExp_eq_three
    {x y z : ℕ} (hm : bealMinExp x y z = 3) :
    Real.pi / 2 < 2 * Real.pi / (bealMinExp x y z : ℝ) := by
  rw [hm]; nlinarith [Real.pi_pos]

/-- Balanced model gap `log 2 / m` misses the modular winding threshold `2π / m`. -/
theorem beal_balanced_fracGap_lt_winding_threshold {m : ℕ} (hm : 0 < m) :
    Real.log 2 / (m : ℝ) < 2 * Real.pi / (m : ℝ) := by
  have hlog : Real.log 2 < 2 * Real.pi := by
    have h1 : Real.log 2 < 1 := by
      have h := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) (by norm_num)
      norm_num at h ⊢; exact h
    exact h1.trans (by nlinarith [Real.pi_gt_three])
  exact div_lt_div_of_pos_right hlog (Nat.cast_pos.mpr hm)

/-- Balanced gap also misses the lifted threshold `2π / bealAmpExp`. -/
theorem beal_balanced_fracGap_lt_ampExp_threshold {x y z : ℕ}
    (hx : 3 ≤ x) (hy : 3 ≤ y) (hz : 3 ≤ z) :
    Real.log 2 / (bealMinExp x y z : ℝ) <
      2 * Real.pi / (bealAmpExp x y z : ℝ) := by
  have hmR : (0 : ℝ) < bealMinExp x y z := Nat.cast_pos.mpr (bealMinExp_pos hx hy hz)
  have hkR : (0 : ℝ) < bealAmpExp x y z := Nat.cast_pos.mpr (bealAmpExp_pos x y z)
  have hlog1 : Real.log 2 < 1 := by
    have h := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) (by norm_num)
    norm_num at h ⊢; exact h
  have : Real.log 2 * (bealAmpExp x y z : ℝ) <
      2 * Real.pi * (bealMinExp x y z : ℝ) := by
    by_cases h4 : 4 ≤ bealMinExp x y z
    · have hkEq : bealAmpExp x y z = bealMinExp x y z := bealAmpExp_eq_of_four_le h4
      rw [hkEq]
      nlinarith [hlog1, Real.pi_gt_three, hmR]
    · have hm3 : bealMinExp x y z = 3 := by
        have hge : 3 ≤ bealMinExp x y z := bealMinExp_ge_three hx hy hz
        have hlt : bealMinExp x y z < 4 := Nat.not_le.mp h4
        omega
      have hk4 : bealAmpExp x y z = 4 := bealAmpExp_eq_four_of_minExp_eq_three hm3
      rw [hm3, hk4]
      -- `4 log 2 < 6π` from `log 2 < 1` and `π > 3`
      have hπ : (3 : ℝ) < Real.pi := Real.pi_gt_three
      have : (4 : ℝ) * Real.log 2 < 6 * Real.pi := by
        nlinarith [hlog1, hπ]
      convert this using 1 <;> ring
  exact (div_lt_div_iff₀ hmR hkR).mpr this

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
If `2π/k ≤ δ < 2π` and `k ∣ N`, the quantised Beal seed (gap still uses `m`)
has nonzero total winding under amplification factor `k`.
-/
theorem beal_has_winding_of_fracGap_ge (N k m : ℕ) [NeZero N] (hk : 0 < k)
    (A C : ℤ) (x z : ℕ)
    (hle : 2 * Real.pi / k ≤ bealFracLogGap A C x z m)
    (hlt : bealFracLogGap A C x z m < 2 * Real.pi)
    (hdvd : k ∣ N) :
    windingTotal k (quantizeBealMismatch N A C x z m) ≠ 0 := by
  have hπk : 0 ≤ 2 * Real.pi / k :=
    div_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) Real.pi_pos.le) (Nat.cast_nonneg _)
  have h0 : 0 ≤ bealFracLogGap A C x z m := le_trans hπk hle
  simpa [quantizeBealMismatch] using
    windingTotal_ne_zero_of_rapidity_ge
      N k hk (bealFracLogGap A C x z m) h0 hle hlt hdvd

/-! ### Live winding bridge (number-theoretic half) -/

/--
**Live** Beal winding bridge (unproved in full generality).

A coprime solution yields some lattice `N` on which the quantised fractional
gap is an admissible modular winding witness with amplification
`k = bealAmpExp = max(m, 4)`. No PGA real-scale / `ConformalGaugeAdmissible`
conjunct — that identification is the diagnostic obstruction.
-/
def BealWindingBridge : Prop :=
  ∀ (A B C : ℤ) (x y z : ℕ) (_hx : 3 ≤ x) (_hy : 3 ≤ y) (_hz : 3 ≤ z)
    (_hA : A ≠ 0) (_hB : B ≠ 0) (_hC : C ≠ 0),
    bealGcd A B C = 1 →
    A ^ x + B ^ y = C ^ z →
      ∃ (N : ℕ) (hN : N ≠ 0),
        letI : NeZero N := ⟨hN⟩
        let m := bealMinExp x y z
        let k := bealAmpExp x y z
        let t := quantizeBealMismatch N A C x z m
        IsAdmissible t ∧ ∃ w : ModularAmplificationWitness N k, w.t.val = t

/-! ### CGA fractional-power gauge (geometric half) -/

/-- Fractional-power magnitude `|n|^{e/m}` used as a 1D CGA null-cone seed. -/
noncomputable def bealRootMag (n : ℤ) (e m : ℕ) : ℝ :=
  (n.natAbs : ℝ) ^ ((e : ℝ) / m)

theorem bealRootMag_pos {n : ℤ} (hn : n ≠ 0) (e m : ℕ) :
    0 < bealRootMag n e m := by
  unfold bealRootMag
  exact Real.rpow_pos_of_pos (Nat.cast_pos.mpr (Int.natAbs_pos.mpr hn)) _

/-- Fractional log-gap equals the log-ratio of fractional-power magnitudes. -/
theorem bealFracLogGap_eq_log_rootMag (A C : ℤ) (x z m : ℕ)
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
theorem beal_cga_dilation_weights (A C : ℤ) (x z m : ℕ)
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
    bealFracLogGap_eq_log_rootMag A C x z m hA hC
  have hCpos : 0 < bealRootMag C z m := bealRootMag_pos hC z m
  have hexp : Real.exp δ * a = bealRootMag C z m := by
    rw [hδ, Real.exp_sub, Real.exp_log hCpos, Real.exp_log ha]
    field_simp [ne_of_gt ha]
  rw [← hexp, conformalPoint_smul]

/--
Residual geometric no-go (unproved): a coprime solution cannot carry a modular
winding witness (amplification `bealAmpExp`) once the CGA fractional-power gauge
is in force. Does **not** reuse `ConformalGaugeAdmissible` / PGA real-scale.
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
          let k := bealAmpExp x y z
          let t := quantizeBealMismatch N A C x z m
          ¬ (IsAdmissible t ∧ ∃ w : ModularAmplificationWitness N k, w.t.val = t)

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

/-! ### Wide principal window (proved construction) -/

private theorem beal_wide_frac_bounds (k : ℕ) (hk : 0 < k) (δ : ℝ)
    (hle : 2 * Real.pi / k ≤ δ) (hlt : δ < 4 * Real.pi / k) :
    (1 : ℝ) ≤ δ * (k : ℝ) / (2 * Real.pi) ∧
      δ * (k : ℝ) / (2 * Real.pi) < (2 : ℝ) := by
  have hden : (0 : ℝ) < 2 * Real.pi := by positivity
  have hk0 : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hk)
  have hN : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have hNpos : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hlo : (2 * Real.pi / k) * (k : ℝ) / (2 * Real.pi) = (1 : ℝ) := by
    field_simp [hk0]
  have hhi : (4 * Real.pi / k) * (k : ℝ) / (2 * Real.pi) = (2 : ℝ) := by
    field_simp [hk0]; ring
  exact ⟨
    by
      have := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hle hN) hden.le
      rwa [hlo] at this,
    by
      have := div_lt_div_of_pos_right (mul_lt_mul_of_pos_right hlt hNpos) hden
      rwa [hhi] at this⟩

private theorem beal_wide_delta_lt_two_pi (k : ℕ) (hk4 : 4 ≤ k)
    (δ : ℝ) (hlt : δ < 4 * Real.pi / k) :
    δ < 2 * Real.pi := by
  have hkR : (4 : ℝ) ≤ k := Nat.cast_le.mpr hk4
  have hupper : 4 * Real.pi / k ≤ Real.pi := by
    have h : 4 * Real.pi / k ≤ 4 * Real.pi / 4 :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hkR
    convert h using 1; ring
  nlinarith [hlt, hupper, Real.pi_pos]

theorem pureBoostSeedOfRapidity_eq_principal (N : ℕ) [NeZero N] {θ : ℝ}
    (hθ : 0 ≤ θ) :
    pureBoostSeedOfRapidity N θ =
      pureBoostSeedOfRapidity N (principalRapidity θ) := by
  refine congr_arg₂ DiscreteTorsion.mk ?_ rfl
  funext i
  fin_cases i
  · change (quantizeRapidity N θ : ZMod N) =
        (quantizeRapidity N (principalRapidity θ) : ZMod N)
    exact quantizeRapidity_zmod_eq_principal N hθ
  · rfl
  · rfl

private theorem beal_wide_n0_val_eq_one (k : ℕ) [NeZero k] (hk4 : 4 ≤ k) {δ : ℝ}
    (hle : 2 * Real.pi / k ≤ δ) (hlt : δ < 4 * Real.pi / k) :
    ((pureBoostSeedOfRapidity k δ).n 0).val = 1 := by
  have hkpos : 0 < k := Nat.zero_lt_of_lt hk4
  have hδlt2π : δ < 2 * Real.pi := beal_wide_delta_lt_two_pi k hk4 δ hlt
  have hδ0 : 0 ≤ δ :=
    le_trans
      (div_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) (Nat.cast_nonneg _)) hle
  have hbounds := quantizeRapidity_of_lt_two_pi k δ hδ0 hδlt2π
  have hfrac := beal_wide_frac_bounds k hkpos δ hle hlt
  have hfloor : quantizeRapidity k δ = 1 := by
    have hleZ : (1 : ℤ) ≤ quantizeRapidity k δ := by
      have : ((1 : ℤ) : ℝ) ≤ δ * (k : ℝ) / (2 * Real.pi) := by
        simpa using hfrac.1
      exact Int.le_floor.mpr this
    have hltZ : quantizeRapidity k δ < (2 : ℤ) := by
      have : δ * (k : ℝ) / (2 * Real.pi) < ((2 : ℤ) : ℝ) := by
        simpa using hfrac.2
      exact Int.floor_lt.mpr this
    omega
  have hvalZ : (((pureBoostSeedOfRapidity k δ).n 0).val : ℤ) =
      quantizeRapidity k δ := hbounds.2.2
  rw [hfloor] at hvalZ
  exact_mod_cast hvalZ

private theorem beal_wide_smul_n0_eq_zero (k : ℕ) [NeZero k] (hk4 : 4 ≤ k) {δ : ℝ}
    (hle : 2 * Real.pi / k ≤ δ) (hlt : δ < 4 * Real.pi / k) :
    k • (pureBoostSeedOfRapidity k δ).n 0 = 0 := by
  set t := pureBoostSeedOfRapidity k δ
  have hval : (t.n 0).val = 1 := beal_wide_n0_val_eq_one k hk4 hle hlt
  have h1lt : 1 < k := Nat.lt_of_lt_of_le (by decide : 1 < 4) hk4
  have hn0 : t.n 0 = (1 : ZMod k) := by
    apply ZMod.val_injective
    have : Fact (1 < k) := ⟨h1lt⟩
    rw [hval, ZMod.val_one]
  rw [hn0, nsmul_eq_mul]
  change ((k : ℕ) : ZMod k) * (1 : ZMod k) = 0
  rw [mul_one, ZMod.natCast_self]

/--
Wide principal window: if `4 ≤ k` and the gap lies in `[2π/k, 4π/k)`, the
quantised seed on `N = k` is a modular winding witness with `n₀ = 1`.

Depends only on the gap size (no solution hypothesis). Includes `m = 3` via
`k = bealAmpExp = 4` (window `[π/2, π)`).
-/
theorem beal_modularWitness_of_fracGap_window
    (A C : ℤ) (x z m k : ℕ) (hk4 : 4 ≤ k)
    (hle : 2 * Real.pi / k ≤ bealFracLogGap A C x z m)
    (hlt : bealFracLogGap A C x z m < 4 * Real.pi / k) :
    let N := k
    ∃ (hN : N ≠ 0),
      letI : NeZero N := ⟨hN⟩
      let t := quantizeBealMismatch N A C x z m
      IsAdmissible t ∧ ∃ w : ModularAmplificationWitness N k, w.t.val = t := by
  set N := k
  set δ := bealFracLogGap A C x z m
  have hkpos : 0 < k := Nat.zero_lt_of_lt hk4
  have hNne : N ≠ 0 := ne_of_gt hkpos
  refine ⟨hNne, ?_⟩
  let : NeZero N := ⟨hNne⟩
  set t := quantizeBealMismatch N A C x z m
  have hp : IsPureBoostSeed t := quantizeBealMismatch_pureBoost N A C x z m
  have hval : (t.n 0).val = 1 := by
    simpa [t, quantizeBealMismatch] using beal_wide_n0_val_eq_one k hk4 hle hlt
  have hadm : IsAdmissible t :=
    isAdmissible_of_pureBoost_n0_le t hp (by simpa [hval] using hk4)
  have hsmul : k • t.n 0 = 0 := by
    simp [t, quantizeBealMismatch]
  have hamp : IsAdmissible (amplifyDiscrete k t) :=
    isAdmissible_amplifyDiscrete_of_pureBoost_smul_n0 k t hp hsmul
  have hδlt2π : δ < 2 * Real.pi := beal_wide_delta_lt_two_pi k hk4 δ hlt
  have hwind : windingTotal k t ≠ 0 :=
    beal_has_winding_of_fracGap_ge N k m hkpos A C x z hle hδlt2π ⟨1, by ring⟩
  exact ⟨hadm, modularWitness_of_pureBoost_winding k t hp hadm hamp hwind, rfl⟩

/-- Specialisation of the wide window to `k = bealAmpExp`. -/
theorem beal_modularWitness_of_fracGap_window_ampExp
    (A C : ℤ) (x y z : ℕ)
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
  beal_modularWitness_of_fracGap_window A C x z (bealMinExp x y z)
    (bealAmpExp x y z) (bealAmpExp_ge_four x y z) hle hlt

/--
Torus fold: if the *principal* gap lies in the wide window, the quantised seed
(using the unreduced gap) still yields a modular winding witness, because
`quantizeRapidity` depends on `θ` only through its class mod `2π`.
-/
theorem beal_modularWitness_of_principal_fracGap_window
    (A C : ℤ) (x z m k : ℕ) (hk4 : 4 ≤ k)
    (hδ0 : 0 ≤ bealFracLogGap A C x z m)
    (hle : 2 * Real.pi / k ≤ principalRapidity (bealFracLogGap A C x z m))
    (hlt : principalRapidity (bealFracLogGap A C x z m) < 4 * Real.pi / k) :
    let N := k
    ∃ (hN : N ≠ 0),
      letI : NeZero N := ⟨hN⟩
      let t := quantizeBealMismatch N A C x z m
      IsAdmissible t ∧ ∃ w : ModularAmplificationWitness N k, w.t.val = t := by
  set δ := bealFracLogGap A C x z m
  set δp := principalRapidity δ
  have hkpos : 0 < k := Nat.zero_lt_of_lt hk4
  have hNne : k ≠ 0 := ne_of_gt hkpos
  refine ⟨hNne, ?_⟩
  let : NeZero k := ⟨hNne⟩
  set t := quantizeBealMismatch k A C x z m
  have ht : t = pureBoostSeedOfRapidity k δp := by
    simp only [t, quantizeBealMismatch, δp]
    exact pureBoostSeedOfRapidity_eq_principal k hδ0
  have hp : IsPureBoostSeed t := quantizeBealMismatch_pureBoost k A C x z m
  have hval : (t.n 0).val = 1 := by
    have : ((pureBoostSeedOfRapidity k δp).n 0).val = 1 :=
      beal_wide_n0_val_eq_one k hk4 hle hlt
    simpa [ht] using this
  have hadm : IsAdmissible t :=
    isAdmissible_of_pureBoost_n0_le t hp (by simpa [hval] using hk4)
  have hsmul : k • t.n 0 = 0 := by
    have : k • (pureBoostSeedOfRapidity k δp).n 0 = 0 :=
      beal_wide_smul_n0_eq_zero k hk4 hle hlt
    simp [ht, this]
  have hamp : IsAdmissible (amplifyDiscrete k t) :=
    isAdmissible_amplifyDiscrete_of_pureBoost_smul_n0 k t hp hsmul
  have hδplt2π : δp < 2 * Real.pi := beal_wide_delta_lt_two_pi k hk4 δp hlt
  have hδp0 : 0 ≤ δp := principalRapidity_nonneg hδ0
  have hwind : windingTotal k t ≠ 0 := by
    have hw0 : windingTotal k (pureBoostSeedOfRapidity k δp) ≠ 0 :=
      windingTotal_ne_zero_of_rapidity_ge k k hkpos δp hδp0 hle hδplt2π ⟨1, by ring⟩
    simpa [ht] using hw0
  exact ⟨hadm, modularWitness_of_pureBoost_winding k t hp hadm hamp hwind, rfl⟩


end Theorems

end DstDiophantine
