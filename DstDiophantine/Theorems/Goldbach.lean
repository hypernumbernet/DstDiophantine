import DstDiophantine.Theorems.Collatz
import DstDiophantine.Framework.Representation
import DstDiophantine.Embedding.PowerMap
import DstDiophantine.Embedding.Height
import DstDiophantine.Algebra.Amplification
import DstDiophantine.Algebra.Invariant
import DstDiophantine.Algebra.Discrete
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

set_option linter.style.native false

/-!
# Phase 5: Goldbach conjecture (mismatch ensemble outside the cone)

We formalise Chapter 9 of `dst-diophantine.tex`. Configurations on the
admissible cone are closed: the only Goldbach pair that meets the stable phase
is `2 + 2 = 4`, and `GoldbachAdmissibleBridge` holds if and only if the
classical conjecture does. It is not a reduction.

## Mismatch ensemble

Past unit height the additive channel is silent. The remaining observable is
the mismatch of the relative rotor `R(p)† R(q)`, the pure boost of angle
`2δ` with `δ = log q - log p`. Its scalar is `J = 2δ²`, and the normalised
height carries the integer-boost coefficient `16/(3π²)`. The equation of
state is `n/2 = √(pq) cosh(δ/2)`. The vacuum `δ = 0` is the identity rotor,
hence admissible, while for every prime `p ≥ 3` the summands of `2p` lie
outside the cone. An unbalanced pair is separated by the parity gap
`d ∈ {2, 4}`, and that floor tends to zero. On a nonempty finite set of
decompositions the statistical weight `exp(-β J)` is greatest on a pair
closest to equality.

## Paper gap (not closed)

Classical Goldbach (`∀ even n ≥ 4, ∃ primes p,q with p+q=n`) is **not** claimed.
The weight describes the ensemble. It does not decide whether the ensemble is
empty. The coefficient of `integerHeight` is `16/(3π²)`.
-/

namespace DstDiophantine

namespace Theorems

open Amplification Discrete Invariant Real
open _root_.DstDiophantine.Embedding
open _root_.DstDiophantine.Framework

/-! ### Classical Goldbach pairs -/

/-- A Goldbach pair for even `n ≥ 4`: primes `p,q` with `p + q = n`. -/
def IsGoldbachPair (p q n : ℕ) : Prop :=
  Nat.Prime p ∧ Nat.Prime q ∧ p + q = n ∧ Even n ∧ 4 ≤ n

theorem isGoldbachPair_symm {p q n : ℕ} (h : IsGoldbachPair p q n) :
    IsGoldbachPair q p n := by
  obtain ⟨hp, hq, hsum, heven, hn⟩ := h
  exact ⟨hq, hp, by rw [add_comm, hsum], heven, hn⟩

theorem isGoldbachPair_of_primes {p q n : ℕ}
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hsum : p + q = n)
    (heven : Even n) (hn : 4 ≤ n) : IsGoldbachPair p q n :=
  ⟨hp, hq, hsum, heven, hn⟩

/-! ### Null-translator encoding -/

theorem goldbach_sum_iff_motor (p q n : ℤ) :
    p + q = n ↔ powerSumMotor (goldbachEquation p q n) = 1 :=
  (goldbachMotor_one_iff p q n).symm

theorem goldbach_solution_iff_motor {p q n : ℕ} (h : IsGoldbachPair p q n) :
    powerSumMotor (goldbachEquation (p : ℤ) (q : ℤ) (n : ℤ)) = 1 := by
  rw [goldbachMotor_one_iff]
  exact_mod_cast h.2.2.1

/-! ### Integer-rotor height of even targets -/

/-- Height of a positive natural via the integer rotor (same model as Collatz). -/
noncomputable def goldbachTargetHeight (n : ℕ) (hn : n ≠ 0) : ℝ :=
  integerHeight (n : ℤ) (Int.natCast_ne_zero.mpr hn)

theorem goldbachTargetHeight_eq (n : ℕ) (hn : n ≠ 0) :
    goldbachTargetHeight n hn =
      (16 / (3 * Real.pi ^ 2)) * (Real.log n) ^ 2 := by
  unfold goldbachTargetHeight
  rw [integerHeight_eq]
  simp only [Int.natAbs_natCast]
  have hcoef : 0 ≤ 16 / (3 * Real.pi ^ 2) := by positivity
  have hlog : 0 ≤ (Real.log n) ^ 2 := sq_nonneg _
  rw [abs_of_nonneg (mul_nonneg hcoef hlog)]

private theorem log_two_sq_bound_gb :
    (64 : ℝ) * (Real.log 2) ^ 2 > 3 * Real.pi ^ 2 := by
  have hlog : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hpi : Real.pi < (3.15 : ℝ) := Real.pi_lt_d2
  have hL : (29.8 : ℝ) < 64 * (0.6931471803 : ℝ) ^ 2 := by norm_num
  have hlog_nonneg : (0 : ℝ) ≤ 0.6931471803 := by norm_num
  have hlog_sq : (0.6931471803 : ℝ) ^ 2 < (Real.log 2) ^ 2 := by
    rw [pow_two, pow_two]
    exact mul_lt_mul'' hlog hlog hlog_nonneg hlog_nonneg
  have hR : 3 * Real.pi ^ 2 < 3 * (3.15 : ℝ) ^ 2 := by
    have hpi_pos : 0 < Real.pi := Real.pi_pos
    have : Real.pi ^ 2 < (3.15 : ℝ) ^ 2 := by
      rw [pow_two, pow_two]
      exact mul_lt_mul'' hpi hpi (le_of_lt hpi_pos) (le_of_lt hpi_pos)
    nlinarith
  have hCmp : 3 * (3.15 : ℝ) ^ 2 < (29.8 : ℝ) := by norm_num
  nlinarith

theorem goldbachTargetHeight_four_gt_one :
    1 < goldbachTargetHeight 4 (by decide : (4 : ℕ) ≠ 0) := by
  rw [goldbachTargetHeight_eq]
  have h4 : Real.log ((4 : ℕ) : ℝ) = 2 * Real.log 2 := by
    have h4eq : ((4 : ℕ) : ℝ) = 2 * 2 := by norm_num
    rw [h4eq, Real.log_mul (by norm_num) (by norm_num)]
    ring
  rw [h4, show (2 * Real.log 2) ^ 2 = 4 * (Real.log 2) ^ 2 from by ring]
  have hbound : 3 * Real.pi ^ 2 < 64 * (Real.log 2) ^ 2 := log_two_sq_bound_gb
  have hden : 0 < 3 * Real.pi ^ 2 := by positivity
  have hform : 1 < (64 * (Real.log 2) ^ 2) / (3 * Real.pi ^ 2) :=
    (one_lt_div hden).mpr hbound
  have : (16 / (3 * Real.pi ^ 2)) * (4 * (Real.log 2) ^ 2) =
      (64 * (Real.log 2) ^ 2) / (3 * Real.pi ^ 2) := by ring
  rwa [this]

private theorem goldbachTargetHeight_mono {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0)
    (hle : m ≤ n) :
    goldbachTargetHeight m hm ≤ goldbachTargetHeight n hn := by
  rw [goldbachTargetHeight_eq, goldbachTargetHeight_eq]
  have hcoef : 0 ≤ 16 / (3 * Real.pi ^ 2) := by positivity
  have hmpos : 0 < (m : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm)
  have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hlog : Real.log m ≤ Real.log n :=
    (Real.log_le_log_iff hmpos hnpos).mpr (Nat.cast_le.mpr hle)
  have hm1 : (1 : ℝ) ≤ m := Nat.one_le_cast.mpr (Nat.one_le_iff_ne_zero.mpr hm)
  have hn1 : (1 : ℝ) ≤ n := Nat.one_le_cast.mpr (Nat.one_le_iff_ne_zero.mpr hn)
  have hlogm : 0 ≤ Real.log m := Real.log_nonneg hm1
  have hlogn : 0 ≤ Real.log n := Real.log_nonneg hn1
  have hsq : (Real.log m) ^ 2 ≤ (Real.log n) ^ 2 :=
    sq_le_sq.mpr (by rwa [abs_of_nonneg hlogm, abs_of_nonneg hlogn])
  exact mul_le_mul_of_nonneg_left hsq hcoef

/-- Every target `n ≥ 4` already has integer-rotor height `> 1` (independent of
Goldbach decompositions). -/
theorem goldbachTargetHeight_gt_one_of_four_le {n : ℕ} (hn : 4 ≤ n) :
    1 < goldbachTargetHeight n
      (Nat.pos_iff_ne_zero.mp (Nat.lt_of_lt_of_le (by decide : 0 < 4) hn)) := by
  set hn0 : n ≠ 0 :=
    Nat.pos_iff_ne_zero.mp (Nat.lt_of_lt_of_le (by decide : 0 < 4) hn)
  have hmono := goldbachTargetHeight_mono (by decide : (4 : ℕ) ≠ 0) hn0 hn
  exact lt_of_lt_of_le goldbachTargetHeight_four_gt_one hmono

/-! ### Mismatch of the relative rotor

`logMismatch` is the half-angle seed. The relative rotor `R(p)† R(q)` is the
pure boost of angle `2(log q - log p)`, the same scale as `integerRotor`.
-/

/-- Rapidity of the ratio `q / p`. -/
noncomputable def goldbachRapidity (p q : ℕ) (_hp : p ≠ 0) (_hq : q ≠ 0) : ℝ :=
  Real.log (q : ℝ) - Real.log (p : ℝ)

/-- Mismatch scalar of `R(p)† R(q)`. The rotor angle is `2δ`, so `J = 2δ²`. -/
noncomputable def goldbachMismatch (p q : ℕ) (hp : p ≠ 0) (hq : q ≠ 0) : ℝ :=
  J (pureBoost (2 * goldbachRapidity p q hp hq))

theorem goldbachMismatch_eq (p q : ℕ) (hp : p ≠ 0) (hq : q ≠ 0) :
    goldbachMismatch p q hp hq = 2 * (goldbachRapidity p q hp hq) ^ 2 := by
  unfold goldbachMismatch
  rw [J_pureBoost]
  ring

theorem goldbachMismatch_nonneg (p q : ℕ) (hp : p ≠ 0) (hq : q ≠ 0) :
    0 ≤ goldbachMismatch p q hp hq := by
  rw [goldbachMismatch_eq]
  positivity

/-- Normalised height of the relative rotor, with the integer-boost coefficient. -/
noncomputable def goldbachMismatchHeight (p q : ℕ) (hp : p ≠ 0) (hq : q ≠ 0) : ℝ :=
  |JNormalized (pureBoost (2 * goldbachRapidity p q hp hq))|

theorem goldbachMismatchHeight_eq (p q : ℕ) (hp : p ≠ 0) (hq : q ≠ 0) :
    goldbachMismatchHeight p q hp hq =
      (16 / (3 * Real.pi ^ 2)) * (goldbachRapidity p q hp hq) ^ 2 := by
  unfold goldbachMismatchHeight
  rw [JNormalized_pureBoost]
  have hnonneg :
      0 ≤ (4 / (3 * Real.pi ^ 2)) * (2 * goldbachRapidity p q hp hq) ^ 2 := by
    positivity
  rw [abs_of_nonneg hnonneg]
  ring

theorem goldbachMismatchHeight_nonneg (p q : ℕ) (hp : p ≠ 0) (hq : q ≠ 0) :
    0 ≤ goldbachMismatchHeight p q hp hq :=
  abs_nonneg _

theorem goldbachMismatchHeight_proof_irrel {p q : ℕ} (hp hp' : p ≠ 0) (hq hq' : q ≠ 0) :
    goldbachMismatchHeight p q hp hq = goldbachMismatchHeight p q hp' hq' := rfl

theorem goldbachRapidity_comm (p q : ℕ) (hp : p ≠ 0) (hq : q ≠ 0) :
    goldbachRapidity p q hp hq = -goldbachRapidity q p hq hp := by
  unfold goldbachRapidity
  ring

theorem goldbachMismatch_symm (p q : ℕ) (hp : p ≠ 0) (hq : q ≠ 0) :
    goldbachMismatch p q hp hq = goldbachMismatch q p hq hp := by
  rw [goldbachMismatch_eq, goldbachMismatch_eq, goldbachRapidity_comm]
  ring

theorem goldbachMismatchHeight_symm (p q : ℕ) (hp : p ≠ 0) (hq : q ≠ 0) :
    goldbachMismatchHeight p q hp hq = goldbachMismatchHeight q p hq hp := by
  rw [goldbachMismatchHeight_eq, goldbachMismatchHeight_eq, goldbachRapidity_comm]
  ring

theorem goldbachRapidity_eq_log_div {p q : ℕ} (hp : 0 < p) (hq : 0 < q) :
    goldbachRapidity p q (Nat.pos_iff_ne_zero.mp hp) (Nat.pos_iff_ne_zero.mp hq) =
      Real.log ((q : ℝ) / p) := by
  unfold goldbachRapidity
  rw [Real.log_div (by exact_mod_cast hq.ne') (by exact_mod_cast hp.ne')]

theorem goldbachMismatch_eq_zero_iff {p q : ℕ} (hp : 0 < p) (hq : 0 < q) :
    goldbachMismatch p q (Nat.pos_iff_ne_zero.mp hp) (Nat.pos_iff_ne_zero.mp hq) = 0 ↔
      p = q := by
  set hp0 : p ≠ 0 := Nat.pos_iff_ne_zero.mp hp
  set hq0 : q ≠ 0 := Nat.pos_iff_ne_zero.mp hq
  constructor
  · intro h0
    have hsq : goldbachRapidity p q hp0 hq0 = 0 := by
      have := goldbachMismatch_eq p q hp0 hq0
      rw [h0] at this
      nlinarith [sq_nonneg (goldbachRapidity p q hp0 hq0)]
    have hexp :
        Real.exp (goldbachRapidity p q hp0 hq0) = (q : ℝ) / p := by
      unfold goldbachRapidity
      rw [Real.exp_sub, Real.exp_log (by exact_mod_cast hq), Real.exp_log (by exact_mod_cast hp)]
    rw [hsq, Real.exp_zero] at hexp
    have hp' : (0 : ℝ) < p := by exact_mod_cast hp
    have hqp : (q : ℝ) = p := by
      have hdiv : (q : ℝ) / p = 1 := hexp.symm
      field_simp at hdiv
      exact hdiv
    exact_mod_cast hqp.symm
  · intro h
    subst h
    rw [goldbachMismatch_eq]
    unfold goldbachRapidity
    ring

/-! ### Equation of state

The additive channel fixes `n = p + q`. The mismatch rapidity is the hyperbolic
cost of the gap between the arithmetic mean `n/2` and the geometric mean
`√(pq)`.
-/

theorem goldbach_equation_of_state {p q : ℕ} (hp : 0 < p) (hq : 0 < q) :
    (p + q : ℝ) =
      2 * Real.sqrt ((p : ℝ) * q) *
        Real.cosh
          (goldbachRapidity p q (Nat.pos_iff_ne_zero.mp hp) (Nat.pos_iff_ne_zero.mp hq) / 2) := by
  set hp0 : p ≠ 0 := Nat.pos_iff_ne_zero.mp hp
  set hq0 : q ≠ 0 := Nat.pos_iff_ne_zero.mp hq
  set δ : ℝ := goldbachRapidity p q hp0 hq0
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hsp : 0 < Real.sqrt (p : ℝ) := Real.sqrt_pos.mpr hp'
  have hsq : 0 < Real.sqrt (q : ℝ) := Real.sqrt_pos.mpr hq'
  have hexp : Real.exp (δ / 2) = Real.sqrt (q : ℝ) / Real.sqrt (p : ℝ) := by
    have hlogp : Real.log (Real.sqrt (p : ℝ)) = Real.log (p : ℝ) / 2 := Real.log_sqrt hp'.le
    have hlogq : Real.log (Real.sqrt (q : ℝ)) = Real.log (q : ℝ) / 2 := Real.log_sqrt hq'.le
    have hδ : δ / 2 = Real.log (Real.sqrt (q : ℝ)) - Real.log (Real.sqrt (p : ℝ)) := by
      unfold δ goldbachRapidity
      rw [hlogp, hlogq]
      ring
    rw [hδ, Real.exp_sub, Real.exp_log hsq, Real.exp_log hsp]
  have hexpNeg : Real.exp (-(δ / 2)) = Real.sqrt (p : ℝ) / Real.sqrt (q : ℝ) := by
    have hlogp : Real.log (Real.sqrt (p : ℝ)) = Real.log (p : ℝ) / 2 := Real.log_sqrt hp'.le
    have hlogq : Real.log (Real.sqrt (q : ℝ)) = Real.log (q : ℝ) / 2 := Real.log_sqrt hq'.le
    have hδ : -(δ / 2) = Real.log (Real.sqrt (p : ℝ)) - Real.log (Real.sqrt (q : ℝ)) := by
      unfold δ goldbachRapidity
      rw [hlogp, hlogq]
      ring
    rw [hδ, Real.exp_sub, Real.exp_log hsp, Real.exp_log hsq]
  have hsqrt : Real.sqrt ((p : ℝ) * q) = Real.sqrt (p : ℝ) * Real.sqrt (q : ℝ) :=
    Real.sqrt_mul hp'.le q
  calc
    (p + q : ℝ)
        = Real.sqrt (q : ℝ) * Real.sqrt (q : ℝ) + Real.sqrt (p : ℝ) * Real.sqrt (p : ℝ) := by
          rw [Real.mul_self_sqrt hq'.le, Real.mul_self_sqrt hp'.le]
          ring
      _ = (Real.sqrt (p : ℝ) * Real.sqrt (q : ℝ)) *
            (Real.sqrt (q : ℝ) / Real.sqrt (p : ℝ) + Real.sqrt (p : ℝ) / Real.sqrt (q : ℝ)) := by
          field_simp
      _ = (Real.sqrt (p : ℝ) * Real.sqrt (q : ℝ)) *
            (Real.exp (δ / 2) + Real.exp (-(δ / 2))) := by
          rw [hexp, hexpNeg]
      _ = 2 * (Real.sqrt (p : ℝ) * Real.sqrt (q : ℝ)) *
            ((Real.exp (δ / 2) + Real.exp (-(δ / 2))) / 2) := by
          ring
      _ = 2 * Real.sqrt ((p : ℝ) * q) * Real.cosh (δ / 2) := by
          rw [← hsqrt, Real.cosh_eq]

/-! ### Vacuum of the mismatch, outside the cone -/

theorem goldbach_double_prime {p : ℕ} (hp : Nat.Prime p) : IsGoldbachPair p p (2 * p) := by
  have htwo : 2 ≤ p := hp.two_le
  exact ⟨hp, hp, by omega, even_two_mul p, by omega⟩

/-- Equal primes are the vacuum of the mismatch, and for `p ≥ 3` both summands
lie outside the cone. The identity rotor does not pull them back. -/
theorem goldbach_vacuum_outside_cone {p : ℕ} (hp : Nat.Prime p) (hp3 : 3 ≤ p) :
    goldbachMismatch p p hp.ne_zero hp.ne_zero = 0 ∧
      IsAdmissibleContinuous (pureBoost 0) ∧
      ¬ IsAdmissibleContinuous (pureBoost (2 * Real.log (p : ℝ))) := by
  refine ⟨?_, (isAdmissibleContinuous_pureBoost_iff 0).mpr ⟨le_rfl, by positivity⟩, ?_⟩
  · rw [goldbachMismatch_eq]
    unfold goldbachRapidity
    ring
  · intro hadm
    have hp2 : p = 2 := (prime_boost_admissible_iff hp).mp hadm
    omega

theorem goldbach_three_three_vacuum :
    goldbachMismatch 3 3 (by decide) (by decide) = 0 ∧
      ¬ IsAdmissibleContinuous (pureBoost (2 * Real.log (3 : ℝ))) := by
  have h := goldbach_vacuum_outside_cone (by decide : Nat.Prime 3) (by decide)
  exact ⟨h.1, h.2.2⟩

/-! ### Parity floor

Both summands of an even target `n ≥ 6` are odd. Their difference is at least
`2` when `4 ∣ n`, and a positive multiple of `4` when `n ≡ 2 (mod 4)`.
-/

/-- Minimal positive separation of an unbalanced odd-odd pair of sum `n`. -/
def goldbachParitySep (n : ℕ) : ℕ :=
  if n % 4 = 0 then 2 else 4

theorem goldbach_summands_odd {p q n : ℕ} (h : IsGoldbachPair p q n) (hn : 6 ≤ n) :
    Odd p ∧ Odd q := by
  have hsum : p + q = n := h.2.2.1
  have heven : n % 2 = 0 := Nat.even_iff.mp h.2.2.2.1
  have hp2 : p ≠ 2 := by
    intro hp
    have hpmod : p % 2 = 0 := by simp [hp]
    rcases Nat.Prime.eq_two_or_odd h.2.1 with hq | hq
    · omega
    · omega
  have hq2 : q ≠ 2 := by
    intro hq
    have hqmod : q % 2 = 0 := by simp [hq]
    rcases Nat.Prime.eq_two_or_odd h.1 with hp | hp
    · omega
    · omega
  rcases Nat.Prime.eq_two_or_odd h.1 with hp | hp
  · exact absurd hp hp2
  rcases Nat.Prime.eq_two_or_odd h.2.1 with hq | hq
  · exact absurd hq hq2
  · exact ⟨Nat.odd_iff.mpr hp, Nat.odd_iff.mpr hq⟩

theorem goldbach_diff_ge {p q n : ℕ} (h : IsGoldbachPair p q n) (hn : 6 ≤ n) (hlt : p < q) :
    goldbachParitySep n ≤ q - p := by
  obtain ⟨hpodd, hqodd⟩ := goldbach_summands_odd h hn
  obtain ⟨a, ha⟩ := hpodd
  obtain ⟨b, hb⟩ := hqodd
  have hsum : p + q = n := h.2.2.1
  have hdiff : q - p = 2 * (b - a) := by omega
  have hba : a < b := by omega
  have heven : Even n := h.2.2.2.1
  have hmod : n % 4 = 0 ∨ n % 4 = 2 := by
    have : n % 2 = 0 := Nat.even_iff.mp heven
    omega
  rcases hmod with h0 | h2mod
  · have hsep : goldbachParitySep n = 2 := by simp [goldbachParitySep, h0]
    have hge : 2 ≤ q - p := by
      rw [hdiff]
      have : 1 ≤ b - a := by omega
      omega
    simp [hsep, hge]
  · have hsep : goldbachParitySep n = 4 := by simp [goldbachParitySep, h2mod]
    have h4 : (q - p) % 4 = 0 := by
      have hnp : q - p = n - 2 * p := by omega
      have hpmod : p % 2 = 1 := by omega
      omega
    have hdvd : 4 ∣ q - p := Nat.dvd_of_mod_eq_zero h4
    obtain ⟨k, hk⟩ := hdvd
    have hkpos : 0 < k := by
      have hpos : 0 < q - p := by omega
      omega
    have hge : 4 ≤ q - p := by omega
    simp [hsep, hge]

theorem goldbach_ratio_ge {p q n : ℕ} (h : IsGoldbachPair p q n) (hn : 6 ≤ n) (hlt : p < q) :
    ((n + goldbachParitySep n : ℕ) : ℝ) / ((n - goldbachParitySep n : ℕ) : ℝ) ≤
      (q : ℝ) / p := by
  have hsep := goldbach_diff_ge h hn hlt
  have hsum : p + q = n := h.2.2.1
  have hppos : 0 < p := h.1.pos
  set d := goldbachParitySep n
  have hnd : d < n := by
    have hd_le : d ≤ 4 := by
      unfold d goldbachParitySep
      split_ifs <;> decide
    omega
  have h2q : n + d ≤ 2 * q := by omega
  have h2p : 2 * p ≤ n - d := by omega
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hppos
  have hden : (0 : ℝ) < ((n - d : ℕ) : ℝ) := by exact_mod_cast Nat.sub_pos_of_lt hnd
  rw [div_le_div_iff₀ hden hp0]
  have hcastq : ((n + d : ℕ) : ℝ) ≤ 2 * (q : ℝ) := by exact_mod_cast h2q
  have hcastp : 2 * (p : ℝ) ≤ ((n - d : ℕ) : ℝ) := by exact_mod_cast h2p
  nlinarith [hden.le, show (0 : ℝ) ≤ ((n + d : ℕ) : ℝ) by positivity]

theorem goldbach_mismatch_floor {p q n : ℕ} (h : IsGoldbachPair p q n) (hn : 6 ≤ n)
    (hlt : p < q) :
    (16 / (3 * Real.pi ^ 2)) *
        (Real.log (((n + goldbachParitySep n : ℕ) : ℝ) /
          ((n - goldbachParitySep n : ℕ) : ℝ))) ^ 2 ≤
      goldbachMismatchHeight p q h.1.ne_zero h.2.1.ne_zero := by
  have hp : 0 < p := h.1.pos
  have hq : 0 < q := h.2.1.pos
  have hp0 : p ≠ 0 := h.1.ne_zero
  have hq0 : q ≠ 0 := h.2.1.ne_zero
  set d := goldbachParitySep n
  have hr := goldbach_ratio_ge h hn hlt
  have hden : (0 : ℝ) < ((n - d : ℕ) : ℝ) := by
    have hd_le : d ≤ 4 := by
      unfold d goldbachParitySep
      split_ifs <;> decide
    exact_mod_cast Nat.sub_pos_of_lt (show d < n by omega)
  have hfloor_pos : (0 : ℝ) < ((n + d : ℕ) : ℝ) / ((n - d : ℕ) : ℝ) := by positivity
  have hratio_pos : (0 : ℝ) < (q : ℝ) / p := by positivity
  have hlog := (Real.log_le_log_iff hfloor_pos hratio_pos).mpr hr
  have hfloor_ge_one : (1 : ℝ) ≤ ((n + d : ℕ) : ℝ) / ((n - d : ℕ) : ℝ) := by
    rw [one_le_div hden]
    exact_mod_cast (show n - d ≤ n + d by omega)
  have hlog_nonneg : 0 ≤ Real.log (((n + d : ℕ) : ℝ) / ((n - d : ℕ) : ℝ)) :=
    Real.log_nonneg hfloor_ge_one
  have hpair_nonneg : 0 ≤ Real.log ((q : ℝ) / p) := by
    have hge : (1 : ℝ) ≤ (q : ℝ) / p := by
      rw [one_le_div (by exact_mod_cast hp)]
      exact_mod_cast (le_of_lt hlt)
    exact Real.log_nonneg hge
  have hsq :
      (Real.log (((n + d : ℕ) : ℝ) / ((n - d : ℕ) : ℝ))) ^ 2 ≤ (Real.log ((q : ℝ) / p)) ^ 2 :=
    pow_le_pow_left₀ hlog_nonneg hlog 2
  rw [goldbachMismatchHeight_eq, goldbachRapidity_eq_log_div hp hq]
  exact mul_le_mul_of_nonneg_left hsq (by positivity)

private theorem goldbach_log_floor_le {n : ℕ} (hn : 8 ≤ n) :
    Real.log (((n + goldbachParitySep n : ℕ) : ℝ) / ((n - goldbachParitySep n : ℕ) : ℝ)) ≤
      (2 * (goldbachParitySep n : ℝ)) / ((n - goldbachParitySep n : ℕ) : ℝ) := by
  set d := goldbachParitySep n
  have hnd : d < n := by
    have hd_le : d ≤ 4 := by
      unfold d goldbachParitySep
      split_ifs <;> decide
    omega
  have hden : (0 : ℝ) < ((n - d : ℕ) : ℝ) := by exact_mod_cast Nat.sub_pos_of_lt hnd
  have hpos : (0 : ℝ) < ((n + d : ℕ) : ℝ) / ((n - d : ℕ) : ℝ) := by positivity
  have hlog := Real.log_le_sub_one_of_pos hpos
  have hsub : ((n + d : ℕ) : ℝ) / ((n - d : ℕ) : ℝ) - 1 =
      (2 * (d : ℝ)) / ((n - d : ℕ) : ℝ) := by
    have hone : (1 : ℝ) = ((n - d : ℕ) : ℝ) / ((n - d : ℕ) : ℝ) := by
      field_simp [hden.ne']
    rw [hone, div_sub_div_same]
    have hdiff : ((n + d : ℕ) : ℝ) - ((n - d : ℕ) : ℝ) = 2 * (d : ℝ) := by
      rw [Nat.cast_add, Nat.cast_sub (le_of_lt hnd)]
      ring
    rw [hdiff]
  linarith

private theorem goldbach_crude_floor_le {n : ℕ} (hn : 8 ≤ n) :
    (16 / (3 * Real.pi ^ 2)) *
        ((2 * (goldbachParitySep n : ℝ)) / ((n - goldbachParitySep n : ℕ) : ℝ)) ^ 2 ≤
      (1024 / (3 * Real.pi ^ 2)) / ((n - 4 : ℕ) : ℝ) ^ 2 := by
  set d := goldbachParitySep n
  have hd_le : (d : ℝ) ≤ 4 := by
    have : d ≤ 4 := by
      unfold d goldbachParitySep
      split_ifs <;> decide
    exact_mod_cast this
  have hden : (0 : ℝ) < ((n - d : ℕ) : ℝ) := by
    have hnd : d < n := by
      have hd4 : d ≤ 4 := by exact_mod_cast hd_le
      omega
    exact_mod_cast Nat.sub_pos_of_lt hnd
  have hfour : (0 : ℝ) < ((n - 4 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.sub_pos_of_lt (show 4 < n by omega))
  have hgap : ((n - 4 : ℕ) : ℝ) ≤ ((n - d : ℕ) : ℝ) := by
    have hle : n - 4 ≤ n - d := by
      have hd4 : d ≤ 4 := by exact_mod_cast hd_le
      omega
    exact_mod_cast hle
  have hfrac : (2 * (d : ℝ)) / ((n - d : ℕ) : ℝ) ≤ 8 / ((n - 4 : ℕ) : ℝ) := by
    rw [div_le_div_iff₀ hden hfour]
    nlinarith
  have hsq :
      ((2 * (d : ℝ)) / ((n - d : ℕ) : ℝ)) ^ 2 ≤ (8 / ((n - 4 : ℕ) : ℝ)) ^ 2 := by
    have hnn : 0 ≤ (2 * (d : ℝ)) / ((n - d : ℕ) : ℝ) := div_nonneg (by linarith) hden.le
    exact pow_le_pow_left₀ hnn hfrac 2
  have hcoef : 0 ≤ 16 / (3 * Real.pi ^ 2) := by positivity
  have h64 : (16 / (3 * Real.pi ^ 2)) * (8 / ((n - 4 : ℕ) : ℝ)) ^ 2 =
      (1024 / (3 * Real.pi ^ 2)) / ((n - 4 : ℕ) : ℝ) ^ 2 := by
    field_simp
    ring
  nlinarith [mul_le_mul_of_nonneg_left hsq hcoef]

/-- The parity floor tends to zero: no uniform positive mismatch separates
unbalanced pairs from the vacuum. -/
theorem goldbach_parity_floor_eventually_lt {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (16 / (3 * Real.pi ^ 2)) *
          (Real.log (((n + goldbachParitySep n : ℕ) : ℝ) /
            ((n - goldbachParitySep n : ℕ) : ℝ))) ^ 2 < ε := by
  have hsqrt : 0 < Real.sqrt (3 * Real.pi ^ 2 * ε) := Real.sqrt_pos.mpr (by positivity)
  obtain ⟨M, hM⟩ := exists_nat_gt (32 / Real.sqrt (3 * Real.pi ^ 2 * ε))
  refine ⟨M + 8, ?_⟩
  intro n hn
  have hn8 : 8 ≤ n := by omega
  set t : ℝ := ((n - 4 : ℕ) : ℝ)
  have ht : 0 < t := by
    dsimp [t]
    exact_mod_cast (Nat.sub_pos_of_lt (show 4 < n by omega))
  have hgt : 32 / Real.sqrt (3 * Real.pi ^ 2 * ε) < t := by
    have hstep : (M : ℝ) < t := by
      dsimp [t]
      exact_mod_cast (show M < n - 4 by omega)
    exact lt_trans hM hstep
  have hs2 : Real.sqrt (3 * Real.pi ^ 2 * ε) ^ 2 = 3 * Real.pi ^ 2 * ε := by
    rw [pow_two, Real.mul_self_sqrt (by positivity)]
  have h32 : (32 : ℝ) < t * Real.sqrt (3 * Real.pi ^ 2 * ε) := by
    have := mul_lt_mul_of_pos_right hgt hsqrt
    rwa [div_mul_cancel₀ _ hsqrt.ne'] at this
  have h1024 : (1024 : ℝ) < t ^ 2 * (3 * Real.pi ^ 2 * ε) := by
    have hsq := mul_lt_mul' h32.le h32 (by norm_num) (mul_pos ht hsqrt)
    nlinarith [hs2]
  have hbound : (1024 / (3 * Real.pi ^ 2)) / t ^ 2 < ε := by
    rw [div_lt_iff₀ (by positivity : 0 < t ^ 2), div_lt_iff₀ (by positivity : 0 < 3 * Real.pi ^ 2)]
    linarith
  have hlog := goldbach_log_floor_le hn8
  have hden : (0 : ℝ) < ((n - goldbachParitySep n : ℕ) : ℝ) := by
    have hd_le : goldbachParitySep n ≤ 4 := by
      unfold goldbachParitySep
      split_ifs <;> decide
    exact_mod_cast Nat.sub_pos_of_lt (show goldbachParitySep n < n by omega)
  have hlog_nn :
      0 ≤ Real.log (((n + goldbachParitySep n : ℕ) : ℝ) /
        ((n - goldbachParitySep n : ℕ) : ℝ)) := by
    have hge : (1 : ℝ) ≤ ((n + goldbachParitySep n : ℕ) : ℝ) /
        ((n - goldbachParitySep n : ℕ) : ℝ) := by
      rw [one_le_div hden]
      exact_mod_cast
        (show n - goldbachParitySep n ≤ n + goldbachParitySep n by omega)
    exact Real.log_nonneg hge
  have hsqlog :
      (Real.log (((n + goldbachParitySep n : ℕ) : ℝ) /
        ((n - goldbachParitySep n : ℕ) : ℝ))) ^ 2 ≤
        ((2 * (goldbachParitySep n : ℝ)) / ((n - goldbachParitySep n : ℕ) : ℝ)) ^ 2 :=
    pow_le_pow_left₀ hlog_nn hlog 2
  have hcoef : 0 ≤ 16 / (3 * Real.pi ^ 2) := by positivity
  have hfloor := mul_le_mul_of_nonneg_left hsqlog hcoef
  have hcrude := goldbach_crude_floor_le hn8
  have : (1024 / (3 * Real.pi ^ 2)) / t ^ 2 =
      (1024 / (3 * Real.pi ^ 2)) / ((n - 4 : ℕ) : ℝ) ^ 2 := rfl
  linarith

/-! ### Statistical weight

The cone does not select a decomposition. On the finite set of prime pairs the
weight `exp(-β J)` is greatest at a minimum of `J`, and that minimum is a pair
closest to equality.
-/

noncomputable def goldbachWeight (β : ℝ) (p q : ℕ) (hp : p ≠ 0) (hq : q ≠ 0) : ℝ :=
  Real.exp (-β * goldbachMismatch p q hp hq)

theorem goldbachWeight_anti {β : ℝ} (hβ : 0 ≤ β) {p q p' q' : ℕ}
    (hp : p ≠ 0) (hq : q ≠ 0) (hp' : p' ≠ 0) (hq' : q' ≠ 0)
    (hle : goldbachMismatch p q hp hq ≤ goldbachMismatch p' q' hp' hq') :
    goldbachWeight β p' q' hp' hq' ≤ goldbachWeight β p q hp hq := by
  unfold goldbachWeight
  apply Real.exp_le_exp.mpr
  have := mul_le_mul_of_nonneg_left hle hβ
  linarith

theorem goldbachMismatchHeight_antitone {n p₁ p₂ : ℕ}
    (hp1 : 0 < p₁) (hp2 : 0 < p₂) (hn1 : p₁ ≤ n - p₁) (hn2 : p₂ ≤ n - p₂)
    (hle : p₁ ≤ p₂) :
    goldbachMismatchHeight p₂ (n - p₂) (Nat.pos_iff_ne_zero.mp hp2)
        (Nat.pos_iff_ne_zero.mp (by omega : 0 < n - p₂)) ≤
      goldbachMismatchHeight p₁ (n - p₁) (Nat.pos_iff_ne_zero.mp hp1)
        (Nat.pos_iff_ne_zero.mp (by omega : 0 < n - p₁)) := by
  have hp1n : p₁ ≤ n := le_trans hn1 (Nat.sub_le n p₁)
  have hp2n : p₂ ≤ n := le_trans hn2 (Nat.sub_le n p₂)
  have hlt1 : p₁ < n := by omega
  have hlt2 : p₂ < n := by omega
  have hcomp1 : 0 < n - p₁ := Nat.sub_pos_of_lt hlt1
  have hcomp2 : 0 < n - p₂ := Nat.sub_pos_of_lt hlt2
  have hp1' : (0 : ℝ) < p₁ := by exact_mod_cast hp1
  have hp2' : (0 : ℝ) < p₂ := by exact_mod_cast hp2
  have hden1 : (0 : ℝ) < ((n - p₁ : ℕ) : ℝ) := by exact_mod_cast hcomp1
  have hden2 : (0 : ℝ) < ((n - p₂ : ℕ) : ℝ) := by exact_mod_cast hcomp2
  have hratio : ((n - p₂ : ℕ) : ℝ) / p₂ ≤ ((n - p₁ : ℕ) : ℝ) / p₁ := by
    rw [div_le_div_iff₀ hp2' hp1']
    have hcast1 : ((n - p₁ : ℕ) : ℝ) = (n : ℝ) - p₁ := Nat.cast_sub hp1n
    have hcast2 : ((n - p₂ : ℕ) : ℝ) = (n : ℝ) - p₂ := Nat.cast_sub hp2n
    rw [hcast1, hcast2]
    have hleR : (p₁ : ℝ) ≤ p₂ := by exact_mod_cast hle
    have hnR : (0 : ℝ) < n := by exact_mod_cast (lt_trans hp1 hlt1)
    nlinarith [hleR, hnR]
  have hlog :=
    (Real.log_le_log_iff (div_pos hden2 hp2') (div_pos hden1 hp1')).mpr hratio
  have hge1 : (1 : ℝ) ≤ ((n - p₂ : ℕ) : ℝ) / p₂ := by
    rw [one_le_div hp2']
    exact_mod_cast hn2
  have hlog_nn : 0 ≤ Real.log (((n - p₂ : ℕ) : ℝ) / p₂) := Real.log_nonneg hge1
  have hsq :
      (Real.log (((n - p₂ : ℕ) : ℝ) / p₂)) ^ 2 ≤
        (Real.log (((n - p₁ : ℕ) : ℝ) / p₁)) ^ 2 :=
    pow_le_pow_left₀ hlog_nn hlog 2
  rw [goldbachMismatchHeight_eq, goldbachMismatchHeight_eq,
    goldbachRapidity_eq_log_div hp2 hcomp2, goldbachRapidity_eq_log_div hp1 hcomp1]
  exact mul_le_mul_of_nonneg_left hsq (by positivity)

/-- Candidate first summands `p ≤ n` with both `p` and `n - p` prime. -/
def goldbachCandidates (n : ℕ) : Finset ℕ :=
  (Finset.range (n + 1)).filter fun p =>
    decide (Nat.Prime p ∧ p ≤ n ∧ Nat.Prime (n - p))

theorem mem_goldbachCandidates_iff {n p : ℕ} :
    p ∈ goldbachCandidates n ↔ p ≤ n ∧ Nat.Prime p ∧ Nat.Prime (n - p) := by
  constructor
  · intro hp
    simp only [goldbachCandidates, Finset.mem_filter, Finset.mem_range, decide_eq_true_eq] at hp
    exact ⟨Nat.lt_succ_iff.mp hp.1, hp.2.1, hp.2.2.2⟩
  · intro ⟨hle, hpp, hq⟩
    simp only [goldbachCandidates, Finset.mem_filter, Finset.mem_range, decide_eq_true_eq]
    exact ⟨Nat.lt_succ_of_le hle, ⟨hpp, hle, hq⟩⟩

/-- Nonempty candidate sets yield a Goldbach pair when `n` is even and `≥ 4`. -/
theorem exists_goldbachPair_of_candidates {n : ℕ} (he : Even n) (hn : 4 ≤ n)
    (hne : (goldbachCandidates n).Nonempty) :
    ∃ p q, IsGoldbachPair p q n := by
  obtain ⟨p, hp⟩ := hne
  obtain ⟨hle, hpp, hq⟩ := mem_goldbachCandidates_iff.mp hp
  refine ⟨p, n - p, hpp, hq, Nat.add_sub_of_le hle, he, hn⟩

/-- Mismatch height on candidate summands (zero outside the candidate set). -/
noncomputable def candidateMismatch (n p : ℕ) : ℝ :=
  if h : p ∈ goldbachCandidates n then
    goldbachMismatchHeight p (n - p)
      (Nat.Prime.ne_zero (mem_goldbachCandidates_iff.mp h).2.1)
      (Nat.Prime.ne_zero (mem_goldbachCandidates_iff.mp h).2.2)
  else 0

/-- On a nonempty finite candidate set the mismatch height attains a minimum. -/
theorem exists_min_goldbachMismatch {n : ℕ}
    (hne : (goldbachCandidates n).Nonempty) :
    ∃ p ∈ goldbachCandidates n,
      ∀ q ∈ goldbachCandidates n, candidateMismatch n p ≤ candidateMismatch n q := by
  classical
  obtain ⟨p, hp, hmin⟩ :=
    Finset.exists_min_image (goldbachCandidates n) (candidateMismatch n) hne
  exact ⟨p, hp, hmin⟩

theorem goldbachCandidates_compl {n p : ℕ} (hp : p ∈ goldbachCandidates n) :
    n - p ∈ goldbachCandidates n := by
  obtain ⟨hle, hpp, hq⟩ := mem_goldbachCandidates_iff.mp hp
  have hback : n - (n - p) = p := Nat.sub_sub_self hle
  rw [mem_goldbachCandidates_iff]
  exact ⟨Nat.sub_le _ _, hq, hback.symm ▸ hpp⟩

/-- Prime summands on the balanced side of `n/2`. -/
def goldbachBalancedCandidates (n : ℕ) : Finset ℕ :=
  (goldbachCandidates n).filter fun p => decide (p ≤ n - p)

theorem mem_goldbachBalancedCandidates {n p : ℕ} :
    p ∈ goldbachBalancedCandidates n ↔ p ∈ goldbachCandidates n ∧ p ≤ n - p := by
  simp [goldbachBalancedCandidates, decide_eq_true_eq]

theorem goldbachBalancedCandidates_nonempty {n : ℕ}
    (hne : (goldbachCandidates n).Nonempty) :
    (goldbachBalancedCandidates n).Nonempty := by
  classical
  obtain ⟨p, hp⟩ := hne
  by_cases hle : p ≤ n - p
  · exact ⟨p, mem_goldbachBalancedCandidates.mpr ⟨hp, hle⟩⟩
  · have hc := goldbachCandidates_compl hp
    have hp_le : p ≤ n := (mem_goldbachCandidates_iff.mp hp).1
    have hlt : n - p < p := lt_of_not_ge hle
    have hbal : n - p ≤ n - (n - p) := by
      rw [Nat.sub_sub_self hp_le]
      exact le_of_lt hlt
    exact ⟨n - p, mem_goldbachBalancedCandidates.mpr ⟨hc, hbal⟩⟩

theorem candidateMismatch_eq {n p : ℕ} (hp : p ∈ goldbachCandidates n) :
    candidateMismatch n p =
      goldbachMismatchHeight p (n - p)
        (Nat.Prime.ne_zero (mem_goldbachCandidates_iff.mp hp).2.1)
        (Nat.Prime.ne_zero (mem_goldbachCandidates_iff.mp hp).2.2) := by
  simp [candidateMismatch, hp]

theorem candidateMismatch_symm {n p : ℕ} (hp : p ∈ goldbachCandidates n) :
    candidateMismatch n p = candidateMismatch n (n - p) := by
  have hc := goldbachCandidates_compl hp
  have hle : p ≤ n := (mem_goldbachCandidates_iff.mp hp).1
  have hback : n - (n - p) = p := Nat.sub_sub_self hle
  rw [candidateMismatch_eq hp, candidateMismatch_eq hc, goldbachMismatchHeight_eq,
    goldbachMismatchHeight_eq]
  unfold goldbachRapidity
  simp only [hback]
  ring

/-- The ground state is a prime pair closest to equality, and it minimises the mismatch. -/
theorem exists_goldbach_ground {n : ℕ} (hne : (goldbachCandidates n).Nonempty) :
    ∃ p ∈ goldbachBalancedCandidates n,
      (∀ q ∈ goldbachBalancedCandidates n, q ≤ p) ∧
        ∀ q ∈ goldbachCandidates n, candidateMismatch n p ≤ candidateMismatch n q := by
  classical
  have hS : (goldbachBalancedCandidates n).Nonempty :=
    goldbachBalancedCandidates_nonempty hne
  let p := (goldbachBalancedCandidates n).max' hS
  have hp : p ∈ goldbachBalancedCandidates n := Finset.max'_mem _ hS
  have hmax : ∀ q ∈ goldbachBalancedCandidates n, q ≤ p := fun q hq => Finset.le_max' _ q hq
  refine ⟨p, hp, hmax, ?_⟩
  intro q hq
  have hp_mem : p ∈ goldbachCandidates n := (mem_goldbachBalancedCandidates.mp hp).1
  have hp_bal : p ≤ n - p := (mem_goldbachBalancedCandidates.mp hp).2
  have hppos : 0 < p := Nat.Prime.pos (mem_goldbachCandidates_iff.mp hp_mem).2.1
  by_cases hbal : q ≤ n - q
  · have hqS : q ∈ goldbachBalancedCandidates n :=
      mem_goldbachBalancedCandidates.mpr ⟨hq, hbal⟩
    have hq_le : q ≤ p := hmax q hqS
    have hqpos : 0 < q := Nat.Prime.pos (mem_goldbachCandidates_iff.mp hq).2.1
    have hanti := goldbachMismatchHeight_antitone hqpos hppos hbal hp_bal hq_le
    rw [candidateMismatch_eq hq, candidateMismatch_eq hp_mem]
    rw [goldbachMismatchHeight_proof_irrel
        (Nat.Prime.ne_zero (mem_goldbachCandidates_iff.mp hq).2.1)
        (Nat.pos_iff_ne_zero.mp hqpos)
        (Nat.Prime.ne_zero (mem_goldbachCandidates_iff.mp hq).2.2)
        (Nat.pos_iff_ne_zero.mp (by omega : 0 < n - q)),
      goldbachMismatchHeight_proof_irrel
        (Nat.Prime.ne_zero (mem_goldbachCandidates_iff.mp hp_mem).2.1)
        (Nat.pos_iff_ne_zero.mp hppos)
        (Nat.Prime.ne_zero (mem_goldbachCandidates_iff.mp hp_mem).2.2)
        (Nat.pos_iff_ne_zero.mp (by omega : 0 < n - p))]
    exact hanti
  · have hc := goldbachCandidates_compl hq
    have hq_le_n : q ≤ n := (mem_goldbachCandidates_iff.mp hq).1
    have hlt : n - q < q := lt_of_not_ge hbal
    have hsmall : n - q ≤ n - (n - q) := by
      rw [Nat.sub_sub_self hq_le_n]
      exact le_of_lt hlt
    have hsmallS : n - q ∈ goldbachBalancedCandidates n :=
      mem_goldbachBalancedCandidates.mpr ⟨hc, hsmall⟩
    have hle_small : n - q ≤ p := hmax _ hsmallS
    have hp_pos_small : 0 < n - q :=
      Nat.Prime.pos (mem_goldbachCandidates_iff.mp hc).2.1
    have hanti :=
      goldbachMismatchHeight_antitone hp_pos_small hppos hsmall hp_bal hle_small
    rw [candidateMismatch_symm hq, candidateMismatch_eq hc, candidateMismatch_eq hp_mem]
    rw [goldbachMismatchHeight_proof_irrel
        (Nat.Prime.ne_zero (mem_goldbachCandidates_iff.mp hc).2.1)
        (Nat.pos_iff_ne_zero.mp hp_pos_small)
        (Nat.Prime.ne_zero (mem_goldbachCandidates_iff.mp hc).2.2)
        (Nat.pos_iff_ne_zero.mp (by omega : 0 < n - (n - q))),
      goldbachMismatchHeight_proof_irrel
        (Nat.Prime.ne_zero (mem_goldbachCandidates_iff.mp hp_mem).2.1)
        (Nat.pos_iff_ne_zero.mp hppos)
        (Nat.Prime.ne_zero (mem_goldbachCandidates_iff.mp hp_mem).2.2)
        (Nat.pos_iff_ne_zero.mp (by omega : 0 < n - p))]
    exact hanti

/-! ### Finite computational certificate -/

/-- Naive search for a Goldbach first summand. -/
def hasGoldbachPair (n : ℕ) : Bool :=
  (List.range (n + 1)).any fun p =>
    decide (Nat.Prime p ∧ p ≤ n ∧ Nat.Prime (n - p))

theorem hasGoldbachPair_sound {n : ℕ} (h : hasGoldbachPair n = true) :
    ∃ p, p ≤ n ∧ Nat.Prime p ∧ Nat.Prime (n - p) := by
  simp only [hasGoldbachPair, List.any_eq_true, decide_eq_true_eq] at h
  obtain ⟨p, hp_mem, hp⟩ := h
  have hp_lt : p < n + 1 := List.mem_range.mp hp_mem
  exact ⟨p, Nat.lt_succ_iff.mp hp_lt, hp.1, hp.2.2⟩

theorem hasGoldbachPair_of_even {n : ℕ} (he : Even n) (hn : 4 ≤ n)
    (h : hasGoldbachPair n = true) : ∃ p q, IsGoldbachPair p q n := by
  obtain ⟨p, hle, hp, hq⟩ := hasGoldbachPair_sound h
  exact ⟨p, n - p, hp, hq, Nat.add_sub_of_le hle, he, hn⟩

/-- All even integers in `4…N` admit a Goldbach pair (Bool certificate). -/
def allEvenGoldbachUpTo (N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n =>
    if decide (4 ≤ n ∧ Even n) then hasGoldbachPair n else true

theorem allEvenGoldbachUpTo_sound {N : ℕ} (h : allEvenGoldbachUpTo N = true) :
    ∀ n, 4 ≤ n → n ≤ N → Even n → ∃ p q, IsGoldbachPair p q n := by
  intro n hn4 hnN he
  have hlt : n < N + 1 := Nat.lt_succ_of_le hnN
  have hall := (List.all_eq_true.mp h) n (List.mem_range.mpr hlt)
  have hcond : decide (4 ≤ n ∧ Even n) = true := by
    simp [hn4, he]
  simp only [hcond, ↓reduceIte] at hall
  exact hasGoldbachPair_of_even he hn4 hall

/-- Chapter 9 finite-exploration certificate for even targets up to `100`. -/
theorem goldbach_of_le_hundred {n : ℕ} (hn4 : 4 ≤ n) (hn : n ≤ 100) (he : Even n) :
    ∃ p q, IsGoldbachPair p q n :=
  allEvenGoldbachUpTo_sound (by native_decide : allEvenGoldbachUpTo 100 = true) n hn4 hn he

/-! ### The cone as the stable phase -/

/-- An even target `n ≥ 4` lies outside the admissible cone. -/
theorem goldbach_target_not_admissible {n : ℕ} (hn : 4 ≤ n) :
    ¬ Discrete.IsAdmissibleContinuous (pureBoost (2 * Real.log (n : ℝ))) := by
  intro hadm
  have hpos : 0 < n := by omega
  have hmem := (positive_integer_boost_admissible_iff hpos).mp hadm
  omega

/-- The pair `2 + 2 = 4` is Goldbach, and both summands lie on the stable phase. -/
theorem goldbach_two_two : IsGoldbachPair 2 2 4 :=
  ⟨by decide, by decide, by decide, even_iff_two_dvd.mpr ⟨2, by decide⟩, by decide⟩

theorem goldbach_two_two_in_cone :
    Discrete.IsAdmissibleContinuous (pureBoost (2 * Real.log (2 : ℝ))) :=
  (prime_boost_admissible_iff (by decide : Nat.Prime 2)).mpr rfl

/-- A summand on the stable phase forces the pair `2 + 2 = 4`. -/
theorem goldbach_summand_in_cone {p q n : ℕ} (h : IsGoldbachPair p q n)
    (hadm : Discrete.IsAdmissibleContinuous (pureBoost (2 * Real.log (p : ℝ)))) :
    p = 2 ∧ q = 2 ∧ n = 4 := by
  obtain ⟨hp, hq, hsum, heven, _⟩ := h
  have hp2 : p = 2 := (prime_boost_admissible_iff hp).mp hadm
  subst hp2
  have hqmod : q % 2 = 0 := by
    have hnmod : n % 2 = 0 := Nat.even_iff.mp heven
    have hsum' : n = 2 + q := hsum.symm
    omega
  rcases Nat.Prime.eq_two_or_odd hq with hq2 | hqodd
  · subst hq2
    exact ⟨rfl, rfl, by omega⟩
  · omega

/-- For every even target `n ≥ 6`, both summands lie outside the cone. -/
theorem goldbach_pair_outside_cone {p q n : ℕ} (h : IsGoldbachPair p q n) (hn : 6 ≤ n) :
    ¬ Discrete.IsAdmissibleContinuous (pureBoost (2 * Real.log (p : ℝ))) ∧
      ¬ Discrete.IsAdmissibleContinuous (pureBoost (2 * Real.log (q : ℝ))) := by
  refine ⟨?_, ?_⟩
  · intro hadm
    have := goldbach_summand_in_cone h hadm
    omega
  · intro hadm
    have := goldbach_summand_in_cone (isGoldbachPair_symm h) hadm
    omega

/-- The pair `3 + 3 = 6` is Goldbach, and both summands lie in the shell. -/
theorem goldbach_three_three : IsGoldbachPair 3 3 6 :=
  ⟨by decide, by decide, by decide, even_iff_two_dvd.mpr ⟨3, by decide⟩, by decide⟩

theorem goldbach_three_in_shell :
    ¬ Discrete.IsAdmissibleContinuous (pureBoost (2 * Real.log (3 : ℝ))) ∧
      collatzHeight 3 (by decide : (3 : ℕ) ≠ 0) < 1 :=
  (prime_shell_iff (by decide : Nat.Prime 3)).mpr rfl

/-- Both summands lie in the shell only for `3 + 3 = 6`. -/
theorem goldbach_both_shell {p q n : ℕ} (h : IsGoldbachPair p q n)
    (hp : ¬ Discrete.IsAdmissibleContinuous (pureBoost (2 * Real.log (p : ℝ))) ∧
      collatzHeight p (Nat.pos_iff_ne_zero.mp (Nat.Prime.pos h.1)) < 1)
    (hq : ¬ Discrete.IsAdmissibleContinuous (pureBoost (2 * Real.log (q : ℝ))) ∧
      collatzHeight q (Nat.pos_iff_ne_zero.mp (Nat.Prime.pos h.2.1)) < 1) :
    p = 3 ∧ q = 3 ∧ n = 6 := by
  have hp3 : p = 3 := (prime_shell_iff h.1).mp hp
  have hq3 : q = 3 := (prime_shell_iff h.2.1).mp hq
  subst hp3
  subst hq3
  obtain ⟨_, _, hsum, _, _⟩ := h
  exact ⟨rfl, rfl, by omega⟩

/-- For every even target `n ≥ 8`, the larger summand is at least `5`. -/
theorem goldbach_max_ge_five {p q n : ℕ} (h : IsGoldbachPair p q n) (hn : 8 ≤ n) :
    5 ≤ max p q := by
  have hout := goldbach_pair_outside_cone h (by omega)
  obtain ⟨hp, hq, hsum, _, _⟩ := h
  have hpge : 3 ≤ p := by
    have hne : p ≠ 2 := by
      intro hp2
      exact hout.1 ((prime_boost_admissible_iff hp).mpr hp2)
    have := Nat.Prime.two_le hp
    omega
  have hqge : 3 ≤ q := by
    have hne : q ≠ 2 := by
      intro hq2
      exact hout.2 ((prime_boost_admissible_iff hq).mpr hq2)
    have := Nat.Prime.two_le hq
    omega
  by_contra hlt
  have hmax : max p q ≤ 4 := by omega
  have hp4 : p ≤ 4 := le_trans (le_max_left p q) hmax
  have hq4 : q ≤ 4 := le_trans (le_max_right p q) hmax
  have hp3 : p = 3 := by
    interval_cases p
    · rfl
    · exact absurd hp (by decide : ¬ Nat.Prime 4)
  have hq3 : q = 3 := by
    interval_cases q
    · rfl
    · exact absurd hq (by decide : ¬ Nat.Prime 4)
  omega

/-- The larger summand of an even target `n ≥ 8` has height greater than one. -/
theorem goldbach_larger_summand_height {p q n : ℕ} (h : IsGoldbachPair p q n) (hn : 8 ≤ n) :
    1 < collatzHeight (max p q)
      (Nat.pos_iff_ne_zero.mp
        (Nat.lt_of_lt_of_le (by decide : 0 < 5) (goldbach_max_ge_five h hn))) :=
  collatzHeight_ge_four_gt_one
    (le_trans (by decide : 4 ≤ 5) (goldbach_max_ge_five h hn))

/-! ### Classical Goldbach under an explicit bridge hypothesis -/

/--
Paper Chapter 9's missing bridge: a classical Goldbach counterexample forces the
pure-boost integer embedding of `n` to be an admissible continuous configuration
(so that `goldbachTargetHeight n > 1` would contradict `torsion_bound_continuous`).

This proposition is **not** proved in this development: for `n ≥ 4` the boost
angle `2 log n` already exits the principal admissible chamber.
-/
def GoldbachAdmissibleBridge : Prop :=
  ∀ n : ℕ, Even n → 4 ≤ n →
    (¬ ∃ p q, IsGoldbachPair p q n) →
      IsAdmissibleContinuous (pureBoost (2 * Real.log n))

/-- Conditional DST recovery of the Goldbach conjecture. -/
theorem goldbach_conjecture_of_bridge (hbridge : GoldbachAdmissibleBridge) :
    ∀ n : ℕ, Even n → 4 ≤ n → ∃ p q, IsGoldbachPair p q n := by
  intro n he hn4
  by_contra hnone
  have hadm := hbridge n he hn4 hnone
  have hgt := goldbachTargetHeight_gt_one_of_four_le hn4
  have hbound := torsion_bound_continuous _ hadm
  unfold goldbachTargetHeight integerHeight torsionHeight at hgt
  have hparams : pureBoost (2 * Real.log (Int.natAbs (n : ℤ))) =
      pureBoost (2 * Real.log n) := by simp
  rw [hparams] at hgt
  exact (not_le_of_gt hgt) hbound

theorem goldbachAdmissibleBridge_of_pairs
    (h : ∀ n : ℕ, Even n → 4 ≤ n → ∃ p q, IsGoldbachPair p q n) :
    GoldbachAdmissibleBridge := by
  intro n he hn4 hnone
  exact absurd (h n he hn4) hnone

/-- The bridge holds exactly when every even target has a prime pair. -/
theorem goldbachAdmissibleBridge_iff :
    GoldbachAdmissibleBridge ↔
      (∀ n : ℕ, Even n → 4 ≤ n → ∃ p q, IsGoldbachPair p q n) :=
  ⟨goldbach_conjecture_of_bridge, goldbachAdmissibleBridge_of_pairs⟩

end Theorems

end DstDiophantine
