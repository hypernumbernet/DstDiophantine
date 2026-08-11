import DstDiophantine.Framework.Representation
import DstDiophantine.Embedding.PowerMap
import DstDiophantine.Embedding.Height
import DstDiophantine.Algebra.Amplification
import DstDiophantine.Algebra.Invariant
import DstDiophantine.Algebra.Discrete
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option linter.style.nativeDecide false

/-!
# Phase 5: Goldbach conjecture (DST additive / height core)

We formalise Chapter 9 of `dst-diophantine.tex` as a **null-translator
decomposition + torsional height** argument, together with a finite
computational certificate and a bridge hypothesis recovering the classical
statement.

## Paper gap (not closed)

Classical Goldbach (`∀ even n ≥ 4, ∃ primes p,q with p+q=n`) is **not** claimed
unconditionally. The paper's step “no prime pair ⇒ irreducible composite rotor
⇒ `J_norm(2n) > 1`” conflates additive decompositions with the multiplicative
integer-rotor height: `integerHeight n` is always `≍ (log n)²`, independently of
whether a Goldbach pair exists. Encoding a Goldbach counterexample as an
*admissible* pure-boost configuration is left as `GoldbachAdmissibleBridge`.
The Lean coefficient of `integerHeight` is `16/(3π²)` (from `JNormalized`); the
paper’s shorter display formula differs by a constant factor and is not used.
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

/-! ### Pair mismatch height and finite minimisers -/

/-- Pure-boost mismatch height between two positive summands (model for `J_pq`). -/
noncomputable def goldbachMismatchHeight (p q : ℕ) (hp : p ≠ 0) (hq : q ≠ 0) : ℝ :=
  |JNormalized (logMismatch (p : ℤ) (q : ℤ) (Int.natCast_ne_zero.mpr hp)
      (Int.natCast_ne_zero.mpr hq))|

theorem goldbachMismatchHeight_nonneg (p q : ℕ) (hp : p ≠ 0) (hq : q ≠ 0) :
    0 ≤ goldbachMismatchHeight p q hp hq :=
  abs_nonneg _

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

end Theorems

end DstDiophantine
