import DstDiophantine.Theorems.Collatz
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

set_option linter.style.native false

/-!
# Phase 5: Goldbach conjecture (DST additive / height core)

We formalise Chapter 9 of `dst-diophantine.tex` as a **null-translator
decomposition + torsional height** argument, together with a finite
computational certificate and a bridge hypothesis recovering the classical
statement.

## The cone as the stable phase

The integer boost of an even target `n ≥ 4` lies beyond unit height, so the
target is outside both the admissible cone and the shell `{3}`. The only prime
on the stable phase is `2`, and the only Goldbach pair that meets the phase is
`2 + 2 = 4`. For every even `n ≥ 6` both summands lie outside the cone. The
only pair with both summands in the shell is `3 + 3 = 6`. For every even
`n ≥ 8` the larger summand is at least `5` and its height exceeds one.

## Paper gap (not closed)

Classical Goldbach (`∀ even n ≥ 4, ∃ primes p,q with p+q=n`) is **not** claimed
unconditionally. `integerHeight n` is `≍ (log n)²` whether or not a prime pair
exists. `GoldbachAdmissibleBridge` asks a missing pair to make the target
admissible. No even `n ≥ 4` is admissible, so the bridge holds if and only if
the conjecture does (`goldbachAdmissibleBridge_iff`). It is not a reduction.
The coefficient of `integerHeight` is `16/(3π²)`.
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
