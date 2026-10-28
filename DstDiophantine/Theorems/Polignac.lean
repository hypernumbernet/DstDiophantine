import DstDiophantine.Theorems.Collatz
import DstDiophantine.Framework.Representation
import DstDiophantine.Embedding.Height
import DstDiophantine.Algebra.Amplification
import DstDiophantine.Algebra.Invariant
import DstDiophantine.Algebra.Discrete
import Mathlib.Algebra.Ring.Parity
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option linter.style.native false

/-!
# Phase 5: Polignac / twin primes (DST even-gap core)

We formalise Chapter 9 of `dst-diophantine.tex` as an **even-gap null-translator
+ cumulative excess height** argument. Twin primes are the special case `k = 1`.

## The cone as the stable phase

The partner of `2` by an even gap `2k > 0` is composite, so no Polignac pair
meets the admissible cone. The smaller member is an odd prime. It lies in the
shell if and only if it is `3`, and the partner then has height greater than
one, as does the partner of every other pair. A pair with smaller member at
least `5` has height greater than one at both vertices.

The gap integer `2k` itself lies on the stable phase if and only if `k = 1`.
Every wider gap has height greater than one.

## Relative rotor

For `q = p + 2k` the rapidity is `δ = log(q/p)`, the same rapidity as the
Goldbach sum channel (`AdditivePhase`). The two channels are the one hyperbola
`(n/2)² - k² = pq`. The relative rotor is the pure
boost of angle `2δ`, with mismatch `J = 2δ²`. The gap is positive, so the
mismatch is positive. The half-gap and the geometric mean are tied by
`k = √(pq) sinh(δ/2)`. Once `p ≥ 2k`, the ratio is at most `2`, so the relative
rotor lies in the cone; every twin pair is in this range, while neither prime
meets the phase. The pair `(3, 7)` has gap `4` and relative angle past `π/2`.
The pair `(7, 11)` has the same gap and an admissible relative rotor. For fixed
`k` the normalised height is strictly less than `(16/(3π²))(2k/p)²`, which
falls below every positive tolerance.

## Paper gap (not closed)

Classical Polignac (`∀ k > 0, infinitely many primes p with p+2k also prime`) is
**not** claimed unconditionally. A gap smaller than `2k` contributes a negative
excess, so omitting one even value does not force the model height above one.
A positive lower bound holds only under **strong avoidance** `g_n ≥ 2k + 2`.
An admissible pure boost has height at most one, whether or not the Polignac
set is finite, so `PolignacAdmissibleBridge` has no witness. The bridge holds
if and only if the conjecture does (`polignacAdmissibleBridge_iff`). It is not
a reduction.
-/

namespace DstDiophantine

namespace Theorems

open Amplification Discrete Invariant Real
open _root_.DstDiophantine.Embedding
open _root_.DstDiophantine.Framework

/-! ### Even gaps and Polignac pairs -/

/-- Even gap `2k` associated to a positive integer `k`. -/
def evenGap (k : ℕ) : ℕ :=
  2 * k

/-- Polignac pair for gap `2k`: primes `p` and `p + 2k`. -/
def IsPolignacPair (p k : ℕ) : Prop :=
  Nat.Prime p ∧ Nat.Prime (p + 2 * k) ∧ 0 < k

/-- Twin-prime pair: Polignac with gap `2`. -/
def IsTwinPrimePair (p : ℕ) : Prop :=
  IsPolignacPair p 1

theorem twinPrimePair_iff (p : ℕ) :
    IsTwinPrimePair p ↔ Nat.Prime p ∧ Nat.Prime (p + 2) := by
  constructor
  · intro ⟨hp, hq, _⟩
    exact ⟨hp, hq⟩
  · intro ⟨hp, hq⟩
    exact ⟨hp, hq, Nat.succ_pos 0⟩

theorem twin_prime_of_polignac {p : ℕ} (h : IsPolignacPair p 1) :
    IsTwinPrimePair p :=
  h

/-! ### Null-translator encoding of even gaps -/

theorem polignac_gap_iff_motor (p q k : ℤ) :
    q = p + 2 * k ↔ powerSumMotor (gapEquation p q k) = 1 :=
  (gapMotor_one_iff p q k).symm

theorem polignac_solution_iff_motor {p k : ℕ} (_h : IsPolignacPair p k) :
    powerSumMotor (gapEquation (p : ℤ) ((p + 2 * k : ℕ) : ℤ) (k : ℤ)) = 1 := by
  rw [gapMotor_one_iff]
  norm_cast

/-! ### Even-gap admissibility (paper `lem:even-gap-admissible` core) -/

theorem even_gap_of_odd_nats {p q : ℕ}
    (hp : p % 2 = 1) (hq : q % 2 = 1) (hle : p ≤ q) : Even (q - p) := by
  refine Nat.even_iff.mpr ?_
  have : (q - p) % 2 = 0 := by omega
  exact this

theorem even_gap_of_odd_prime_pair {p q : ℕ}
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hp2 : p ≠ 2) (hq2 : q ≠ 2)
    (hle : p ≤ q) : Even (q - p) :=
  even_gap_of_odd_nats (hp.mod_two_eq_one_iff_ne_two.mpr hp2)
    (hq.mod_two_eq_one_iff_ne_two.mpr hq2) hle

/-! ### Cumulative gap excess and chain height -/

/-- Single excess term `(g - 2k) / p`. -/
noncomputable def gapExcessTerm (g p k : ℕ) : ℝ :=
  ((g : ℝ) - (2 * k : ℝ)) / (p : ℝ)

/-- Partial excess sum along parallel gap / prime lists of equal length. -/
noncomputable def gapExcessSum (gs ps : List ℕ) (k : ℕ) : ℝ :=
  (List.zipWith (fun g p => gapExcessTerm g p k) gs ps).sum

/-- Pure-boost height of a cumulative excess scalar (model for `J(Σ_M)`). -/
noncomputable def gapChainHeight (S : ℝ) : ℝ :=
  |JNormalized (pureBoost S)|

theorem gapChainHeight_eq (S : ℝ) :
    gapChainHeight S = (4 / (3 * Real.pi ^ 2)) * S ^ 2 := by
  unfold gapChainHeight
  rw [JNormalized_coef]
  simp only [pureBoost, Fin.sum_univ_three, zero_pow two_ne_zero, sub_zero, add_zero]
  have hnonneg : 0 ≤ (4 / (3 * Real.pi ^ 2)) * S ^ 2 := by positivity
  exact abs_of_nonneg hnonneg

/-- Strong avoidance: each gap is at least two more than the target even gap. -/
theorem strong_avoidance_term_ge {g p k : ℕ} (hp : 0 < p) (hg : 2 * k + 2 ≤ g) :
    (2 : ℝ) / p ≤ gapExcessTerm g p k := by
  unfold gapExcessTerm
  have hppos : 0 < (p : ℝ) := Nat.cast_pos.mpr hp
  have hle_sub : 2 * k ≤ g := Nat.le_of_add_right_le hg
  have hsub : (2 : ℕ) ≤ g - 2 * k := Nat.le_sub_of_add_le (by linarith [hg])
  have hnum : (2 : ℝ) ≤ (g : ℝ) - (2 * k : ℝ) := by
    have : ((g - 2 * k : ℕ) : ℝ) = (g : ℝ) - (2 * k : ℝ) := by
      rw [Nat.cast_sub hle_sub]
      norm_cast
    have h2 : (2 : ℝ) ≤ ((g - 2 * k : ℕ) : ℝ) := Nat.cast_le.mpr hsub
    rwa [← this]
  exact (div_le_div_iff_of_pos_right hppos).mpr hnum

theorem strong_avoidance_singleton {g p k : ℕ} (hp : 0 < p) (hg : 2 * k + 2 ≤ g) :
    (2 : ℝ) / p ≤ gapExcessSum [g] [p] k := by
  simpa [gapExcessSum, List.zipWith] using strong_avoidance_term_ge hp hg

theorem strong_avoidance_pair {g₁ g₂ p₁ p₂ k : ℕ}
    (hp1 : 0 < p₁) (hp2 : 0 < p₂)
    (hg1 : 2 * k + 2 ≤ g₁) (hg2 : 2 * k + 2 ≤ g₂) :
    (2 : ℝ) / p₁ + (2 : ℝ) / p₂ ≤ gapExcessSum [g₁, g₂] [p₁, p₂] k := by
  have h1 := strong_avoidance_term_ge hp1 hg1
  have h2 := strong_avoidance_term_ge hp2 hg2
  simp [gapExcessSum, List.zipWith]
  linarith

/-- A gap strictly below the chosen even gap contributes a negative excess. -/
theorem gapExcessTerm_neg_of_smaller {g p k : ℕ} (hp : 0 < p) (hg : g < 2 * k) :
    gapExcessTerm g p k < 0 := by
  unfold gapExcessTerm
  have hnum : (g : ℝ) - (2 * (k : ℝ)) < 0 := by
    have : (g : ℝ) < 2 * (k : ℝ) := by exact_mod_cast hg
    linarith
  exact div_neg_of_neg_of_pos hnum (by exact_mod_cast hp)

theorem gapChainHeight_gt_one_of_sq {S : ℝ}
    (h : (3 * Real.pi ^ 2) / 4 < S ^ 2) :
    1 < gapChainHeight S := by
  rw [gapChainHeight_eq]
  have hden : 0 < 3 * Real.pi ^ 2 := by positivity
  have h' : 3 * Real.pi ^ 2 < 4 * S ^ 2 := by
    have := (div_lt_iff₀ (by norm_num : (0 : ℝ) < 4)).mp h
    linarith
  have hform : 1 < (4 * S ^ 2) / (3 * Real.pi ^ 2) := (one_lt_div hden).mpr h'
  convert hform using 1
  ring

theorem gapChainHeight_gt_one_of_term {g p k : ℕ} (hp : 0 < p)
    (hg : 2 * k + 2 ≤ g)
    (hlarge : (3 * Real.pi ^ 2) / 4 < ((2 : ℝ) / p) ^ 2) :
    1 < gapChainHeight (gapExcessSum [g] [p] k) := by
  have hge := strong_avoidance_singleton hp hg
  have hpos : 0 ≤ (2 : ℝ) / p := div_nonneg (by norm_num) (Nat.cast_nonneg _)
  have hsq : ((2 : ℝ) / p) ^ 2 ≤ (gapExcessSum [g] [p] k) ^ 2 := by
    rw [pow_two, pow_two]
    exact mul_le_mul hge hge hpos (le_trans hpos hge)
  exact gapChainHeight_gt_one_of_sq (lt_of_lt_of_le hlarge hsq)

/-! ### Small certificates -/

theorem polignac_three_one : IsPolignacPair 3 1 := by
  refine ⟨?_, ?_, Nat.succ_pos 0⟩
  · native_decide
  · native_decide

theorem twin_three_five : IsTwinPrimePair 3 :=
  twin_prime_of_polignac polignac_three_one

theorem polignac_three_two : IsPolignacPair 3 2 := by
  refine ⟨?_, ?_, by decide⟩
  · native_decide
  · native_decide

theorem polignac_seven_three : IsPolignacPair 7 3 := by
  refine ⟨?_, ?_, by decide⟩
  · native_decide
  · native_decide

/-- Search for a Polignac first component `p ≤ N` for fixed gap parameter `k`. -/
def hasPolignacPairUpTo (N k : ℕ) : Bool :=
  (List.range (N + 1)).any fun p =>
    decide (0 < k ∧ Nat.Prime p ∧ Nat.Prime (p + 2 * k))

theorem hasPolignacPairUpTo_sound {N k : ℕ} (h : hasPolignacPairUpTo N k = true) :
    ∃ p ≤ N, IsPolignacPair p k := by
  simp only [hasPolignacPairUpTo, List.any_eq_true, decide_eq_true_eq] at h
  obtain ⟨p, hp_mem, hk, hp, hq⟩ := h
  exact ⟨p, Nat.lt_succ_iff.mp (List.mem_range.mp hp_mem), hp, hq, hk⟩

theorem exists_twin_of_le_twenty :
    ∃ p ≤ 20, IsTwinPrimePair p := by
  obtain ⟨p, hp, hpair⟩ :=
    hasPolignacPairUpTo_sound (by native_decide : hasPolignacPairUpTo 20 1 = true)
  exact ⟨p, hp, hpair⟩

theorem exists_polignac_gap_four_of_le_thirty :
    ∃ p ≤ 30, IsPolignacPair p 2 :=
  hasPolignacPairUpTo_sound (by native_decide : hasPolignacPairUpTo 30 2 = true)

theorem exists_polignac_gap_six_of_le_thirty :
    ∃ p ≤ 30, IsPolignacPair p 3 :=
  hasPolignacPairUpTo_sound (by native_decide : hasPolignacPairUpTo 30 3 = true)

/-! ### The cone as the stable phase -/

/-- The even translate of `2` by a positive gap is composite. -/
theorem polignac_two_partner_composite {k : ℕ} (hk : 0 < k) :
    ¬ Nat.Prime (2 + 2 * k) := by
  refine Nat.not_prime_of_dvd_of_lt ?_ (by decide : 1 < 2) ?_
  · exact ⟨1 + k, by ring⟩
  · omega

/-- No Polignac pair has smaller member `2`. -/
theorem polignac_not_two {p k : ℕ} (h : IsPolignacPair p k) : p ≠ 2 := by
  intro hp2
  have hprime : Nat.Prime (p + 2 * k) := h.2.1
  rw [hp2] at hprime
  exact polignac_two_partner_composite h.2.2 hprime

/-- Neither member of a Polignac pair lies on the stable phase. -/
theorem polignac_outside_cone {p k : ℕ} (h : IsPolignacPair p k) :
    ¬ Discrete.IsAdmissibleContinuous (pureBoost (2 * Real.log (p : ℝ))) ∧
      ¬ Discrete.IsAdmissibleContinuous
        (pureBoost (2 * Real.log ((p + 2 * k : ℕ) : ℝ))) := by
  refine ⟨?_, ?_⟩
  · intro hadm
    exact polignac_not_two h ((prime_boost_admissible_iff h.1).mp hadm)
  · intro hadm
    have hq2 : p + 2 * k = 2 := (prime_boost_admissible_iff h.2.1).mp hadm
    have hpge : 2 ≤ p := Nat.Prime.two_le h.1
    have hk : 0 < k := h.2.2
    omega

/-- The smaller member lies in the shell if and only if it is `3`. -/
theorem polignac_smaller_shell_iff {p k : ℕ} (h : IsPolignacPair p k) :
    (¬ Discrete.IsAdmissibleContinuous (pureBoost (2 * Real.log (p : ℝ))) ∧
        collatzHeight p (Nat.pos_iff_ne_zero.mp (Nat.Prime.pos h.1)) < 1) ↔
      p = 3 :=
  prime_shell_iff h.1

/-- The partner of every Polignac pair has height greater than one. -/
theorem polignac_partner_height {p k : ℕ} (h : IsPolignacPair p k) :
    1 < collatzHeight (p + 2 * k)
      (Nat.pos_iff_ne_zero.mp (Nat.Prime.pos h.2.1)) := by
  have hp : 3 ≤ p := by
    have hne := polignac_not_two h
    have := Nat.Prime.two_le h.1
    omega
  have hk : 0 < k := h.2.2
  have h5 : 5 ≤ p + 2 * k := by omega
  exact collatzHeight_ge_four_gt_one (le_trans (by decide : 4 ≤ 5) h5)

/-- A smaller member at least `5` has height greater than one. -/
theorem polignac_smaller_height {p k : ℕ} (h : IsPolignacPair p k) (hp : 5 ≤ p) :
    1 < collatzHeight p (Nat.pos_iff_ne_zero.mp (Nat.Prime.pos h.1)) :=
  collatzHeight_ge_four_gt_one (by omega)

/-- The first twin meets the shell at `3`, and `5` lies beyond unit height. -/
theorem twin_three_five_phase :
    (¬ Discrete.IsAdmissibleContinuous (pureBoost (2 * Real.log (3 : ℝ))) ∧
        collatzHeight 3 (by decide : (3 : ℕ) ≠ 0) < 1) ∧
      1 < collatzHeight 5 (by decide : (5 : ℕ) ≠ 0) := by
  refine ⟨(prime_shell_iff (by decide : Nat.Prime 3)).mpr rfl, ?_⟩
  exact collatzHeight_ge_four_gt_one (by decide : 4 ≤ 5)

/-- An admissible pure boost never has gap-chain height greater than one. -/
theorem gapChainHeight_admissible_le_one {S : ℝ}
    (hadm : IsAdmissibleContinuous (pureBoost S)) :
    gapChainHeight S ≤ 1 := by
  simpa [gapChainHeight] using torsion_bound_continuous (pureBoost S) hadm

theorem polignac_admissible_witness_empty :
    ¬ ∃ S : ℝ, IsAdmissibleContinuous (pureBoost S) ∧ 1 < gapChainHeight S := by
  intro ⟨S, hadm, hgt⟩
  exact not_lt_of_ge (gapChainHeight_admissible_le_one hadm) hgt

/-! ### The gap integer on the axis -/

/-- The even gap `2k` lies on the stable phase if and only if it is the twin gap. -/
theorem polignac_gap_phase_iff {k : ℕ} (hk : 0 < k) :
    IsAdmissibleContinuous (pureBoost (2 * Real.log ((2 * k : ℕ) : ℝ))) ↔ k = 1 := by
  have hpos : 0 < 2 * k := by omega
  rw [positive_integer_boost_admissible_iff hpos]
  constructor
  · intro h
    rcases h with h1 | h2
    · omega
    · omega
  · intro hk1
    subst hk1
    exact Or.inr rfl

/-- Every even gap wider than `2` has integer height greater than one. -/
theorem polignac_wide_gap_height {k : ℕ} (hk : 2 ≤ k) :
    1 < collatzHeight (2 * k) (by omega : 2 * k ≠ 0) :=
  collatzHeight_ge_four_gt_one (by omega : 4 ≤ 2 * k)

/-! ### Relative rotor of a pair

The rapidity is `δ = log((p+2k)/p)`. The relative rotor is the pure boost of
angle `2δ`, so the mismatch is `J = 2δ²`, on the same scale as an integer boost.
-/

/-- Rapidity of the ratio `(p + 2k) / p`. -/
noncomputable def polignacRapidity (p k : ℕ) (_hp : p ≠ 0) : ℝ :=
  Real.log ((p + 2 * k : ℕ) : ℝ) - Real.log (p : ℝ)

theorem polignacRapidity_eq_log_div {p k : ℕ} (hp : 0 < p) :
    polignacRapidity p k (Nat.pos_iff_ne_zero.mp hp) =
      Real.log (((p + 2 * k : ℕ) : ℝ) / p) := by
  unfold polignacRapidity
  rw [Real.log_div (by exact_mod_cast (show p + 2 * k ≠ 0 by omega)) (by exact_mod_cast hp.ne')]

/-- Mismatch scalar of `R(p)† R(p+2k)`. The rotor angle is `2δ`, so `J = 2δ²`. -/
noncomputable def polignacMismatch (p k : ℕ) (hp : p ≠ 0) : ℝ :=
  J (pureBoost (2 * polignacRapidity p k hp))

theorem polignacMismatch_eq (p k : ℕ) (hp : p ≠ 0) :
    polignacMismatch p k hp = 2 * (polignacRapidity p k hp) ^ 2 := by
  unfold polignacMismatch
  rw [J_pureBoost]
  ring

/-- Normalised height of the relative rotor. -/
noncomputable def polignacMismatchHeight (p k : ℕ) (hp : p ≠ 0) : ℝ :=
  |JNormalized (pureBoost (2 * polignacRapidity p k hp))|

theorem polignacMismatchHeight_eq (p k : ℕ) (hp : p ≠ 0) :
    polignacMismatchHeight p k hp =
      (16 / (3 * Real.pi ^ 2)) * (polignacRapidity p k hp) ^ 2 := by
  unfold polignacMismatchHeight
  rw [JNormalized_pureBoost]
  have hnonneg :
      0 ≤ (4 / (3 * Real.pi ^ 2)) * (2 * polignacRapidity p k hp) ^ 2 := by
    positivity
  rw [abs_of_nonneg hnonneg]
  ring

theorem polignac_rapidity_pos {p k : ℕ} (hp : 0 < p) (hk : 0 < k) :
    0 < polignacRapidity p k (Nat.pos_iff_ne_zero.mp hp) := by
  rw [polignacRapidity_eq_log_div hp]
  rw [Real.log_pos_iff (by positivity)]
  rw [one_lt_div (by exact_mod_cast hp)]
  exact_mod_cast (show p < p + 2 * k by omega)

theorem polignac_mismatch_pos {p k : ℕ} (h : IsPolignacPair p k) :
    0 < polignacMismatch p k (Nat.Prime.ne_zero h.1) := by
  rw [polignacMismatch_eq]
  have hδ := polignac_rapidity_pos (Nat.Prime.pos h.1) h.2.2
  have hsq : 0 < (polignacRapidity p k (Nat.Prime.ne_zero h.1)) ^ 2 := sq_pos_of_pos hδ
  nlinarith

/-- Half-gap equals the geometric mean times `sinh` of half the mismatch rapidity. -/
theorem polignac_equation_of_state {p k : ℕ} (h : IsPolignacPair p k) :
    (k : ℝ) =
      Real.sqrt ((p : ℝ) * (p + 2 * k : ℕ)) *
        Real.sinh (polignacRapidity p k (Nat.Prime.ne_zero h.1) / 2) := by
  set hp0 : p ≠ 0 := Nat.Prime.ne_zero h.1
  set q : ℕ := p + 2 * k
  set δ : ℝ := polignacRapidity p k hp0
  have hp : 0 < p := Nat.Prime.pos h.1
  have hq : 0 < q := Nat.Prime.pos h.2.1
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hsp : 0 < Real.sqrt (p : ℝ) := Real.sqrt_pos.mpr hp'
  have hsq : 0 < Real.sqrt (q : ℝ) := Real.sqrt_pos.mpr hq'
  have hexp : Real.exp (δ / 2) = Real.sqrt (q : ℝ) / Real.sqrt (p : ℝ) := by
    have hlogp : Real.log (Real.sqrt (p : ℝ)) = Real.log (p : ℝ) / 2 := Real.log_sqrt hp'.le
    have hlogq : Real.log (Real.sqrt (q : ℝ)) = Real.log (q : ℝ) / 2 := Real.log_sqrt hq'.le
    have hδ : δ / 2 = Real.log (Real.sqrt (q : ℝ)) - Real.log (Real.sqrt (p : ℝ)) := by
      unfold δ polignacRapidity
      rw [hlogp, hlogq]
      ring
    rw [hδ, Real.exp_sub, Real.exp_log hsq, Real.exp_log hsp]
  have hexpNeg : Real.exp (-(δ / 2)) = Real.sqrt (p : ℝ) / Real.sqrt (q : ℝ) := by
    have hlogp : Real.log (Real.sqrt (p : ℝ)) = Real.log (p : ℝ) / 2 := Real.log_sqrt hp'.le
    have hlogq : Real.log (Real.sqrt (q : ℝ)) = Real.log (q : ℝ) / 2 := Real.log_sqrt hq'.le
    have hδ : -(δ / 2) = Real.log (Real.sqrt (p : ℝ)) - Real.log (Real.sqrt (q : ℝ)) := by
      unfold δ polignacRapidity
      rw [hlogp, hlogq]
      ring
    rw [hδ, Real.exp_sub, Real.exp_log hsp, Real.exp_log hsq]
  have hsqrt : Real.sqrt ((p : ℝ) * q) = Real.sqrt (p : ℝ) * Real.sqrt (q : ℝ) :=
    Real.sqrt_mul hp'.le q
  have hs :
      Real.sqrt ((p : ℝ) * q) * Real.sinh (δ / 2) = ((q : ℝ) - p) / 2 := by
    rw [Real.sinh_eq, hexp, hexpNeg, hsqrt]
    field_simp
    rw [pow_two, pow_two, Real.mul_self_sqrt hq'.le, Real.mul_self_sqrt hp'.le]
  have hgap : ((q : ℝ) - p) / 2 = (k : ℝ) := by
    have hqcast : (q : ℝ) = (p : ℝ) + 2 * (k : ℝ) := by
      dsimp [q]
      push_cast
      ring
    rw [hqcast]
    ring
  have hprod : (p : ℝ) * (p + 2 * k : ℕ) = (p : ℝ) * q := by
    dsimp [q]
  rw [hprod, hs, hgap]

/-- Once the smaller member is at least the gap, the ratio is at most `2`. -/
theorem polignac_ratio_le_two {p k : ℕ} (hp : 0 < p) (hge : 2 * k ≤ p) :
    ((p + 2 * k : ℕ) : ℝ) / p ≤ 2 := by
  rw [div_le_iff₀ (by exact_mod_cast hp)]
  exact_mod_cast (show p + 2 * k ≤ 2 * p by omega)

/-- The relative rotor lies in the cone when the smaller member is at least the gap. -/
theorem polignac_relative_admissible {p k : ℕ} (h : IsPolignacPair p k) (hge : 2 * k ≤ p) :
    IsAdmissibleContinuous
      (pureBoost (2 * polignacRapidity p k (Nat.Prime.ne_zero h.1))) := by
  rw [isAdmissibleContinuous_pureBoost_iff]
  have hp : 0 < p := Nat.Prime.pos h.1
  rw [polignacRapidity_eq_log_div hp]
  have hratio := polignac_ratio_le_two hp hge
  have hlog :
      Real.log (((p + 2 * k : ℕ) : ℝ) / p) ≤ Real.log 2 :=
    (Real.log_le_log_iff (by positivity) (by positivity)).mpr hratio
  have hmul :
      2 * Real.log (((p + 2 * k : ℕ) : ℝ) / p) ≤ 2 * Real.log 2 :=
    mul_le_mul_of_nonneg_left hlog (by norm_num)
  have hlt : 2 * Real.log 2 < Real.pi / 2 := two_log_two_lt_pi_div_two
  refine ⟨?_, le_trans hmul hlt.le⟩
  have hge1 : (1 : ℝ) ≤ ((p + 2 * k : ℕ) : ℝ) / p := by
    rw [one_le_div (by exact_mod_cast hp)]
    exact_mod_cast (show p ≤ p + 2 * k by omega)
  have hlog0 : 0 ≤ Real.log (((p + 2 * k : ℕ) : ℝ) / p) := Real.log_nonneg hge1
  positivity

/-- Every twin pair has an admissible relative rotor, positive mismatch, and both
primes off the stable phase. -/
theorem twin_relative_admissible {p : ℕ} (h : IsTwinPrimePair p) :
    IsAdmissibleContinuous
        (pureBoost (2 * polignacRapidity p 1 (Nat.Prime.ne_zero h.1))) ∧
      0 < polignacMismatch p 1 (Nat.Prime.ne_zero h.1) ∧
      ¬ IsAdmissibleContinuous (pureBoost (2 * Real.log (p : ℝ))) ∧
      ¬ IsAdmissibleContinuous (pureBoost (2 * Real.log ((p + 2 : ℕ) : ℝ))) := by
  have hpair : IsPolignacPair p 1 := h
  have hp3 : 3 ≤ p := by
    have hne := polignac_not_two hpair
    have := Nat.Prime.two_le hpair.1
    omega
  refine ⟨polignac_relative_admissible hpair (by omega), polignac_mismatch_pos hpair,
    (polignac_outside_cone hpair).1, (polignac_outside_cone hpair).2⟩

/-- The pair `3` and `7` has gap `4`, and its relative angle exceeds `π/2`. -/
theorem two_log_seven_div_three_gt_pi_div_two :
    Real.pi / 2 < 2 * Real.log ((7 : ℝ) / 3) := by
  have hlog3 : (1.0986122885 : ℝ) < Real.log 3 := Real.log_three_gt_d9
  have hlog2 : Real.log 2 < (0.6931471808 : ℝ) := Real.log_two_lt_d9
  have hpi : Real.pi < (3.141593 : ℝ) := Real.pi_lt_d6
  have hcmp : (9 : ℝ) / 4 < 7 / 3 := by norm_num
  have hloglt : Real.log ((9 : ℝ) / 4) < Real.log ((7 : ℝ) / 3) :=
    (Real.log_lt_log_iff (by norm_num) (by norm_num)).mpr hcmp
  have heq : Real.log ((9 : ℝ) / 4) = 2 * Real.log 3 - 2 * Real.log 2 := by
    rw [Real.log_div (by norm_num) (by norm_num)]
    have h9 : Real.log (9 : ℝ) = 2 * Real.log 3 := by
      rw [show (9 : ℝ) = 3 ^ (2 : ℕ) by norm_num, Real.log_pow]
      ring
    have h4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
      ring
    rw [h9, h4]
  have hlow : (1.6218604308 : ℝ) < 2 * (2 * Real.log 3 - 2 * Real.log 2) := by
    nlinarith [hlog3, hlog2]
  have htwice : 2 * (2 * Real.log 3 - 2 * Real.log 2) = 2 * Real.log ((9 : ℝ) / 4) := by
    rw [heq]
  nlinarith [hloglt, hpi]

theorem polignac_three_seven_relative_outside :
    IsPolignacPair 3 2 ∧
      ¬ IsAdmissibleContinuous
        (pureBoost (2 * polignacRapidity 3 2 (by decide : (3 : ℕ) ≠ 0))) := by
  refine ⟨polignac_three_two, ?_⟩
  intro hadm
  rw [isAdmissibleContinuous_pureBoost_iff, polignacRapidity_eq_log_div (by decide : 0 < 3)] at hadm
  have hcast : ((3 + 2 * 2 : ℕ) : ℝ) / ((3 : ℕ) : ℝ) = (7 : ℝ) / 3 := by norm_num
  rw [hcast] at hadm
  exact not_le_of_gt two_log_seven_div_three_gt_pi_div_two hadm.2

theorem polignac_seven_two : IsPolignacPair 7 2 := by
  refine ⟨?_, ?_, by decide⟩
  · native_decide
  · native_decide

/-- The gap-`4` pair `7` and `11` has its relative rotor in the cone, and both
primes off the phase. -/
theorem polignac_seven_eleven_relative_admissible :
    IsAdmissibleContinuous
        (pureBoost (2 * polignacRapidity 7 2 (by decide : (7 : ℕ) ≠ 0))) ∧
      ¬ IsAdmissibleContinuous (pureBoost (2 * Real.log (7 : ℝ))) ∧
      ¬ IsAdmissibleContinuous (pureBoost (2 * Real.log (11 : ℝ))) := by
  have h := polignac_seven_two
  exact ⟨polignac_relative_admissible h (by decide : 2 * 2 ≤ 7),
    (polignac_outside_cone h).1, (polignac_outside_cone h).2⟩

/-- For a fixed gap the normalised mismatch is strictly below `(16/(3π²))(2k/p)²`. -/
theorem polignac_mismatchHeight_lt_envelope {p k : ℕ} (hp : 0 < p) (hk : 0 < k) :
    polignacMismatchHeight p k (Nat.pos_iff_ne_zero.mp hp) <
      (16 / (3 * Real.pi ^ 2)) * ((2 * (k : ℝ)) / (p : ℝ)) ^ 2 := by
  rw [polignacMismatchHeight_eq, polignacRapidity_eq_log_div hp]
  set x : ℝ := (2 * (k : ℝ)) / (p : ℝ)
  have hx : 0 < x := by positivity
  have hratio : ((p + 2 * k : ℕ) : ℝ) / p = 1 + x := by
    dsimp [x]
    have hnum : ((p + 2 * k : ℕ) : ℝ) = (p : ℝ) + 2 * (k : ℝ) := by
      push_cast
      ring
    rw [hnum]
    field_simp
  rw [hratio]
  have hlog : Real.log (1 + x) < x := by
    have h1 : 0 < 1 + x := by linarith
    have hne : 1 + x ≠ 1 := by
      intro h
      exact hx.ne' (by linarith)
    have hlt := Real.log_lt_sub_one_of_pos h1 hne
    linarith
  have hlog0 : 0 ≤ Real.log (1 + x) := Real.log_nonneg (by linarith : (1 : ℝ) ≤ 1 + x)
  have hsq : (Real.log (1 + x)) ^ 2 < x ^ 2 := by
    rw [sq_lt_sq, abs_of_nonneg hlog0, abs_of_pos hx]
    exact hlog
  exact mul_lt_mul_of_pos_left hsq (by positivity)

/-- The envelope `(16/(3π²))(2k/p)²` falls below every positive tolerance. -/
theorem polignac_envelope_eventually_lt {k : ℕ} (hk : 0 < k) {ε : ℝ} (hε : 0 < ε) :
    ∃ B : ℕ, ∀ p : ℕ, B ≤ p →
      (16 / (3 * Real.pi ^ 2)) * ((2 * (k : ℝ)) / (p : ℝ)) ^ 2 < ε := by
  have hsqrt : 0 < Real.sqrt (3 * Real.pi ^ 2 * ε) := Real.sqrt_pos.mpr (by positivity)
  obtain ⟨B, hB⟩ := exists_nat_gt ((8 * (k : ℝ)) / Real.sqrt (3 * Real.pi ^ 2 * ε))
  refine ⟨B + 1, ?_⟩
  intro p hp
  have hp0 : 0 < p := by omega
  have hgt : (8 * (k : ℝ)) / Real.sqrt (3 * Real.pi ^ 2 * ε) < (p : ℝ) := by
    have hBp : (B : ℝ) < p := by exact_mod_cast (show B < p by omega)
    exact lt_trans hB hBp
  have hs : Real.sqrt (3 * Real.pi ^ 2 * ε) ^ 2 = 3 * Real.pi ^ 2 * ε := by
    rw [pow_two, Real.mul_self_sqrt (by positivity)]
  have hmul : (8 * (k : ℝ)) < (p : ℝ) * Real.sqrt (3 * Real.pi ^ 2 * ε) := by
    have := mul_lt_mul_of_pos_right hgt hsqrt
    rwa [div_mul_cancel₀ _ hsqrt.ne'] at this
  have hsq : (8 * (k : ℝ)) ^ 2 < (p : ℝ) ^ 2 * (3 * Real.pi ^ 2 * ε) := by
    have hsq' :=
      mul_lt_mul' hmul.le hmul (by positivity) (mul_pos (by exact_mod_cast hp0) hsqrt)
    nlinarith [hs]
  have h64 : (8 * (k : ℝ)) ^ 2 = 64 * (k : ℝ) ^ 2 := by ring
  have hform : (64 * (k : ℝ) ^ 2) / (3 * Real.pi ^ 2 * (p : ℝ) ^ 2) < ε := by
    rw [div_lt_iff₀ (by positivity)]
    nlinarith [hsq, h64]
  have heq :
      (16 / (3 * Real.pi ^ 2)) * ((2 * (k : ℝ)) / (p : ℝ)) ^ 2 =
        (64 * (k : ℝ) ^ 2) / (3 * Real.pi ^ 2 * (p : ℝ) ^ 2) := by
    field_simp
    ring
  linarith

/-- For each fixed gap, every sufficiently large Polignac pair has mismatch height
below a prescribed positive tolerance. -/
theorem polignac_mismatch_height_eventually_lt {k : ℕ} (hk : 0 < k) {ε : ℝ} (hε : 0 < ε) :
    ∃ B : ℕ, ∀ p : ℕ, B ≤ p → ∀ h : IsPolignacPair p k,
      polignacMismatchHeight p k (Nat.Prime.ne_zero h.1) < ε := by
  obtain ⟨B, hB⟩ := polignac_envelope_eventually_lt hk hε
  refine ⟨B, ?_⟩
  intro p hp hpair
  have hlt := polignac_mismatchHeight_lt_envelope (Nat.Prime.pos hpair.1) hk
  have henv := hB p hp
  simpa using lt_trans hlt henv

/-- For a fixed gap the mismatch height falls as the smaller member grows. -/
theorem polignac_mismatchHeight_strictAnti {p q k : ℕ}
    (hp : 0 < p) (hlt : p < q) (hk : 0 < k) :
    polignacMismatchHeight q k (Nat.pos_iff_ne_zero.mp (by omega : 0 < q)) <
      polignacMismatchHeight p k (Nat.pos_iff_ne_zero.mp hp) := by
  rw [polignacMismatchHeight_eq, polignacMismatchHeight_eq,
    polignacRapidity_eq_log_div (by omega : 0 < q), polignacRapidity_eq_log_div hp]
  have hq : 0 < q := by omega
  have hratio :
      ((q + 2 * k : ℕ) : ℝ) / q < ((p + 2 * k : ℕ) : ℝ) / p := by
    rw [div_lt_div_iff₀ (by exact_mod_cast hq) (by exact_mod_cast hp)]
    have hcross : (q + 2 * k) * p < (p + 2 * k) * q := by
      nlinarith
    exact_mod_cast hcross
  have hlog :
      Real.log (((q + 2 * k : ℕ) : ℝ) / q) <
        Real.log (((p + 2 * k : ℕ) : ℝ) / p) :=
    (Real.log_lt_log_iff (by positivity) (by positivity)).mpr hratio
  have hpos : 0 < Real.log (((q + 2 * k : ℕ) : ℝ) / q) := by
    rw [Real.log_pos_iff (by positivity)]
    rw [one_lt_div (by exact_mod_cast hq)]
    exact_mod_cast (show q < q + 2 * k by omega)
  have hsq :
      (Real.log (((q + 2 * k : ℕ) : ℝ) / q)) ^ 2 <
        (Real.log (((p + 2 * k : ℕ) : ℝ) / p)) ^ 2 := by
    rw [sq_lt_sq, abs_of_pos hpos, abs_of_pos (lt_trans hpos hlog)]
    exact hlog
  exact mul_lt_mul_of_pos_left hsq (by positivity)

/-! ### Classical Polignac under an explicit bridge hypothesis -/

/--
Paper Chapter 9's missing bridge: if Polignac pairs for gap `2k` are bounded,
then a strongly avoiding prime-gap tail yields an admissible pure-boost
configuration with `gapChainHeight > 1`.

This proposition is **not** proved in this development.
-/
def PolignacAdmissibleBridge : Prop :=
  ∀ k : ℕ, 0 < k →
    (¬ ∀ B : ℕ, ∃ p, B < p ∧ IsPolignacPair p k) →
      ∃ S : ℝ, IsAdmissibleContinuous (pureBoost S) ∧ 1 < gapChainHeight S

/-- Conditional DST recovery of Polignac's conjecture. -/
theorem polignac_conjecture_of_bridge (hbridge : PolignacAdmissibleBridge) :
    ∀ k : ℕ, 0 < k → ∀ B : ℕ, ∃ p, B < p ∧ IsPolignacPair p k := by
  intro k hk
  by_contra hnone
  obtain ⟨S, hadm, hgt⟩ := hbridge k hk hnone
  have hbound := torsion_bound_continuous _ hadm
  unfold gapChainHeight at hgt
  exact (not_le_of_gt hgt) hbound

/-- Twin-prime conjecture as the `k = 1` case under the same bridge. -/
theorem twin_prime_conjecture_of_bridge (hbridge : PolignacAdmissibleBridge) :
    ∀ B : ℕ, ∃ p, B < p ∧ IsTwinPrimePair p :=
  fun B => polignac_conjecture_of_bridge hbridge 1 (Nat.succ_pos 0) B

theorem polignacAdmissibleBridge_of_infinite
    (h : ∀ k : ℕ, 0 < k → ∀ B : ℕ, ∃ p, B < p ∧ IsPolignacPair p k) :
    PolignacAdmissibleBridge := by
  intro k hk hnot
  exact absurd (h k hk) hnot

/-- The bridge holds exactly when every even gap returns infinitely often. -/
theorem polignacAdmissibleBridge_iff :
    PolignacAdmissibleBridge ↔
      (∀ k : ℕ, 0 < k → ∀ B : ℕ, ∃ p, B < p ∧ IsPolignacPair p k) :=
  ⟨polignac_conjecture_of_bridge, polignacAdmissibleBridge_of_infinite⟩

end Theorems

end DstDiophantine
