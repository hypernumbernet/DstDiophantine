import DstDiophantine.Theorems.Collatz
import DstDiophantine.Framework.Representation
import DstDiophantine.Embedding.Height
import DstDiophantine.Algebra.Amplification
import DstDiophantine.Algebra.Invariant
import DstDiophantine.Algebra.Discrete
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Defs
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

## Paper gap (not closed)

Classical Polignac (`∀ k > 0, infinitely many primes p with p+2k also prime`) is
**not** claimed unconditionally. Avoidance of a single even gap does not force
`(g_n - 2k)/p_n > 0`, because a smaller even gap may still occur. A height
lower bound holds only under **strong avoidance** `g_n ≥ 2k + 2`. An admissible
pure boost has height at most one, so `PolignacAdmissibleBridge` has no
witness. The bridge holds if and only if the conjecture does
(`polignacAdmissibleBridge_iff`). It is not a reduction.
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
