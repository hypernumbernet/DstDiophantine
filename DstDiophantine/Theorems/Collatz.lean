import DstDiophantine.Embedding.Height
import DstDiophantine.Algebra.Amplification
import DstDiophantine.Algebra.Invariant
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.IntervalCases

set_option linter.style.nativeDecide false

/-!
# Phase 5: Collatz conjecture (DST orbit / height core)

We formalise Chapter 9 of `dst-diophantine.tex` as a **finite-orbit / height
bound** argument on the pure-boost integer-rotor model, together with a small
computational certificate and a bridge hypothesis recovering the classical
statement.

## What is proved

* The canonical pure boost of a positive integer lies in the admissible cone
  if and only if the integer is `1` or `2`. The normalised height of `2` is
  strictly less than one third; `3` has already left the cone, while its
  height is still strictly less than one; every `n ≥ 4` has height greater
  than one.
* The odd step is the pure boost `log(3n+1) = log n + log(3 + 1/n)` on that
  same axis. The outgoing leg `1 → 4` has rapidity `2 log 2 > π/4`, so the
  cycle `4 → 2 → 1` meets the cone and immediately leaves it.
* The only periodic points whose orbit reaches `1` are `1`, `2`, and `4`.
* On the accelerated map (one halving per step), every integer `n ≥ 3` whose
  first sixteen inputs include at most ten odd values returns strictly below
  itself. Exactly `6885` residue classes modulo `2^16` have eleven or more
  odd inputs in that block.
* Every positive integer up to `2^20` reaches `1`. Any other periodic point
  is strictly larger, and the normalised height is then greater than `100` at
  every vertex of its cycle.

## Paper gap (not closed)

Classical Collatz (`∀ n > 0, the orbit reaches 1`) is **not** claimed.
`CollatzAdmissibleBridge` asks a counterexample to produce a cycle of height
at most one. No cycle that avoids `1` has that height, so the bridge holds
if and only if the conjecture does (`collatzAdmissibleBridge_iff`). It is not
a reduction. Divergence is not forbidden by the torsion bound: the bound
applies on the admissible cone, and the cone is not forward-invariant.
-/

namespace DstDiophantine

namespace Theorems

open Amplification Invariant Real Admissible
open _root_.DstDiophantine.Embedding

/-! ### Classical Collatz dynamics -/

/-- One Collatz step: `n/2` if even, else `3n+1`. -/
def collatzStep (n : ℕ) : ℕ :=
  if n % 2 = 0 then n / 2 else 3 * n + 1

theorem collatzStep_even {n : ℕ} (h : n % 2 = 0) :
    collatzStep n = n / 2 := by
  simp [collatzStep, h]

theorem collatzStep_odd {n : ℕ} (h : n % 2 = 1) :
    collatzStep n = 3 * n + 1 := by
  simp [collatzStep, h]

theorem collatzStep_zero : collatzStep 0 = 0 := by
  simp [collatzStep]

theorem collatzStep_one : collatzStep 1 = 4 := by
  native_decide

theorem collatzStep_two : collatzStep 2 = 1 := by
  native_decide

theorem collatzStep_four : collatzStep 4 = 2 := by
  native_decide

/-- The attracting classical cycle `4 → 2 → 1 → 4`. -/
theorem collatz_cycle_421 :
    collatzStep 4 = 2 ∧ collatzStep 2 = 1 ∧ collatzStep 1 = 4 :=
  ⟨collatzStep_four, collatzStep_two, collatzStep_one⟩

/-- `k`-fold iterate of `collatzStep`. -/
def collatzIter (k n : ℕ) : ℕ :=
  collatzStep^[k] n

theorem collatzIter_zero (n : ℕ) : collatzIter 0 n = n :=
  rfl

theorem collatzIter_succ (k n : ℕ) :
    collatzIter (k + 1) n = collatzStep (collatzIter k n) := by
  simp [collatzIter, Function.iterate_succ_apply']

theorem collatzIter_succ_left (k n : ℕ) :
    collatzIter (k + 1) n = collatzIter k (collatzStep n) := by
  simp [collatzIter, Function.iterate_succ_apply]

/-- The orbit of `n` eventually reaches `1`. -/
def ReachesOne (n : ℕ) : Prop :=
  ∃ k : ℕ, collatzIter k n = 1

theorem reachesOne_one : ReachesOne 1 :=
  ⟨0, collatzIter_zero 1⟩

theorem reachesOne_of_step {n : ℕ} (h : ReachesOne (collatzStep n)) : ReachesOne n := by
  obtain ⟨k, hk⟩ := h
  refine ⟨k + 1, ?_⟩
  rw [collatzIter_succ_left, hk]

/-! ### Rotor height encoding -/

/-- Torsional height of a positive Collatz value via the integer rotor. -/
noncomputable def collatzHeight (n : ℕ) (hn : n ≠ 0) : ℝ :=
  integerHeight (n : ℤ) (Int.natCast_ne_zero.mpr hn)

theorem collatzHeight_eq (n : ℕ) (hn : n ≠ 0) :
    collatzHeight n hn =
      |(16 / (3 * Real.pi ^ 2)) * (Real.log n) ^ 2| := by
  unfold collatzHeight
  rw [integerHeight_eq]
  simp

theorem collatzHeight_nonneg (n : ℕ) (hn : n ≠ 0) : 0 ≤ collatzHeight n hn := by
  unfold collatzHeight integerHeight torsionHeight
  exact abs_nonneg _

theorem collatzHeight_eq_mul (n : ℕ) (hn : n ≠ 0) :
    collatzHeight n hn = (16 / (3 * Real.pi ^ 2)) * (Real.log n) ^ 2 := by
  rw [collatzHeight_eq]
  have hcoef : 0 ≤ 16 / (3 * Real.pi ^ 2) := by positivity
  have hlog : 0 ≤ (Real.log n) ^ 2 := sq_nonneg _
  rw [abs_of_nonneg (mul_nonneg hcoef hlog)]

theorem collatzHeight_one : collatzHeight 1 (by decide : (1 : ℕ) ≠ 0) = 0 := by
  rw [collatzHeight_eq_mul]
  simp [Real.log_one]

private theorem collatzHeight_mono_of_le {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0)
    (hle : m ≤ n) :
    collatzHeight m hm ≤ collatzHeight n hn := by
  rw [collatzHeight_eq_mul, collatzHeight_eq_mul]
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

/-- Even Collatz step contracts the pure-boost height. -/
theorem collatzHeight_even_le {n : ℕ} (hn : 2 ≤ n) (_he : n % 2 = 0) :
    collatzHeight (n / 2) (by
      have : 0 < n / 2 := Nat.div_pos hn (by decide : 0 < 2)
      exact Nat.pos_iff_ne_zero.mp this) ≤
      collatzHeight n (Nat.pos_iff_ne_zero.mp (Nat.lt_of_lt_of_le (by decide : 0 < 2) hn)) := by
  refine collatzHeight_mono_of_le _ _ (Nat.div_le_self n 2)

/-- Strict contraction for even `n ≥ 4`. -/
theorem collatzHeight_even_lt {n : ℕ} (hn : 4 ≤ n) (_he : n % 2 = 0) :
    collatzHeight (n / 2) (by
      have : 0 < n / 2 := Nat.div_pos (le_trans (by decide : 2 ≤ 4) hn) (by decide : 0 < 2)
      exact Nat.pos_iff_ne_zero.mp this) <
      collatzHeight n (Nat.pos_iff_ne_zero.mp (Nat.lt_of_lt_of_le (by decide : 0 < 4) hn)) := by
  set hn0 : n ≠ 0 := Nat.pos_iff_ne_zero.mp (Nat.lt_of_lt_of_le (by decide : 0 < 4) hn)
  set hhalf : n / 2 ≠ 0 := by
    have : 0 < n / 2 := Nat.div_pos (le_trans (by decide : 2 ≤ 4) hn) (by decide : 0 < 2)
    exact Nat.pos_iff_ne_zero.mp this
  rw [collatzHeight_eq_mul _ hhalf, collatzHeight_eq_mul _ hn0]
  have hcoefPos : 0 < 16 / (3 * Real.pi ^ 2) := by positivity
  have hpos : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn0)
  have hhalfPos : 0 < ((n / 2 : ℕ) : ℝ) :=
    Nat.cast_pos.mpr (Nat.pos_of_ne_zero hhalf)
  have hlt_div : (n / 2 : ℕ) < n :=
    Nat.div_lt_self (Nat.pos_of_ne_zero hn0) (by decide : 1 < 2)
  have hloglt : Real.log ((n / 2 : ℕ) : ℝ) < Real.log n :=
    Real.log_lt_log hhalfPos (Nat.cast_lt.mpr hlt_div)
  have hlogn : 0 < Real.log n :=
    Real.log_pos (lt_of_lt_of_le (by norm_num : (1 : ℝ) < 4) (Nat.cast_le.mpr hn))
  have hhalf1 : (1 : ℝ) ≤ (n / 2 : ℕ) :=
    Nat.one_le_cast.mpr (Nat.div_pos (le_trans (by decide : 2 ≤ 4) hn) (by decide : 0 < 2))
  have hlogm : 0 ≤ Real.log ((n / 2 : ℕ) : ℝ) := Real.log_nonneg hhalf1
  have hsq : (Real.log ((n / 2 : ℕ) : ℝ)) ^ 2 < (Real.log n) ^ 2 := by
    rw [pow_two, pow_two]
    exact mul_lt_mul'' hloglt hloglt hlogm hlogm
  exact (mul_lt_mul_of_pos_left hsq hcoefPos)

/-- Odd-step pure-boost delta: `log(3n+1) = log n + log(3 + 1/n)`.

This replaces the paper's informal shear
`exp(log 3 · iI + Γ₁ · log(1 + 1/n))` by a single hyperbolic boost. -/
theorem collatz_odd_log_delta {n : ℕ} (hn : 0 < n) :
    Real.log ((3 * n + 1 : ℕ) : ℝ) =
      Real.log n + Real.log (3 + 1 / (n : ℝ)) := by
  have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hrepr : ((3 * n + 1 : ℕ) : ℝ) = (n : ℝ) * (3 + (1 : ℝ) / n) := by
    have : ((3 * n + 1 : ℕ) : ℝ) = 3 * (n : ℝ) + 1 := by simp
    rw [this]
    field_simp
  have hfac : 0 < 3 + (1 : ℝ) / n := by positivity
  rw [hrepr, Real.log_mul (ne_of_gt hnpos) (ne_of_gt hfac)]

/-! ### Height bound core -/

private theorem log_two_sq_bound :
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

theorem collatzHeight_four_gt_one :
    1 < collatzHeight 4 (by decide : (4 : ℕ) ≠ 0) := by
  rw [collatzHeight_eq_mul]
  have h4 : Real.log ((4 : ℕ) : ℝ) = 2 * Real.log 2 := by
    have h4eq : ((4 : ℕ) : ℝ) = 2 * 2 := by norm_num
    rw [h4eq, Real.log_mul (by norm_num) (by norm_num)]
    ring
  rw [h4, show (2 * Real.log 2) ^ 2 = 4 * (Real.log 2) ^ 2 from by ring]
  have hbound : 3 * Real.pi ^ 2 < 64 * (Real.log 2) ^ 2 := log_two_sq_bound
  have hden : 0 < 3 * Real.pi ^ 2 := by positivity
  have hform : 1 < (64 * (Real.log 2) ^ 2) / (3 * Real.pi ^ 2) :=
    (one_lt_div hden).mpr hbound
  convert hform using 1
  ring

theorem collatzHeight_ge_four_gt_one {n : ℕ} (hn : 4 ≤ n) :
    1 < collatzHeight n (Nat.pos_iff_ne_zero.mp (Nat.lt_of_lt_of_le (by decide : 0 < 4) hn)) := by
  set hn0 : n ≠ 0 := Nat.pos_iff_ne_zero.mp (Nat.lt_of_lt_of_le (by decide : 0 < 4) hn)
  have h4 : 1 < collatzHeight 4 (by decide) := collatzHeight_four_gt_one
  exact lt_of_lt_of_le h4 (collatzHeight_mono_of_le (by decide) hn0 hn)

/-- Values with normalised height at most `1` are at most `3`. -/
theorem collatzHeight_le_one_implies_le_three {n : ℕ} (hn : n ≠ 0)
    (hle : collatzHeight n hn ≤ 1) : n ≤ 3 := by
  by_contra hgt
  push Not at hgt
  have h4 : 4 ≤ n := by omega
  exact (not_le_of_gt (collatzHeight_ge_four_gt_one h4)) hle

/-! ### Collatz cycles -/

/-- A nonempty Finset closed under `collatzStep`. -/
def IsCollatzCycle (s : Finset ℕ) : Prop :=
  s.Nonempty ∧ ∀ m ∈ s, collatzStep m ∈ s

theorem isCollatzCycle_421 :
    IsCollatzCycle ({1, 2, 4} : Finset ℕ) := by
  refine ⟨by decide, ?_⟩
  intro m hm
  fin_cases hm <;> simp [collatzStep_one, collatzStep_two, collatzStep_four]

/-- Chapter 9 core: a Collatz cycle that avoids `1` must exceed height `1`. -/
theorem collatz_cycle_avoids_one_exceeds_bound {s : Finset ℕ}
    (hcyc : IsCollatzCycle s)
    (hpos : ∀ m ∈ s, 0 < m)
    (hone : 1 ∉ s) :
    ∃ m ∈ s, ∃ hm : m ≠ 0, 1 < collatzHeight m hm := by
  obtain ⟨⟨m0, hm0⟩, hclosed⟩ := hcyc
  by_cases hle : ∀ m ∈ s, m ≤ 3
  · -- Then s ⊆ {2,3} (positive, avoids 1), which cannot be a cycle.
    have hs23 : ∀ m ∈ s, m = 2 ∨ m = 3 := by
      intro m hm
      have hmpos : 0 < m := hpos m hm
      have hmle : m ≤ 3 := hle m hm
      have hmne1 : m ≠ 1 := fun h => hone (h ▸ hm)
      interval_cases m <;> try contradiction
      · exact Or.inl rfl
      · exact Or.inr rfl
    rcases hs23 m0 hm0 with h2 | h3
    · subst h2
      have : collatzStep 2 ∈ s := hclosed 2 hm0
      rw [collatzStep_two] at this
      exact absurd this hone
    · subst h3
      have h10 : collatzStep 3 ∈ s := hclosed 3 hm0
      have hstep : collatzStep 3 = 10 := by native_decide
      rw [hstep] at h10
      exact absurd (hle 10 h10) (by decide : ¬ (10 ≤ 3))
  · push Not at hle
    obtain ⟨m, hm, h4⟩ := hle
    have hmne : m ≠ 0 := Nat.pos_iff_ne_zero.mp (hpos m hm)
    refine ⟨m, hm, hmne, ?_⟩
    have hm4 : 4 ≤ m := by omega
    simpa [hmne] using collatzHeight_ge_four_gt_one hm4

/-! ### Finite-type eventual periodicity -/

/-- On a finite type every orbit is eventually periodic (pigeonhole). -/
theorem eventually_periodic_of_fintype {α : Type*} [Finite α]
    (f : α → α) (x : α) :
    ∃ m n : ℕ, m < n ∧ f^[n] x = f^[m] x := by
  classical
  let _ : Fintype α := Fintype.ofFinite α
  let N := Fintype.card α + 1
  have hlt : Fintype.card α < Fintype.card (Fin N) := by
    simp [N]
  obtain ⟨a, b, hab, heq⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt (fun i : Fin N => f^[i.val] x) hlt
  wlog hle : a.val ≤ b.val generalizing a b
  · exact this b a hab.symm heq.symm (le_of_not_ge hle)
  refine ⟨a.val, b.val, ?_, ?_⟩
  · exact lt_of_le_of_ne hle (Fin.val_ne_iff.mpr hab)
  · simpa [hle] using heq.symm

/-! ### Small computational certificate -/

/-- Fuel-bounded search for reaching `1`. -/
def collatzReachesOneFuel : ℕ → ℕ → Bool
  | 0, n => decide (n = 1)
  | fuel + 1, n => decide (n = 1) || collatzReachesOneFuel fuel (collatzStep n)

theorem collatzReachesOneFuel_sound :
    ∀ fuel n : ℕ, collatzReachesOneFuel fuel n = true → ReachesOne n
  | 0, n, h => by
    have hn : n = 1 := by simpa [collatzReachesOneFuel] using h
    exact ⟨0, by simp [collatzIter, hn]⟩
  | fuel + 1, n, h => by
    have h' : n = 1 ∨ collatzReachesOneFuel fuel (collatzStep n) = true := by
      simpa [collatzReachesOneFuel, Bool.or_eq_true, decide_eq_true_eq] using h
    rcases h' with hn | hfuel
    · exact ⟨0, by simp [collatzIter, hn]⟩
    · exact reachesOne_of_step (collatzReachesOneFuel_sound fuel (collatzStep n) hfuel)

/-- All of `1…N` reach `1` within the given fuel budget. -/
def allReachOneUpTo (N fuel : ℕ) : Bool :=
  (List.range N).all fun i => collatzReachesOneFuel fuel (i + 1)

theorem allReachOneUpTo_sound {N fuel : ℕ} (h : allReachOneUpTo N fuel = true) :
    ∀ n, 1 ≤ n → n ≤ N → ReachesOne n := by
  intro n hn1 hnN
  have hlt : n - 1 < N := by omega
  have hall := (List.all_eq_true.mp h) (n - 1) (List.mem_range.mpr hlt)
  have : n - 1 + 1 = n := Nat.sub_add_cancel hn1
  rw [this] at hall
  exact collatzReachesOneFuel_sound fuel n hall

/-- Chapter 9 finite-exploration certificate for starting values up to `20`. -/
theorem reachesOne_of_le_twenty {n : ℕ} (hn1 : 1 ≤ n) (hn : n ≤ 20) : ReachesOne n :=
  allReachOneUpTo_sound (by native_decide : allReachOneUpTo 20 1000 = true) n hn1 hn

/-! ### Admissible window on the integer boost -/

theorem two_log_two_lt_pi_div_two : 2 * Real.log 2 < Real.pi / 2 := by
  have hlog : Real.log 2 < (0.6931471808 : ℝ) := Real.log_two_lt_d9
  have hpi : (3.141592 : ℝ) < Real.pi := Real.pi_gt_d6
  nlinarith

theorem pi_div_four_lt_two_log_two : Real.pi / 4 < 2 * Real.log 2 := by
  have hlog : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hpi : Real.pi < (3.141593 : ℝ) := Real.pi_lt_d6
  nlinarith

theorem pi_div_two_lt_two_log_three : Real.pi / 2 < 2 * Real.log 3 := by
  have hlog : (1.0986122885 : ℝ) < Real.log 3 := Real.log_three_gt_d9
  have hpi : Real.pi < (3.141593 : ℝ) := Real.pi_lt_d6
  nlinarith

/-- Positive integers whose canonical pure boost lies in the admissible cone. -/
theorem positive_integer_boost_admissible_iff {n : ℕ} (hn : 0 < n) :
    Discrete.IsAdmissibleContinuous (pureBoost (2 * Real.log (n : ℝ))) ↔ n = 1 ∨ n = 2 := by
  rw [isAdmissibleContinuous_pureBoost_iff]
  constructor
  · intro ⟨_, hle⟩
    by_contra hnot
    have h3 : 3 ≤ n := by omega
    have hnreal : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
    have hlog : Real.log 3 ≤ Real.log (n : ℝ) :=
      (Real.log_le_log_iff (by norm_num) hnreal).mpr (by exact_mod_cast h3)
    have hmul : 2 * Real.log 3 ≤ 2 * Real.log (n : ℝ) :=
      mul_le_mul_of_nonneg_left hlog (by norm_num)
    have hgt : Real.pi / 2 < 2 * Real.log (n : ℝ) :=
      lt_of_lt_of_le pi_div_two_lt_two_log_three hmul
    exact not_le_of_gt hgt hle
  · intro h
    rcases h with rfl | rfl
    · simp only [Nat.cast_one, Real.log_one, mul_zero, le_refl, true_and]
      positivity
    · exact ⟨by positivity, le_of_lt two_log_two_lt_pi_div_two⟩

theorem collatzHeight_two_lt_third :
    collatzHeight 2 (by decide : (2 : ℕ) ≠ 0) < 1 / 3 := by
  rw [collatzHeight_eq_mul]
  have hcast : Real.log ((2 : ℕ) : ℝ) = Real.log 2 := by norm_num
  rw [hcast]
  have hlt : 2 * Real.log 2 < Real.pi / 2 := two_log_two_lt_pi_div_two
  have hpos : (0 : ℝ) ≤ 2 * Real.log 2 := by positivity
  have hsq : (2 * Real.log 2) ^ 2 < (Real.pi / 2) ^ 2 := by
    have hpi : (0 : ℝ) ≤ Real.pi / 2 := by positivity
    exact sq_lt_sq' (by nlinarith) hlt
  have heq : (16 / (3 * Real.pi ^ 2)) * (Real.log 2) ^ 2 =
      (4 / (3 * Real.pi ^ 2)) * (2 * Real.log 2) ^ 2 := by ring
  rw [heq]
  have hedge : (4 / (3 * Real.pi ^ 2)) * (Real.pi / 2) ^ 2 = 1 / 3 := by
    field_simp
    ring_nf
  have hcoef : (0 : ℝ) < 4 / (3 * Real.pi ^ 2) := by positivity
  have hlt' : (4 / (3 * Real.pi ^ 2)) * (2 * Real.log 2) ^ 2 <
      (4 / (3 * Real.pi ^ 2)) * (Real.pi / 2) ^ 2 :=
    mul_lt_mul_of_pos_left hsq hcoef
  linarith

theorem collatzHeight_three_gt_third :
    1 / 3 < collatzHeight 3 (by decide : (3 : ℕ) ≠ 0) := by
  rw [collatzHeight_eq_mul]
  have hcast : Real.log ((3 : ℕ) : ℝ) = Real.log 3 := by norm_num
  rw [hcast]
  have hlt : Real.pi / 2 < 2 * Real.log 3 := pi_div_two_lt_two_log_three
  have hpi : (0 : ℝ) ≤ Real.pi / 2 := by positivity
  have hsq : (Real.pi / 2) ^ 2 < (2 * Real.log 3) ^ 2 := by
    exact sq_lt_sq' (by nlinarith) hlt
  have heq : (16 / (3 * Real.pi ^ 2)) * (Real.log 3) ^ 2 =
      (4 / (3 * Real.pi ^ 2)) * (2 * Real.log 3) ^ 2 := by ring
  rw [heq]
  have hedge : (4 / (3 * Real.pi ^ 2)) * (Real.pi / 2) ^ 2 = 1 / 3 := by
    field_simp
    ring_nf
  have hcoef : (0 : ℝ) < 4 / (3 * Real.pi ^ 2) := by positivity
  have hlt' : (4 / (3 * Real.pi ^ 2)) * (Real.pi / 2) ^ 2 <
      (4 / (3 * Real.pi ^ 2)) * (2 * Real.log 3) ^ 2 :=
    mul_lt_mul_of_pos_left hsq hcoef
  linarith

theorem collatzHeight_three_lt_one :
    collatzHeight 3 (by decide : (3 : ℕ) ≠ 0) < 1 := by
  rw [collatzHeight_eq_mul]
  have hcast : Real.log ((3 : ℕ) : ℝ) = Real.log 3 := by norm_num
  rw [hcast]
  have hlog : Real.log 3 < (1.0986122888 : ℝ) := Real.log_three_lt_d9
  have hlog0 : (0 : ℝ) ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hsq : (Real.log 3) ^ 2 < (1.0986122888 : ℝ) ^ 2 := by
    rw [pow_two, pow_two]
    exact mul_lt_mul'' hlog hlog hlog0 hlog0
  have h16 : 16 * (Real.log 3) ^ 2 < 16 * (1.0986122888 : ℝ) ^ 2 :=
    mul_lt_mul_of_pos_left hsq (by norm_num)
  have hpi : (3.141592 : ℝ) < Real.pi := Real.pi_gt_d6
  have hsqpi : (3.141592 : ℝ) ^ 2 < Real.pi ^ 2 := by
    nlinarith [hpi, Real.pi_pos]
  have hnum : 16 * (1.0986122888 : ℝ) ^ 2 < 3 * (3.141592 : ℝ) ^ 2 := by norm_num
  have hden : (0 : ℝ) < 3 * Real.pi ^ 2 := by positivity
  have hcmp : 16 * (Real.log 3) ^ 2 < 3 * Real.pi ^ 2 := by
    have hmid : 3 * (3.141592 : ℝ) ^ 2 < 3 * Real.pi ^ 2 :=
      mul_lt_mul_of_pos_left hsqpi (by norm_num)
    nlinarith
  have hform : (16 / (3 * Real.pi ^ 2)) * (Real.log 3) ^ 2 < 1 := by
    rw [div_mul_eq_mul_div, div_lt_one hden]
    exact hcmp
  simpa using hform

theorem collatzHeight_le_one_iff {n : ℕ} (hn : n ≠ 0) :
    collatzHeight n hn ≤ 1 ↔ n ≤ 3 := by
  constructor
  · exact fun h => collatzHeight_le_one_implies_le_three hn h
  · intro hle
    have h3 : collatzHeight 3 (by decide) < 1 := collatzHeight_three_lt_one
    have hmono : collatzHeight n hn ≤ collatzHeight 3 (by decide) :=
      collatzHeight_mono_of_le hn (by decide) hle
    exact le_of_lt (lt_of_le_of_lt hmono h3)

/-! ### The return cycle leaves the cone -/

theorem collatz_orbit_three :
    collatzIter 1 3 = 10 ∧ collatzIter 2 3 = 5 ∧ collatzIter 3 3 = 16 ∧
      collatzIter 4 3 = 8 ∧ collatzIter 5 3 = 4 ∧ collatzIter 6 3 = 2 ∧
      collatzIter 7 3 = 1 := by
  native_decide

theorem collatzIter_one_mem (k : ℕ) :
    collatzIter k 1 = 1 ∨ collatzIter k 1 = 2 ∨ collatzIter k 1 = 4 := by
  induction k with
  | zero => simp [collatzIter]
  | succ k ih =>
    rw [collatzIter_succ]
    rcases ih with h1 | h2 | h4
    · simp [h1, collatzStep_one]
    · simp [h2, collatzStep_two]
    · simp [h4, collatzStep_four]

theorem collatzIter_add (a b n : ℕ) :
    collatzIter (a + b) n = collatzIter a (collatzIter b n) := by
  induction a with
  | zero => simp [collatzIter]
  | succ a ih =>
    rw [Nat.succ_add, collatzIter_succ, collatzIter_succ, ih]

theorem collatzIter_period_mul {k n q : ℕ} (hk : collatzIter k n = n) :
    collatzIter (q * k) n = n := by
  induction q with
  | zero => simp [collatzIter]
  | succ q ih =>
    rw [Nat.succ_mul, collatzIter_add, hk, ih]

/-- A positive integer on a cycle. -/
def IsCollatzPeriodic (n : ℕ) : Prop :=
  ∃ k, 0 < k ∧ collatzIter k n = n

theorem collatz_periodic_421 :
    IsCollatzPeriodic 1 ∧ IsCollatzPeriodic 2 ∧ IsCollatzPeriodic 4 := by
  refine ⟨⟨3, by decide, ?_⟩, ⟨3, by decide, ?_⟩, ⟨3, by decide, ?_⟩⟩
  · native_decide
  · native_decide
  · native_decide

theorem periodic_preimage_of_hit {n m : ℕ} (hper : IsCollatzPeriodic n)
    (hhit : ∃ j, collatzIter j n = m) : ∃ i, collatzIter i m = n := by
  obtain ⟨k, hk0, hk⟩ := hper
  obtain ⟨j, hj⟩ := hhit
  let r := j % k
  let q := j / k
  have hrlt : r < k := Nat.mod_lt _ hk0
  refine ⟨k - r, ?_⟩
  rw [← hj]
  have hcomp : collatzIter (k - r) (collatzIter j n) =
      collatzIter ((k - r) + j) n := by
    rw [← collatzIter_add]
  rw [hcomp]
  have hdecomp : j = r + k * q := (Nat.mod_add_div j k).symm
  have hsum : (k - r) + j = (q + 1) * k := by
    calc
      (k - r) + j = (k - r) + (r + k * q) := by rw [hdecomp]
      _ = k + k * q := by omega
      _ = k * (q + 1) := by ring
      _ = (q + 1) * k := by rw [Nat.mul_comm]
  rw [hsum, collatzIter_period_mul hk]

theorem periodic_reachesOne_mem_421 {n : ℕ} (hper : IsCollatzPeriodic n)
    (hreach : ReachesOne n) : n = 1 ∨ n = 2 ∨ n = 4 := by
  obtain ⟨j, hj⟩ := hreach
  obtain ⟨i, hi⟩ := periodic_preimage_of_hit hper ⟨j, hj⟩
  have hmem := collatzIter_one_mem i
  rw [hi] at hmem
  exact hmem

theorem not_collatz_periodic_three : ¬ IsCollatzPeriodic 3 := by
  intro hper
  have hreach : ReachesOne 3 := ⟨7, collatz_orbit_three.2.2.2.2.2.2⟩
  have hmem := periodic_reachesOne_mem_421 hper hreach
  omega

/-- An odd integer congruent to `1` modulo `4` falls in three ordinary steps. -/
theorem collatz_one_mod_four_descends {n : ℕ} (hn : 1 < n) (hmod : n % 4 = 1) :
    collatzIter 3 n = (3 * n + 1) / 4 ∧ (3 * n + 1) / 4 < n := by
  have hodd : n % 2 = 1 := by omega
  have hstep1 : collatzStep n = 3 * n + 1 := collatzStep_odd hodd
  have heven1 : (3 * n + 1) % 2 = 0 := by omega
  have heven2 : ((3 * n + 1) / 2) % 2 = 0 := by omega
  have hthree : collatzIter 3 n = (3 * n + 1) / 4 := by
    rw [collatzIter_succ, collatzIter_succ, collatzIter_succ, collatzIter_zero]
    rw [hstep1, collatzStep_even heven1, collatzStep_even heven2, Nat.div_div_eq_div_mul]
  refine ⟨hthree, ?_⟩
  have hlt : 3 * n + 1 < 4 * n := by omega
  exact Nat.div_lt_of_lt_mul (by simpa [Nat.mul_comm] using hlt)

/-! ### Accelerated map: one halving per step -/

/-- Even input halves; odd input applies `(3n+1)/2`. -/
def collatzAccel (n : ℕ) : ℕ :=
  if n % 2 = 0 then n / 2 else (3 * n + 1) / 2

theorem collatzAccel_even {n : ℕ} (h : n % 2 = 0) : collatzAccel n = n / 2 := by
  simp [collatzAccel, h]

theorem collatzAccel_odd {n : ℕ} (h : n % 2 = 1) : collatzAccel n = (3 * n + 1) / 2 := by
  simp [collatzAccel, h]

theorem collatzAccel_odd_eq_two_steps {n : ℕ} (h : n % 2 = 1) :
    collatzAccel n = collatzStep (collatzStep n) := by
  rw [collatzAccel_odd h, collatzStep_odd h]
  have he : (3 * n + 1) % 2 = 0 := by omega
  rw [collatzStep_even he]

/-- `k` accelerated steps, together with the number of odd inputs. -/
def accelRun : ℕ → ℕ → ℕ × ℕ
  | 0, n => (n, 0)
  | steps + 1, n =>
    if n % 2 = 0 then
      accelRun steps (n / 2)
    else
      let (img, c) := accelRun steps ((3 * n + 1) / 2)
      (img, c + 1)

private theorem add_two_mul_div (x z : ℕ) : (x + 2 * z) / 2 = x / 2 + z := by
  simpa using Nat.add_mul_div_left x z (by decide : 0 < 2)

theorem accelRun_shift : ∀ k r t : ℕ, r < 2 ^ k →
    accelRun k (r + t * 2 ^ k) =
      ((accelRun k r).1 + 3 ^ (accelRun k r).2 * t, (accelRun k r).2)
  | 0, r, t, hr => by
    have hr0 : r = 0 := by simpa using hr
    subst hr0
    simp [accelRun]
  | k + 1, r, t, hr => by
    have htwo : 2 ∣ 2 ^ (k + 1) := by
      rw [pow_succ]
      exact dvd_mul_of_dvd_right (dvd_refl 2) _
    by_cases hpar : r % 2 = 0
    · have hnpar : (r + t * 2 ^ (k + 1)) % 2 = 0 := by
        have : 2 ∣ t * 2 ^ (k + 1) := dvd_mul_of_dvd_right htwo _
        omega
      have hr' : r / 2 < 2 ^ k := by
        have hmul : r < 2 * 2 ^ k := by simpa [pow_succ, Nat.mul_comm] using hr
        exact Nat.div_lt_of_lt_mul hmul
      have hdiv : (r + t * 2 ^ (k + 1)) / 2 = r / 2 + t * 2 ^ k := by
        have hpow : t * 2 ^ (k + 1) = 2 * (t * 2 ^ k) := by
          calc
            t * 2 ^ (k + 1) = t * (2 ^ k * 2) := by rw [pow_succ]
            _ = t * 2 ^ k * 2 := by rw [Nat.mul_assoc]
            _ = 2 * (t * 2 ^ k) := by rw [Nat.mul_comm]
        rw [hpow, add_two_mul_div]
      have hstep : accelRun (k + 1) (r + t * 2 ^ (k + 1)) =
          accelRun k (r / 2 + t * 2 ^ k) := by
        simp [accelRun, hnpar, hdiv]
      have hbase : accelRun (k + 1) r = accelRun k (r / 2) := by
        simp [accelRun, hpar]
      rw [hstep, hbase]
      exact accelRun_shift k (r / 2) t hr'
    · have hodd : r % 2 = 1 := by omega
      have hnodd : (r + t * 2 ^ (k + 1)) % 2 = 1 := by
        have : 2 ∣ t * 2 ^ (k + 1) := dvd_mul_of_dvd_right htwo _
        omega
      have hdiv : (3 * (r + t * 2 ^ (k + 1)) + 1) / 2 =
          (3 * r + 1) / 2 + 3 * t * 2 ^ k := by
        have h3 : 3 * (r + t * 2 ^ (k + 1)) + 1 =
            (3 * r + 1) + 2 * (3 * t * 2 ^ k) := by
          calc
            3 * (r + t * 2 ^ (k + 1)) + 1
              = 3 * r + 3 * (t * (2 ^ k * 2)) + 1 := by rw [pow_succ]; ring_nf
            _ = 3 * r + 1 + 2 * (3 * t * 2 ^ k) := by ring_nf
        rw [h3, add_two_mul_div]
      set s : ℕ := (3 * r + 1) / 2
      have hn1 : (3 * (r + t * 2 ^ (k + 1)) + 1) / 2 = s + 3 * t * 2 ^ k := by
        simpa [s] using hdiv
      have hM : 0 < 2 ^ k := Nat.two_pow_pos k
      have hr' : s % 2 ^ k < 2 ^ k := Nat.mod_lt _ hM
      have hs_eq : s = s % 2 ^ k + (s / 2 ^ k) * 2 ^ k := by
        calc
          s = s % 2 ^ k + 2 ^ k * (s / 2 ^ k) := (Nat.mod_add_div s (2 ^ k)).symm
          _ = s % 2 ^ k + (s / 2 ^ k) * 2 ^ k := by rw [Nat.mul_comm]
      have hsplit : s + 3 * t * 2 ^ k =
          s % 2 ^ k + (s / 2 ^ k + 3 * t) * 2 ^ k := by
        conv_lhs => rw [hs_eq]
        ring_nf
      have hL : accelRun (k + 1) (r + t * 2 ^ (k + 1)) =
          ((accelRun k (s + 3 * t * 2 ^ k)).1,
            (accelRun k (s + 3 * t * 2 ^ k)).2 + 1) := by
        simp [accelRun, hnodd, hn1]
      have hR : accelRun (k + 1) r =
          ((accelRun k s).1, (accelRun k s).2 + 1) := by
        simp [accelRun, hodd, s]
      have hS := accelRun_shift k (s % 2 ^ k) (s / 2 ^ k) hr'
      have hN := accelRun_shift k (s % 2 ^ k) (s / 2 ^ k + 3 * t) hr'
      rw [← hs_eq] at hS
      rw [← hsplit] at hN
      rw [hL, hR, hS, hN]
      refine Prod.ext ?_ rfl
      · ring_nf

/-- Largest positive non-contraction in a good class, or `0` if the class may climb. -/
def collatzBlockFail (k r : ℕ) : ℕ :=
  let img := (accelRun k r).1
  let c := (accelRun k r).2
  if 2 ^ k ≤ 3 ^ c then
    0
  else if img < r then
    0
  else
    r + (img - r) / (2 ^ k - 3 ^ c) * 2 ^ k

/-- Check residues `0 ≤ r < bound`. -/
def allBlockFailBounded : ℕ → ℕ → ℕ → Bool
  | _, _, 0 => true
  | k, bound, r + 1 =>
    if collatzBlockFail k r ≤ bound then allBlockFailBounded k bound r else false

theorem allBlockFailBounded_sound :
    ∀ bound r k, allBlockFailBounded k bound r = true →
      ∀ i, i < r → collatzBlockFail k i ≤ bound
  | bound, 0, k, _, i, hi => by omega
  | bound, r + 1, k, h, i, hi => by
    simp only [allBlockFailBounded] at h
    split_ifs at h with hle
    · by_cases hi' : i = r
      · simpa [hi'] using hle
      · exact allBlockFailBounded_sound bound r k h i (by omega)

/-- Count residues `r < bound` whose sixteen-step block has at least eleven odd inputs. -/
def countBlockBad : ℕ → ℕ → ℕ
  | acc, 0 => acc
  | acc, r + 1 =>
    countBlockBad (acc + if 2 ^ 16 ≤ 3 ^ (accelRun 16 r).2 then 1 else 0) r

theorem three_pow_ten_lt_two_pow_sixteen : 3 ^ 10 < 2 ^ 16 := by native_decide

theorem two_pow_sixteen_lt_three_pow_eleven : 2 ^ 16 < 3 ^ 11 := by native_decide

set_option maxRecDepth 2000000 in
theorem collatz_block_fail_bounded :
    allBlockFailBounded 16 2 (2 ^ 16) = true := by
  native_decide

set_option maxRecDepth 2000000 in
theorem countBlockBad_sixteen : countBlockBad 0 (2 ^ 16) = 6885 := by
  native_decide

theorem collatz_bad_class_card :
    ((Finset.range (2 ^ 16)).filter fun i => 2 ^ 16 ≤ 3 ^ (accelRun 16 i).2).card = 6885 := by
  native_decide

theorem accel_block_contracts {n : ℕ} (hn : 2 < n)
    (hc : (accelRun 16 (n % 2 ^ 16)).2 ≤ 10) :
    (accelRun 16 n).1 < n := by
  set M : ℕ := 2 ^ 16
  set r : ℕ := n % M
  set t : ℕ := n / M
  have hM : 0 < M := by decide
  have hr : r < M := Nat.mod_lt _ hM
  have hnM : n = r + t * M := by
    have hmod : n = r + M * t := by
      simpa [r, t] using (Nat.mod_add_div n M).symm
    rw [hmod, Nat.mul_comm]
  have hshift := accelRun_shift 16 r t hr
  have hsum : r + t * 2 ^ 16 = r + t * M := by simp [M]
  rw [hsum] at hshift
  rw [← hnM] at hshift
  set img := (accelRun 16 r).1
  set c := (accelRun 16 r).2
  have himg : (accelRun 16 n).1 = img + 3 ^ c * t :=
    congrArg Prod.fst hshift
  have hc10 : c ≤ 10 := by simpa [c, r, M] using hc
  have hpow : 3 ^ c < M := by
    have hmono : 3 ^ c ≤ 3 ^ 10 := Nat.pow_le_pow_right (by decide) hc10
    exact lt_of_le_of_lt hmono (by simpa [M] using three_pow_ten_lt_two_pow_sixteen)
  have hfail : collatzBlockFail 16 r ≤ 2 :=
    allBlockFailBounded_sound 2 M 16 (by simpa [M] using collatz_block_fail_bounded) r hr
  rw [himg, hnM]
  by_cases himglt : img < r
  · have hmul : 3 ^ c * t ≤ M * t := Nat.mul_le_mul_right t (le_of_lt hpow)
    have hmul' : 3 ^ c * t ≤ t * M := by rwa [Nat.mul_comm M t] at hmul
    omega
  · have himgge : r ≤ img := by omega
    let D := M - 3 ^ c
    let q := (img - r) / D
    have hD : 0 < D := by
      have : 0 < M - 3 ^ c := Nat.sub_pos_of_lt hpow
      simpa [D] using this
    have hfail_def : collatzBlockFail 16 r = r + q * M := by
      have hnotpow : ¬ 2 ^ 16 ≤ 3 ^ (accelRun 16 r).2 := by
        simpa [c, M] using not_le_of_gt hpow
      have hnotimg : ¬ (accelRun 16 r).1 < r := by
        simpa [img] using himglt
      unfold collatzBlockFail
      simp only [hnotpow, hnotimg, ite_false, img, c, M, D, q, Nat.mul_comm]
    have hq : r + q * M ≤ 2 := by simpa [hfail_def] using hfail
    have ht : q < t := by
      by_contra hle
      have ht' : t ≤ q := Nat.le_of_not_gt hle
      have hnle : n ≤ r + q * M := by
        rw [hnM]
        exact Nat.add_le_add_left (Nat.mul_le_mul_right M ht') r
      have : n ≤ 2 := le_trans hnle hq
      omega
    have hrem : img - r < (q + 1) * D := by
      have hmod : img - r = (img - r) % D + D * q := (Nat.mod_add_div (img - r) D).symm
      have hlt : (img - r) % D < D := Nat.mod_lt _ hD
      calc
        img - r = (img - r) % D + D * q := hmod
        _ < D + D * q := Nat.add_lt_add_right hlt _
        _ = (q + 1) * D := by ring
    have hmulD : (q + 1) * D ≤ t * D := Nat.mul_le_mul_right D ht
    have hdiff : img - r < t * D := lt_of_lt_of_le hrem hmulD
    let d := img - r
    have hd : img = r + d := by
      simpa [d] using (Nat.add_sub_of_le himgge).symm
    have hdlt : d < t * D := by simpa [d] using hdiff
    have hsplit : t * D + 3 ^ c * t = t * M := by
      have hsub : D + 3 ^ c = M := by simp [D, Nat.sub_add_cancel (le_of_lt hpow)]
      calc
        t * D + 3 ^ c * t = t * D + t * 3 ^ c := by rw [Nat.mul_comm (3 ^ c) t]
        _ = t * (D + 3 ^ c) := by rw [← Nat.mul_add]
        _ = t * M := by rw [hsub]
    calc
      img + 3 ^ c * t = r + d + 3 ^ c * t := by rw [hd]
      _ < r + t * D + 3 ^ c * t := by omega
      _ = r + (t * D + 3 ^ c * t) := by rw [add_assoc]
      _ = r + t * M := by rw [hsplit]

theorem collatz_accel_sixteen_odd_le_ten_contracts {n : ℕ} (hn : 2 < n)
    (hc : (accelRun 16 n).2 ≤ 10) : (accelRun 16 n).1 < n := by
  have hc' : (accelRun 16 (n % 2 ^ 16)).2 ≤ 10 := by
    have hshift := accelRun_shift 16 (n % 2 ^ 16) (n / 2 ^ 16) (Nat.mod_lt _ (by decide))
    have hn' : n = n % 2 ^ 16 + n / 2 ^ 16 * 2 ^ 16 := by
      rw [Nat.mul_comm, Nat.mod_add_div]
    rw [← hn'] at hshift
    have hc_eq : (accelRun 16 n).2 = (accelRun 16 (n % 2 ^ 16)).2 := by
      simpa using congrArg Prod.snd hshift
    simpa [hc_eq] using hc
  exact accel_block_contracts hn hc'

/-! ### Certificate up to `2^20`, and the height of any other cycle -/

theorem collatzStep_pos {n : ℕ} (hn : 0 < n) : 0 < collatzStep n := by
  by_cases h : n % 2 = 0
  · rw [collatzStep_even h]
    exact Nat.div_pos (by omega) (by decide)
  · have h1 : n % 2 = 1 := by omega
    rw [collatzStep_odd h1]
    omega

theorem collatzIter_pos {k n : ℕ} (hn : 0 < n) : 0 < collatzIter k n := by
  induction k with
  | zero => simpa [collatzIter] using hn
  | succ k ih =>
    rw [collatzIter_succ]
    exact collatzStep_pos ih

theorem reachesOne_of_iter {k n : ℕ} (h : ReachesOne (collatzIter k n)) : ReachesOne n := by
  induction k generalizing n with
  | zero => simpa [collatzIter] using h
  | succ k ih =>
    rw [collatzIter_succ_left] at h
    exact reachesOne_of_step (ih h)

/-- `dropsBelow fuel n start` follows the ordinary orbit of `n` until it falls
strictly below `start`, or hits `1`. -/
def dropsBelow : ℕ → ℕ → ℕ → Bool
  | 0, _, _ => false
  | fuel + 1, n, start =>
    if n < start ∨ n ≤ 1 then
      true
    else
      dropsBelow fuel (collatzStep n) start

theorem dropsBelow_sound : ∀ fuel n start, dropsBelow fuel n start = true →
    ∃ k, collatzIter k n < start ∨ collatzIter k n ≤ 1
  | 0, _, _, h => by simp [dropsBelow] at h
  | fuel + 1, n, start, h => by
    by_cases hdone : n < start ∨ n ≤ 1
    · exact ⟨0, by simpa [collatzIter] using hdone⟩
    · simp only [dropsBelow, hdone, ite_false] at h
      obtain ⟨k, hk⟩ := dropsBelow_sound fuel (collatzStep n) start h
      refine ⟨k + 1, ?_⟩
      rw [collatzIter_succ_left]
      exact hk

def allDrop (lo hi fuel : ℕ) : Bool :=
  if hi < lo then
    true
  else if dropsBelow fuel lo lo = false then
    false
  else
    allDrop (lo + 1) hi fuel
termination_by hi + 1 - lo

theorem allDrop_sound : ∀ lo hi fuel, allDrop lo hi fuel = true →
    ∀ n, lo ≤ n → n ≤ hi → dropsBelow fuel n n = true
  | lo, hi, fuel, h, n, hlo, hhi => by
    by_cases hlt : hi < lo
    · omega
    · have hform : allDrop lo hi fuel =
          if dropsBelow fuel lo lo = false then false else allDrop (lo + 1) hi fuel := by
        conv_lhs => unfold allDrop
        rw [if_neg hlt]
      rw [hform] at h
      by_cases hd : dropsBelow fuel lo lo = false
      · simp [hd] at h
      · have hdrop : dropsBelow fuel lo lo = true := by
          cases hbool : dropsBelow fuel lo lo
          · exact absurd hbool hd
          · rfl
        simp [hd] at h
        by_cases hne : n = lo
        · simpa [hne] using hdrop
        · exact allDrop_sound (lo + 1) hi fuel h n (by omega) hhi

theorem reachesOne_of_drop {n : ℕ} (hn : 1 < n)
    (h : dropsBelow 400 n n = true) (ih : ∀ m, 0 < m → m < n → ReachesOne m) :
    ReachesOne n := by
  obtain ⟨k, hk⟩ := dropsBelow_sound 400 n n h
  rcases hk with hlt | hle
  · have hm : 0 < collatzIter k n := collatzIter_pos (by omega)
    exact reachesOne_of_iter (ih _ hm hlt)
  · have h1 : collatzIter k n = 1 := by
      have hpos : 0 < collatzIter k n := collatzIter_pos (by omega)
      omega
    exact reachesOne_of_iter (h1 ▸ reachesOne_one)

theorem reachesOne_of_allDrop {N : ℕ} (h : allDrop 1 N 400 = true) :
    ∀ n, 1 ≤ n → n ≤ N → ReachesOne n := by
  intro n hn1 hnN
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases h1 : n ≤ 1
    · have : n = 1 := by omega
      simpa [this] using reachesOne_one
    · have hdrop : dropsBelow 400 n n = true := allDrop_sound 1 N 400 h n hn1 hnN
      exact reachesOne_of_drop (by omega) hdrop (fun m hm hlt => ih m hlt (by omega) (by omega))

-- The orbit search is a tail recursion of length `2^20`; the limit only lets the
-- compiler finish checking the resulting proof term.
set_option maxHeartbeats 0 in
set_option maxRecDepth 2000000 in
theorem allDrop_two_pow_twenty : allDrop 1 (2 ^ 20) 400 = true := by
  native_decide

theorem reachesOne_of_le_two_pow_twenty {n : ℕ} (hn1 : 1 ≤ n) (hn : n ≤ 2 ^ 20) :
    ReachesOne n :=
  reachesOne_of_allDrop allDrop_two_pow_twenty n hn1 hn

theorem log_nat_two_pow (k : ℕ) :
    Real.log ((2 ^ k : ℕ) : ℝ) = (k : ℝ) * Real.log 2 := by
  have hpow : ((2 ^ k : ℕ) : ℝ) = (2 : ℝ) ^ k := by norm_cast
  rw [hpow]
  simpa using Real.log_pow (2 : ℝ) k

theorem collatzHeight_strictMono {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) (hlt : m < n) :
    collatzHeight m hm < collatzHeight n hn := by
  rw [collatzHeight_eq_mul, collatzHeight_eq_mul]
  have hcoef : (0 : ℝ) < 16 / (3 * Real.pi ^ 2) := by positivity
  have hmpos : (0 : ℝ) < m := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm)
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hlog : Real.log m < Real.log n := Real.log_lt_log hmpos (by exact_mod_cast hlt)
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hm
  have hlogm : 0 ≤ Real.log m := Real.log_nonneg hm1
  have hlogn : 0 ≤ Real.log n := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
    exact Real.log_nonneg this
  have hsq : (Real.log m) ^ 2 < (Real.log n) ^ 2 := by
    rw [pow_two, pow_two]
    exact mul_lt_mul'' hlog hlog hlogm hlogm
  exact mul_lt_mul_of_pos_left hsq hcoef

theorem collatzHeight_two_pow_twenty_gt_hundred :
    100 < collatzHeight (2 ^ 20) (by decide : 2 ^ 20 ≠ 0) := by
  rw [collatzHeight_eq_mul, log_nat_two_pow]
  have hsq : (↑(20 : ℕ) * Real.log 2) ^ 2 = 400 * (Real.log 2) ^ 2 := by ring
  rw [hsq]
  have hbound : 3 * Real.pi ^ 2 < 64 * (Real.log 2) ^ 2 := log_two_sq_bound
  have hden : (0 : ℝ) < 3 * Real.pi ^ 2 := by positivity
  have heq : (16 / (3 * Real.pi ^ 2)) * (400 * (Real.log 2) ^ 2) =
      (6400 * (Real.log 2) ^ 2) / (3 * Real.pi ^ 2) := by ring
  rw [heq, lt_div_iff₀ hden]
  have : 100 * (3 * Real.pi ^ 2) < 100 * (64 * (Real.log 2) ^ 2) :=
    mul_lt_mul_of_pos_left hbound (by norm_num)
  nlinarith

theorem collatz_periodic_above_bound_height {n : ℕ} (hper : IsCollatzPeriodic n)
    (hn : 2 ^ 20 < n) :
    ∀ j, 100 < collatzHeight (collatzIter j n)
      (Nat.pos_iff_ne_zero.mp (collatzIter_pos (by omega : 0 < n))) := by
  intro j
  have hgt : 2 ^ 20 < collatzIter j n := by
    by_contra hle
    have hmj : collatzIter j n ≤ 2 ^ 20 := by omega
    have hpos : 0 < collatzIter j n := collatzIter_pos (by omega)
    have hreach_m : ReachesOne (collatzIter j n) :=
      reachesOne_of_le_two_pow_twenty (Nat.succ_le_of_lt hpos) hmj
    have hreach_n : ReachesOne n := reachesOne_of_iter hreach_m
    have hmem := periodic_reachesOne_mem_421 hper hreach_n
    omega
  have hne : collatzIter j n ≠ 0 :=
    Nat.pos_iff_ne_zero.mp (collatzIter_pos (by omega))
  exact lt_trans collatzHeight_two_pow_twenty_gt_hundred
    (collatzHeight_strictMono (by decide : (2 ^ 20) ≠ 0) hne hgt)

/-! ### Classical Collatz under an explicit bridge hypothesis -/

/--
A counterexample would have to produce a cycle that avoids `1` and stays inside
normalised height `1`. No such cycle exists, so the implication is vacuous
precisely when every orbit reaches `1`. The bridge is therefore equivalent to
the classical conjecture (`collatzAdmissibleBridge_iff`), not a reduction of it.
-/
def CollatzAdmissibleBridge : Prop :=
  ∀ n : ℕ, 0 < n → ¬ ReachesOne n →
    ∃ s : Finset ℕ,
      IsCollatzCycle s ∧
        (∀ m ∈ s, 0 < m) ∧
        1 ∉ s ∧
        (∀ m ∈ s, ∀ hm : m ≠ 0, collatzHeight m hm ≤ 1)

/-- Conditional DST recovery of the Collatz conjecture. -/
theorem collatz_conjecture_of_bridge (hbridge : CollatzAdmissibleBridge) :
    ∀ n : ℕ, 0 < n → ReachesOne n := by
  intro n hn
  by_contra hnot
  obtain ⟨s, hcyc, hpos, hone, hht⟩ := hbridge n hn hnot
  obtain ⟨m, hm, hmne, hgt⟩ := collatz_cycle_avoids_one_exceeds_bound hcyc hpos hone
  exact (not_le_of_gt hgt) (hht m hm hmne)

theorem collatzAdmissibleBridge_of_reachesOne
    (h : ∀ n : ℕ, 0 < n → ReachesOne n) : CollatzAdmissibleBridge := by
  intro n hn hnot
  exact absurd (h n hn) hnot

theorem collatzAdmissibleBridge_iff :
    CollatzAdmissibleBridge ↔ (∀ n : ℕ, 0 < n → ReachesOne n) :=
  ⟨collatz_conjecture_of_bridge, collatzAdmissibleBridge_of_reachesOne⟩

end Theorems

end DstDiophantine
