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

## Paper gap (not closed)

Classical Collatz (`∀ n > 0, the orbit reaches 1`) is **not** claimed
unconditionally. The paper's odd-step shear involving a cyclic generator `Γ₁`
is replaced by the pure-boost identity
`log(3n+1) = log n + log(3 + 1/n)`. Encoding every classical trajectory as a
forever-admissible flow on the finite torus (forcing periodicity of divergent
paths) is left as `CollatzAdmissibleBridge`. The attracting cycle `4 → 2 → 1`
itself need not lie entirely inside `|JNormalized| ≤ 1` under the continuous
integer embedding.
-/

namespace DstDiophantine

namespace Theorems

open Amplification Invariant Real
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

/-! ### Classical Collatz under an explicit bridge hypothesis -/

/--
Paper Chapter 9's missing bridge: a classical Collatz counterexample produces a
positive Collatz cycle that avoids `1` yet stays inside normalised height `1`.

This proposition is **not** proved in this development (it encodes the
identification of classical orbits with forever height-bounded rotor flows on
the discrete torus).
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

end Theorems

end DstDiophantine
