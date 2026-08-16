/-
Copyright (c) 2026 DstDiophantine contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DstDiophantine contributors
-/
import DstDiophantine.Logic.Formula
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Valuations, designated values, and two-valued fragments

A valuation assigns each atom a height in `[-1,1]`. Two designated
predicates turn heights into consequence:

* `HoldsT` — synchrony, `j = 0` (the label `T`).
* `HoldsNotF` — not refuted, `j < 1` (every label except `F`).

Two-valued *restrictions* of the interval are not unique:

* `IsNamedTwo` — `{0,1} = {T,F}`. The names match classical true/false,
  but `negJ 0 = 0`, so this fragment is not a Boolean algebra.
* `IsWallTwo` — `{-1,1}` = {deepest `B`, `F`}. Negation swaps the walls
  and has no fixed point; this is the faithful classical core.

No Belnap-FOUR isomorphism is claimed.
-/

namespace DstDiophantine

namespace Logic

/-- An assignment of atoms to admissible signed heights. -/
structure Valuation where
  assign : ℕ → ℝ
  mem : ∀ n, |assign n| ≤ 1

namespace Valuation

/-- Constant assignment. -/
def const (j : ℝ) (hj : |j| ≤ 1) : Valuation where
  assign := fun _ => j
  mem := fun _ => hj

/-- Assignment with atom `0 ↦ j`, atom `1 ↦ k`, and `0` elsewhere. -/
def pair (j k : ℝ) (hj : |j| ≤ 1) (hk : |k| ≤ 1) : Valuation where
  assign := fun n => if n = 0 then j else if n = 1 then k else 0
  mem := fun n => by
    by_cases h0 : n = 0
    · simpa [h0] using hj
    · by_cases h1 : n = 1
      · simpa [h0, h1] using hk
      · simp [h0, h1]

@[simp] theorem pair_zero (j k : ℝ) (hj : |j| ≤ 1) (hk : |k| ≤ 1) :
    (pair j k hj hk).assign 0 = j := by
  simp [pair]

@[simp] theorem pair_one (j k : ℝ) (hj : |j| ≤ 1) (hk : |k| ≤ 1) :
    (pair j k hj hk).assign 1 = k := by
  simp [pair]

/-- Every formula evaluates inside `[-1,1]`. -/
theorem eval_mem (v : Valuation) (φ : Formula) : |φ.eval v.assign| ≤ 1 :=
  φ.eval_mem v.mem

end Valuation

/-- Designated synchrony: the unique information bottom. -/
def HoldsT (j : ℝ) : Prop :=
  j = 0

/-- Designated non-refutation: every label except the positive wall `F`. -/
def HoldsNotF (j : ℝ) : Prop :=
  j < 1

/-- Named two-valued fragment `{T,F}`. -/
def IsNamedTwo (j : ℝ) : Prop :=
  j = 0 ∨ j = 1

/-- Wall two-valued fragment `{deep B, F}`. -/
def IsWallTwo (j : ℝ) : Prop :=
  j = -1 ∨ j = 1

theorem holdsT_iff_classify {j : ℝ} (hj : |j| ≤ 1) :
    HoldsT j ↔ classifyOfMem j hj = .T :=
  (classifyOfMem_eq_T_iff hj).symm

theorem holdsNotF_iff_ne_one {j : ℝ} (hj : |j| ≤ 1) :
    HoldsNotF j ↔ j ≠ 1 :=
  ⟨ne_of_lt, fun hne => lt_of_le_of_ne (abs_le.mp hj).2 hne⟩

theorem holdsNotF_iff_ne_F {j : ℝ} (hj : |j| ≤ 1) :
    HoldsNotF j ↔ classifyOfMem j hj ≠ .F := by
  rw [holdsNotF_iff_ne_one hj]
  exact (Iff.not (classifyOfMem_eq_F_iff hj)).symm

theorem holdsT_holdsNotF {j : ℝ} (h : HoldsT j) : HoldsNotF j := by
  simp [HoldsT, HoldsNotF] at h ⊢
  linarith

/-- `j ∧ ¬j` never saturates `F`. -/
theorem conj_neg_holdsNotF (j : ℝ) : HoldsNotF (conjJ j (negJ j)) := by
  unfold HoldsNotF
  rw [conj_neg_eq_neg_abs]
  linarith [abs_nonneg j]

/-- On the named fragment, non-refutation collapses to synchrony. -/
theorem namedTwo_holdsNotF_iff_holdsT {j : ℝ} (h : IsNamedTwo j) :
    HoldsNotF j ↔ HoldsT j := by
  rcases h with h | h <;> simp [HoldsNotF, HoldsT, h]

/-- Named two-valued ∩ not-`F` is exactly `{T}`. -/
theorem namedTwo_notF_only_T {j : ℝ} :
    IsNamedTwo j ∧ HoldsNotF j ↔ j = 0 := by
  constructor
  · intro h
    exact (namedTwo_holdsNotF_iff_holdsT h.1).mp h.2
  · intro hj
    exact ⟨Or.inl hj, by simp [HoldsNotF, hj]⟩

@[simp] theorem negJ_zero : negJ (0 : ℝ) = 0 :=
  neg_zero

/-- The named fragment is not closed under D4L negation: `F ↦` deepest `B`. -/
theorem namedTwo_not_closed_under_neg :
    ∃ j, IsNamedTwo j ∧ ¬ IsNamedTwo (negJ j) :=
  ⟨1, Or.inr rfl, by simp [IsNamedTwo, negJ]; norm_num⟩

theorem wallTwo_neg {j : ℝ} (h : IsWallTwo j) : IsWallTwo (negJ j) := by
  rcases h with h | h <;> simp [IsWallTwo, negJ, h]

/-- On the walls, a value and its negation cannot both be `+1`. -/
theorem wall_not_both_pos {j : ℝ} (h : IsWallTwo j) :
    ¬ (j = 1 ∧ negJ j = 1) := by
  rcases h with h | h <;> simp [negJ, h] <;> norm_num

theorem exists_holdsNotF_label {tv : TruthValue} (hne : tv ≠ .F) :
    ∃ (j : ℝ) (hj : |j| ≤ 1),
      classifyOfMem j hj = tv ∧ HoldsNotF j := by
  cases tv with
  | T =>
    refine ⟨0, by norm_num, ?_, by norm_num [HoldsNotF]⟩
    exact (classifyOfMem_eq_T_iff (by norm_num : |(0 : ℝ)| ≤ 1)).mpr rfl
  | U =>
    refine ⟨(1 / 2 : ℝ), by norm_num, ?_, by norm_num [HoldsNotF]⟩
    exact (classifyOfMem_eq_U_iff (by norm_num : |(1 / 2 : ℝ)| ≤ 1)).mpr
      (by norm_num)
  | F => exact (hne rfl).elim
  | B =>
    refine ⟨(-1 / 2 : ℝ), by norm_num, ?_, by norm_num [HoldsNotF]⟩
    exact (classifyOfMem_eq_B_iff (by norm_num : |(-1 / 2 : ℝ)| ≤ 1)).mpr
      (by norm_num)

end Logic

end DstDiophantine
