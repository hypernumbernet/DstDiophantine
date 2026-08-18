/-
Copyright (c) 2026 DstDiophantine contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DstDiophantine contributors
-/
import DstDiophantine.Logic.TruthValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Connectives on the signed height

Algebraic operations live on `JNormalized ∈ [-1,1]`, not on the four labels:
state-level negation is not a function of `TruthValue` (deepest `B` maps to
`F`, interior `B` maps to `U`).
-/

namespace DstDiophantine

namespace Logic

def negJ (j : ℝ) : ℝ := -j

def conjJ (a b : ℝ) : ℝ := min a b

def disjJ (a b : ℝ) : ℝ := max a b

theorem negJ_involutive (j : ℝ) : negJ (negJ j) = j :=
  neg_neg j

theorem deMorgan_conj (a b : ℝ) : negJ (conjJ a b) = disjJ (negJ a) (negJ b) := by
  simp only [negJ, conjJ, disjJ]
  rcases le_total a b with h | h
  · rw [min_eq_left h, max_eq_left (neg_le_neg h)]
  · rw [min_eq_right h, max_eq_right (neg_le_neg h)]

theorem deMorgan_disj (a b : ℝ) : negJ (disjJ a b) = conjJ (negJ a) (negJ b) := by
  simp only [negJ, conjJ, disjJ]
  rcases le_total a b with h | h
  · rw [max_eq_right h, min_eq_right (neg_le_neg h)]
  · rw [max_eq_left h, min_eq_left (neg_le_neg h)]

theorem conj_distrib_left (a b c : ℝ) :
    conjJ a (disjJ b c) = disjJ (conjJ a b) (conjJ a c) :=
  min_max_distrib_left a b c

/-- Paraconsistent non-explosion: \(j\wedge\neg j=-|j|\) never saturates `F`. -/
theorem conj_neg_eq_neg_abs (j : ℝ) : conjJ j (negJ j) = -|j| := by
  simp only [conjJ, negJ]
  rcases le_total j (-j) with h | h
  · have hj : j ≤ 0 := by linarith
    rw [min_eq_left h, abs_of_nonpos hj, neg_neg]
  · have hj : 0 ≤ j := by linarith
    rw [min_eq_right h, abs_of_nonneg hj]

theorem conj_neg_nonpos (j : ℝ) : conjJ j (negJ j) ≤ 0 := by
  rw [conj_neg_eq_neg_abs]
  exact neg_nonpos.mpr (abs_nonneg j)

theorem abs_conj_neg_le {j : ℝ} (hj : |j| ≤ 1) : |conjJ j (negJ j)| ≤ 1 := by
  rw [conj_neg_eq_neg_abs, abs_neg, abs_abs]
  exact hj

theorem classify_conj_neg_ne_F {j : ℝ} (hj : |j| ≤ 1) :
    classifyOfMem (conjJ j (negJ j)) (abs_conj_neg_le hj) ≠ .F := by
  intro hf
  rw [classifyOfMem_eq_F_iff] at hf
  rw [conj_neg_eq_neg_abs] at hf
  have : |j| = -1 := by linarith
  have : 0 ≤ |j| := abs_nonneg j
  linarith

theorem classify_conj_neg_T_or_B {j : ℝ} (hj : |j| ≤ 1) :
    classifyOfMem (conjJ j (negJ j)) (abs_conj_neg_le hj) = .T ∨
      classifyOfMem (conjJ j (negJ j)) (abs_conj_neg_le hj) = .B := by
  have hk := abs_conj_neg_le hj
  rw [classifyOfMem_eq_T_iff hk, classifyOfMem_eq_B_iff hk, conj_neg_eq_neg_abs]
  rcases eq_or_lt_of_le (abs_nonneg j) with h0 | hpos
  · left
    linarith
  · right
    constructor
    · linarith [abs_le.mp hj]
    · linarith

/-- State-level negation is not a function of the four labels. -/
theorem neg_not_a_function_of_TruthValue :
    ∃ j₁ j₂ : ℝ, ∃ h₁ : |j₁| ≤ 1, ∃ h₂ : |j₂| ≤ 1,
      classifyOfMem j₁ h₁ = .B ∧ classifyOfMem j₂ h₂ = .B ∧
        classifyOfMem (negJ j₁) (by simpa [negJ, abs_neg] using h₁) ≠
          classifyOfMem (negJ j₂) (by simpa [negJ, abs_neg] using h₂) := by
  refine ⟨-1, -1 / 2, by norm_num, by norm_num, ?_, ?_, ?_⟩
  · rw [classifyOfMem_eq_B_iff]; norm_num
  · rw [classifyOfMem_eq_B_iff]; norm_num
  · have h1' : |(1 : ℝ)| ≤ 1 := by norm_num
    have h2' : |(1 / 2 : ℝ)| ≤ 1 := by norm_num
    have hF : classifyOfMem (1 : ℝ) h1' = .F := (classifyOfMem_eq_F_iff h1').mpr rfl
    have hU : classifyOfMem (1 / 2 : ℝ) h2' = .U :=
      (classifyOfMem_eq_U_iff h2').mpr (by norm_num)
    have hL : classifyOfMem (negJ (-1)) (by unfold negJ; norm_num) =
        classifyOfMem (1 : ℝ) h1' :=
      classifyOfMem_eq_of_eq (by simp [negJ]) _ _
    have hR : classifyOfMem (negJ (-1 / 2)) (by unfold negJ; norm_num) =
        classifyOfMem (1 / 2 : ℝ) h2' :=
      classifyOfMem_eq_of_eq (by unfold negJ; ring) _ _
    rw [hL, hR, hF, hU]
    decide

end Logic

end DstDiophantine
