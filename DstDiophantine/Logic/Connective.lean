/-
Copyright (c) 2026 DstDiophantine contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DstDiophantine contributors
-/
import DstDiophantine.Logic.TruthValue
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.Order.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Connectives on the signed height, and the softmin family

Algebraic operations live on `JNormalized ∈ [-1,1]`, not on the four labels:
state-level negation is not a function of `TruthValue` (deepest `B` maps to
`F`, interior `B` maps to `U`).

The scale-deformed conjunction is the softmin. Large
inverse-temperature recovers `min`. Small inverse-temperature diverges to
\(-\infty\); it is not a binary hard decision.
-/

namespace DstDiophantine

namespace Logic

open Filter Real Topology

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

/-- Softmin conjunction, \(\beta>0\). -/
noncomputable def softmin (β a b : ℝ) : ℝ :=
  -(1 / β) * Real.log (Real.exp (-β * a) + Real.exp (-β * b))

theorem softmin_eq_min_sub (β a b : ℝ) (hβ : β ≠ 0) :
    softmin β a b =
      min a b - (1 / β) * Real.log (1 + Real.exp (-β * |a - b|)) := by
  unfold softmin
  rcases le_total a b with hab | hba
  · have hmin : min a b = a := min_eq_left hab
    have habs : |a - b| = b - a := by
      rw [abs_of_nonpos (sub_nonpos.mpr hab), neg_sub]
    have hfac :
        Real.exp (-β * a) + Real.exp (-β * b) =
          Real.exp (-β * a) * (1 + Real.exp (-β * (b - a))) := by
      have : Real.exp (-β * b) = Real.exp (-β * a) * Real.exp (-β * (b - a)) := by
        rw [← Real.exp_add]; ring_nf
      rw [this]; ring
    rw [hmin, habs, hfac, Real.log_mul (Real.exp_pos _).ne' (by positivity), Real.log_exp]
    field_simp [hβ]
    ring
  · have hmin : min a b = b := min_eq_right hba
    have habs : |a - b| = a - b := abs_of_nonneg (sub_nonneg.mpr hba)
    have hfac :
        Real.exp (-β * a) + Real.exp (-β * b) =
          Real.exp (-β * b) * (1 + Real.exp (-β * (a - b))) := by
      have : Real.exp (-β * a) = Real.exp (-β * b) * Real.exp (-β * (a - b)) := by
        rw [← Real.exp_add]; ring_nf
      rw [this]; ring
    rw [hmin, habs, hfac, Real.log_mul (Real.exp_pos _).ne' (by positivity), Real.log_exp]
    field_simp [hβ]
    ring

private theorem tendsto_inv_mul_log2 :
    Tendsto (fun β : ℝ => (1 / β) * Real.log 2) atTop (𝓝 0) := by
  simpa [div_eq_mul_inv] using tendsto_inv_atTop_zero.mul_const (Real.log 2)

private theorem tendsto_log_one_add_exp_div (δ : ℝ) (hδ : 0 ≤ δ) :
    Tendsto (fun β : ℝ => (1 / β) * Real.log (1 + Real.exp (-β * δ))) atTop (𝓝 0) := by
  rcases eq_or_lt_of_le hδ with h0 | hpos
  · subst h0
    simp only [mul_zero, Real.exp_zero]
    have : (1 : ℝ) + 1 = 2 := by norm_num
    simpa [this] using tendsto_inv_mul_log2
  · have hexp : Tendsto (fun β : ℝ => Real.exp (-β * δ)) atTop (𝓝 0) := by
      have hbot : Tendsto (fun β : ℝ => -β * δ) atTop atBot := by
        simpa [mul_comm] using tendsto_neg_atTop_atBot.atBot_mul_const hpos
      exact Real.tendsto_exp_atBot.comp hbot
    have hlog : Tendsto (fun β : ℝ => Real.log (1 + Real.exp (-β * δ))) atTop (𝓝 0) := by
      have hlim : Tendsto (fun β : ℝ => (1 : ℝ) + Real.exp (-β * δ)) atTop (𝓝 (1 + 0)) :=
        tendsto_const_nhds.add hexp
      have := hlim.log (by norm_num)
      simpa using this
    have hinv : Tendsto (fun β : ℝ => (1 : ℝ) / β) atTop (𝓝 0) := by
      simpa [one_div] using tendsto_inv_atTop_zero
    simpa using hinv.mul hlog

theorem tendsto_softmin_atTop (a b : ℝ) :
    Tendsto (fun β : ℝ => softmin β a b) atTop (𝓝 (min a b)) := by
  have hmain :
      Tendsto (fun β : ℝ => min a b - (1 / β) * Real.log (1 + Real.exp (-β * |a - b|)))
        atTop (𝓝 (min a b)) := by
    simpa using tendsto_const_nhds.sub (tendsto_log_one_add_exp_div _ (abs_nonneg _))
  refine hmain.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with β hβ
  exact (softmin_eq_min_sub β a b hβ.ne').symm

/-- Softmin is strictly below `min` for every finite positive inverse temperature.
In particular the small-`β` regime is not a binary hard decision. -/
theorem softmin_lt_min {β a b : ℝ} (hβ : 0 < β) :
    softmin β a b < min a b := by
  rw [softmin_eq_min_sub β a b hβ.ne']
  have hlog : 0 < Real.log (1 + Real.exp (-β * |a - b|)) := by
    apply Real.log_pos
    nlinarith [Real.exp_pos (-β * |a - b|)]
  have : 0 < (1 / β) * Real.log (1 + Real.exp (-β * |a - b|)) :=
    mul_pos (one_div_pos.mpr hβ) hlog
  linarith

end Logic

end DstDiophantine
