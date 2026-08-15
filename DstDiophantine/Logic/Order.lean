/-
Copyright (c) 2026 DstDiophantine contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DstDiophantine contributors
-/
import DstDiophantine.Logic.TruthValue
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Tactic.Linarith

/-!
# Two DST-native orders on the signed height

These are not the Belnap FOUR orders. Labels `{T,U,F,B}` do not match
`{⊥, t, f, ⊤}`, and no bilattice isomorphism is claimed.

* Height order `HeightLE`: more rotation-dominant → more boost-dominant.
* Information order `InfoLE`: less decided → more saturated.

On `[-1,1]`, `T` (`j = 0`) is the unique information bottom, and the two
information tops are `F` (`j = 1`) and deepest `B` (`j = -1`).
-/

namespace DstDiophantine

namespace Logic

/-- Height (truth-direction) preorder: the usual order of `ℝ`. -/
def HeightLE (j k : ℝ) : Prop :=
  j ≤ k

/-- Information (saturation) preorder. -/
def InfoLE (j k : ℝ) : Prop :=
  |j| ≤ |k|

theorem HeightLE.refl (j : ℝ) : HeightLE j j :=
  le_rfl

theorem HeightLE.trans {j k ℓ : ℝ} (hjk : HeightLE j k) (hkl : HeightLE k ℓ) :
    HeightLE j ℓ :=
  le_trans hjk hkl

theorem InfoLE.refl (j : ℝ) : InfoLE j j :=
  le_rfl

theorem InfoLE.trans {j k ℓ : ℝ} (hjk : InfoLE j k) (hkl : InfoLE k ℓ) :
    InfoLE j ℓ :=
  le_trans hjk hkl

theorem info_bottom_zero (k : ℝ) : InfoLE (0 : ℝ) k := by
  simp [InfoLE]

theorem info_le_one_of_mem {j : ℝ} (hj : |j| ≤ 1) : InfoLE j (1 : ℝ) := by
  simpa [InfoLE, abs_one] using hj

theorem info_le_neg_one_of_mem {j : ℝ} (hj : |j| ≤ 1) : InfoLE j (-1 : ℝ) := by
  simpa [InfoLE, abs_neg, abs_one] using hj

/-- On `[-1,1]`, `j = 0` is the unique information bottom. -/
theorem info_bottom_iff {j : ℝ} (_hj : |j| ≤ 1) :
    (∀ k : ℝ, |k| ≤ 1 → InfoLE j k) ↔ j = 0 := by
  constructor
  · intro h
    have hj0 : InfoLE j 0 := h 0 (by simp)
    have : |j| ≤ 0 := by
      simpa [InfoLE, abs_zero] using hj0
    exact abs_eq_zero.mp (le_antisymm this (abs_nonneg _))
  · intro hj k _hk
    simp [InfoLE, hj]

/-- On `[-1,1]`, the information tops are exactly the two walls `±1`. -/
theorem info_top_iff {j : ℝ} (hj : |j| ≤ 1) :
    (∀ k : ℝ, |k| ≤ 1 → InfoLE k j) ↔ j = 1 ∨ j = -1 := by
  constructor
  · intro h
    have : 1 ≤ |j| := by
      simpa [InfoLE, abs_one] using h 1 (by simp)
    have : |j| = 1 := le_antisymm hj this
    exact (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp this
  · intro hjk k hk
    rcases hjk with hjk | hjk <;> simpa [InfoLE, hjk, abs_neg, abs_one] using hk

theorem classify_T_iff_info_bottom {j : ℝ} (hj : |j| ≤ 1) :
    classifyOfMem j hj = .T ↔ ∀ k : ℝ, |k| ≤ 1 → InfoLE j k := by
  rw [classifyOfMem_eq_T_iff, info_bottom_iff hj]

theorem classify_F_iff_pos_info_top {j : ℝ} (hj : |j| ≤ 1) :
    classifyOfMem j hj = .F ↔ j = 1 :=
  classifyOfMem_eq_F_iff hj

theorem classify_deepB_iff {j : ℝ} (hj : |j| ≤ 1) :
    classifyOfMem j hj = .B ∧ |j| = 1 ↔ j = -1 := by
  constructor
  · intro h
    have hB := (classifyOfMem_eq_B_iff hj).mp h.1
    have : j = 1 ∨ j = -1 := (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp h.2
    rcases this with h1 | hneg
    · linarith [hB.2]
    · exact hneg
  · intro hjneg
    constructor
    · rw [classifyOfMem_eq_B_iff]
      subst hjneg
      constructor <;> norm_num
    · simp [hjneg]

/-- Interior `B` is strictly below deepest `B` in the information order. -/
theorem info_interiorB_lt_deepB {j : ℝ} (hj : |j| ≤ 1)
    (hB : classifyOfMem j hj = .B) (hne : j ≠ -1) :
    InfoLE j (-1) ∧ ¬InfoLE (-1) j := by
  have hmem := (classifyOfMem_eq_B_iff hj).mp hB
  constructor
  · exact info_le_neg_one_of_mem hj
  · intro h
    have : 1 ≤ |j| := by
      have h' : |(-1 : ℝ)| ≤ |j| := h
      rwa [abs_neg, abs_one] at h'
    have : |j| = 1 := le_antisymm hj this
    have : j = 1 ∨ j = -1 := (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp this
    rcases this with h1 | hneg
    · linarith [hmem.2]
    · exact hne hneg

end Logic

end DstDiophantine
