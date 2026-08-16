/-
Copyright (c) 2026 DstDiophantine contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DstDiophantine contributors
-/
import DstDiophantine.Logic.Consequence
import DstDiophantine.Logic.Amplitude
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Example 1: the negation fixed-point sentence

The semantic condition `P = ¬P` is unsatisfiable in any two-valued algebra
whose negation has no fixed point. On D4L heights it is exactly `j = 0`,
the unique label `T`.

This is **not** Gödel's sentence and does **not** refute the incompleteness
theorems. It records that a self-referential equality which classical
two-valued logic cannot host has a unique D4L solution.

The faithful classical core is the *wall* fragment `{-1,1}`: there
`negJ` is a swap. The *named* fragment `{0,1}` already contains the
fixed point `0`, so it is not a Boolean negation.
-/

namespace DstDiophantine

namespace Logic

/-- Semantic fixed-point condition `j = -j`. -/
def IsNegFixed (j : ℝ) : Prop :=
  j = negJ j

theorem isNegFixed_iff_zero (j : ℝ) : IsNegFixed j ↔ j = 0 := by
  simp only [IsNegFixed, negJ]
  constructor
  · intro h
    linarith
  · intro h
    simp [h]

/-- Walls have no negation fixed point. -/
theorem wallTwo_not_negFixed {j : ℝ} (h : IsWallTwo j) : ¬ IsNegFixed j := by
  intro hf
  have hj0 : j = 0 := (isNegFixed_iff_zero j).mp hf
  rcases h with h | h <;> linarith

/-- D4L realises the fixed point (the constant-`0` valuation). -/
theorem exists_negFixed_valuation :
    ∃ v : Valuation, IsNegFixed ((Formula.atom 0).eval v.assign) :=
  ⟨Valuation.const 0 (by norm_num), by
    simp [IsNegFixed, Valuation.const]⟩

/-- No wall-restricted valuation satisfies `P = ¬P`. -/
theorem not_exists_wall_negFixed :
    ¬ ∃ v : Valuation,
        IsWallTwo (v.assign 0) ∧
          IsNegFixed ((Formula.atom 0).eval v.assign) := by
  rintro ⟨v, hw, hf⟩
  exact wallTwo_not_negFixed hw (by simpa using hf)

/-- Realised by an amplitude, not only by a scalar. -/
theorem exists_amplitude_negFixed :
    ∃ a : Amplitude, IsNegFixed a.measure := by
  obtain ⟨a, ha⟩ := exists_amplitude .T
  exact ⟨a, (isNegFixed_iff_zero _).mpr (a.measure_eq_zero_iff.mpr ha)⟩

end Logic

end DstDiophantine
