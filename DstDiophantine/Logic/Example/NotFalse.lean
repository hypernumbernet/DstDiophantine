/-
Copyright (c) 2026 DstDiophantine contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DstDiophantine contributors
-/
import DstDiophantine.Logic.Consequence
import DstDiophantine.Logic.Amplitude
import DstDiophantine.Logic.Potential

/-!
# Example 3: the constraint `JNormalized < 1`

A sentence forbidden from sitting at the unique all-boost world is the
constraint `HoldsNotF`. On the named two-valued fragment `{T,F}` this
leaves only `T`. On D4L it leaves `{T,U,B}`.

This is the Lean form of the paper's self-reference reading. It is a
change of semantics, **not** a proof that Gödel's theorems fail in
classical arithmetic, and not a completion of the Hilbert programme
inside Peano arithmetic.
-/

namespace DstDiophantine

namespace Logic

/-- D4L realises three distinct non-refuted labels. -/
theorem exists_three_notF_labels :
    (∃ (j : ℝ) (hj : |j| ≤ 1), classifyOfMem j hj = .T ∧ HoldsNotF j) ∧
      (∃ (j : ℝ) (hj : |j| ≤ 1), classifyOfMem j hj = .U ∧ HoldsNotF j) ∧
        (∃ (j : ℝ) (hj : |j| ≤ 1), classifyOfMem j hj = .B ∧ HoldsNotF j) :=
  ⟨exists_holdsNotF_label (by decide : TruthValue.T ≠ .F),
    exists_holdsNotF_label (by decide : TruthValue.U ≠ .F),
    exists_holdsNotF_label (by decide : TruthValue.B ≠ .F)⟩

/-- Interior `U` is not an attractor of the large-scale flow; the
constraint `j < 1` still inhabits it as a *label*. -/
theorem notF_inhabits_U_not_attractor :
    (∃ (j : ℝ) (hj : |j| ≤ 1), classifyOfMem j hj = .U ∧ HoldsNotF j) ∧
      flowInf (1 / 2 : ℝ) = 0 ∧
        (2 * Real.pi) ^ 2 * Real.cos (2 * Real.pi * (1 / 2 : ℝ)) < 0 :=
  ⟨exists_holdsNotF_label (by decide : TruthValue.U ≠ .F),
    flowInf_eq_zero_at_half, VInf_second_neg_at_half⟩

/-- Amplitudes realise every non-refuted label. -/
theorem exists_amplitude_notF (tv : TruthValue) (hne : tv ≠ .F) :
    ∃ a : Amplitude, a.collapse = tv ∧ HoldsNotF a.measure := by
  obtain ⟨a, ha⟩ := exists_amplitude tv
  refine ⟨a, ha, ?_⟩
  have hj := a.abs_measure
  have : classifyOfMem a.measure hj = tv := by
    simpa [Amplitude.collapse_eq_classify] using ha
  exact (holdsNotF_iff_ne_F hj).mpr (by simp [this, hne])

end Logic

end DstDiophantine
