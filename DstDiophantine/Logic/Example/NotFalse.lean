import DstDiophantine.Logic.Consequence
import DstDiophantine.Logic.Amplitude

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
