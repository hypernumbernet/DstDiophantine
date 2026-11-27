import DoubleSpacetime.Logic.Consequence
import DoubleSpacetime.Logic.Amplitude

/-!
# Non-refutation

`HoldsNotF` leaves `{T, U, B}`. On `{0, 1}` it leaves only `0`.
-/

namespace DoubleSpacetime

namespace Logic

theorem exists_three_notF_labels :
    (∃ (j : ℝ) (hj : |j| ≤ 1), classifyOfMem j hj = .T ∧ HoldsNotF j) ∧
      (∃ (j : ℝ) (hj : |j| ≤ 1), classifyOfMem j hj = .U ∧ HoldsNotF j) ∧
        (∃ (j : ℝ) (hj : |j| ≤ 1), classifyOfMem j hj = .B ∧ HoldsNotF j) :=
  ⟨exists_holdsNotF_label (by decide : TruthValue.T ≠ .F),
    exists_holdsNotF_label (by decide : TruthValue.U ≠ .F),
    exists_holdsNotF_label (by decide : TruthValue.B ≠ .F)⟩

theorem exists_amplitude_notF (tv : TruthValue) (hne : tv ≠ .F) :
    ∃ a : Amplitude, a.collapse = tv ∧ HoldsNotF a.measure := by
  obtain ⟨a, ha⟩ := exists_amplitude tv
  refine ⟨a, ha, ?_⟩
  have hj := a.abs_measure
  have : classifyOfMem a.measure hj = tv := by
    simpa [Amplitude.collapse_eq_classify] using ha
  exact (holdsNotF_iff_ne_F hj).mpr (by simp [this, hne])

end Logic

end DoubleSpacetime
