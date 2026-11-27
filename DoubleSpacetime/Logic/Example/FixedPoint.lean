import DoubleSpacetime.Logic.Consequence
import DoubleSpacetime.Logic.Amplitude
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Negation fixed point

`j = -j` holds exactly at `0`. The wall fragment `{-1, 1}` has none.
-/

namespace DoubleSpacetime

namespace Logic

/-- `j = -j`. -/
def IsNegFixed (j : ℝ) : Prop :=
  j = negJ j

theorem isNegFixed_iff_zero (j : ℝ) : IsNegFixed j ↔ j = 0 := by
  simp only [IsNegFixed, negJ]
  constructor
  · intro h
    linarith
  · intro h
    simp [h]

theorem wallTwo_not_negFixed {j : ℝ} (h : IsWallTwo j) : ¬ IsNegFixed j := by
  intro hf
  have hj0 : j = 0 := (isNegFixed_iff_zero j).mp hf
  rcases h with h | h <;> linarith

theorem exists_negFixed_valuation :
    ∃ v : Valuation, IsNegFixed ((Formula.atom 0).eval v.assign) :=
  ⟨Valuation.const 0 (by norm_num), by
    simp [IsNegFixed, Valuation.const]⟩

theorem not_exists_wall_negFixed :
    ¬ ∃ v : Valuation,
        IsWallTwo (v.assign 0) ∧
          IsNegFixed ((Formula.atom 0).eval v.assign) := by
  rintro ⟨v, hw, hf⟩
  exact wallTwo_not_negFixed hw (by simpa using hf)

theorem exists_amplitude_negFixed :
    ∃ a : Amplitude, IsNegFixed a.measure := by
  obtain ⟨a, ha⟩ := exists_amplitude .T
  exact ⟨a, (isNegFixed_iff_zero _).mpr (a.measure_eq_zero_iff.mpr ha)⟩

end Logic

end DoubleSpacetime
