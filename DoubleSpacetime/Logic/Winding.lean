import DoubleSpacetime.Logic.TruthValue
import DoubleSpacetime.Algebra.ModularAmplification

/-!
# Height and winding

Admissible real scale and nonzero winding cannot hold together. This separates two measurements; it
is not a Both-status on one observable.
-/

namespace DoubleSpacetime

namespace Logic

open Discrete ModularAmplification

variable {N : ℕ} [NeZero N]

theorem not_both_admissibleScale_and_winding (k : ℕ) (t : DiscreteTorsion N) :
    ¬ (IsAdmissibleContinuous (Amplification.scaleTorsion (k : ℝ) (toTorsionParams t)) ∧
        windingTotal k t ≠ 0) := by
  rintro ⟨hadm, hw⟩
  exact hw (admissible_scale_implies_windingTotal_eq_zero k t hadm)

/-- Already proved in the algebra. -/
theorem winding_not_admissibleScale (k : ℕ) (t : DiscreteTorsion N)
    (hw : windingTotal k t ≠ 0) :
    ¬ IsAdmissibleContinuous (Amplification.scaleTorsion (k : ℝ) (toTorsionParams t)) :=
  windingTotal_ne_zero_implies_not_admissible_scale k t hw

end Logic

end DoubleSpacetime
