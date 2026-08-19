/-
Copyright (c) 2026 DstDiophantine contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DstDiophantine contributors
-/
import DstDiophantine.Logic.TruthValue
import DstDiophantine.Algebra.ModularAmplification

/-!
# Two D4L observables: height and winding

Real-scale admissibility and nonzero modular winding cannot hold together
(`admissible_scale_implies_windingTotal_eq_zero`). This is a separation of
two measurements, not a Both-status on one observable. No new arithmetic.

Does not import `Theorems`.
-/

namespace DstDiophantine

namespace Logic

open Discrete ModularAmplification

variable {N : ℕ} [NeZero N]

/-- The two measurements are not simultaneously designated:
admissible real-scale amplification and nonzero winding. -/
theorem not_both_admissibleScale_and_winding (k : ℕ) (t : DiscreteTorsion N) :
    ¬ (IsAdmissibleContinuous (Amplification.scaleTorsion (k : ℝ) (toTorsionParams t)) ∧
        windingTotal k t ≠ 0) := by
  rintro ⟨hadm, hw⟩
  exact hw (admissible_scale_implies_windingTotal_eq_zero k t hadm)

/-- Dual form, already proved in the algebra: winding rules out the cone. -/
theorem winding_not_admissibleScale (k : ℕ) (t : DiscreteTorsion N)
    (hw : windingTotal k t ≠ 0) :
    ¬ IsAdmissibleContinuous (Amplification.scaleTorsion (k : ℝ) (toTorsionParams t)) :=
  windingTotal_ne_zero_implies_not_admissible_scale k t hw

end Logic

end DstDiophantine
