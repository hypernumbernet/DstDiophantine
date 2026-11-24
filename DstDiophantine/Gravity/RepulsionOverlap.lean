import DstDiophantine.Gravity.GaugeDictionary
import DstDiophantine.Gravity.MismatchAngleBridge
import DstDiophantine.Gravity.ElectronShell
import Mathlib.Tactic.Positivity

set_option linter.style.whitespace false

/-!
# Repulsion via overlap (angle-first)

Repulsive shell layers are gated by the **overlap scalar** `axisOverlapScalar`
(= `gammaS` on one axis), not by the Killing diagnostic `J` alone. The legacy
teleparallel chart still yields `repulsive_requires_negative_J` as a corollary
on the `J` cone.
-/

namespace DstDiophantine

namespace Gravity

open MismatchAngle RelativeRotor Invariant Real

/-! ### Pure boost cannot switch overlap sign -/

theorem axisOverlap_strict_pos_dual_zero (α : ℝ) :
    1 ≤ axisOverlapScalar α 0 := by
  have h : axisOverlapScalar α 0 = Real.cosh (α / 2) := by
    unfold axisOverlapScalar pgaAxisMotorGradeZero
    simp [Real.sin_zero, Real.cos_zero]
  rw [h]
  exact Real.one_le_cosh (α / 2)

theorem not_repulsive_pure_boost (α : ℝ) : ¬ axisOverlapScalar α 0 < 0 := by
  intro h
  linarith [axisOverlap_strict_pos_dual_zero α]

theorem axisOverlap_eq_gammaS_dual_zero (α : ℝ) :
    axisOverlapScalar α 0 = gammaS α 0 :=
  axisOverlap_eq_gammaS α 0

theorem not_repulsive_pure_gammaS (α : ℝ) : ¬ gammaS α 0 < 0 := by
  rw [← axisOverlap_eq_gammaS_dual_zero α]
  exact not_repulsive_pure_boost α

/-! ### Equal-scale repulsion at rotation threshold -/

/-- `J = 0` on the balanced ray but overlap turns negative at half-angle `π/2`. -/
theorem repulsive_equal_scale_J_zero_overlap_neg :
    J (axisParams Real.pi Real.pi) = 0 ∧
      axisOverlapScalar Real.pi Real.pi < 0 ∧
        gammaS Real.pi Real.pi < 0 := by
  refine ⟨J_axisParams_balanced Real.pi, ?_, ?_⟩
  · exact axisOverlap_balanced_neg_at_half_pi
  · rw [← axisOverlap_eq_gammaS Real.pi Real.pi]
    exact axisOverlap_balanced_neg_at_half_pi

theorem repulsive_equal_scale_gammaSEqual :
    gammaSEqual (Real.pi / 2) < 0 ∧
      axisOverlapScalar (2 * (Real.pi / 2)) (2 * (Real.pi / 2)) =
        gammaSEqual (Real.pi / 2) := by
  have heq := axisOverlap_eq_gammaSEqual_balanced (Real.pi / 2)
  have hO : axisOverlapScalar (2 * (Real.pi / 2)) (2 * (Real.pi / 2)) < 0 := by
    rw [show (2 : ℝ) * (Real.pi / 2) = Real.pi by ring]
    exact axisOverlap_balanced_neg_at_half_pi
  constructor
  · rw [← heq]
    exact hO
  · exact heq

/-! ### Legacy teleparallel chart (J diagnostic) -/

/-- Teleparallel sign on the `J` cone (diagnostic corollary of `repulsive_requires_negative_J`). -/
theorem repulsive_teleparallel_forces_negative_J {Jval r : ℝ} (hr : r ≠ 0)
    (hbound : |Jval| ≤ JMax) (hT : teleparallelTofJ Jval r < 0) : Jval < 0 :=
  repulsive_requires_negative_J hr hbound hT

/-- Negative overlap does **not** force `J < 0` on the balanced ray (`J = 0`, overlap `< 0`). -/
theorem overlap_neg_not_J_neg_witness : axisOverlapScalar Real.pi Real.pi < 0 ∧
    J (axisParams Real.pi Real.pi) = 0 := by
  refine ⟨axisOverlap_balanced_neg_at_half_pi, J_axisParams_balanced Real.pi⟩

end Gravity
end DstDiophantine