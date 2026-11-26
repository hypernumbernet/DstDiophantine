import DstDiophantine.Gravity.GaugeDictionary
import DstDiophantine.Gravity.MismatchAngleBridge
import DstDiophantine.Gravity.ElectronShell
import Mathlib.Tactic.Positivity

set_option linter.style.whitespace false

/-!
# Repulsion via dual overlap (`cosh·cos`)

Dual overlap vanishes only when `cos(β/2)=0` (rotation mismatch `β=π` on-axis);
`cosh(α/2)` scales magnitude with boost. Legacy `gammaS` charts remain in
`ElectronShell` / `TorsionalLayer` unchanged.
-/

namespace DstDiophantine

namespace Gravity

open MismatchAngle RelativeRotor Invariant Real

/-! ### Pure boost cannot switch overlap sign -/

theorem dualOverlap_strict_pos_dual_zero (α : ℝ) :
    1 ≤ dualOverlap α 0 := by
  have h : dualOverlap α 0 = Real.cosh (α / 2) := by
    simp [dualOverlap, Real.cos_zero]
  rw [h]
  exact Real.one_le_cosh (α / 2)

theorem not_repulsive_pure_boost (α : ℝ) : ¬ dualOverlap α 0 < 0 := by
  intro h
  linarith [dualOverlap_strict_pos_dual_zero α]

theorem dualOverlap_eq_gammaS_dual_zero (α : ℝ) :
    dualOverlap α 0 = gammaS α 0 :=
  dualOverlap_eq_gammaS_usual α

/-! ### Sign reversal (primary): rotation π, not legacy mixed node -/

theorem repulsive_equal_scale_J_zero_overlap_zero :
    J (axisParams Real.pi Real.pi) = 0 ∧
      dualOverlap Real.pi Real.pi = 0 := by
  refine ⟨J_axisParams_balanced Real.pi, ?_⟩
  simp [dualOverlap, Real.cos_pi]

theorem legacy_overlap_neg_at_balanced_pi :
    axisOverlapLegacy Real.pi Real.pi < 0 ∧
      gammaS Real.pi Real.pi < 0 := by
  refine ⟨axisOverlapLegacy_sign_reversal_at_pi.2, ?_⟩
  rw [← axisOverlapLegacy_eq_gammaS]
  exact axisOverlapLegacy_sign_reversal_at_pi.2

theorem repulsive_equal_scale_legacy_gammaSEqual :
    gammaSEqualLegacy (Real.pi / 2) < 0 ∧
      axisOverlapLegacy (Real.pi) (Real.pi) = gammaSEqualLegacy (Real.pi / 2) := by
  constructor
  · unfold gammaSEqualLegacy
    have hpos : 0 < Real.pi / 2 := by linarith [Real.pi_pos]
    simp [Real.cos_pi_div_two, Real.sin_pi_div_two, Real.sinh_pos_iff.mpr hpos]
  · have hπ : (2 : ℝ) * (Real.pi / 2) = Real.pi := by ring
    simpa [hπ] using axisOverlap_eq_gammaSEqual_balanced (Real.pi / 2)

theorem dualOverlap_zero_legacy_neg_witness :
    dualOverlap Real.pi Real.pi = 0 ∧
      axisOverlapLegacy Real.pi Real.pi < 0 ∧
        J (axisParams Real.pi Real.pi) = 0 :=
  ⟨repulsive_equal_scale_J_zero_overlap_zero.2,
    ⟨axisOverlapLegacy_sign_reversal_at_pi.2, J_axisParams_balanced Real.pi⟩⟩

/-! ### Legacy teleparallel chart (J diagnostic) -/

theorem repulsive_teleparallel_forces_negative_J {Jval r : ℝ} (hr : r ≠ 0)
    (hbound : |Jval| ≤ JMax) (hT : teleparallelTofJ Jval r < 0) : Jval < 0 :=
  repulsive_requires_negative_J hr hbound hT

end Gravity
end DstDiophantine