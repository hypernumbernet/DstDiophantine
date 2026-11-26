import DstDiophantine.Algebra.MismatchAngle
import DstDiophantine.Gravity.ElectronShell
import DstDiophantine.Gravity.TorsionalLayer

set_option linter.style.whitespace false

/-!
# Bridge: dual overlap, legacy `γ_s`, and shell charts
-/

namespace DstDiophantine

namespace Gravity

open MismatchAngle

theorem axisOverlapLegacy_eq_gammaS (α β : ℝ) : axisOverlapLegacy α β = gammaS α β := rfl

theorem axisOverlap_eq_gammaSEqual_balanced (x : ℝ) :
    axisOverlapLegacy (2 * x) (2 * x) = gammaSEqualLegacy x := by
  rw [axisOverlapLegacy_balanced]
  unfold gammaSEqualLegacy
  ring_nf

theorem dualOverlap_balanced_cosh_cos (x : ℝ) :
    dualOverlap (2 * x) (2 * x) = Real.cosh x * Real.cos x :=
  dualOverlap_balanced x

theorem dualOverlap_eq_gammaS_usual (α : ℝ) :
    dualOverlap α 0 = gammaS α 0 := by
  simp [dualOverlap, gammaS]

theorem dualOverlap_eq_gammaS_dual (β : ℝ) :
    dualOverlap 0 β = gammaS 0 β := by
  simp [dualOverlap, gammaS]

end Gravity
end DstDiophantine