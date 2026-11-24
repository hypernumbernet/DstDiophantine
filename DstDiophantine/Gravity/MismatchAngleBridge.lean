import DstDiophantine.Algebra.MismatchAngle
import DstDiophantine.Gravity.ElectronShell
import DstDiophantine.Gravity.TorsionalLayer

set_option linter.style.whitespace false

/-!
# Bridge: primary overlap, legacy `γ_s`, and shell charts
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

theorem axisOverlap_primary_balanced (x : ℝ) :
    axisOverlapScalar (2 * x) (2 * x) = Real.cosh x * Real.cos x :=
  axisOverlap_balanced x

theorem axisOverlap_primary_eq_gammaS_usual (α : ℝ) :
    axisOverlapScalar α 0 = gammaS α 0 := by
  simp [axisOverlapScalar, gammaS]

theorem axisOverlap_primary_eq_gammaS_dual (β : ℝ) :
    axisOverlapScalar 0 β = gammaS 0 β := by
  simp [axisOverlapScalar, gammaS]

end Gravity
end DstDiophantine