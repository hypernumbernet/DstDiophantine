import DstDiophantine.Algebra.MismatchAngle
import DstDiophantine.Gravity.ElectronShell
import DstDiophantine.Gravity.TorsionalLayer

set_option linter.style.whitespace false

/-!
# Bridge: algebra mismatch overlap and shell interference `γ_s`
-/

namespace DstDiophantine

namespace Gravity

open MismatchAngle

theorem axisOverlap_eq_gammaS (α β : ℝ) :
    MismatchAngle.axisOverlapScalar α β = gammaS α β := rfl

theorem axisOverlap_eq_gammaSEqual_balanced (x : ℝ) :
    MismatchAngle.axisOverlapScalar (2 * x) (2 * x) = gammaSEqual x := by
  rw [MismatchAngle.axisOverlap_balanced]
  unfold gammaSEqual
  ring_nf

end Gravity
end DstDiophantine