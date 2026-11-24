import DstDiophantine.Algebra.MismatchAngle
import DstDiophantine.Algebra.Admissible

set_option linter.style.whitespace false

/-!
# Admissible cone in overlap coordinates (open)

Restating `|JNormalized| ≤ 1` and the four D4L regime boundaries using mismatch
half-coefficients is currently under research.
-/

namespace Goals.Diophantine

open DstDiophantine
open Operations Admissible MismatchAngle

/-- Open: box bound on mismatch half-coefficients equivalent to admissibility. -/
theorem admissible_iff_mismatch_box (p : TorsionParams) :
    IsAdmissibleContinuous p ↔
      ∀ a : Fin 3,
        mismatchBoostHalf (p.alpha a) (p.beta a) ^ 2 +
            mismatchRotationHalf (p.alpha a) (p.beta a) ^ 2 ≤
          (Real.pi / 2) ^ 2 := by sorry

end Goals.Diophantine