import DstDiophantine.Algebra.MismatchAngle
import DstDiophantine.Algebra.RelativeRotor

set_option linter.style.whitespace false

/-!
# Grade-zero overlap from `Ω` inside PGA

The chart scalar `axisOverlapScalar` matches `gammaS` on one axis. The remaining
step is to identify it with the grade-zero coefficient of `relativeRotor` without
re-importing the closed formula.
-/

namespace Goals.Diophantine

open DstDiophantine
open RelativeRotor MismatchAngle PGA Generators Operations

/-- Grade-zero scalar coefficient of a PGA multivector (definition deferred to Clifford projection). -/
opaque pgaGradeZeroScalar : PGA → ℝ

/-- Grade-zero coefficient of `relativeRotor (axisParams α β)` agrees with `axisOverlapScalar`.

On the commuting `{B⁺₀, B⁻₀}` subalgebra this is the scalar overlap used for shell charts.
-/
theorem relativeRotor_axis_gradeZero_eq_overlap (α β : ℝ) :
    pgaGradeZeroScalar (relativeRotor (axisParams α β)) = axisOverlapScalar α β := by sorry

end Goals.Diophantine