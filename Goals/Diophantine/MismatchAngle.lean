import DstDiophantine.Algebra.MismatchAngle
import DstDiophantine.Algebra.RelativeRotor

set_option linter.style.whitespace false

/-!
# Off-axis mismatch log (open)

One-axis overlap and `Ω = exp(ω)` are closed in main (`MismatchAngle`, `PgaAxisMotor`).
Lattice winding on the rotation leg is in `Framework/MismatchLattice` (`windingRotationTotal`).
-/

namespace Goals.Diophantine

open DstDiophantine
open Operations RelativeRotor MismatchAngle PGA Generators NormedSpace

/-- Open: principal-branch mismatch bivector when hyperbolic and cyclic generators do not commute. -/
theorem omegaMismatch_off_axis_principal_branch (p : TorsionParams) :
    ∃ ω : PGA, relativeRotor p = NormedSpace.exp ω := by sorry

end Goals.Diophantine