import DstDiophantine.Algebra.MismatchAngle

set_option linter.style.whitespace false

/-!
# General mismatch angle (principal branch)

On non-commuting two-sector configurations there is no global additive
logarithm of `Ω = R_usual† R_dual`. A principal-branch mismatch bivector is
currently under research.
-/

namespace Goals.Diophantine

open DstDiophantine
open Operations RelativeRotor MismatchAngle PGA Generators NormedSpace

/-- Principal-branch mismatch bivector for general parameters (open). -/
theorem omegaMismatch_principal_branch (p : TorsionParams) :
    ∃ ω : PGA, relativeRotor p = NormedSpace.exp ω ∧
      (∀ a : Fin 3, p.alpha a ≠ 0 → p.beta a ≠ 0 → False) := by sorry

end Goals.Diophantine