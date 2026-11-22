import DstDiophantine.Gravity.NuclearLayer
import DstDiophantine.Gravity.SignReversal

/-!
# Physics frontiers

Each target calls a function from the main library. The Mercury perihelion arcsecond bound is a
theorem of `DstDiophantine.Gravity.Mercury` and is no longer a Goal.
-/

namespace Goals.Gravity

open DstDiophantine.Gravity

/-! ### Charged pion -/

/-- Open. The charged-pion Compton length selects one sign-reversal scale in `(1/2, 1)`. -/
theorem chargedPionSelectsReversalScale :
    ∃! r₁ : ℝ, 1 / 2 < r₁ ∧ r₁ < 1 ∧
      lengthOfReversal r₁ = (pionComptonFm : ℝ) := by sorry

end Goals.Gravity
