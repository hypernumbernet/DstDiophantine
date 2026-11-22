import DstDiophantine.Gravity.NuclearLayer
import DstDiophantine.Gravity.Perihelion
import DstDiophantine.Gravity.SignReversal

/-!
# Physics frontiers

Each target calls a function from the main library. Orbital elements are external rationals.
-/

namespace Goals.Gravity

open DstDiophantine.Gravity DstDiophantine.Gravity.Perihelion Real

/-! ### Mercury -/

/-- External semi-major axis of Mercury, in metres. -/
def mercurySemiMajor : ℚ := 57909050000

/-- External eccentricity of Mercury. -/
def mercuryEccentricity : ℚ := 205630 / 1000000

/-- External sidereal period of Mercury, in days. -/
def mercuryPeriodDays : ℚ := 879691 / 10000

/-- Days in a Julian century. -/
def julianCenturyDays : ℚ := 36525

/-- Orbits of Mercury in one Julian century. -/
def mercuryRevsPerCentury : ℚ := julianCenturyDays / mercuryPeriodDays

/-- Solar geometric mass `GM/c²`, in metres, from the SI stand-ins. -/
def solarGeometricMass : ℚ :=
  SI.GApprox * SI.solarMassApprox / SI.speedOfLight ^ 2

/-- Reciprocal aphelion radius. Smaller turning value of the radial return. -/
noncomputable def mercuryAlpha : ℝ :=
  1 / ((mercurySemiMajor : ℝ) * (1 + (mercuryEccentricity : ℝ)))

/-- Reciprocal perihelion radius. Larger turning value of the radial return. -/
noncomputable def mercuryBeta : ℝ :=
  1 / ((mercurySemiMajor : ℝ) * (1 - (mercuryEccentricity : ℝ)))

/-- Advance from `radialReturn`, in arcseconds per Julian century. -/
noncomputable def mercuryArcsecPerCentury : ℝ :=
  (radialReturn (solarGeometricMass : ℝ) mercuryAlpha mercuryBeta - 2 * Real.pi) *
    (mercuryRevsPerCentury : ℝ) * (648000 / Real.pi)

/-- Open. Exterior radial return of Mercury, in arcseconds per Julian century. -/
theorem mercuryPerihelionArcsecPerCentury :
    42 < mercuryArcsecPerCentury ∧
      mercuryArcsecPerCentury < 44 := by sorry

/-! ### Charged pion -/

/-- Open. The charged-pion Compton length selects one sign-reversal scale in `(1/2, 1)`. -/
theorem chargedPionSelectsReversalScale :
    ∃! r₁ : ℝ, 1 / 2 < r₁ ∧ r₁ < 1 ∧
      lengthOfReversal r₁ = (pionComptonFm : ℝ) := by sorry

end Goals.Gravity
