import DstDiophantine.Algebra.Discrete
import DstDiophantine.Algebra.Motor

/-!
# Finite unit group of the discrete torsion sector

On the compact torus `(ℤ/Nℤ)⁶` only finitely many torsion rotors arise. Phase 3 will relate
this image to the integer biquaternion unit group; here we expose the finite rotor image.
-/

namespace DstDiophantine

open Discrete Motor

namespace UnitGroup

variable {N : ℕ} [NeZero N]

/-- Rotor associated with a discrete torus point. -/
noncomputable def discreteRotor (t : DiscreteTorsion N) : PGA :=
  rotorTorsion (toTorsionParams t)

/-- Image of all discrete rotors on `(ℤ/Nℤ)⁶`. -/
def DiscreteUnit (N : ℕ) [NeZero N] : Set PGA :=
  Set.range (discreteRotor (N := N))

theorem mem_discreteUnit_iff {x : PGA} :
    x ∈ DiscreteUnit N ↔ ∃ t : DiscreteTorsion N, discreteRotor t = x :=
  Set.mem_range

theorem discreteUnit_finite : (DiscreteUnit N).Finite :=
  Set.finite_range _

noncomputable instance : Fintype {x // x ∈ DiscreteUnit N} :=
  discreteUnit_finite.fintype

end UnitGroup

end DstDiophantine
