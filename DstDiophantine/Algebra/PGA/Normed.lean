import DstDiophantine.Algebra.QuadraticForm
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Normed algebra structure on `PGA`

Finite-dimensional `Cl(3,1,1)` inherits a `NormedAlgebra` from left-multiplication matrices.
This enables `NormedSpace.exp` for torsion rotors.

## Deferred instances (`sorry`)

- `Module.Finite` / `CharZero` on `Cl(3,1,1)` (expected dimension `2⁵`)
- `NormedAlgebra ℚ` (needed for full `exp_add_of_commute` infrastructure)
-/

set_option warn.sorry false

namespace DstDiophantine

namespace PGANormed

open scoped BigOperators Matrix

abbrev Alg311 := CliffordAlgebra Q311

instance : Module.Finite ℝ Alg311 := by sorry

instance : CharZero Alg311 := by sorry

noncomputable abbrev BasisIndex := Fin (Module.finrank ℝ Alg311)

noncomputable def vectorBasis : Module.Basis BasisIndex ℝ Alg311 :=
  Module.finBasis ℝ Alg311

noncomputable local instance matrixNormedRing : NormedRing (Matrix BasisIndex BasisIndex ℝ) :=
  Matrix.linftyOpNormedRing

noncomputable local instance matrixNormedAlgebra :
    NormedAlgebra ℝ (Matrix BasisIndex BasisIndex ℝ) :=
  Matrix.linftyOpNormedAlgebra

noncomputable instance : NormedRing Alg311 :=
  NormedRing.induced Alg311 (Matrix BasisIndex BasisIndex ℝ)
    (Algebra.leftMulMatrix vectorBasis) (Algebra.leftMulMatrix_injective vectorBasis)

noncomputable instance : NormedAlgebra ℝ Alg311 :=
  NormedAlgebra.induced ℝ Alg311 (Matrix BasisIndex BasisIndex ℝ)
    (Algebra.leftMulMatrix vectorBasis)

instance : CompleteSpace Alg311 :=
  FiniteDimensional.complete ℝ Alg311

noncomputable instance instNormedAlgebraRat : NormedAlgebra ℚ Alg311 := by sorry

end PGANormed

end DstDiophantine
