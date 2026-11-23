import DstDiophantine.Theorems.BealEven
import DstDiophantine.Theorems.BealGaussianCube
import DstDiophantine.Theorems.BennettEllenbergNg
import DstDiophantine.Theorems.Bruin
import DstDiophantine.Theorems.DahmenSiksek
import DstDiophantine.Theorems.FermatMixed

/-!
# Diophantine residuals

Each theorem is one open `*Residual` the main library does not prove.
-/

namespace Goals.Diophantine

open DstDiophantine.Theorems

/-- Open. `FermatLastTheorem_of_mixed_motor_residual` turns this into classical FLT. -/
theorem fermatMixedMotorResidual : FermatMixedMotorResidual := by sorry

/-- Open. The case `e = 3` is discharged; this leaf starts at `e ≥ 5`. -/
theorem bealEqualOddTwoFactorExpGeFiveResidual :
    BealEqualOddTwoFactorExpGeFiveResidual := by sorry

/-- Open. `(10,10,9)` is `IsSharedExpCubeOrFifth`. `(22,22,7)` remains. -/
theorem bealTwoEqualEvenSumExpGeSevenOutsideFourthFifthResidual :
    BealTwoEqualEvenSumExpGeSevenOutsideFourthFifthResidual := by sorry

/-- Open. Outside cube-pair and fifth-power shapes. -/
theorem bealTwoEqualEvenDiffOutsideFifthPairResidual :
    BealTwoEqualEvenDiffOutsideFifthPairResidual := by sorry

/-- Open. `(5,5,11)` remains after the shared-exponent cut. -/
theorem bealTwoEqualOddOutsideFifthPairResidual :
    BealTwoEqualOddOutsideFifthPairResidual := by sorry

/-- Open. `(3,5,7)` remains after the shared-exponent cut. -/
theorem bealAllDistinctOutsideFifthPairResidual :
    BealAllDistinctOutsideFifthPairResidual := by sorry

/-- Open. Outside the equal-odd Gaussian slices and the named shapes. -/
theorem bealPythagoreanUnequalOddOutsideFifthPairResidual :
    BealPythagoreanUnequalOddOutsideFifthPairResidual := by sorry

end Goals.Diophantine
