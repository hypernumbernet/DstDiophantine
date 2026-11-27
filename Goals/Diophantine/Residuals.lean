import DoubleSpacetime.Theorems.BealEven
import DoubleSpacetime.Theorems.BealGaussianCube
import DoubleSpacetime.Theorems.BennettEllenbergNg
import DoubleSpacetime.Theorems.Bruin
import DoubleSpacetime.Theorems.AnniSiksek
import DoubleSpacetime.Theorems.DahmenSiksek
import DoubleSpacetime.Theorems.FermatMixed

/-!
# Diophantine residuals

Each theorem is one open `*Residual` the main library does not prove.
-/

namespace Goals.Diophantine

open DoubleSpacetime.Theorems

/-- Open face. Exponents divisible by `3` or by `4` are mathlib. -/
theorem fermatMixedMotorOddPrimeResidual : FermatMixedMotorOddPrimeResidual := by sorry

/-- Assembled from the odd-prime face. -/
theorem fermatMixedMotorResidual : FermatMixedMotorResidual :=
  FermatMixedMotorResidual_of_oddPrime fermatMixedMotorOddPrimeResidual

/-- Open. The case `e = 3` is discharged; this leaf starts at `e ≥ 5`. -/
theorem bealEqualOddTwoFactorExpGeFiveResidual :
    BealEqualOddTwoFactorExpGeFiveResidual := by sorry

/-- Open. `(22,22,7)` is `IsAnniSiksekEvenSumShape`. `(14,14,17)` is an equal even
seventeenth power. `(10,10,23)` and `(14,14,19)` remain. -/
theorem bealTwoEqualEvenSumExpGeSevenOutsideAnniSeventeenthResidual :
    BealTwoEqualEvenSumExpGeSevenOutsideAnniSeventeenthResidual := by sorry

/-- Open. Outside cube-pair and fifth-power shapes. -/
theorem bealTwoEqualEvenDiffOutsideFifthPairResidual :
    BealTwoEqualEvenDiffOutsideFifthPairResidual := by sorry

/-- Open. `(5,5,11)` is a fifth-power pair. `(5,5,23)` and `(7,7,11)` remain.
A prime hypotenuse past `10^9` with `p ≡ 2 (mod 3)` is a Freitas cube companion. -/
theorem bealTwoEqualOddOutsideFifthPairResidual :
    BealTwoEqualOddOutsideFifthPairResidual := by sorry

/-- Open. `(5,10,11)` is a fifth-power pair. `(3,5,7)` remains. -/
theorem bealAllDistinctOutsideFifthPairResidual :
    BealAllDistinctOutsideFifthPairResidual := by sorry

/-- Open. `(22,22,14)` is `IsAnniSiksekEvenSumShape`. `(10,10,14)` is a fifth-power pair. -/
theorem bealPythagoreanUnequalOddOutsideAnniSeventeenthResidual :
    BealPythagoreanUnequalOddOutsideAnniSeventeenthResidual := by sorry

end Goals.Diophantine
