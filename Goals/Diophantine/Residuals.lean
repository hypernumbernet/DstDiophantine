import DstDiophantine.Theorems.Beal
import DstDiophantine.Theorems.BealEven
import DstDiophantine.Theorems.BealGaussian
import DstDiophantine.Theorems.BealGaussianCube
import DstDiophantine.Theorems.BealMixed
import DstDiophantine.Theorems.BealPythagorean
import DstDiophantine.Theorems.Bruin
import DstDiophantine.Theorems.DahmenSiksek
import DstDiophantine.Theorems.FermatMixed

/-!
# Diophantine residuals (live leaves of the amplification programme)

Each `theorem` proves one `*Residual` proposition from the main library.
Partial closures in the main library are noted in the index (`Goals/README.md`).
-/

namespace Goals.Diophantine

open DstDiophantine.Theorems

/-! ### Fermat -/

/-- **Paper:** `papers/dst-diophantine.tex`. **Status:** open (dual-axis motor). -/
theorem fermatMixedMotorResidual : FermatMixedMotorResidual := by sorry

/-! ### Beal — mixed exponent -/

theorem bealMixedExpResidual : BealMixedExpResidual := by sorry

theorem bealPythagoreanResidual : BealPythagoreanResidual := by sorry

theorem bealTwoEqualOddResidual : BealTwoEqualOddResidual := by sorry

theorem bealAllDistinctExpResidual : BealAllDistinctExpResidual := by sorry

theorem bealPythagoreanUnequalOddResidual : BealPythagoreanUnequalOddResidual := by sorry

/-! ### Beal — even two-equal -/

theorem bealTwoEqualEvenResidual : BealTwoEqualEvenResidual := by sorry

theorem bealTwoEqualEvenSumResidual : BealTwoEqualEvenSumResidual := by sorry

theorem bealTwoEqualEvenDiffResidual : BealTwoEqualEvenDiffResidual := by sorry

theorem bealTwoEqualEvenDiffPerfectPowerResidual : BealTwoEqualEvenDiffPerfectPowerResidual := by sorry

theorem bealTwoEqualEvenDiffFactorResidual : BealTwoEqualEvenDiffFactorResidual := by sorry

theorem bealTwoEqualEvenSumOutsideCubeResidual : BealTwoEqualEvenSumOutsideCubeResidual := by sorry

theorem bealTwoEqualEvenSumExpFiveResidual : BealTwoEqualEvenSumExpFiveResidual := by sorry

theorem bealTwoEqualEvenSumExpGeSevenResidual : BealTwoEqualEvenSumExpGeSevenResidual := by sorry

theorem bealTwoEqualEvenSumExpGeSevenOutsideCubePairResidual :
    BealTwoEqualEvenSumExpGeSevenOutsideCubePairResidual := by sorry

theorem bealTwoEqualEvenDiffOutsideCubePairResidual :
    BealTwoEqualEvenDiffOutsideCubePairResidual := by sorry

/-! ### Beal — Gaussian / cube -/

theorem bealEqualOddTwoFactorResidual : BealEqualOddTwoFactorResidual := by sorry

theorem bealPosCubeAddTwoCubeResidual : BealPosCubeAddTwoCubeResidual := by sorry

theorem bealMordellCubeAddTwoResidual : BealMordellCubeAddTwoResidual := by sorry

theorem bealEqualOddTwoFactorExpGeFiveResidual : BealEqualOddTwoFactorExpGeFiveResidual := by sorry

/-! ### Beal — Bruin / Dahmen–Siksek leaves -/

theorem bealTwoEqualOddOutsideBruinResidual : BealTwoEqualOddOutsideBruinResidual := by sorry

theorem bealTwoEqualOddOutsideCubePairResidual : BealTwoEqualOddOutsideCubePairResidual := by sorry

theorem bealAllDistinctOutsideCubePairResidual : BealAllDistinctOutsideCubePairResidual := by sorry

theorem bealPythagoreanUnequalOddOutsideCubePairResidual :
    BealPythagoreanUnequalOddOutsideCubePairResidual := by sorry

theorem bealTwoEqualOddOutsideRepeatedFifthResidual :
    BealTwoEqualOddOutsideRepeatedFifthResidual := by sorry

/-! ### Beal — legacy CGA live leaf -/

/-- **Paper:** `papers/dst-diophantine.tex` (equal-exponent CGA slice).
    **Status:** open — diagnostic equal-exponent programme. -/
theorem bealCGADilationNoGo : BealCGADilationNoGo := by sorry

end Goals.Diophantine