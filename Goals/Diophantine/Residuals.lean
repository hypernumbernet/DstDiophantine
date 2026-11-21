import DstDiophantine.Theorems.BealEven
import DstDiophantine.Theorems.BealGaussianCube
import DstDiophantine.Theorems.Bruin
import DstDiophantine.Theorems.DahmenSiksek
import DstDiophantine.Theorems.FermatMixed

/-!
# Diophantine residuals (live leaves)

Each `theorem` is one `*Residual` the main library does not prove and does
not derive from a narrower residual. Coarser residuals are assembled in
`Goals.Diophantine.Headlines` from these leaves. The index of discharged
props is `Goals/README.md`.
-/

namespace Goals.Diophantine

open DstDiophantine.Theorems

/-- **Claim (EN):** A mixed dual-axis Fermat motor is incompatible with a
    positive power sum of degree `n ≥ 3`.

    **Claim (JA):** 混合した双軸フェルマー・モーターは、次数 `n ≥ 3` の正の
    べき和と両立しない。

    **Paper:** `papers/dst-diophantine.tex`.

    **Status:** open. `FermatLastTheorem_of_mixed_motor_residual` turns this
    into classical FLT.
-/
theorem fermatMixedMotorResidual : FermatMixedMotorResidual := by sorry

/-- **Claim (EN):** No equal-odd two-factor Gaussian solution for an odd
    exponent `e ≥ 5` whose pure-power absolute value is greater than 1.

    **Claim (JA):** 奇数指数 `e ≥ 5` で、純べきの絶対値が 1 より大きい等奇数
    二因子のガウス解はない。

    **Paper:** `papers/dst-diophantine.tex`.

    **Status:** open. The case `e = 3` is `BealPosCubeAddTwoCubeResidual_of_euler`.
    `BealEqualOddTwoFactorResidual_of_ge_five` lifts this leaf.
-/
theorem bealEqualOddTwoFactorExpGeFiveResidual :
    BealEqualOddTwoFactorExpGeFiveResidual := by sorry

/-- **Claim (EN):** No coprime even two-equal sum `A^x + B^x = C^z` with
    `z ≥ 7` outside a cube-pair shape.

    **Claim (JA):** 立方対の形を除き、`z ≥ 7` の互いに素な偶数二等和
    `A^x + B^x = C^z` はない。

    **Paper:** `papers/dst-diophantine.tex`.

    **Status:** open. `z = 5` is `BealTwoEqualEvenSumExpFiveResidual_of_NN5`.
    `(6,6,7)` is a cube-pair shape. `(4,4,7)` remains here.
-/
theorem bealTwoEqualEvenSumExpGeSevenOutsideCubePairResidual :
    BealTwoEqualEvenSumExpGeSevenOutsideCubePairResidual := by sorry

/-- **Claim (EN):** No coprime even-difference two-equal solution outside a
    cube-pair shape.

    **Claim (JA):** 立方対の形を除き、互いに素な偶数差の二等解はない。

    **Paper:** `papers/dst-diophantine.tex`.

    **Status:** open. `(5,6,6)` is removed with the two-cube prohibition.
-/
theorem bealTwoEqualEvenDiffOutsideCubePairResidual :
    BealTwoEqualEvenDiffOutsideCubePairResidual := by sorry

/-- **Claim (EN):** No coprime odd two-equal solution outside cube-pair shapes
    and outside a repeated five beside `7` or `19`.

    **Claim (JA):** 立方対の形と、`7` または `19` の隣に並ぶ反復五を除き、
    互いに素な奇数二等解はない。

    **Paper:** `papers/dst-diophantine.tex`.

    **Status:** open.
-/
theorem bealTwoEqualOddOutsideRepeatedFifthResidual :
    BealTwoEqualOddOutsideRepeatedFifthResidual := by sorry

/-- **Claim (EN):** No coprime solution with pairwise distinct exponents outside
    a cube-pair shape.

    **Claim (JA):** 立方対の形を除き、指数が互いに異なる互いに素な解はない。

    **Paper:** `papers/dst-diophantine.tex`.

    **Status:** open. Signature `(3,4,5)` is already closed in every order.
-/
theorem bealAllDistinctOutsideCubePairResidual :
    BealAllDistinctOutsideCubePairResidual := by sorry

/-- **Claim (EN):** No coprime solution of exponent gcd `2`, with at least two
    reduced exponents odd, outside the equal-odd Gaussian slices and outside
    a cube-pair shape.

    **Claim (JA):** 等奇数のガウス切片と立方対の形を除き、指数の gcd が `2` で
    既約指数の少なくとも二つが奇数である互いに素な解はない。

    **Paper:** `papers/dst-diophantine.tex`.

    **Status:** open.
-/
theorem bealPythagoreanUnequalOddOutsideCubePairResidual :
    BealPythagoreanUnequalOddOutsideCubePairResidual := by sorry

end Goals.Diophantine
