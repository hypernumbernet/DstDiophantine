import DstDiophantine.Embedding.ConformalInteger

/-!
# 1D CGA probe (Conformal Geometric Algebra)

Diagnostic layer investigating the multiplicative / dilation sector that PGA
`G(3,1,1)` does not supply.  **Not** re-exported from `DstDiophantine.Basic`,
so the Diophantine path does not depend on these modules (same policy as
`DstDiophantine.Gravity`).

## Contents

* `Algebra.CGA.QuadraticForm` — `Cl(2,1)` quadratic form
* `Algebra.CGA.NullCone` — null pair `n₀, n∞`, conformal point `X(x)² = 0`,
  point–point pairing, scale-invariant dilation mismatch
* `Embedding.ConformalInteger` — integer null embedding, DST lattice predicate
  `IsCGAIntegerPoint`, dilation weights, PGA `integerHeight` unboundedness
-/

namespace DstDiophantine

namespace CGA

/-- Regression: null-cone points square to zero. -/
example (x : ℝ) : CGA1.point x * CGA1.point x = 0 :=
  CGA1.point_sq x

/-- Regression: conformal integers lie on the null cone. -/
example (n : ℤ) :
    Embedding.conformalInteger n * Embedding.conformalInteger n = 0 :=
  Embedding.conformalInteger_sq n

/-- Regression: PGA integer-rotor height is not globally bounded. -/
example : ¬ ∃ M : ℝ, ∀ (n : ℤ) (hn : n ≠ 0),
    Embedding.integerHeight n hn ≤ M :=
  Embedding.integerHeight_not_globally_bounded

/-- Regression: point–point polarisation. -/
example (x y : ℝ) :
    CGA1.bilin21 (CGA1.pointVec x) (CGA1.pointVec y) = -((x - y) ^ 2) / 2 :=
  CGA1.bilin21_pointVec_pointVec x y

/-- Regression: balanced dilation mismatch is positive. -/
example (m : ℕ) (hm : 0 < m) :
    0 < CGA1.cgaDilationMismatch (Real.log 2 / (m : ℝ)) :=
  CGA1.cgaDilationMismatch_balanced_pos m hm

/-- Regression: nonzero integers are CGA lattice points. -/
example {n : ℤ} (hn : n ≠ 0) : Embedding.IsCGAIntegerPoint (n : ℝ) :=
  Embedding.IsCGAIntegerPoint_conformalInteger hn

end CGA

end DstDiophantine
