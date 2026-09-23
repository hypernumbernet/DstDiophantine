import Mathlib.Data.Rat.Defs

/-!
# Euler's determination of \(X^3 + 2Y^3 = 1\) as an axiom

mathlib (v4.34) does not contain Euler's theorem on the rational points of
`X³ + 2Y³ = 1` (equivalently `x³ − 2y³ = 1`). We take the classical statement
as an `axiom` (same contract as `fermatLastTheorem` / `mihailescu`) and close
the Beal positive-cube residual from it.

The only rational solutions are `(1, 0)` and `(-1, 1)`. The signed relation
`(-1)³ + 2·1³ = 1³` is the second of those points; it does not yield a positive
triple `α³ + 2β³ = γ³`.
-/

namespace DstDiophantine

namespace Theorems

/--
Euler: the only rational points on `X³ + 2Y³ = 1` are `(1, 0)` and `(-1, 1)`.

Equivalent (via `Y ↦ -Y`) to the rational points of `x³ − 2y³ = 1`. Not in
mathlib at this pin; recorded as an axiom rather than a `sorry`. This is
**not** a Lean proof of Euler's theorem.
-/
axiom eulerAffineCubeAddTwo :
    ∀ (X Y : ℚ), X ^ 3 + 2 * Y ^ 3 = 1 →
      (X = 1 ∧ Y = 0) ∨ (X = -1 ∧ Y = 1)

end Theorems

end DstDiophantine
