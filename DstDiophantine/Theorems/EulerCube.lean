import Mathlib.Data.Rat.Defs

/-!
# Euler's `X³ + 2Y³ = 1` as an axiom

`eulerAffineCubeAddTwo` assumes the only rational points are `(1, 0)` and `(-1, 1)`. It is an axiom,
not a Lean proof of Euler's theorem.
-/

namespace DstDiophantine

namespace Theorems

/-- Only rational points on `X³ + 2Y³ = 1` are `(1, 0)` and `(-1, 1)`. An axiom, not a Lean
proof. -/
axiom eulerAffineCubeAddTwo :
    ∀ (X Y : ℚ), X ^ 3 + 2 * Y ^ 3 = 1 →
      (X = 1 ∧ Y = 0) ∨ (X = -1 ∧ Y = 1)

end Theorems

end DstDiophantine
