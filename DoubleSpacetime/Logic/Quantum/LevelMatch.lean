import DoubleSpacetime.Algebra.Invariant
import Mathlib.Tactic.Positivity

/-!
# Level-matching dictionary

String level matching `L₀ = L̄₀` is not identified with a DST equation. The dictionary records the
slice `J = 0`, and balanced rays sit on it.
-/

namespace DoubleSpacetime

namespace Logic

open Operations Invariant

/-- Algebraic stand-in for level matching: torsional Killing form vanishes. -/
def IsLevelMatched (p : TorsionParams) : Prop :=
  J p = 0

theorem isLevelMatched_iff_JNormalized (p : TorsionParams) :
    IsLevelMatched p ↔ JNormalized p = 0 := by
  unfold IsLevelMatched JNormalized
  constructor
  · intro h; simp [h]
  · intro h
    have hcoef : (8 / (3 * Real.pi ^ 2) : ℝ) ≠ 0 := by positivity
    exact (mul_eq_zero.mp h).resolve_left hcoef

theorem isLevelMatched_balancedRay (t : ℝ) :
    IsLevelMatched (balancedRay t) :=
  (isLevelMatched_iff_JNormalized _).mpr (JNormalized_balancedRay t)

end Logic

end DoubleSpacetime
