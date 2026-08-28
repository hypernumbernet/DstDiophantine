import DstDiophantine.Algebra.Invariant
import Mathlib.Tactic.Positivity

/-!
# Level-matching dictionary (usual–dual ↔ string L₀ = L̄₀)

String level matching `L₀ = L̄₀` is **not** identified with a DST equation.
The dictionary records the Killing-neutral slice `J = 0` as the algebraic
stand-in for “usual / dual mismatch vanishes”, and proves that balanced
rays sit on that slice.
-/

namespace DstDiophantine

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

/-- Balanced equal usual–dual rapidity is level-matched. -/
theorem isLevelMatched_balancedRay (t : ℝ) :
    IsLevelMatched (balancedRay t) :=
  (isLevelMatched_iff_JNormalized _).mpr (JNormalized_balancedRay t)

end Logic

end DstDiophantine
