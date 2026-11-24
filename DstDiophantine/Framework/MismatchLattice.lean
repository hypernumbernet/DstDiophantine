import DstDiophantine.Framework.Lattice
import DstDiophantine.Algebra.MismatchAngle
import DstDiophantine.Algebra.ModularAmplification
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.BigOperators.Fin

set_option linter.style.whitespace false

/-!
# Discrete `latticeMismatch` as mismatch half-square sums

On `toTorsionParams t`, the legacy scalar `J` is the diagnostic difference of global
`mismatchBoostHalf` / `mismatchRotationHalf` square sums. The integer `latticeMismatch t`
is exactly that difference at scale `(2π/N)²`.

On a pure-boost seed, rotation half-squares vanish and winding lives on the boost leg
(`ModularAmplification.windingTotal_pureBoost`), not on `mismatchRotationHalf`.
-/

namespace DstDiophantine

namespace Framework

open Discrete Invariant Operations Real MismatchAngle ModularAmplification

variable {N : ℕ} [NeZero N]

theorem mismatch_half_sq_diff (t : DiscreteTorsion N) :
    mismatchBoostHalfSqSum (toTorsionParams t) -
        mismatchRotationHalfSqSum (toTorsionParams t) =
      (1 / 4) * (2 * Real.pi / N) ^ 2 * (latticeMismatch t : ℝ) := by
  have hJ := J_eq_mismatch_half_sq_diff (toTorsionParams t)
  have hlat := J_toTorsionParams t
  linarith

theorem J_toTorsionParams_via_mismatch_halves (t : DiscreteTorsion N) :
    J (toTorsionParams t) =
      2 *
        (mismatchBoostHalfSqSum (toTorsionParams t) -
          mismatchRotationHalfSqSum (toTorsionParams t)) :=
  J_eq_mismatch_half_sq_diff (toTorsionParams t)

theorem pure_boost_rotation_sq_zero (t : DiscreteTorsion N) (hp : IsPureBoostSeed t) :
    mismatchRotationHalfSqSum (toTorsionParams t) = 0 := by
  simp only [mismatchRotationHalfSqSum, mismatchRotationHalf, toTorsionParams_beta]
  refine Finset.sum_eq_zero fun a _ => ?_
  simp [hp.2 a]

theorem pure_boost_mismatch_boost_eq_lattice (t : DiscreteTorsion N) (hp : IsPureBoostSeed t) :
    mismatchBoostHalfSqSum (toTorsionParams t) =
      (Real.pi / N) ^ 2 * (latticeMismatch t : ℝ) := by
  calc mismatchBoostHalfSqSum (toTorsionParams t)
      = (1 / 4) * (2 * Real.pi / N) ^ 2 * (latticeMismatch t : ℝ) := by
        rw [← mismatch_half_sq_diff t, pure_boost_rotation_sq_zero t hp, sub_zero]
      _ = (Real.pi / N) ^ 2 * (latticeMismatch t : ℝ) := by ring_nf

theorem winding_implies_latticeMismatch_ne (k : ℕ) (t : DiscreteTorsion N)
    (hp : IsPureBoostSeed t) (hw : windingTotal k t ≠ 0) :
    latticeMismatch t ≠ 0 :=
  latticeMismatch_ne_zero_of_winding_pureBoost k t hp hw

theorem windingTotal_pureBoost_eq_windingCoord (k : ℕ) (t : DiscreteTorsion N)
    (hp : IsPureBoostSeed t) :
    windingTotal k t = windingCoord k (t.n 0) :=
  windingTotal_pureBoost k t hp

end Framework

end DstDiophantine