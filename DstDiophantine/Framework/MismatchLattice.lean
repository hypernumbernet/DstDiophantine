import DstDiophantine.Framework.Lattice
import DstDiophantine.Algebra.MismatchAngle
import DstDiophantine.Algebra.ModularAmplification
import DstDiophantine.Algebra.Discrete
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

open Discrete Invariant Operations Real MismatchAngle ModularAmplification Amplification

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

/-- Winding on dual (`m`) coordinates: periodic rotation leg of the lattice. -/
def windingRotationTotal (k : ℕ) (t : DiscreteTorsion N) : ℕ :=
  ∑ a : Fin 3, windingCoord k (t.m a)

theorem windingRotationTotal_pureBoost_zero (k : ℕ) (t : DiscreteTorsion N)
    (hp : IsPureBoostSeed t) :
    windingRotationTotal k t = 0 := by
  unfold windingRotationTotal
  refine Finset.sum_eq_zero fun a _ => ?_
  simpa [windingCoord, hp.2 a] using Nat.div_eq_zero_of_lt (ZMod.val_lt (t.m a))

theorem winding_pureBoost_decomposition (k : ℕ) (t : DiscreteTorsion N)
    (hp : IsPureBoostSeed t) :
    windingTotal k t = windingCoord k (t.n 0) ∧
      windingRotationTotal k t = 0 ∧
        mismatchRotationHalfSqSum (toTorsionParams t) = 0 := by
  refine ⟨windingTotal_pureBoost k t hp, windingRotationTotal_pureBoost_zero k t hp,
    pure_boost_rotation_sq_zero t hp⟩

private theorem windingRotationTotal_eq_sum_three (k : ℕ) (t : DiscreteTorsion N) :
    windingRotationTotal k t =
      windingCoord k (t.m 0) + windingCoord k (t.m 1) + windingCoord k (t.m 2) := by
  unfold windingRotationTotal
  simp [Fin.sum_univ_three]

private theorem coord_le_windingRotationTotal (k : ℕ) (t : DiscreteTorsion N) (a : Fin 3) :
    windingCoord k (t.m a) ≤ windingRotationTotal k t := by
  unfold windingRotationTotal
  simpa using Finset.single_le_sum (f := fun i => windingCoord k (t.m i))
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)

theorem windingRotationTotal_pos_of_coord_pos (k : ℕ) (t : DiscreteTorsion N) (a : Fin 3)
    (h : 0 < windingCoord k (t.m a)) : 0 < windingRotationTotal k t :=
  Nat.lt_of_lt_of_le h (coord_le_windingRotationTotal k t a)

theorem mismatch_rotation_winding_at_scale (k : ℕ) (t : DiscreteTorsion N) (a : Fin 3) :
    (scaleTorsion (k : ℝ) (toTorsionParams t)).beta a =
      (amplifiedParams k t).beta a + 2 * Real.pi * windingCoord k (t.m a) :=
  scale_beta_eq_amplified_plus_winding k t a

end Framework

end DstDiophantine