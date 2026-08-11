import DstDiophantine.Framework.Lattice
import DstDiophantine.Framework.Descent
import DstDiophantine.Framework.Representation
import Mathlib.Data.Fintype.Basic

/-!
# Finite search and decidability on the admissible lattice

`ExistsZeroHeight N` is a finite existential over a decidable predicate, hence
decidable. The search function `findZeroHeight` returns a witness when one
exists (and always does: the origin is admissible of zero height).
-/

namespace DstDiophantine

namespace Framework

open Discrete

variable {N : ℕ} [NeZero N]

private instance : DecidableEq (DiscreteTorsion N) :=
  Equiv.decidableEq discreteEquiv

private instance : DecidableEq (AdmissibleClass N) :=
  Subtype.instDecidableEq

instance : DecidablePred (AdmissibleClass.IsZero (N := N)) := fun t =>
  decidable_of_iff _ (AdmissibleClass.isZero_iff_latticeMismatch t).symm

/-- Exhaustive search for an admissible zero-height lattice point. -/
noncomputable def findZeroHeight (N : ℕ) [NeZero N] : Option (AdmissibleClass N) :=
  open Classical in
  if h : ExistsZeroHeight N then some (Classical.choose h) else none

theorem findZeroHeight_isSome_iff :
    (findZeroHeight N).isSome ↔ ExistsZeroHeight N := by
  constructor
  · intro h
    rw [findZeroHeight] at h
    split_ifs at h with hex
    · exact hex
    · cases h
  · intro hex
    simp [findZeroHeight, hex]

theorem findZeroHeight_eq_none_iff :
    findZeroHeight N = none ↔ ¬ ExistsZeroHeight N := by
  rw [← findZeroHeight_isSome_iff, Option.not_isSome_iff_eq_none]

theorem findZeroHeight_sound {t : AdmissibleClass N}
    (h : findZeroHeight N = some t) : AdmissibleClass.IsZero t := by
  rw [findZeroHeight] at h
  split_ifs at h with hex
  · cases h
    exact Classical.choose_spec hex

theorem findZeroHeight_isSome (N : ℕ) [NeZero N] : (findZeroHeight N).isSome :=
  findZeroHeight_isSome_iff.mpr (existsZeroHeight_of_neZero N)

/-- Decidability via the integer mismatch characterisation of zero height. -/
noncomputable instance : Decidable (ExistsZeroHeight N) := by
  classical
  exact inferInstance

theorem latticeSearch_terminates (N : ℕ) [NeZero N] :
    ∃ s' : LatticeSearchState N, LatticeSearchState.terminal s' :=
  latticeSearch_reaches_terminal N

/--
Three-layer Phase-4 interface (not a single biconditional):
1. Integer power-sum equations ↔ null motors.
2. Admissible lattice zero-height search always finds a witness.
3. Amplification / contradiction schemas are supplied by Phase 5.
-/
theorem phase4_layers (e : PowerSumEquation) (N : ℕ) [NeZero N] :
    (powerSumMotor e = 1 ↔ evalPowerSum e = 0) ∧
      (findZeroHeight N).isSome ∧
      ∃ s' : LatticeSearchState N, LatticeSearchState.terminal s' :=
  ⟨powerSumMotor_one_iff e, findZeroHeight_isSome N, latticeSearch_terminates N⟩

end Framework

end DstDiophantine
