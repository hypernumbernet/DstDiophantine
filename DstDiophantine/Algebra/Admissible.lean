import DstDiophantine.Algebra.Operations
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Admissible torsional configurations

Parameter dictionary (DST papers ↔ Lean):
* Main paper: usual rapidities `φ_a`, dual angles `θ_a`
* Discrete companion: `ω_a`, `φ_a`
* Lean: `TorsionParams.alpha` / `TorsionParams.beta`

## Predicates

* `IsPrincipalBranch`: `|α_a + β_a| ≤ π/2` (neighbourhood of `Ω ≈ 1`).
  Alone this does not bound `J` (`Invariant.torsion_bound_naive_false`).
* `IsAdmissibleContinuous`: non-negative rapidities with `α_a + β_a ≤ π/2`
  on each axis. On this cone `|J| ≤ 3π²/8` and `|JNormalized| ≤ 1`
  (`Invariant`).

Anti-synchronisation in the main paper is the rotor condition
`R_dual = R_usual†`, which is not this cone inequality. The discrete
companion uses the same phrase for `α_a + β_a ≤ π/2`.
-/

namespace DstDiophantine

open Operations Real

namespace Admissible

/-- Principal branch: `|α_a + β_a| ≤ π/2` on each axis. -/
def IsPrincipalBranch (p : TorsionParams) : Prop :=
  ∀ a : Fin 3, |p.alpha a + p.beta a| ≤ Real.pi / 2

/-- Admissible cone: non-negative rapidities with `α_a + β_a ≤ π/2` on each axis. -/
def IsAdmissibleContinuous (p : TorsionParams) : Prop :=
  ∀ a : Fin 3, 0 ≤ p.alpha a ∧ 0 ≤ p.beta a ∧ p.alpha a + p.beta a ≤ Real.pi / 2

theorem admissibleContinuous_implies_principalBranch (p : TorsionParams)
    (h : IsAdmissibleContinuous p) : IsPrincipalBranch p := by
  intro a
  have hα := (h a).1
  have hβ := (h a).2.1
  have hsum := (h a).2.2
  rw [abs_of_nonneg (add_nonneg hα hβ)]
  exact hsum

theorem admissibleContinuous_alpha_nonneg (p : TorsionParams)
    (h : IsAdmissibleContinuous p) (a : Fin 3) : 0 ≤ p.alpha a :=
  (h a).1

theorem admissibleContinuous_beta_nonneg (p : TorsionParams)
    (h : IsAdmissibleContinuous p) (a : Fin 3) : 0 ≤ p.beta a :=
  (h a).2.1

theorem admissibleContinuous_sum_le (p : TorsionParams)
    (h : IsAdmissibleContinuous p) (a : Fin 3) :
    p.alpha a + p.beta a ≤ Real.pi / 2 :=
  (h a).2.2

theorem admissibleContinuous_alpha_le_half_pi (p : TorsionParams)
    (h : IsAdmissibleContinuous p) (a : Fin 3) :
    p.alpha a ≤ Real.pi / 2 := by
  linarith [admissibleContinuous_beta_nonneg p h a, admissibleContinuous_sum_le p h a]

theorem admissibleContinuous_beta_le_half_pi (p : TorsionParams)
    (h : IsAdmissibleContinuous p) (a : Fin 3) :
    p.beta a ≤ Real.pi / 2 := by
  linarith [admissibleContinuous_alpha_nonneg p h a, admissibleContinuous_sum_le p h a]

end Admissible

end DstDiophantine
