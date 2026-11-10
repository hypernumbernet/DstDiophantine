import DstDiophantine.Gravity.Sandwich
import DstDiophantine.Gravity.Schwarzschild
import DstDiophantine.Gravity.Weitzenbock
import DstDiophantine.Gravity.KillingAxis
import DstDiophantine.Algebra.Sandwich
import DstDiophantine.Algebra.Motor
import DstDiophantine.Algebra.Generators
import DstDiophantine.Algebra.LorentzLie
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum

/-!
# Motor-induced reference vectors (chart tetrad bridge)

## Proved

* Motor sandwich of the Cl(3,1) frame vectors `ι a` (`a : Fin 4`).
* Pure radial boost recovers the hyperbolic `(t,r)` mixing
  `cosh φ · ι0 + sinh φ · ι1`.
* Pure translator `T = 1 + Ω_trans` is nontrivial when `λ ≠ 0`, and does
  **not** by itself reproduce the classical Schwarzschild diagonal gauge.
* For every `λ`, constant or not, `T e_μ T̃ = e_μ + (η_μμ λ^μ) e₄`. The
  Minkowski leg is the inertial frame, so the induced metric is Minkowski and
  the Weitzenböck torsion of that leg vanishes. The jet of `λ` is carried by
  the coefficient of `e₄`.
* A motor `M = R T` has the same Minkowski leg as `R`. The translation does
  not enter the spacetime torsion. This is the chart reading of the proved
  one-parameter rotors; a rotor about a moving axis is not given a
  teleparallel scalar here.

Light-cone eigenvalues and `(t,r)` coframe scales live in `Gravity.Sandwich` /
`Gravity.Schwarzschild` (`sandwich_radialBoost_eigenvalues_eq_schwarzschild`,
`schwarzschildDiag_eq_boostScales`).

## Not claimed

* General grade-1 projection for arbitrary multivectors in `G(3,1,1)`.
* Degenerate-metric isometry of the full sandwich.
* Angular legs `r`, `r sin θ` from a pure radial boost (spherical reference
  coframe, not `R(φ)`).
-/

namespace DstDiophantine

namespace Gravity

open PGA Generators Motor Real CliffordAlgebra NormedSpace
open Sandwich (sandwich)

/-- Minkowski frame vector `ι a` inside `G(3,1,1)` (`a : Fin 4`). -/
noncomputable def frameVec (a : Fin 4) : PGA :=
  ι (Fin.castAdd 1 a)

/-- Motor-induced reference vector `M ê^a M̃` (no grade projection).
For pure Lorentz rotors on `{ι 0..3}` the result stays in the Minkowski
grade-1 span (proved below for radial boosts). -/
noncomputable def motorInducedVector (m : PGA) (a : Fin 4) : PGA :=
  sandwich m (frameVec a)

@[simp] theorem motorInducedVector_one (a : Fin 4) :
    motorInducedVector 1 a = frameVec a := by
  simp [motorInducedVector, frameVec, sandwich]

theorem motorInduced_radialBoost_ι0 (rs r : ℝ) :
    motorInducedVector (rotorTorsion (radialBoostParams rs r)) 0 =
      Real.cosh (schwarzschildRapidity rs r) • frameVec 0 +
        Real.sinh (schwarzschildRapidity rs r) • frameVec 1 := by
  simpa [motorInducedVector, frameVec, radialBoostParams, Fin.castAdd] using
    Sandwich.sandwich_pureBoost_ι0 (schwarzschildRapidity rs r)

theorem motorInduced_radialBoost_ι1 (rs r : ℝ) :
    motorInducedVector (rotorTorsion (radialBoostParams rs r)) 1 =
      Real.sinh (schwarzschildRapidity rs r) • frameVec 0 +
        Real.cosh (schwarzschildRapidity rs r) • frameVec 1 := by
  simpa [motorInducedVector, frameVec, radialBoostParams, Fin.castAdd] using
    Sandwich.sandwich_pureBoost_ι1 (schwarzschildRapidity rs r)

theorem motorInduced_radialBoost_ι2 (rs r : ℝ) :
    motorInducedVector (rotorTorsion (radialBoostParams rs r)) 2 = frameVec 2 := by
  simpa [motorInducedVector, frameVec, radialBoostParams, Fin.castAdd] using
    Sandwich.sandwich_pureBoost_ι2 (schwarzschildRapidity rs r)

theorem motorInduced_radialBoost_ι3 (rs r : ℝ) :
    motorInducedVector (rotorTorsion (radialBoostParams rs r)) 3 = frameVec 3 := by
  simpa [motorInducedVector, frameVec, radialBoostParams, Fin.castAdd] using
    Sandwich.sandwich_pureBoost_ι3 (schwarzschildRapidity rs r)

/-! ### Translators do not supply the Schwarzschild diagonal gauge -/

theorem expTrans_eq_one_iff (p : TransParams) :
    expTrans p = 1 ↔ omegaTrans p = 0 := by
  constructor
  · intro h
    have : (1 : PGA) + omegaTrans p = 1 := by simpa [expTrans] using h
    exact add_left_cancel (a := (1 : PGA)) (by simpa using this)
  · intro h
    simp [expTrans, h]

theorem omegaTrans_spatial_one :
    omegaTrans ⟨fun μ => if μ = 1 then (1 : ℝ) else 0⟩ =
      (1 / 2 : ℝ) • null 1 := by
  simp [omegaTrans, Fin.sum_univ_four, null]

/-- Pure spatial translator is not the identity; hence it cannot by itself
reproduce the classical diagonal Schwarzschild coframe. -/
theorem pure_translator_ne_identity_of_spatial :
    expTrans ⟨fun μ => if μ = 1 then (1 : ℝ) else 0⟩ ≠ 1 := by
  intro h
  have hω := (expTrans_eq_one_iff _).mp h
  rw [omegaTrans_spatial_one] at hω
  have hnull : (null 1 : PGA) ≠ 0 := Generators.null_one_ne_zero
  have : (1 / 2 : ℝ) • null 1 ≠ 0 := by
    intro hz
    rcases (smul_eq_zero.mp hz) with h2 | hn
    · norm_num at h2
    · exact hnull hn
  exact this hω

/-- Full motor with vanishing torsion reduces to the translator. -/
theorem motor_of_pure_translation (p : TransParams) :
    motor ⟨⟨fun _ => 0, fun _ => 0⟩, p⟩ = expTrans p := by
  simp only [motor, rotorTorsion]
  have hω : omegaTorsion ⟨fun _ => 0, fun _ => 0⟩ = 0 := by
    simp [omegaTorsion]
  rw [hω, NormedSpace.exp_zero, one_mul]

/-! ### A varying translator leaves the spacetime coframe inertial -/

theorem translator_minkowski_leg (p : TransParams) (μ : Fin 4) :
    sandwich (expTrans p) (frameVec μ) =
      frameVec μ + (w31 μ * p.lambda μ) • ι e4Index := by
  simpa [frameVec] using KillingAxis.sandwich_expTrans_ι p μ

theorem translator_null_difference (p q : TransParams) (μ : Fin 4) :
    sandwich (expTrans p) (frameVec μ) - sandwich (expTrans q) (frameVec μ) =
      (w31 μ * (p.lambda μ - q.lambda μ)) • ι e4Index := by
  rw [translator_minkowski_leg, translator_minkowski_leg]
  module

/-- Inertial coframe, the Minkowski leg of every translator. -/
def inertialCoframe : Coframe :=
  fun a μ => if a = μ then 1 else 0

theorem inertial_weitzenbock (a μ ν : Fin 4) :
    weitzenbockTorsion (fun _ _ _ => (0 : ℝ)) a μ ν = 0 := by
  simp [weitzenbockTorsion]

theorem inducedMetric_inertial (μ ν : Fin 4) :
    inducedMetric inertialCoframe μ ν = if μ = ν then w31 μ else 0 := by
  rw [inducedMetric_eq_weighted]
  fin_cases μ <;> fin_cases ν <;>
    simp [inertialCoframe, w31]

/-! ### Motor `RT`: the spacetime leg is the rotor's leg -/

theorem rotor_fixes_null (p : Operations.TorsionParams) :
    sandwich (rotorTorsion p) (ι e4Index) = ι e4Index := by
  have hω : Commute (ι e4Index) (omegaTorsion p) :=
    KillingAxis.commute_e4_of_mem_lorentzSpan
      (LorentzLie.omegaTorsion_mem_lorentzSpan p)
  have hR : Commute (ι e4Index) (rotorTorsion p) := by
    simpa [rotorTorsion] using hω.exp_right
  rw [sandwich, hR.symm.eq, mul_assoc, rotor_unitary, mul_one]

theorem motor_minkowski_leg (p : OmegaParams) (μ : Fin 4) :
    sandwich (motor p) (frameVec μ) =
      sandwich (rotorTorsion p.torsion) (frameVec μ) +
        (w31 μ * p.trans.lambda μ) • ι e4Index := by
  rw [motor, Sandwich.sandwich_comp, translator_minkowski_leg, Sandwich.sandwich_add,
    Sandwich.sandwich_smul, rotor_fixes_null]

end Gravity

end DstDiophantine
