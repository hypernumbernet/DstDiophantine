import DstDiophantine.Gravity.Sandwich
import DstDiophantine.Gravity.Schwarzschild
import DstDiophantine.Algebra.Sandwich
import DstDiophantine.Algebra.Motor
import DstDiophantine.Algebra.Generators
import Mathlib.Tactic.NormNum

/-!
# Motor-induced reference vectors (chart tetrad bridge)

## Proved

* Motor sandwich of the Cl(3,1) frame vectors `ι a` (`a : Fin 4`).
* Pure radial boost recovers the hyperbolic `(t,r)` mixing
  `cosh φ · ι0 + sinh φ · ι1`.
* Pure translator `T = 1 + Ω_trans` is nontrivial when `λ ≠ 0`, and does
  **not** by itself reproduce the classical Schwarzschild diagonal gauge.

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

end Gravity

end DstDiophantine
