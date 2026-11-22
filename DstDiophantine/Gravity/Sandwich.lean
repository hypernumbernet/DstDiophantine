import DstDiophantine.Gravity.Coframe
import DstDiophantine.Algebra.Sandwich
import DstDiophantine.Algebra.Motor
import DstDiophantine.Algebra.Amplification
import DstDiophantine.Algebra.Generators
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Positivity

/-!
# Chart-level sandwich scales and Schwarzschild radial boost

Degenerate-metric sandwich preservation on full `G(3,1,1)` and a general grade-1 projection are not
derived here.
-/

namespace DstDiophantine

namespace Gravity

open PGA Generators Motor Amplification Real CliffordAlgebra
open Sandwich (sandwich)

export Sandwich (sandwich sandwich_one)

theorem sandwich_rotorTorsion (p : Operations.TorsionParams) (v : PGA) :
    sandwich (rotorTorsion p) v =
      rotorTorsion p * v * reverse (rotorTorsion p) :=
  rfl

/-- Schwarzschild radial rapidity `φ(r) = -½ log(1 - rₛ/r)`. -/
noncomputable def schwarzschildRapidity (rs r : ℝ) : ℝ :=
  -(1 / 2) * Real.log (1 - rs / r)

theorem A_pos_of_exterior {rs r : ℝ} (hrs : 0 < rs) (hr : rs < r) :
    0 < 1 - rs / r := by
  have : rs / r < 1 := (div_lt_one (hrs.trans hr)).mpr hr
  linarith

theorem schwarzschildRapidity_eq_log_sqrt {rs r : ℝ}
    (hrs : 0 < rs) (hr : rs < r) :
    schwarzschildRapidity rs r = -Real.log (Real.sqrt (1 - rs / r)) := by
  have hApos := A_pos_of_exterior hrs hr
  have hlog :
      Real.log (Real.sqrt (1 - rs / r)) = (1 / 2) * Real.log (1 - rs / r) := by
    rw [Real.sqrt_eq_rpow, Real.log_rpow hApos]
  simp [schwarzschildRapidity, hlog]

theorem exp_neg_schwarzschildRapidity {rs r : ℝ}
    (hrs : 0 < rs) (hr : rs < r) :
    Real.exp (-schwarzschildRapidity rs r) = Real.sqrt (1 - rs / r) := by
  have hApos := A_pos_of_exterior hrs hr
  rw [schwarzschildRapidity_eq_log_sqrt hrs hr, neg_neg,
    Real.exp_log (Real.sqrt_pos.mpr hApos)]

theorem exp_schwarzschildRapidity {rs r : ℝ}
    (hrs : 0 < rs) (hr : rs < r) :
    Real.exp (schwarzschildRapidity rs r) = (Real.sqrt (1 - rs / r))⁻¹ := by
  have h := exp_neg_schwarzschildRapidity hrs hr
  have hmul : Real.exp (schwarzschildRapidity rs r) *
      Real.exp (-schwarzschildRapidity rs r) = 1 := by
    simp [← Real.exp_add]
  rw [h] at hmul
  exact eq_inv_of_mul_eq_one_left hmul

/-- Diagonal boost scale factors matching Schwarzschild `(t,r)` legs. -/
noncomputable def boostScaleFactors (φ : ℝ) : Fin 4 → ℝ
  | 0 => Real.exp (-φ)
  | 1 => Real.exp φ
  | 2 | 3 => 1

theorem boostScaleFactors_schwarzschild {rs r : ℝ}
    (hrs : 0 < rs) (hr : rs < r) :
    boostScaleFactors (schwarzschildRapidity rs r) 0 = Real.sqrt (1 - rs / r) ∧
      boostScaleFactors (schwarzschildRapidity rs r) 1 =
        (Real.sqrt (1 - rs / r))⁻¹ := by
  refine ⟨?_, ?_⟩
  · simpa [boostScaleFactors] using exp_neg_schwarzschildRapidity hrs hr
  · simpa [boostScaleFactors] using exp_schwarzschildRapidity hrs hr

/-- Pure-boost torsional parameter for the radial Schwarzschild gauge. -/
noncomputable def radialBoostParams (rs r : ℝ) : Operations.TorsionParams :=
  Amplification.pureBoost (schwarzschildRapidity rs r)

theorem J_radialBoostParams {rs r : ℝ} :
    Invariant.J (radialBoostParams rs r) =
      (1 / 2) * (schwarzschildRapidity rs r) ^ 2 := by
  simpa [radialBoostParams] using Amplification.J_pureBoost (schwarzschildRapidity rs r)

theorem cosh_add_sinh (φ : ℝ) : cosh φ + sinh φ = Real.exp φ :=
  Real.cosh_add_sinh φ

theorem cosh_sub_sinh (φ : ℝ) : cosh φ - sinh φ = Real.exp (-φ) :=
  Real.cosh_sub_sinh φ

theorem boost_eigenvalues_eq_schwarzschild_scales {rs r : ℝ}
    (hrs : 0 < rs) (hr : rs < r) :
    let φ := schwarzschildRapidity rs r
    cosh φ - sinh φ = Real.sqrt (1 - rs / r) ∧
      cosh φ + sinh φ = (Real.sqrt (1 - rs / r))⁻¹ := by
  intro φ
  constructor
  · rw [cosh_sub_sinh, exp_neg_schwarzschildRapidity hrs hr]
  · rw [cosh_add_sinh, exp_schwarzschildRapidity hrs hr]

theorem sandwich_radialBoost_lightlike_plus (rs r : ℝ) :
    sandwich (rotorTorsion (radialBoostParams rs r)) (ι 0 + ι 1) =
      Real.exp (schwarzschildRapidity rs r) • (ι 0 + ι 1) := by
  simpa [radialBoostParams] using
    Sandwich.sandwich_pureBoost_lightlike_plus (schwarzschildRapidity rs r)

theorem sandwich_radialBoost_lightlike_minus (rs r : ℝ) :
    sandwich (rotorTorsion (radialBoostParams rs r)) (ι 0 - ι 1) =
      Real.exp (-schwarzschildRapidity rs r) • (ι 0 - ι 1) := by
  simpa [radialBoostParams] using
    Sandwich.sandwich_pureBoost_lightlike_minus (schwarzschildRapidity rs r)

theorem sandwich_radialBoost_null_plus (rs r : ℝ) :
    sandwich (rotorTorsion (radialBoostParams rs r)) (null 0 + null 1) =
      Real.exp (schwarzschildRapidity rs r) • (null 0 + null 1) := by
  simpa [radialBoostParams] using
    Sandwich.sandwich_pureBoost_null_plus (schwarzschildRapidity rs r)

theorem sandwich_radialBoost_null_minus (rs r : ℝ) :
    sandwich (rotorTorsion (radialBoostParams rs r)) (null 0 - null 1) =
      Real.exp (-schwarzschildRapidity rs r) • (null 0 - null 1) := by
  simpa [radialBoostParams] using
    Sandwich.sandwich_pureBoost_null_minus (schwarzschildRapidity rs r)

/-- Exterior chart: a radial ray's momentum scales by \(A^{-1/2}\) or by \(\sqrt{A}\). -/
theorem sandwich_radialBoost_null_eigenvalue {rs r : ℝ}
    (hrs : 0 < rs) (hr : rs < r) :
    sandwich (rotorTorsion (radialBoostParams rs r)) (null 0 + null 1) =
      (Real.sqrt (1 - rs / r))⁻¹ • (null 0 + null 1) ∧
    sandwich (rotorTorsion (radialBoostParams rs r)) (null 0 - null 1) =
      Real.sqrt (1 - rs / r) • (null 0 - null 1) := by
  refine ⟨?_, ?_⟩
  · rw [sandwich_radialBoost_null_plus, exp_schwarzschildRapidity hrs hr]
  · rw [sandwich_radialBoost_null_minus, exp_neg_schwarzschildRapidity hrs hr]

theorem sandwich_radialBoost_eigenvalues_eq_schwarzschild {rs r : ℝ}
    (hrs : 0 < rs) (hr : rs < r) :
    sandwich (rotorTorsion (radialBoostParams rs r)) (ι 0 + ι 1) =
      (Real.sqrt (1 - rs / r))⁻¹ • (ι 0 + ι 1) ∧
      sandwich (rotorTorsion (radialBoostParams rs r)) (ι 0 - ι 1) =
        Real.sqrt (1 - rs / r) • (ι 0 - ι 1) := by
  refine ⟨?_, ?_⟩
  · rw [sandwich_radialBoost_lightlike_plus, exp_schwarzschildRapidity hrs hr]
  · rw [sandwich_radialBoost_lightlike_minus, exp_neg_schwarzschildRapidity hrs hr]

end Gravity

end DstDiophantine
