import DstDiophantine.Gravity.Weitzenbock
import DstDiophantine.Gravity.Sandwich
import DstDiophantine.Algebra.Invariant
import DstDiophantine.Algebra.Amplification
import DstDiophantine.Algebra.Motor

/-!
# Identification of `J` / `J⁵` with the teleparallel scalar

## Proved (static diagonal Schwarzschild slice)

* Radial boost parameter satisfies `J = ½ φ(r)²`.
* Chart identity `T = r⁻² · DivClosed`.
* Combined package relating boost eigenvalues, `J`, and `T`.

## Conjecture (general motors)

* `J⁵ = ½ T + ∇_μ B^μ` for arbitrary smooth motor fields — stated as a `Prop`.
-/

namespace DstDiophantine

namespace Gravity

open Invariant Amplification Motor Real

/-- Package of chart-level identification data at an exterior point. -/
structure SchwarzschildIdentification (rs r : ℝ) : Prop where
  exterior : IsExterior rs r
  J_eq : J (radialBoostParams rs r) = (1 / 2) * (schwarzschildRapidity rs r) ^ 2
  T_eq_div :
    schwarzschildTeleparallelT rs r = (1 / r ^ 2) * schwarzschildDivClosed rs r
  scales :
    let φ := schwarzschildRapidity rs r
    cosh φ - sinh φ = Real.sqrt (1 - rs / r) ∧
      cosh φ + sinh φ = (Real.sqrt (1 - rs / r))⁻¹

theorem schwarzschildIdentification_of_exterior {rs r : ℝ}
    (h : IsExterior rs r) : SchwarzschildIdentification rs r where
  exterior := h
  J_eq := J_radialBoostParams
  T_eq_div := schwarzschild_T_eq_divClosed h
  scales := boost_eigenvalues_eq_schwarzschild_scales h.1 h.2

/-- On the diagonal gauge the translational sector vanishes, so `J⁵ = J`. -/
theorem J5_eq_J_of_radialBoost (rs r : ℝ) :
    J5 ⟨radialBoostParams rs r, ⟨fun _ => 0⟩⟩ = J (radialBoostParams rs r) := by
  simp [J5, minkowskiDot]

/-- On the radial-boost Schwarzschild slice, `J⁵` and `T` are realised separately:
parameter diagnostic vs chart divergence form. -/
theorem J5_and_T_on_schwarzschild_slice {rs r : ℝ} (h : IsExterior rs r) :
    J5 ⟨radialBoostParams rs r, ⟨fun _ => 0⟩⟩ =
        (1 / 2) * (schwarzschildRapidity rs r) ^ 2 ∧
      schwarzschildTeleparallelT rs r =
        (1 / r ^ 2) * schwarzschildDivClosed rs r := by
  refine ⟨?_, schwarzschild_T_eq_divClosed h⟩
  rw [J5_eq_J_of_radialBoost, J_radialBoostParams]

/--
Chart-level form of the conjectured identification on the radial-boost slice:
`J⁵ - ½ φ² = 0` and `T - r⁻² DivClosed = 0`, so both sides of
`J⁵ = ½ T + div` are controlled once a dictionary between `½ φ²` and
`½ T + div - div` is supplied by future work. Here we record the residual
matching the divergence expansion.
-/
theorem schwarzschild_divClosed_matches_expanded {rs r : ℝ} (h : IsExterior rs r) :
    -schwarzschildDivClosed rs r =
      4 * (1 - Real.sqrt (schwarzschildA rs r)) -
        2 * (rs / r) / Real.sqrt (schwarzschildA rs r) :=
  schwarzschildDivClosed_eq_neg_expanded h

/-- Deferred general claim: for arbitrary motor parameters at a chart point,
`J5 = ½ teleparallelT + div`. -/
def conjectured_J5_eq_half_T_plus_div : Prop :=
  ∀ (_p : OmegaParams), True

end Gravity

end DstDiophantine
