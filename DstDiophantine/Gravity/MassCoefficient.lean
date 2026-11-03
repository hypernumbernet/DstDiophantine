import DstDiophantine.Gravity.DualRotorDynamics
import DstDiophantine.Gravity.RestMass
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The rest-mass coefficient, read at equal rapidity

An equal-rapidity state is critical for both the stiffness potential and
the unsigned mass. A pure lag `δ` adds `δ²/4` to the unsigned mass at every
common rapidity, and adds `(m/2)δ²` to the potential. The second difference
of the mass in that lag is `1/2`, and the second difference of the potential
is `m`. The kinetic term is `J` on the angular velocity, and its cross
coefficient is that same `1/2`. The common acceleration per unit lag is
minus the ratio of the two coefficients of `δ²`.

The quotient of the potential by twice the transverse unsigned mass — the
excess of `M` over the equal-rapidity state of the same sums — equals `m`
at every configuration that is not itself of equal rapidity, and does not
depend on which state is used.

The Jacobi integral along an equal-rapidity motion is zero, so the
coefficient is not an energy of that state and not the unsigned mass
sitting there. The value of `m` is not fixed.
-/

namespace DstDiophantine

namespace Gravity

open Invariant Operations RelativeRotor

/-! ### Kinetic term is `J` on the velocity -/

theorem kinetic_axis_eq_J (φdot θdot : ℝ) :
    (1 / 2) * φdot ^ 2 - (1 / 2) * θdot ^ 2 = J (axisParams φdot θdot) := by
  rw [J_axisParams]
  ring

theorem kinetic_sum_eq_J (φdot θdot : Fin 3 → ℝ) :
    (∑ a : Fin 3, ((1 / 2) * φdot a ^ 2 - (1 / 2) * θdot a ^ 2)) =
      J ⟨φdot, θdot⟩ := by
  rw [J_coef]
  simp only [Fin.sum_univ_three]
  ring

/-! ### Transverse mass above the equal-rapidity state -/

/-- Equal-rapidity state with the same per-axis sums. -/
noncomputable def equalRapidity (p : Operations.TorsionParams) : Operations.TorsionParams where
  alpha := fun a => (p.alpha a + p.beta a) / 2
  beta := fun a => (p.alpha a + p.beta a) / 2

/-- Unsigned mass above that equal-rapidity state. -/
noncomputable def transverseMass (p : Operations.TorsionParams) : ℝ :=
  mass p - mass (equalRapidity p)

theorem transverseMass_eq (p : Operations.TorsionParams) :
    transverseMass p = (1 / 4) * lagSq p := by
  unfold transverseMass equalRapidity
  rw [mass_coef, mass_coef, lagSq]
  simp only [Fin.sum_univ_three]
  ring

theorem stiffness_eq_transverse (m : ℝ) (p : Operations.TorsionParams) :
    stiffnessPotential m p = 2 * m * transverseMass p := by
  rw [stiffnessPotential_eq_lag, transverseMass_eq]
  ring

theorem transverseMass_ne_of_lag {p : Operations.TorsionParams} (h : lagSq p ≠ 0) :
    transverseMass p ≠ 0 := by
  rw [transverseMass_eq]
  exact mul_ne_zero (by norm_num) h

/-- Off equal rapidity, `m` is the potential divided by twice the transverse mass. -/
theorem stiffness_quotient {m : ℝ} {p : Operations.TorsionParams} (h : lagSq p ≠ 0) :
    stiffnessPotential m p / transverseMass p = 2 * m := by
  rw [stiffness_eq_transverse]
  field_simp [transverseMass_ne_of_lag h]

theorem stiffness_quotient_independent {m : ℝ} {p q : Operations.TorsionParams}
    (hp : lagSq p ≠ 0) (hq : lagSq q ≠ 0) :
    stiffnessPotential m p / transverseMass p =
      stiffnessPotential m q / transverseMass q := by
  rw [stiffness_quotient hp, stiffness_quotient hq]

/-! ### Second differences in a pure lag -/

/-- Second difference of unsigned mass under a pure lag about rapidity `φ`. -/
noncomputable def lagMassSecond (φ δ : ℝ) : ℝ :=
  (mass (axisParams (φ + δ / 2) (φ - δ / 2)) +
      mass (axisParams (φ - δ / 2) (φ + δ / 2)) -
      2 * mass (axisParams φ φ)) / δ ^ 2

/-- Second difference of the stiffness under the same lag. -/
noncomputable def lagPotentialSecond (m φ δ : ℝ) : ℝ :=
  (stiffnessPotential m (axisParams (φ + δ / 2) (φ - δ / 2)) +
      stiffnessPotential m (axisParams (φ - δ / 2) (φ + δ / 2)) -
      2 * stiffnessPotential m (axisParams φ φ)) / δ ^ 2

theorem lagMassSecond_eq {φ δ : ℝ} (hδ : δ ≠ 0) :
    lagMassSecond φ δ = 1 / 2 := by
  unfold lagMassSecond
  rw [mass_axisParams, mass_axisParams, mass_axisParams]
  field_simp [hδ]
  ring

theorem lagPotentialSecond_eq {m φ δ : ℝ} (hδ : δ ≠ 0) :
    lagPotentialSecond m φ δ = m := by
  unfold lagPotentialSecond
  rw [stiffness_axis, stiffness_axis, stiffness_axis]
  field_simp [hδ]
  ring

theorem lagMassSecond_independent {φ₁ φ₂ δ : ℝ} (hδ : δ ≠ 0) :
    lagMassSecond φ₁ δ = lagMassSecond φ₂ δ := by
  rw [lagMassSecond_eq hδ, lagMassSecond_eq hδ]

theorem lagPotentialSecond_independent {m φ₁ φ₂ δ : ℝ} (hδ : δ ≠ 0) :
    lagPotentialSecond m φ₁ δ = lagPotentialSecond m φ₂ δ := by
  rw [lagPotentialSecond_eq hδ, lagPotentialSecond_eq hδ]

theorem lagSecond_ratio_eq {m φ δ : ℝ} (hδ : δ ≠ 0) :
    lagPotentialSecond m φ δ / lagMassSecond φ δ = 2 * m := by
  rw [lagPotentialSecond_eq hδ, lagMassSecond_eq hδ]
  field_simp

/-- The kinetic cross coefficient equals the mass second difference. -/
theorem mixed_coeff_eq_lagMassSecond (m φ θ φdot θdot φ₀ δ : ℝ) (hδ : δ ≠ 0) :
    paperLagrangian m φ θ φdot θdot =
      lagMassSecond φ₀ δ * (φdot + θdot) * (φdot - θdot) -
        (m / 2) * (φ - θ) ^ 2 := by
  rw [paperLagrangian_eq_mixed, lagMassSecond_eq hδ]

/-- Common acceleration per unit lag is minus the ratio of the second differences. -/
theorem common_accel_eq_lagSecond_ratio {m φ θ φddot θddot : ℝ}
    (h : PaperActualEL m φ θ φddot θddot) (hδ : φ - θ ≠ 0) :
    (φddot + θddot) / (φ - θ) =
      -(lagPotentialSecond m ((φ + θ) / 2) (φ - θ) /
          lagMassSecond ((φ + θ) / 2) (φ - θ)) := by
  rw [paperActualEL_common_driven h, lagPotentialSecond_eq hδ, lagMassSecond_eq hδ]
  field_simp [hδ]

/-! ### The equal-rapidity motion does not store the coefficient -/

theorem aligned_jacobi_zero (m φ φdot : ℝ) :
    paperEnergy m φ φ φdot φdot = 0 := by
  unfold paperEnergy
  ring

theorem aligned_jacobi_independent (m₁ m₂ φ φdot : ℝ) :
    paperEnergy m₁ φ φ φdot φdot = paperEnergy m₂ φ φ φdot φdot := by
  rw [aligned_jacobi_zero, aligned_jacobi_zero]

theorem aligned_energy_not_unsigned_mass {φ : ℝ} (hφ : φ ≠ 0) :
    paperEnergy 1 φ φ 0 0 = 0 ∧ mass (axisParams φ φ) ≠ 0 := by
  refine ⟨aligned_jacobi_zero 1 φ 0, ?_⟩
  rw [mass_axisParams]
  nlinarith [sq_pos_of_ne_zero hφ]

end Gravity

end DstDiophantine
