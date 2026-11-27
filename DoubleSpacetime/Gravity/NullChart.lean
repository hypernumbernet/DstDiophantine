import DoubleSpacetime.Algebra.Invariant
import DoubleSpacetime.Gravity.Coframe
import DoubleSpacetime.Gravity.NullRotation
import DoubleSpacetime.Gravity.PlaneTorsion
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Null rotation on the inertial chart

The coframe is the inverse of the parabolic rotor `1 + t(B⁺₀ + B⁻₁)` on Minkowski coordinates. Its
Maurer–Cartan generator is constant, and the coefficient mismatch `α₀ = β₁ = 2t` is zero.
-/

namespace DoubleSpacetime

namespace Gravity

open Finset PlaneTorsion Invariant

def nullMismatch (t : ℝ) : Operations.TorsionParams where
  alpha := fun a => if a = 0 then 2 * t else 0
  beta := fun a => if a = 1 then 2 * t else 0

theorem J_nullMismatch (t : ℝ) : J (nullMismatch t) = 0 := by
  rw [J_coef]
  simp [nullMismatch]

/-- `A` in the `so(1,3)` basis: boost `(t,x)` and rotation `(x,z)`, each with coefficient `2`. -/
def nullCoCoeff : Fin 6 → ℝ :=
  fun k => if k = 0 then 2 else if k = 4 then 2 else 0

def nullCoGen : Fin 4 → Fin 4 → ℝ :=
  soK nullCoCoeff

theorem nullCoGen_eq (ρ ν : Fin 4) : nullCoGen ρ ν = nullGen ρ ν := by
  fin_cases ρ <;> fin_cases ν <;>
    simp [nullCoGen, nullGen, nullCoCoeff, soK]

theorem nullCoGen_antisym : PlaneTorsion.MinkowskiAntisym nullCoGen :=
  soK_minkowskiAntisym _

theorem nullTeleparallel_eq_zero (d : Fin 4 → ℝ) :
    genTeleparallel nullCoGen d = 0 :=
  genTeleparallel_eq_zero nullCoGen_antisym d

theorem nullCoordTorsion_gen (t : ℝ) (d : Fin 4 → ℝ) (ρ μ ν : Fin 4) :
    (∑ a : Fin 4, nullFrame t ρ a *
        (d μ * nullVelocity (-t) (nullBasis ν) a -
          d ν * nullVelocity (-t) (nullBasis μ) a)) =
      genTorsion nullCoGen d ρ μ ν := by
  rw [nullCoordTorsion]
  simp [genTorsion, nullCoGen_eq]

private theorem weighted_eq_prod (x y : Fin 4 → ℝ) :
    ∑ a : Fin 4, w31 a * x a * y a = KillingAxis.minkowskiProd x y := by
  simp [Fin.sum_univ_four, KillingAxis.minkowskiProd, w31]

private theorem prod_basis (μ ν : Fin 4) :
    KillingAxis.minkowskiProd (nullBasis μ) (nullBasis ν) =
      if μ = ν then w31 μ else 0 := by
  fin_cases μ <;> fin_cases ν <;>
    simp [KillingAxis.minkowskiProd, nullBasis, w31]

theorem inducedMetric_nullCoframe (t : ℝ) (μ ν : Fin 4) :
    inducedMetric (nullCoframe t) μ ν = if μ = ν then w31 μ else 0 := by
  have hμ : (fun a => nullCoframe t a μ) = nullRotation (-t) (nullBasis μ) := rfl
  have hν : (fun a => nullCoframe t a ν) = nullRotation (-t) (nullBasis ν) := rfl
  rw [inducedMetric_eq_weighted, weighted_eq_prod, hμ, hν, minkowskiProd_nullRotation, prod_basis]

end Gravity

end DoubleSpacetime
