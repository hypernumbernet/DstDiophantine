import DstDiophantine.Algebra.RelativeRotor
import DstDiophantine.Gravity.Coframe
import DstDiophantine.Gravity.PlaneTorsion
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Commuting boost and rotation

`hyperbolic 0` and `cyclic 0` commute, so the `(t,x)` boost and the `(y,z)`
rotation may be multiplied in either order. The product coframe keeps the
Minkowski metric. Its coordinate torsion is the sum of the two one-generator
torsions, and that sum has vanishing teleparallel scalar for every pair of
jets. A noncommuting pair is not claimed.
-/

namespace DstDiophantine

namespace Gravity

open Finset PlaneTorsion Real Generators

def orthBoostCoeff : Fin 6 → ℝ
  | 0 => 1
  | _ => 0

def orthRotCoeff : Fin 6 → ℝ
  | 5 => 1
  | _ => 0

def orthBoostGen : Fin 4 → Fin 4 → ℝ := soK orthBoostCoeff

def orthRotGen : Fin 4 → Fin 4 → ℝ := soK orthRotCoeff

noncomputable def productCoframe (φ θ : ℝ) : Coframe :=
  fun a μ =>
    if a = 0 ∧ μ = 0 then Real.cosh φ
    else if a = 0 ∧ μ = 1 then Real.sinh φ
    else if a = 1 ∧ μ = 0 then Real.sinh φ
    else if a = 1 ∧ μ = 1 then Real.cosh φ
    else if a = 2 ∧ μ = 2 then Real.cos θ
    else if a = 2 ∧ μ = 3 then Real.sin θ
    else if a = 3 ∧ μ = 2 then -Real.sin θ
    else if a = 3 ∧ μ = 3 then Real.cos θ
    else 0

theorem product_blockDet_tx (φ θ : ℝ) :
    productCoframe φ θ 0 0 * productCoframe φ θ 1 1 -
        productCoframe φ θ 0 1 * productCoframe φ θ 1 0 = 1 := by
  simp [productCoframe]
  ring_nf
  exact Real.cosh_sq_sub_sinh_sq φ

theorem product_blockDet_yz (φ θ : ℝ) :
    productCoframe φ θ 2 2 * productCoframe φ θ 3 3 -
        productCoframe φ θ 2 3 * productCoframe φ θ 3 2 = 1 := by
  simp [productCoframe]
  ring_nf
  exact Real.cos_sq_add_sin_sq θ

theorem inducedMetric_product (φ θ : ℝ) (μ ν : Fin 4) :
    inducedMetric (productCoframe φ θ) μ ν = if μ = ν then w31 μ else 0 := by
  rw [inducedMetric_eq_weighted]
  have hb := Real.cosh_sq_sub_sinh_sq φ
  have hr := Real.cos_sq_add_sin_sq θ
  fin_cases μ <;> fin_cases ν <;>
    simp [Fin.sum_univ_four, productCoframe, w31] <;>
    ring_nf <;> linarith

def productTorsion (dφ dθ : Fin 4 → ℝ) (ρ μ ν : Fin 4) : ℝ :=
  genTorsion orthBoostGen dφ ρ μ ν + genTorsion orthRotGen dθ ρ μ ν

def productDown (dφ dθ : Fin 4 → ℝ) (ρ μ ν : Fin 4) : ℝ :=
  w31 ρ * productTorsion dφ dθ ρ μ ν

def productUp (dφ dθ : Fin 4 → ℝ) (ρ μ ν : Fin 4) : ℝ :=
  w31 ρ * w31 μ * w31 ν * productDown dφ dθ ρ μ ν

def productTrace (dφ dθ : Fin 4 → ℝ) (ρ : Fin 4) : ℝ :=
  ∑ σ : Fin 4, productTorsion dφ dθ σ ρ σ

def productSquare (dφ dθ : Fin 4 → ℝ) : ℝ :=
  ∑ ρ : Fin 4, ∑ μ : Fin 4, ∑ ν : Fin 4, productDown dφ dθ ρ μ ν * productUp dφ dθ ρ μ ν

def productCross (dφ dθ : Fin 4 → ℝ) : ℝ :=
  ∑ ρ : Fin 4, ∑ μ : Fin 4, ∑ ν : Fin 4, productDown dφ dθ ρ μ ν * productUp dφ dθ ν μ ρ

def productTraceContr (dφ dθ : Fin 4 → ℝ) : ℝ :=
  ∑ ρ : Fin 4, productTrace dφ dθ ρ * (w31 ρ * productTrace dφ dθ ρ)

noncomputable def productTeleparallel (dφ dθ : Fin 4 → ℝ) : ℝ :=
  (1 / 4) * productSquare dφ dθ + (1 / 2) * productCross dφ dθ - productTraceContr dφ dθ

private theorem sameRow_zero (dφ dθ : Fin 4 → ℝ) (ρ μ ν : Fin 4) :
    genTdown orthBoostGen dφ ρ μ ν * genTup orthRotGen dθ ρ μ ν = 0 := by
  fin_cases ρ <;> fin_cases μ <;> fin_cases ν <;>
    simp [genTdown, genTup, genTorsion, orthBoostGen, orthRotGen, soK, orthBoostCoeff, orthRotCoeff,
      w31]

private theorem sameRow_zero' (dφ dθ : Fin 4 → ℝ) (ρ μ ν : Fin 4) :
    genTdown orthRotGen dθ ρ μ ν * genTup orthBoostGen dφ ρ μ ν = 0 := by
  fin_cases ρ <;> fin_cases μ <;> fin_cases ν <;>
    simp [genTdown, genTup, genTorsion, orthBoostGen, orthRotGen, soK, orthBoostCoeff, orthRotCoeff,
      w31]

private theorem swappedRow_zero (dφ dθ : Fin 4 → ℝ) (ρ μ ν : Fin 4) :
    genTdown orthBoostGen dφ ρ μ ν * genTup orthRotGen dθ ν μ ρ = 0 := by
  fin_cases ρ <;> fin_cases μ <;> fin_cases ν <;>
    simp [genTdown, genTup, genTorsion, orthBoostGen, orthRotGen, soK, orthBoostCoeff, orthRotCoeff,
      w31]

private theorem swappedRow_zero' (dφ dθ : Fin 4 → ℝ) (ρ μ ν : Fin 4) :
    genTdown orthRotGen dθ ρ μ ν * genTup orthBoostGen dφ ν μ ρ = 0 := by
  fin_cases ρ <;> fin_cases μ <;> fin_cases ν <;>
    simp [genTdown, genTup, genTorsion, orthBoostGen, orthRotGen, soK, orthBoostCoeff, orthRotCoeff,
      w31]

private theorem traceRow_zero (dφ dθ : Fin 4 → ℝ) (ρ : Fin 4) :
    genTrace orthBoostGen dφ ρ * genTraceUp orthRotGen dθ ρ = 0 := by
  fin_cases ρ <;>
    simp [genTrace, genTraceUp, Fin.sum_univ_four, genTorsion, orthBoostGen, orthRotGen, soK,
      orthBoostCoeff, orthRotCoeff, w31]

private theorem traceRow_zero' (dφ dθ : Fin 4 → ℝ) (ρ : Fin 4) :
    genTrace orthRotGen dθ ρ * genTraceUp orthBoostGen dφ ρ = 0 := by
  fin_cases ρ <;>
    simp [genTrace, genTraceUp, Fin.sum_univ_four, genTorsion, orthBoostGen, orthRotGen, soK,
      orthBoostCoeff, orthRotCoeff, w31]

private theorem down_split (dφ dθ : Fin 4 → ℝ) (ρ μ ν : Fin 4) :
    productDown dφ dθ ρ μ ν =
      genTdown orthBoostGen dφ ρ μ ν + genTdown orthRotGen dθ ρ μ ν := by
  simp only [productDown, productTorsion, genTdown]
  ring

private theorem up_split (dφ dθ : Fin 4 → ℝ) (ρ μ ν : Fin 4) :
    productUp dφ dθ ρ μ ν =
      genTup orthBoostGen dφ ρ μ ν + genTup orthRotGen dθ ρ μ ν := by
  simp only [productUp, down_split dφ dθ, genTup]
  ring

private theorem trace_split (dφ dθ : Fin 4 → ℝ) (ρ : Fin 4) :
    productTrace dφ dθ ρ =
      genTrace orthBoostGen dφ ρ + genTrace orthRotGen dθ ρ := by
  simp only [productTrace, productTorsion, genTrace, Finset.sum_add_distrib]

private theorem sum_sameRow (dφ dθ : Fin 4 → ℝ) :
    (∑ ρ : Fin 4, ∑ μ : Fin 4, ∑ ν : Fin 4,
        genTdown orthBoostGen dφ ρ μ ν * genTup orthRotGen dθ ρ μ ν) = 0 :=
  Finset.sum_eq_zero fun ρ _ => Finset.sum_eq_zero fun μ _ =>
    Finset.sum_eq_zero fun ν _ => sameRow_zero dφ dθ ρ μ ν

private theorem sum_sameRow' (dφ dθ : Fin 4 → ℝ) :
    (∑ ρ : Fin 4, ∑ μ : Fin 4, ∑ ν : Fin 4,
        genTdown orthRotGen dθ ρ μ ν * genTup orthBoostGen dφ ρ μ ν) = 0 :=
  Finset.sum_eq_zero fun ρ _ => Finset.sum_eq_zero fun μ _ =>
    Finset.sum_eq_zero fun ν _ => sameRow_zero' dφ dθ ρ μ ν

private theorem sum_swappedRow (dφ dθ : Fin 4 → ℝ) :
    (∑ ρ : Fin 4, ∑ μ : Fin 4, ∑ ν : Fin 4,
        genTdown orthBoostGen dφ ρ μ ν * genTup orthRotGen dθ ν μ ρ) = 0 :=
  Finset.sum_eq_zero fun ρ _ => Finset.sum_eq_zero fun μ _ =>
    Finset.sum_eq_zero fun ν _ => swappedRow_zero dφ dθ ρ μ ν

private theorem sum_swappedRow' (dφ dθ : Fin 4 → ℝ) :
    (∑ ρ : Fin 4, ∑ μ : Fin 4, ∑ ν : Fin 4,
        genTdown orthRotGen dθ ρ μ ν * genTup orthBoostGen dφ ν μ ρ) = 0 :=
  Finset.sum_eq_zero fun ρ _ => Finset.sum_eq_zero fun μ _ =>
    Finset.sum_eq_zero fun ν _ => swappedRow_zero' dφ dθ ρ μ ν

private theorem sum_traceRow (dφ dθ : Fin 4 → ℝ) :
    (∑ ρ : Fin 4, genTrace orthBoostGen dφ ρ * genTraceUp orthRotGen dθ ρ) = 0 :=
  Finset.sum_eq_zero fun ρ _ => traceRow_zero dφ dθ ρ

private theorem sum_traceRow' (dφ dθ : Fin 4 → ℝ) :
    (∑ ρ : Fin 4, genTrace orthRotGen dθ ρ * genTraceUp orthBoostGen dφ ρ) = 0 :=
  Finset.sum_eq_zero fun ρ _ => traceRow_zero' dφ dθ ρ

theorem productTeleparallel_eq_zero (dφ dθ : Fin 4 → ℝ) :
    productTeleparallel dφ dθ = 0 := by
  have hBoost : genTeleparallel orthBoostGen dφ = 0 :=
    genTeleparallel_eq_zero (soK_minkowskiAntisym orthBoostCoeff) dφ
  have hRot : genTeleparallel orthRotGen dθ = 0 :=
    genTeleparallel_eq_zero (soK_minkowskiAntisym orthRotCoeff) dθ
  have hsq : productSquare dφ dθ =
      genSquare orthBoostGen dφ + genSquare orthRotGen dθ := by
    unfold productSquare genSquare
    simp_rw [down_split dφ dθ, up_split dφ dθ, add_mul, mul_add, Finset.sum_add_distrib,
      sum_sameRow dφ dθ, sum_sameRow' dφ dθ, add_zero, zero_add]
  have hcross : productCross dφ dθ =
      genCross orthBoostGen dφ + genCross orthRotGen dθ := by
    unfold productCross genCross
    simp_rw [down_split dφ dθ, up_split dφ dθ, add_mul, mul_add, Finset.sum_add_distrib,
      sum_swappedRow dφ dθ, sum_swappedRow' dφ dθ, add_zero, zero_add]
  have htrace : productTraceContr dφ dθ =
      genTraceContr orthBoostGen dφ + genTraceContr orthRotGen dθ := by
    unfold productTraceContr genTraceContr
    simp_rw [trace_split dφ dθ]
    simp_rw [show ∀ ρ, w31 ρ * (genTrace orthBoostGen dφ ρ + genTrace orthRotGen dθ ρ) =
        genTraceUp orthBoostGen dφ ρ + genTraceUp orthRotGen dθ ρ by
        intro ρ; rw [genTraceUp, genTraceUp]; ring]
    simp_rw [add_mul, mul_add, Finset.sum_add_distrib, sum_traceRow dφ dθ, sum_traceRow' dφ dθ,
      add_zero, zero_add]
  unfold productTeleparallel
  rw [hsq, hcross, htrace]
  have hsplit :
      (1 / 4) * (genSquare orthBoostGen dφ + genSquare orthRotGen dθ) +
          (1 / 2) * (genCross orthBoostGen dφ + genCross orthRotGen dθ) -
          (genTraceContr orthBoostGen dφ + genTraceContr orthRotGen dθ) =
        genTeleparallel orthBoostGen dφ + genTeleparallel orthRotGen dθ := by
    unfold genTeleparallel
    ring
  rw [hsplit, hBoost, hRot, add_zero]

/-- The generators commute, so the product does not depend on an ordering of planes. -/
theorem orth_generators_commute :
    Commute (hyperbolic 0) (cyclic 0) :=
  RelativeRotor.commute_hyperbolic_cyclic_same 0

end Gravity

end DstDiophantine
