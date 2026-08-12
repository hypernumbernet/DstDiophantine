import DstDiophantine.Algebra.QuadraticForm
import Mathlib.Tactic.FinCases
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Chart coframes and induced metrics

Pointwise tetrads `e^a_μ` on a fixed coordinate chart (`Fin 4` indices), with the
Minkowski fibre metric `η = diag(-1,+1,+1,+1)` and the induced spacetime metric
`g_μν = η_ab e^a_μ e^b_ν`.
-/

namespace DstDiophantine

namespace Gravity

open Finset BigOperators

/-- Coframe / tetrad components `e^a_μ` at a point. -/
abbrev Coframe := Fin 4 → Fin 4 → ℝ

/-- Minkowski fibre metric `η_ab`. -/
def eta (a b : Fin 4) : ℝ :=
  if a = b then w31 a else 0

@[simp] theorem eta_diag (a : Fin 4) : eta a a = w31 a := by
  simp [eta]

@[simp] theorem eta_off {a b : Fin 4} (h : a ≠ b) : eta a b = 0 := by
  simp [eta, h]

/-- Induced spacetime metric `g_μν = η_ab e^a_μ e^b_ν`. -/
noncomputable def inducedMetric (e : Coframe) (μ ν : Fin 4) : ℝ :=
  ∑ a : Fin 4, ∑ b : Fin 4, eta a b * e a μ * e b ν

theorem inducedMetric_eq_weighted (e : Coframe) (μ ν : Fin 4) :
    inducedMetric e μ ν = ∑ a : Fin 4, w31 a * e a μ * e a ν := by
  simp only [inducedMetric]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [eta, mul_assoc]
  calc
    (∑ b : Fin 4, (if a = b then w31 a else 0) * (e a μ * e b ν)) =
        ∑ b : Fin 4, if a = b then w31 a * (e a μ * e b ν) else 0 := by
          refine Finset.sum_congr rfl fun b _ => ?_
          split_ifs <;> ring
    _ = w31 a * (e a μ * e a ν) := by
          simp [Finset.sum_ite_eq]

/-- Inverse-tetrad skeleton for a diagonal coframe. -/
noncomputable def diagonalInverse (e : Coframe) (a μ : Fin 4) : ℝ :=
  if a = μ then (e a a)⁻¹ else 0

def zeroCoframe : Coframe := fun _ _ => 0

@[simp] theorem inducedMetric_zero (μ ν : Fin 4) :
    inducedMetric zeroCoframe μ ν = 0 := by
  simp [inducedMetric_eq_weighted, zeroCoframe]

/-- Diagonal coframe constructor. -/
def diagonalCoframe (d : Fin 4 → ℝ) : Coframe :=
  fun a μ => if a = μ then d a else 0

theorem inducedMetric_diagonal (d : Fin 4 → ℝ) (μ ν : Fin 4) :
    inducedMetric (diagonalCoframe d) μ ν =
      (if μ = ν then w31 μ * (d μ) ^ 2 else 0) := by
  rw [inducedMetric_eq_weighted]
  simp only [diagonalCoframe]
  by_cases hμν : μ = ν
  · subst hμν
    calc
      (∑ a : Fin 4, w31 a * (if a = μ then d a else 0) *
          (if a = μ then d a else 0)) =
          ∑ a : Fin 4, w31 a * (if a = μ then (d a) ^ 2 else 0) := by
            refine Finset.sum_congr rfl fun a _ => ?_
            split_ifs <;> ring
      _ = w31 μ * (d μ) ^ 2 := by
          simp [pow_two]
      _ = if μ = μ then w31 μ * (d μ) ^ 2 else 0 := by simp
  · simp only [hμν, ↓reduceIte]
    refine Finset.sum_eq_zero fun a _ => ?_
    by_cases ha : a = μ
    · subst ha
      simp [hμν]
    · simp [ha]

end Gravity

end DstDiophantine
