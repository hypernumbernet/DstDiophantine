import DstDiophantine.Gravity.Coframe
import DstDiophantine.Gravity.Sandwich
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# Exterior Schwarzschild diagonal tetrad

Defines the classical diagonal coframe on `r > rₛ` and proves that the induced
metric is the Schwarzschild metric
`diag(-(1-rₛ/r), (1-rₛ/r)⁻¹, r², r² sin²θ)`.
-/

namespace DstDiophantine

namespace Gravity

open Real

/-- Exterior radial domain predicate. -/
def IsExterior (rs r : ℝ) : Prop :=
  0 < rs ∧ rs < r

/-- Schwarzschild factor `A(r) = 1 - rₛ/r`. -/
noncomputable def schwarzschildA (rs r : ℝ) : ℝ :=
  1 - rs / r

theorem schwarzschildA_pos {rs r : ℝ} (h : IsExterior rs r) :
    0 < schwarzschildA rs r :=
  A_pos_of_exterior h.1 h.2

/-- Diagonal legs `(√A, A⁻¹/², r, r sin θ)`. -/
noncomputable def schwarzschildDiag (rs r θ : ℝ) : Fin 4 → ℝ
  | 0 => Real.sqrt (schwarzschildA rs r)
  | 1 => (Real.sqrt (schwarzschildA rs r))⁻¹
  | 2 => r
  | 3 => r * Real.sin θ

/-- Diagonal Schwarzschild coframe at fixed chart point `(t,r,θ,φ)`. -/
noncomputable def schwarzschildCoframe (rs r θ : ℝ) : Coframe :=
  diagonalCoframe (schwarzschildDiag rs r θ)

/-- Coordinate Schwarzschild metric components. -/
noncomputable def schwarzschildMetric (rs r θ : ℝ) (μ ν : Fin 4) : ℝ :=
  if μ = ν then
    match μ with
    | 0 => -(schwarzschildA rs r)
    | 1 => (schwarzschildA rs r)⁻¹
    | 2 => r ^ 2
    | 3 => r ^ 2 * (Real.sin θ) ^ 2
  else 0

theorem inducedMetric_schwarzschild {rs r θ : ℝ} (h : IsExterior rs r) :
    inducedMetric (schwarzschildCoframe rs r θ) =
      schwarzschildMetric rs r θ := by
  funext μ ν
  rw [schwarzschildCoframe, inducedMetric_diagonal]
  by_cases hμν : μ = ν
  · subst hμν
    have hA := schwarzschildA_pos h
    have hsq : (Real.sqrt (schwarzschildA rs r)) ^ 2 = schwarzschildA rs r :=
      Real.sq_sqrt hA.le
    have hs : Real.sqrt (schwarzschildA rs r) ≠ 0 := (Real.sqrt_pos.mpr hA).ne'
    simp only [schwarzschildMetric, ↓reduceIte]
    fin_cases μ
    · -- g₀₀ = -A
      change w31 0 * (schwarzschildDiag rs r θ 0) ^ 2 = -(schwarzschildA rs r)
      have hsq' : √(1 - rs / r) * √(1 - rs / r) = 1 - rs / r := by
        simpa [schwarzschildA, pow_two] using hsq
      simp only [schwarzschildDiag, w31, pow_two, schwarzschildA]
      linarith
    · -- g₁₁ = A⁻¹
      change w31 1 * (schwarzschildDiag rs r θ 1) ^ 2 = (schwarzschildA rs r)⁻¹
      simp only [schwarzschildDiag, w31, pow_two, one_mul, schwarzschildA]
      have hsq' : √(1 - rs / r) * √(1 - rs / r) = 1 - rs / r := by
        simpa [schwarzschildA, pow_two] using hsq
      calc (√(1 - rs / r))⁻¹ * (√(1 - rs / r))⁻¹
          = (√(1 - rs / r) * √(1 - rs / r))⁻¹ := by rw [mul_inv]
        _ = (1 - rs / r)⁻¹ := by rw [hsq']
    · change w31 2 * (schwarzschildDiag rs r θ 2) ^ 2 = r ^ 2
      simp [schwarzschildDiag, w31, pow_two]
    · change w31 3 * (schwarzschildDiag rs r θ 3) ^ 2 = r ^ 2 * (Real.sin θ) ^ 2
      simp only [schwarzschildDiag, w31, pow_two, one_mul]
      ring
  · simp [schwarzschildMetric, hμν]

/-- `(t,r)` diagonal scales coincide with boost scale factors from `Sandwich`. -/
theorem schwarzschildDiag_eq_boostScales {rs r θ : ℝ} (h : IsExterior rs r) :
    schwarzschildDiag rs r θ 0 =
        boostScaleFactors (schwarzschildRapidity rs r) 0 ∧
      schwarzschildDiag rs r θ 1 =
        boostScaleFactors (schwarzschildRapidity rs r) 1 := by
  have ⟨h0, h1⟩ := boostScaleFactors_schwarzschild h.1 h.2
  refine ⟨?_, ?_⟩
  · simpa [schwarzschildDiag, schwarzschildA] using h0.symm
  · simpa [schwarzschildDiag, schwarzschildA] using h1.symm

end Gravity

end DstDiophantine
