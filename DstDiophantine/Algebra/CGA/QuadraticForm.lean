import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-!
# Quadratic form for 1D conformal GA `Cl(2,1)`

Diagnostic probe (not the spacetime algebra of the Diophantine path).
Signature weights `(-,+,+)` on `Fin 3`: time-like `e₋`, Euclidean line `e`,
space-like `e₊`.
-/

namespace DstDiophantine

namespace CGA

abbrev Vec3 := Fin 3 → ℝ

/-- Weights for `Cl(2,1)`: `e₋² = -1`, `e² = +1`, `e₊² = +1`. -/
def w21 : Fin 3 → ℝ
  | 0 => -1
  | 1 | 2 => 1

/-- Quadratic form for `Cl(2,1)`. -/
noncomputable def Q21 : QuadraticForm ℝ Vec3 :=
  QuadraticMap.weightedSumSquares ℝ w21

def e3vec (μ : Fin 3) : Vec3 :=
  Pi.single μ 1

theorem Q21_e3vec (μ : Fin 3) : Q21 (e3vec μ) = w21 μ := by
  simp only [Q21, QuadraticMap.weightedSumSquares_apply, e3vec, w21]
  fin_cases μ <;> simp [Pi.single, Fin.sum_univ_three]

theorem Q21_isOrtho_basis (i j : Fin 3) (hij : i ≠ j) :
    Q21.IsOrtho (e3vec i) (e3vec j) := by
  rw [QuadraticMap.isOrtho_def]
  simp only [Q21, QuadraticMap.weightedSumSquares_apply, e3vec, w21]
  fin_cases i <;> fin_cases j <;>
    first
    | exact absurd rfl hij
    | simp [Pi.single, Fin.sum_univ_three, mul_add, add_mul, mul_one, add_assoc]

end CGA

end DstDiophantine
