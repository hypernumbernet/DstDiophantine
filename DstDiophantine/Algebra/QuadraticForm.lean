import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-!
# Quadratic forms for Cl(3,1) and G(3,1,1)

Signature `(3,1)` on four dimensions and `(3,1,1)` on five dimensions with a null
direction `e₄` (`Q(e₄) = 0`).
-/

namespace DstDiophantine

abbrev Vec4 := Fin 4 → ℝ
abbrev Vec5 := Fin 5 → ℝ

/-- Weights for the Minkowski signature `(-,+,+,+)` on `Fin 4`. -/
def w31 : Fin 4 → ℝ
  | 0 => -1
  | 1 | 2 | 3 => 1

/-- Weights for `G(3,1,1)`: Minkowski on `e₀…e₃` and null `e₄`. -/
def w311 : Fin 5 → ℝ
  | 0 => -1
  | 1 | 2 | 3 => 1
  | 4 => 0

/-- Quadratic form for `Cl(3,1)`. -/
noncomputable def Q31 : QuadraticForm ℝ Vec4 :=
  QuadraticMap.weightedSumSquares ℝ w31

/-- Quadratic form for `G(3,1,1) = Cl(3,1,1)`. -/
noncomputable def Q311 : QuadraticForm ℝ Vec5 :=
  QuadraticMap.weightedSumSquares ℝ w311

/-- Standard basis vector in `Fin 4 → ℝ`. -/
def e4vec (μ : Fin 4) : Vec4 :=
  Pi.single μ 1

/-- Standard basis vector in `Fin 5 → ℝ`. -/
def e5vec (μ : Fin 5) : Vec5 :=
  Pi.single μ 1

/-- Embed `Fin 4 → ℝ` into the first four components of `Fin 5 → ℝ`. -/
def extend4 (v : Vec4) : Vec5 :=
  fun i =>
    match i with
    | ⟨0, _⟩ => v 0
    | ⟨1, _⟩ => v 1
    | ⟨2, _⟩ => v 2
    | ⟨3, _⟩ => v 3
    | ⟨4, _⟩ => 0

@[simp] theorem extend4_apply (v : Vec4) (μ : Fin 4) :
    extend4 v (Fin.castAdd 1 μ) = v μ := by
  fin_cases μ <;> simp [extend4]

@[simp] theorem extend4_last (v : Vec4) : extend4 v (Fin.last 4) = 0 := by
  rfl

@[simp] theorem extend4_castSucc (v : Vec4) (i : Fin 4) :
    extend4 v (Fin.castSucc i) = v i := by
  fin_cases i <;> rfl

@[simp] theorem extend4_e4vec (μ : Fin 4) : extend4 (e4vec μ) = e5vec (Fin.castAdd 1 μ) := by
  funext i
  fin_cases i <;> fin_cases μ <;> simp [extend4, e4vec, e5vec, Pi.single]

theorem Q311_extend4 (v : Vec4) : Q311 (extend4 v) = Q31 v := by
  simp only [Q311, Q31, QuadraticMap.weightedSumSquares_apply, w311, w31, extend4]
  rw [Fin.sum_univ_five, Fin.sum_univ_four]
  simp

theorem Q311_e5vec (μ : Fin 5) : Q311 (e5vec μ) = w311 μ := by
  simp only [Q311, QuadraticMap.weightedSumSquares_apply, e5vec, w311]
  fin_cases μ <;> simp [Pi.single, Fin.sum_univ_five]

theorem Q31_e4vec (μ : Fin 4) : Q31 (e4vec μ) = w31 μ := by
  simp only [Q31, QuadraticMap.weightedSumSquares_apply, e4vec, w31]
  fin_cases μ <;> simp [Pi.single, Fin.sum_univ_four]

theorem Q311_isOrtho_basis (i j : Fin 5) (hij : i ≠ j) :
    Q311.IsOrtho (e5vec i) (e5vec j) := by
  rw [QuadraticMap.isOrtho_def]
  simp only [Q311, QuadraticMap.weightedSumSquares_apply, e5vec, w311]
  fin_cases i <;> fin_cases j <;>
    first
    | exact absurd rfl hij
    | simp [Pi.single, Fin.sum_univ_five, mul_add, add_mul, mul_one, add_assoc]

theorem Q31_isOrtho_basis (i j : Fin 4) (hij : i ≠ j) :
    Q31.IsOrtho (e4vec i) (e4vec j) := by
  rw [QuadraticMap.isOrtho_def]
  simp only [Q31, QuadraticMap.weightedSumSquares_apply, e4vec, w31]
  fin_cases i <;> fin_cases j <;>
    first
    | exact absurd rfl hij
    | simp [Pi.single, Fin.sum_univ_four, mul_add, add_mul, mul_one, add_assoc]

/-- Minkowski inner product on translation parameters. -/
def minkowskiDot (lam : Fin 4 → ℝ) : ℝ :=
  -lam 0 * lam 0 + lam 1 * lam 1 + lam 2 * lam 2 + lam 3 * lam 3

end DstDiophantine
