import DstDiophantine.Algebra.CGA.QuadraticForm
import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

/-!
# Null pair and algebra API for 1D CGA

Null infinity / origin as grade-1 vectors in Cl(2,1):

Inf = e₋ - e₊, 
0 = (e₋ + e₊) / 2.
Squares are proved via Q21 on the underlying vectors.
-/

namespace DstDiophantine

namespace CGA

open CliffordAlgebra

/-- 1D conformal geometric algebra Cl(2,1). -/
abbrev CGA1 := CliffordAlgebra Q21

namespace CGA1

/-- Index of e₋ (Q = -1). -/
def eMinusIndex : Fin 3 := 0

/-- Index of the Euclidean line basis e (Q = +1). -/
def eIndex : Fin 3 := 1

/-- Index of e₊ (Q = +1). -/
def ePlusIndex : Fin 3 := 2

noncomputable def ι (μ : Fin 3) : CGA1 :=
  CliffordAlgebra.ι Q21 (e3vec μ)

theorem e_sq (μ : Fin 3) : ι μ * ι μ = algebraMap ℝ CGA1 (Q21 (e3vec μ)) :=
  ι_sq_scalar (Q := Q21) (e3vec μ)

theorem eMinus_sq : ι eMinusIndex * ι eMinusIndex = algebraMap ℝ CGA1 (-1 : ℝ) := by
  simp [e_sq, Q21_e3vec, w21, eMinusIndex]

theorem e_sq_one : ι eIndex * ι eIndex = (1 : CGA1) := by
  simp [e_sq, Q21_e3vec, w21, eIndex]

theorem ePlus_sq : ι ePlusIndex * ι ePlusIndex = (1 : CGA1) := by
  simp [e_sq, Q21_e3vec, w21, ePlusIndex]

theorem e_anticomm {i j : Fin 3} (hij : i ≠ j) :
    ι i * ι j + ι j * ι i = 0 :=
  ι_mul_ι_add_swap_of_isOrtho (Q := Q21) (Q21_isOrtho_basis i j hij)

/-- Euclidean line generator (grade 1). -/
noncomputable def eLine : CGA1 := ι eIndex

/-- Underlying vector for null infinity: (1, 0, -1). -/
def nInfVec : Vec3
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => 0
  | ⟨2, _⟩ => -1

/-- Underlying vector for null origin: (1/2, 0, 1/2). -/
noncomputable def n0Vec : Vec3
  | ⟨0, _⟩ => 1 / 2
  | ⟨1, _⟩ => 0
  | ⟨2, _⟩ => 1 / 2

/-- Euclidean line vector: (0, 1, 0). -/
def eLineVec : Vec3
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => 1
  | ⟨2, _⟩ => 0

theorem Q21_nInfVec : Q21 nInfVec = 0 := by
  simp only [Q21, QuadraticMap.weightedSumSquares_apply, nInfVec, w21]
  rw [Fin.sum_univ_three]
  norm_num

theorem Q21_n0Vec : Q21 n0Vec = 0 := by
  simp only [Q21, QuadraticMap.weightedSumSquares_apply, n0Vec, w21]
  rw [Fin.sum_univ_three]
  norm_num

/-- Null infinity 
∞. -/
noncomputable def nInf : CGA1 :=
  CliffordAlgebra.ι Q21 nInfVec

/-- Null origin 
₀. -/
noncomputable def n0 : CGA1 :=
  CliffordAlgebra.ι Q21 n0Vec

theorem nInf_sq : nInf * nInf = 0 := by
  unfold nInf
  rw [ι_sq_scalar (Q := Q21) nInfVec, Q21_nInfVec, map_zero]

theorem n0_sq : n0 * n0 = 0 := by
  unfold n0
  rw [ι_sq_scalar (Q := Q21) n0Vec, Q21_n0Vec, map_zero]

/--
Conformal point vector on the null cone:
X(x) = n₀ + x e + (1/2) x² n∞ as a grade-1 element of Cl(2,1).
-/
noncomputable def pointVec (x : ℝ) : Vec3 :=
  fun i =>
    match i with
    | ⟨0, _⟩ => 1 / 2 + (1 / 2) * x ^ 2
    | ⟨1, _⟩ => x
    | ⟨2, _⟩ => 1 / 2 - (1 / 2) * x ^ 2

theorem pointVec_eq (x : ℝ) :
    pointVec x = n0Vec + x • eLineVec + ((1 / 2) * x ^ 2) • nInfVec := by
  funext i
  fin_cases i
  · simp [pointVec, n0Vec, eLineVec, nInfVec, Pi.add_apply, Pi.smul_apply]; try ring
  · simp [pointVec, n0Vec, eLineVec, nInfVec, Pi.add_apply, Pi.smul_apply]
  · simp [pointVec, n0Vec, eLineVec, nInfVec, Pi.add_apply, Pi.smul_apply]; try ring

theorem Q21_pointVec (x : ℝ) : Q21 (pointVec x) = 0 := by
  simp only [Q21, QuadraticMap.weightedSumSquares_apply, pointVec, w21]
  rw [Fin.sum_univ_three]
  ring

/-- Grade-1 conformal point embedding. -/
noncomputable def point (x : ℝ) : CGA1 :=
  CliffordAlgebra.ι Q21 (pointVec x)

theorem point_sq (x : ℝ) : point x * point x = 0 := by
  unfold point
  rw [ι_sq_scalar (Q := Q21) (pointVec x), Q21_pointVec x, map_zero]

/-- Algebraic dilation on the null cone: weights (1, c, c²). -/
theorem pointVec_smul_weights (c x : ℝ) :
    pointVec (c * x) =
      n0Vec + c • (x • eLineVec) + (c ^ 2) • ((1 / 2 * x ^ 2) • nInfVec) := by
  funext i
  fin_cases i
  · simp [pointVec, n0Vec, eLineVec, nInfVec, Pi.add_apply, Pi.smul_apply, smul_smul]; try ring
  · simp [pointVec, n0Vec, eLineVec, nInfVec, Pi.add_apply, Pi.smul_apply, smul_smul]; try ring
  · simp [pointVec, n0Vec, eLineVec, nInfVec, Pi.add_apply, Pi.smul_apply, smul_smul]; try ring

/-- Integer multiplication as a dilation of the conformal point. -/
theorem pointVec_mul (m n : ℤ) :
    pointVec ((m * n : ℤ) : ℝ) =
      n0Vec + ((m : ℝ) * (n : ℝ)) • eLineVec
        + (1 / 2 * ((m : ℝ) * (n : ℝ)) ^ 2) • nInfVec := by
  rw [Int.cast_mul, pointVec_eq]

theorem point_mul (m n : ℤ) :
    point ((m * n : ℤ) : ℝ) =
      CliffordAlgebra.ι Q21
        (n0Vec + ((m : ℝ) * (n : ℝ)) • eLineVec
          + (1 / 2 * ((m : ℝ) * (n : ℝ)) ^ 2) • nInfVec) := by
  unfold point
  rw [pointVec_mul]

end CGA1

end CGA

end DstDiophantine
