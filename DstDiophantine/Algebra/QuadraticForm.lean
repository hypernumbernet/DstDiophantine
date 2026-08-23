import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Quadratic forms for Cl(3,1), G(3,1,1), and Cl(9,1)

Signature `(3,1)` on four dimensions, `(3,1,1)` on five dimensions with a null
direction `e₄` (`Q(e₄) = 0`), and textbook Minkowski `(9,1)` on ten dimensions
for the superstring comparison layer.
-/

namespace DstDiophantine

abbrev Vec4 := Fin 4 → ℝ
abbrev Vec5 := Fin 5 → ℝ
abbrev Vec10 := Fin 10 → ℝ

/-- Weights for the Minkowski signature `(-,+,+,+)` on `Fin 4`. -/
def w31 : Fin 4 → ℝ
  | 0 => -1
  | 1 | 2 | 3 => 1

/-- Weights for `G(3,1,1)`: Minkowski on `e₀…e₃` and null `e₄`. -/
def w311 : Fin 5 → ℝ
  | 0 => -1
  | 1 | 2 | 3 => 1
  | 4 => 0

/-- Weights for textbook `Cl(9,1)`: `(-,+,+,+,+,+,+,+,+,+)`. -/
def w91 : Fin 10 → ℝ
  | 0 => -1
  | _ => 1

/-- Quadratic form for `Cl(3,1)`. -/
noncomputable def Q31 : QuadraticForm ℝ Vec4 :=
  QuadraticMap.weightedSumSquares ℝ w31

/-- Quadratic form for `G(3,1,1) = Cl(3,1,1)`. -/
noncomputable def Q311 : QuadraticForm ℝ Vec5 :=
  QuadraticMap.weightedSumSquares ℝ w311

/-- Quadratic form for textbook `Cl(9,1)`. -/
noncomputable def Q91 : QuadraticForm ℝ Vec10 :=
  QuadraticMap.weightedSumSquares ℝ w91

/-- Standard basis vector in `Fin 4 → ℝ`. -/
def e4vec (μ : Fin 4) : Vec4 :=
  Pi.single μ 1

/-- Standard basis vector in `Fin 5 → ℝ`. -/
def e5vec (μ : Fin 5) : Vec5 :=
  Pi.single μ 1

/-- Standard basis vector in `Fin 10 → ℝ`. -/
def e10vec (μ : Fin 10) : Vec10 :=
  Pi.single μ 1

/-- Distinct standard basis vectors are orthogonal for any weight function. -/
theorem weightedSumSquares_isOrtho_single {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ι → ℝ) {i j : ι} (hij : i ≠ j) :
    (QuadraticMap.weightedSumSquares ℝ w).IsOrtho (Pi.single i (1 : ℝ)) (Pi.single j (1 : ℝ)) := by
  set ei : ι → ℝ := Pi.single i 1
  set ej : ι → ℝ := Pi.single j 1
  have hQi : QuadraticMap.weightedSumSquares ℝ w ei = w i := by
    simp only [QuadraticMap.weightedSumSquares_apply, ei, smul_eq_mul]
    rw [Fintype.sum_eq_single i]
    · simp [Pi.single_eq_same]
    · intro k hk; simp [Pi.single_eq_of_ne hk]
  have hQj : QuadraticMap.weightedSumSquares ℝ w ej = w j := by
    simp only [QuadraticMap.weightedSumSquares_apply, ej, smul_eq_mul]
    rw [Fintype.sum_eq_single j]
    · simp [Pi.single_eq_same]
    · intro k hk; simp [Pi.single_eq_of_ne hk]
  have hQij : QuadraticMap.weightedSumSquares ℝ w (ei + ej) = w i + w j := by
    simp only [QuadraticMap.weightedSumSquares_apply, ei, ej, Pi.add_apply, smul_eq_mul]
    rw [← Finset.sum_subset (s₁ := ({i, j} : Finset ι)) (Finset.subset_univ _)]
    · simp [Finset.sum_pair hij, Pi.single_eq_same,
        Pi.single_eq_of_ne hij, Pi.single_eq_of_ne hij.symm]
    · intro k _ hk
      have hk' : k ≠ i ∧ k ≠ j := by simpa [Finset.mem_insert, Finset.mem_singleton] using hk
      simp [Pi.single_eq_of_ne hk'.1, Pi.single_eq_of_ne hk'.2]
  rw [QuadraticMap.isOrtho_def, hQij, hQi, hQj]

/-- Embed `Fin 4 → ℝ` into the first four components of `Fin 5 → ℝ`. -/
def extend4 (v : Vec4) : Vec5 :=
  fun i =>
    match i with
    | ⟨0, _⟩ => v 0
    | ⟨1, _⟩ => v 1
    | ⟨2, _⟩ => v 2
    | ⟨3, _⟩ => v 3
    | ⟨4, _⟩ => 0

/-- Embed `Fin 4 → ℝ` into the first four components of `Fin 10 → ℝ`. -/
def extend4to10 (v : Vec4) : Vec10
  | ⟨0, _⟩ => v 0
  | ⟨1, _⟩ => v 1
  | ⟨2, _⟩ => v 2
  | ⟨3, _⟩ => v 3
  | ⟨4, _⟩ | ⟨5, _⟩ | ⟨6, _⟩ | ⟨7, _⟩ | ⟨8, _⟩ | ⟨9, _⟩ => 0

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

@[simp] theorem extend4to10_apply (v : Vec4) (μ : Fin 4) :
    extend4to10 v (Fin.castAdd 6 μ) = v μ := by
  fin_cases μ <;> simp [extend4to10]

@[simp] theorem extend4to10_e4vec (μ : Fin 4) :
    extend4to10 (e4vec μ) = e10vec (Fin.castAdd 6 μ) := by
  funext i
  fin_cases μ <;> fin_cases i <;> simp [extend4to10, e4vec, e10vec, Pi.single]

theorem Q311_extend4 (v : Vec4) : Q311 (extend4 v) = Q31 v := by
  simp only [Q311, Q31, QuadraticMap.weightedSumSquares_apply, w311, w31, extend4]
  rw [Fin.sum_univ_five, Fin.sum_univ_four]
  simp

private theorem extend4to10_of_ge_four (v : Vec4) (k : Fin 10) (hk : 4 ≤ (k : ℕ)) :
    extend4to10 v k = 0 := by
  have : k.val = 4 ∨ k.val = 5 ∨ k.val = 6 ∨ k.val = 7 ∨ k.val = 8 ∨ k.val = 9 := by
    omega
  rcases this with h | h | h | h | h | h
  · have : k = 4 := Fin.ext h; subst this; rfl
  · have : k = 5 := Fin.ext h; subst this; rfl
  · have : k = 6 := Fin.ext h; subst this; rfl
  · have : k = 7 := Fin.ext h; subst this; rfl
  · have : k = 8 := Fin.ext h; subst this; rfl
  · have : k = 9 := Fin.ext h; subst this; rfl

theorem Q91_extend4to10 (v : Vec4) : Q91 (extend4to10 v) = Q31 v := by
  simp only [Q91, Q31, QuadraticMap.weightedSumSquares_apply, smul_eq_mul]
  have hR : (∑ μ : Fin 4, w31 μ * (v μ * v μ)) =
      -(v 0 * v 0) + v 1 * v 1 + v 2 * v 2 + v 3 * v 3 := by
    simp [Fin.sum_univ_four, w31]
  have hL : (∑ i : Fin 10, w91 i * (extend4to10 v i * extend4to10 v i)) =
      -(v 0 * v 0) + v 1 * v 1 + v 2 * v 2 + v 3 * v 3 := by
    rw [← Finset.sum_subset (s₁ := ({(0 : Fin 10), 1, 2, 3} : Finset (Fin 10)))
      (Finset.subset_univ _)]
    · simp [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, extend4to10, w91]
      ring
    · intro i _ hi
      have hi4 : 4 ≤ (i : ℕ) := by
        fin_cases i <;> simp_all [Finset.mem_insert, Finset.mem_singleton]
      simp [extend4to10_of_ge_four v i hi4]
  rw [hL, hR]

theorem Q91_e10vec (μ : Fin 10) : Q91 (e10vec μ) = w91 μ := by
  simp only [Q91, QuadraticMap.weightedSumSquares_apply, e10vec, smul_eq_mul]
  rw [Fintype.sum_eq_single μ]
  · simp [Pi.single_eq_same]
  · intro k hk; simp [Pi.single_eq_of_ne hk]

theorem Q311_e5vec (μ : Fin 5) : Q311 (e5vec μ) = w311 μ := by
  simp only [Q311, QuadraticMap.weightedSumSquares_apply, e5vec, w311]
  fin_cases μ <;> simp [Pi.single, Fin.sum_univ_five]

theorem Q31_e4vec (μ : Fin 4) : Q31 (e4vec μ) = w31 μ := by
  simp only [Q31, QuadraticMap.weightedSumSquares_apply, e4vec, w31]
  fin_cases μ <;> simp [Pi.single, Fin.sum_univ_four]

theorem Q311_isOrtho_basis (i j : Fin 5) (hij : i ≠ j) :
    Q311.IsOrtho (e5vec i) (e5vec j) :=
  weightedSumSquares_isOrtho_single w311 hij

theorem Q31_isOrtho_basis (i j : Fin 4) (hij : i ≠ j) :
    Q31.IsOrtho (e4vec i) (e4vec j) :=
  weightedSumSquares_isOrtho_single w31 hij

theorem Q91_isOrtho_basis (i j : Fin 10) (hij : i ≠ j) :
    Q91.IsOrtho (e10vec i) (e10vec j) :=
  weightedSumSquares_isOrtho_single w91 hij

/-- Minkowski inner product on translation parameters. -/
def minkowskiDot (lam : Fin 4 → ℝ) : ℝ :=
  -lam 0 * lam 0 + lam 1 * lam 1 + lam 2 * lam 2 + lam 3 * lam 3

end DstDiophantine
