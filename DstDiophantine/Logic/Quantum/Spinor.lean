/-
Copyright (c) 2026 DstDiophantine contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DstDiophantine contributors
-/
import DstDiophantine.Logic.Quantum.Quaternion
import DstDiophantine.Logic.Quantum.DualSector
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Complex.Basic


/-!
# Dual-sector spinor Hilbert space `ℂ²`

The cyclic generators are represented by `-i σ_a`. This sign is chosen so that
`I J = K` matches `cyclic_zero_mul_one` and the standard rotation is
`exp(-i/2 β · σ)`. The paper draft `I ↔ i σ` differs by a global sign of `i`;
Lean is authoritative.

This Hilbert space is D4L's dual-sector kinematics. It is not the space
of scalar-layer propositions `{T,U,F,B}`.
-/

namespace DstDiophantine

namespace Logic

open Matrix Complex

/-- Dual-sector spinor: the Hilbert space `ℂ²`. -/
abbrev DualSpinor := EuclideanSpace ℂ (Fin 2)

/-- Pauli `σ_x`. -/
def pauliX : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, 1; 1, 0]

/-- Pauli `σ_y`. -/
def pauliY : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, -I; I, 0]

/-- Pauli `σ_z`. -/
def pauliZ : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, 0; 0, -1]

def pauli : Fin 3 → Matrix (Fin 2) (Fin 2) ℂ
  | 0 => pauliX
  | 1 => pauliY
  | 2 => pauliZ

/-- Representation of a cyclic generator: `cyclic a ↦ -i σ_a`. -/
def cyclicRep (a : Fin 3) : Matrix (Fin 2) (Fin 2) ℂ :=
  -I • pauli a

@[simp] theorem pauliX_apply_00 : pauliX 0 0 = 0 := rfl
@[simp] theorem pauliX_apply_01 : pauliX 0 1 = 1 := rfl
@[simp] theorem pauliX_apply_10 : pauliX 1 0 = 1 := rfl
@[simp] theorem pauliX_apply_11 : pauliX 1 1 = 0 := rfl

private theorem matrix_two_eq
    (A B : Matrix (Fin 2) (Fin 2) ℂ)
    (h00 : A 0 0 = B 0 0) (h01 : A 0 1 = B 0 1)
    (h10 : A 1 0 = B 1 0) (h11 : A 1 1 = B 1 1) : A = B := by
  ext i j
  fin_cases i <;> fin_cases j <;> assumption

theorem pauliX_sq : pauliX * pauliX = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliX, Matrix.mul_apply, Fin.sum_univ_two]

theorem pauliY_sq : pauliY * pauliY = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliY, Matrix.mul_apply, Fin.sum_univ_two, I_mul_I]

theorem pauliZ_sq : pauliZ * pauliZ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliZ, Matrix.mul_apply, Fin.sum_univ_two]

theorem pauli_sq (a : Fin 3) : pauli a * pauli a = 1 := by
  fin_cases a
  · exact pauliX_sq
  · exact pauliY_sq
  · exact pauliZ_sq

theorem cyclicRep_sq (a : Fin 3) : cyclicRep a * cyclicRep a = -1 := by
  unfold cyclicRep
  -- (-I • σ) * (-I • σ) = (I * I) • (σ * σ) = (-1) • 1 = -1
  have hI : (-I) * (-I) = (-1 : ℂ) := by
    simp [neg_mul, mul_neg, I_mul_I]
  calc (-I) • pauli a * ((-I) • pauli a)
      = ((-I) * (-I)) • (pauli a * pauli a) := by
        simp [smul_smul]
    _ = (-1 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by rw [hI, pauli_sq]
    _ = -1 := by simp

theorem pauliX_mul_pauliY : pauliX * pauliY = I • pauliZ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliX, pauliY, pauliZ, Matrix.mul_apply, Fin.sum_univ_two]

theorem cyclicRep_zero_mul_one : cyclicRep 0 * cyclicRep 1 = cyclicRep 2 := by
  unfold cyclicRep pauli
  have hσ : pauliX * pauliY = I • pauliZ := pauliX_mul_pauliY
  calc (-I) • pauliX * ((-I) • pauliY)
      = ((-I) * (-I)) • (pauliX * pauliY) := by
        simp [smul_smul]
    _ = (-1 : ℂ) • (I • pauliZ) := by
        have : (-I) * (-I) = (-1 : ℂ) := by simp [neg_mul, mul_neg, I_mul_I]
        rw [this, hσ]
    _ = (-I) • pauliZ := by
        simp [smul_smul]

/-- Apply a `2×2` matrix to a dual spinor. -/
def applyMat (M : Matrix (Fin 2) (Fin 2) ℂ) (ψ : DualSpinor) : DualSpinor :=
  WithLp.toLp 2 (M *ᵥ WithLp.ofLp ψ)

/-- Dual rotor as a matrix: `exp(Σ (β_a/2) (-i σ_a)) = exp(-i/2 β·σ)`. -/
noncomputable def dualRotorMat (β : DualRapidity) : Matrix (Fin 2) (Fin 2) ℂ :=
  NormedSpace.exp (∑ a : Fin 3, (β a / 2 : ℂ) • cyclicRep a)

/-- One-axis generator: the matrix logarithm of a pure dual rotation about axis `0`. -/
noncomputable def axis0Gen (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (θ / 2 : ℂ) • cyclicRep 0

theorem dualRotorMat_axis0 (θ : ℝ) :
    dualRotorMat (EuclideanSpace.single 0 θ) = NormedSpace.exp (axis0Gen θ) := by
  unfold dualRotorMat axis0Gen
  congr 1
  simp [PiLp.single_apply, Fin.sum_univ_three]

/-- Pauli matrices are Hermitian. -/
theorem pauliX_isHermitian : pauliX.IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliX, Matrix.conjTranspose_apply]

theorem pauliY_isHermitian : pauliY.IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliY, Matrix.conjTranspose_apply, conj_I]

theorem pauliZ_isHermitian : pauliZ.IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliZ, Matrix.conjTranspose_apply]

theorem cyclicRep_conjTranspose (a : Fin 3) :
    (cyclicRep a).conjTranspose = -cyclicRep a := by
  unfold cyclicRep
  have hσ : (pauli a).conjTranspose = pauli a := by
    fin_cases a
    · exact pauliX_isHermitian
    · exact pauliY_isHermitian
    · exact pauliZ_isHermitian
  have hstar : star (-I : ℂ) = I := by
    simp [conj_I]
  calc ((-I : ℂ) • pauli a).conjTranspose
      = star (-I) • (pauli a).conjTranspose := by
        simp [Matrix.conjTranspose_smul]
    _ = I • pauli a := by rw [hstar, hσ]
    _ = -((-I) • pauli a) := by simp [neg_smul]

/-- A projective measurement on `DualSpinor` has at most two orthogonal outcomes. -/
theorem dualSpinor_finrank : Module.finrank ℂ DualSpinor = 2 := by
  simp

end Logic

end DstDiophantine
