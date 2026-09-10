import DstDiophantine.Logic.Quantum.Spinor
import DstDiophantine.Logic.Quantum.Dirac
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Dirac spinor \(\mathbb{C}^4\) as a matrix representation of \(\mathrm{Cl}(3,1)\)

Signature \((-,+,+,+)\). The four gamma matrices act on `DiracSpinor ≃ ℂ⁴`.
This is a representation of the Clifford relations already proved in
`Logic.Quantum.Dirac`; it is **not** the dual-sector Hilbert space
`DualSpinor ≃ ℂ²`, and it is not a Dirac equation.
-/

namespace DstDiophantine

namespace Logic

open Matrix Complex

/-- Dirac spinor: the representation space \(\mathbb{C}^4\). -/
abbrev DiracSpinor := EuclideanSpace ℂ (Fin 4)

/-- Weyl block form of \(\gamma^0\): \(\begin{pmatrix}0&I\\-I&0\end{pmatrix}\). -/
def diracMat0 : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0, 0, 1, 0;
     0, 0, 0, 1;
     -1, 0, 0, 0;
     0, -1, 0, 0]

/-- Weyl block form of \(\gamma^1\): \(\begin{pmatrix}0&\sigma_x\\\sigma_x&0\end{pmatrix}\). -/
def diracMat1 : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0, 0, 0, 1;
     0, 0, 1, 0;
     0, 1, 0, 0;
     1, 0, 0, 0]

/-- Weyl block form of \(\gamma^2\): \(\begin{pmatrix}0&\sigma_y\\\sigma_y&0\end{pmatrix}\). -/
def diracMat2 : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0, 0, 0, -I;
     0, 0, I, 0;
     0, -I, 0, 0;
     I, 0, 0, 0]

/-- Weyl block form of \(\gamma^3\): \(\begin{pmatrix}0&\sigma_z\\\sigma_z&0\end{pmatrix}\). -/
def diracMat3 : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0, 0, 1, 0;
     0, 0, 0, -1;
     1, 0, 0, 0;
     0, -1, 0, 0]

/-- Dirac matrices \(\gamma^\mu\in M_4(\mathbb{C})\). -/
def diracMat : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ
  | 0 => diracMat0
  | 1 => diracMat1
  | 2 => diracMat2
  | 3 => diracMat3

theorem diracMat0_sq : diracMat0 * diracMat0 = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diracMat0, Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply, Matrix.neg_apply]

theorem diracMat1_sq : diracMat1 * diracMat1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diracMat1, Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply]

theorem diracMat2_sq : diracMat2 * diracMat2 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diracMat2, Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply, I_mul_I]

theorem diracMat3_sq : diracMat3 * diracMat3 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diracMat3, Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply]

theorem diracMat0_anticomm_1 : diracMat0 * diracMat1 + diracMat1 * diracMat0 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diracMat0, diracMat1, Matrix.mul_apply, Matrix.add_apply, Fin.sum_univ_four]

theorem diracMat0_anticomm_2 : diracMat0 * diracMat2 + diracMat2 * diracMat0 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diracMat0, diracMat2, Matrix.mul_apply, Matrix.add_apply, Fin.sum_univ_four]

theorem diracMat0_anticomm_3 : diracMat0 * diracMat3 + diracMat3 * diracMat0 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diracMat0, diracMat3, Matrix.mul_apply, Matrix.add_apply, Fin.sum_univ_four]

theorem diracMat1_anticomm_2 : diracMat1 * diracMat2 + diracMat2 * diracMat1 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diracMat1, diracMat2, Matrix.mul_apply, Matrix.add_apply, Fin.sum_univ_four]

theorem diracMat1_anticomm_3 : diracMat1 * diracMat3 + diracMat3 * diracMat1 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diracMat1, diracMat3, Matrix.mul_apply, Matrix.add_apply, Fin.sum_univ_four]

theorem diracMat2_anticomm_3 : diracMat2 * diracMat3 + diracMat3 * diracMat2 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diracMat2, diracMat3, Matrix.mul_apply, Matrix.add_apply, Fin.sum_univ_four]

private theorem diag_two_neg_one :
    diracMat0 * diracMat0 + diracMat0 * diracMat0 =
      (2 * minkowskiEta 0 0 : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  simp [minkowskiEta, w31, diracMat0_sq]
  ext i j
  simp [Matrix.add_apply, Matrix.neg_apply, Matrix.smul_apply, Matrix.one_apply]
  split_ifs <;> ring

private theorem diag_two_one (A : Matrix (Fin 4) (Fin 4) ℂ) (h : A * A = 1) {μ : Fin 4}
    (hμ : minkowskiEta μ μ = 1) :
    A * A + A * A = (2 * minkowskiEta μ μ : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  rw [h, hμ]
  ext i j
  simp [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply]
  split_ifs <;> ring

/-- Matrix Clifford relation \(\{\gamma^\mu,\gamma^\nu\}=2\eta^{\mu\nu}I\). -/
theorem diracMat_clifford (μ ν : Fin 4) :
    diracMat μ * diracMat ν + diracMat ν * diracMat μ =
      (2 * minkowskiEta μ ν : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  fin_cases μ <;> fin_cases ν
  · simpa [diracMat] using diag_two_neg_one
  · simpa [diracMat, minkowskiEta] using diracMat0_anticomm_1
  · simpa [diracMat, minkowskiEta] using diracMat0_anticomm_2
  · simpa [diracMat, minkowskiEta] using diracMat0_anticomm_3
  · simpa [diracMat, minkowskiEta, add_comm] using diracMat0_anticomm_1
  · simpa [diracMat] using
      diag_two_one diracMat1 diracMat1_sq (μ := 1) (by simp [minkowskiEta, w31])
  · simpa [diracMat, minkowskiEta] using diracMat1_anticomm_2
  · simpa [diracMat, minkowskiEta] using diracMat1_anticomm_3
  · simpa [diracMat, minkowskiEta, add_comm] using diracMat0_anticomm_2
  · simpa [diracMat, minkowskiEta, add_comm] using diracMat1_anticomm_2
  · simpa [diracMat] using
      diag_two_one diracMat2 diracMat2_sq (μ := 2) (by simp [minkowskiEta, w31])
  · simpa [diracMat, minkowskiEta] using diracMat2_anticomm_3
  · simpa [diracMat, minkowskiEta, add_comm] using diracMat0_anticomm_3
  · simpa [diracMat, minkowskiEta, add_comm] using diracMat1_anticomm_3
  · simpa [diracMat, minkowskiEta, add_comm] using diracMat2_anticomm_3
  · simpa [diracMat] using
      diag_two_one diracMat3 diracMat3_sq (μ := 3) (by simp [minkowskiEta, w31])

theorem diracSpinor_finrank : Module.finrank ℂ DiracSpinor = 4 := by
  simp

theorem dualSpinor_ne_diracSpinor :
    Module.finrank ℂ DualSpinor ≠ Module.finrank ℂ DiracSpinor := by
  rw [dualSpinor_finrank, diracSpinor_finrank]
  norm_num

/-- Chiral (Weyl) embedding of a dual spinor as the upper \(\mathbb{C}^2\) block. -/
def weylUpper (ψ : DualSpinor) : DiracSpinor :=
  WithLp.toLp 2 ![WithLp.ofLp ψ 0, WithLp.ofLp ψ 1, 0, 0]

/-- Lower Weyl block. -/
def weylLower (ψ : DualSpinor) : DiracSpinor :=
  WithLp.toLp 2 ![0, 0, WithLp.ofLp ψ 0, WithLp.ofLp ψ 1]

theorem weylUpper_injective : Function.Injective weylUpper := by
  intro ψ φ h
  have hvec := WithLp.toLp_injective (p := 2) h
  ext i
  fin_cases i
  · simpa [weylUpper] using congrFun hvec 0
  · simpa [weylUpper] using congrFun hvec 1

/-- The two Weyl embeddings land in complementary coordinate subspaces. -/
theorem weylUpper_add_lower (ψ φ : DualSpinor) :
    weylUpper ψ + weylLower φ =
      WithLp.toLp 2 ![WithLp.ofLp ψ 0, WithLp.ofLp ψ 1,
        WithLp.ofLp φ 0, WithLp.ofLp φ 1] := by
  ext i
  fin_cases i <;> simp [weylUpper, weylLower, PiLp.add_apply]

end Logic

end DstDiophantine
