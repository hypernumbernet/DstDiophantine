import DstDiophantine.Logic.Quantum.Spinor
import DstDiophantine.Logic.Quantum.Dirac
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

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
    simp [diracMat0, Matrix.mul_apply, Fin.sum_univ_four, Matrix.neg_apply]

theorem diracMat1_sq : diracMat1 * diracMat1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diracMat1, Matrix.mul_apply, Fin.sum_univ_four]

theorem diracMat2_sq : diracMat2 * diracMat2 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diracMat2, Matrix.mul_apply, Fin.sum_univ_four, I_mul_I]

theorem diracMat3_sq : diracMat3 * diracMat3 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diracMat3, Matrix.mul_apply, Fin.sum_univ_four]

theorem diracMat0_anticomm_1 : diracMat0 * diracMat1 + diracMat1 * diracMat0 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diracMat0, diracMat1, Matrix.add_apply]

theorem diracMat0_anticomm_2 : diracMat0 * diracMat2 + diracMat2 * diracMat0 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diracMat0, diracMat2, Matrix.add_apply]

theorem diracMat0_anticomm_3 : diracMat0 * diracMat3 + diracMat3 * diracMat0 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diracMat0, diracMat3, Matrix.add_apply]

theorem diracMat1_anticomm_2 : diracMat1 * diracMat2 + diracMat2 * diracMat1 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diracMat1, diracMat2, Matrix.add_apply]

theorem diracMat1_anticomm_3 : diracMat1 * diracMat3 + diracMat3 * diracMat1 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diracMat1, diracMat3, Matrix.add_apply]

theorem diracMat2_anticomm_3 : diracMat2 * diracMat3 + diracMat3 * diracMat2 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diracMat2, diracMat3, Matrix.add_apply]

private theorem diag_two_neg_one :
    diracMat0 * diracMat0 + diracMat0 * diracMat0 =
      (2 * minkowskiEta 0 0 : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  rw [diracMat0_sq, minkowskiEta_diag, show w31 0 = -1 from rfl]
  ext i j
  simp only [Matrix.add_apply, Matrix.neg_apply, Matrix.smul_apply, Matrix.one_apply]
  split_ifs <;> push_cast <;> ring

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

theorem weylLower_injective : Function.Injective weylLower := by
  intro ψ φ h
  have hvec := WithLp.toLp_injective (p := 2) h
  ext i
  fin_cases i
  · simpa [weylLower] using congrFun hvec 2
  · simpa [weylLower] using congrFun hvec 3

/-- The two Weyl embeddings land in complementary coordinate subspaces. -/
theorem weylUpper_add_lower (ψ φ : DualSpinor) :
    weylUpper ψ + weylLower φ =
      WithLp.toLp 2 ![WithLp.ofLp ψ 0, WithLp.ofLp ψ 1,
        WithLp.ofLp φ 0, WithLp.ofLp φ 1] := by
  ext i
  fin_cases i <;> simp [weylUpper, weylLower, PiLp.add_apply]

/-- Upper Weyl block of a Dirac spinor. -/
def diracUpper (Ψ : DiracSpinor) : DualSpinor :=
  WithLp.toLp 2 ![WithLp.ofLp Ψ 0, WithLp.ofLp Ψ 1]

/-- Lower Weyl block of a Dirac spinor. -/
def diracLower (Ψ : DiracSpinor) : DualSpinor :=
  WithLp.toLp 2 ![WithLp.ofLp Ψ 2, WithLp.ofLp Ψ 3]

/-- Every Dirac spinor is the sum of its upper and lower Weyl blocks. -/
theorem weyl_decompose (Ψ : DiracSpinor) :
    weylUpper (diracUpper Ψ) + weylLower (diracLower Ψ) = Ψ := by
  rw [weylUpper_add_lower]
  ext i
  fin_cases i <;> simp [diracUpper, diracLower]

theorem diracUpper_weylUpper (u : DualSpinor) : diracUpper (weylUpper u) = u := by
  ext i
  fin_cases i <;> simp [diracUpper, weylUpper]

theorem diracLower_weylLower (l : DualSpinor) : diracLower (weylLower l) = l := by
  ext i
  fin_cases i <;> simp [diracLower, weylLower]

theorem diracUpper_weylLower (l : DualSpinor) : diracUpper (weylLower l) = 0 := by
  ext i
  fin_cases i <;> simp [diracUpper, weylLower]

theorem diracLower_weylUpper (u : DualSpinor) : diracLower (weylUpper u) = 0 := by
  ext i
  fin_cases i <;> simp [diracLower, weylUpper]

theorem diracUpper_add (Ψ Φ : DiracSpinor) :
    diracUpper (Ψ + Φ) = diracUpper Ψ + diracUpper Φ := by
  ext i
  fin_cases i <;> simp [diracUpper]

theorem diracLower_add (Ψ Φ : DiracSpinor) :
    diracLower (Ψ + Φ) = diracLower Ψ + diracLower Φ := by
  ext i
  fin_cases i <;> simp [diracLower]

theorem diracUpper_sub (Ψ Φ : DiracSpinor) :
    diracUpper (Ψ - Φ) = diracUpper Ψ - diracUpper Φ := by
  ext i
  fin_cases i <;> simp [diracUpper]

theorem diracLower_sub (Ψ Φ : DiracSpinor) :
    diracLower (Ψ - Φ) = diracLower Ψ - diracLower Φ := by
  ext i
  fin_cases i <;> simp [diracLower]

theorem diracUpper_smul (c : ℂ) (Ψ : DiracSpinor) :
    diracUpper (c • Ψ) = c • diracUpper Ψ := by
  ext i
  fin_cases i <;> simp [diracUpper]

theorem diracLower_smul (c : ℂ) (Ψ : DiracSpinor) :
    diracLower (c • Ψ) = c • diracLower Ψ := by
  ext i
  fin_cases i <;> simp [diracLower]

theorem diracUpper_finset_sum {ι : Type*} (s : Finset ι) (f : ι → DiracSpinor) :
    diracUpper (∑ i ∈ s, f i) = ∑ i ∈ s, diracUpper (f i) := by
  induction s using Finset.cons_induction with
  | empty =>
    ext j
    fin_cases j <;> simp [diracUpper]
  | cons a s ha ih =>
    rw [Finset.sum_cons, Finset.sum_cons, diracUpper_add, ih]

theorem diracLower_finset_sum {ι : Type*} (s : Finset ι) (f : ι → DiracSpinor) :
    diracLower (∑ i ∈ s, f i) = ∑ i ∈ s, diracLower (f i) := by
  induction s using Finset.cons_induction with
  | empty =>
    ext j
    fin_cases j <;> simp [diracLower]
  | cons a s ha ih =>
    rw [Finset.sum_cons, Finset.sum_cons, diracLower_add, ih]

theorem weylUpper_add (ψ φ : DualSpinor) :
    weylUpper (ψ + φ) = weylUpper ψ + weylUpper φ := by
  ext i; fin_cases i <;> simp [weylUpper]

theorem weylLower_add (ψ φ : DualSpinor) :
    weylLower (ψ + φ) = weylLower ψ + weylLower φ := by
  ext i; fin_cases i <;> simp [weylLower]

theorem weylUpper_smul (c : ℂ) (ψ : DualSpinor) :
    weylUpper (c • ψ) = c • weylUpper ψ := by
  ext i; fin_cases i <;> simp [weylUpper]

theorem weylLower_smul (c : ℂ) (ψ : DualSpinor) :
    weylLower (c • ψ) = c • weylLower ψ := by
  ext i; fin_cases i <;> simp [weylLower]

theorem weylUpper_neg (ψ : DualSpinor) : weylUpper (-ψ) = -weylUpper ψ := by
  simpa using weylUpper_smul (-1) ψ

theorem weylLower_neg (ψ : DualSpinor) : weylLower (-ψ) = -weylLower ψ := by
  simpa using weylLower_smul (-1) ψ

theorem weylUpper_zero : weylUpper (0 : DualSpinor) = 0 := by
  simpa using weylUpper_smul 0 (0 : DualSpinor)

theorem weylLower_zero : weylLower (0 : DualSpinor) = 0 := by
  simpa using weylLower_smul 0 (0 : DualSpinor)

/-- A Dirac spinor determines its two Weyl blocks. -/
theorem weyl_pair_injective {u l u' l' : DualSpinor}
    (h : weylUpper u + weylLower l = weylUpper u' + weylLower l') :
    u = u' ∧ l = l' := by
  have hu := congrArg diracUpper h
  have hl := congrArg diracLower h
  simp only [diracUpper_add, diracLower_add, diracUpper_weylUpper, diracUpper_weylLower,
    diracLower_weylUpper, diracLower_weylLower, add_zero, zero_add] at hu hl
  exact ⟨hu, hl⟩

/-- Upper and lower Weyl images meet only at zero. -/
theorem weylUpper_eq_lower_implies_zero {ψ φ : DualSpinor}
    (h : weylUpper ψ = weylLower φ) : ψ = 0 ∧ φ = 0 := by
  have h0 : (weylUpper ψ) 0 = (weylLower φ) 0 := congrArg (fun v => v 0) h
  have h1 : (weylUpper ψ) 1 = (weylLower φ) 1 := congrArg (fun v => v 1) h
  have h2 : (weylUpper ψ) 2 = (weylLower φ) 2 := congrArg (fun v => v 2) h
  have h3 : (weylUpper ψ) 3 = (weylLower φ) 3 := congrArg (fun v => v 3) h
  have ψ0 : WithLp.ofLp ψ 0 = 0 := by simpa [weylUpper, weylLower] using h0
  have ψ1 : WithLp.ofLp ψ 1 = 0 := by simpa [weylUpper, weylLower] using h1
  have φ0 : WithLp.ofLp φ 0 = 0 := by simpa [weylUpper, weylLower] using h2.symm
  have φ1 : WithLp.ofLp φ 1 = 0 := by simpa [weylUpper, weylLower] using h3.symm
  refine ⟨?_, ?_⟩
  · ext i; fin_cases i
    · exact ψ0
    · exact ψ1
  · ext i; fin_cases i
    · exact φ0
    · exact φ1

/-- Apply a \(4\times 4\) matrix to a Dirac spinor. -/
def applyDiracMat (M : Matrix (Fin 4) (Fin 4) ℂ) (Ψ : DiracSpinor) : DiracSpinor :=
  WithLp.toLp 2 (M *ᵥ WithLp.ofLp Ψ)

/-! ### Linearity and adjoint of the matrix action -/

theorem applyDiracMat_add (M : Matrix (Fin 4) (Fin 4) ℂ) (Ψ Φ : DiracSpinor) :
    applyDiracMat M (Ψ + Φ) = applyDiracMat M Ψ + applyDiracMat M Φ := by
  simp [applyDiracMat, Matrix.mulVec_add]

theorem applyDiracMat_sub (M : Matrix (Fin 4) (Fin 4) ℂ) (Ψ Φ : DiracSpinor) :
    applyDiracMat M (Ψ - Φ) = applyDiracMat M Ψ - applyDiracMat M Φ := by
  simp [applyDiracMat, Matrix.mulVec_sub]

theorem applyDiracMat_smul (c : ℂ) (M : Matrix (Fin 4) (Fin 4) ℂ) (Ψ : DiracSpinor) :
    applyDiracMat M (c • Ψ) = c • applyDiracMat M Ψ := by
  simp [applyDiracMat, Matrix.mulVec_smul]

theorem applyDiracMat_smul_mat (c : ℂ) (M : Matrix (Fin 4) (Fin 4) ℂ) (Ψ : DiracSpinor) :
    applyDiracMat (c • M) Ψ = c • applyDiracMat M Ψ := by
  simp [applyDiracMat, Matrix.smul_mulVec]

theorem applyDiracMat_add_mat (A B : Matrix (Fin 4) (Fin 4) ℂ) (Ψ : DiracSpinor) :
    applyDiracMat (A + B) Ψ = applyDiracMat A Ψ + applyDiracMat B Ψ := by
  simp [applyDiracMat, Matrix.add_mulVec]

theorem applyDiracMat_sub_mat (A B : Matrix (Fin 4) (Fin 4) ℂ) (Ψ : DiracSpinor) :
    applyDiracMat (A - B) Ψ = applyDiracMat A Ψ - applyDiracMat B Ψ := by
  simp [applyDiracMat, Matrix.sub_mulVec]

theorem applyDiracMat_neg (M : Matrix (Fin 4) (Fin 4) ℂ) (Ψ : DiracSpinor) :
    applyDiracMat (-M) Ψ = -applyDiracMat M Ψ := by
  simpa using applyDiracMat_smul_mat (-1) M Ψ

theorem applyDiracMat_zero_mat (Ψ : DiracSpinor) :
    applyDiracMat (0 : Matrix (Fin 4) (Fin 4) ℂ) Ψ = 0 := by
  simp [applyDiracMat]

theorem applyDiracMat_mul (A B : Matrix (Fin 4) (Fin 4) ℂ) (Ψ : DiracSpinor) :
    applyDiracMat (A * B) Ψ = applyDiracMat A (applyDiracMat B Ψ) := by
  simp [applyDiracMat, Matrix.mulVec_mulVec]

theorem applyDiracMat_one (Ψ : DiracSpinor) :
    applyDiracMat (1 : Matrix (Fin 4) (Fin 4) ℂ) Ψ = Ψ := by
  simp [applyDiracMat, Matrix.one_mulVec]

theorem applyDiracMat_smul_one (c : ℂ) (Ψ : DiracSpinor) :
    applyDiracMat (c • (1 : Matrix (Fin 4) (Fin 4) ℂ)) Ψ = c • Ψ := by
  rw [applyDiracMat_smul_mat, applyDiracMat_one]

theorem applyDiracMat_finset_sum {ι : Type*} (s : Finset ι) (M : Matrix (Fin 4) (Fin 4) ℂ)
    (f : ι → DiracSpinor) :
    applyDiracMat M (∑ i ∈ s, f i) = ∑ i ∈ s, applyDiracMat M (f i) := by
  induction s using Finset.cons_induction with
  | empty => simp [applyDiracMat]
  | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, applyDiracMat_add, ih]

theorem applyDiracMat_finset_sum_mat {ι : Type*} (s : Finset ι)
    (M : ι → Matrix (Fin 4) (Fin 4) ℂ) (Ψ : DiracSpinor) :
    applyDiracMat (∑ i ∈ s, M i) Ψ = ∑ i ∈ s, applyDiracMat (M i) Ψ := by
  induction s using Finset.cons_induction with
  | empty => simp [applyDiracMat]
  | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, applyDiracMat_add_mat, ih]

theorem diracSpinor_inner_eq (χ ψ : DiracSpinor) :
    inner ℂ χ ψ = ∑ i : Fin 4, star (χ i) * ψ i := by
  simp [inner, Fin.sum_univ_four]
  ring

/-- The adjoint of `applyDiracMat M` is `applyDiracMat Mᴴ`. -/
theorem applyDiracMat_inner_ct (M : Matrix (Fin 4) (Fin 4) ℂ) (Ψ Φ : DiracSpinor) :
    inner ℂ Ψ (applyDiracMat M Φ) = inner ℂ (applyDiracMat Mᴴ Ψ) Φ := by
  simp only [applyDiracMat, PiLp.inner_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_four,
    Matrix.conjTranspose_apply, RCLike.inner_apply]
  simp only [map_add, map_mul]
  ring_nf
  simp only [Complex.star_def, Complex.conj_conj]
  ring

/-! ### Block-diagonal matrices -/

/-- Block-diagonal `4×4` matrix with `P` on the upper and `Q` on the lower Weyl block. -/
def blockDiag2 (P Q : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![P 0 0, P 0 1, 0, 0;
     P 1 0, P 1 1, 0, 0;
     0, 0, Q 0 0, Q 0 1;
     0, 0, Q 1 0, Q 1 1]

theorem diracUpper_blockDiag2 (P Q : Matrix (Fin 2) (Fin 2) ℂ) (Ψ : DiracSpinor) :
    diracUpper (applyDiracMat (blockDiag2 P Q) Ψ) = applyMat P (diracUpper Ψ) := by
  ext i
  fin_cases i <;>
    simp [blockDiag2, applyDiracMat, applyMat, diracUpper, Matrix.mulVec, dotProduct,
      Fin.sum_univ_four, Fin.sum_univ_two]

theorem diracLower_blockDiag2 (P Q : Matrix (Fin 2) (Fin 2) ℂ) (Ψ : DiracSpinor) :
    diracLower (applyDiracMat (blockDiag2 P Q) Ψ) = applyMat Q (diracLower Ψ) := by
  ext i
  fin_cases i <;>
    simp [blockDiag2, applyDiracMat, applyMat, diracLower, Matrix.mulVec, dotProduct,
      Fin.sum_univ_four, Fin.sum_univ_two]

/-- Chirality matrix \(\gamma^5=-i\gamma^0\gamma^1\gamma^2\gamma^3\),
so that this Weyl representation has \(\gamma^5=\mathrm{diag}(1,1,-1,-1)\). -/
def diracMat5 : Matrix (Fin 4) (Fin 4) ℂ :=
  (-I) • (diracMat0 * diracMat1 * diracMat2 * diracMat3)

/-- In this Weyl representation, \(\gamma^5=\mathrm{diag}(1,1,-1,-1)\). -/
theorem diracMat5_eq :
    diracMat5 = !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, -1, 0; 0, 0, 0, -1] := by
  unfold diracMat5 diracMat0 diracMat1 diracMat2 diracMat3
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.smul_apply, I_mul_I]

theorem diracMat5_sq : diracMat5 * diracMat5 = 1 := by
  rw [diracMat5_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four]

theorem diracMat5_anticomm (μ : Fin 4) :
    diracMat5 * diracMat μ + diracMat μ * diracMat5 = 0 := by
  rw [diracMat5_eq]
  fin_cases μ <;> unfold diracMat diracMat0 diracMat1 diracMat2 diracMat3
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.add_apply]
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.add_apply]
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.add_apply]
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.add_apply]

/-- Weyl projector \(P_+=(1+\gamma^5)/2\). -/
noncomputable def weylProjPlus : Matrix (Fin 4) (Fin 4) ℂ :=
  (1 / 2 : ℂ) • (1 + diracMat5)

/-- Weyl projector \(P_-=(1-\gamma^5)/2\). -/
noncomputable def weylProjMinus : Matrix (Fin 4) (Fin 4) ℂ :=
  (1 / 2 : ℂ) • (1 - diracMat5)

theorem weylProjPlus_eq :
    weylProjPlus = !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0] := by
  unfold weylProjPlus
  rw [diracMat5_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.add_apply, Matrix.smul_apply] <;> ring

theorem weylProjMinus_eq :
    weylProjMinus = !![0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] := by
  unfold weylProjMinus
  rw [diracMat5_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.sub_apply, Matrix.smul_apply] <;> ring

theorem weylProjPlus_sq : weylProjPlus * weylProjPlus = weylProjPlus := by
  rw [weylProjPlus_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four]

theorem weylProjMinus_sq : weylProjMinus * weylProjMinus = weylProjMinus := by
  rw [weylProjMinus_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four]

theorem weylProjPlus_add_minus : weylProjPlus + weylProjMinus = 1 := by
  rw [weylProjPlus_eq, weylProjMinus_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.add_apply]

theorem weylProjPlus_mul_minus : weylProjPlus * weylProjMinus = 0 := by
  rw [weylProjPlus_eq, weylProjMinus_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four]

/-- Upper Weyl image is the \(+1\) eigenspace of \(\gamma^5\). -/
theorem applyDiracMat5_weylUpper (ψ : DualSpinor) :
    applyDiracMat diracMat5 (weylUpper ψ) = weylUpper ψ := by
  rw [diracMat5_eq]
  ext i
  fin_cases i <;> simp [applyDiracMat, weylUpper]

/-- Lower Weyl image is the \(-1\) eigenspace of \(\gamma^5\). -/
theorem applyDiracMat5_weylLower (ψ : DualSpinor) :
    applyDiracMat diracMat5 (weylLower ψ) = -weylLower ψ := by
  rw [diracMat5_eq]
  ext i
  fin_cases i <;> simp [applyDiracMat, weylLower,
    PiLp.neg_apply]

theorem applyWeylProjPlus_weylUpper (ψ : DualSpinor) :
    applyDiracMat weylProjPlus (weylUpper ψ) = weylUpper ψ := by
  rw [weylProjPlus_eq]
  ext i
  fin_cases i <;> simp [applyDiracMat, weylUpper]

theorem applyWeylProjMinus_weylLower (ψ : DualSpinor) :
    applyDiracMat weylProjMinus (weylLower ψ) = weylLower ψ := by
  rw [weylProjMinus_eq]
  ext i
  fin_cases i <;> simp [applyDiracMat, weylLower]

theorem applyWeylProjPlus_weylLower (ψ : DualSpinor) :
    applyDiracMat weylProjPlus (weylLower ψ) = 0 := by
  rw [weylProjPlus_eq]
  ext i
  fin_cases i <;> simp [applyDiracMat, weylLower]

theorem applyWeylProjMinus_weylUpper (ψ : DualSpinor) :
    applyDiracMat weylProjMinus (weylUpper ψ) = 0 := by
  rw [weylProjMinus_eq]
  ext i
  fin_cases i <;> simp [applyDiracMat, weylUpper]

/-- Real dimension of the Dirac spinor matches the commuting left ideal. -/
theorem diracSpinor_finrank_real : Module.finrank ℝ DiracSpinor = 8 := by
  have h := Module.finrank_mul_finrank ℝ ℂ DiracSpinor
  have hℂ : Module.finrank ℝ ℂ = 2 := Complex.finrank_real_complex
  have h4 : Module.finrank ℂ DiracSpinor = 4 := diracSpinor_finrank
  calc Module.finrank ℝ DiracSpinor
      = Module.finrank ℝ ℂ * Module.finrank ℂ DiracSpinor := h.symm
    _ = 2 * 4 := by rw [hℂ, h4]
    _ = 8 := by norm_num

end Logic

end DstDiophantine
