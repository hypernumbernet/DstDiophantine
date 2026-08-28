import DstDiophantine.Logic.Quantum.Quaternion
import DstDiophantine.Logic.Quantum.DualSector
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.Matrix.Normed
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

open Matrix Complex NormedSpace

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

/-! ### Axis-0 Rodrigues formula and SU(2) unitarity -/

open scoped Matrix

noncomputable local instance :
    NormedRing (Matrix (Fin 2) (Fin 2) ℂ) :=
  Matrix.linftyOpNormedRing

noncomputable local instance :
    NormedAlgebra ℂ (Matrix (Fin 2) (Fin 2) ℂ) :=
  Matrix.linftyOpNormedAlgebra

noncomputable local instance :
    NormedAlgebra ℝ (Matrix (Fin 2) (Fin 2) ℂ) :=
  NormedAlgebra.restrictScalars ℝ ℂ (Matrix (Fin 2) (Fin 2) ℂ)

noncomputable local instance :
    NormedAlgebra ℚ (Matrix (Fin 2) (Fin 2) ℂ) :=
  NormedAlgebra.restrictScalars ℚ ℝ (Matrix (Fin 2) (Fin 2) ℂ)

theorem axis0Gen_eq_real_smul (θ : ℝ) :
    axis0Gen θ = (θ / 2 : ℝ) • cyclicRep 0 := by
  unfold axis0Gen cyclicRep
  have h : (θ / 2 : ℂ) = ↑(θ / 2) := by
    simp [Complex.ofReal_div]
  rw [h]
  rfl

private theorem hasDerivAt_exp_neg_smul_mat
    (x : Matrix (Fin 2) (Fin 2) ℂ) (u : ℝ) :
    HasDerivAt (fun v : ℝ => NormedSpace.exp ((-v) • x))
      (NormedSpace.exp ((-u) • x) * (-x)) u := by
  have h : HasDerivAt (fun v : ℝ => NormedSpace.exp (v • (-x)))
      (NormedSpace.exp (u • (-x)) * (-x)) u :=
    hasDerivAt_exp_smul_const (-x) u
  have hfun : (fun v : ℝ => NormedSpace.exp ((-v) • x)) =
      fun v : ℝ => NormedSpace.exp (v • (-x)) :=
    funext fun v => by rw [neg_smul, smul_neg]
  simpa [hfun, neg_smul, smul_neg] using h

private theorem exp_smul_mul_exp_neg_smul_mat
    (x : Matrix (Fin 2) (Fin 2) ℂ) (t : ℝ) :
    NormedSpace.exp (t • x) * NormedSpace.exp ((-t) • x) = 1 := by
  have hneg : (-t) • x = -(t • x) := neg_smul t x
  rw [hneg]
  have hc : Commute (t • x) (-(t • x)) := Commute.neg_right (Commute.refl _)
  have h := (NormedSpace.exp_add_of_commute hc).symm
  rw [add_neg_cancel, NormedSpace.exp_zero] at h
  exact h

/-- Circular closed form on `M₂(ℂ)`: `x² = -1 ⇒ exp(t • x) = cos t + sin t • x`. -/
theorem exp_mat_of_sq_neg_one {x : Matrix (Fin 2) (Fin 2) ℂ}
    (hx : x * x = -1) (t : ℝ) :
    NormedSpace.exp (t • x) =
      Real.cos t • (1 : Matrix (Fin 2) (Fin 2) ℂ) + Real.sin t • x := by
  let R : ℝ → Matrix (Fin 2) (Fin 2) ℂ :=
    fun u => Real.cos u • (1 : Matrix (Fin 2) (Fin 2) ℂ) + Real.sin u • x
  let f : ℝ → Matrix (Fin 2) (Fin 2) ℂ :=
    fun u => NormedSpace.exp ((-u) • x) * R u
  have hRx (u : ℝ) : x * R u = (-Real.sin u) • (1 : Matrix (Fin 2) (Fin 2) ℂ) +
      Real.cos u • x := by
    simp only [R, mul_add]
    have h1 : x * (Real.cos u • (1 : Matrix (Fin 2) (Fin 2) ℂ)) = Real.cos u • x := by
      rw [mul_smul_comm, mul_one]
    have h2 : x * (Real.sin u • x) = (-Real.sin u) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
      rw [mul_smul_comm, hx, smul_neg, neg_smul]
    rw [h1, h2, add_comm]
  have hR' (u : ℝ) :
      HasDerivAt R ((-Real.sin u) • (1 : Matrix (Fin 2) (Fin 2) ℂ) +
        Real.cos u • x) u :=
    ((Real.hasDerivAt_cos u).smul_const (1 : Matrix (Fin 2) (Fin 2) ℂ)).add
      ((Real.hasDerivAt_sin u).smul_const x)
  have hf' (u : ℝ) : HasDerivAt f 0 u := by
    have hexp := hasDerivAt_exp_neg_smul_mat x u
    have hmul :
        HasDerivAt ((fun v => NormedSpace.exp ((-v) • x)) * R)
          (NormedSpace.exp ((-u) • x) * (-x) * R u +
            NormedSpace.exp ((-u) • x) *
              ((-Real.sin u) • (1 : Matrix (Fin 2) (Fin 2) ℂ) + Real.cos u • x)) u :=
      hexp.mul (hR' u)
    have hzero :
        NormedSpace.exp ((-u) • x) * (-x) * R u +
          NormedSpace.exp ((-u) • x) *
            ((-Real.sin u) • (1 : Matrix (Fin 2) (Fin 2) ℂ) + Real.cos u • x) = 0 := by
      calc
        NormedSpace.exp ((-u) • x) * (-x) * R u +
              NormedSpace.exp ((-u) • x) *
                ((-Real.sin u) • (1 : Matrix (Fin 2) (Fin 2) ℂ) + Real.cos u • x)
            = NormedSpace.exp ((-u) • x) * ((-x) * R u) +
                NormedSpace.exp ((-u) • x) * (x * R u) := by
              rw [mul_assoc, hRx]
        _ = NormedSpace.exp ((-u) • x) * ((-x) * R u + x * R u) := by
              rw [← mul_add]
        _ = NormedSpace.exp ((-u) • x) * (-(x * R u) + x * R u) := by
              rw [neg_mul]
        _ = NormedSpace.exp ((-u) • x) * 0 := by
              rw [neg_add_cancel]
        _ = 0 := mul_zero _
    convert hmul using 2
    · rfl
    · exact hzero.symm
  have hf0 : f 0 = 1 := by
    simp only [f, R, neg_zero, zero_smul, NormedSpace.exp_zero, Real.cos_zero,
      Real.sin_zero, one_smul, zero_smul, add_zero, mul_one]
  have hdiff : Differentiable ℝ f := fun u => (hf' u).differentiableAt
  have hderiv : ∀ u, deriv f u = 0 := fun u => (hf' u).deriv
  have hf_one : ∀ u, f u = 1 := fun u =>
    (is_const_of_deriv_eq_zero hdiff hderiv u 0).trans hf0
  have : NormedSpace.exp ((-t) • x) * R t = 1 := hf_one t
  calc
    NormedSpace.exp (t • x) = NormedSpace.exp (t • x) * 1 := (mul_one _).symm
    _ = NormedSpace.exp (t • x) * (NormedSpace.exp ((-t) • x) * R t) := by rw [this]
    _ = (NormedSpace.exp (t • x) * NormedSpace.exp ((-t) • x)) * R t := by rw [mul_assoc]
    _ = 1 * R t := by rw [exp_smul_mul_exp_neg_smul_mat]
    _ = R t := one_mul _

/-- Axis-0 dual rotor: `exp(-i θ/2 σ_x) = cos(θ/2) I + sin(θ/2) (-i σ_x)`. -/
theorem dualRotorMat_axis0_rodrigues (θ : ℝ) :
    dualRotorMat (EuclideanSpace.single 0 θ) =
      Real.cos (θ / 2) • (1 : Matrix (Fin 2) (Fin 2) ℂ) +
        Real.sin (θ / 2) • cyclicRep 0 := by
  rw [dualRotorMat_axis0, axis0Gen_eq_real_smul]
  exact exp_mat_of_sq_neg_one (cyclicRep_sq 0) (θ / 2)

theorem cyclicRep_zero_eq : cyclicRep 0 = !![0, -I; -I, 0] := by
  unfold cyclicRep pauli pauliX
  ext i j
  fin_cases i <;> fin_cases j <;> simp

private theorem ofReal_cos_sin_sq (θ : ℝ) :
    (↑(Real.cos θ) : ℂ) * ↑(Real.cos θ) + ↑(Real.sin θ) * ↑(Real.sin θ) = 1 := by
  rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_add]
  rw [← pow_two, ← pow_two, Real.cos_sq_add_sin_sq]
  simp

private theorem dualRotorMat_axis0_entries (θ : ℝ) :
    dualRotorMat (EuclideanSpace.single 0 θ) =
      !![↑(Real.cos (θ / 2)), -I * ↑(Real.sin (θ / 2));
         -I * ↑(Real.sin (θ / 2)), ↑(Real.cos (θ / 2))] := by
  rw [dualRotorMat_axis0_rodrigues, cyclicRep_zero_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.add_apply, Matrix.smul_apply, mul_comm]

/-- Axis-0 dual rotor is unitary. -/
theorem dualRotorMat_axis0_unitary (θ : ℝ) :
    (dualRotorMat (EuclideanSpace.single 0 θ)).conjTranspose *
      dualRotorMat (EuclideanSpace.single 0 θ) = 1 := by
  rw [dualRotorMat_axis0_rodrigues]
  set c := Real.cos (θ / 2)
  set s := Real.sin (θ / 2)
  have hRℂ (r : ℝ) (m : Matrix (Fin 2) (Fin 2) ℂ) :
      r • m = (r : ℂ) • m := (algebraMap_smul ℂ r m).symm
  rw [hRℂ c, hRℂ s]
  have hG : (cyclicRep 0).conjTranspose = -cyclicRep 0 := cyclicRep_conjTranspose 0
  have hstar :
      ((c : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) + (s : ℂ) • cyclicRep 0).conjTranspose =
        (c : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) - (s : ℂ) • cyclicRep 0 := by
    simp [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.conjTranspose_one,
      hG, smul_neg, sub_eq_add_neg]
  rw [hstar]
  have hCC : ((c : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) *
        ((c : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) =
      ((c : ℂ) * c) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    calc ((c : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) *
          ((c : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ))
        = (c : ℂ) • ((1 : Matrix (Fin 2) (Fin 2) ℂ) *
            ((c : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ))) := by
          rw [smul_mul_assoc]
      _ = (c : ℂ) • ((c : ℂ) • ((1 : Matrix (Fin 2) (Fin 2) ℂ) * 1)) := by
          rw [mul_smul_comm]
      _ = ((c : ℂ) * c) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
          rw [smul_smul, one_mul]
  have hGG : ((s : ℂ) • cyclicRep 0) * ((s : ℂ) • cyclicRep 0) =
      ((s : ℂ) * s) • (cyclicRep 0 * cyclicRep 0) := by
    calc ((s : ℂ) • cyclicRep 0) * ((s : ℂ) • cyclicRep 0)
        = (s : ℂ) • (cyclicRep 0 * ((s : ℂ) • cyclicRep 0)) := by
          rw [smul_mul_assoc]
      _ = (s : ℂ) • ((s : ℂ) • (cyclicRep 0 * cyclicRep 0)) := by
          rw [mul_smul_comm]
      _ = ((s : ℂ) * s) • (cyclicRep 0 * cyclicRep 0) := by
          rw [smul_smul]
  have hCG : ((c : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) * ((s : ℂ) • cyclicRep 0) =
      ((c : ℂ) * s) • cyclicRep 0 := by
    calc ((c : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) * ((s : ℂ) • cyclicRep 0)
        = (c : ℂ) • ((1 : Matrix (Fin 2) (Fin 2) ℂ) * ((s : ℂ) • cyclicRep 0)) := by
          rw [smul_mul_assoc]
      _ = (c : ℂ) • ((s : ℂ) • ((1 : Matrix (Fin 2) (Fin 2) ℂ) * cyclicRep 0)) := by
          rw [mul_smul_comm]
      _ = ((c : ℂ) * s) • cyclicRep 0 := by
          rw [smul_smul, one_mul]
  have hGC : ((s : ℂ) • cyclicRep 0) * ((c : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) =
      ((s : ℂ) * c) • cyclicRep 0 := by
    calc ((s : ℂ) • cyclicRep 0) * ((c : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ))
        = (s : ℂ) • (cyclicRep 0 * ((c : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ))) := by
          rw [smul_mul_assoc]
      _ = (s : ℂ) • ((c : ℂ) • (cyclicRep 0 * 1)) := by
          rw [mul_smul_comm]
      _ = ((s : ℂ) * c) • cyclicRep 0 := by
          rw [smul_smul, mul_one]
  rw [sub_mul, mul_add, mul_add, hCC, hGG, hCG, hGC, cyclicRep_sq,
    mul_comm (s : ℂ) c]
  have htrig : ((c : ℂ) * c + (s : ℂ) * s) • (1 : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
    have : (c : ℂ) * c + (s : ℂ) * s = 1 := ofReal_cos_sin_sq (θ / 2)
    simp [this]
  convert htrig using 1
  simp [smul_neg, add_smul, sub_eq_add_neg]
  abel

/-- Axis-0 dual rotor has determinant `1`. -/
theorem dualRotorMat_axis0_det (θ : ℝ) :
    (dualRotorMat (EuclideanSpace.single 0 θ)).det = 1 := by
  rw [dualRotorMat_axis0_entries, Matrix.det_fin_two]
  set c := (↑(Real.cos (θ / 2)) : ℂ)
  set s := (↑(Real.sin (θ / 2)) : ℂ)
  have hcs : c * c + s * s = 1 := ofReal_cos_sin_sq (θ / 2)
  have hI : (-I : ℂ) * s * ((-I) * s) = - (s * s) := by
    calc (-I) * s * ((-I) * s)
        = ((-I) * (-I)) * (s * s) := by ring
      _ = (I * I) * (s * s) := by simp
      _ = (-1) * (s * s) := by simp [I_mul_I]
      _ = -(s * s) := by ring
  -- det = c*c - ((-I)s)*((-I)s)
  change c * c - ((-I) * s) * ((-I) * s) = 1
  rw [hI, sub_neg_eq_add, hcs]

end Logic

end DstDiophantine
