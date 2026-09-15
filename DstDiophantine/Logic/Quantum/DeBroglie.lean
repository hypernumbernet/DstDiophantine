import DstDiophantine.Logic.Quantum.Spinor
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Dual-rotor character, spinor amplitude, and relative overlap

The dual rotor is already an element of \(\mathrm{SU}(2)\). Three
invariants of that matrix are distinguished here.

* The character \(\operatorname{Tr} R = 2\cos(\lVert\beta\rVert/2)\) is real.
* The spinor matrix element \(\langle\uparrow\rvert R\lvert\uparrow\rangle\)
  is \(\cos(\theta/2)-i n_z\sin(\theta/2)\). Along \(\sigma_z\) it is the
  pure phase \(e^{-i\theta/2}\); along \(\sigma_x\) it is the real cosine.
* The observer–particle pairing is the Hilbert inner product
  \(\langle R_{\mathcal{O}}\chi\mid R_A\chi\rangle\), equal to
  \(\langle\chi\mid R_{\mathcal{O}}^{\dagger}R_A\chi\rangle\).

None of these is a spacetime Schrödinger wave, a Born position density,
or a derivation of \(E/\hbar\) from rest mass.
-/

namespace DstDiophantine

namespace Logic

open Matrix Complex NormedSpace InnerProductSpace

open scoped Matrix InnerProductSpace

/-! ### Computational spin-up and matrix action -/

/-- Computational \(\lvert\uparrow\rangle\): the \(+1\) eigenvector of \(\sigma_z\). -/
noncomputable def spinUp : DualSpinor :=
  EuclideanSpace.single (0 : Fin 2) (1 : ℂ)

private theorem spinUp_apply_zero : spinUp 0 = 1 := by
  simp [spinUp]

private theorem spinUp_apply_one : spinUp 1 = 0 := by
  simp [spinUp]

private theorem applyMat_mul (A B : Matrix (Fin 2) (Fin 2) ℂ) (ψ : DualSpinor) :
    applyMat (A * B) ψ = applyMat A (applyMat B ψ) := by
  simp [applyMat, Matrix.mulVec_mulVec]

private theorem applyMat_one' (ψ : DualSpinor) :
    applyMat (1 : Matrix (Fin 2) (Fin 2) ℂ) ψ = ψ := by
  simp [applyMat, Matrix.one_mulVec]

private theorem inner_sum (χ ψ : DualSpinor) :
    inner ℂ χ ψ = ∑ i : Fin 2, star (χ i) * ψ i := by
  simp [inner, Fin.sum_univ_two]
  ring

private theorem applyMat_apply (A : Matrix (Fin 2) (Fin 2) ℂ) (ψ : DualSpinor)
    (i : Fin 2) :
    applyMat A ψ i = ∑ j : Fin 2, A i j * ψ j := by
  simp [applyMat, Matrix.mulVec, dotProduct]

private theorem smul_mul_smul_mat (c d : ℂ) (u v : Matrix (Fin 2) (Fin 2) ℂ) :
    (c • u) * (d • v) = (c * d) • (u * v) := by
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]

private theorem applyMat_inner (A : Matrix (Fin 2) (Fin 2) ℂ) (χ ψ : DualSpinor) :
    inner ℂ (applyMat A χ) ψ = inner ℂ χ (applyMat A.conjTranspose ψ) := by
  simp only [inner_sum, applyMat_apply, Fin.sum_univ_two]
  simp only [star_add, star_mul', Matrix.conjTranspose_apply]
  ring

private theorem applyMat_inner_mul (A B : Matrix (Fin 2) (Fin 2) ℂ)
    (χ ψ : DualSpinor) :
    inner ℂ (applyMat A χ) (applyMat B ψ) =
      inner ℂ χ (applyMat (A.conjTranspose * B) ψ) := by
  rw [applyMat_inner, applyMat_mul]

/-! ### Character: the trace is real -/

theorem cyclicRep_trace (a : Fin 3) : (cyclicRep a).trace = 0 := by
  fin_cases a <;>
    simp [cyclicRep, pauli, pauliX, pauliY, pauliZ, Matrix.trace_fin_two]

theorem cyclicRepComb_trace (n : Fin 3 → ℝ) :
    (cyclicRepComb n).trace = 0 := by
  unfold cyclicRepComb
  simp only [Fin.sum_univ_three]
  rw [trace_add, trace_add, trace_smul, trace_smul, trace_smul]
  simp [cyclicRep_trace]

private theorem algebraMap_smul_mat (r : ℝ) (A : Matrix (Fin 2) (Fin 2) ℂ) :
    (r : ℝ) • A = (r : ℂ) • A :=
  (algebraMap_smul ℂ r A).symm

private theorem trace_real_smul_one (r : ℝ) :
    ((r • (1 : Matrix (Fin 2) (Fin 2) ℂ)).trace) = (2 * r : ℂ) := by
  rw [algebraMap_smul_mat, trace_smul, trace_one]
  simp
  ring

private theorem trace_real_smul (r : ℝ) (A : Matrix (Fin 2) (Fin 2) ℂ) :
    ((r • A).trace) = (r : ℂ) * A.trace := by
  rw [algebraMap_smul_mat, trace_smul]
  simp [smul_eq_mul]

/-- Dual-rotor character: \(\operatorname{Tr} R(\beta)=2\cos(\lVert\beta\rVert/2)\). -/
theorem dualRotorMat_trace (β : DualRapidity) :
    (dualRotorMat β).trace = 2 * (Real.cos (‖β‖ / 2) : ℂ) := by
  rw [dualRotorMat_rodrigues]
  by_cases h : β = 0
  · subst h
    simp only [norm_zero, zero_div, Real.cos_zero, dite_true, add_zero]
    exact trace_real_smul_one 1
  · simp only [h, dite_false]
    rw [trace_add, trace_real_smul_one, trace_real_smul, cyclicRepComb_trace]
    simp

/-- Half-trace character is a real cosine. -/
theorem dualRotorMat_character_real (β : DualRapidity) :
    ((dualRotorMat β).trace / 2).im = 0 := by
  rw [dualRotorMat_trace]
  have h2 : (2 : ℂ) ≠ 0 := by norm_num
  rw [mul_div_cancel_left₀ _ h2]
  exact Complex.ofReal_im _

/-! ### Axis-2 Rodrigues and the pure phase -/

noncomputable def axis2Gen (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (θ / 2 : ℂ) • cyclicRep 2

theorem dualRotorMat_axis2 (θ : ℝ) :
    dualRotorMat (EuclideanSpace.single 2 θ) = NormedSpace.exp (axis2Gen θ) := by
  unfold dualRotorMat axis2Gen
  congr 1
  simp [PiLp.single_apply, Fin.sum_univ_three]

theorem axis2Gen_eq_real_smul (θ : ℝ) :
    axis2Gen θ = (θ / 2 : ℝ) • cyclicRep 2 := by
  unfold axis2Gen
  have h : (θ / 2 : ℂ) = ↑(θ / 2) := by simp [Complex.ofReal_div]
  rw [h]
  rfl

/-- Axis-2 dual rotor: \(\exp(-i\theta\sigma_z/2)=\cos(\theta/2)I+\sin(\theta/2)(-i\sigma_z)\). -/
theorem dualRotorMat_axis2_rodrigues (θ : ℝ) :
    dualRotorMat (EuclideanSpace.single 2 θ) =
      Real.cos (θ / 2) • (1 : Matrix (Fin 2) (Fin 2) ℂ) +
        Real.sin (θ / 2) • cyclicRep 2 := by
  rw [dualRotorMat_axis2, axis2Gen_eq_real_smul]
  exact exp_mat_of_sq_neg_one (cyclicRep_sq 2) (θ / 2)

theorem cyclicRep_two_eq : cyclicRep 2 = !![ -I, 0; 0, I] := by
  unfold cyclicRep pauli pauliZ
  ext i j
  fin_cases i <;> fin_cases j <;> simp

private theorem dualRotorMat_axis2_entries (θ : ℝ) :
    dualRotorMat (EuclideanSpace.single 2 θ) =
      !![↑(Real.cos (θ / 2)) - I * ↑(Real.sin (θ / 2)), 0;
         0, ↑(Real.cos (θ / 2)) + I * ↑(Real.sin (θ / 2))] := by
  rw [dualRotorMat_axis2_rodrigues, cyclicRep_two_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.add_apply, Matrix.smul_apply] <;> ring

/-! ### Spinor amplitude -/

/-- Dual-rotor spinor amplitude \(\langle\chi\rvert R(\beta)\lvert\chi\rangle\). -/
noncomputable def dualRotorAmplitude (β : DualRapidity) (χ : DualSpinor) : ℂ :=
  inner ℂ χ (applyMat (dualRotorMat β) χ)

private theorem mulVec_spinUp (A : Matrix (Fin 2) (Fin 2) ℂ) :
    applyMat A spinUp 0 = A 0 0 ∧ applyMat A spinUp 1 = A 1 0 := by
  constructor <;> simp [applyMat, spinUp]

private theorem dualRotorAmplitude_spinUp_eq_entry (β : DualRapidity) :
    dualRotorAmplitude β spinUp = dualRotorMat β 0 0 := by
  unfold dualRotorAmplitude
  rw [inner_sum]
  have h := mulVec_spinUp (dualRotorMat β)
  simp [Fin.sum_univ_two, spinUp_apply_zero, spinUp_apply_one, h]

private theorem complex_cos_half (θ : ℝ) :
    Complex.cos (θ / 2 : ℂ) = (Real.cos (θ / 2) : ℂ) := by
  calc Complex.cos (θ / 2 : ℂ)
      = Complex.cos (↑(θ / 2)) := by simp [Complex.ofReal_div]
    _ = ↑(Real.cos (θ / 2)) := (Complex.ofReal_cos _).symm

private theorem complex_sin_half (θ : ℝ) :
    Complex.sin (θ / 2 : ℂ) = (Real.sin (θ / 2) : ℂ) := by
  calc Complex.sin (θ / 2 : ℂ)
      = Complex.sin (↑(θ / 2)) := by simp [Complex.ofReal_div]
    _ = ↑(Real.sin (θ / 2)) := (Complex.ofReal_sin _).symm

/-- Along \(\sigma_z\), the amplitude is the half-angle phase \(e^{-i\theta/2}\). -/
theorem dualRotorAmplitude_axis2 (θ : ℝ) :
    dualRotorAmplitude (EuclideanSpace.single 2 θ) spinUp =
      Complex.exp (-(θ / 2 : ℂ) * I) := by
  rw [dualRotorAmplitude_spinUp_eq_entry, dualRotorMat_axis2_entries]
  simp only [of_apply, cons_val', cons_val_zero, empty_val', cons_val_fin_one]
  rw [Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg,
    complex_cos_half, complex_sin_half]
  ring

/-- Along \(\sigma_x\), the amplitude is the real half-angle cosine. -/
theorem dualRotorAmplitude_axis0 (θ : ℝ) :
    dualRotorAmplitude (EuclideanSpace.single 0 θ) spinUp =
      (Real.cos (θ / 2) : ℂ) := by
  rw [dualRotorAmplitude_spinUp_eq_entry, dualRotorMat_axis0_rodrigues,
    cyclicRep_zero_eq]
  simp [Matrix.add_apply, Matrix.smul_apply]

private theorem cyclicRep_apply_00 (a : Fin 3) :
    cyclicRep a 0 0 = if a = 2 then -I else 0 := by
  fin_cases a <;> simp [cyclicRep, pauli, pauliX, pauliY, pauliZ]

private theorem cyclicRepComb_apply_00 (n : Fin 3 → ℝ) :
    cyclicRepComb n 0 0 = -I * (n 2 : ℂ) := by
  simp only [cyclicRepComb, Fin.sum_univ_three, Matrix.add_apply, Matrix.smul_apply]
  simp [cyclicRep_apply_00]
  ring

private theorem real_smul_apply (r : ℝ) (A : Matrix (Fin 2) (Fin 2) ℂ) :
    (r • A) 0 0 = (r : ℂ) * A 0 0 := by
  rw [algebraMap_smul_mat, Matrix.smul_apply]
  simp

/-- Closed form of the spin-up matrix element along a general dual rapidity. -/
theorem dualRotorAmplitude_spinUp (β : DualRapidity) :
    dualRotorAmplitude β spinUp =
      (Real.cos (‖β‖ / 2) : ℂ) - I *
        (if β = 0 then 0
          else (β 2 / ‖β‖ : ℂ) * (Real.sin (‖β‖ / 2) : ℂ)) := by
  rw [dualRotorAmplitude_spinUp_eq_entry, dualRotorMat_rodrigues]
  by_cases h : β = 0
  · subst h
    simp [Real.cos_zero]
  · simp only [h, dite_false, ite_false]
    rw [Matrix.add_apply, real_smul_apply, real_smul_apply, Matrix.one_apply,
      cyclicRepComb_apply_00]
    simp
    ring

/-! ### Relative overlap and the unitarity bound -/

/-- Observer–particle pairing equals the relative-rotor matrix element. -/
theorem dualRotor_relative_overlap (βO βA : DualRapidity) (χ : DualSpinor) :
    inner ℂ (applyMat (dualRotorMat βO) χ) (applyMat (dualRotorMat βA) χ) =
      inner ℂ χ
        (applyMat ((dualRotorMat βO).conjTranspose * dualRotorMat βA) χ) :=
  applyMat_inner_mul _ _ _ _

private theorem applyMat_dualRotor_inner (β : DualRapidity) (χ ψ : DualSpinor) :
    inner ℂ (applyMat (dualRotorMat β) χ) (applyMat (dualRotorMat β) ψ) =
      inner ℂ χ ψ := by
  rw [applyMat_inner_mul, dualRotorMat_unitary, applyMat_one']

private theorem applyMat_dualRotor_norm (β : DualRapidity) (ψ : DualSpinor) :
    ‖applyMat (dualRotorMat β) ψ‖ = ‖ψ‖ := by
  have hinner := applyMat_dualRotor_inner β ψ ψ
  have hU : ‖applyMat (dualRotorMat β) ψ‖ ^ 2 = ‖ψ‖ ^ 2 := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), norm_sq_eq_re_inner (𝕜 := ℂ)]
    exact congrArg Complex.re hinner
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hU

/-- Unitarity bound on a dual-rotor matrix element. -/
theorem dualRotor_matrix_element_bound (β : DualRapidity) (χ ψ : DualSpinor) :
    ‖inner ℂ χ (applyMat (dualRotorMat β) ψ)‖ ≤ ‖χ‖ * ‖ψ‖ := by
  have h :=
    norm_inner_le_norm (𝕜 := ℂ) χ (applyMat (dualRotorMat β) ψ)
  rwa [applyMat_dualRotor_norm] at h

theorem dualRotorAmplitude_bound (β : DualRapidity) (χ : DualSpinor) :
    ‖dualRotorAmplitude β χ‖ ≤ ‖χ‖ ^ 2 := by
  have h := dualRotor_matrix_element_bound β χ χ
  simpa [dualRotorAmplitude, pow_two] using h

/-! ### Same-axis composition on \(\sigma_z\) -/

private theorem axis2Gen_add (θ φ : ℝ) :
    axis2Gen (θ + φ) = axis2Gen θ + axis2Gen φ := by
  unfold axis2Gen
  have h : (↑(θ + φ) / 2) = (θ / 2 : ℂ) + (φ / 2 : ℂ) := by
    rw [Complex.ofReal_add]
    ring
  rw [h, add_smul]

private theorem commute_axis2Gen (θ φ : ℝ) :
    Commute (axis2Gen θ) (axis2Gen φ) := by
  unfold axis2Gen
  change ((θ / 2 : ℂ) • cyclicRep 2) * ((φ / 2 : ℂ) • cyclicRep 2) =
    ((φ / 2 : ℂ) • cyclicRep 2) * ((θ / 2 : ℂ) • cyclicRep 2)
  rw [smul_mul_smul_mat, smul_mul_smul_mat, mul_comm (θ / 2 : ℂ)]

/-- Same-axis dual rotors compose by adding angles. -/
theorem dualRotorMat_axis2_add (θ φ : ℝ) :
    dualRotorMat (EuclideanSpace.single 2 (θ + φ)) =
      dualRotorMat (EuclideanSpace.single 2 θ) *
        dualRotorMat (EuclideanSpace.single 2 φ) := by
  rw [dualRotorMat_axis2, dualRotorMat_axis2, dualRotorMat_axis2, axis2Gen_add]
  exact Matrix.exp_add_of_commute (axis2Gen θ) (axis2Gen φ) (commute_axis2Gen θ φ)

end Logic

end DstDiophantine
