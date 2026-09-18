import DstDiophantine.Logic.Quantum.Spinor
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Abel

/-!
# Dual-rotor character, spinor amplitude, and relative overlap

The dual rotor is already an element of \(\mathrm{SU}(2)\). Three
invariants of that matrix are distinguished here.

* The character \(\operatorname{Tr} R = 2\cos(\lVert\beta\rVert/2)\) is
  the sum of opposite computational amplitudes, hence real.
* The spinor matrix element \(\langle\uparrow\rvert R\lvert\uparrow\rangle\)
  is \(\cos(\theta/2)-i n_z\sin(\theta/2)\). Along \(\sigma_z\) it is the
  pure phase \(e^{-i\theta/2}\); along \(\sigma_x\) it is the real cosine.
  Its squared modulus is the polar tilt of the dual axis.
* The observer–particle pairing is the Hilbert inner product
  \(\langle R_{\mathcal{O}}\chi\mid R_A\chi\rangle\), equal to
  \(\langle\chi\mid R_{\mathcal{O}}^{\dagger}R_A\chi\rangle\).
  The relative rotor stays in \(\mathrm{SU}(2)\). The inverse is the
  opposite rapidity, so the relative rotor is \(R(-\beta_{\mathcal{O}})R(\beta_A)\).
  On a common ray it is a single dual rotation by the difference. Off-axis
  the character of a product records axis alignment; the remainder is a
  traceless tilt, and perpendicular \(\pi\) dual rotations have group
  commutator \(-I\). A \(2\pi\) dual rotation about the observer axis is
  \(-I\).

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

private theorem real_smul_apply (r : ℝ) (A : Matrix (Fin 2) (Fin 2) ℂ)
    (i j : Fin 2) : (r • A) i j = (r : ℂ) * A i j := by
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

/-! ### Spin-down, character as opposite-phase sum, modulus, double cover -/

/-- Computational \(\lvert\downarrow\rangle\): the \(-1\) eigenvector of \(\sigma_z\). -/
noncomputable def spinDown : DualSpinor :=
  EuclideanSpace.single (1 : Fin 2) (1 : ℂ)

private theorem spinDown_apply_zero : spinDown 0 = 0 := by
  simp [spinDown]

private theorem spinDown_apply_one : spinDown 1 = 1 := by
  simp [spinDown]

private theorem mulVec_spinDown (A : Matrix (Fin 2) (Fin 2) ℂ) :
    applyMat A spinDown 0 = A 0 1 ∧ applyMat A spinDown 1 = A 1 1 := by
  constructor <;> simp [applyMat, spinDown]

private theorem dualRotorAmplitude_spinDown_eq_entry (β : DualRapidity) :
    dualRotorAmplitude β spinDown = dualRotorMat β 1 1 := by
  unfold dualRotorAmplitude
  rw [inner_sum]
  have h := mulVec_spinDown (dualRotorMat β)
  simp [Fin.sum_univ_two, spinDown_apply_zero, spinDown_apply_one, h]

/-- The character is the sum of the two computational matrix elements. -/
theorem dualRotorMat_trace_eq_amplitudes (β : DualRapidity) :
    (dualRotorMat β).trace =
      dualRotorAmplitude β spinUp + dualRotorAmplitude β spinDown := by
  rw [dualRotorAmplitude_spinUp_eq_entry, dualRotorAmplitude_spinDown_eq_entry,
    Matrix.trace_fin_two]

/-- Along \(\sigma_z\), the down amplitude is the opposite half-angle phase. -/
theorem dualRotorAmplitude_axis2_down (θ : ℝ) :
    dualRotorAmplitude (EuclideanSpace.single 2 θ) spinDown =
      Complex.exp ((θ / 2 : ℂ) * I) := by
  rw [dualRotorAmplitude_spinDown_eq_entry, dualRotorMat_axis2_entries]
  simp only [of_apply, cons_val', empty_val', cons_val_fin_one, cons_val_one]
  rw [Complex.exp_mul_I, complex_cos_half, complex_sin_half]
  ring

private theorem cyclicRep_apply_11 (a : Fin 3) :
    cyclicRep a 1 1 = if a = 2 then I else 0 := by
  fin_cases a <;> simp [cyclicRep, pauli, pauliX, pauliY, pauliZ]

private theorem cyclicRepComb_apply_11 (n : Fin 3 → ℝ) :
    cyclicRepComb n 1 1 = I * (n 2 : ℂ) := by
  simp only [cyclicRepComb, Fin.sum_univ_three, Matrix.add_apply, Matrix.smul_apply]
  simp [cyclicRep_apply_11]
  ring

theorem dualRotorAmplitude_spinDown (β : DualRapidity) :
    dualRotorAmplitude β spinDown =
      (Real.cos (‖β‖ / 2) : ℂ) + I *
        (if β = 0 then 0
          else (β 2 / ‖β‖ : ℂ) * (Real.sin (‖β‖ / 2) : ℂ)) := by
  rw [dualRotorAmplitude_spinDown_eq_entry, dualRotorMat_rodrigues]
  by_cases h : β = 0
  · subst h
    simp [Real.cos_zero]
  · simp only [h, dite_false, ite_false]
    rw [Matrix.add_apply, real_smul_apply, real_smul_apply, Matrix.one_apply,
      cyclicRepComb_apply_11]
    simp
    ring

/-- Polar weight of the observer axis in the spin-up matrix element. -/
private noncomputable def dualNzSin (β : DualRapidity) : ℝ :=
  if β = 0 then 0 else (β 2 / ‖β‖) * Real.sin (‖β‖ / 2)

private theorem dualNzSin_coe (β : DualRapidity) :
    (if β = 0 then (0 : ℂ)
      else (β 2 / ‖β‖ : ℂ) * (Real.sin (‖β‖ / 2) : ℂ)) =
      (dualNzSin β : ℂ) := by
  by_cases h : β = 0
  · simp [h, dualNzSin]
  · simp [h, dualNzSin, Complex.ofReal_mul]

private theorem re_ofReal_sub_I (a b : ℝ) :
    ((a : ℂ) - I * (b : ℂ)).re = a := by
  rw [sub_re, mul_re]
  simp [I_re, I_im, Complex.ofReal_re, Complex.ofReal_im]

private theorem norm_sq_ofReal_sub_I (a b : ℝ) :
    ‖(a : ℂ) - I * (b : ℂ)‖ ^ 2 = a ^ 2 + b ^ 2 := by
  have : (a : ℂ) - I * b = ↑a + ↑(-b) * I := by
    simp [sub_eq_add_neg, mul_comm]
  rw [this, ← Complex.normSq_eq_norm_sq, Complex.normSq_add_mul_I]
  ring

/-- Half-trace character equals the real part of the spin-up matrix element. -/
theorem dualRotorAmplitude_spinUp_re (β : DualRapidity) :
    (dualRotorAmplitude β spinUp).re = Real.cos (‖β‖ / 2) := by
  rw [dualRotorAmplitude_spinUp, dualNzSin_coe, re_ofReal_sub_I]

/-- Squared modulus of the spin-up matrix element: polar tilt of the dual axis. -/
theorem dualRotorAmplitude_spinUp_normSq (β : DualRapidity) :
    ‖dualRotorAmplitude β spinUp‖ ^ 2 =
      Real.cos (‖β‖ / 2) ^ 2 + dualNzSin β ^ 2 := by
  rw [dualRotorAmplitude_spinUp, dualNzSin_coe, norm_sq_ofReal_sub_I]

private theorem dualRapidity_norm_sq (β : DualRapidity) :
    ‖β‖ ^ 2 = (β 0) ^ 2 + (β 1) ^ 2 + (β 2) ^ 2 := by
  simpa [inner, Fin.sum_univ_three, sq] using
    (real_inner_self_eq_norm_sq (F := DualRapidity) β).symm

private theorem dualRapidity_unit_sq {β : DualRapidity} (h : β ≠ 0) :
    (β 0 / ‖β‖) ^ 2 + (β 1 / ‖β‖) ^ 2 + (β 2 / ‖β‖) ^ 2 = 1 := by
  have hr : ‖β‖ ≠ 0 := norm_ne_zero_iff.mpr h
  have hdiv :
      (β 0 / ‖β‖) ^ 2 + (β 1 / ‖β‖) ^ 2 + (β 2 / ‖β‖) ^ 2 =
        ((β 0) ^ 2 + (β 1) ^ 2 + (β 2) ^ 2) / ‖β‖ ^ 2 := by
    field_simp [hr]
  rw [hdiv, ← dualRapidity_norm_sq, div_self (pow_ne_zero 2 hr)]

/-- Equivalently, the squared modulus is one minus the equatorial weight. -/
theorem dualRotorAmplitude_spinUp_normSq_equator {β : DualRapidity} (h : β ≠ 0) :
    ‖dualRotorAmplitude β spinUp‖ ^ 2 =
      1 - ((β 0 / ‖β‖) ^ 2 + (β 1 / ‖β‖) ^ 2) * Real.sin (‖β‖ / 2) ^ 2 := by
  have hn := dualRapidity_unit_sq h
  have hcs : Real.cos (‖β‖ / 2) ^ 2 + Real.sin (‖β‖ / 2) ^ 2 = 1 :=
    Real.cos_sq_add_sin_sq _
  rw [dualRotorAmplitude_spinUp_normSq]
  simp only [dualNzSin, h, ite_false]
  have hnz :
      (β 2 / ‖β‖) ^ 2 = 1 - ((β 0 / ‖β‖) ^ 2 + (β 1 / ‖β‖) ^ 2) := by
    linarith
  calc Real.cos (‖β‖ / 2) ^ 2 + (β 2 / ‖β‖ * Real.sin (‖β‖ / 2)) ^ 2
      = Real.cos (‖β‖ / 2) ^ 2 +
          (β 2 / ‖β‖) ^ 2 * Real.sin (‖β‖ / 2) ^ 2 := by ring
    _ = Real.cos (‖β‖ / 2) ^ 2 +
          (1 - ((β 0 / ‖β‖) ^ 2 + (β 1 / ‖β‖) ^ 2)) *
            Real.sin (‖β‖ / 2) ^ 2 := by rw [hnz]
    _ = Real.cos (‖β‖ / 2) ^ 2 + Real.sin (‖β‖ / 2) ^ 2 -
          ((β 0 / ‖β‖) ^ 2 + (β 1 / ‖β‖) ^ 2) *
            Real.sin (‖β‖ / 2) ^ 2 := by ring
    _ = 1 - ((β 0 / ‖β‖) ^ 2 + (β 1 / ‖β‖) ^ 2) *
          Real.sin (‖β‖ / 2) ^ 2 := by rw [hcs]

/-- Along the observer axis the spin-up matrix element is a pure phase. -/
theorem dualRotorAmplitude_axis2_norm (θ : ℝ) :
    ‖dualRotorAmplitude (EuclideanSpace.single 2 θ) spinUp‖ = 1 := by
  rw [dualRotorAmplitude_axis2, Complex.norm_exp]
  have hre : (-(θ / 2 : ℂ) * I).re = 0 := by simp
  rw [hre, Real.exp_zero]

/-- \(2\pi\) dual rotation about the observer axis is \(-I\). -/
theorem dualRotorMat_axis2_two_pi :
    dualRotorMat (EuclideanSpace.single 2 (2 * Real.pi)) = -1 := by
  rw [dualRotorMat_axis2_rodrigues]
  have hhalf : (2 * Real.pi) / 2 = Real.pi := by ring
  rw [hhalf, Real.cos_pi, Real.sin_pi]
  simp

/-- \(4\pi\) dual rotation about the observer axis is the identity. -/
theorem dualRotorMat_axis2_four_pi :
    dualRotorMat (EuclideanSpace.single 2 (4 * Real.pi)) = 1 := by
  rw [dualRotorMat_axis2_rodrigues]
  have hhalf : (4 * Real.pi) / 2 = 2 * Real.pi := by ring
  rw [hhalf, Real.cos_two_pi, Real.sin_two_pi]
  simp

theorem dualRotorAmplitude_axis2_two_pi :
    dualRotorAmplitude (EuclideanSpace.single 2 (2 * Real.pi)) spinUp = -1 := by
  rw [dualRotorAmplitude_spinUp_eq_entry, dualRotorMat_axis2_two_pi]
  simp [Matrix.neg_apply]

theorem dualRotorMat_character_two_pi :
    (dualRotorMat (EuclideanSpace.single 2 (2 * Real.pi))).trace / 2 = -1 := by
  rw [dualRotorMat_axis2_two_pi, trace_neg, trace_one]
  norm_num

/-! ### Relative dual rotor stays in \(\mathrm{SU}(2)\); distinct axes need not commute -/

theorem dualRotorMat_mul_conjTranspose (β : DualRapidity) :
    dualRotorMat β * (dualRotorMat β).conjTranspose = 1 := by
  have hdet : IsUnit (dualRotorMat β).det := by
    rw [dualRotorMat_det]
    exact isUnit_one
  rw [← Matrix.inv_eq_left_inv (dualRotorMat_unitary β)]
  exact Matrix.mul_nonsing_inv _ hdet

/-- The observer–particle relative dual rotor is unitary. -/
theorem dualRotor_relative_unitary (βO βA : DualRapidity) :
    ((dualRotorMat βO).conjTranspose * dualRotorMat βA).conjTranspose *
      ((dualRotorMat βO).conjTranspose * dualRotorMat βA) = 1 := by
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  calc (dualRotorMat βA).conjTranspose * dualRotorMat βO *
        ((dualRotorMat βO).conjTranspose * dualRotorMat βA)
      = (dualRotorMat βA).conjTranspose *
          (dualRotorMat βO * (dualRotorMat βO).conjTranspose) * dualRotorMat βA := by
        simp [mul_assoc]
    _ = (dualRotorMat βA).conjTranspose * dualRotorMat βA := by
        rw [dualRotorMat_mul_conjTranspose, mul_one]
    _ = 1 := dualRotorMat_unitary βA

/-- The observer–particle relative dual rotor has determinant \(1\). -/
theorem dualRotor_relative_det (βO βA : DualRapidity) :
    ((dualRotorMat βO).conjTranspose * dualRotorMat βA).det = 1 := by
  rw [det_mul, det_conjTranspose, dualRotorMat_det, dualRotorMat_det]
  simp

private theorem dualRotorMat_axis0_pi :
    dualRotorMat (EuclideanSpace.single 0 Real.pi) = cyclicRep 0 := by
  rw [dualRotorMat_axis0_rodrigues, Real.cos_pi_div_two, Real.sin_pi_div_two]
  simp

private theorem dualRotorMat_axis2_pi :
    dualRotorMat (EuclideanSpace.single 2 Real.pi) = cyclicRep 2 := by
  rw [dualRotorMat_axis2_rodrigues, Real.cos_pi_div_two, Real.sin_pi_div_two]
  simp

private theorem cyclicRep_one_eq : cyclicRep 1 = !![0, -1; 1, 0] := by
  unfold cyclicRep pauli pauliY
  ext i j
  fin_cases i <;> fin_cases j <;> simp [neg_mul, I_mul_I]

/-- Distinct-axis dual rotors need not commute. -/
theorem dualRotorMat_axes_not_commute :
    dualRotorMat (EuclideanSpace.single 0 Real.pi) *
        dualRotorMat (EuclideanSpace.single 2 Real.pi) ≠
      dualRotorMat (EuclideanSpace.single 2 Real.pi) *
        dualRotorMat (EuclideanSpace.single 0 Real.pi) := by
  rw [dualRotorMat_axis0_pi, dualRotorMat_axis2_pi,
    cyclicRep_zero_mul_two, cyclicRep_two_mul_zero]
  intro h
  have hsum : cyclicRep 1 + cyclicRep 1 = 0 := by
    nth_rw 1 [← h]
    exact neg_add_cancel _
  have he : (cyclicRep 1 + cyclicRep 1) 1 0 = (0 : Matrix (Fin 2) (Fin 2) ℂ) 1 0 :=
    congrArg (fun A : Matrix (Fin 2) (Fin 2) ℂ => A 1 0) hsum
  simp [cyclicRep_one_eq, Matrix.add_apply] at he

/-! ### Relative composition, character of a product, noncommutative residue -/

private theorem smul_mul_smul_matR (c d : ℝ) (u v : Matrix (Fin 2) (Fin 2) ℂ) :
    (c • u) * (d • v) = (c * d : ℝ) • (u * v) := by
  rw [algebraMap_smul_mat, algebraMap_smul_mat, smul_mul_smul_mat,
    algebraMap_smul_mat (c * d), Complex.ofReal_mul]

/-- Unit dual axis, or zero if the rapidity vanishes. -/
noncomputable def dualAxis (β : DualRapidity) : Fin 3 → ℝ :=
  fun a => if β = 0 then 0 else β a / ‖β‖

/-- Alignment \(\hat\beta\cdot\hat\gamma\) of two dual axes. -/
noncomputable def dualAxisInner (β γ : DualRapidity) : ℝ :=
  dualAxis β 0 * dualAxis γ 0 + dualAxis β 1 * dualAxis γ 1 +
    dualAxis β 2 * dualAxis γ 2

private theorem dualRotorMat_cos_sin (β : DualRapidity) :
    dualRotorMat β =
      Real.cos (‖β‖ / 2) • (1 : Matrix (Fin 2) (Fin 2) ℂ) +
        Real.sin (‖β‖ / 2) • cyclicRepComb (dualAxis β) := by
  rw [dualRotorMat_rodrigues]
  by_cases h : β = 0
  · subst h
    simp [Real.sin_zero]
  · have hax : dualAxis β = fun a => β a / ‖β‖ := by
      funext a
      simp [dualAxis, h]
    simp [h, hax]

private theorem dualAxis_neg (β : DualRapidity) (a : Fin 3) :
    dualAxis (-β) a = -dualAxis β a := by
  unfold dualAxis
  by_cases h : β = 0
  · subst h
    simp
  · have hneg : (-β) ≠ 0 := neg_ne_zero.mpr h
    simp [h, hneg, PiLp.neg_apply, norm_neg, neg_div]

private theorem dualAxisInner_neg_left (β γ : DualRapidity) :
    dualAxisInner (-β) γ = -dualAxisInner β γ := by
  unfold dualAxisInner
  simp [dualAxis_neg]
  ring

/-- Observer–particle relative dual rotor is \(R(-\beta_{\mathcal{O}})R(\beta_A)\). -/
theorem dualRotor_relative_eq_neg_mul (βO βA : DualRapidity) :
    (dualRotorMat βO).conjTranspose * dualRotorMat βA =
      dualRotorMat (-βO) * dualRotorMat βA := by
  rw [dualRotorMat_neg]

/-- On a common ray the relative dual rotor is a single dual rotation by the difference. -/
theorem dualRotor_relative_ray (s t : ℝ) (β : DualRapidity) :
    (dualRotorMat (s • β)).conjTranspose * dualRotorMat (t • β) =
      dualRotorMat ((t - s) • β) := by
  rw [dualRotor_relative_eq_neg_mul]
  have hneg : -(s • β) = (-s) • β := by
    simp [neg_smul]
  rw [hneg, ← dualRotorMat_ray_add]
  have hscale : (-s + t) • β = (t - s) • β := by
    simp [sub_eq_add_neg, add_comm]
  rw [hscale]

private theorem cyclicRepComb_mul_trace (n m : Fin 3 → ℝ) :
    (cyclicRepComb n * cyclicRepComb m).trace =
      (-2 * (n 0 * m 0 + n 1 * m 1 + n 2 * m 2) : ℂ) := by
  rw [cyclicRepComb_mul, trace_add, trace_neg, cyclicRepComb_trace]
  have hI : (((n 0 * m 0 + n 1 * m 1 + n 2 * m 2 : ℂ) •
      (1 : Matrix (Fin 2) (Fin 2) ℂ)).trace) =
      (2 * (n 0 * m 0 + n 1 * m 1 + n 2 * m 2) : ℂ) := by
    rw [trace_smul, trace_one]
    simp [Fintype.card_fin]
    ring
  rw [hI]
  ring

/-- Character of a composite: \(\frac12\operatorname{Tr}(R(\beta)R(\gamma))=
\cos(\theta/2)\cos(\phi/2)-(\hat n\cdot\hat m)\sin(\theta/2)\sin(\phi/2)\). -/
theorem dualRotorMat_mul_trace (β γ : DualRapidity) :
    (dualRotorMat β * dualRotorMat γ).trace =
      2 * ((Real.cos (‖β‖ / 2) : ℂ) * Real.cos (‖γ‖ / 2) -
        (dualAxisInner β γ : ℂ) * Real.sin (‖β‖ / 2) * Real.sin (‖γ‖ / 2)) := by
  rw [dualRotorMat_cos_sin β, dualRotorMat_cos_sin γ]
  set c1 := Real.cos (‖β‖ / 2)
  set s1 := Real.sin (‖β‖ / 2)
  set c2 := Real.cos (‖γ‖ / 2)
  set s2 := Real.sin (‖γ‖ / 2)
  have hprod :
      (c1 • (1 : Matrix (Fin 2) (Fin 2) ℂ) + s1 • cyclicRepComb (dualAxis β)) *
          (c2 • (1 : Matrix (Fin 2) (Fin 2) ℂ) + s2 • cyclicRepComb (dualAxis γ)) =
        (c1 * c2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) +
          (c1 * s2 : ℝ) • cyclicRepComb (dualAxis γ) +
            (s1 * c2 : ℝ) • cyclicRepComb (dualAxis β) +
              (s1 * s2 : ℝ) •
                (cyclicRepComb (dualAxis β) * cyclicRepComb (dualAxis γ)) := by
    simp only [add_mul, mul_add, smul_mul_smul_matR, Matrix.one_mul, Matrix.mul_one]
    abel
  rw [hprod, trace_add, trace_add, trace_add, trace_real_smul_one,
    trace_real_smul, cyclicRepComb_trace, trace_real_smul, cyclicRepComb_trace,
    trace_real_smul, cyclicRepComb_mul_trace]
  simp only [dualAxisInner, mul_zero, add_zero, Complex.ofReal_mul, Complex.ofReal_add]
  ring

/-- Relative-rotor character records the alignment of the two dual axes. -/
theorem dualRotor_relative_trace (βO βA : DualRapidity) :
    ((dualRotorMat βO).conjTranspose * dualRotorMat βA).trace =
      2 * ((Real.cos (‖βO‖ / 2) : ℂ) * Real.cos (‖βA‖ / 2) +
        (dualAxisInner βO βA : ℂ) * Real.sin (‖βO‖ / 2) * Real.sin (‖βA‖ / 2)) := by
  rw [dualRotor_relative_eq_neg_mul, dualRotorMat_mul_trace, norm_neg,
    dualAxisInner_neg_left]
  simp [Complex.ofReal_neg]

/-- \(\pi\) dual rotations about \(x\) and \(z\) compose to \(-\Gamma_y\). -/
theorem dualRotorMat_pi_compose :
    dualRotorMat (EuclideanSpace.single 0 Real.pi) *
        dualRotorMat (EuclideanSpace.single 2 Real.pi) =
      -cyclicRep 1 := by
  rw [dualRotorMat_axis0_pi, dualRotorMat_axis2_pi, cyclicRep_zero_mul_two]

/-- Group commutator of perpendicular \(\pi\) dual rotations is the double-cover element \(-I\). -/
theorem dualRotorMat_axes_group_commutator :
    dualRotorMat (EuclideanSpace.single 0 Real.pi) *
        dualRotorMat (EuclideanSpace.single 2 Real.pi) *
          (dualRotorMat (EuclideanSpace.single 0 Real.pi)).conjTranspose *
            (dualRotorMat (EuclideanSpace.single 2 Real.pi)).conjTranspose =
      -1 := by
  rw [dualRotorMat_axis0_pi, dualRotorMat_axis2_pi,
    cyclicRep_conjTranspose, cyclicRep_conjTranspose]
  simp only [mul_neg, neg_mul, neg_neg]
  calc cyclicRep 0 * cyclicRep 2 * cyclicRep 0 * cyclicRep 2
      = -cyclicRep 1 * cyclicRep 0 * cyclicRep 2 := by
        rw [cyclicRep_zero_mul_two]
    _ = -(cyclicRep 1 * cyclicRep 0) * cyclicRep 2 := by
        simp [mul_assoc]
    _ = -(-cyclicRep 2) * cyclicRep 2 := by
        rw [cyclicRep_one_mul_zero]
    _ = cyclicRep 2 * cyclicRep 2 := by
        simp
    _ = -1 := cyclicRep_sq 2

end Logic

end DstDiophantine
