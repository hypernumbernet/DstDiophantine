import DstDiophantine.Gravity.GravitonQuantum
import DstDiophantine.Logic.Quantum.QuantumLogic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option linter.style.native false

/-!
# Gravitons on the quantum logic of one device

The computational observable has two atoms, the line of `spinUp` and its
negation, the line of the orthogonal outcome. An axial graviton maps each
atom into itself. The carrier of an eigenstate stays in the original atom,
and the device error is zero.

A transverse graviton of angle strictly between `0` and `π` puts the carrier
on a third atom. That atom is neither computational line, it meets each of
them at the bottom, and it is not orthogonal to the original line. The
device can still record the negation. The carrier has not become it.

The same axial graviton, taken after the transverse step, leaves the device
error unchanged and moves the carrier onto a different atom. Taken before
it, the atom is the one the transverse step determines. The proposition
depends on the order. The device error does not.

One graviton about each of two transverse axes: the two orders determine
distinct atoms and share one device error. That error is exactly half the
error of the same two gravitons aligned on one transverse axis, and it is
strictly less than twice the error of one. The height of the perpendicular
pair is exactly twice the height of one. For `N ≥ 8` the ratio of the two
device errors equals the ratio of the two expressed heights.

## Not claimed

* That the device error is the proposition the carrier satisfies.
* A laboratory error rate. The integer `N` is not fixed.
* That the order of the rotors is seen by the height. The height does not
  see it. The atoms do.
-/

noncomputable section

namespace DstDiophantine.Gravity.GravitonLogic

open DstDiophantine.Logic
open DstDiophantine.Gravity.GravitonQuantum
open Submodule Module Invariant
open scoped InnerProductSpace

/-- Phase written by one axial dual rotor on the computational eigenstate. -/
def axialFactor (φ : ℝ) : ℂ :=
  (Real.cos (φ / 2) : ℂ) - Complex.I * (Real.sin (φ / 2) : ℂ)

/-- Carrier after one transverse dual rotor of angle `θ`. -/
def afterTransverse (θ : ℝ) : DualSpinor :=
  applyMat (dualRotorMat (EuclideanSpace.single (0 : Fin 3) θ)) spinUp

/-- Transverse angle `θ`, then the other transverse axis by `φ`. -/
def afterPerp (θ φ : ℝ) : DualSpinor :=
  applyMat (dualRotorMat (EuclideanSpace.single (1 : Fin 3) φ)) (afterTransverse θ)

/-- The other transverse axis by `φ`, then the first by `θ`. -/
def afterPerpRev (θ φ : ℝ) : DualSpinor :=
  applyMat (dualRotorMat (EuclideanSpace.single (0 : Fin 3) θ))
    (applyMat (dualRotorMat (EuclideanSpace.single (1 : Fin 3) φ)) spinUp)

/-- Transverse angle `θ`, then the eigenaxis by `φ`. -/
def afterTransverseAxial (θ φ : ℝ) : DualSpinor :=
  applyMat (dualRotorMat (EuclideanSpace.single (2 : Fin 3) φ)) (afterTransverse θ)

/-- The eigenaxis by `φ`, then the transverse axis by `θ`. -/
def afterAxialTransverse (θ φ : ℝ) : DualSpinor :=
  applyMat (dualRotorMat (EuclideanSpace.single (0 : Fin 3) θ))
    (applyMat (dualRotorMat (EuclideanSpace.single (2 : Fin 3) φ)) spinUp)

/-- The atom occupied by a nonzero carrier. -/
def atomOf (u : DualSpinor) : QProp := ℂ ∙ u

/-- Error a computational device records on a carrier. -/
def deviceError (u : DualSpinor) : ℝ :=
  1 - computationalWeight u

theorem spinUp_eq_e0 : spinUp = e0 := rfl

theorem mem_lineE0_iff (v : DualSpinor) : v ∈ lineE0 ↔ v 1 = 0 := by
  constructor
  · intro hv
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hv
    simp [e0, PiLp.smul_apply]
  · intro hv
    refine Submodule.mem_span_singleton.mpr ⟨v 0, ?_⟩
    ext i
    fin_cases i
    · simp [e0, PiLp.smul_apply]
    · simp [e0, PiLp.smul_apply, hv]

theorem mem_lineE1_iff (v : DualSpinor) : v ∈ lineE1 ↔ v 0 = 0 := by
  constructor
  · intro hv
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hv
    simp [e1, PiLp.smul_apply]
  · intro hv
    refine Submodule.mem_span_singleton.mpr ⟨v 1, ?_⟩
    ext i
    fin_cases i
    · simp [e1, PiLp.smul_apply, hv]
    · simp [e1, PiLp.smul_apply]

/-- The orthogonal outcome is the negation of the computational atom. -/
theorem lineE1_eq_negation : lineE1 = qNot lineE0 := by
  have hle : lineE1 ≤ lineE0ᗮ := by
    intro y hy
    rw [Submodule.mem_orthogonal']
    intro x hx
    exact lineE0_isOrtho_lineE1 hx y hy
  have hdim : Module.finrank ℂ lineE0ᗮ = 1 := by
    have h := Submodule.finrank_add_finrank_orthogonal (K := lineE0)
    rw [dualSpinor_finrank, lineE0_finrank] at h
    omega
  exact eq_of_le_of_finrank_eq hle (lineE1_finrank.trans hdim.symm)

private theorem axis0_entry (θ : ℝ) :
    dualRotorMat (EuclideanSpace.single (0 : Fin 3) θ) 0 0 = (Real.cos (θ / 2) : ℂ) ∧
      dualRotorMat (EuclideanSpace.single (0 : Fin 3) θ) 0 1 =
        -Complex.I * (Real.sin (θ / 2) : ℂ) ∧
      dualRotorMat (EuclideanSpace.single (0 : Fin 3) θ) 1 0 =
        -Complex.I * (Real.sin (θ / 2) : ℂ) ∧
      dualRotorMat (EuclideanSpace.single (0 : Fin 3) θ) 1 1 =
        (Real.cos (θ / 2) : ℂ) := by
  have hR := dualRotorMat_axis0_rodrigues θ
  have hC := cyclicRep_zero_eq
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℂ => A 0 0) hR
    simpa [hC, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply] using h
  · have h := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℂ => A 0 1) hR
    simpa [hC, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, mul_comm] using h
  · have h := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℂ => A 1 0) hR
    simpa [hC, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, mul_comm] using h
  · have h := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℂ => A 1 1) hR
    simpa [hC, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply] using h

private theorem cyclicRep_one_entries :
    cyclicRep 1 0 0 = 0 ∧ cyclicRep 1 0 1 = -1 ∧
      cyclicRep 1 1 0 = 1 ∧ cyclicRep 1 1 1 = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold cyclicRep pauli pauliY
    simp [Matrix.smul_apply]
  · unfold cyclicRep pauli pauliY
    simp [Matrix.smul_apply, neg_mul, Complex.I_mul_I]
  · unfold cyclicRep pauli pauliY
    simp [Matrix.smul_apply, neg_mul, Complex.I_mul_I]
  · unfold cyclicRep pauli pauliY
    simp [Matrix.smul_apply]

private theorem axis1_entry (θ : ℝ) :
    dualRotorMat (EuclideanSpace.single (1 : Fin 3) θ) 0 0 = (Real.cos (θ / 2) : ℂ) ∧
      dualRotorMat (EuclideanSpace.single (1 : Fin 3) θ) 0 1 =
        -((Real.sin (θ / 2) : ℂ)) ∧
      dualRotorMat (EuclideanSpace.single (1 : Fin 3) θ) 1 0 =
        (Real.sin (θ / 2) : ℂ) ∧
      dualRotorMat (EuclideanSpace.single (1 : Fin 3) θ) 1 1 =
        (Real.cos (θ / 2) : ℂ) := by
  have hR := dualRotorMat_axis1_rodrigues θ
  have hC := cyclicRep_one_entries
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℂ => A 0 0) hR
    simpa [hC.1, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply] using h
  · have h := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℂ => A 0 1) hR
    simpa [hC.2.1, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply] using h
  · have h := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℂ => A 1 0) hR
    simpa [hC.2.2.1, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply] using h
  · have h := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℂ => A 1 1) hR
    simpa [hC.2.2.2, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply] using h

private theorem axis2_entry (θ : ℝ) :
    dualRotorMat (EuclideanSpace.single (2 : Fin 3) θ) 0 0 = axialFactor θ ∧
      dualRotorMat (EuclideanSpace.single (2 : Fin 3) θ) 0 1 = 0 ∧
      dualRotorMat (EuclideanSpace.single (2 : Fin 3) θ) 1 0 = 0 ∧
      dualRotorMat (EuclideanSpace.single (2 : Fin 3) θ) 1 1 =
        (Real.cos (θ / 2) : ℂ) + Complex.I * (Real.sin (θ / 2) : ℂ) := by
  have hR := dualRotorMat_axis2_rodrigues θ
  have hC := cyclicRep_two_eq
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℂ => A 0 0) hR
    unfold axialFactor
    simpa [hC, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, sub_eq_add_neg,
      mul_comm] using h
  · have h := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℂ => A 0 1) hR
    simpa [hC, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply] using h
  · have h := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℂ => A 1 0) hR
    simpa [hC, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply] using h
  · have h := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℂ => A 1 1) hR
    simpa [hC, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, mul_comm] using h

theorem transverse_coord (θ : ℝ) :
    afterTransverse θ 0 = (Real.cos (θ / 2) : ℂ) ∧
      afterTransverse θ 1 = -Complex.I * (Real.sin (θ / 2) : ℂ) := by
  have hA := axis0_entry θ
  refine ⟨?_, ?_⟩
  · rw [afterTransverse, applyMat_apply, Fin.sum_univ_two, spinUp_zero, spinUp_one, hA.1]
    simp
  · rw [afterTransverse, applyMat_apply, Fin.sum_univ_two, spinUp_zero, spinUp_one, hA.2.2.1]
    simp

theorem axial_on_eigen (φ : ℝ) :
    applyMat (dualRotorMat (EuclideanSpace.single (2 : Fin 3) φ)) spinUp =
      axialFactor φ • spinUp := by
  have hA := axis2_entry φ
  ext i
  fin_cases i
  · simp [applyMat_apply, Fin.sum_univ_two, spinUp_zero, spinUp_one, hA.1, axialFactor,
      PiLp.smul_apply]
  · simp [applyMat_apply, Fin.sum_univ_two, spinUp_zero, spinUp_one, hA.2.2.1, PiLp.smul_apply]

private theorem axialFactor_re (φ : ℝ) : (axialFactor φ).re = Real.cos (φ / 2) := by
  unfold axialFactor
  simp only [Complex.sub_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, zero_mul, sub_zero]

private theorem axialFactor_im (φ : ℝ) : (axialFactor φ).im = -Real.sin (φ / 2) := by
  unfold axialFactor
  simp only [Complex.sub_im, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero]
  ring

theorem axialFactor_normSq (φ : ℝ) : Complex.normSq (axialFactor φ) = 1 := by
  rw [Complex.normSq_apply, axialFactor_re, axialFactor_im]
  have hcs := Real.cos_sq_add_sin_sq (φ / 2)
  ring_nf at hcs ⊢
  exact hcs

theorem axialFactor_ne_zero (φ : ℝ) : axialFactor φ ≠ 0 := by
  intro h
  have hsq := axialFactor_normSq φ
  rw [h, Complex.normSq_zero] at hsq
  exact zero_ne_one hsq

theorem axial_preserves_line (φ : ℝ) {v : DualSpinor} (hv : v ∈ lineE0) :
    applyMat (dualRotorMat (EuclideanSpace.single (2 : Fin 3) φ)) v ∈ lineE0 := by
  rw [mem_lineE0_iff] at hv ⊢
  have hA := axis2_entry φ
  rw [applyMat_apply, Fin.sum_univ_two, hv, hA.2.2.1]
  simp

theorem axial_preserves_negation (φ : ℝ) {v : DualSpinor} (hv : v ∈ lineE1) :
    applyMat (dualRotorMat (EuclideanSpace.single (2 : Fin 3) φ)) v ∈ lineE1 := by
  rw [mem_lineE1_iff] at hv ⊢
  have hA := axis2_entry φ
  rw [applyMat_apply, Fin.sum_univ_two, hv, hA.2.1]
  simp

/-- An axial graviton leaves the eigenstate in its proposition and out of the negation.
The device records no error. -/
theorem axial_no_logical_error (φ : ℝ) :
    applyMat (dualRotorMat (EuclideanSpace.single (2 : Fin 3) φ)) spinUp ∈ lineE0 ∧
      applyMat (dualRotorMat (EuclideanSpace.single (2 : Fin 3) φ)) spinUp ∉ qNot lineE0 ∧
      deviceError (applyMat (dualRotorMat (EuclideanSpace.single (2 : Fin 3) φ)) spinUp) =
        0 := by
  have hup : spinUp ∈ lineE0 := by
    rw [spinUp_eq_e0, mem_lineE0_iff]
    simp [e0]
  refine ⟨axial_preserves_line φ hup, ?_, ?_⟩
  · rw [← lineE1_eq_negation, mem_lineE1_iff]
    have hA := axis2_entry φ
    rw [applyMat_apply, Fin.sum_univ_two, spinUp_zero, spinUp_one, hA.1]
    simp only [mul_one, mul_zero, add_zero]
    intro h
    have hns := axialFactor_normSq φ
    rw [h, Complex.normSq_zero] at hns
    exact zero_ne_one hns
  · rw [deviceError, axialStep_defect]

theorem weight_eq_coord {u : DualSpinor} (_hu : ‖u‖ = 1) :
    computationalWeight u = ‖u 0‖ ^ 2 := by
  have hsum : ‖u 0‖ ^ 2 + ‖u 1‖ ^ 2 = ‖u‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
  unfold computationalWeight
  rw [spinVec_coord_two]
  have hsplit : ‖u‖ ^ 2 + (‖u 0‖ ^ 2 - ‖u 1‖ ^ 2) = 2 * ‖u 0‖ ^ 2 := by
    linarith
  rw [hsplit]
  field_simp

theorem weight_after_rotor (β : DualRapidity) :
    computationalWeight (applyMat (dualRotorMat β) spinUp) =
      ‖applyMat (dualRotorMat β) spinUp 0‖ ^ 2 := by
  have hsq := norm_applyMat_dualRotor_sq β spinUp
  rw [spinUp_norm_sq] at hsq
  have hnorm : ‖applyMat (dualRotorMat β) spinUp‖ = 1 := by
    nlinarith [norm_nonneg (applyMat (dualRotorMat β) spinUp), hsq]
  exact weight_eq_coord hnorm

private theorem halfAngle_mem {θ : ℝ} (h0 : 0 < θ) (hπ : θ < Real.pi) :
    θ / 2 ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
  refine ⟨?_, ?_⟩
  · linarith [Real.pi_pos]
  · linarith

private theorem transverse_ne_zero {θ : ℝ} (h0 : 0 < θ) (hπ : θ < Real.pi) :
    afterTransverse θ ≠ 0 := by
  intro h
  have hc := (transverse_coord θ).1
  rw [h] at hc
  simp only [PiLp.zero_apply] at hc
  have hpos : 0 < Real.cos (θ / 2) := Real.cos_pos_of_mem_Ioo (halfAngle_mem h0 hπ)
  exact absurd hc.symm (Complex.ofReal_ne_zero.mpr (ne_of_gt hpos))

private theorem third_not_ortho {θ : ℝ} (h0 : 0 < θ) (hπ : θ < Real.pi) :
    ¬ atomOf (afterTransverse θ) ⟂ lineE0 := by
  intro horth
  have hinner := horth (Submodule.mem_span_singleton_self (afterTransverse θ)) e0
    (Submodule.mem_span_singleton_self e0)
  have hcoord := (transverse_coord θ).1
  have hprod : ⟪e0, afterTransverse θ⟫_ℂ = afterTransverse θ 0 := by
    simp [e0, EuclideanSpace.inner_single_left]
  rw [hprod, hcoord] at hinner
  have hpos : 0 < Real.cos (θ / 2) := Real.cos_pos_of_mem_Ioo (halfAngle_mem h0 hπ)
  exact Complex.ofReal_ne_zero.mpr (ne_of_gt hpos) hinner

private theorem meet_bot_of_outside {u : DualSpinor} {L : QProp}
    (hout : u ∉ L) : (ℂ ∙ u) ⊓ L = ⊥ := by
  refine eq_bot_iff.mpr ?_
  intro x hx
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx.1
  by_cases hc : c = 0
  · simp [hc]
  · exfalso
    have hinv : u = c⁻¹ • (c • u) := by
      rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
    rw [hinv] at hout
    exact hout (Submodule.smul_mem _ _ hx.2)

/-- A transverse graviton of angle in `(0, π)` occupies a third atom. The device
error is the Born weight of the negation, which the carrier does not satisfy. -/
theorem transverse_third_atom {θ : ℝ} (h0 : 0 < θ) (hπ : θ < Real.pi) :
    afterTransverse θ ∉ lineE0 ∧
      afterTransverse θ ∉ qNot lineE0 ∧
      atomOf (afterTransverse θ) ≠ lineE0 ∧
      atomOf (afterTransverse θ) ≠ qNot lineE0 ∧
      ¬ atomOf (afterTransverse θ) ⟂ lineE0 ∧
      atomOf (afterTransverse θ) ⊓ lineE0 = ⊥ ∧
      atomOf (afterTransverse θ) ⊓ qNot lineE0 = ⊥ ∧
      deviceError (afterTransverse θ) = Real.sin (θ / 2) ^ 2 := by
  have hcoord := transverse_coord θ
  have hhalf : 0 < θ / 2 := by linarith
  have hsin : 0 < Real.sin (θ / 2) :=
    Real.sin_pos_of_pos_of_lt_pi hhalf (by linarith)
  have hcos : 0 < Real.cos (θ / 2) :=
    Real.cos_pos_of_mem_Ioo (halfAngle_mem h0 hπ)
  have hne0 : afterTransverse θ 0 ≠ 0 := by
    rw [hcoord.1]
    exact Complex.ofReal_ne_zero.mpr (ne_of_gt hcos)
  have hne1 : afterTransverse θ 1 ≠ 0 := by
    rw [hcoord.2]
    exact mul_ne_zero (by simp [Complex.I_ne_zero]) (Complex.ofReal_ne_zero.mpr (ne_of_gt hsin))
  have hout0 : afterTransverse θ ∉ lineE0 := by
    rw [mem_lineE0_iff]
    exact hne1
  have hout1 : afterTransverse θ ∉ lineE1 := by
    rw [mem_lineE1_iff]
    exact hne0
  refine ⟨hout0, by rwa [← lineE1_eq_negation], ?_, ?_, third_not_ortho h0 hπ, ?_, ?_, ?_⟩
  · intro hspan
    have hmem : afterTransverse θ ∈ lineE0 := by
      rw [← hspan]
      exact Submodule.mem_span_singleton_self _
    exact hout0 hmem
  · intro hspan
    have hmem : afterTransverse θ ∈ qNot lineE0 := by
      rw [← hspan]
      exact Submodule.mem_span_singleton_self _
    rw [← lineE1_eq_negation] at hmem
    exact hout1 hmem
  · exact meet_bot_of_outside hout0
  · rw [← lineE1_eq_negation]
    exact meet_bot_of_outside hout1
  · have hu : ‖afterTransverse θ‖ = 1 := by
      have hsq := norm_applyMat_dualRotor_sq (EuclideanSpace.single (0 : Fin 3) θ) spinUp
      rw [spinUp_norm_sq] at hsq
      have hsq' : ‖afterTransverse θ‖ ^ 2 = 1 := by simpa [afterTransverse] using hsq
      nlinarith [norm_nonneg (afterTransverse θ)]
    rw [deviceError, weight_eq_coord hu, hcoord.1]
    have hns : ‖(Real.cos (θ / 2) : ℂ)‖ ^ 2 = Real.cos (θ / 2) ^ 2 := by
      rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
    rw [hns]
    have htrig := Real.cos_sq_add_sin_sq (θ / 2)
    linarith

theorem transverse_step_third_atom {N : ℕ} (hN : 3 ≤ N) :
    afterTransverse (stepAngle N) ∉ lineE0 ∧
      afterTransverse (stepAngle N) ∉ qNot lineE0 ∧
      atomOf (afterTransverse (stepAngle N)) ≠ lineE0 ∧
      atomOf (afterTransverse (stepAngle N)) ≠ qNot lineE0 ∧
      deviceError (afterTransverse (stepAngle N)) = Real.sin (Real.pi / (N : ℝ)) ^ 2 := by
  have hpos : 0 < N := lt_of_lt_of_le (by decide : 0 < 3) hN
  have hθ : 0 < stepAngle N := stepAngle_pos hpos
  have hπ : stepAngle N < Real.pi := by
    unfold stepAngle
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hpos
    rw [div_lt_iff₀ hN0]
    have h3 : (2 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le (by decide : 2 < 3) hN)
    nlinarith [Real.pi_pos]
  have h := transverse_third_atom hθ hπ
  refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, ?_⟩
  rw [h.2.2.2.2.2.2.2, stepAngle_half hpos]

private theorem span_smul {c : ℂ} {u : DualSpinor} (hc : c ≠ 0) :
    (ℂ ∙ (c • u)) = (ℂ ∙ u) := by
  refine le_antisymm ?_ ?_
  · rw [Submodule.span_singleton_le_iff_mem]
    exact Submodule.smul_mem _ c (Submodule.mem_span_singleton_self u)
  · rw [Submodule.span_singleton_le_iff_mem]
    have hmem : c⁻¹ • (c • u) ∈ ℂ ∙ (c • u) :=
      Submodule.smul_mem _ c⁻¹ (Submodule.mem_span_singleton_self (c • u))
    have heq : c⁻¹ • (c • u) = u := by
      rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
    rwa [heq] at hmem

theorem axial_before_same_atom (θ φ : ℝ) :
    atomOf (afterAxialTransverse θ φ) = atomOf (afterTransverse θ) := by
  have hax := axial_on_eigen φ
  have hlin : afterAxialTransverse θ φ = axialFactor φ • afterTransverse θ := by
    unfold afterAxialTransverse afterTransverse
    rw [hax, applyMat_smul]
  rw [hlin]
  exact span_smul (axialFactor_ne_zero φ)

private theorem axial_after_coord (θ φ : ℝ) :
    afterTransverseAxial θ φ 0 = axialFactor φ * afterTransverse θ 0 ∧
      afterTransverseAxial θ φ 1 =
        ((Real.cos (φ / 2) : ℂ) + Complex.I * (Real.sin (φ / 2) : ℂ)) *
          afterTransverse θ 1 := by
  have hA := axis2_entry φ
  refine ⟨?_, ?_⟩
  · rw [afterTransverseAxial, applyMat_apply, Fin.sum_univ_two, hA.1, hA.2.1]
    simp
  · rw [afterTransverseAxial, applyMat_apply, Fin.sum_univ_two, hA.2.2.1, hA.2.2.2]
    simp

private theorem wedge_axial_phase (α β : ℝ) :
    ((Real.cos α : ℂ) * (((Real.cos β : ℂ) + Complex.I * Real.sin β) *
        (-Complex.I * Real.sin α)) -
      (-Complex.I * Real.sin α) * (((Real.cos β : ℂ) - Complex.I * Real.sin β) *
        Real.cos α)) =
      (2 : ℂ) * Real.sin β * Real.sin α * Real.cos α := by
  ring_nf
  rw [Complex.I_sq]
  ring

/-- After a transverse step, an axial graviton moves the atom and leaves the
device error unchanged. Before it, the atom is the transverse one. -/
theorem axial_order_changes_atom {θ φ : ℝ}
    (hθ0 : 0 < θ) (hθπ : θ < Real.pi) (hφ0 : 0 < φ) (hφ2 : φ < 2 * Real.pi) :
    atomOf (afterAxialTransverse θ φ) = atomOf (afterTransverse θ) ∧
      atomOf (afterTransverseAxial θ φ) ≠ atomOf (afterTransverse θ) ∧
      deviceError (afterTransverseAxial θ φ) = deviceError (afterTransverse θ) ∧
      deviceError (afterAxialTransverse θ φ) = deviceError (afterTransverse θ) := by
  refine ⟨axial_before_same_atom θ φ, ?_, ?_, ?_⟩
  · intro hspan
    have ht := transverse_coord θ
    have ha := axial_after_coord θ φ
    have hmem : afterTransverseAxial θ φ ∈ atomOf (afterTransverse θ) := by
      rw [← hspan]
      exact Submodule.mem_span_singleton_self _
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
    have h0 := congrArg (fun v : DualSpinor => v 0) hc
    have h1 := congrArg (fun v : DualSpinor => v 1) hc
    simp only [PiLp.smul_apply, smul_eq_mul] at h0 h1
    have hwedge :
        afterTransverse θ 0 * afterTransverseAxial θ φ 1 -
          afterTransverse θ 1 * afterTransverseAxial θ φ 0 = 0 := by
      rw [← h1, ← h0]
      ring
    rw [ht.1, ht.2, ha.1, ha.2, ht.1, ht.2] at hwedge
    have hform := wedge_axial_phase (θ / 2) (φ / 2)
    have hfac : (2 : ℂ) * (Real.sin (φ / 2) : ℂ) * (Real.sin (θ / 2) : ℂ) *
        (Real.cos (θ / 2) : ℂ) = 0 := by
      have hsub : axialFactor φ = (Real.cos (φ / 2) : ℂ) - Complex.I * (Real.sin (φ / 2) : ℂ) := rfl
      rw [hsub] at hwedge
      exact hform.symm.trans hwedge
    have hsinφ : (Real.sin (φ / 2) : ℂ) ≠ 0 := by
      exact Complex.ofReal_ne_zero.mpr (ne_of_gt
        (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)))
    have hsinθ : (Real.sin (θ / 2) : ℂ) ≠ 0 := by
      exact Complex.ofReal_ne_zero.mpr (ne_of_gt
        (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)))
    have hcosθ : (Real.cos (θ / 2) : ℂ) ≠ 0 := by
      exact Complex.ofReal_ne_zero.mpr (ne_of_gt
        (Real.cos_pos_of_mem_Ioo (halfAngle_mem hθ0 hθπ)))
    exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hsinφ) hsinθ) hcosθ) hfac
  · have hnorm : ‖afterTransverseAxial θ φ‖ = 1 := by
      have hsq := norm_applyMat_dualRotor_sq (EuclideanSpace.single (2 : Fin 3) φ)
        (afterTransverse θ)
      have hbase := norm_applyMat_dualRotor_sq (EuclideanSpace.single (0 : Fin 3) θ) spinUp
      rw [spinUp_norm_sq] at hbase
      have hsq' : ‖afterTransverseAxial θ φ‖ ^ 2 = 1 := by
        simpa [afterTransverseAxial, afterTransverse] using hsq.trans hbase
      nlinarith [norm_nonneg (afterTransverseAxial θ φ)]
    have hbase : ‖afterTransverse θ‖ = 1 := by
      have hsq := norm_applyMat_dualRotor_sq (EuclideanSpace.single (0 : Fin 3) θ) spinUp
      rw [spinUp_norm_sq] at hsq
      have hsq' : ‖afterTransverse θ‖ ^ 2 = 1 := by simpa [afterTransverse] using hsq
      nlinarith [norm_nonneg (afterTransverse θ)]
    rw [deviceError, deviceError, weight_eq_coord hnorm, weight_eq_coord hbase]
    have ha := (axial_after_coord θ φ).1
    have hone : ‖axialFactor φ‖ = 1 := by
      have hsq : ‖axialFactor φ‖ ^ 2 = 1 := by
        rw [← Complex.normSq_eq_norm_sq, axialFactor_normSq]
      nlinarith [norm_nonneg (axialFactor φ)]
    rw [ha, norm_mul, hone]
    ring
  · have hax := axial_on_eigen φ
    have hlin : afterAxialTransverse θ φ = axialFactor φ • afterTransverse θ := by
      unfold afterAxialTransverse afterTransverse
      rw [hax, applyMat_smul]
    have hnorm : ‖afterAxialTransverse θ φ‖ = 1 := by
      rw [hlin, norm_smul]
      have hone : ‖axialFactor φ‖ = 1 := by
        have hsq : ‖axialFactor φ‖ ^ 2 = 1 := by
          rw [← Complex.normSq_eq_norm_sq, axialFactor_normSq]
        nlinarith [norm_nonneg (axialFactor φ)]
      have hbase : ‖afterTransverse θ‖ = 1 := by
        have hsq := norm_applyMat_dualRotor_sq (EuclideanSpace.single (0 : Fin 3) θ) spinUp
        rw [spinUp_norm_sq] at hsq
        have hsq' : ‖afterTransverse θ‖ ^ 2 = 1 := by simpa [afterTransverse] using hsq
        nlinarith [norm_nonneg (afterTransverse θ)]
      rw [hone, hbase]
      norm_num
    have hbase : ‖afterTransverse θ‖ = 1 := by
      have hsq := norm_applyMat_dualRotor_sq (EuclideanSpace.single (0 : Fin 3) θ) spinUp
      rw [spinUp_norm_sq] at hsq
      have hsq' : ‖afterTransverse θ‖ ^ 2 = 1 := by simpa [afterTransverse] using hsq
      nlinarith [norm_nonneg (afterTransverse θ)]
    rw [deviceError, deviceError, weight_eq_coord hnorm, weight_eq_coord hbase, hlin]
    simp only [PiLp.smul_apply, smul_eq_mul, norm_mul]
    have hone : ‖axialFactor φ‖ = 1 := by
      have hsq : ‖axialFactor φ‖ ^ 2 = 1 := by
        rw [← Complex.normSq_eq_norm_sq, axialFactor_normSq]
      nlinarith [norm_nonneg (axialFactor φ)]
    rw [hone]
    ring

private theorem perp_coord (θ φ : ℝ) :
    afterPerp θ φ 0 =
      (Real.cos (φ / 2) : ℂ) * (Real.cos (θ / 2) : ℂ) +
        Complex.I * (Real.sin (φ / 2) : ℂ) * (Real.sin (θ / 2) : ℂ) ∧
      afterPerp θ φ 1 =
        (Real.sin (φ / 2) : ℂ) * (Real.cos (θ / 2) : ℂ) -
          Complex.I * (Real.cos (φ / 2) : ℂ) * (Real.sin (θ / 2) : ℂ) := by
  have ht := transverse_coord θ
  have hA := axis1_entry φ
  refine ⟨?_, ?_⟩
  · rw [afterPerp, applyMat_apply, Fin.sum_univ_two, ht.1, ht.2, hA.1, hA.2.1]
    ring
  · rw [afterPerp, applyMat_apply, Fin.sum_univ_two, ht.1, ht.2, hA.2.2.1, hA.2.2.2]
    ring

private theorem axis1_on_up (φ : ℝ) :
    applyMat (dualRotorMat (EuclideanSpace.single (1 : Fin 3) φ)) spinUp 0 =
      (Real.cos (φ / 2) : ℂ) ∧
      applyMat (dualRotorMat (EuclideanSpace.single (1 : Fin 3) φ)) spinUp 1 =
        (Real.sin (φ / 2) : ℂ) := by
  have hA := axis1_entry φ
  refine ⟨?_, ?_⟩
  · rw [applyMat_apply, Fin.sum_univ_two, spinUp_zero, spinUp_one, hA.1]
    simp
  · rw [applyMat_apply, Fin.sum_univ_two, spinUp_zero, spinUp_one, hA.2.2.1]
    simp

private theorem perpRev_coord (θ φ : ℝ) :
    afterPerpRev θ φ 0 =
      (Real.cos (θ / 2) : ℂ) * (Real.cos (φ / 2) : ℂ) -
        Complex.I * (Real.sin (θ / 2) : ℂ) * (Real.sin (φ / 2) : ℂ) ∧
      afterPerpRev θ φ 1 =
        (Real.cos (θ / 2) : ℂ) * (Real.sin (φ / 2) : ℂ) -
          Complex.I * (Real.sin (θ / 2) : ℂ) * (Real.cos (φ / 2) : ℂ) := by
  have hy := axis1_on_up φ
  have hA := axis0_entry θ
  refine ⟨?_, ?_⟩
  · rw [afterPerpRev, applyMat_apply, Fin.sum_univ_two, hy.1, hy.2, hA.1, hA.2.1]
    ring
  · rw [afterPerpRev, applyMat_apply, Fin.sum_univ_two, hy.1, hy.2, hA.2.2.1, hA.2.2.2]
    ring

private theorem normSq_rect (x y : ℝ) :
    ‖(x : ℂ) + Complex.I * (y : ℂ)‖ ^ 2 = x ^ 2 + y ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
    Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero,
    zero_add]
  ring

private theorem perp_weight (θ φ : ℝ) :
    computationalWeight (afterPerp θ φ) =
      Real.cos (φ / 2) ^ 2 * Real.cos (θ / 2) ^ 2 +
        Real.sin (φ / 2) ^ 2 * Real.sin (θ / 2) ^ 2 := by
  have hnorm : ‖afterPerp θ φ‖ = 1 := by
    have hsq := norm_applyMat_dualRotor_sq (EuclideanSpace.single (1 : Fin 3) φ) (afterTransverse θ)
    have hbase := norm_applyMat_dualRotor_sq (EuclideanSpace.single (0 : Fin 3) θ) spinUp
    rw [spinUp_norm_sq] at hbase
    have hsq' : ‖afterPerp θ φ‖ ^ 2 = 1 := by
      simpa [afterPerp, afterTransverse] using hsq.trans hbase
    nlinarith [norm_nonneg (afterPerp θ φ)]
  rw [weight_eq_coord hnorm, (perp_coord θ φ).1, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
    Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add, sub_zero]
  ring

private theorem perpRev_weight (θ φ : ℝ) :
    computationalWeight (afterPerpRev θ φ) =
      Real.cos (θ / 2) ^ 2 * Real.cos (φ / 2) ^ 2 +
        Real.sin (θ / 2) ^ 2 * Real.sin (φ / 2) ^ 2 := by
  have hnorm : ‖afterPerpRev θ φ‖ = 1 := by
    have hsq := norm_applyMat_dualRotor_sq (EuclideanSpace.single (0 : Fin 3) θ)
      (applyMat (dualRotorMat (EuclideanSpace.single (1 : Fin 3) φ)) spinUp)
    have hbase := norm_applyMat_dualRotor_sq (EuclideanSpace.single (1 : Fin 3) φ) spinUp
    rw [spinUp_norm_sq] at hbase
    have hsq' : ‖afterPerpRev θ φ‖ ^ 2 = 1 := by
      simpa [afterPerpRev] using hsq.trans hbase
    nlinarith [norm_nonneg (afterPerpRev θ φ)]
  rw [weight_eq_coord hnorm, (perpRev_coord θ φ).1, ← Complex.normSq_eq_norm_sq,
    Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
    Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add, sub_zero]
  ring

/-- The two orders of perpendicular gravitons share one device error. -/
theorem perp_orders_same_error (θ φ : ℝ) :
    deviceError (afterPerp θ φ) = deviceError (afterPerpRev θ φ) := by
  rw [deviceError, deviceError, perp_weight, perpRev_weight]
  ring

private theorem perp_wedge (α β : ℝ) :
    ((Real.cos β : ℂ) * Real.cos α + Complex.I * Real.sin β * Real.sin α) *
        ((Real.cos α : ℂ) * Real.sin β - Complex.I * Real.sin α * Real.cos β) -
      ((Real.sin β : ℂ) * Real.cos α - Complex.I * Real.cos β * Real.sin α) *
        ((Real.cos α : ℂ) * Real.cos β - Complex.I * Real.sin α * Real.sin β) =
      (2 : ℂ) * Complex.I * Real.sin α * Real.sin β *
        ((Real.sin β : ℂ) * Real.cos α - Complex.I * Real.cos β * Real.sin α) := by
  ring_nf

private theorem perp_atom_ne {θ φ : ℝ} (hθ0 : 0 < θ) (hθπ : θ < Real.pi)
    (hφ0 : 0 < φ) (hφπ : φ < Real.pi) :
    atomOf (afterPerp θ φ) ≠ atomOf (afterPerpRev θ φ) := by
  intro hspan
  have hmem : afterPerp θ φ ∈ atomOf (afterPerpRev θ φ) := by
    have hself : afterPerp θ φ ∈ atomOf (afterPerp θ φ) :=
      Submodule.mem_span_singleton_self _
    simpa [hspan] using hself
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
  have h0 := congrArg (fun v : DualSpinor => v 0) hc
  have h1 := congrArg (fun v : DualSpinor => v 1) hc
  simp only [PiLp.smul_apply, smul_eq_mul] at h0 h1
  have hwedge : afterPerp θ φ 0 * afterPerpRev θ φ 1 -
      afterPerp θ φ 1 * afterPerpRev θ φ 0 = 0 := by
    rw [← h0, ← h1]
    ring
  have hu := perp_coord θ φ
  have hw := perpRev_coord θ φ
  rw [hu.1, hu.2, hw.1, hw.2] at hwedge
  have hform := perp_wedge (θ / 2) (φ / 2)
  have hfac : (2 : ℂ) * Complex.I * (Real.sin (θ / 2) : ℂ) * (Real.sin (φ / 2) : ℂ) *
      ((Real.sin (φ / 2) : ℂ) * Real.cos (θ / 2) -
        Complex.I * Real.cos (φ / 2) * Real.sin (θ / 2)) = 0 := by
    exact hform.symm.trans hwedge
  have hsinθ : 0 < Real.sin (θ / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hcosφ : 0 < Real.cos (φ / 2) :=
    Real.cos_pos_of_mem_Ioo (halfAngle_mem hφ0 hφπ)
  have hsinφ : 0 < Real.sin (φ / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hcosθ : 0 < Real.cos (θ / 2) :=
    Real.cos_pos_of_mem_Ioo (halfAngle_mem hθ0 hθπ)
  have him :
      ((Real.sin (φ / 2) : ℂ) * (Real.cos (θ / 2) : ℂ) -
        Complex.I * (Real.cos (φ / 2) : ℂ) * (Real.sin (θ / 2) : ℂ)).im =
        -(Real.cos (φ / 2) * Real.sin (θ / 2)) := by
    simp only [Complex.sub_im, Complex.mul_im, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, add_zero, sub_zero, zero_mul]
    ring
  have hu1 : afterPerp θ φ 1 ≠ 0 := by
    intro hzero
    have him0 : (afterPerp θ φ 1).im = 0 := by simp [hzero]
    rw [hu.2, him] at him0
    exact neg_ne_zero.mpr (mul_ne_zero (ne_of_gt hcosφ) (ne_of_gt hsinθ)) him0
  have hI : (2 : ℂ) * Complex.I ≠ 0 := by simp [Complex.I_ne_zero]
  have hsinθC : (Real.sin (θ / 2) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hsinθ)
  have hsinφC : (Real.sin (φ / 2) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hsinφ)
  have hsecond : ((Real.sin (φ / 2) : ℂ) * Real.cos (θ / 2) -
      Complex.I * Real.cos (φ / 2) * Real.sin (θ / 2)) ≠ 0 := by
    rw [← hu.2]
    exact hu1
  exact (mul_ne_zero (mul_ne_zero (mul_ne_zero hI hsinθC) hsinφC) hsecond) hfac

private theorem perp_error_trig (θ : ℝ) :
    deviceError (afterPerp θ θ) = (1 / 2) * Real.sin θ ^ 2 := by
  rw [deviceError, perp_weight]
  set c : ℝ := Real.cos (θ / 2)
  set s : ℝ := Real.sin (θ / 2)
  have hc : c ^ 2 + s ^ 2 = 1 := by
    simp [c, s]
  have hs : Real.sin θ = 2 * s * c := by
    simpa [c, s, show 2 * (θ / 2) = θ by ring] using Real.sin_two_mul (θ / 2)
  rw [hs]
  have hpoly : (c ^ 2 + s ^ 2) ^ 2 - (c ^ 4 + s ^ 4) = 2 * c ^ 2 * s ^ 2 := by ring
  rw [hc] at hpoly
  have hleft : (1 : ℝ) - (c ^ 2 * c ^ 2 + s ^ 2 * s ^ 2) = 2 * s ^ 2 * c ^ 2 := by
    have hone : (1 : ℝ) ^ 2 = 1 := by norm_num
    linarith
  have hright : (1 / 2) * (2 * s * c) ^ 2 = 2 * s ^ 2 * c ^ 2 := by ring
  linarith

private theorem aligned_error_trig {θ : ℝ} (hθ : 0 < θ) :
    deviceError (afterTransverse (2 * θ)) = Real.sin θ ^ 2 := by
  have htwo : 0 < 2 * θ := by linarith
  have hw := computationalWeight_eq_cos_sq htwo
  rw [deviceError, afterTransverse, hw]
  have hdouble := Real.cos_sq_add_sin_sq θ
  have hhalf : (2 * θ) / 2 = θ := by ring
  rw [hhalf]
  linarith

/-- Perpendicular gravitons of one angle in `(0, π)` occupy different atoms in the
two orders, and they share a device error. That error is half the error of the
same two gravitons aligned, and strictly less than twice the error of one. -/
theorem perp_device_and_logic {θ : ℝ} (h0 : 0 < θ) (hπ : θ < Real.pi) :
    atomOf (afterPerp θ θ) ≠ atomOf (afterPerpRev θ θ) ∧
      deviceError (afterPerp θ θ) = deviceError (afterPerpRev θ θ) ∧
      deviceError (afterPerp θ θ) = (1 / 2) * deviceError (afterTransverse (2 * θ)) ∧
      deviceError (afterPerp θ θ) < 2 * deviceError (afterTransverse θ) ∧
      deviceError (afterTransverse θ) = Real.sin (θ / 2) ^ 2 := by
  have hone := transverse_third_atom h0 hπ
  have haligned := aligned_error_trig h0
  have hhalf := perp_error_trig θ
  have hsin : 0 < Real.sin (θ / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hcos : Real.cos (θ / 2) < 1 := by
    have hlt : Real.cos (θ / 2) < Real.cos 0 :=
      Real.cos_lt_cos_of_nonneg_of_le_pi (le_refl 0) (by linarith) (by linarith)
    simpa [Real.cos_zero] using hlt
  refine ⟨perp_atom_ne h0 hπ h0 hπ, perp_orders_same_error θ θ, ?_, ?_, hone.2.2.2.2.2.2.2⟩
  · rw [hhalf, haligned]
  · rw [hhalf, hone.2.2.2.2.2.2.2]
    set c : ℝ := Real.cos (θ / 2)
    set s : ℝ := Real.sin (θ / 2)
    have hs : Real.sin θ = 2 * s * c := by
      simpa [c, s, show 2 * (θ / 2) = θ by ring] using Real.sin_two_mul (θ / 2)
    have hc : 0 < c := by
      simpa [c] using Real.cos_pos_of_mem_Ioo (halfAngle_mem h0 hπ)
    have hslt : c < 1 := by simpa [c] using hcos
    rw [hs]
    have hsq : c ^ 2 < 1 := by nlinarith
    have hpos : 0 < s := by simpa [s] using hsin
    have hcmp : 2 * s ^ 2 * c ^ 2 < 2 * s ^ 2 := by
      have hmul : s ^ 2 * c ^ 2 < s ^ 2 * 1 :=
        mul_lt_mul_of_pos_left hsq (by positivity : 0 < s ^ 2)
      linarith
    have hleft : (1 / 2) * (2 * s * c) ^ 2 = 2 * s ^ 2 * c ^ 2 := by ring
    linarith

theorem lattice_perp {N : ℕ} (hN : 3 ≤ N) :
    atomOf (afterPerp (stepAngle N) (stepAngle N)) ≠
        atomOf (afterPerpRev (stepAngle N) (stepAngle N)) ∧
      deviceError (afterPerp (stepAngle N) (stepAngle N)) =
        deviceError (afterPerpRev (stepAngle N) (stepAngle N)) ∧
      deviceError (afterPerp (stepAngle N) (stepAngle N)) =
        (1 / 2) * deviceError (afterTransverse (2 * stepAngle N)) ∧
      deviceError (afterPerp (stepAngle N) (stepAngle N)) <
        2 * deviceError (afterTransverse (stepAngle N)) := by
  have hpos : 0 < N := lt_of_lt_of_le (by decide : 0 < 3) hN
  have hθ : 0 < stepAngle N := stepAngle_pos hpos
  have hπ : stepAngle N < Real.pi := by
    unfold stepAngle
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hpos
    rw [div_lt_iff₀ hN0]
    have h2 : (2 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le (by decide : 2 < 3) hN)
    nlinarith [Real.pi_pos]
  have h := perp_device_and_logic hθ hπ
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

/-- For `N ≥ 8` the perpendicular pair and the aligned pair are both in the cone,
and the ratio of their device errors equals the ratio of their expressed heights. -/
theorem error_ratio_eq_height_ratio {N : ℕ} (hN : 8 ≤ N) :
    deviceError (afterPerp (stepAngle N) (stepAngle N)) /
        deviceError (afterTransverse (2 * stepAngle N)) =
      JNormalized (perpSteps N) / JNormalized (alignedSteps 2 N) := by
  have h3 : 3 ≤ N := le_trans (by decide : (3 : ℕ) ≤ 8) hN
  have hpos : 0 < N := lt_of_lt_of_le (by decide : 0 < 8) hN
  have hlat := lattice_perp h3
  have hθ : 0 < stepAngle N := stepAngle_pos hpos
  have hheight := twoGravitons_fourfold hN
  have hperp := perp_twofold (le_trans (by decide : (4 : ℕ) ≤ 8) hN)
  have hfar : farHeight N ≠ 0 := ne_of_lt (farHeight_neg hpos)
  have hone : JNormalized (alignedSteps 1 N) = farHeight N := by
    rw [alignedSteps_one]
    rfl
  have hden : deviceError (afterTransverse (2 * stepAngle N)) ≠ 0 := by
    have hform := aligned_error_trig hθ
    have hπ : stepAngle N < Real.pi := by
      unfold stepAngle
      have hN0 : (0 : ℝ) < N := by exact_mod_cast hpos
      have h8 : (8 : ℝ) ≤ N := by exact_mod_cast hN
      rw [div_lt_iff₀ hN0]
      nlinarith [Real.pi_pos, h8]
    have hsin : 0 < Real.sin (stepAngle N) := Real.sin_pos_of_pos_of_lt_pi hθ hπ
    have hposErr : 0 < deviceError (afterTransverse (2 * stepAngle N)) := by
      rw [hform]
      exact sq_pos_of_pos hsin
    exact ne_of_gt hposErr
  have hJden : JNormalized (alignedSteps 2 N) ≠ 0 := by
    rw [hheight.2, hone]
    exact mul_ne_zero (by norm_num) hfar
  have hleft : deviceError (afterPerp (stepAngle N) (stepAngle N)) /
      deviceError (afterTransverse (2 * stepAngle N)) = 1 / 2 := by
    rw [hlat.2.2.1, mul_div_cancel_right₀ _ hden]
  have hright : JNormalized (perpSteps N) / JNormalized (alignedSteps 2 N) = 1 / 2 := by
    rw [hperp.2, hheight.2, hone]
    have h4 : (4 : ℝ) * farHeight N ≠ 0 := mul_ne_zero (by norm_num) hfar
    rw [div_eq_iff h4]
    ring
  rw [hleft, hright]

theorem lattice_axial_order {N : ℕ} (hN : 3 ≤ N) :
    atomOf (afterAxialTransverse (stepAngle N) (stepAngle N)) =
        atomOf (afterTransverse (stepAngle N)) ∧
      atomOf (afterTransverseAxial (stepAngle N) (stepAngle N)) ≠
        atomOf (afterTransverse (stepAngle N)) ∧
      deviceError (afterTransverseAxial (stepAngle N) (stepAngle N)) =
        deviceError (afterTransverse (stepAngle N)) ∧
      deviceError (applyMat (dualRotorMat (EuclideanSpace.single (2 : Fin 3) (stepAngle N)))
        spinUp) = 0 ∧
      afterTransverse (stepAngle N) ∉ lineE0 ∧
      afterTransverse (stepAngle N) ∉ qNot lineE0 := by
  have hpos : 0 < N := lt_of_lt_of_le (by decide : 0 < 3) hN
  have hθ : 0 < stepAngle N := stepAngle_pos hpos
  have hπ : stepAngle N < Real.pi := by
    unfold stepAngle
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hpos
    rw [div_lt_iff₀ hN0]
    have h2 : (2 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le (by decide : 2 < 3) hN)
    nlinarith [Real.pi_pos]
  have htwo : stepAngle N < 2 * Real.pi := by linarith [Real.pi_pos]
  have hord := axial_order_changes_atom hθ hπ hθ htwo
  have hthird := transverse_step_third_atom hN
  have hax := axial_no_logical_error (stepAngle N)
  exact ⟨hord.1, hord.2.1, hord.2.2.1, hax.2.2, hthird.1, hthird.2.1⟩

end DstDiophantine.Gravity.GravitonLogic

end
