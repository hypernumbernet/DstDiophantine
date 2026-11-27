import DoubleSpacetime.Gravity.GravitonQuantum
import DoubleSpacetime.Logic.Quantum.BooleanIsland
import DoubleSpacetime.Logic.Valuation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option linter.style.native false

/-!
# Gravitons on the quantum logic of one device

An axial graviton stays in the computational atom, and a transverse graviton
of angle in `(0, π)` occupies a third atom. The two orders of one step on
each of two transverse axes occupy distinct atoms and record one device error.
The integer `N` is not fixed, and the device error is not a height.
-/

noncomputable section

namespace DoubleSpacetime.Gravity.GravitonLogic

open DoubleSpacetime.Logic
open DoubleSpacetime.Gravity.GravitonQuantum
open SourceSuperposition Submodule Module Invariant
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

private theorem transverse_wedge (θ φ : ℝ) :
    afterTransverse θ 0 * afterTransverse φ 1 - afterTransverse θ 1 * afterTransverse φ 0 =
      -Complex.I * (Real.sin ((φ - θ) / 2) : ℂ) := by
  have hu := transverse_coord θ
  have hv := transverse_coord φ
  rw [hu.1, hu.2, hv.1, hv.2]
  have hsin := Real.sin_sub (φ / 2) (θ / 2)
  rw [show φ / 2 - θ / 2 = (φ - θ) / 2 by ring] at hsin
  apply Complex.ext
  · simp only [Complex.sub_re, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  · simp only [Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    rw [hsin]
    ring

private theorem transverse_atoms_ne {θ φ : ℝ} (h : Real.sin ((φ - θ) / 2) ≠ 0) :
    atomOf (afterTransverse θ) ≠ atomOf (afterTransverse φ) := by
  intro hspan
  have hmem : afterTransverse θ ∈ atomOf (afterTransverse φ) := by
    have hself : afterTransverse θ ∈ atomOf (afterTransverse θ) :=
      Submodule.mem_span_singleton_self _
    simpa [hspan] using hself
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
  have h0 := congrArg (fun v : DualSpinor => v 0) hc
  have h1 := congrArg (fun v : DualSpinor => v 1) hc
  simp only [PiLp.smul_apply, smul_eq_mul] at h0 h1
  have hwedge : afterTransverse θ 0 * afterTransverse φ 1 -
      afterTransverse θ 1 * afterTransverse φ 0 = 0 := by
    rw [← h0, ← h1]
    ring
  rw [transverse_wedge θ φ] at hwedge
  have hI : (-Complex.I : ℂ) ≠ 0 := by simp [Complex.I_ne_zero]
  have hsin : (Real.sin ((φ - θ) / 2) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr h
  exact mul_ne_zero hI hsin hwedge

private theorem halfArg_eq {n N : ℕ} (hN : 0 < N) :
    (n : ℝ) * stepAngle N / 2 = (n : ℝ) * Real.pi / N := by
  unfold stepAngle
  have hNz : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_iff_ne_zero.mp hN)
  field_simp [hNz]

theorem aligned_carrier_ray {n N : ℕ} (hn : 0 < n) (hN : n ≤ N)
    (u : DualSpinor) (hu : u = afterTransverse ((n : ℝ) * stepAngle N)) :
    (n = N → u ∈ lineE0 ∧ atomOf u = lineE0 ∧ u ∉ qNot lineE0 ∧ deviceError u = 0) ∧
      (2 * n = N → u ∈ qNot lineE0 ∧ atomOf u = qNot lineE0 ∧ u ∉ lineE0 ∧
        deviceError u = 1) ∧
      (n ≠ N → 2 * n ≠ N → u ∉ lineE0 ∧ u ∉ qNot lineE0 ∧
        atomOf u ≠ lineE0 ∧ atomOf u ≠ qNot lineE0 ∧
        0 < deviceError u ∧ deviceError u < 1) := by
  have hpos : 0 < N := lt_of_lt_of_le hn hN
  set α : ℝ := (n : ℝ) * Real.pi / N
  have hα : (n : ℝ) * stepAngle N / 2 = α := by
    simpa [α] using halfArg_eq (n := n) hpos
  have hcoord := transverse_coord ((n : ℝ) * stepAngle N)
  have hαpos : 0 < α := by
    unfold α
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hpos
    exact div_pos (mul_pos (by exact_mod_cast hn) Real.pi_pos) hN0
  have hαle : α ≤ Real.pi := by
    unfold α
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hpos
    have hle : (n : ℝ) / N ≤ 1 := by
      rw [div_le_one hN0]
      exact_mod_cast hN
    have hmul := mul_le_mul_of_nonneg_right hle Real.pi_pos.le
    have hform : (n : ℝ) * Real.pi / N = (n : ℝ) / N * Real.pi := by ring
    linarith [hform, hmul]
  have hsin_zero : Real.sin α = 0 ↔ n = N := by
    constructor
    · intro hzero
      by_contra hne
      have hltn : n < N := lt_of_le_of_ne hN hne
      have hαlt : α < Real.pi := by
        unfold α
        have hN0 : (0 : ℝ) < N := by exact_mod_cast hpos
        have hlt : (n : ℝ) < N := by exact_mod_cast hltn
        have hdiv : (n : ℝ) / N < 1 := (div_lt_one hN0).mpr hlt
        have hmul := mul_lt_mul_of_pos_right hdiv Real.pi_pos
        have hform : (n : ℝ) * Real.pi / N = (n : ℝ) / N * Real.pi := by ring
        linarith [hform, hmul]
      exact (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hαpos hαlt)) hzero
    · intro hnN
      have hαpi : α = Real.pi := by
        unfold α
        rw [hnN]
        have hNz : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_iff_ne_zero.mp hpos)
        field_simp [hNz]
      simp [hαpi, Real.sin_pi]
  have hcos_zero : Real.cos α = 0 ↔ 2 * n = N := by
    constructor
    · intro hzero
      have hαeq : α = Real.pi / 2 := by
        rcases lt_trichotomy α (Real.pi / 2) with hlt | heq | hgt
        · have hposc : 0 < Real.cos α := by
            have hltc : Real.cos (Real.pi / 2) < Real.cos α :=
              Real.cos_lt_cos_of_nonneg_of_le_pi (by linarith) (by linarith [Real.pi_pos]) hlt
            simpa [Real.cos_pi_div_two] using hltc
          exact absurd hzero (ne_of_gt hposc)
        · exact heq
        · have hneg : Real.cos α < 0 := by
            have hltc : Real.cos α < Real.cos (Real.pi / 2) :=
              Real.cos_lt_cos_of_nonneg_of_le_pi (by linarith [Real.pi_pos]) hαle hgt
            simpa [Real.cos_pi_div_two] using hltc
          exact absurd hzero (ne_of_lt hneg)
      unfold α at hαeq
      have hN0 : (0 : ℝ) < N := by exact_mod_cast hpos
      have hmul : (n : ℝ) * Real.pi = (Real.pi / 2) * N := by
        have hNz : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_iff_ne_zero.mp hpos)
        apply (div_eq_iff hNz).mp
        exact hαeq
      have hclear : (2 : ℝ) * n = N := by
        have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
        field_simp [hpi] at hmul
        linarith
      exact_mod_cast hclear
    · intro hhalf
      have hαhalf : α = Real.pi / 2 := by
        unfold α
        have hcast : (N : ℝ) = 2 * (n : ℝ) := by exact_mod_cast hhalf.symm
        rw [hcast]
        have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_iff_ne_zero.mp hn)
        field_simp [hn0]
      simp [hαhalf, Real.cos_pi_div_two]
  have hnorm : ‖u‖ = 1 := by
    have hsq := norm_applyMat_dualRotor_sq
      (EuclideanSpace.single (0 : Fin 3) ((n : ℝ) * stepAngle N)) spinUp
    rw [spinUp_norm_sq] at hsq
    have hsq' : ‖u‖ ^ 2 = 1 := by simpa [hu, afterTransverse] using hsq
    nlinarith [norm_nonneg u]
  have herr : deviceError u = Real.sin α ^ 2 := by
    rw [deviceError, weight_eq_coord hnorm, hu, hcoord.1, hα]
    have hns : ‖(Real.cos α : ℂ)‖ ^ 2 = Real.cos α ^ 2 := by
      rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
    rw [hns]
    have htrig := Real.cos_sq_add_sin_sq α
    linarith
  refine ⟨?_, ?_, ?_⟩
  · intro hnN
    have hsin0 : Real.sin α = 0 := hsin_zero.mpr hnN
    have hcos : Real.cos α = -1 := by
      have hαpi : α = Real.pi := by
        unfold α
        rw [hnN]
        have hNz : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_iff_ne_zero.mp hpos)
        field_simp [hNz]
      simp [hαpi, Real.cos_pi]
    have h1 : u 1 = 0 := by
      rw [hu, hcoord.2, hα, hsin0]
      simp
    have h0 : u 0 = -1 := by
      rw [hu, hcoord.1, hα, hcos]
      norm_num
    have hin : u ∈ lineE0 := by
      rw [mem_lineE0_iff]
      exact h1
    have hnz : u ≠ 0 := by
      intro hzero
      have : u 0 = 0 := by
        rw [hzero]
        simp [PiLp.zero_apply]
      rw [h0] at this
      exact one_ne_zero (neg_eq_zero.mp this)
    have hspan : atomOf u = lineE0 := by
      have hle : atomOf u ≤ lineE0 := by
        unfold atomOf
        rw [Submodule.span_singleton_le_iff_mem]
        exact hin
      have hfr : Module.finrank ℂ (atomOf u) = 1 := finrank_span_singleton hnz
      exact eq_of_le_of_finrank_eq hle (hfr.trans lineE0_finrank.symm)
    refine ⟨hin, hspan, ?_, ?_⟩
    · rw [← lineE1_eq_negation, mem_lineE1_iff, h0]
      exact neg_ne_zero.mpr one_ne_zero
    · rw [herr, hsin0]
      norm_num
  · intro hhalf
    have hcos0 : Real.cos α = 0 := hcos_zero.mpr hhalf
    have hsin1 : Real.sin α = 1 := by
      have hαhalf : α = Real.pi / 2 := by
        unfold α
        have hcast : (N : ℝ) = 2 * (n : ℝ) := by exact_mod_cast hhalf.symm
        rw [hcast]
        have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_iff_ne_zero.mp hn)
        field_simp [hn0]
      simp [hαhalf, Real.sin_pi_div_two]
    have h0 : u 0 = 0 := by
      rw [hu, hcoord.1, hα, hcos0]
      norm_num
    have h1 : u 1 = -Complex.I := by
      rw [hu, hcoord.2, hα, hsin1]
      simp
    have hin1 : u ∈ lineE1 := by
      rw [mem_lineE1_iff]
      exact h0
    have hnz : u ≠ 0 := by
      intro hzero
      have : u 1 = 0 := by
        rw [hzero]
        simp [PiLp.zero_apply]
      rw [h1] at this
      exact Complex.I_ne_zero (neg_eq_zero.mp this)
    have hspan : atomOf u = lineE1 := by
      have hle : atomOf u ≤ lineE1 := by
        unfold atomOf
        rw [Submodule.span_singleton_le_iff_mem]
        exact hin1
      have hfr : Module.finrank ℂ (atomOf u) = 1 := finrank_span_singleton hnz
      exact eq_of_le_of_finrank_eq hle (hfr.trans lineE1_finrank.symm)
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [← lineE1_eq_negation]
      exact hin1
    · rw [← lineE1_eq_negation, hspan]
    · rw [mem_lineE0_iff, h1]
      exact neg_ne_zero.mpr Complex.I_ne_zero
    · rw [herr, hsin1]
      norm_num
  · intro hneN hneHalf
    have hsin_ne : Real.sin α ≠ 0 := by
      intro hzero
      exact hneN (hsin_zero.mp hzero)
    have hcos_ne : Real.cos α ≠ 0 := by
      intro hzero
      exact hneHalf (hcos_zero.mp hzero)
    have hne1 : u 1 ≠ 0 := by
      rw [hu, hcoord.2, hα]
      exact mul_ne_zero (by simp [Complex.I_ne_zero]) (Complex.ofReal_ne_zero.mpr hsin_ne)
    have hne0 : u 0 ≠ 0 := by
      rw [hu, hcoord.1, hα]
      exact Complex.ofReal_ne_zero.mpr hcos_ne
    have hout0 : u ∉ lineE0 := by
      rw [mem_lineE0_iff]
      exact hne1
    have hout1 : u ∉ lineE1 := by
      rw [mem_lineE1_iff]
      exact hne0
    refine ⟨hout0, by rwa [← lineE1_eq_negation], ?_, ?_, ?_, ?_⟩
    · intro hspan
      have hmem : u ∈ lineE0 := by
        rw [← hspan]
        exact Submodule.mem_span_singleton_self _
      exact hout0 hmem
    · intro hspan
      have hmem : u ∈ qNot lineE0 := by
        rw [← hspan]
        exact Submodule.mem_span_singleton_self _
      rw [← lineE1_eq_negation] at hmem
      exact hout1 hmem
    · rw [herr]
      exact sq_pos_of_ne_zero hsin_ne
    · rw [herr]
      have hcosSq : 0 < Real.cos α ^ 2 := sq_pos_of_ne_zero hcos_ne
      have hsum := Real.cos_sq_add_sin_sq α
      linarith

theorem locked_four_rays {N : ℕ} (hdiv : 4 ∣ N) (hN : 4 ≤ N) :
    atomOf (afterTransverse (((N / 4 : ℕ) : ℝ) * stepAngle N)) ≠ lineE0 ∧
      atomOf (afterTransverse (((N / 4 : ℕ) : ℝ) * stepAngle N)) ≠ qNot lineE0 ∧
      atomOf (afterTransverse (((N / 2 : ℕ) : ℝ) * stepAngle N)) = qNot lineE0 ∧
      afterTransverse (((N / 2 : ℕ) : ℝ) * stepAngle N) ∉ lineE0 ∧
      atomOf (afterTransverse (((3 * (N / 4) : ℕ) : ℝ) * stepAngle N)) ≠ lineE0 ∧
      atomOf (afterTransverse (((3 * (N / 4) : ℕ) : ℝ) * stepAngle N)) ≠ qNot lineE0 ∧
      atomOf (afterTransverse (((3 * (N / 4) : ℕ) : ℝ) * stepAngle N)) ≠
        atomOf (afterTransverse (((N / 4 : ℕ) : ℝ) * stepAngle N)) ∧
      atomOf (afterTransverse ((N : ℝ) * stepAngle N)) = lineE0 ∧
      afterTransverse ((N : ℝ) * stepAngle N) ∉ qNot lineE0 ∧
      deviceError (afterTransverse (((N / 4 : ℕ) : ℝ) * stepAngle N)) = 1 / 2 ∧
      deviceError (afterTransverse (((N / 2 : ℕ) : ℝ) * stepAngle N)) = 1 ∧
      deviceError (afterTransverse (((3 * (N / 4) : ℕ) : ℝ) * stepAngle N)) = 1 / 2 ∧
      deviceError (afterTransverse ((N : ℝ) * stepAngle N)) = 0 ∧
      JNormalized (express (alignedSteps (N / 4) N)) = -((1 : ℝ) / 3) ∧
      JNormalized (express (alignedSteps (N / 2) N)) = -((1 : ℝ) / 3) ∧
      JNormalized (express (alignedSteps (3 * (N / 4)) N)) = -((1 : ℝ) / 3) ∧
      JNormalized (express (alignedSteps N N)) = -((1 : ℝ) / 3) := by
  set q := afterTransverse (((N / 4 : ℕ) : ℝ) * stepAngle N) with hq_def
  set h := afterTransverse (((N / 2 : ℕ) : ℝ) * stepAngle N) with hh_def
  set t := afterTransverse (((3 * (N / 4) : ℕ) : ℝ) * stepAngle N) with ht_def
  set f := afterTransverse ((N : ℝ) * stepAngle N) with hf_def
  have hpos : 0 < N := lt_of_lt_of_le (by decide : (0 : ℕ) < 4) hN
  have h4 : 4 * (N / 4) = N := Nat.mul_div_cancel' hdiv
  have hqpos : 0 < N / 4 := by
    have h1 : 4 * 1 ≤ 4 * (N / 4) := by
      rw [h4]
      exact hN
    exact Nat.succ_le_iff.mp (Nat.le_of_mul_le_mul_left h1 (by decide : 0 < 4))
  have hqne : N / 4 ≠ N := by
    intro heq
    have : 4 * N = N := by simpa [heq] using h4
    omega
  have hhalfNe : 2 * (N / 4) ≠ N := by
    intro heq
    have htwice : 4 * (N / 4) = 2 * N := by
      calc
        4 * (N / 4) = 2 * (2 * (N / 4)) := by ring
        _ = 2 * N := by rw [heq]
    rw [h4] at htwice
    omega
  have hthreePos : 0 < 3 * (N / 4) := by omega
  have hthreeNe : 3 * (N / 4) ≠ N := by
    intro heq
    have : 3 * (N / 4) = 4 * (N / 4) := by rw [heq, h4]
    omega
  have hthreeHalf : 2 * (3 * (N / 4)) ≠ N := by
    intro heq
    have : 6 * (N / 4) = 4 * (N / 4) := by
      calc
        6 * (N / 4) = 2 * (3 * (N / 4)) := by ring
        _ = N := heq
        _ = 4 * (N / 4) := h4.symm
    omega
  have hhalfPos : 0 < N / 2 := by
    have h2dvd : 2 ∣ N := dvd_trans (by decide : 2 ∣ 4) hdiv
    have h2 : 2 * (N / 2) = N := Nat.mul_div_cancel' h2dvd
    have h1 : 2 * 1 ≤ 2 * (N / 2) := by
      rw [h2]
      exact le_trans (by decide : (2 : ℕ) ≤ 4) hN
    exact Nat.succ_le_iff.mp (Nat.le_of_mul_le_mul_left h1 (by decide : 0 < 2))
  have hhalfLe : N / 2 ≤ N := Nat.div_le_self N 2
  have hthreeLe : 3 * (N / 4) ≤ N := by
    have hle : 3 * (N / 4) ≤ 4 * (N / 4) := Nat.mul_le_mul_right (N / 4) (by decide : 3 ≤ 4)
    simpa [h4] using hle
  have hq := aligned_carrier_ray (n := N / 4) hqpos (Nat.div_le_self N 4) q hq_def
  have hh := aligned_carrier_ray (n := N / 2) hhalfPos hhalfLe h hh_def
  have ht := aligned_carrier_ray (n := 3 * (N / 4)) hthreePos hthreeLe t ht_def
  have hf := aligned_carrier_ray (n := N) hpos le_rfl f hf_def
  have hqRay := hq.2.2 hqne hhalfNe
  have hhRay := hh.2.1 (Nat.mul_div_cancel' (dvd_trans (by decide : 2 ∣ 4) hdiv))
  have htRay := ht.2.2 hthreeNe hthreeHalf
  have hfRay := hf.1 rfl
  have hcounts := fourCounts_lock hdiv hN
  have hθ : ((N / 4 : ℕ) : ℝ) * stepAngle N = Real.pi / 2 := quarterTurn_angle hdiv hpos
  have hφ : ((3 * (N / 4) : ℕ) : ℝ) * stepAngle N = 3 * Real.pi / 2 :=
    threeQuarterTurn_angle hdiv hpos
  have hsin : Real.sin ((3 * Real.pi / 2 - Real.pi / 2) / 2) ≠ 0 := by
    have hdiff : (3 * Real.pi / 2 - Real.pi / 2) / 2 = Real.pi / 2 := by ring
    rw [hdiff, Real.sin_pi_div_two]
    norm_num
  have hatoms : atomOf t ≠ atomOf q := by
    have hne := transverse_atoms_ne (θ := ((N / 4 : ℕ) : ℝ) * stepAngle N)
      (φ := ((3 * (N / 4) : ℕ) : ℝ) * stepAngle N) ?_
    · simpa [q, t] using hne.symm
    · rw [hθ, hφ]
      exact hsin
  have hdq : deviceError q = 1 / 2 := by
    rw [hq_def, deviceError, afterTransverse]
    exact hcounts.2.2.2.2.1
  have hdh : deviceError h = 1 := by
    rw [hh_def, deviceError, afterTransverse]
    exact hcounts.2.2.2.2.2.1
  have hdt : deviceError t = 1 / 2 := by
    rw [ht_def, deviceError, afterTransverse]
    exact hcounts.2.2.2.2.2.2.1
  have hdf : deviceError f = 0 := by
    rw [hf_def, deviceError, afterTransverse]
    exact hcounts.2.2.2.2.2.2.2.1
  exact ⟨hqRay.2.2.1, hqRay.2.2.2.1, hhRay.2.1, hhRay.2.2.1, htRay.2.2.1, htRay.2.2.2.1,
    hatoms, hfRay.2.1, hfRay.2.2.1, hdq, hdh, hdt, hdf, hcounts.1, hcounts.2.1, hcounts.2.2.1,
    hcounts.2.2.2.1⟩

private theorem classify?_eq_T {j : ℝ} (hj : j = 0) : classify? j = some .T := by
  have habs : |j| ≤ 1 := by rw [hj]; norm_num
  have hT : classifyOfMem j habs = .T := (classifyOfMem_eq_T_iff habs).mpr hj
  simpa [classify?, habs] using hT

private theorem classify?_eq_U {j : ℝ} (hj : j = 1 / 2) : classify? j = some .U := by
  have habs : |j| ≤ 1 := by rw [hj]; norm_num
  have hU : classifyOfMem j habs = .U :=
    (classifyOfMem_eq_U_iff habs).mpr (by rw [hj]; constructor <;> norm_num)
  simpa [classify?, habs] using hU

private theorem classify?_eq_F {j : ℝ} (hj : j = 1) : classify? j = some .F := by
  have habs : |j| ≤ 1 := by rw [hj]; norm_num
  have hF : classifyOfMem j habs = .F := (classifyOfMem_eq_F_iff habs).mpr hj
  simpa [classify?, habs] using hF

private theorem classify?_eq_B {j : ℝ} (hj : j = -((1 : ℝ) / 3)) : classify? j = some .B := by
  have habs : |j| ≤ 1 := by rw [hj]; norm_num
  have hB : classifyOfMem j habs = .B :=
    (classifyOfMem_eq_B_iff habs).mpr (by rw [hj]; constructor <;> norm_num)
  simpa [classify?, habs] using hB

private theorem afterTransverse_ne_zero_of_cos {θ : ℝ} (h : Real.cos (θ / 2) ≠ 0) :
    afterTransverse θ ≠ 0 := by
  intro hz
  have h0 : afterTransverse θ 0 = 0 := by
    rw [hz]
    simp [PiLp.zero_apply]
  rw [(transverse_coord θ).1] at h0
  exact h (Complex.ofReal_eq_zero.mp h0)

private theorem ray_not_mem_island {L A : QProp} (hA : finrank ℂ A = 1)
    (hne : A ≠ L) (hneo : A ≠ Lᗮ) : A ∉ Island L := by
  intro hmem
  rcases mem_island_iff.mp hmem with h | h | h | h
  · exact (bot_ne_of_finrank_one hA) h.symm
  · exact hne h
  · exact hneo h
  · exact (top_ne_of_finrank_one hA) h.symm

private theorem not_compatible_third_ray {L A : QProp} (hL : finrank ℂ L = 1)
    (hA : finrank ℂ A = 1) (hne : A ≠ L) (hneo : A ≠ Lᗮ) : ¬ Compatible L A := by
  intro hc
  rcases (compatible_line_iff hL hA).mp hc with h | hortho
  · exact hne h.symm
  · have hle : L ≤ Aᗮ := (Submodule.isOrtho_iff_le).mp hortho
    have hLeq : L = Aᗮ :=
      eq_of_le_of_finrank_eq hle (hL.trans (finrank_orthogonal_line hA).symm)
    exact hneo (by rw [← orthogonal_orthogonal A, hLeq])

theorem four_turns_one_label {N : ℕ} (hdiv : 4 ∣ N) (hN : 4 ≤ N) :
    let jq := JNormalized (express (alignedSteps (N / 4) N))
    let jh := JNormalized (express (alignedSteps (N / 2) N))
    let jt := JNormalized (express (alignedSteps (3 * (N / 4)) N))
    let jf := JNormalized (express (alignedSteps N N))
    let q := atomOf (afterTransverse (((N / 4 : ℕ) : ℝ) * stepAngle N))
    let half := atomOf (afterTransverse (((N / 2 : ℕ) : ℝ) * stepAngle N))
    let three := atomOf (afterTransverse (((3 * (N / 4) : ℕ) : ℝ) * stepAngle N))
    let full := atomOf (afterTransverse ((N : ℝ) * stepAngle N))
    let eq := deviceError (afterTransverse (((N / 4 : ℕ) : ℝ) * stepAngle N))
    let eh := deviceError (afterTransverse (((N / 2 : ℕ) : ℝ) * stepAngle N))
    let et := deviceError (afterTransverse (((3 * (N / 4) : ℕ) : ℝ) * stepAngle N))
    let ef := deviceError (afterTransverse ((N : ℝ) * stepAngle N))
    let j0 := JNormalized (express (alignedSteps 0 N))
    jq = -((1 : ℝ) / 3) ∧ jh = -((1 : ℝ) / 3) ∧ jt = -((1 : ℝ) / 3) ∧
      jf = -((1 : ℝ) / 3) ∧
      classify? jq = some .B ∧ classify? jh = some .B ∧
      classify? jt = some .B ∧ classify? jf = some .B ∧
      HoldsNotF jq ∧ HoldsNotF jh ∧ HoldsNotF jt ∧ HoldsNotF jf ∧
      ¬ HoldsT jq ∧ ¬ HoldsT jh ∧ ¬ HoldsT jt ∧ ¬ HoldsT jf ∧
      full = lineE0 ∧ half = qNot lineE0 ∧
      full ∈ Island lineE0 ∧ half ∈ Island lineE0 ∧
      q ∉ Island lineE0 ∧ three ∉ Island lineE0 ∧ q ≠ three ∧ full ≠ half ∧
      ¬ Compatible lineE0 q ∧ ¬ Compatible lineE0 three ∧
      ¬ lineE0 ⊓ material lineE0 q ≤ q ∧
      ¬ lineE0 ⊓ material lineE0 three ≤ three ∧
      eq = 1 / 2 ∧ eh = 1 ∧ et = 1 / 2 ∧ ef = 0 ∧
      classify? eq = some .U ∧ classify? eh = some .F ∧
      classify? et = some .U ∧ classify? ef = some .T ∧
      j0 = 0 ∧ classify? j0 = some .T ∧ HoldsT j0 ∧
      atomOf (afterTransverse 0) = lineE0 ∧ atomOf (afterTransverse 0) = full := by
  intro jq jh jt jf q half three full eq eh et ef j0
  have hlock := locked_four_rays hdiv hN
  rcases hlock with
    ⟨hqNe, hqNeo, hhalf, _hhalfOut, htNe, htNeo, htq, hfull, _hfullOut,
      heq, heh, het, hef, hjq, hjh, hjt, hjf⟩
  have hpos : 0 < N := lt_of_lt_of_le (by decide : (0 : ℕ) < 4) hN
  have hθ := quarterTurn_angle hdiv hpos
  have hφ := threeQuarterTurn_angle hdiv hpos
  have hcosQ : Real.cos ((((N / 4 : ℕ) : ℝ) * stepAngle N) / 2) ≠ 0 := by
    rw [hθ]
    have harg : (Real.pi / 2) / 2 = Real.pi / 4 := by ring
    rw [harg, Real.cos_pi_div_four]
    positivity
  have hcosT : Real.cos ((((3 * (N / 4) : ℕ) : ℝ) * stepAngle N) / 2) ≠ 0 := by
    rw [hφ]
    have harg : (3 * Real.pi / 2) / 2 = 3 * Real.pi / 4 := by ring
    rw [harg]
    have hsub : 3 * Real.pi / 4 = Real.pi - Real.pi / 4 := by ring
    rw [hsub, Real.cos_pi_sub, Real.cos_pi_div_four]
    exact neg_ne_zero.mpr
      (ne_of_gt (div_pos (Real.sqrt_pos.mpr (by norm_num)) (by norm_num)))
  have hqFin : finrank ℂ q = 1 :=
    finrank_span_singleton (afterTransverse_ne_zero_of_cos hcosQ)
  have htFin : finrank ℂ three = 1 :=
    finrank_span_singleton (afterTransverse_ne_zero_of_cos hcosT)
  have hnotQ : ¬ Compatible lineE0 q :=
    not_compatible_third_ray lineE0_finrank hqFin hqNe hqNeo
  have hnotT : ¬ Compatible lineE0 three :=
    not_compatible_third_ray lineE0_finrank htFin htNe htNeo
  have hfullEq : full = lineE0 := hfull
  have hhalfEq : half = qNot lineE0 := hhalf
  have hfullNe : full ≠ half := by
    rw [hfullEq, hhalfEq]
    exact line_ne_orthogonal lineE0_finrank
  have hzeroSteps : alignedSteps 0 N = oneAxisDual 0 := by
    unfold alignedSteps
    simp
  have hadm0 :=
    oneAxisDual_admissible (θ := 0) (by norm_num) (by nlinarith [Real.pi_pos])
  have hexp0 : express (alignedSteps 0 N) = oneAxisDual 0 := by
    rw [hzeroSteps]
    exact express_eq_of_admissible hadm0
  have hj0 : j0 = 0 := by
    have hJ : JNormalized (express (alignedSteps 0 N)) = JNormalized (oneAxisDual 0) :=
      congrArg JNormalized hexp0
    have hJ0 : JNormalized (oneAxisDual 0) = 0 := by
      rw [JNormalized_oneAxisDual]
      simp
    exact hJ.trans hJ0
  have hcoord0 := transverse_coord 0
  have hmem0 : afterTransverse 0 ∈ lineE0 := by
    rw [mem_lineE0_iff, hcoord0.2]
    simp
  have hnz0 : afterTransverse 0 ≠ 0 := by
    intro hz
    have : afterTransverse 0 0 = 0 := by
      rw [hz]
      simp [PiLp.zero_apply]
    rw [hcoord0.1] at this
    simp at this
  have hat0 : atomOf (afterTransverse 0) = lineE0 := by
    have hle : atomOf (afterTransverse 0) ≤ lineE0 := by
      unfold atomOf
      rw [Submodule.span_singleton_le_iff_mem]
      exact hmem0
    have hfr : finrank ℂ (atomOf (afterTransverse 0)) = 1 := finrank_span_singleton hnz0
    exact eq_of_le_of_finrank_eq hle (hfr.trans lineE0_finrank.symm)
  have hfullMem : full ∈ Island lineE0 := by
    rw [hfullEq, mem_island_iff]
    exact Or.inr (Or.inl rfl)
  have hhalfMem : half ∈ Island lineE0 := by
    rw [hhalfEq, mem_island_iff]
    exact Or.inr (Or.inr (Or.inl rfl))
  refine ⟨hjq, hjh, hjt, hjf, classify?_eq_B hjq, classify?_eq_B hjh, classify?_eq_B hjt,
    classify?_eq_B hjf, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hfullEq, hhalfEq, hfullMem, hhalfMem,
    ray_not_mem_island hqFin hqNe hqNeo, ray_not_mem_island htFin htNe htNeo, htq.symm, hfullNe,
    hnotQ, hnotT, (material_detach_iff_compatible).not.mpr hnotQ,
    (material_detach_iff_compatible).not.mpr hnotT, heq, heh, het, hef, classify?_eq_U heq,
    classify?_eq_F heh, classify?_eq_U het, classify?_eq_T hef, hj0, classify?_eq_T hj0, ?_,
    hat0, hat0.trans hfullEq.symm⟩
  · have hlt : JNormalized (express (alignedSteps (N / 4) N)) < 1 := by rw [hjq]; norm_num
    exact hlt
  · have hlt : JNormalized (express (alignedSteps (N / 2) N)) < 1 := by rw [hjh]; norm_num
    exact hlt
  · have hlt : JNormalized (express (alignedSteps (3 * (N / 4)) N)) < 1 := by rw [hjt]; norm_num
    exact hlt
  · have hlt : JNormalized (express (alignedSteps N N)) < 1 := by rw [hjf]; norm_num
    exact hlt
  · intro hT
    have hzero : JNormalized (express (alignedSteps (N / 4) N)) = 0 := hT
    rw [hjq] at hzero
    norm_num at hzero
  · intro hT
    have hzero : JNormalized (express (alignedSteps (N / 2) N)) = 0 := hT
    rw [hjh] at hzero
    norm_num at hzero
  · intro hT
    have hzero : JNormalized (express (alignedSteps (3 * (N / 4)) N)) = 0 := hT
    rw [hjt] at hzero
    norm_num at hzero
  · intro hT
    have hzero : JNormalized (express (alignedSteps N N)) = 0 := hT
    rw [hjf] at hzero
    norm_num at hzero
  · exact hj0

theorem four_turns_read {N : ℕ} (hdiv : 4 ∣ N) (hN : 4 ≤ N) :
    classify? (JNormalized (express (alignedSteps (N / 4) N))) = some .B ∧
      classify? (JNormalized (express (alignedSteps (N / 2) N))) = some .B ∧
      classify? (JNormalized (express (alignedSteps (3 * (N / 4)) N))) = some .B ∧
      classify? (JNormalized (express (alignedSteps N N))) = some .B ∧
      classify? (JNormalized (express (alignedSteps 0 N))) = some .T ∧
      ¬ Compatible lineE0 (atomOf (afterTransverse (((N / 4 : ℕ) : ℝ) * stepAngle N))) ∧
      ¬ lineE0 ⊓ material lineE0
          (atomOf (afterTransverse (((N / 4 : ℕ) : ℝ) * stepAngle N))) ≤
        atomOf (afterTransverse (((N / 4 : ℕ) : ℝ) * stepAngle N)) ∧
      ¬ Compatible lineE0
          (atomOf (afterTransverse (((3 * (N / 4) : ℕ) : ℝ) * stepAngle N))) ∧
      classify? (deviceError (afterTransverse (((N / 4 : ℕ) : ℝ) * stepAngle N))) = some .U ∧
      classify? (deviceError (afterTransverse (((N / 2 : ℕ) : ℝ) * stepAngle N))) = some .F ∧
      classify? (deviceError (afterTransverse (((3 * (N / 4) : ℕ) : ℝ) * stepAngle N))) =
        some .U ∧
      classify? (deviceError (afterTransverse ((N : ℝ) * stepAngle N))) = some .T ∧
      atomOf (afterTransverse 0) = atomOf (afterTransverse ((N : ℝ) * stepAngle N)) ∧
      atomOf (afterTransverse 0) ∈ Island lineE0 ∧
      atomOf (afterTransverse (((N / 2 : ℕ) : ℝ) * stepAngle N)) ∈ Island lineE0 ∧
      atomOf (afterTransverse (((N / 4 : ℕ) : ℝ) * stepAngle N)) ∉ Island lineE0 := by
  have h := four_turns_one_label hdiv hN
  dsimp only at h
  rcases h with ⟨_, _, _, _, hq, hh, ht, hf, _, _, _, _, _, _, _, _, _, _, hfullMem,
    hhalfMem, hqOut, _, _, _, hcomp, hcompT, hdet, _, _, _, _, _, hU, hF, hUt, hT, _,
    hT0, _, _, hsame⟩
  refine ⟨hq, hh, ht, hf, hT0, hcomp, hdet, hcompT, hU, hF, hUt, hT, hsame, ?_, hhalfMem,
    hqOut⟩
  rw [hsame]
  exact hfullMem

private theorem half_trig_pos {θ : ℝ} (h0 : 0 < θ) (hπ : θ < Real.pi) :
    0 < Real.cos (θ / 2) ∧ 0 < Real.sin (θ / 2) := by
  exact ⟨Real.cos_pos_of_mem_Ioo (halfAngle_mem h0 hπ),
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)⟩

private theorem coord_re_cos_sq {θ : ℝ} :
    (afterPerp θ θ 0).re = Real.cos (θ / 2) ^ 2 := by
  rw [(perp_coord θ θ).1]
  simp only [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
  ring

private theorem coord_re_sin_cos {θ : ℝ} :
    (afterPerp θ θ 1).re = Real.sin (θ / 2) * Real.cos (θ / 2) := by
  rw [(perp_coord θ θ).2]
  simp only [Complex.sub_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero]

private theorem coord_re_rev_cos_sq {θ : ℝ} :
    (afterPerpRev θ θ 0).re = Real.cos (θ / 2) ^ 2 := by
  rw [(perpRev_coord θ θ).1]
  simp only [Complex.sub_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero]
  ring

private theorem coord_re_rev_sin_cos {θ : ℝ} :
    (afterPerpRev θ θ 1).re = Real.sin (θ / 2) * Real.cos (θ / 2) := by
  rw [(perpRev_coord θ θ).2]
  simp only [Complex.sub_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero]
  ring

private theorem perp_forward_coords_ne {θ : ℝ} (h0 : 0 < θ) (hπ : θ < Real.pi) :
    afterPerp θ θ 0 ≠ 0 ∧ afterPerp θ θ 1 ≠ 0 := by
  obtain ⟨hc, hs⟩ := half_trig_pos h0 hπ
  constructor
  · intro hz
    have hre := coord_re_cos_sq (θ := θ)
    rw [hz, Complex.zero_re] at hre
    exact (sq_pos_of_pos hc).ne hre
  · intro hz
    have hre := coord_re_sin_cos (θ := θ)
    rw [hz, Complex.zero_re] at hre
    exact (mul_pos hs hc).ne hre

private theorem perp_reverse_coords_ne {θ : ℝ} (h0 : 0 < θ) (hπ : θ < Real.pi) :
    afterPerpRev θ θ 0 ≠ 0 ∧ afterPerpRev θ θ 1 ≠ 0 := by
  obtain ⟨hc, hs⟩ := half_trig_pos h0 hπ
  constructor
  · intro hz
    have hre := coord_re_rev_cos_sq (θ := θ)
    rw [hz, Complex.zero_re] at hre
    exact (sq_pos_of_pos hc).ne hre
  · intro hz
    have hre := coord_re_rev_sin_cos (θ := θ)
    rw [hz, Complex.zero_re] at hre
    exact (mul_pos hs hc).ne hre

private theorem carrier_ne_zero_of_coord {u : DualSpinor} (h : u 0 ≠ 0) : u ≠ 0 := by
  intro hz
  exact h (by simp [hz, PiLp.zero_apply])

private theorem atom_outside_computational {u : DualSpinor}
    (h0 : u 0 ≠ 0) (h1 : u 1 ≠ 0) :
    atomOf u ∉ Island lineE0 ∧
      ¬ Compatible lineE0 (atomOf u) ∧
      ¬ lineE0 ⊓ material lineE0 (atomOf u) ≤ atomOf u := by
  have hu : u ≠ 0 := carrier_ne_zero_of_coord h0
  have hfin : finrank ℂ (atomOf u) = 1 := finrank_span_singleton hu
  have hout0 : u ∉ lineE0 := by
    rw [mem_lineE0_iff]
    exact h1
  have hout1 : u ∉ lineE1 := by
    rw [mem_lineE1_iff]
    exact h0
  have hne : atomOf u ≠ lineE0 := by
    intro hspan
    have hmem : u ∈ lineE0 := by
      rw [← hspan]
      exact Submodule.mem_span_singleton_self _
    exact hout0 hmem
  have hneo : atomOf u ≠ qNot lineE0 := by
    intro hspan
    have hmem : u ∈ qNot lineE0 := by
      rw [← hspan]
      exact Submodule.mem_span_singleton_self _
    rw [← lineE1_eq_negation] at hmem
    exact hout1 hmem
  have hcomp : ¬ Compatible lineE0 (atomOf u) :=
    not_compatible_third_ray lineE0_finrank hfin hne hneo
  exact ⟨ray_not_mem_island hfin hne hneo, hcomp,
    (material_detach_iff_compatible).not.mpr hcomp⟩

private theorem perp_order_inner_im (θ : ℝ) :
    (inner ℂ (afterPerp θ θ) (afterPerpRev θ θ)).im =
      -2 * Real.cos (θ / 2) ^ 2 * Real.sin (θ / 2) ^ 2 := by
  rw [dualSpinor_inner_eq, Fin.sum_univ_two, (perp_coord θ θ).1, (perp_coord θ θ).2,
    (perpRev_coord θ θ).1, (perpRev_coord θ θ).2]
  simp only [star_add, star_sub, star_mul', Complex.star_def, Complex.conj_ofReal, Complex.conj_I]
  simp only [Complex.add_im, Complex.sub_im, Complex.mul_im, Complex.mul_re, Complex.neg_im,
    Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring_nf
  simp only [← Complex.ofReal_pow, Complex.ofReal_re, Complex.ofReal_im, Complex.neg_re,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.add_re, Complex.sub_re]
  ring

private theorem perp_orders_not_ortho {θ : ℝ} (h0 : 0 < θ) (hπ : θ < Real.pi) :
    ¬ atomOf (afterPerp θ θ) ⟂ atomOf (afterPerpRev θ θ) := by
  intro hortho
  have hzero := hortho.inner_eq (Submodule.mem_span_singleton_self _)
    (Submodule.mem_span_singleton_self _)
  have him := congrArg Complex.im hzero
  rw [perp_order_inner_im, Complex.zero_im] at him
  obtain ⟨hc, hs⟩ := half_trig_pos h0 hπ
  nlinarith [sq_pos_of_pos hc, sq_pos_of_pos hs]

theorem perp_orders_outside {θ : ℝ} (h0 : 0 < θ) (hπ : θ < Real.pi) :
    atomOf (afterPerp θ θ) ≠ atomOf (afterPerpRev θ θ) ∧
      atomOf (afterPerp θ θ) ∉ Island lineE0 ∧
      atomOf (afterPerpRev θ θ) ∉ Island lineE0 ∧
      ¬ Compatible lineE0 (atomOf (afterPerp θ θ)) ∧
      ¬ Compatible lineE0 (atomOf (afterPerpRev θ θ)) ∧
      ¬ lineE0 ⊓ material lineE0 (atomOf (afterPerp θ θ)) ≤ atomOf (afterPerp θ θ) ∧
      ¬ lineE0 ⊓ material lineE0 (atomOf (afterPerpRev θ θ)) ≤
        atomOf (afterPerpRev θ θ) ∧
      ¬ Compatible (atomOf (afterPerp θ θ)) (atomOf (afterPerpRev θ θ)) := by
  have hf := perp_forward_coords_ne h0 hπ
  have hr := perp_reverse_coords_ne h0 hπ
  have houtF := atom_outside_computational hf.1 hf.2
  have houtR := atom_outside_computational hr.1 hr.2
  have hfinF : finrank ℂ (atomOf (afterPerp θ θ)) = 1 :=
    finrank_span_singleton (carrier_ne_zero_of_coord hf.1)
  have hfinR : finrank ℂ (atomOf (afterPerpRev θ θ)) = 1 :=
    finrank_span_singleton (carrier_ne_zero_of_coord hr.1)
  refine ⟨perp_atom_ne h0 hπ h0 hπ, houtF.1, houtR.1, houtF.2.1, houtR.2.1, houtF.2.2,
    houtR.2.2, ?_⟩
  intro hc
  rcases (compatible_line_iff hfinF hfinR).mp hc with hEq | hortho
  · exact perp_atom_ne h0 hπ h0 hπ hEq
  · exact perp_orders_not_ortho h0 hπ hortho

private theorem phase_factor_ne_zero (φ : ℝ) :
    (Real.cos (φ / 2) : ℂ) + Complex.I * (Real.sin (φ / 2) : ℂ) ≠ 0 := by
  intro hz
  have hns : Complex.normSq
      ((Real.cos (φ / 2) : ℂ) + Complex.I * (Real.sin (φ / 2) : ℂ)) = 1 := by
    rw [Complex.normSq_apply]
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
      Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul, sub_zero,
      add_zero, zero_add]
    have hsum := Real.cos_sq_add_sin_sq (φ / 2)
    linarith
  rw [hz, Complex.normSq_zero] at hns
  exact zero_ne_one hns

private theorem axial_reverse_coords_ne {θ φ : ℝ} (hθ0 : 0 < θ) (hθπ : θ < Real.pi) :
    afterTransverseAxial θ φ 0 ≠ 0 ∧ afterTransverseAxial θ φ 1 ≠ 0 := by
  obtain ⟨hc, hs⟩ := half_trig_pos hθ0 hθπ
  have ha := axial_after_coord θ φ
  have ht := transverse_coord θ
  constructor
  · intro hz
    rw [ha.1, ht.1] at hz
    exact mul_ne_zero (axialFactor_ne_zero φ)
      (Complex.ofReal_ne_zero.mpr (ne_of_gt hc)) hz
  · intro hz
    rw [ha.2, ht.2] at hz
    exact mul_ne_zero (phase_factor_ne_zero φ)
      (mul_ne_zero (by simp [Complex.I_ne_zero])
        (Complex.ofReal_ne_zero.mpr (ne_of_gt hs))) hz

theorem axial_atom_computational (φ : ℝ) :
    atomOf (applyMat (dualRotorMat (EuclideanSpace.single (2 : Fin 3) φ)) spinUp) = lineE0 ∧
      applyMat (dualRotorMat (EuclideanSpace.single (2 : Fin 3) φ)) spinUp ∈ lineE0 ∧
      deviceError (applyMat (dualRotorMat (EuclideanSpace.single (2 : Fin 3) φ)) spinUp) =
        0 := by
  have hlin := axial_on_eigen φ
  have herr := (axial_no_logical_error φ).2.2
  refine ⟨?_, (axial_no_logical_error φ).1, herr⟩
  rw [hlin, spinUp_eq_e0]
  simpa [atomOf, lineE0] using span_smul (axialFactor_ne_zero φ)

theorem order_atom_error {N : ℕ} (hN : 3 ≤ N) :
    atomOf (afterPerp (stepAngle N) (stepAngle N)) ≠
        atomOf (afterPerpRev (stepAngle N) (stepAngle N)) ∧
      atomOf (afterPerp (stepAngle N) (stepAngle N)) ∉ Island lineE0 ∧
      atomOf (afterPerpRev (stepAngle N) (stepAngle N)) ∉ Island lineE0 ∧
      ¬ Compatible lineE0 (atomOf (afterPerp (stepAngle N) (stepAngle N))) ∧
      ¬ Compatible lineE0 (atomOf (afterPerpRev (stepAngle N) (stepAngle N))) ∧
      ¬ lineE0 ⊓ material lineE0 (atomOf (afterPerp (stepAngle N) (stepAngle N))) ≤
        atomOf (afterPerp (stepAngle N) (stepAngle N)) ∧
      ¬ lineE0 ⊓ material lineE0 (atomOf (afterPerpRev (stepAngle N) (stepAngle N))) ≤
        atomOf (afterPerpRev (stepAngle N) (stepAngle N)) ∧
      ¬ Compatible (atomOf (afterPerp (stepAngle N) (stepAngle N)))
        (atomOf (afterPerpRev (stepAngle N) (stepAngle N))) ∧
      deviceError (afterPerp (stepAngle N) (stepAngle N)) =
        deviceError (afterPerpRev (stepAngle N) (stepAngle N)) ∧
      deviceError (afterPerp (stepAngle N) (stepAngle N)) =
        (1 / 2) * deviceError (afterTransverse (2 * stepAngle N)) ∧
      deviceError (afterPerp (stepAngle N) (stepAngle N)) <
        2 * deviceError (afterTransverse (stepAngle N)) ∧
      atomOf (afterAxialTransverse (stepAngle N) (stepAngle N)) =
        atomOf (afterTransverse (stepAngle N)) ∧
      atomOf (afterTransverseAxial (stepAngle N) (stepAngle N)) ≠
        atomOf (afterTransverse (stepAngle N)) ∧
      atomOf (afterTransverseAxial (stepAngle N) (stepAngle N)) ∉ Island lineE0 ∧
      ¬ Compatible lineE0 (atomOf (afterTransverseAxial (stepAngle N) (stepAngle N))) ∧
      ¬ lineE0 ⊓ material lineE0
          (atomOf (afterTransverseAxial (stepAngle N) (stepAngle N))) ≤
        atomOf (afterTransverseAxial (stepAngle N) (stepAngle N)) ∧
      deviceError (afterAxialTransverse (stepAngle N) (stepAngle N)) =
        deviceError (afterTransverse (stepAngle N)) ∧
      deviceError (afterTransverseAxial (stepAngle N) (stepAngle N)) =
        deviceError (afterTransverse (stepAngle N)) ∧
      atomOf (applyMat (dualRotorMat (EuclideanSpace.single (2 : Fin 3) (stepAngle N)))
        spinUp) = lineE0 ∧
      deviceError (applyMat (dualRotorMat (EuclideanSpace.single (2 : Fin 3) (stepAngle N)))
        spinUp) = 0 := by
  have hpos : 0 < N := lt_of_lt_of_le (by decide : 0 < 3) hN
  have hθ : 0 < stepAngle N := stepAngle_pos hpos
  have hπ : stepAngle N < Real.pi := by
    unfold stepAngle
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hpos
    rw [div_lt_iff₀ hN0]
    have h2 : (2 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le (by decide : 2 < 3) hN)
    nlinarith [Real.pi_pos]
  have htwo : stepAngle N < 2 * Real.pi := by linarith [Real.pi_pos]
  have hper := perp_orders_outside hθ hπ
  have hlat := lattice_perp hN
  have hord := axial_order_changes_atom hθ hπ hθ htwo
  have hrev := axial_reverse_coords_ne (φ := stepAngle N) hθ hπ
  have hout := atom_outside_computational hrev.1 hrev.2
  have hax := axial_atom_computational (stepAngle N)
  exact ⟨hper.1, hper.2.1, hper.2.2.1, hper.2.2.2.1, hper.2.2.2.2.1, hper.2.2.2.2.2.1,
    hper.2.2.2.2.2.2.1, hper.2.2.2.2.2.2.2, hlat.2.1, hlat.2.2.1, hlat.2.2.2, hord.1,
    hord.2.1, hout.1, hout.2.1, hout.2.2, hord.2.2.2, hord.2.2.1, hax.1, hax.2.2⟩

private theorem step_lt_half_pi {N : ℕ} (hN : 8 ≤ N) :
    0 < stepAngle N ∧ stepAngle N < Real.pi / 2 := by
  have hpos : 0 < N := lt_of_lt_of_le (by decide : 0 < 8) hN
  refine ⟨stepAngle_pos hpos, ?_⟩
  unfold stepAngle
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hpos
  rw [div_lt_iff₀ hN0]
  have h4 : (4 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le (by decide : 4 < 8) hN)
  nlinarith [Real.pi_pos]

private theorem sin_sq_unit {α : ℝ} (h0 : 0 < α) (hπ : α < Real.pi / 2) :
    0 < Real.sin α ^ 2 ∧ Real.sin α ^ 2 < 1 := by
  have hs : 0 < Real.sin α := Real.sin_pos_of_pos_of_lt_pi h0 (by linarith [Real.pi_pos])
  have hc : 0 < Real.cos α := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hsum := Real.cos_sq_add_sin_sq α
  exact ⟨sq_pos_of_pos hs, by nlinarith [sq_pos_of_pos hc]⟩

private theorem classify?_open {j : ℝ} (h0 : 0 < j) (h1 : j < 1) :
    classify? j = some .U := by
  have habs : |j| ≤ 1 := by
    rw [abs_of_pos h0]
    exact h1.le
  have hU : classifyOfMem j habs = .U := (classifyOfMem_eq_U_iff habs).mpr ⟨h0, h1⟩
  simpa [classify?, habs] using hU

private theorem classify?_neg {j : ℝ} (hlo : -1 ≤ j) (hhi : j < 0) :
    classify? j = some .B := by
  have habs : |j| ≤ 1 := abs_le.mpr ⟨hlo, by linarith⟩
  have hB : classifyOfMem j habs = .B := (classifyOfMem_eq_B_iff habs).mpr ⟨hlo, hhi⟩
  simpa [classify?, habs] using hB

theorem order_height_ratio {N : ℕ} (hN : 8 ≤ N) :
    deviceError (afterPerp (stepAngle N) (stepAngle N)) /
        deviceError (afterTransverse (2 * stepAngle N)) =
      JNormalized (express (perpSteps N)) / JNormalized (express (alignedSteps 2 N)) ∧
      deviceError (afterPerp (stepAngle N) (stepAngle N)) /
          deviceError (afterTransverse (2 * stepAngle N)) = (1 : ℝ) / 2 ∧
        JNormalized (express (alignedSteps 2 N)) < JNormalized (express (perpSteps N)) ∧
          JNormalized (express (perpSteps N)) < 0 ∧
            classify? (JNormalized (express (perpSteps N))) = some .B ∧
              classify? (JNormalized (express (alignedSteps 2 N))) = some .B ∧
                HoldsNotF (JNormalized (express (perpSteps N))) ∧
                  HoldsNotF (JNormalized (express (alignedSteps 2 N))) ∧
                    ¬ HoldsT (JNormalized (express (perpSteps N))) ∧
                      ¬ HoldsT (JNormalized (express (alignedSteps 2 N))) ∧
                        classify? (deviceError (afterTransverse (stepAngle N))) = some .U ∧
                          classify? (deviceError (afterPerp (stepAngle N) (stepAngle N))) =
                            some .U ∧
                            classify? (deviceError (afterTransverse (2 * stepAngle N))) =
                              some .U := by
  set eOne := deviceError (afterTransverse (stepAngle N))
  set ePerp := deviceError (afterPerp (stepAngle N) (stepAngle N))
  set eAlign := deviceError (afterTransverse (2 * stepAngle N))
  set jPerp := JNormalized (express (perpSteps N))
  set jAlign := JNormalized (express (alignedSteps 2 N))
  have hpos : 0 < N := lt_of_lt_of_le (by decide : 0 < 8) hN
  have h3 : 3 ≤ N := le_trans (by decide : (3 : ℕ) ≤ 8) hN
  have h4 : 4 ≤ N := le_trans (by decide : (4 : ℕ) ≤ 8) hN
  have hlat := lattice_perp h3
  have hstep := step_lt_half_pi hN
  have honeForm := transverse_step_third_atom h3
  have halign := aligned_error_trig hstep.1
  have hden : eAlign ≠ 0 := by
    change deviceError (afterTransverse (2 * stepAngle N)) ≠ 0
    rw [halign]
    exact ne_of_gt (sin_sq_unit hstep.1 hstep.2).1
  have hleft : ePerp / eAlign = (1 : ℝ) / 2 := by
    change deviceError (afterPerp (stepAngle N) (stepAngle N)) /
        deviceError (afterTransverse (2 * stepAngle N)) = (1 : ℝ) / 2
    rw [hlat.2.2.1, mul_div_cancel_right₀ _ hden]
  have hadmA := (twoGravitons_fourfold hN).1
  have hadmP := perpSteps_admissible h4
  have hJA : jAlign = 4 * farHeight N := by
    change JNormalized (express (alignedSteps 2 N)) = 4 * farHeight N
    rw [express_eq_of_admissible hadmA, (twoGravitons_fourfold hN).2, alignedSteps_one]
    rfl
  have hJP : jPerp = 2 * farHeight N := by
    change JNormalized (express (perpSteps N)) = 2 * farHeight N
    rw [express_eq_of_admissible hadmP, (perp_twofold h4).2]
  have hfar := farHeight_eq hpos
  have hneg := farHeight_neg hpos
  have hlt : jAlign < jPerp := by
    rw [hJA, hJP]
    linarith
  have hjp0 : jPerp < 0 := by
    rw [hJP]
    linarith
  have hN8 : (8 : ℝ) ≤ N := by exact_mod_cast hN
  have hsq : (64 : ℝ) ≤ (N : ℝ) ^ 2 := by
    have hpow : (8 : ℝ) ^ 2 ≤ (N : ℝ) ^ 2 := pow_le_pow_left₀ (by norm_num) hN8 2
    norm_num at hpow
    exact hpow
  have habsA : |jAlign| ≤ 1 := by
    rw [hJA, hfar, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4), abs_neg,
      abs_of_pos (div_pos (by norm_num) (by positivity : (0 : ℝ) < 3 * (N : ℝ) ^ 2))]
    have hden3 : (0 : ℝ) < 3 * (N : ℝ) ^ 2 := by positivity
    have hform : 4 * (16 / (3 * (N : ℝ) ^ 2)) = 64 / (3 * (N : ℝ) ^ 2) := by ring
    rw [hform, div_le_one hden3]
    nlinarith [hsq]
  have habsP : |jPerp| ≤ 1 := by
    rw [hJP, hfar, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_neg,
      abs_of_pos (div_pos (by norm_num) (by positivity : (0 : ℝ) < 3 * (N : ℝ) ^ 2))]
    have hden3 : (0 : ℝ) < 3 * (N : ℝ) ^ 2 := by positivity
    have hform : 2 * (16 / (3 * (N : ℝ) ^ 2)) = 32 / (3 * (N : ℝ) ^ 2) := by ring
    rw [hform, div_le_one hden3]
    nlinarith [hsq]
  have hloA : -1 ≤ jAlign := (abs_le.mp habsA).1
  have hloP : -1 ≤ jPerp := (abs_le.mp habsP).1
  have hJden : jAlign ≠ 0 := ne_of_lt (lt_trans hlt hjp0)
  have hright : jPerp / jAlign = (1 : ℝ) / 2 := by
    rw [hJP, hJA]
    have hf : farHeight N ≠ 0 := ne_of_lt hneg
    field_simp [hf]
    norm_num
  have honeUnit := sin_sq_unit (by linarith : 0 < stepAngle N / 2)
    (by linarith : stepAngle N / 2 < Real.pi / 2)
  have halignUnit := sin_sq_unit hstep.1 hstep.2
  have honeBound : 0 < eOne ∧ eOne < 1 := by
    have hhalf : stepAngle N / 2 = Real.pi / N := by
      simpa using halfArg_eq (n := 1) hpos
    constructor
    · change 0 < deviceError (afterTransverse (stepAngle N))
      rw [honeForm.2.2.2.2, ← hhalf]
      exact honeUnit.1
    · change deviceError (afterTransverse (stepAngle N)) < 1
      rw [honeForm.2.2.2.2, ← hhalf]
      exact honeUnit.2
  have halignBound : 0 < eAlign ∧ eAlign < 1 := by
    constructor
    · change 0 < deviceError (afterTransverse (2 * stepAngle N))
      rw [halign]
      exact halignUnit.1
    · change deviceError (afterTransverse (2 * stepAngle N)) < 1
      rw [halign]
      exact halignUnit.2
  have hperpBound : 0 < ePerp ∧ ePerp < 1 := by
    constructor
    · change 0 < deviceError (afterPerp (stepAngle N) (stepAngle N))
      rw [hlat.2.2.1]
      exact mul_pos (by norm_num) halignBound.1
    · change deviceError (afterPerp (stepAngle N) (stepAngle N)) < 1
      rw [hlat.2.2.1]
      nlinarith [halignBound.1, halignBound.2]
  refine ⟨hleft.trans hright.symm, hleft, hlt, hjp0, classify?_neg hloP hjp0,
    classify?_neg hloA (lt_trans hlt hjp0), ?_, ?_, ?_, ?_,
    classify?_open honeBound.1 honeBound.2, classify?_open hperpBound.1 hperpBound.2,
    classify?_open halignBound.1 halignBound.2⟩
  · change jPerp < 1
    linarith
  · change jAlign < 1
    linarith
  · intro hT
    exact hjp0.ne hT
  · intro hT
    exact (lt_trans hlt hjp0).ne hT

end DoubleSpacetime.Gravity.GravitonLogic

end
