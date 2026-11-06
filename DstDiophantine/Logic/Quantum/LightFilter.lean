import DstDiophantine.Algebra.Operations
import DstDiophantine.Algebra.QuadraticForm
import DstDiophantine.Logic.Quantum.DualObservables
import DstDiophantine.Logic.Quantum.Separation

/-!
# Dual Hilbert space and the light-cone filter

The body of a quantum state is a vector of the dual sector `ℂ²`. The joint
rapidity pairing is indefinite, so it is not that space. Two dual spinors
carry the same information when one is a unit-modulus phase times the other.

Manifestation into the usual chart is the four-vector whose time component
is the squared norm and whose spatial part is the spin vector. The identity
`|r(u)|² = ‖u‖⁴`, read in signature `(-,+,+,+)`, places every such
four-vector on the future light cone. A unit phase leaves it fixed, and a
dual rotor turns only its spatial part.
-/

namespace DstDiophantine

namespace Logic

open Operations Invariant

/-! ### The body of the information -/

/-- Two dual spinors carry the same information when one is a phase of
modulus one times the other. -/
def SameInformation (ψ φ : DualSpinor) : Prop :=
  ∃ z : ℂ, ‖z‖ = 1 ∧ φ = z • ψ

/-- Information weight: the squared Hilbert norm of a dual spinor. -/
noncomputable def informationWeight (u : DualSpinor) : ℝ :=
  ‖u‖ ^ 2

theorem informationWeight_nonneg (u : DualSpinor) : 0 ≤ informationWeight u := by
  unfold informationWeight
  positivity

theorem informationWeight_eq_zero_iff (u : DualSpinor) :
    informationWeight u = 0 ↔ u = 0 := by
  unfold informationWeight
  rw [sq_eq_zero_iff, norm_eq_zero]

/-- The joint rapidity pairing takes negative values, so it is not the
information weight. -/
theorem killingForm_not_informationWeight :
    ¬ ∀ p : TorsionParams, 0 ≤ killingForm p p :=
  killingForm_not_positive_definite

theorem SameInformation_refl (ψ : DualSpinor) : SameInformation ψ ψ :=
  ⟨1, by simp, by simp⟩

private theorem star_mul_self_of_norm_one {z : ℂ} (hz : ‖z‖ = 1) :
    (starRingEnd ℂ) z * z = 1 := by
  have hsq : ‖z‖ ^ 2 = 1 := by rw [hz]; norm_num
  rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hsq]
  simp

theorem SameInformation_symm {ψ φ : DualSpinor} (h : SameInformation ψ φ) :
    SameInformation φ ψ := by
  obtain ⟨z, hz, rfl⟩ := h
  refine ⟨(starRingEnd ℂ) z, ?_, ?_⟩
  · simpa using hz
  · rw [smul_smul, star_mul_self_of_norm_one hz, one_smul]

theorem SameInformation_trans {ψ φ χ : DualSpinor}
    (hφ : SameInformation ψ φ) (hχ : SameInformation φ χ) : SameInformation ψ χ := by
  obtain ⟨z, hz, rfl⟩ := hφ
  obtain ⟨w, hw, rfl⟩ := hχ
  refine ⟨w * z, ?_, ?_⟩
  · rw [norm_mul, hz, hw, mul_one]
  · rw [smul_smul]

theorem SameInformation_zero_iff (φ : DualSpinor) : SameInformation 0 φ ↔ φ = 0 := by
  constructor
  · rintro ⟨_, _, h⟩
    simpa using h
  · rintro rfl
    exact SameInformation_refl 0

/-! ### The four-vector written into the usual chart -/

/-- Manifestation of a dual spinor. The time component is the information
weight; the spatial components are the spin vector. -/
noncomputable def manifest (u : DualSpinor) : Vec4
  | 0 => informationWeight u
  | 1 => spinVec u 0
  | 2 => spinVec u 1
  | 3 => spinVec u 2

theorem manifest_zero (u : DualSpinor) : manifest u 0 = informationWeight u := rfl

theorem manifest_succ (u : DualSpinor) (k : Fin 3) : manifest u k.succ = spinVec u k := by
  fin_cases k <;> rfl

theorem manifest_time_nonneg (u : DualSpinor) : 0 ≤ manifest u 0 := by
  rw [manifest_zero]
  exact informationWeight_nonneg u

theorem spinExp_smul_vec (c : ℂ) (A : Matrix (Fin 2) (Fin 2) ℂ) (u : DualSpinor) :
    spinExp A (c • u) = (starRingEnd ℂ) c * c * spinExp A u := by
  rw [spinExp, spinExp, applyMat_smul, inner_smul_left, inner_smul_right, ← mul_assoc]

private theorem star_mul_self_norm (c : ℂ) : (starRingEnd ℂ) c * c = (‖c‖ ^ 2 : ℂ) := by
  rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
  simp

theorem spinVec_smul (c : ℂ) (u : DualSpinor) :
    spinVec (c • u) = fun k => ‖c‖ ^ 2 * spinVec u k := by
  funext k
  have h := spinExp_smul_vec c (pauli k) u
  rw [star_mul_self_norm, spinExp_pauli, spinExp_pauli] at h
  exact_mod_cast h

theorem informationWeight_smul (c : ℂ) (u : DualSpinor) :
    informationWeight (c • u) = ‖c‖ ^ 2 * informationWeight u := by
  unfold informationWeight
  rw [norm_smul, mul_pow]

theorem manifest_smul (c : ℂ) (u : DualSpinor) :
    manifest (c • u) = ‖c‖ ^ 2 • manifest u := by
  funext i
  fin_cases i
  · simp [manifest, informationWeight_smul]
  · simp [manifest, spinVec_smul]
  · simp [manifest, spinVec_smul]
  · simp [manifest, spinVec_smul]

/-- A phase of modulus one does not change the manifested four-vector. -/
theorem manifest_phase (u : DualSpinor) {z : ℂ} (hz : ‖z‖ = 1) :
    manifest (z • u) = manifest u := by
  rw [manifest_smul, hz]
  simp

theorem manifest_sameInformation {ψ φ : DualSpinor} (h : SameInformation ψ φ) :
    manifest φ = manifest ψ := by
  obtain ⟨z, hz, rfl⟩ := h
  exact manifest_phase ψ hz

theorem spinVec_zero : spinVec (0 : DualSpinor) = 0 := by
  funext k
  simp [spinVec, spinExp, applyMat, Matrix.mulVec_zero]

theorem manifest_eq_zero_iff (u : DualSpinor) : manifest u = 0 ↔ u = 0 := by
  constructor
  · intro h
    have h0 : manifest u 0 = 0 := congrFun h 0
    rw [manifest_zero, informationWeight_eq_zero_iff] at h0
    exact h0
  · rintro rfl
    funext i
    fin_cases i <;> simp [manifest, informationWeight, spinVec_zero]

/-- Every manifested four-vector is lightlike. -/
theorem Q31_manifest (u : DualSpinor) : Q31 (manifest u) = 0 := by
  rw [Q31_eq_minkowskiDot]
  have h := axisDot_spinVec u
  simp only [minkowskiDot, manifest, informationWeight, axisDot] at h ⊢
  nlinarith [sq_nonneg (‖u‖ ^ 2)]

theorem manifest_not_timelike (u : DualSpinor) : ¬ Q31 (manifest u) < 0 := by
  rw [Q31_manifest]
  exact lt_irrefl 0

theorem manifest_not_spacelike (u : DualSpinor) : ¬ 0 < Q31 (manifest u) := by
  rw [Q31_manifest]
  exact lt_irrefl 0

theorem manifest_time_of_norm {u : DualSpinor} (hu : ‖u‖ = 1) : manifest u 0 = 1 := by
  simp [manifest, informationWeight, hu]

/-- On a unit dual spinor the spatial part of the manifestation is a unit vector. -/
theorem axisDot_manifest_space_of_norm {u : DualSpinor} (hu : ‖u‖ = 1) :
    axisDot (fun k : Fin 3 => manifest u k.succ) (fun k => manifest u k.succ) = 1 := by
  have hfun : (fun k : Fin 3 => manifest u k.succ) = spinVec u := by
    funext k
    rw [manifest_succ]
  rw [hfun, axisDot_spinVec_of_norm hu]

/-! ### Dual rotors preserve the cone and turn the direction -/

theorem informationWeight_dualRotor (β : DualRapidity) (u : DualSpinor) :
    informationWeight (applyMat (dualRotorMat β) u) = informationWeight u := by
  unfold informationWeight
  exact norm_applyMat_dualRotor_sq β u

theorem manifest_time_dualRotor (β : DualRapidity) (u : DualSpinor) :
    manifest (applyMat (dualRotorMat β) u) 0 = manifest u 0 := by
  simp [manifest, informationWeight_dualRotor]

theorem manifest_dualRotor_zero (u : DualSpinor) :
    manifest (applyMat (dualRotorMat 0) u) = manifest u := by
  rw [dualRotorMat_zero, applyMat_one]

/-- A nonzero dual rotor turns the spatial part by the full angle and leaves
the four-vector lightlike. -/
theorem manifest_space_dualRotor {β : DualRapidity} (hβ : β ≠ 0) (u : DualSpinor) :
    (fun k : Fin 3 => manifest (applyMat (dualRotorMat β) u) k.succ) =
      axisRot (fun k => β k / ‖β‖) ‖β‖ (spinVec u) := by
  funext k
  rw [manifest_succ, spinVec_dualRotor hβ]

theorem Q31_manifest_dualRotor (β : DualRapidity) (u : DualSpinor) :
    Q31 (manifest (applyMat (dualRotorMat β) u)) = 0 :=
  Q31_manifest _

end Logic

end DstDiophantine
