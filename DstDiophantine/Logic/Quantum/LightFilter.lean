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
four-vector on the future light cone, and every future lightlike four-vector
arises in this way. A unit phase leaves it fixed, and a dual rotor turns
only its spatial part. Superposition is not addition in the chart: the sum
of two manifested four-vectors may be timelike, the discrepancy may be
spacelike, and a relative phase, invisible in either summand, turns the
null direction of the superposition.
-/

namespace DstDiophantine

namespace Logic

open Operations Invariant Complex

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

/-! ### The image is the future light cone -/

/-- A dual spinor with the two components `a` and `b`. -/
noncomputable def dualOf (a b : ℂ) : DualSpinor :=
  WithLp.toLp 2 ![a, b]

@[simp] theorem dualOf_zero (a b : ℂ) : dualOf a b 0 = a := rfl

@[simp] theorem dualOf_one (a b : ℂ) : dualOf a b 1 = b := rfl

private theorem re_add_star (z : ℂ) : (z + star z).re = 2 * z.re := by
  simp [Complex.add_re, Complex.conj_re]
  ring

private theorem spinExp_pauliX_coord (u : DualSpinor) :
    spinExp pauliX u = (starRingEnd ℂ) (u 0) * u 1 + (starRingEnd ℂ) (u 1) * u 0 := by
  rw [spinExp, dualSpinor_inner_eq]
  simp [applyMat_apply, pauliX, Fin.sum_univ_two]

private theorem spinExp_pauliY_coord (u : DualSpinor) :
    spinExp pauliY u =
      (starRingEnd ℂ) (u 0) * (-I * u 1) + (starRingEnd ℂ) (u 1) * (I * u 0) := by
  rw [spinExp, dualSpinor_inner_eq]
  simp [applyMat_apply, pauliY, Fin.sum_univ_two]

private theorem spinExp_pauliZ_coord (u : DualSpinor) :
    spinExp pauliZ u = (starRingEnd ℂ) (u 0) * u 0 - (starRingEnd ℂ) (u 1) * u 1 := by
  rw [spinExp, dualSpinor_inner_eq]
  simp [applyMat_apply, pauliZ, Fin.sum_univ_two]
  ring

theorem spinVec_coord_zero (u : DualSpinor) :
    spinVec u 0 = 2 * ((starRingEnd ℂ) (u 0) * u 1).re := by
  have hstar : (starRingEnd ℂ) (u 1) * u 0 = star ((starRingEnd ℂ) (u 0) * u 1) := by
    simp [star_mul', mul_comm]
  rw [spinVec, show pauli 0 = pauliX from rfl, spinExp_pauliX_coord, hstar, re_add_star]

theorem spinVec_coord_one (u : DualSpinor) :
    spinVec u 1 = 2 * ((starRingEnd ℂ) (u 0) * u 1).im := by
  set z := (starRingEnd ℂ) (u 0) * u 1
  have hsecond : (starRingEnd ℂ) (u 1) * (I * u 0) = I * star z := by
    simp [z, star_mul', mul_assoc, mul_left_comm, mul_comm]
  have hfirst : (starRingEnd ℂ) (u 0) * (-I * u 1) = -I * z := by
    simp [z, mul_assoc, mul_left_comm, mul_comm]
  rw [spinVec, show pauli 1 = pauliY from rfl, spinExp_pauliY_coord, hfirst, hsecond]
  simp [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.conj_re, Complex.conj_im]
  ring

theorem spinVec_coord_two (u : DualSpinor) :
    spinVec u 2 = ‖u 0‖ ^ 2 - ‖u 1‖ ^ 2 := by
  rw [spinVec, show pauli 2 = pauliZ from rfl, spinExp_pauliZ_coord]
  simp [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, Complex.sub_re]
  norm_cast

theorem informationWeight_coord (u : DualSpinor) :
    informationWeight u = ‖u 0‖ ^ 2 + ‖u 1‖ ^ 2 := by
  unfold informationWeight
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]

private theorem futureNull_space_sq {v : Vec4} (hQ : Q31 v = 0) :
    v 1 ^ 2 + v 2 ^ 2 + v 3 ^ 2 = v 0 ^ 2 := by
  rw [Q31_eq_minkowskiDot, minkowskiDot] at hQ
  linarith

private theorem futureNull_time_add_nonneg {v : Vec4} (hQ : Q31 v = 0) (ht : 0 ≤ v 0) :
    0 ≤ v 0 + v 3 := by
  have hspace := futureNull_space_sq hQ
  have hz : v 3 ^ 2 ≤ v 0 ^ 2 := by nlinarith [sq_nonneg (v 1), sq_nonneg (v 2)]
  have habs : |v 3| ≤ |v 0| := (sq_le_sq).mp hz
  rw [abs_of_nonneg ht] at habs
  linarith [neg_le_of_abs_le habs]

private theorem futureNull_vanish_of_add_zero {v : Vec4}
    (hQ : Q31 v = 0) (hz : v 0 + v 3 = 0) : v 1 = 0 ∧ v 2 = 0 ∧ v 3 = -v 0 := by
  have hz' : v 3 = -v 0 := by linarith
  have hspace := futureNull_space_sq hQ
  rw [hz'] at hspace
  have hxy : v 1 ^ 2 + v 2 ^ 2 = 0 := by nlinarith
  have hx : v 1 = 0 := by nlinarith [sq_nonneg (v 1), sq_nonneg (v 2)]
  have hy : v 2 = 0 := by nlinarith [sq_nonneg (v 1), sq_nonneg (v 2)]
  exact ⟨hx, hy, hz'⟩

/-- A dual spinor whose manifestation is a prescribed future lightlike four-vector. -/
noncomputable def spinorOfNull (v : Vec4) : DualSpinor :=
  if v 0 + v 3 = 0 then
    dualOf 0 (Real.sqrt (v 0))
  else
    dualOf (Real.sqrt ((v 0 + v 3) / 2))
      (((v 1 : ℂ) + (v 2 : ℂ) * I) /
        (2 * (Real.sqrt ((v 0 + v 3) / 2) : ℂ)))

private theorem norm_sq_real_add_I (x y : ℝ) :
    ‖(x : ℂ) + (y : ℂ) * I‖ ^ 2 = x ^ 2 + y ^ 2 := by
  have hxy : (x : ℂ) + (y : ℂ) * I = ⟨x, y⟩ := by
    apply Complex.ext <;> simp
  rw [hxy, ← Complex.normSq_eq_norm_sq, Complex.normSq_mk]
  ring

theorem manifest_spinorOfNull {v : Vec4} (hQ : Q31 v = 0) (ht : 0 ≤ v 0) :
    manifest (spinorOfNull v) = v := by
  have hadd := futureNull_time_add_nonneg hQ ht
  unfold spinorOfNull
  split_ifs with hz
  · obtain ⟨hx, hy, hz'⟩ := futureNull_vanish_of_add_zero hQ hz
    have hs : (Real.sqrt (v 0)) ^ 2 = v 0 := Real.sq_sqrt ht
    funext i
    fin_cases i
    · simp [manifest, informationWeight_coord, hx, hy, hz', hs]
    · simp [manifest, spinVec_coord_zero, hx]
    · simp [manifest, spinVec_coord_one, hy]
    · simp [manifest, spinVec_coord_two, hz', hs, Complex.norm_real, Real.norm_of_nonneg
        (Real.sqrt_nonneg _), sq_abs]
  · set s : ℝ := Real.sqrt ((v 0 + v 3) / 2)
    have hspos : 0 < s := by
      refine Real.sqrt_pos.mpr ?_
      have hlt : 0 < v 0 + v 3 := lt_of_le_of_ne hadd (Ne.symm hz)
      linarith
    have hs0 : (s : ℂ) ≠ 0 := by exact_mod_cast hspos.ne'
    have hsq : s ^ 2 = (v 0 + v 3) / 2 := Real.sq_sqrt (by linarith)
    have hspace := futureNull_space_sq hQ
    have hxy : v 1 ^ 2 + v 2 ^ 2 = (v 0 - v 3) * (v 0 + v 3) := by
      nlinarith
    set u : DualSpinor := dualOf s (((v 1 : ℂ) + (v 2 : ℂ) * I) / (2 * (s : ℂ)))
    have hu0 : u 0 = s := by simp [u]
    have hu1 : u 1 = ((v 1 : ℂ) + (v 2 : ℂ) * I) / (2 * (s : ℂ)) := by simp [u]
    have hnorm0 : ‖u 0‖ ^ 2 = (v 0 + v 3) / 2 := by
      rw [hu0, Complex.norm_real, Real.norm_of_nonneg (le_of_lt hspos), hsq]
    have hnorm1 : ‖u 1‖ ^ 2 = (v 0 - v 3) / 2 := by
      rw [hu1, norm_div, div_pow, norm_sq_real_add_I]
      have hden : ‖(2 : ℂ) * (s : ℂ)‖ ^ 2 = 2 * (v 0 + v 3) := by
        rw [norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_of_nonneg (le_of_lt hspos)]
        nlinarith [hsq]
      rw [hden, hxy]
      have hpos : 0 < v 0 + v 3 := lt_of_le_of_ne hadd (Ne.symm hz)
      field_simp
    have hcross : (starRingEnd ℂ) (u 0) * u 1 = ((v 1 : ℂ) + (v 2 : ℂ) * I) / 2 := by
      rw [hu0, hu1]
      have hstar : (starRingEnd ℂ) (s : ℂ) = s := by simp
      rw [hstar]
      have hhalf : (s : ℂ) / (2 * (s : ℂ)) = 1 / 2 := by field_simp
      calc (s : ℂ) * (((v 1 : ℂ) + (v 2 : ℂ) * I) / (2 * (s : ℂ)))
          = ((v 1 : ℂ) + (v 2 : ℂ) * I) * ((s : ℂ) / (2 * (s : ℂ))) := by ring
        _ = ((v 1 : ℂ) + (v 2 : ℂ) * I) * (1 / 2) := by rw [hhalf]
        _ = ((v 1 : ℂ) + (v 2 : ℂ) * I) / 2 := by ring
    have htime : informationWeight u = v 0 := by
      rw [informationWeight_coord, hnorm0, hnorm1]
      ring
    have hx : spinVec u 0 = v 1 := by
      rw [spinVec_coord_zero, hcross]
      simp [Complex.div_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im]
      ring
    have hy : spinVec u 1 = v 2 := by
      rw [spinVec_coord_one, hcross]
      simp [Complex.div_im, Complex.add_im, Complex.mul_im, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im]
      ring
    have hzv : spinVec u 2 = v 3 := by
      rw [spinVec_coord_two, hnorm0, hnorm1]
      ring
    funext i
    fin_cases i <;> simp [manifest, htime, hx, hy, hzv]

/-- A four-vector is the manifestation of some dual spinor exactly when it is
future lightlike. -/
theorem exists_manifest_iff (v : Vec4) :
    (∃ u : DualSpinor, manifest u = v) ↔ Q31 v = 0 ∧ 0 ≤ v 0 := by
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨Q31_manifest u, manifest_time_nonneg u⟩
  · intro h
    exact ⟨spinorOfNull v, manifest_spinorOfNull h.1 h.2⟩

/-! ### Superposition does not add in the chart -/

theorem spinExp_add_sub (A : Matrix (Fin 2) (Fin 2) ℂ) (u v : DualSpinor) :
    spinExp A (u + v) + spinExp A (u - v) = 2 * spinExp A u + 2 * spinExp A v := by
  simp only [spinExp]
  have hadd : applyMat A (u + v) = applyMat A u + applyMat A v := applyMat_add _ _ _
  have hsub : applyMat A (u - v) = applyMat A u - applyMat A v := by
    rw [sub_eq_add_neg, ← neg_one_smul (R := ℂ) v, applyMat_add, applyMat_smul, sub_eq_add_neg]
    simp
  rw [hadd, hsub]
  simp only [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right]
  ring

theorem informationWeight_add_sub (u v : DualSpinor) :
    informationWeight (u + v) + informationWeight (u - v) =
      2 * informationWeight u + 2 * informationWeight v := by
  have h := congrArg Complex.re (spinExp_add_sub 1 u v)
  simp only [spinExp_one, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero] at h
  simpa [informationWeight] using h

theorem spinVec_add_sub (u v : DualSpinor) :
    spinVec (u + v) + spinVec (u - v) = (2 : ℝ) • spinVec u + (2 : ℝ) • spinVec v := by
  funext k
  have h := congrArg Complex.re (spinExp_add_sub (pauli k) u v)
  simp only [spinExp_pauli] at h
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
    sub_zero] at h
  simpa [Pi.add_apply, Pi.smul_apply] using h

/-- Addition of information, read after the filter, keeps only the parallelogram
identity. The cross term cancels between the two relative signs. -/
theorem manifest_add_sub (u v : DualSpinor) :
    manifest (u + v) + manifest (u - v) =
      (2 : ℝ) • manifest u + (2 : ℝ) • manifest v := by
  funext i
  fin_cases i
  · simpa [manifest, Pi.add_apply, Pi.smul_apply] using informationWeight_add_sub u v
  · simpa [manifest, Pi.add_apply, Pi.smul_apply] using congrFun (spinVec_add_sub u v) 0
  · simpa [manifest, Pi.add_apply, Pi.smul_apply] using congrFun (spinVec_add_sub u v) 1
  · simpa [manifest, Pi.add_apply, Pi.smul_apply] using congrFun (spinVec_add_sub u v) 2

theorem spinUp_eq_dualOf : spinUp = dualOf 1 0 := by
  ext i
  fin_cases i <;> simp [spinUp, EuclideanSpace.single, PiLp.single_apply]

theorem spinDown_eq_dualOf : spinDown = dualOf 0 1 := by
  ext i
  fin_cases i <;> simp [spinDown, EuclideanSpace.single, PiLp.single_apply]

theorem manifest_spinUp : manifest spinUp = ![1, 0, 0, 1] := by
  rw [spinUp_eq_dualOf]
  funext i
  fin_cases i <;> simp [manifest, informationWeight_coord, spinVec_coord_zero, spinVec_coord_one,
    spinVec_coord_two]

theorem manifest_spinDown : manifest spinDown = ![1, 0, 0, -1] := by
  rw [spinDown_eq_dualOf]
  funext i
  fin_cases i <;> simp [manifest, informationWeight_coord, spinVec_coord_zero, spinVec_coord_one,
    spinVec_coord_two]

theorem manifest_spinUp_add_spinDown : manifest (spinUp + spinDown) = ![2, 2, 0, 0] := by
  have hvec : spinUp + spinDown = dualOf 1 1 := by
    rw [spinUp_eq_dualOf, spinDown_eq_dualOf]
    ext i
    fin_cases i <;> simp [PiLp.add_apply]
  rw [hvec]
  funext i
  fin_cases i
  · simp [manifest, informationWeight_coord]
    norm_num
  · simp [manifest, spinVec_coord_zero]
  · simp [manifest, spinVec_coord_one]
  · simp [manifest, spinVec_coord_two]

theorem manifest_spinUp_add_manifest_spinDown :
    manifest spinUp + manifest spinDown = ![2, 0, 0, 0] := by
  rw [manifest_spinUp, manifest_spinDown]
  funext i
  fin_cases i
  · simp; norm_num
  · simp
  · simp
  · simp

/-- The appearances of the two basis vectors add to a timelike four-vector. -/
theorem Q31_add_manifest_basis :
    Q31 (manifest spinUp + manifest spinDown) < 0 := by
  rw [manifest_spinUp_add_manifest_spinDown, Q31_eq_minkowskiDot]
  simp [minkowskiDot]

/-- The appearance of the superposition is not the sum of the appearances. -/
theorem manifest_not_additive :
    manifest (spinUp + spinDown) ≠ manifest spinUp + manifest spinDown := by
  rw [manifest_spinUp_add_spinDown, manifest_spinUp_add_manifest_spinDown]
  intro h
  have := congrFun h 1
  simp at this

/-- The discrepancy between the superposition and the sum of the appearances
is spacelike. -/
theorem Q31_manifest_discrepancy :
    0 < Q31 (manifest (spinUp + spinDown) - (manifest spinUp + manifest spinDown)) := by
  rw [manifest_spinUp_add_spinDown, manifest_spinUp_add_manifest_spinDown, Q31_eq_minkowskiDot]
  simp [minkowskiDot]

theorem SameInformation_spinDown_phase : SameInformation spinDown ((I : ℂ) • spinDown) :=
  ⟨I, by simp, by simp⟩

theorem manifest_spinUp_add_phase : manifest (spinUp + (I : ℂ) • spinDown) = ![2, 0, 2, 0] := by
  have hvec : spinUp + (I : ℂ) • spinDown = dualOf 1 I := by
    rw [spinUp_eq_dualOf, spinDown_eq_dualOf]
    ext i
    fin_cases i <;> simp [PiLp.add_apply, PiLp.smul_apply]
  rw [hvec]
  funext i
  fin_cases i
  · simp [manifest, informationWeight_coord]
    norm_num
  · simp [manifest, spinVec_coord_zero]
  · simp [manifest, spinVec_coord_one]
  · simp [manifest, spinVec_coord_two]

/-- A relative phase, which does not change either summand's appearance, turns
the null direction of the superposition. -/
theorem manifest_relativePhase :
    manifest (spinUp + (I : ℂ) • spinDown) ≠ manifest (spinUp + spinDown) := by
  rw [manifest_spinUp_add_phase, manifest_spinUp_add_spinDown]
  intro h
  have := congrFun h 1
  simp at this

theorem not_SameInformation_relativePhase :
    ¬ SameInformation (spinUp + spinDown) (spinUp + (I : ℂ) • spinDown) := by
  intro h
  exact manifest_relativePhase (manifest_sameInformation h)

end Logic

end DstDiophantine
