import DstDiophantine.Logic.Quantum.DiracCovariance
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Dirac current, Gordon identity, and the spacetime Dirac equation

The adjoint matrix `A = -iγ⁰` is Hermitian and every `Aγ^μ` is
anti-Hermitian. The current of a single spinor is therefore `i` times a
real four-vector, whose time component is `Ψ†Ψ`.

For two solutions of mass `m` at the same momentum the current is the
momentum with its index raised, times the mass bilinear:
`m j^μ = -i η^{μμ} p_μ Ψ̄Φ`. The time component gives
`m ⟨Ψ, Φ⟩ = p₀ Ψ̄Φ`, so on a solution with `m ≠ 0` the mass bilinear is a
nonzero real multiple of `Ψ†Ψ`. The real current of one solution has
Minkowski square `-(Ψ̄Ψ)²`. A total rotor carrying the rest momentum to
`p` multiplies the density of a rest solution by `p₀ / m`; dual rotors
leave the density unchanged.

On spacetime the correspondence `p_μ ↦ -i∂_μ` gives the field equation
`γ^μ ∂_μ Ψ = -m Ψ`. A plane wave `e^{i p·x} u` solves it exactly when `u`
solves the momentum-space equation, and solutions of one mass form a
complex vector space. For any two differentiable solutions of the same
real mass the current is conserved: `∂_μ j^μ = 0`.
-/

namespace DstDiophantine

namespace Logic

open Matrix Complex

open scoped InnerProductSpace

/-! ### Adjoint relations -/

theorem applyDiracMat_inner_ct (M : Matrix (Fin 4) (Fin 4) ℂ) (Ψ Φ : DiracSpinor) :
    inner ℂ Ψ (applyDiracMat M Φ) = inner ℂ (applyDiracMat Mᴴ Ψ) Φ := by
  simp only [applyDiracMat, PiLp.inner_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_four,
    Matrix.conjTranspose_apply, RCLike.inner_apply]
  simp only [map_add, map_mul]
  ring_nf
  simp only [Complex.star_def, Complex.conj_conj]
  ring

theorem diracAdjointMat_hermitian : diracAdjointMatᴴ = diracAdjointMat := by
  unfold diracAdjointMat diracMat0
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose_apply]

theorem diracAdjointMat_mul_gamma_antiHermitian (μ : Fin 4) :
    (diracAdjointMat * diracMat μ)ᴴ = -(diracAdjointMat * diracMat μ) := by
  unfold diracAdjointMat
  fin_cases μ <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [diracMat, diracMat0, diracMat1, diracMat2, diracMat3, Matrix.conjTranspose_apply]

theorem inner_diracAdjoint_left (Ψ Φ : DiracSpinor) :
    inner ℂ (applyDiracMat diracAdjointMat Ψ) Φ =
      inner ℂ Ψ (applyDiracMat diracAdjointMat Φ) := by
  rw [applyDiracMat_inner_ct, diracAdjointMat_hermitian]

theorem diracAdjointMat_mul_slash_antiHermitian (p : Vec4) :
    (diracAdjointMat * slashMat p)ᴴ = -(diracAdjointMat * slashMat p) := by
  have h : diracAdjointMat * slashMat p =
      ∑ μ : Fin 4, (p μ : ℂ) • (diracAdjointMat * diracMat μ) := by
    simp only [slashMat, Finset.mul_sum, Matrix.mul_smul]
  rw [h, Matrix.conjTranspose_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [Matrix.conjTranspose_smul, diracAdjointMat_mul_gamma_antiHermitian, Complex.star_def,
    Complex.conj_ofReal, smul_neg]

/-! ### The current of a single spinor is `i` times a real vector -/

private theorem re_eq_zero_of_eq_neg_conj {z : ℂ} (h : z = -(starRingEnd ℂ) z) : z.re = 0 := by
  have := congrArg Complex.re h
  simp at this
  linarith

private theorem im_eq_zero_of_eq_conj {z : ℂ} (h : z = (starRingEnd ℂ) z) : z.im = 0 := by
  have := congrArg Complex.im h
  simp at this
  linarith

theorem diracCurrent_self_re (μ : Fin 4) (Ψ : DiracSpinor) :
    (diracCurrent μ Ψ Ψ).re = 0 := by
  apply re_eq_zero_of_eq_neg_conj
  unfold diracCurrent
  conv_lhs => rw [applyDiracMat_inner_ct, diracAdjointMat_mul_gamma_antiHermitian,
    applyDiracMat_neg, inner_neg_left]
  rw [inner_conj_symm]

theorem diracScalar_self_im (Ψ : DiracSpinor) : (diracScalar Ψ Ψ).im = 0 := by
  apply im_eq_zero_of_eq_conj
  unfold diracScalar
  conv_lhs => rw [applyDiracMat_inner_ct, diracAdjointMat_hermitian]
  rw [inner_conj_symm]

/-- Real current `J^μ = -i j^μ(Ψ,Ψ)`. -/
noncomputable def realCurrent (Ψ : DiracSpinor) : Vec4 :=
  fun μ => (-I * diracCurrent μ Ψ Ψ).re

theorem realCurrent_zero (Ψ : DiracSpinor) : realCurrent Ψ 0 = ‖Ψ‖ ^ 2 := by
  unfold realCurrent
  rw [diracCurrent_zero, inner_self_eq_norm_sq_to_K]
  rw [← mul_assoc, show -I * I = (1 : ℂ) by rw [neg_mul, I_mul_I, neg_neg], one_mul]
  norm_cast

/-- The density `Ψ†Ψ` is nonnegative and vanishes only at `Ψ = 0`. -/
theorem realCurrent_zero_pos {Ψ : DiracSpinor} (hΨ : Ψ ≠ 0) : 0 < realCurrent Ψ 0 := by
  rw [realCurrent_zero]
  have : 0 < ‖Ψ‖ := norm_pos_iff.mpr hΨ
  positivity

/-! ### Gordon identity in momentum space -/

theorem slashMat_anticomm (p : Vec4) (μ : Fin 4) :
    slashMat p * diracMat μ + diracMat μ * slashMat p =
      ((2 * minkowskiEta μ μ * p μ : ℝ) : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  have h : slashMat p * diracMat μ + diracMat μ * slashMat p =
      ∑ ν : Fin 4, (p ν : ℂ) • (diracMat ν * diracMat μ + diracMat μ * diracMat ν) := by
    simp only [slashMat, Finset.sum_mul, Finset.mul_sum, Matrix.smul_mul, Matrix.mul_smul,
      ← Finset.sum_add_distrib, smul_add]
  rw [h]
  simp_rw [diracMat_clifford]
  rw [Finset.sum_eq_single μ]
  · rw [smul_smul]
    congr 1
    push_cast
    ring
  · intro ν _ hν
    rw [minkowskiEta_off hν]
    simp
  · simp

/-- Gordon identity: for two solutions of mass `m` at `p`, the current is
the raised momentum times the mass bilinear. -/
theorem diracCurrent_gordon {m : ℝ} {p : Vec4} {Ψ Φ : DiracSpinor}
    (hΨ : DiracMomentum m p Ψ) (hΦ : DiracMomentum m p Φ) (μ : Fin 4) :
    (m : ℂ) * diracCurrent μ Ψ Φ =
      -I * ((minkowskiEta μ μ * p μ : ℝ) : ℂ) * diracScalar Ψ Φ := by
  have k1 : inner ℂ Ψ (applyDiracMat (diracAdjointMat * (diracMat μ * slashMat p)) Φ) =
      I * m * diracCurrent μ Ψ Φ := by
    unfold DiracMomentum at hΦ
    rw [← Matrix.mul_assoc, applyDiracMat_mul, hΦ, applyDiracMat_smul, inner_smul_right]
    rfl
  have k2 : inner ℂ Ψ (applyDiracMat (diracAdjointMat * (slashMat p * diracMat μ)) Φ) =
      I * m * diracCurrent μ Ψ Φ := by
    unfold DiracMomentum at hΨ
    rw [← Matrix.mul_assoc, applyDiracMat_mul, applyDiracMat_inner_ct,
      diracAdjointMat_mul_slash_antiHermitian, applyDiracMat_neg, applyDiracMat_mul, hΨ,
      applyDiracMat_smul, inner_neg_left, inner_smul_left, inner_diracAdjoint_left,
      ← applyDiracMat_mul]
    unfold diracCurrent
    simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
    ring
  have hsum : inner ℂ Ψ (applyDiracMat (diracAdjointMat *
      (slashMat p * diracMat μ + diracMat μ * slashMat p)) Φ) =
      2 * (I * m * diracCurrent μ Ψ Φ) := by
    rw [Matrix.mul_add, applyDiracMat_add_mat, inner_add_right, k1, k2]
    ring
  rw [slashMat_anticomm, Matrix.mul_smul, Matrix.mul_one, applyDiracMat_smul_mat,
    inner_smul_right] at hsum
  have hS : inner ℂ Ψ (applyDiracMat diracAdjointMat Φ) = diracScalar Ψ Φ := rfl
  rw [hS] at hsum
  push_cast at hsum ⊢
  linear_combination (I / 2) * hsum + ((m : ℂ) * diracCurrent μ Ψ Φ) * I_sq

/-- Time component of the Gordon identity: the Euclidean overlap of two
solutions is `p₀ / m` times their mass bilinear. -/
theorem inner_gordon {m : ℝ} {p : Vec4} {Ψ Φ : DiracSpinor}
    (hΨ : DiracMomentum m p Ψ) (hΦ : DiracMomentum m p Φ) :
    (m : ℂ) * inner ℂ Ψ Φ = (p 0 : ℂ) * diracScalar Ψ Φ := by
  have h := diracCurrent_gordon hΨ hΦ 0
  rw [diracCurrent_zero] at h
  simp only [minkowskiEta_diag, w31] at h
  push_cast at h
  have h' : I * ((m : ℂ) * inner ℂ Ψ Φ) = I * ((p 0 : ℂ) * diracScalar Ψ Φ) := by
    linear_combination h
  exact mul_left_cancel₀ I_ne_zero h'

/-- On a nonzero solution with `m ≠ 0` the energy component is nonzero and
the mass bilinear is `m / p₀` times `Ψ†Ψ`. -/
theorem diracScalar_self_eq {m : ℝ} {p : Vec4} {Ψ : DiracSpinor} (hm : m ≠ 0)
    (hΨ : Ψ ≠ 0) (h : DiracMomentum m p Ψ) :
    p 0 ≠ 0 ∧ diracScalar Ψ Ψ = ((m / p 0 * ‖Ψ‖ ^ 2 : ℝ) : ℂ) := by
  have hg := inner_gordon h h
  rw [inner_self_eq_norm_sq_to_K] at hg
  have hp0 : p 0 ≠ 0 := by
    intro h0
    rw [h0] at hg
    simp only [ofReal_zero, zero_mul] at hg
    have hn : ‖Ψ‖ ≠ 0 := norm_ne_zero_iff.mpr hΨ
    have : (m : ℂ) * (‖Ψ‖ : ℂ) ^ 2 ≠ 0 := by
      apply mul_ne_zero (ofReal_ne_zero.mpr hm)
      exact pow_ne_zero _ (ofReal_ne_zero.mpr hn)
    exact this hg
  refine ⟨hp0, ?_⟩
  have hp0C : (p 0 : ℂ) ≠ 0 := ofReal_ne_zero.mpr hp0
  push_cast
  field_simp
  linear_combination -hg

/-- On the forward shell with positive mass the mass bilinear is positive
and at most the density `Ψ†Ψ`. -/
theorem diracScalar_self_pos_le {m : ℝ} {p : Vec4} {Ψ : DiracSpinor} (hm : 0 < m)
    (hp : 0 < p 0) (hΨ : Ψ ≠ 0) (h : DiracMomentum m p Ψ) :
    0 < (diracScalar Ψ Ψ).re ∧ (diracScalar Ψ Ψ).re ≤ ‖Ψ‖ ^ 2 := by
  obtain ⟨-, hS⟩ := diracScalar_self_eq hm.ne' hΨ h
  have hQ := diracMomentum_implies_mass_shell hΨ h
  rw [minkowskiQ_eq] at hQ
  have hmp : m ≤ p 0 := by
    nlinarith [sq_nonneg (p 1), sq_nonneg (p 2), sq_nonneg (p 3)]
  have hn : 0 < ‖Ψ‖ ^ 2 := by
    have := norm_pos_iff.mpr hΨ
    positivity
  rw [hS, ofReal_re]
  refine ⟨by positivity, ?_⟩
  have : m / p 0 ≤ 1 := (div_le_one hp).mpr hmp
  nlinarith

/-- The real current of a solution is the raised momentum scaled by the mass
bilinear, and its Minkowski square is `-(Ψ̄Ψ)²`. -/
theorem realCurrent_gordon {m : ℝ} {p : Vec4} {Ψ : DiracSpinor} (hm : m ≠ 0)
    (h : DiracMomentum m p Ψ) (μ : Fin 4) :
    realCurrent Ψ μ = -(minkowskiEta μ μ * p μ) * (diracScalar Ψ Ψ).re / m := by
  have hg := diracCurrent_gordon h h μ
  have hmC : (m : ℂ) ≠ 0 := ofReal_ne_zero.mpr hm
  have hS : diracScalar Ψ Ψ = ((diracScalar Ψ Ψ).re : ℂ) := by
    apply Complex.ext <;> simp [diracScalar_self_im]
  have hj : -I * diracCurrent μ Ψ Ψ =
      ((-(minkowskiEta μ μ * p μ) * (diracScalar Ψ Ψ).re / m : ℝ) : ℂ) := by
    rw [hS] at hg
    push_cast at hg ⊢
    field_simp
    linear_combination (-I) * hg +
      ((minkowskiEta μ μ : ℂ) * (p μ : ℂ) * ((diracScalar Ψ Ψ).re : ℂ)) * I_sq
  unfold realCurrent
  rw [hj, ofReal_re]

theorem minkowskiQ_realCurrent {m : ℝ} {p : Vec4} {Ψ : DiracSpinor} (hm : m ≠ 0)
    (hΨ : Ψ ≠ 0) (h : DiracMomentum m p Ψ) :
    minkowskiQ (realCurrent Ψ) = -((diracScalar Ψ Ψ).re) ^ 2 := by
  have hQ := diracMomentum_implies_mass_shell hΨ h
  rw [minkowskiQ_eq] at hQ ⊢
  simp only [realCurrent_gordon hm h, minkowskiEta_diag, w31]
  field_simp
  linear_combination (diracScalar Ψ Ψ).re ^ 2 * hQ

/-- A total rotor that carries the rest momentum to `Λ p_rest` multiplies the
density of a rest solution by `(Λ p_rest)₀ / m`. -/
theorem norm_sq_rotorDirac_rest {M : Matrix (Fin 2) (Fin 2) ℂ} (hM : M.det = 1) {m : ℝ}
    (hm : m ≠ 0) {Ψ : DiracSpinor} (h : DiracMomentum m (restMomentum m) Ψ) :
    m * ‖rotorDirac M Ψ‖ ^ 2 = lorentzAct M (restMomentum m) 0 * ‖Ψ‖ ^ 2 := by
  have h' := diracMomentum_rotorDirac hM h
  have g1 := inner_gordon h' h'
  have g0 := inner_gordon h h
  rw [diracScalar_rotorDirac hM, inner_self_eq_norm_sq_to_K] at g1
  rw [inner_self_eq_norm_sq_to_K] at g0
  have hr : restMomentum m 0 = m := by simp [restMomentum]
  rw [hr] at g0
  have hmC : (m : ℂ) ≠ 0 := ofReal_ne_zero.mpr hm
  have hS : diracScalar Ψ Ψ = (‖Ψ‖ : ℂ) ^ 2 := (mul_left_cancel₀ hmC g0).symm
  rw [hS] at g1
  have h2 : ((m * ‖rotorDirac M Ψ‖ ^ 2 : ℝ) : ℂ) =
      ((lorentzAct M (restMomentum m) 0 * ‖Ψ‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    exact g1
  exact ofReal_injective h2

/-- Dual rotors leave the density unchanged. -/
theorem norm_rotorDirac_dualRotor (β : DualRapidity) (Ψ : DiracSpinor) :
    ‖rotorDirac (dualRotorMat β) Ψ‖ = ‖Ψ‖ := by
  have hU := dualRotorMat_unitary β
  have hU' : (dualRotorMat β)ᴴ * dualRotorMat β = 1 := hU
  have hinner : ∀ ψ : DualSpinor,
      inner ℂ (applyMat (dualRotorMat β) ψ) (applyMat (dualRotorMat β) ψ) = inner ℂ ψ ψ := by
    intro ψ
    simp only [applyMat, PiLp.inner_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      RCLike.inner_apply]
    have e00 := congrFun (congrFun hU' 0) 0
    have e01 := congrFun (congrFun hU' 0) 1
    have e10 := congrFun (congrFun hU' 1) 0
    have e11 := congrFun (congrFun hU' 1) 1
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
      Matrix.one_apply_eq, Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
      Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide)] at e00 e01 e10 e11
    simp only [map_add, map_mul, Complex.star_def] at e00 e01 e10 e11 ⊢
    linear_combination (starRingEnd ℂ (ψ 0) * ψ 0) * e00 + (starRingEnd ℂ (ψ 0) * ψ 1) * e01 +
      (starRingEnd ℂ (ψ 1) * ψ 0) * e10 + (starRingEnd ℂ (ψ 1) * ψ 1) * e11
  have hsq : ‖rotorDirac (dualRotorMat β) Ψ‖ ^ 2 = ‖Ψ‖ ^ 2 := by
    have key : inner ℂ (rotorDirac (dualRotorMat β) Ψ) (rotorDirac (dualRotorMat β) Ψ) =
        inner ℂ Ψ Ψ := by
      rw [← weyl_decompose' Ψ, rotorDirac_weyl, rotorLower_dualRotor, inner_add_left,
        inner_add_right, inner_add_right, inner_add_left, inner_add_right, inner_add_right,
        weylUpper_inner_upper, weylUpper_inner_lower, weylLower_inner_upper,
        weylLower_inner_lower, weylUpper_inner_upper, weylUpper_inner_lower,
        weylLower_inner_upper, weylLower_inner_lower, hinner, hinner]
    rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at key
    exact_mod_cast key
  have h1 := norm_nonneg (rotorDirac (dualRotorMat β) Ψ)
  have h2 := norm_nonneg Ψ
  nlinarith [sq_nonneg (‖rotorDirac (dualRotorMat β) Ψ‖ - ‖Ψ‖),
    sq_nonneg (‖rotorDirac (dualRotorMat β) Ψ‖ + ‖Ψ‖)]

/-! ### Spacetime Dirac equation -/

/-- Partial derivative `∂_μ Ψ`. -/
noncomputable def partialD (Ψ : Vec4 → DiracSpinor) (μ : Fin 4) (x : Vec4) : DiracSpinor :=
  fderiv ℝ Ψ x (Pi.single μ 1)

/-- Dirac operator `γ^μ ∂_μ`. -/
noncomputable def diracOp (Ψ : Vec4 → DiracSpinor) (x : Vec4) : DiracSpinor :=
  ∑ μ : Fin 4, applyDiracMat (diracMat μ) (partialD Ψ μ x)

/-- Spacetime Dirac equation `γ^μ ∂_μ Ψ = -m Ψ`, the image of
`γ(p) Ψ = i m Ψ` under `p_μ ↦ -i ∂_μ`. -/
def DiracField (m : ℝ) (Ψ : Vec4 → DiracSpinor) : Prop :=
  Differentiable ℝ Ψ ∧ ∀ x, diracOp Ψ x = (-(m : ℂ)) • Ψ x

/-- Phase `p_μ x^μ`. -/
def wavePhase (p x : Vec4) : ℝ :=
  ∑ μ : Fin 4, p μ * x μ

/-- Plane wave `e^{i p·x} u`. -/
noncomputable def planeWave (p : Vec4) (u : DiracSpinor) (x : Vec4) : DiracSpinor :=
  Complex.exp (I * (wavePhase p x : ℂ)) • u

/-- `wavePhase p` as a continuous linear functional. -/
noncomputable def wavePhaseCLM (p : Vec4) : Vec4 →L[ℝ] ℝ :=
  ∑ μ : Fin 4, p μ • ContinuousLinearMap.proj μ

theorem wavePhaseCLM_apply (p x : Vec4) : wavePhaseCLM p x = wavePhase p x := by
  simp [wavePhaseCLM, wavePhase]

theorem wavePhase_zero (p : Vec4) : wavePhase p 0 = 0 := by
  simp [wavePhase]

theorem wavePhase_single (p : Vec4) (μ : Fin 4) : wavePhase p (Pi.single μ 1) = p μ := by
  unfold wavePhase
  rw [Finset.sum_eq_single μ]
  · simp
  · intro ν _ hν
    simp [Pi.single_eq_of_ne hν]
  · simp

theorem hasFDerivAt_planeWave (p : Vec4) (u : DiracSpinor) (x : Vec4) :
    HasFDerivAt (planeWave p u)
      ((Complex.exp (I * (wavePhase p x : ℂ)) •
        (I • (Complex.ofRealCLM.comp (wavePhaseCLM p)))).smulRight u) x := by
  have h1 : HasFDerivAt (fun y => ((wavePhaseCLM p y : ℝ) : ℂ))
      (Complex.ofRealCLM.comp (wavePhaseCLM p)) x :=
    (Complex.ofRealCLM.comp (wavePhaseCLM p)).hasFDerivAt
  have h2 := (h1.const_mul I).cexp
  have h3 := h2.smul_const u
  simp only [wavePhaseCLM_apply] at h3
  exact h3

theorem planeWave_partialD (p : Vec4) (u : DiracSpinor) (μ : Fin 4) (x : Vec4) :
    partialD (planeWave p u) μ x = (I * (p μ : ℂ)) • planeWave p u x := by
  unfold partialD
  rw [(hasFDerivAt_planeWave p u x).fderiv]
  simp only [ContinuousLinearMap.smulRight_apply, _root_.smul_apply,
    ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, wavePhaseCLM_apply,
    wavePhase_single, smul_eq_mul]
  unfold planeWave
  rw [smul_smul]
  ring_nf

theorem differentiable_planeWave (p : Vec4) (u : DiracSpinor) :
    Differentiable ℝ (planeWave p u) :=
  fun x => (hasFDerivAt_planeWave p u x).differentiableAt

private theorem applyDiracMat_sum4 (M : Matrix (Fin 4) (Fin 4) ℂ) (f : Fin 4 → DiracSpinor) :
    applyDiracMat M (∑ μ : Fin 4, f μ) = ∑ μ : Fin 4, applyDiracMat M (f μ) := by
  simp only [Fin.sum_univ_four, applyDiracMat_add]

theorem planeWave_diracOp (p : Vec4) (u : DiracSpinor) (x : Vec4) :
    diracOp (planeWave p u) x =
      (I * Complex.exp (I * (wavePhase p x : ℂ))) • applyDiracMat (slashMat p) u := by
  unfold diracOp slashMat
  simp only [planeWave_partialD]
  unfold planeWave
  simp only [smul_smul, applyDiracMat_smul, Fin.sum_univ_four, applyDiracMat_add_mat,
    applyDiracMat_smul_mat, smul_add]
  module

/-- A plane wave solves the spacetime equation exactly when its amplitude
solves the momentum-space equation. -/
theorem diracField_planeWave_iff (m : ℝ) (p : Vec4) (u : DiracSpinor) :
    DiracField m (planeWave p u) ↔ DiracMomentum m p u := by
  constructor
  · rintro ⟨-, h⟩
    have h0 := h 0
    rw [planeWave_diracOp] at h0
    unfold planeWave at h0
    rw [wavePhase_zero, ofReal_zero, mul_zero, Complex.exp_zero, mul_one, one_smul] at h0
    unfold DiracMomentum
    have := congrArg (fun v => (-I) • v) h0
    simp only [smul_smul] at this
    rw [show -I * I = (1 : ℂ) by rw [neg_mul, I_mul_I, neg_neg], one_smul] at this
    rw [this]
    congr 1
    ring
  · intro h
    refine ⟨differentiable_planeWave p u, fun x => ?_⟩
    rw [planeWave_diracOp, h]
    unfold planeWave
    rw [smul_smul, smul_smul]
    congr 1
    rw [show I * Complex.exp (I * (wavePhase p x : ℂ)) * (I * (m : ℂ)) =
      (I * I) * (m : ℂ) * Complex.exp (I * (wavePhase p x : ℂ)) by ring, I_mul_I]
    ring

theorem diracOp_add {Ψ Φ : Vec4 → DiracSpinor} (hΨ : Differentiable ℝ Ψ)
    (hΦ : Differentiable ℝ Φ) (x : Vec4) :
    diracOp (Ψ + Φ) x = diracOp Ψ x + diracOp Φ x := by
  unfold diracOp partialD
  rw [fderiv_add (hΨ x) (hΦ x)]
  simp only [_root_.add_apply, applyDiracMat_add, Finset.sum_add_distrib]

theorem diracOp_smul {Ψ : Vec4 → DiracSpinor} (hΨ : Differentiable ℝ Ψ) (c : ℂ) (x : Vec4) :
    diracOp (c • Ψ) x = c • diracOp Ψ x := by
  unfold diracOp partialD
  rw [fderiv_const_smul (hΨ x) c]
  simp only [_root_.smul_apply, applyDiracMat_smul, Finset.smul_sum]

/-- Solutions of one mass add. -/
theorem DiracField.add {m : ℝ} {Ψ Φ : Vec4 → DiracSpinor} (hΨ : DiracField m Ψ)
    (hΦ : DiracField m Φ) : DiracField m (Ψ + Φ) := by
  refine ⟨hΨ.1.add hΦ.1, fun x => ?_⟩
  rw [diracOp_add hΨ.1 hΦ.1, hΨ.2, hΦ.2, Pi.add_apply, smul_add]

/-- Solutions of one mass are closed under complex scaling. -/
theorem DiracField.smul {m : ℝ} {Ψ : Vec4 → DiracSpinor} (hΨ : DiracField m Ψ) (c : ℂ) :
    DiracField m (c • Ψ) := by
  refine ⟨hΨ.1.const_smul c, fun x => ?_⟩
  rw [diracOp_smul hΨ.1, hΨ.2, Pi.smul_apply, smul_comm]

/-! ### Conservation of the current -/

/-- `applyDiracMat M` as a real continuous linear map. -/
noncomputable def diracCLM (M : Matrix (Fin 4) (Fin 4) ℂ) : DiracSpinor →L[ℝ] DiracSpinor :=
  LinearMap.toContinuousLinearMap
    { toFun := applyDiracMat M
      map_add' := applyDiracMat_add M
      map_smul' := fun r Ψ => by
        simp only [RingHom.id_apply]
        rw [← Complex.coe_smul, applyDiracMat_smul, Complex.coe_smul] }

theorem diracCLM_apply (M : Matrix (Fin 4) (Fin 4) ℂ) (Ψ : DiracSpinor) :
    diracCLM M Ψ = applyDiracMat M Ψ := rfl

/-- Current field `j^μ(x) = Ψ̄(x) γ^μ Φ(x)`. -/
noncomputable def currentField (Ψ Φ : Vec4 → DiracSpinor) (μ : Fin 4) (x : Vec4) : ℂ :=
  diracCurrent μ (Ψ x) (Φ x)

theorem currentField_partial {Ψ Φ : Vec4 → DiracSpinor} (hΨ : Differentiable ℝ Ψ)
    (hΦ : Differentiable ℝ Φ) (μ : Fin 4) (x : Vec4) :
    fderiv ℝ (currentField Ψ Φ μ) x (Pi.single μ 1) =
      inner ℂ (Ψ x) (applyDiracMat (diracAdjointMat * diracMat μ) (partialD Φ μ x)) +
        inner ℂ (partialD Ψ μ x) (applyDiracMat (diracAdjointMat * diracMat μ) (Φ x)) := by
  have hg : HasFDerivAt (fun y => diracCLM (diracAdjointMat * diracMat μ) (Φ y))
      ((diracCLM (diracAdjointMat * diracMat μ)).comp (fderiv ℝ Φ x)) x :=
    (diracCLM _).hasFDerivAt.comp x (hΦ x).hasFDerivAt
  have hcf : currentField Ψ Φ μ =
      fun y => inner ℂ (Ψ y) (diracCLM (diracAdjointMat * diracMat μ) (Φ y)) := rfl
  rw [hcf, fderiv_inner_apply ℂ (hΨ x) hg.differentiableAt, hg.fderiv]
  rfl

/-- The current between two plane waves of one momentum is uniform. -/
theorem currentField_planeWave (p : Vec4) (u v : DiracSpinor) (μ : Fin 4) (x : Vec4) :
    currentField (planeWave p u) (planeWave p v) μ x = diracCurrent μ u v := by
  unfold currentField planeWave diracCurrent
  rw [applyDiracMat_smul, inner_smul_left, inner_smul_right, ← mul_assoc]
  have h : (starRingEnd ℂ) (Complex.exp (I * (wavePhase p x : ℂ))) *
      Complex.exp (I * (wavePhase p x : ℂ)) = 1 := by
    rw [← Complex.exp_conj, ← Complex.exp_add]
    simp [Complex.conj_ofReal]
  rw [h, one_mul]

/-- Continuity equation: for two differentiable solutions of the same real
mass the current is conserved, `∂_μ j^μ = 0`. -/
theorem currentField_conserved {m : ℝ} {Ψ Φ : Vec4 → DiracSpinor} (hΨ : DiracField m Ψ)
    (hΦ : DiracField m Φ) (x : Vec4) :
    ∑ μ : Fin 4, fderiv ℝ (currentField Ψ Φ μ) x (Pi.single μ 1) = 0 := by
  simp only [currentField_partial hΨ.1 hΦ.1]
  rw [Finset.sum_add_distrib]
  have hA : ∀ μ : Fin 4, inner ℂ (Ψ x)
      (applyDiracMat (diracAdjointMat * diracMat μ) (partialD Φ μ x)) =
      inner ℂ (Ψ x) (applyDiracMat diracAdjointMat
        (applyDiracMat (diracMat μ) (partialD Φ μ x))) := fun μ => by
    rw [applyDiracMat_mul]
  have hB : ∀ μ : Fin 4, inner ℂ (partialD Ψ μ x)
      (applyDiracMat (diracAdjointMat * diracMat μ) (Φ x)) =
      -inner ℂ (applyDiracMat diracAdjointMat
        (applyDiracMat (diracMat μ) (partialD Ψ μ x))) (Φ x) := fun μ => by
    rw [applyDiracMat_inner_ct, diracAdjointMat_mul_gamma_antiHermitian, applyDiracMat_neg,
      inner_neg_left, applyDiracMat_mul]
  simp only [hA, hB]
  have hΦx : ∑ μ : Fin 4, applyDiracMat (diracMat μ) (partialD Φ μ x) = (-(m : ℂ)) • Φ x :=
    hΦ.2 x
  have hΨx : ∑ μ : Fin 4, applyDiracMat (diracMat μ) (partialD Ψ μ x) = (-(m : ℂ)) • Ψ x :=
    hΨ.2 x
  rw [Finset.sum_neg_distrib, ← inner_sum, ← sum_inner, ← applyDiracMat_sum4,
    ← applyDiracMat_sum4, hΦx, hΨx, applyDiracMat_smul, applyDiracMat_smul,
    inner_smul_right, inner_smul_left]
  have hsym : inner ℂ (applyDiracMat diracAdjointMat (Ψ x)) (Φ x) =
      inner ℂ (Ψ x) (applyDiracMat diracAdjointMat (Φ x)) := by
    rw [applyDiracMat_inner_ct, diracAdjointMat_hermitian]
  rw [hsym]
  simp only [map_neg, Complex.conj_ofReal]
  ring

end Logic

end DstDiophantine
