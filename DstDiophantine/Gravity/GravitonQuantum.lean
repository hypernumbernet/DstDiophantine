import DstDiophantine.Algebra.SourceSuperposition
import DstDiophantine.Logic.Quantum.DeBroglie
import DstDiophantine.Logic.Quantum.DualObservables
import DstDiophantine.Logic.Quantum.LightFilter
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option linter.style.native false

/-!
# One dual step, and the mismatch a body expresses

A particle meets the mismatch one lattice step at a time. On one axis the
least nonzero step is a pure dual angle `2π/N`. For `N ≥ 4` it lies in the
admissible cone, and its normalized height is exactly the floor
`-ε_N = -16/(3N²)`.

`n` aligned copies add in the rapidity. While `4n ≤ N` they stay in the
cone and the height they express is `n²` times one step. Once `4n ≥ N` the
nearest admissible point on that axis is the pure dual corner: the expressed
height locks at `-1/3`, and any further step remains in the internal sum.

The same step is a dual rotation. About an axis transverse to a
computational eigenstate it replaces the Born weight `1` by `cos²(π/N)`,
which for `N ≥ 5` lies strictly between `1/2` and `1`. About the eigenaxis
it multiplies the eigenstate by a phase, leaves the weight equal to `1`,
and is not `±I`.

## Not claimed

* A derivation of `G`, of `α_G`, or of a laboratory error rate. The integer
  `N` is not fixed. `NuclearLayer.alphaG_bounds` is a separate window, and
  it is not this Born weight.
* That every device error is one step, or that a meson mass equals `ε_N`.
  The exchange of one step is the step itself.
* A Newtonian multi-body law. The expressed point is the admissible foot
  already constructed in `SourceSuperposition`.
-/

noncomputable section

namespace DstDiophantine.Gravity.GravitonQuantum

open Admissible Invariant Operations Real SourceSuperposition
open DstDiophantine.Logic

/-- Pure dual rapidity `θ` on axis 0. -/
def oneAxisDual (θ : ℝ) : TorsionParams where
  alpha := fun
    | 0 => 0
    | 1 => 0
    | 2 => 0
  beta := fun
    | 0 => θ
    | 1 => 0
    | 2 => 0

@[simp] theorem oneAxisDual_alpha (θ : ℝ) (a : Fin 3) : (oneAxisDual θ).alpha a = 0 := by
  fin_cases a <;> rfl

@[simp] theorem oneAxisDual_beta_0 (θ : ℝ) : (oneAxisDual θ).beta 0 = θ := rfl

@[simp] theorem oneAxisDual_beta_1 (θ : ℝ) : (oneAxisDual θ).beta 1 = 0 := rfl

@[simp] theorem oneAxisDual_beta_2 (θ : ℝ) : (oneAxisDual θ).beta 2 = 0 := rfl

theorem J_oneAxisDual (θ : ℝ) : J (oneAxisDual θ) = -(θ ^ 2) / 2 := by
  rw [J_coef]
  simp [oneAxisDual, Fin.sum_univ_three]
  ring

theorem JNormalized_oneAxisDual (θ : ℝ) :
    JNormalized (oneAxisDual θ) = -((4 : ℝ) / (3 * Real.pi ^ 2)) * θ ^ 2 := by
  unfold JNormalized
  rw [J_oneAxisDual]
  ring

/-- One lattice spacing `2π/N`. -/
def stepAngle (N : ℕ) : ℝ := 2 * Real.pi / N

theorem stepAngle_nonneg (N : ℕ) : 0 ≤ stepAngle N := by
  unfold stepAngle
  exact div_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) (Nat.cast_nonneg _)

theorem stepAngle_pos {N : ℕ} (hN : 0 < N) : 0 < stepAngle N := by
  unfold stepAngle
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  exact div_pos (mul_pos (by norm_num) Real.pi_pos) hN0

theorem JNormalized_oneStep {N : ℕ} (hN : 0 < N) :
    JNormalized (oneAxisDual (stepAngle N)) = -((16 : ℝ) / (3 * (N : ℝ) ^ 2)) := by
  rw [JNormalized_oneAxisDual, stepAngle]
  have hNz : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hN)
  field_simp [hNz]
  ring

theorem oneAxisDual_admissible {θ : ℝ} (h0 : 0 ≤ θ) (hθ : θ ≤ Real.pi / 2) :
    IsAdmissibleContinuous (oneAxisDual θ) := by
  intro a
  match a with
  | 0 =>
    rw [oneAxisDual_alpha, oneAxisDual_beta_0]
    simp only [le_rfl, zero_add, true_and]
    exact ⟨h0, hθ⟩
  | 1 =>
    rw [oneAxisDual_alpha, oneAxisDual_beta_1]
    simp only [le_rfl, add_zero, true_and]
    exact div_nonneg Real.pi_pos.le (by norm_num)
  | 2 =>
    rw [oneAxisDual_alpha, oneAxisDual_beta_2]
    simp only [le_rfl, add_zero, true_and]
    exact div_nonneg Real.pi_pos.le (by norm_num)

theorem stepAngle_le_half_pi {N : ℕ} (hN : 4 ≤ N) : stepAngle N ≤ Real.pi / 2 := by
  unfold stepAngle
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 4) hN)
  rw [div_le_div_iff₀ hN0 (by positivity : (0 : ℝ) < 2)]
  have h4 : (4 : ℝ) ≤ N := by exact_mod_cast hN
  nlinarith [Real.pi_pos]

theorem oneStep_admissible {N : ℕ} (hN : 4 ≤ N) :
    IsAdmissibleContinuous (oneAxisDual (stepAngle N)) :=
  oneAxisDual_admissible (stepAngle_pos (lt_of_lt_of_le (by decide : 0 < 4) hN)).le
    (stepAngle_le_half_pi hN)

/-- `n` aligned dual steps on axis 0. -/
def alignedSteps (n N : ℕ) : TorsionParams :=
  oneAxisDual ((n : ℝ) * stepAngle N)

theorem alignedAngle_le_half_pi {n N : ℕ} (h : 4 * n ≤ N) :
    (n : ℝ) * stepAngle N ≤ Real.pi / 2 := by
  unfold stepAngle
  cases n with
  | zero =>
    simp only [CharP.cast_eq_zero, zero_mul]
    exact div_nonneg Real.pi_pos.le (by norm_num)
  | succ n =>
    have hN : 0 < N := by
      have hpos : 0 < 4 * (n + 1) := by positivity
      exact lt_of_lt_of_le hpos h
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    have hmul : ((n + 1 : ℕ) : ℝ) * (2 * Real.pi / N) =
        ((n + 1 : ℕ) : ℝ) * 2 * Real.pi / N := by ring
    rw [hmul, div_le_iff₀ hN0]
    have h4 : (4 * ((n + 1 : ℕ) : ℝ)) * Real.pi ≤ (N : ℝ) * Real.pi :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast h) Real.pi_pos.le
    have htwice : ((n + 1 : ℕ) : ℝ) * 2 * Real.pi * 2 ≤ Real.pi / 2 * N * 2 := by
      calc
        ((n + 1 : ℕ) : ℝ) * 2 * Real.pi * 2 = (4 * ((n + 1 : ℕ) : ℝ)) * Real.pi := by ring
        _ ≤ (N : ℝ) * Real.pi := h4
        _ = Real.pi / 2 * N * 2 := by ring
    exact (mul_le_mul_iff_of_pos_right (by norm_num : (0 : ℝ) < 2)).mp htwice

theorem alignedAngle_ge_half_pi {n N : ℕ} (hN : 0 < N) (h : N ≤ 4 * n) :
    Real.pi / 2 ≤ (n : ℝ) * stepAngle N := by
  unfold stepAngle
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hmul : (n : ℝ) * (2 * Real.pi / N) = (n : ℝ) * 2 * Real.pi / N := by ring
  rw [hmul, le_div_iff₀ hN0]
  have h4 : (N : ℝ) * Real.pi ≤ (4 * (n : ℝ)) * Real.pi :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast h) Real.pi_pos.le
  have htwice : Real.pi / 2 * N * 2 ≤ (n : ℝ) * 2 * Real.pi * 2 := by
    calc
      Real.pi / 2 * N * 2 = (N : ℝ) * Real.pi := by ring
      _ ≤ (4 * (n : ℝ)) * Real.pi := h4
      _ = (n : ℝ) * 2 * Real.pi * 2 := by ring
  exact (mul_le_mul_iff_of_pos_right (by norm_num : (0 : ℝ) < 2)).mp htwice

theorem collective_admissible {n N : ℕ} (h : 4 * n ≤ N) :
    IsAdmissibleContinuous (alignedSteps n N) :=
  oneAxisDual_admissible
    (mul_nonneg (Nat.cast_nonneg _) (stepAngle_nonneg N))
    (alignedAngle_le_half_pi h)

theorem collective_square {n N : ℕ} (hN : 0 < N) :
    JNormalized (alignedSteps n N) =
      (n : ℝ) ^ 2 * JNormalized (oneAxisDual (stepAngle N)) := by
  rw [alignedSteps, JNormalized_oneAxisDual, JNormalized_oneStep hN, stepAngle]
  have hNz : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hN)
  field_simp [hNz]
  ring

/-- The admissible foot of a pure dual rapidity on axis 0. -/
def expressedOneAxis (θ : ℝ) : TorsionParams where
  alpha := fun
    | 0 => (axisExpress 0 θ).1
    | 1 => 0
    | 2 => 0
  beta := fun
    | 0 => (axisExpress 0 θ).2
    | 1 => 0
    | 2 => 0

theorem expressed_corner {θ : ℝ} (h : Real.pi / 2 ≤ θ) :
    axisExpress 0 θ = (0, Real.pi / 2) :=
  axisExpress_pureDual ⟨h, by linarith⟩

theorem J_expressed_corner {θ : ℝ} (h : Real.pi / 2 ≤ θ) :
    J (expressedOneAxis θ) = -(Real.pi ^ 2) / 8 := by
  have hax := expressed_corner h
  rw [J_coef]
  simp [expressedOneAxis, hax, Fin.sum_univ_three]
  ring

theorem expressed_locks {θ : ℝ} (h : Real.pi / 2 ≤ θ) :
    JNormalized (expressedOneAxis θ) = -((1 : ℝ) / 3) := by
  have hJ := J_expressed_corner h
  unfold JNormalized
  rw [hJ]
  field_simp

theorem collective_locks {n N : ℕ} (hN : 0 < N) (h : N ≤ 4 * n) :
    JNormalized (expressedOneAxis ((n : ℝ) * stepAngle N)) = -((1 : ℝ) / 3) :=
  expressed_locks (alignedAngle_ge_half_pi hN h)

theorem internal_exceeds_lock {θ : ℝ} (h : Real.pi / 2 < θ) :
    J (oneAxisDual θ) < J (expressedOneAxis θ) := by
  rw [J_oneAxisDual, J_expressed_corner h.le]
  have hdiff : θ ^ 2 - (Real.pi / 2) ^ 2 = (θ - Real.pi / 2) * (θ + Real.pi / 2) := by ring
  nlinarith [hdiff, h, Real.pi_pos]

theorem oneStep_below_corner {N : ℕ} (hN : 5 ≤ N) :
    -((1 : ℝ) / 3) < JNormalized (oneAxisDual (stepAngle N)) ∧
      JNormalized (oneAxisDual (stepAngle N)) < 0 := by
  have hpos : 0 < N := lt_of_lt_of_le (by decide : 0 < 5) hN
  rw [JNormalized_oneStep hpos]
  have hden : (0 : ℝ) < 3 * (N : ℝ) ^ 2 := by positivity
  refine ⟨?_, ?_⟩
  · rw [neg_lt_neg_iff, div_lt_div_iff₀ hden (by norm_num : (0 : ℝ) < 3)]
    have hsq : (25 : ℝ) ≤ (N : ℝ) ^ 2 := by
      exact_mod_cast Nat.pow_le_pow_left hN 2
    nlinarith
  · exact neg_lt_zero.mpr (div_pos (by norm_num) hden)

/-! ### The step as a dual rotation -/

theorem spinUp_zero : spinUp 0 = 1 := by
  simp [spinUp]

theorem spinUp_one : spinUp 1 = 0 := by
  simp [spinUp]

theorem spinVec_spinUp :
    spinVec spinUp 0 = 0 ∧ spinVec spinUp 1 = 0 ∧ spinVec spinUp 2 = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [spinVec_coord_zero]
    simp [spinUp_zero, spinUp_one]
  · rw [spinVec_coord_one]
    simp [spinUp_zero, spinUp_one]
  · rw [spinVec_coord_two]
    simp [spinUp_zero, spinUp_one, norm_one, norm_zero]

theorem spinUp_norm_sq : ‖spinUp‖ ^ 2 = 1 := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
  simp [spinUp_zero, spinUp_one, norm_one, norm_zero]

theorem spinUp_norm : ‖spinUp‖ = 1 := by
  have hsq := spinUp_norm_sq
  nlinarith [norm_nonneg spinUp]

/-- Born weight of the outcome `+1` along the computational axis. -/
def computationalWeight (u : DualSpinor) : ℝ :=
  (‖u‖ ^ 2 + spinVec u 2) / 2

theorem computationalWeight_spinUp : computationalWeight spinUp = 1 := by
  unfold computationalWeight
  rw [spinUp_norm_sq, spinVec_spinUp.2.2]
  norm_num

private theorem norm_single_axis0 {θ : ℝ} (hθ : 0 < θ) :
    ‖(EuclideanSpace.single (0 : Fin 3) θ : DualRapidity)‖ = θ := by
  have hsq : ‖(EuclideanSpace.single (0 : Fin 3) θ : DualRapidity)‖ ^ 2 = θ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]
    simp
  have hdiff : (‖(EuclideanSpace.single (0 : Fin 3) θ : DualRapidity)‖ - θ) *
      (‖(EuclideanSpace.single (0 : Fin 3) θ : DualRapidity)‖ + θ) = 0 := by
    nlinarith
  rcases mul_eq_zero.mp hdiff with h | h
  · linarith
  · linarith [norm_nonneg (EuclideanSpace.single (0 : Fin 3) θ : DualRapidity), hθ]

private theorem single_axis0_ne {θ : ℝ} (hθ : θ ≠ 0) :
    (EuclideanSpace.single (0 : Fin 3) θ : DualRapidity) ≠ 0 := by
  intro h
  have h0 : (EuclideanSpace.single (0 : Fin 3) θ : DualRapidity) 0 = θ := by
    simp
  rw [h] at h0
  simp at h0
  exact hθ h0.symm

theorem spinVec_transverse {θ : ℝ} (hθ : 0 < θ) :
    spinVec (applyMat (dualRotorMat (EuclideanSpace.single 0 θ)) spinUp) 2 = Real.cos θ := by
  set β : DualRapidity := EuclideanSpace.single 0 θ
  have hβ : β ≠ 0 := single_axis0_ne (ne_of_gt hθ)
  have hnorm : ‖β‖ = θ := norm_single_axis0 hθ
  rw [spinVec_dualRotor hβ]
  have hspin := spinVec_spinUp
  have hb2 : β 2 = 0 := by simp [β]
  simp only [axisRot, axisDot, cross3, hnorm, hspin, hb2]
  ring

theorem computationalWeight_transverse {θ : ℝ} (hθ : 0 < θ) :
    computationalWeight (applyMat (dualRotorMat (EuclideanSpace.single 0 θ)) spinUp) =
      (1 + Real.cos θ) / 2 := by
  have hsq := norm_applyMat_dualRotor_sq (EuclideanSpace.single 0 θ) spinUp
  rw [spinUp_norm_sq] at hsq
  unfold computationalWeight
  rw [hsq, spinVec_transverse hθ]

theorem computationalWeight_eq_cos_sq {θ : ℝ} (hθ : 0 < θ) :
    computationalWeight (applyMat (dualRotorMat (EuclideanSpace.single 0 θ)) spinUp) =
      Real.cos (θ / 2) ^ 2 := by
  rw [computationalWeight_transverse hθ]
  have h := Real.cos_two_mul (θ / 2)
  have htwice : 2 * (θ / 2) = θ := by ring
  rw [htwice] at h
  linarith

theorem transverseStep_weight {N : ℕ} (hN : 5 ≤ N) :
    1 / 2 < computationalWeight
        (applyMat (dualRotorMat (EuclideanSpace.single 0 (stepAngle N))) spinUp) ∧
      computationalWeight
        (applyMat (dualRotorMat (EuclideanSpace.single 0 (stepAngle N))) spinUp) < 1 := by
  have hpos : 0 < N := lt_of_lt_of_le (by decide : 0 < 5) hN
  have hθ : 0 < stepAngle N := stepAngle_pos hpos
  have hhalf : stepAngle N < Real.pi / 2 := by
    unfold stepAngle
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hpos
    rw [div_lt_div_iff₀ hN0 (by positivity : (0 : ℝ) < 2)]
    have h5 : (5 : ℝ) ≤ N := by exact_mod_cast hN
    nlinarith [Real.pi_pos]
  rw [computationalWeight_transverse hθ]
  refine ⟨?_, ?_⟩
  · have hcos : 0 < Real.cos (stepAngle N) :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith, hhalf⟩
    linarith
  · have hlt : Real.cos (stepAngle N) < Real.cos 0 :=
      Real.cos_lt_cos_of_nonneg_of_le_pi (le_refl 0)
        (le_of_lt (lt_trans hhalf (by linarith [Real.pi_pos]))) hθ
    rw [Real.cos_zero] at hlt
    linarith

theorem transverseStep_leaves_ray {θ : ℝ} (hθ : 0 < θ) (hθπ : θ < Real.pi) :
    ¬ ∃ c : ℂ,
        applyMat (dualRotorMat (EuclideanSpace.single 0 θ)) spinUp = c • spinUp := by
  intro ⟨c, hc⟩
  have hsq := norm_applyMat_dualRotor_sq (EuclideanSpace.single 0 θ) spinUp
  rw [spinUp_norm_sq] at hsq
  have hw := computationalWeight_transverse hθ
  have hcos : Real.cos θ < 1 := by
    have hlt : Real.cos θ < Real.cos 0 :=
      Real.cos_lt_cos_of_nonneg_of_le_pi (le_refl 0) hθπ.le hθ
    simpa [Real.cos_zero] using hlt
  have hweight : computationalWeight
      (applyMat (dualRotorMat (EuclideanSpace.single 0 θ)) spinUp) < 1 := by
    rw [hw]
    linarith
  have hphase : computationalWeight (c • spinUp) = ‖c‖ ^ 2 := by
    unfold computationalWeight
    rw [norm_smul, spinVec_smul, spinUp_norm]
    dsimp
    rw [spinVec_spinUp.2.2]
    ring
  rw [← hc] at hphase
  have hc1 : ‖c‖ ^ 2 = 1 := by
    have hnorm : ‖c • spinUp‖ ^ 2 = 1 := by simpa [hc] using hsq
    rw [norm_smul, spinUp_norm] at hnorm
    nlinarith [norm_nonneg c]
  linarith

private def axialPhase (θ : ℝ) : ℂ :=
  (Real.cos (θ / 2) : ℂ) - Complex.I * (Real.sin (θ / 2) : ℂ)

private theorem axialPhase_norm_sq (θ : ℝ) : ‖axialPhase θ‖ ^ 2 = 1 := by
  have hre : (axialPhase θ).re = Real.cos (θ / 2) := by
    unfold axialPhase
    simp only [Complex.sub_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, zero_mul, sub_zero]
  have him : (axialPhase θ).im = -Real.sin (θ / 2) := by
    unfold axialPhase
    simp only [Complex.sub_im, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero]
    ring
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, hre, him]
  have hcs := Real.cos_sq_add_sin_sq (θ / 2)
  ring_nf at hcs ⊢
  exact hcs

theorem axial_on_ray (θ : ℝ) :
    applyMat (dualRotorMat (EuclideanSpace.single 2 θ)) spinUp = axialPhase θ • spinUp := by
  ext i
  fin_cases i
  · simp [PiLp.smul_apply, spinUp_zero, applyMat_apply, Fin.sum_univ_two, spinUp_one,
      dualRotorMat_axis2_rodrigues, cyclicRep_two_eq, Matrix.add_apply, Matrix.smul_apply,
      axialPhase]
    ring
  · simp [PiLp.smul_apply, spinUp_one, applyMat_apply, Fin.sum_univ_two, spinUp_zero,
      dualRotorMat_axis2_rodrigues, cyclicRep_two_eq, Matrix.add_apply, Matrix.smul_apply,
      axialPhase]

theorem axialStep_weight (θ : ℝ) :
    computationalWeight
      (applyMat (dualRotorMat (EuclideanSpace.single 2 θ)) spinUp) = 1 := by
  rw [axial_on_ray]
  unfold computationalWeight
  rw [norm_smul, spinVec_smul, spinUp_norm]
  simp [axialPhase_norm_sq, spinVec_spinUp.2.2]

theorem axialStep_not_sign {θ : ℝ} (hθ : 0 < θ) (hθπ : θ < 2 * Real.pi) :
    dualRotorMat (EuclideanSpace.single 2 θ) ≠ 1 ∧
      dualRotorMat (EuclideanSpace.single 2 θ) ≠ -1 := by
  have hamp := dualRotorAmplitude_axis2 θ
  have hre : (Complex.exp (-(θ / 2 : ℂ) * Complex.I)).re = Real.cos (θ / 2) := by
    rw [Complex.exp_mul_I]
    simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, mul_zero, mul_one,
      Complex.cos_neg, Complex.sin_neg]
    have hdiv : (θ : ℂ) / 2 = ↑(θ / 2) := by simp [Complex.ofReal_div]
    have him0 : (-Complex.sin ↑(θ / 2)).im = 0 := by
      rw [Complex.neg_im, Complex.sin_ofReal_im]
      simp
    rw [hdiv, Complex.cos_ofReal_re, him0]
    ring
  have hcos_lt : Real.cos (θ / 2) < 1 := by
    have hlt : Real.cos (θ / 2) < Real.cos 0 :=
      Real.cos_lt_cos_of_nonneg_of_le_pi (le_refl 0) (by linarith) (by linarith)
    simpa [Real.cos_zero] using hlt
  have hcos_gt : -1 < Real.cos (θ / 2) := by
    have hpi : θ / 2 < Real.pi := by linarith
    have hcomp := Real.cos_lt_cos_of_nonneg_of_le_pi (by linarith : 0 ≤ θ / 2) (le_refl Real.pi) hpi
    simpa [Real.cos_pi] using hcomp
  constructor
  · intro hR
    have h1 : dualRotorAmplitude (EuclideanSpace.single 2 θ) spinUp = 1 := by
      unfold dualRotorAmplitude
      rw [hR, applyMat_one, inner_self_eq_norm_sq_to_K, spinUp_norm]
      norm_num
    rw [hamp] at h1
    have : (1 : ℂ).re = (Complex.exp (-(θ / 2 : ℂ) * Complex.I)).re := by rw [h1]
    rw [hre] at this
    norm_num at this
    linarith
  · intro hR
    have hneg : dualRotorAmplitude (EuclideanSpace.single 2 θ) spinUp = -1 := by
      unfold dualRotorAmplitude
      rw [hR, applyMat_neg, applyMat_one, inner_neg_right, inner_self_eq_norm_sq_to_K,
        spinUp_norm]
      norm_num
    rw [hamp] at hneg
    have : (-1 : ℂ).re = (Complex.exp (-(θ / 2 : ℂ) * Complex.I)).re := by rw [hneg]
    rw [hre] at this
    norm_num at this
    linarith

theorem axialStep_not_sign_of_lattice {N : ℕ} (hN : 3 ≤ N) :
    dualRotorMat (EuclideanSpace.single 2 (stepAngle N)) ≠ 1 ∧
      dualRotorMat (EuclideanSpace.single 2 (stepAngle N)) ≠ -1 := by
  have hpos : 0 < N := lt_of_lt_of_le (by decide : 0 < 3) hN
  refine axialStep_not_sign (stepAngle_pos hpos) ?_
  unfold stepAngle
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hpos
  rw [div_lt_iff₀ hN0]
  have h3 : (3 : ℝ) ≤ N := by exact_mod_cast hN
  nlinarith [Real.pi_pos]

end DstDiophantine.Gravity.GravitonQuantum

end
