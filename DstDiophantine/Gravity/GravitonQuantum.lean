import DstDiophantine.Algebra.SourceSuperposition
import DstDiophantine.Gravity.TorsionalLayer
import DstDiophantine.Gravity.MismatchAngleBridge
import DstDiophantine.Logic.Quantum.DeBroglie
import DstDiophantine.Logic.Quantum.DualObservables
import DstDiophantine.Logic.Quantum.LightFilter
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option linter.style.native false

/-!
# One graviton

A graviton is one pure dual step of angle `2π/N`, with normalized height `-ε_N` for `N ≥ 4`. No
derivation of `G`, `α_G`, or a laboratory error rate is claimed, `N` is not fixed, and the
orthogonal probability is not the height `ε_N`.
-/

noncomputable section

namespace DstDiophantine.Gravity.GravitonQuantum

open Admissible Invariant Operations Real SourceSuperposition MismatchAngle
open DstDiophantine.Logic Gravity

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

theorem mismatchBoostHalfSqSum_oneAxisDual (θ : ℝ) :
    mismatchBoostHalfSqSum (oneAxisDual θ) = 0 := by
  simp [oneAxisDual, mismatchBoostHalfSqSum, mismatchBoostHalf, Fin.sum_univ_three]

theorem mismatchRotationHalfSqSum_oneAxisDual (θ : ℝ) :
    mismatchRotationHalfSqSum (oneAxisDual θ) = (θ / 2) ^ 2 := by
  simp [oneAxisDual, mismatchRotationHalfSqSum, mismatchRotationHalf, Fin.sum_univ_three]

theorem J_oneAxisDual_mismatch_halves (θ : ℝ) :
    J (oneAxisDual θ) =
      2 *
        (mismatchBoostHalfSqSum (oneAxisDual θ) -
          mismatchRotationHalfSqSum (oneAxisDual θ)) := by
  simpa using J_eq_mismatch_half_sq_diff (oneAxisDual θ)

theorem J_oneAxisDual_mismatch_rotation_half_sq (θ : ℝ) :
    J (oneAxisDual θ) = -2 * mismatchRotationHalfSqSum (oneAxisDual θ) := by
  rw [J_oneAxisDual_mismatch_halves, mismatchBoostHalfSqSum_oneAxisDual,
    mismatchRotationHalfSqSum_oneAxisDual]
  ring_nf

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

theorem oneAxisDual_admissible_legacy {θ : ℝ} (h0 : 0 ≤ θ) (hθ : θ ≤ Real.pi / 2) :
    IsAdmissibleContinuousLegacy (oneAxisDual θ) := by
  intro a
  fin_cases a <;> simp only [oneAxisDual]
  · exact ⟨le_rfl, h0, by simpa [add_zero] using hθ⟩
  · exact ⟨le_rfl, le_rfl, le_rfl⟩
  · exact ⟨le_rfl, le_rfl, le_rfl⟩

theorem oneAxisDual_admissible {θ : ℝ} (h0 : 0 ≤ θ) (hθ : θ ≤ Real.pi / 2) :
    IsAdmissibleContinuous (oneAxisDual θ) :=
  legacy_admissible_implies_mismatch _ (oneAxisDual_admissible_legacy h0 hθ)

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

/-- `n` gravitons aligned on axis 0: `n` times one dual step. -/
def alignedSteps (n N : ℕ) : TorsionParams :=
  oneAxisDual ((n : ℝ) * stepAngle N)

theorem alignedSteps_one (N : ℕ) :
    alignedSteps 1 N = oneAxisDual (stepAngle N) := by
  unfold alignedSteps
  rw [Nat.cast_one, one_mul]

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

theorem collective_admissible_legacy {n N : ℕ} (h : 4 * n ≤ N) :
    IsAdmissibleContinuousLegacy (alignedSteps n N) :=
  oneAxisDual_admissible_legacy
    (mul_nonneg (Nat.cast_nonneg _) (stepAngle_nonneg N))
    (alignedAngle_le_half_pi h)

theorem collective_admissible {n N : ℕ} (h : 4 * n ≤ N) :
    IsAdmissibleContinuous (alignedSteps n N) :=
  legacy_admissible_implies_mismatch _ (collective_admissible_legacy h)

theorem collective_square {n N : ℕ} (hN : 0 < N) :
    JNormalized (alignedSteps n N) =
      (n : ℝ) ^ 2 * JNormalized (oneAxisDual (stepAngle N)) := by
  rw [alignedSteps, JNormalized_oneAxisDual, JNormalized_oneStep hN, stepAngle]
  have hNz : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hN)
  field_simp [hNz]
  ring

theorem mismatchRotationHalfSqSum_alignedSteps {n N : ℕ} :
    mismatchRotationHalfSqSum (alignedSteps n N) =
      (n : ℝ) ^ 2 * mismatchRotationHalfSqSum (oneAxisDual (stepAngle N)) := by
  simp [alignedSteps, oneAxisDual, mismatchRotationHalfSqSum,
    mismatchRotationHalf, Fin.sum_univ_three]
  ring_nf

theorem oneStep_JNormalized_mismatch_rotation_sq {N : ℕ} (hN : 0 < N) :
    JNormalized (oneAxisDual (stepAngle N)) =
      -((16 : ℝ) / (3 * Real.pi ^ 2)) *
        mismatchRotationHalfSqSum (oneAxisDual (stepAngle N)) := by
  rw [JNormalized_oneStep hN, mismatchRotationHalfSqSum_oneAxisDual, stepAngle]
  have hNz : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hN)
  field_simp [hNz]

theorem collective_square_mismatch_halves {n N : ℕ} (hN : 0 < N) :
    JNormalized (alignedSteps n N) =
      -((16 : ℝ) / (3 * Real.pi ^ 2)) *
        mismatchRotationHalfSqSum (alignedSteps n N) := by
  rw [collective_square hN, oneStep_JNormalized_mismatch_rotation_sq hN,
    mismatchRotationHalfSqSum_alignedSteps]
  ring

theorem twoGravitons_fourfold {N : ℕ} (hN : 8 ≤ N) :
    IsAdmissibleContinuous (alignedSteps 2 N) ∧
      JNormalized (alignedSteps 2 N) = 4 * JNormalized (alignedSteps 1 N) := by
  have hpos : 0 < N := lt_of_lt_of_le (by decide : 0 < 8) hN
  have hadm : 4 * 2 ≤ N := by
    have : 4 * 2 = 8 := by norm_num
    simpa [this] using hN
  refine ⟨collective_admissible hadm, ?_⟩
  rw [collective_square (n := 2) hpos, collective_square (n := 1) hpos]
  norm_num

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

theorem expressed_locks_mismatch_diagnostic {θ : ℝ} (h : Real.pi / 2 ≤ θ) :
    J (expressedOneAxis θ) =
      2 *
        (mismatchBoostHalfSqSum (expressedOneAxis θ) -
          mismatchRotationHalfSqSum (expressedOneAxis θ)) ∧
      JNormalized (expressedOneAxis θ) = -((1 : ℝ) / 3) := by
  refine ⟨?_, expressed_locks h⟩
  simpa using J_eq_mismatch_half_sq_diff (expressedOneAxis θ)

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

theorem oneGraviton_above_lock {N : ℕ} (hN : 5 ≤ N) :
    -((1 : ℝ) / 3) < JNormalized (alignedSteps 1 N) := by
  rw [alignedSteps_one]
  exact (oneStep_below_corner hN).1

/-! ### The same step, read on a spinor -/

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

theorem stepAngle_half {N : ℕ} (hN : 0 < N) :
    stepAngle N / 2 = Real.pi / (N : ℝ) := by
  unfold stepAngle
  have hNz : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hN)
  field_simp [hNz]

theorem transverseStep_defect {N : ℕ} (hN : 0 < N) :
    1 - computationalWeight
        (applyMat (dualRotorMat (EuclideanSpace.single 0 (stepAngle N))) spinUp) =
      Real.sin (Real.pi / (N : ℝ)) ^ 2 := by
  rw [computationalWeight_eq_cos_sq (stepAngle_pos hN), stepAngle_half hN]
  have h := Real.cos_sq_add_sin_sq (Real.pi / (N : ℝ))
  linarith

theorem axialStep_defect (θ : ℝ) :
    1 - computationalWeight
        (applyMat (dualRotorMat (EuclideanSpace.single 2 θ)) spinUp) = 0 := by
  rw [axialStep_weight]
  norm_num

theorem defect_between_floor {N : ℕ} (hN : 3 ≤ N) :
    (3 / 4) * ((16 : ℝ) / (3 * (N : ℝ) ^ 2)) < Real.sin (Real.pi / (N : ℝ)) ^ 2 ∧
      Real.sin (Real.pi / (N : ℝ)) ^ 2 <
        (3 * Real.pi ^ 2 / 16) * ((16 : ℝ) / (3 * (N : ℝ) ^ 2)) := by
  have hpos : 0 < N := lt_of_lt_of_le (by decide : 0 < 3) hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hpos
  set x : ℝ := Real.pi / (N : ℝ)
  have hx : 0 < x := div_pos Real.pi_pos hN0
  have hxhalf : x < Real.pi / 2 := by
    unfold x
    rw [div_lt_div_iff₀ hN0 (by positivity : (0 : ℝ) < 2)]
    have h3 : (3 : ℝ) ≤ N := by exact_mod_cast hN
    nlinarith [Real.pi_pos]
  have hlow : (2 : ℝ) / N < Real.sin x := by
    have hmul := Real.mul_lt_sin hx hxhalf
    have hcoeff : 2 / Real.pi * x = 2 / (N : ℝ) := by
      unfold x
      field_simp
    simpa [hcoeff] using hmul
  have hhigh : Real.sin x < x := Real.sin_lt hx
  have hsin : 0 < Real.sin x :=
    Real.sin_pos_of_pos_of_lt_pi hx (by linarith [hxhalf, Real.pi_pos])
  have hsqLow : (2 / (N : ℝ)) ^ 2 < Real.sin x ^ 2 :=
    (sq_lt_sq₀ (div_nonneg (by norm_num : (0 : ℝ) ≤ 2) hN0.le) hsin.le).mpr hlow
  have hsqHigh : Real.sin x ^ 2 < x ^ 2 :=
    (sq_lt_sq₀ hsin.le hx.le).mpr hhigh
  have hfloor : (3 / 4) * ((16 : ℝ) / (3 * (N : ℝ) ^ 2)) = (2 / (N : ℝ)) ^ 2 := by
    field_simp
    ring
  have hceil : (3 * Real.pi ^ 2 / 16) * ((16 : ℝ) / (3 * (N : ℝ) ^ 2)) = x ^ 2 := by
    unfold x
    field_simp
  exact ⟨by simpa [hfloor] using hsqLow, by simpa [hceil] using hsqHigh⟩

theorem transverseDefect_vs_floor {N : ℕ} (hN : 5 ≤ N) :
    (3 / 4 : ℝ) * (-JNormalized (oneAxisDual (stepAngle N))) <
        1 - computationalWeight
          (applyMat (dualRotorMat (EuclideanSpace.single 0 (stepAngle N))) spinUp) ∧
      1 - computationalWeight
          (applyMat (dualRotorMat (EuclideanSpace.single 0 (stepAngle N))) spinUp) <
        (3 * Real.pi ^ 2 / 16) * (-JNormalized (oneAxisDual (stepAngle N))) ∧
      1 - computationalWeight
          (applyMat (dualRotorMat (EuclideanSpace.single 0 (stepAngle N))) spinUp) <
        1 / 2 := by
  have hpos : 0 < N := lt_of_lt_of_le (by decide : 0 < 5) hN
  have hdef := transverseStep_defect hpos
  have hJ := JNormalized_oneStep hpos
  have hfloor := defect_between_floor (le_trans (by decide : 3 ≤ 5) hN)
  have hweight := transverseStep_weight hN
  have hneg : -JNormalized (oneAxisDual (stepAngle N)) =
      (16 : ℝ) / (3 * (N : ℝ) ^ 2) := by
    rw [hJ]
    ring
  refine ⟨?_, ?_, ?_⟩
  · rw [hdef, hneg]
    exact hfloor.1
  · rw [hdef, hneg]
    exact hfloor.2
  · linarith [hweight.1]

theorem defect_gt_floor {N : ℕ} (hN : 3 ≤ N) :
    (16 : ℝ) / (3 * (N : ℝ) ^ 2) < Real.sin (Real.pi / (N : ℝ)) ^ 2 := by
  have hpos : 0 < N := lt_of_lt_of_le (by decide : 0 < 3) hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hpos
  set x : ℝ := Real.pi / (N : ℝ)
  have hx : 0 < x := div_pos Real.pi_pos hN0
  have hxle : x ≤ Real.pi / 3 := by
    unfold x
    rw [div_le_div_iff₀ hN0 (by positivity : (0 : ℝ) < 3)]
    have h3 : (3 : ℝ) ≤ N := by exact_mod_cast hN
    nlinarith [Real.pi_pos]
  have hcubic : x - x ^ 3 / 6 < Real.sin x := sin_gt_sub_cube hx
  have hπlo : (3.14 : ℝ) < Real.pi := pi_gt_d2
  have hπhi : Real.pi < 3.15 := pi_lt_d2
  have hfacWall : (0 : ℝ) < 1 - ((3.15 : ℝ) / 3) ^ 2 / 6 := by norm_num
  have hfacPi : (0 : ℝ) < 1 - (Real.pi / 3) ^ 2 / 6 := by
    have hlt : (Real.pi / 3) ^ 2 < ((3.15 : ℝ) / 3) ^ 2 := by
      have hdiv : Real.pi / 3 < (3.15 : ℝ) / 3 := by
        rw [div_lt_div_iff₀ (by norm_num) (by norm_num)]
        nlinarith [hπhi]
      exact pow_lt_pow_left₀ hdiv (div_nonneg Real.pi_nonneg (by norm_num))
        (by decide : (2 : ℕ) ≠ 0)
    have hsub : (Real.pi / 3) ^ 2 / 6 < ((3.15 : ℝ) / 3) ^ 2 / 6 := by
      rw [div_lt_div_iff₀ (by norm_num) (by norm_num)]
      nlinarith [hlt]
    linarith [hfacWall, hsub]
  have hxsq : x ^ 2 ≤ (Real.pi / 3) ^ 2 :=
    pow_le_pow_left₀ hx.le hxle 2
  have hfac : (0 : ℝ) < 1 - x ^ 2 / 6 := by
    have hsub : x ^ 2 / 6 ≤ (Real.pi / 3) ^ 2 / 6 := by
      rw [div_le_div_iff₀ (by norm_num) (by norm_num)]
      nlinarith [hxsq]
    linarith [hfacPi, hsub]
  have hlin : 0 < x - x ^ 3 / 6 := by
    have : x - x ^ 3 / 6 = x * (1 - x ^ 2 / 6) := by ring
    rw [this]
    exact mul_pos hx hfac
  have hsin : 0 < Real.sin x :=
    Real.sin_pos_of_pos_of_lt_pi hx (by linarith [hxle, Real.pi_pos])
  have hsqLt : (x - x ^ 3 / 6) ^ 2 < Real.sin x ^ 2 :=
    (sq_lt_sq₀ hlin.le hsin.le).mpr hcubic
  have hident : (x - x ^ 3 / 6) ^ 2 = x ^ 2 * (1 - x ^ 2 / 6) ^ 2 := by ring
  have hratio : (16 : ℝ) / (3 * Real.pi ^ 2) < (1 - x ^ 2 / 6) ^ 2 := by
    have hπsq : (3.14 : ℝ) ^ 2 < Real.pi ^ 2 :=
      pow_lt_pow_left₀ hπlo (by norm_num) (by decide : (2 : ℕ) ≠ 0)
    have hden : (16 : ℝ) / (3 * Real.pi ^ 2) < 16 / (3 * (3.14 : ℝ) ^ 2) := by
      rw [div_lt_div_iff₀ (mul_pos (by norm_num) (pow_pos Real.pi_pos 2))
        (mul_pos (by norm_num) (pow_pos (by norm_num : (0 : ℝ) < 3.14) 2))]
      nlinarith [hπsq]
    have hrat : (16 : ℝ) / (3 * (3.14 : ℝ) ^ 2) <
        (1 - ((3.15 : ℝ) / 3) ^ 2 / 6) ^ 2 := by
      norm_num
    have hwall : (1 - ((3.15 : ℝ) / 3) ^ 2 / 6) ^ 2 <
        (1 - (Real.pi / 3) ^ 2 / 6) ^ 2 := by
      have hsub : (Real.pi / 3) ^ 2 / 6 < ((3.15 : ℝ) / 3) ^ 2 / 6 := by
        have hdiv : Real.pi / 3 < (3.15 : ℝ) / 3 := by
          rw [div_lt_div_iff₀ (by norm_num) (by norm_num)]
          nlinarith [hπhi]
        have hpow : (Real.pi / 3) ^ 2 < ((3.15 : ℝ) / 3) ^ 2 :=
          pow_lt_pow_left₀ hdiv (div_nonneg Real.pi_nonneg (by norm_num))
            (by decide : (2 : ℕ) ≠ 0)
        rw [div_lt_div_iff₀ (by norm_num) (by norm_num)]
        nlinarith [hpow]
      have hbase : 1 - ((3.15 : ℝ) / 3) ^ 2 / 6 < 1 - (Real.pi / 3) ^ 2 / 6 := by
        linarith [hsub]
      exact pow_lt_pow_left₀ hbase hfacWall.le (by decide : (2 : ℕ) ≠ 0)
    have hmono : (1 - (Real.pi / 3) ^ 2 / 6) ^ 2 ≤ (1 - x ^ 2 / 6) ^ 2 := by
      have hbase : 1 - (Real.pi / 3) ^ 2 / 6 ≤ 1 - x ^ 2 / 6 := by
        have hsub : x ^ 2 / 6 ≤ (Real.pi / 3) ^ 2 / 6 := by
          rw [div_le_div_iff₀ (by norm_num) (by norm_num)]
          nlinarith [hxsq]
        linarith [hsub]
      exact pow_le_pow_left₀ hfacPi.le hbase 2
    exact lt_of_lt_of_le (lt_trans (lt_trans hden hrat) hwall) hmono
  have hx2 : 0 < x ^ 2 := pow_pos hx 2
  have hfloor : (16 : ℝ) / (3 * (N : ℝ) ^ 2) =
      x ^ 2 * ((16 : ℝ) / (3 * Real.pi ^ 2)) := by
    unfold x
    field_simp
  have hmul : x ^ 2 * ((16 : ℝ) / (3 * Real.pi ^ 2)) <
      x ^ 2 * (1 - x ^ 2 / 6) ^ 2 :=
    mul_lt_mul_of_pos_left hratio hx2
  rw [hfloor]
  exact hmul.trans (by simpa [hident] using hsqLt)

theorem transverse_defect_gt_height {N : ℕ} (hN : 3 ≤ N) :
    -JNormalized (oneAxisDual (stepAngle N)) <
      1 - computationalWeight
        (applyMat (dualRotorMat (EuclideanSpace.single 0 (stepAngle N))) spinUp) := by
  have hpos : 0 < N := lt_of_lt_of_le (by decide : 0 < 3) hN
  have hJ : -JNormalized (oneAxisDual (stepAngle N)) =
      (16 : ℝ) / (3 * (N : ℝ) ^ 2) := by
    rw [JNormalized_oneStep hpos]
    ring
  rw [hJ, transverseStep_defect hpos]
  exact defect_gt_floor hN

theorem transverse_defect_below_inv_pow {N : ℕ} (hN : 10 ^ 19 < N) :
    Real.sin (Real.pi / (N : ℝ)) ^ 2 < (1 : ℝ) / 10 ^ 37 := by
  have hpos : 0 < N := lt_trans (by decide : (0 : ℕ) < 10 ^ 19) hN
  have h3 : 3 ≤ N := le_trans (by decide : (3 : ℕ) ≤ 10 ^ 19) (le_of_lt hN)
  have hhigh := (defect_between_floor h3).2
  have hceil : (3 * Real.pi ^ 2 / 16) * ((16 : ℝ) / (3 * (N : ℝ) ^ 2)) =
      Real.pi ^ 2 / (N : ℝ) ^ 2 := by
    field_simp
  rw [hceil] at hhigh
  have hπsq : Real.pi ^ 2 < 10 := by
    have hsq : Real.pi ^ 2 < (3.15 : ℝ) ^ 2 :=
      pow_lt_pow_left₀ pi_lt_d2 Real.pi_nonneg (by decide : (2 : ℕ) ≠ 0)
    have hnum : (3.15 : ℝ) ^ 2 < 10 := by norm_num
    exact hsq.trans hnum
  have hcast : (10 : ℝ) ^ 19 < (N : ℝ) := by exact_mod_cast hN
  have hsqN : (10 : ℝ) ^ 38 < (N : ℝ) ^ 2 := by
    have hpow : ((10 : ℝ) ^ 19) ^ 2 < (N : ℝ) ^ 2 :=
      pow_lt_pow_left₀ hcast (by positivity) (by decide : (2 : ℕ) ≠ 0)
    have hid : ((10 : ℝ) ^ 19) ^ 2 = (10 : ℝ) ^ 38 := by
      rw [← pow_mul]
    simpa [hid] using hpow
  have hdiv : Real.pi ^ 2 / (N : ℝ) ^ 2 < 10 / (10 : ℝ) ^ 38 := by
    rw [div_lt_div_iff₀ (pow_pos (by exact_mod_cast hpos) 2) (by positivity)]
    nlinarith [hπsq, hsqN, Real.pi_pos]
  have hten : (10 : ℝ) / (10 : ℝ) ^ 38 = 1 / 10 ^ 37 := by norm_num
  exact hhigh.trans (by simpa [hten] using hdiv)

theorem threeHundred_square {N : ℕ} (hN : 10 ^ 19 < N) :
    IsAdmissibleContinuous (alignedSteps 300 N) ∧
      JNormalized (alignedSteps 300 N) =
        (300 : ℝ) ^ 2 * JNormalized (alignedSteps 1 N) ∧
      -((1 : ℝ) / 10 ^ 32) < JNormalized (alignedSteps 300 N) ∧
      JNormalized (alignedSteps 300 N) < 0 := by
  have hpos : 0 < N := lt_trans (by decide : (0 : ℕ) < 10 ^ 19) hN
  have hadm : 4 * 300 ≤ N :=
    le_trans (by decide : 4 * 300 ≤ 10 ^ 19) (le_of_lt hN)
  have hrel : JNormalized (alignedSteps 300 N) =
      (300 : ℝ) ^ 2 * JNormalized (alignedSteps 1 N) := by
    rw [collective_square (n := 300) hpos, collective_square (n := 1) hpos]
    ring
  have hform : JNormalized (alignedSteps 300 N) =
      -((90000 : ℝ) * 16 / (3 * (N : ℝ) ^ 2)) := by
    rw [collective_square (n := 300) hpos, JNormalized_oneStep hpos]
    ring
  have hcast : (10 : ℝ) ^ 19 < (N : ℝ) := by exact_mod_cast hN
  have hsqN : (10 : ℝ) ^ 38 < (N : ℝ) ^ 2 := by
    have hpow : ((10 : ℝ) ^ 19) ^ 2 < (N : ℝ) ^ 2 :=
      pow_lt_pow_left₀ hcast (by positivity) (by decide : (2 : ℕ) ≠ 0)
    have hid : ((10 : ℝ) ^ 19) ^ 2 = (10 : ℝ) ^ 38 := by
      rw [← pow_mul]
    simpa [hid] using hpow
  have hposFrac : (0 : ℝ) < (90000 : ℝ) * 16 / (3 * (N : ℝ) ^ 2) := by
    positivity
  have htiny : (90000 : ℝ) * 16 / (3 * (N : ℝ) ^ 2) < 1 / 10 ^ 32 := by
    have hcap : (90000 : ℝ) * 16 / (3 * (10 : ℝ) ^ 38) < 1 / 10 ^ 32 := by
      norm_num
    have hdenN : (0 : ℝ) < 3 * (N : ℝ) ^ 2 := by positivity
    have hden10 : (0 : ℝ) < 3 * (10 : ℝ) ^ 38 := by positivity
    have hlt : (90000 : ℝ) * 16 / (3 * (N : ℝ) ^ 2) <
        (90000 : ℝ) * 16 / (3 * (10 : ℝ) ^ 38) := by
      rw [div_lt_div_iff₀ hdenN hden10]
      nlinarith [hsqN]
    exact hlt.trans hcap
  refine ⟨collective_admissible hadm, hrel, ?_, ?_⟩
  · rw [hform]
    exact neg_lt_neg htiny
  · rw [hform]
    exact neg_lt_zero.mpr hposFrac

/-! ### Own shares and mutual shares -/

/-- Height of one graviton, the step that travels alone. -/
def farHeight (N : ℕ) : ℝ :=
  JNormalized (oneAxisDual (stepAngle N))

/-- Sum of the own shares of `n` aligned gravitons. -/
def ownSum (n N : ℕ) : ℝ :=
  (n : ℝ) * farHeight N

/-- Sum of the ordered-pair shares among `n` aligned gravitons. -/
def mutualSum (n N : ℕ) : ℝ :=
  (n : ℝ) * ((n : ℝ) - 1) * farHeight N

theorem farHeight_eq {N : ℕ} (hN : 0 < N) :
    farHeight N = -((16 : ℝ) / (3 * (N : ℝ) ^ 2)) :=
  JNormalized_oneStep hN

theorem farHeight_mismatch_rotation_sq {N : ℕ} (hN : 0 < N) :
    farHeight N =
      -((16 : ℝ) / (3 * Real.pi ^ 2)) *
        mismatchRotationHalfSqSum (oneAxisDual (stepAngle N)) := by
  unfold farHeight
  exact oneStep_JNormalized_mismatch_rotation_sq hN

theorem farHeight_neg {N : ℕ} (hN : 0 < N) : farHeight N < 0 := by
  rw [farHeight_eq hN]
  have hden : (0 : ℝ) < 3 * (N : ℝ) ^ 2 := by positivity
  exact neg_lt_zero.mpr (div_pos (by norm_num) hden)

theorem height_own_plus_mutual {n N : ℕ} (hN : 0 < N) :
    JNormalized (alignedSteps n N) = ownSum n N + mutualSum n N := by
  rw [collective_square hN]
  unfold ownSum mutualSum farHeight
  ring

theorem mutual_factor {n N : ℕ} :
    mutualSum n N = ((n : ℝ) - 1) * ownSum n N := by
  unfold mutualSum ownSum
  ring

theorem mutualSum_one (N : ℕ) : mutualSum 1 N = 0 := by
  unfold mutualSum
  ring

theorem lone_eq_far {N : ℕ} (hN : 0 < N) :
    JNormalized (alignedSteps 1 N) = farHeight N ∧ mutualSum 1 N = 0 := by
  refine ⟨?_, mutualSum_one N⟩
  rw [height_own_plus_mutual (n := 1) hN]
  unfold ownSum mutualSum
  ring

theorem added_step_split {n N : ℕ} (hN : 0 < N) :
    JNormalized (alignedSteps (n + 1) N) - JNormalized (alignedSteps n N) =
      farHeight N + (2 * (n : ℝ)) * farHeight N := by
  rw [collective_square (n := n + 1) hN, collective_square hN]
  have hJ : JNormalized (oneAxisDual (stepAngle N)) = farHeight N := rfl
  rw [hJ]
  have h1 : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by norm_cast
  rw [h1]
  have hsq : ((n : ℝ) + 1) ^ 2 = (n : ℝ) ^ 2 + 2 * (n : ℝ) + 1 := by ring
  rw [hsq]
  ring

theorem mutual_strict {n N : ℕ} (hN : 0 < N) (hn : 0 < n) :
    mutualSum (n + 1) N < mutualSum n N := by
  have hstep : mutualSum (n + 1) N =
      mutualSum n N + (2 * (n : ℝ)) * farHeight N := by
    unfold mutualSum
    have h1 : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by norm_cast
    rw [h1]
    ring
  have hpos : (0 : ℝ) < 2 * (n : ℝ) := by
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    positivity
  linarith [hstep, mul_neg_of_pos_of_neg hpos (farHeight_neg hN)]

theorem mutual_grows {n m N : ℕ} (hN : 0 < N) (hn : 1 ≤ n) (hnm : n < m) :
    mutualSum m N < mutualSum n N := by
  unfold mutualSum
  have hf := farHeight_neg hN
  have hcoef : (n : ℝ) * ((n : ℝ) - 1) < (m : ℝ) * ((m : ℝ) - 1) := by
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hnmR : (n : ℝ) < m := by exact_mod_cast hnm
    have hpos : (0 : ℝ) < (m : ℝ) - 1 := by linarith
    have hleft : (n : ℝ) * ((n : ℝ) - 1) ≤ (n : ℝ) * ((m : ℝ) - 1) :=
      mul_le_mul_of_nonneg_left (by linarith : (n : ℝ) - 1 ≤ (m : ℝ) - 1) (by linarith)
    have hright : (n : ℝ) * ((m : ℝ) - 1) < (m : ℝ) * ((m : ℝ) - 1) :=
      mul_lt_mul_of_pos_right hnmR hpos
    exact lt_of_le_of_lt hleft hright
  have hgap : (0 : ℝ) < (m : ℝ) * ((m : ℝ) - 1) - (n : ℝ) * ((n : ℝ) - 1) := by
    linarith
  have hprod :
      ((m : ℝ) * ((m : ℝ) - 1) - (n : ℝ) * ((n : ℝ) - 1)) * farHeight N < 0 :=
    mul_neg_of_pos_of_neg hgap hf
  have hassoc :
      (m : ℝ) * ((m : ℝ) - 1) * farHeight N -
          (n : ℝ) * ((n : ℝ) - 1) * farHeight N =
        ((m : ℝ) * ((m : ℝ) - 1) - (n : ℝ) * ((n : ℝ) - 1)) * farHeight N := by
    ring
  linarith

theorem mutual_below_own {n N : ℕ} (hN : 0 < N) (hn : 3 ≤ n) :
    mutualSum n N < ownSum n N ∧ ownSum n N < 0 := by
  have hnpos : 0 < n := lt_of_lt_of_le (by decide : (0 : ℕ) < 3) hn
  have hownNeg : ownSum n N < 0 := by
    unfold ownSum
    exact mul_neg_of_pos_of_neg (by exact_mod_cast hnpos) (farHeight_neg hN)
  have hlt : ((n : ℝ) - 1) * ownSum n N < ownSum n N := by
    have hgap : (1 : ℝ) < (n : ℝ) - 1 := by
      have h3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    have hdiff :
        ((n : ℝ) - 1) * ownSum n N - ownSum n N = ((n : ℝ) - 2) * ownSum n N := by
      ring
    have hpos : (0 : ℝ) < (n : ℝ) - 2 := by linarith
    linarith [hdiff, mul_neg_of_pos_of_neg hpos hownNeg]
  refine ⟨?_, hownNeg⟩
  rw [mutual_factor]
  exact hlt

theorem two_fourfold_split {N : ℕ} (hN : 0 < N) :
    JNormalized (alignedSteps 2 N) = ownSum 2 N + mutualSum 2 N ∧
      ownSum 2 N = 2 * farHeight N ∧
      mutualSum 2 N = 2 * farHeight N := by
  refine ⟨height_own_plus_mutual hN, ?_, ?_⟩
  · unfold ownSum
    ring
  · unfold mutualSum
    ring

theorem axisExpress_origin : axisExpress 0 0 = (0, 0) := by
  refine axisExpress_triangle ⟨le_rfl, le_rfl, ?_⟩
  simpa using div_nonneg Real.pi_nonneg (by norm_num : (0 : ℝ) ≤ 2)

theorem express_oneAxis (θ : ℝ) : express (oneAxisDual θ) = expressedOneAxis θ := by
  refine congrArg₂ TorsionParams.mk ?_ ?_
  · funext a
    fin_cases a
    · rfl
    · change (axisExpress 0 0).1 = 0
      rw [axisExpress_origin]
    · change (axisExpress 0 0).1 = 0
      rw [axisExpress_origin]
  · funext a
    fin_cases a
    · rfl
    · change (axisExpress 0 0).2 = 0
      rw [axisExpress_origin]
    · change (axisExpress 0 0).2 = 0
      rw [axisExpress_origin]

theorem express_aligned (n N : ℕ) :
    express (alignedSteps n N) = expressedOneAxis ((n : ℝ) * stepAngle N) := by
  simpa [alignedSteps] using express_oneAxis ((n : ℝ) * stepAngle N)

theorem expressed_own_plus_mutual {n N : ℕ} (hN : 0 < N) (h : 4 * n ≤ N) :
    JNormalized (express (alignedSteps n N)) = ownSum n N + mutualSum n N := by
  rw [express_eq_of_admissible (collective_admissible_legacy h)]
  exact height_own_plus_mutual hN

theorem expressed_locks_while_mutual_grows {n N : ℕ} (hN : 0 < N) (h : N ≤ 4 * n)
    (hn : 0 < n) :
    JNormalized (express (alignedSteps n N)) = -((1 : ℝ) / 3) ∧
      mutualSum (n + 1) N < mutualSum n N := by
  refine ⟨?_, mutual_strict hN hn⟩
  rw [express_aligned]
  exact collective_locks hN h

/-! ### Carriers of one angle -/

/-- Pure usual rapidity `θ` on axis 0. -/
def oneAxisUsual (θ : ℝ) : TorsionParams where
  alpha := fun
    | 0 => θ
    | 1 => 0
    | 2 => 0
  beta := fun
    | 0 => 0
    | 1 => 0
    | 2 => 0

/-- Equal-scale rapidity `θ` on axis 0. -/
def oneAxisBalanced (θ : ℝ) : TorsionParams where
  alpha := fun
    | 0 => θ
    | 1 => 0
    | 2 => 0
  beta := fun
    | 0 => θ
    | 1 => 0
    | 2 => 0

theorem J_oneAxisUsual (θ : ℝ) : J (oneAxisUsual θ) = θ ^ 2 / 2 := by
  rw [J_coef]
  simp [oneAxisUsual, Fin.sum_univ_three]
  ring

theorem JNormalized_oneAxisUsual (θ : ℝ) :
    JNormalized (oneAxisUsual θ) = ((4 : ℝ) / (3 * Real.pi ^ 2)) * θ ^ 2 := by
  unfold JNormalized
  rw [J_oneAxisUsual]
  ring

theorem JNormalized_usualStep {N : ℕ} (hN : 0 < N) :
    JNormalized (oneAxisUsual (stepAngle N)) = (16 : ℝ) / (3 * (N : ℝ) ^ 2) := by
  rw [JNormalized_oneAxisUsual, stepAngle]
  have hNz : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hN)
  field_simp [hNz]
  ring

theorem J_oneAxisBalanced (θ : ℝ) : J (oneAxisBalanced θ) = 0 := by
  rw [J_coef]
  simp [oneAxisBalanced]

theorem JNormalized_balanced (θ : ℝ) : JNormalized (oneAxisBalanced θ) = 0 := by
  unfold JNormalized
  rw [J_oneAxisBalanced]
  ring

theorem usualStep_admissible_legacy {N : ℕ} (hN : 4 ≤ N) :
    IsAdmissibleContinuousLegacy (oneAxisUsual (stepAngle N)) := by
  have hθ := (stepAngle_pos (lt_of_lt_of_le (by decide : 0 < 4) hN)).le
  have hle := stepAngle_le_half_pi hN
  intro a
  fin_cases a <;> simp only [oneAxisUsual]
  · exact ⟨hθ, le_rfl, by linarith [hθ, hle]⟩
  · exact ⟨le_rfl, le_rfl, le_rfl⟩
  · exact ⟨le_rfl, le_rfl, le_rfl⟩

theorem usualStep_admissible {N : ℕ} (hN : 4 ≤ N) :
    IsAdmissibleContinuous (oneAxisUsual (stepAngle N)) :=
  legacy_admissible_implies_mismatch _ (usualStep_admissible_legacy hN)

theorem balancedStep_admissible_legacy {N : ℕ} (hN : 4 ≤ N) :
    IsAdmissibleContinuousLegacy (oneAxisBalanced (stepAngle N / 2)) := by
  have hsum := stepAngle_le_half_pi hN
  have hhalf := div_nonneg (stepAngle_nonneg N) (by norm_num)
  intro a
  fin_cases a <;> simp only [oneAxisBalanced]
  · exact ⟨hhalf, hhalf, by nlinarith [hhalf, hsum]⟩
  · exact ⟨le_rfl, le_rfl, le_rfl⟩
  · exact ⟨le_rfl, le_rfl, le_rfl⟩

theorem balancedStep_admissible {N : ℕ} (hN : 4 ≤ N) :
    IsAdmissibleContinuous (oneAxisBalanced (stepAngle N / 2)) :=
  legacy_admissible_implies_mismatch _ (balancedStep_admissible_legacy hN)

theorem gammaS_usual (θ : ℝ) : gammaS θ 0 = Real.cosh (θ / 2) := by
  unfold gammaS
  simp

theorem gammaS_dual (θ : ℝ) : gammaS 0 θ = Real.cos (θ / 2) := by
  unfold gammaS
  simp

theorem gammaS_balanced (θ : ℝ) : gammaS θ θ = gammaSEqualLegacy (θ / 2) := by
  unfold gammaS gammaSEqualLegacy
  ring_nf

theorem usual_interference_gt_one {θ : ℝ} (hθ : 0 < θ) : 1 < gammaS θ 0 := by
  rw [gammaS_usual, Real.cosh_eq]
  have hpos : 0 < θ / 2 := by linarith
  set t : ℝ := Real.exp (θ / 2)
  have ht0 : 0 < t := Real.exp_pos _
  have hexp : 1 < t := by
    rw [Real.one_lt_exp_iff]
    exact hpos
  have hinv : Real.exp (-(θ / 2)) = t⁻¹ := by
    simp [t, Real.exp_neg]
  rw [hinv]
  have htwo : 2 * t < t ^ 2 + 1 := by nlinarith [hexp]
  have hmul : (t + t⁻¹) * t = t ^ 2 + 1 := by field_simp [ht0.ne']
  have hlt : 2 * t < (t + t⁻¹) * t := by simpa [hmul] using htwo
  have hclear : 2 < t + t⁻¹ := (mul_lt_mul_iff_of_pos_right ht0).mp hlt
  linarith

theorem dual_interference_between {θ : ℝ} (h0 : 0 < θ) (hθ : θ ≤ Real.pi / 2) :
    0 < gammaS 0 θ ∧ gammaS 0 θ < 1 := by
  rw [gammaS_dual]
  refine ⟨?_, ?_⟩
  · exact Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith [hθ, Real.pi_pos]⟩
  · have hlt : Real.cos (θ / 2) < Real.cos 0 :=
      Real.cos_lt_cos_of_nonneg_of_le_pi (by linarith) (by linarith [hθ, Real.pi_pos])
        (by linarith)
    simpa [Real.cos_zero] using hlt

theorem gammaSEqualLegacy_pos_up_to_quarter {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ Real.pi / 4) :
    0 < gammaSEqualLegacy x := by
  rcases hx0.eq_or_lt with rfl | hxpos
  · simp [gammaSEqualLegacy]
  · unfold gammaSEqualLegacy
    have hcos : 0 < cos x :=
      cos_pos_of_mem_Ioo ⟨hxpos, lt_of_le_of_lt hx (by linarith [Real.pi_pos])⟩
    exact mul_pos (Real.cosh_pos _) hcos

theorem balanced_interference_pos {N : ℕ} (hN : 4 ≤ N) :
    0 < gammaS (stepAngle N / 2) (stepAngle N / 2) := by
  rw [gammaS_balanced]
  have hstep := stepAngle_le_half_pi hN
  refine gammaSEqualLegacy_pos_up_to_quarter ?_ ?_
  · exact div_nonneg (div_nonneg (stepAngle_nonneg N) (by norm_num)) (by norm_num)
  · have hform : stepAngle N / 2 / 2 = stepAngle N / 4 := by ring
    rw [hform]
    have hdiv : stepAngle N / 4 ≤ (Real.pi / 2) / 4 :=
      div_le_div_of_nonneg_right hstep (by norm_num)
    have hq : (Real.pi / 2) / 4 = Real.pi / 8 := by ring
    have hcmp : Real.pi / 8 ≤ Real.pi / 4 := by
      rw [div_le_div_iff₀ (by norm_num) (by norm_num)]
      nlinarith [Real.pi_pos]
    exact le_trans (by simpa [hq] using hdiv) hcmp

/-! ### Primary overlap channel (`cosh·cos`; legacy `gammaS` separate) -/

theorem graviton_usual_overlap_gt_one {θ : ℝ} (hθ : 0 < θ) :
    1 < MismatchAngle.axisOverlapScalar θ 0 := by
  rw [axisOverlap_primary_eq_gammaS_usual]
  exact usual_interference_gt_one hθ

theorem graviton_dual_overlap_between {θ : ℝ} (h0 : 0 < θ) (hθ : θ ≤ Real.pi / 2) :
    0 < MismatchAngle.axisOverlapScalar 0 θ ∧
      MismatchAngle.axisOverlapScalar 0 θ < 1 := by
  rw [axisOverlap_primary_eq_gammaS_dual]
  exact dual_interference_between h0 hθ

theorem graviton_primary_balanced_overlap (θ : ℝ) :
    MismatchAngle.axisOverlapScalar θ θ =
      Real.cosh (θ / 2) * Real.cos (θ / 2) := by
  simp [MismatchAngle.axisOverlapScalar]

theorem graviton_legacy_balanced_overlap (θ : ℝ) :
    MismatchAngle.axisOverlapLegacy θ θ = gammaSEqualLegacy (θ / 2) := by
  have h : 2 * (θ / 2) = θ := by ring
  simpa [h] using axisOverlap_eq_gammaSEqual_balanced (θ / 2)

theorem graviton_balanced_overlap_pos {N : ℕ} (hN : 4 ≤ N) :
    0 < MismatchAngle.axisOverlapScalar (stepAngle N / 2) (stepAngle N / 2) := by
  rw [graviton_primary_balanced_overlap]
  have hform : stepAngle N / 2 / 2 = stepAngle N / 4 := by ring
  rw [hform]
  have hstep := stepAngle_le_half_pi hN
  have hNpos : 0 < N := lt_of_lt_of_le (by decide : 0 < 4) hN
  have hlo : -(Real.pi / 2) < stepAngle N / 4 := by linarith [stepAngle_pos hNpos, Real.pi_pos]
  have hhi : stepAngle N / 4 < Real.pi / 2 := by nlinarith [hstep, Real.pi_pos]
  have hmem : stepAngle N / 4 ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := ⟨hlo, hhi⟩
  exact mul_pos (Real.cosh_pos _) (Real.cos_pos_of_mem_Ioo hmem)

theorem gammaSEqual_pi_neg : gammaSEqual Real.pi < 0 := by
  have h := gammaSEqual_nat_mul_pi 1
  simp only [Nat.cast_one, one_mul, pow_one] at h
  rw [h]
  linarith [Real.cosh_pos Real.pi]

theorem gammaSEqualLegacy_pi_neg : gammaSEqualLegacy Real.pi < 0 := by
  unfold gammaSEqualLegacy
  simp [cos_pi, sin_pi]
  linarith [Real.cosh_pos Real.pi]

theorem negative_interference_not_admissible :
    gammaS (2 * Real.pi) (2 * Real.pi) < 0 ∧
      ¬ IsAdmissibleContinuous (oneAxisBalanced (2 * Real.pi)) := by
  refine ⟨?_, ?_⟩
  · rw [gammaS_balanced]
    simpa using gammaSEqualLegacy_pi_neg
  · intro h
    have hsum := (h 0).2.2.2
    simp [oneAxisBalanced] at hsum
    linarith [Real.pi_pos]

theorem graviton_primary_overlap_zero_at_rotation_pi :
    axisOverlapScalar Real.pi Real.pi = 0 ∧
      MismatchAngle.axisOverlapLegacy (2 * Real.pi) (2 * Real.pi) < 0 ∧
      ¬ IsAdmissibleContinuous (oneAxisBalanced (2 * Real.pi)) := by
  refine ⟨axisOverlap_zero_at_full_rotation Real.pi, ?_, negative_interference_not_admissible.2⟩
  · rw [graviton_legacy_balanced_overlap]
    simpa using gammaSEqualLegacy_pi_neg

theorem graviton_step_usual_overlap_gt_one {N : ℕ} (hN : 4 ≤ N) :
    1 < axisOverlapScalar (stepAngle N) 0 := by
  have hpos : 0 < N := lt_of_lt_of_le (by decide : 0 < 4) hN
  exact graviton_usual_overlap_gt_one (stepAngle_pos hpos)

theorem graviton_step_dual_overlap_between {N : ℕ} (hN : 4 ≤ N) :
    0 < axisOverlapScalar 0 (stepAngle N) ∧
      axisOverlapScalar 0 (stepAngle N) < 1 := by
  have hpos : 0 < N := lt_of_lt_of_le (by decide : 0 < 4) hN
  exact graviton_dual_overlap_between (stepAngle_pos hpos) (stepAngle_le_half_pi hN)

theorem carriers_distinct {N : ℕ} (hN : 4 ≤ N) :
    oneAxisUsual (stepAngle N) ≠ oneAxisDual (stepAngle N) ∧
      oneAxisDual (stepAngle N) ≠ oneAxisBalanced (stepAngle N / 2) ∧
      oneAxisUsual (stepAngle N) ≠ oneAxisBalanced (stepAngle N / 2) := by
  have hθ : 0 < stepAngle N := stepAngle_pos (lt_of_lt_of_le (by decide : 0 < 4) hN)
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have := congrArg (fun p : TorsionParams => p.beta 0) h
    simp [oneAxisUsual, oneAxisDual] at this
    linarith
  · intro h
    have := congrArg (fun p : TorsionParams => p.beta 0) h
    simp [oneAxisDual, oneAxisBalanced] at this
    linarith
  · intro h
    have := congrArg (fun p : TorsionParams => p.alpha 0) h
    simp [oneAxisUsual, oneAxisBalanced] at this
    linarith

theorem three_carriers {N : ℕ} (hN : 5 ≤ N) :
    IsAdmissibleContinuous (oneAxisUsual (stepAngle N)) ∧
      IsAdmissibleContinuous (oneAxisDual (stepAngle N)) ∧
      IsAdmissibleContinuous (oneAxisBalanced (stepAngle N / 2)) ∧
      JNormalized (oneAxisUsual (stepAngle N)) =
        (16 : ℝ) / (3 * (N : ℝ) ^ 2) ∧
      JNormalized (oneAxisDual (stepAngle N)) =
        -((16 : ℝ) / (3 * (N : ℝ) ^ 2)) ∧
      JNormalized (oneAxisBalanced (stepAngle N / 2)) = 0 ∧
      1 < gammaS (stepAngle N) 0 ∧
      0 < gammaS 0 (stepAngle N) ∧ gammaS 0 (stepAngle N) < 1 ∧
      0 < gammaS (stepAngle N / 2) (stepAngle N / 2) ∧
      -((1 : ℝ) / 3) < JNormalized (oneAxisDual (stepAngle N)) ∧
      JNormalized (oneAxisUsual (stepAngle N)) < (1 : ℝ) / 3 := by
  have h4 : 4 ≤ N := le_trans (by decide : (4 : ℕ) ≤ 5) hN
  have hpos : 0 < N := lt_of_lt_of_le (by decide : 0 < 5) hN
  have hθ : 0 < stepAngle N := stepAngle_pos hpos
  have hhalf := stepAngle_le_half_pi h4
  have hheight := oneStep_below_corner hN
  have hdual := dual_interference_between hθ hhalf
  refine ⟨usualStep_admissible h4, oneStep_admissible h4, balancedStep_admissible h4,
    JNormalized_usualStep hpos, JNormalized_oneStep hpos, JNormalized_balanced _,
    usual_interference_gt_one hθ, hdual.1, hdual.2, balanced_interference_pos h4,
    hheight.1, ?_⟩
  rw [JNormalized_usualStep hpos]
  have hden : (0 : ℝ) < 3 * (N : ℝ) ^ 2 := by positivity
  rw [div_lt_iff₀ hden]
  have hsq : (25 : ℝ) ≤ (N : ℝ) ^ 2 := by
    exact_mod_cast Nat.pow_le_pow_left hN 2
  have hright : (1 : ℝ) / 3 * (3 * (N : ℝ) ^ 2) = (N : ℝ) ^ 2 := by ring
  linarith [hsq, hright]

theorem excess_unexpressed {n N : ℕ} (hN : 0 < N) (h : N < 4 * n) :
    JNormalized (alignedSteps n N) < JNormalized (express (alignedSteps n N)) ∧
      JNormalized (express (alignedSteps n N)) = -((1 : ℝ) / 3) := by
  have hlt : Real.pi / 2 < (n : ℝ) * stepAngle N := by
    have hge := alignedAngle_ge_half_pi hN (le_of_lt h)
    by_contra hnot
    have hle : (n : ℝ) * stepAngle N ≤ Real.pi / 2 := le_of_not_gt hnot
    have heq : (n : ℝ) * stepAngle N = Real.pi / 2 := le_antisymm hle hge
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    have hNz : (N : ℝ) ≠ 0 := ne_of_gt hN0
    have hangle : (n : ℝ) * (2 * Real.pi / N) = Real.pi / 2 := by
      simpa [stepAngle] using heq
    have hmul : (n : ℝ) * (2 * Real.pi) = Real.pi / 2 * N := by
      have hscaled := congrArg (fun t : ℝ => t * N) hangle
      have hleft : (n : ℝ) * (2 * Real.pi / N) * N = (n : ℝ) * (2 * Real.pi) := by
        field_simp [hNz]
      linarith
    have hNeq : (N : ℝ) = 4 * (n : ℝ) := by
      have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
      have hdivL : (n : ℝ) * (2 * Real.pi) / Real.pi = (n : ℝ) * 2 := by
        field_simp [hπ]
      have hdivR : Real.pi / 2 * N / Real.pi = N / 2 := by
        field_simp [hπ]
      have hscaled := congrArg (fun t : ℝ => t / Real.pi) hmul
      linarith
    have hNat : N = 4 * n := by exact_mod_cast hNeq
    simp [hNat] at h
  refine ⟨?_, ?_⟩
  · rw [express_aligned, alignedSteps]
    have hJ := internal_exceeds_lock hlt
    have hc : (0 : ℝ) < 8 / (3 * Real.pi ^ 2) := by positivity
    unfold JNormalized
    exact mul_lt_mul_of_pos_left hJ hc
  · rw [express_aligned]
    exact expressed_locks hlt.le

theorem carrier_roles {N : ℕ} (hN : 5 ≤ N) :
    1 < gammaS (stepAngle N) 0 ∧
      0 < gammaS 0 (stepAngle N) ∧ gammaS 0 (stepAngle N) < 1 ∧
      0 < gammaS (stepAngle N / 2) (stepAngle N / 2) ∧
      JNormalized (oneAxisBalanced (stepAngle N / 2)) = 0 ∧
      JNormalized (oneAxisUsual (stepAngle N)) =
        -JNormalized (oneAxisDual (stepAngle N)) := by
  obtain ⟨_, _, _, hU, hD, hB, hγU, hγDpos, hγDlt, hγB, _, _⟩ := three_carriers hN
  refine ⟨hγU, hγDpos, hγDlt, hγB, hB, ?_⟩
  linarith

/-! ### Gravitons on distinct axes -/

/-- One graviton on axis 0 and one on axis 1. -/
def perpSteps (N : ℕ) : TorsionParams where
  alpha := fun
    | 0 => 0
    | 1 => 0
    | 2 => 0
  beta := fun
    | 0 => stepAngle N
    | 1 => stepAngle N
    | 2 => 0

/-- One graviton on each of the three axes. -/
def splitSteps (N : ℕ) : TorsionParams where
  alpha := fun
    | 0 => 0
    | 1 => 0
    | 2 => 0
  beta := fun
    | 0 => stepAngle N
    | 1 => stepAngle N
    | 2 => stepAngle N

theorem J_perpSteps (N : ℕ) :
    JNormalized (perpSteps N) = 2 * JNormalized (oneAxisDual (stepAngle N)) := by
  unfold JNormalized
  rw [J_coef, J_oneAxisDual]
  simp [perpSteps, Fin.sum_univ_three]
  ring

theorem J_splitSteps (N : ℕ) :
    JNormalized (splitSteps N) = 3 * JNormalized (oneAxisDual (stepAngle N)) := by
  unfold JNormalized
  rw [J_coef, J_oneAxisDual]
  simp [splitSteps, Fin.sum_univ_three]
  ring

theorem perpSteps_admissible {N : ℕ} (hN : 4 ≤ N) :
    IsAdmissibleContinuous (perpSteps N) := by
  have hθ : 0 ≤ stepAngle N :=
    (stepAngle_pos (lt_of_lt_of_le (by decide : 0 < 4) hN)).le
  have hle := stepAngle_le_half_pi hN
  intro a
  fin_cases a
  · simp only [perpSteps]
    exact ⟨le_rfl, hθ, by linarith [Real.pi_pos], by linarith [hle, hθ]⟩
  · simp only [perpSteps]
    exact ⟨le_rfl, hθ, by linarith [Real.pi_pos], by linarith [hle, hθ]⟩
  · simp only [perpSteps]
    refine ⟨le_rfl, le_rfl, by linarith [Real.pi_pos], by linarith⟩

theorem splitSteps_admissible {N : ℕ} (hN : 4 ≤ N) :
    IsAdmissibleContinuous (splitSteps N) := by
  have hθ : 0 ≤ stepAngle N :=
    (stepAngle_pos (lt_of_lt_of_le (by decide : 0 < 4) hN)).le
  have hle := stepAngle_le_half_pi hN
  intro a
  fin_cases a <;> simp only [splitSteps] <;>
    exact ⟨le_rfl, hθ, by linarith [Real.pi_pos], by linarith [hle, hθ]⟩

theorem perp_twofold {N : ℕ} (hN : 4 ≤ N) :
    IsAdmissibleContinuous (perpSteps N) ∧
      JNormalized (perpSteps N) = 2 * farHeight N := by
  have hpos : 0 < N := lt_of_lt_of_le (by decide : 0 < 4) hN
  refine ⟨perpSteps_admissible hN, ?_⟩
  rw [J_perpSteps]
  rfl

theorem perp_missing_pair {N : ℕ} (hN : 8 ≤ N) :
    JNormalized (alignedSteps 2 N) = JNormalized (perpSteps N) + mutualSum 2 N ∧
      JNormalized (alignedSteps 2 N) < JNormalized (perpSteps N) ∧
      mutualSum 2 N = 2 * farHeight N := by
  have hpos : 0 < N := lt_of_lt_of_le (by decide : 0 < 8) hN
  have h4 : 4 ≤ N := le_trans (by decide : (4 : ℕ) ≤ 8) hN
  have hsplit := two_fourfold_split hpos
  have hperp := (perp_twofold h4).2
  refine ⟨?_, ?_, hsplit.2.2⟩
  · rw [hsplit.1, hsplit.2.1, hsplit.2.2, hperp]
  · rw [hsplit.1, hsplit.2.1, hsplit.2.2, hperp]
    have hneg := farHeight_neg hpos
    linarith [hneg]

theorem split_threefold {N : ℕ} (hN : 4 ≤ N) :
    IsAdmissibleContinuous (splitSteps N) ∧
      JNormalized (splitSteps N) = 3 * farHeight N := by
  have hpos : 0 < N := lt_of_lt_of_le (by decide : 0 < 4) hN
  refine ⟨splitSteps_admissible hN, ?_⟩
  rw [J_splitSteps]
  rfl

theorem split_at_four :
    IsAdmissibleContinuous (splitSteps 4) ∧
      JNormalized (splitSteps 4) = -1 ∧
      (splitSteps 4).beta 0 = Real.pi / 2 ∧
      (splitSteps 4).beta 1 = Real.pi / 2 ∧
      (splitSteps 4).beta 2 = Real.pi / 2 := by
  have hadm := splitSteps_admissible (N := 4) (by decide)
  have hJ := (split_threefold (N := 4) (by decide)).2
  have hfar := farHeight_eq (N := 4) (by decide)
  refine ⟨hadm, ?_, ?_, ?_, ?_⟩
  · rw [hJ, hfar]
    norm_num
  · simp [splitSteps, stepAngle]
    ring
  · simp [splitSteps, stepAngle]
    ring
  · simp [splitSteps, stepAngle]
    ring

theorem split_above_floor {N : ℕ} (hN : 5 ≤ N) :
    -1 < JNormalized (splitSteps N) ∧ JNormalized (splitSteps N) < 0 := by
  have hpos : 0 < N := lt_of_lt_of_le (by decide : 0 < 5) hN
  have h4 : 4 ≤ N := le_trans (by decide : (4 : ℕ) ≤ 5) hN
  have hJ := (split_threefold h4).2
  rw [hJ, farHeight_eq hpos]
  have hform : (3 : ℝ) * (-((16 : ℝ) / (3 * (N : ℝ) ^ 2))) =
      -((16 : ℝ) / (N : ℝ) ^ 2) := by ring
  rw [hform]
  constructor
  · rw [neg_lt_neg_iff]
    have hden : (0 : ℝ) < (N : ℝ) ^ 2 := by positivity
    rw [div_lt_one hden]
    have h5 : (25 : ℝ) ≤ (N : ℝ) ^ 2 := by exact_mod_cast Nat.pow_le_pow_left hN 2
    linarith
  · have hden : (0 : ℝ) < (N : ℝ) ^ 2 := by positivity
    exact neg_lt_zero.mpr (div_pos (by norm_num) hden)

theorem split_above_lock {N : ℕ} (hN : 7 ≤ N) :
    -((1 : ℝ) / 3) < JNormalized (splitSteps N) := by
  have hpos : 0 < N := lt_of_lt_of_le (by decide : 0 < 7) hN
  have h4 : 4 ≤ N := le_trans (by decide : (4 : ℕ) ≤ 7) hN
  have hJ := (split_threefold h4).2
  rw [hJ, farHeight_eq hpos]
  have hform : (3 : ℝ) * (-((16 : ℝ) / (3 * (N : ℝ) ^ 2))) =
      -((16 : ℝ) / (N : ℝ) ^ 2) := by ring
  rw [hform, neg_lt_neg_iff]
  rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
  have h7 : (49 : ℝ) ≤ (N : ℝ) ^ 2 := by exact_mod_cast Nat.pow_le_pow_left hN 2
  linarith

theorem split_missing_pairs {N : ℕ} (hN : 12 ≤ N) :
    IsAdmissibleContinuous (alignedSteps 3 N) ∧
      JNormalized (alignedSteps 3 N) =
        JNormalized (splitSteps N) + 6 * farHeight N ∧
      JNormalized (alignedSteps 3 N) < JNormalized (splitSteps N) := by
  have hpos : 0 < N := lt_of_lt_of_le (by decide : 0 < 12) hN
  have h4 : 4 ≤ N := le_trans (by decide : (4 : ℕ) ≤ 12) hN
  have hcone : 4 * 3 ≤ N := by simpa [Nat.reduceMul] using hN
  have hadm := collective_admissible hcone
  have hsq := collective_square (n := 3) hpos
  have hsplit := (split_threefold h4).2
  have hfar : JNormalized (oneAxisDual (stepAngle N)) = farHeight N := rfl
  refine ⟨hadm, ?_, ?_⟩
  · rw [hsq, hsplit, hfar]
    ring
  · rw [hsq, hsplit, hfar]
    have hneg := farHeight_neg hpos
    have hsq3 : ((3 : ℕ) : ℝ) ^ 2 = 9 := by norm_num
    rw [hsq3]
    linarith [hneg]

/-! ### The same two steps, read as rotors -/

private theorem cyclicRep_one_oo : cyclicRep 1 0 0 = 0 := by
  unfold cyclicRep pauli pauliY
  simp [Matrix.smul_apply]

private theorem cyclicRep_one_ol : cyclicRep 1 0 1 = -1 := by
  unfold cyclicRep pauli pauliY
  simp [Matrix.smul_apply, neg_mul, Complex.I_mul_I]

private theorem cyclicRep_one_lo : cyclicRep 1 1 0 = 1 := by
  unfold cyclicRep pauli pauliY
  simp [Matrix.smul_apply, neg_mul, Complex.I_mul_I]

private theorem cyclicRep_one_ll : cyclicRep 1 1 1 = 0 := by
  unfold cyclicRep pauli pauliY
  simp [Matrix.smul_apply]

private theorem axis0_entry (θ : ℝ) :
    dualRotorMat (EuclideanSpace.single 0 θ) 0 0 = (Real.cos (θ / 2) : ℂ) ∧
      dualRotorMat (EuclideanSpace.single 0 θ) 0 1 =
        -Complex.I * (Real.sin (θ / 2) : ℂ) ∧
      dualRotorMat (EuclideanSpace.single 0 θ) 1 0 =
        -Complex.I * (Real.sin (θ / 2) : ℂ) ∧
      dualRotorMat (EuclideanSpace.single 0 θ) 1 1 = (Real.cos (θ / 2) : ℂ) := by
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

private theorem axis1_entry (θ : ℝ) :
    dualRotorMat (EuclideanSpace.single 1 θ) 0 0 = (Real.cos (θ / 2) : ℂ) ∧
      dualRotorMat (EuclideanSpace.single 1 θ) 0 1 = -((Real.sin (θ / 2) : ℂ)) ∧
      dualRotorMat (EuclideanSpace.single 1 θ) 1 0 = (Real.sin (θ / 2) : ℂ) ∧
      dualRotorMat (EuclideanSpace.single 1 θ) 1 1 = (Real.cos (θ / 2) : ℂ) := by
  have hR := dualRotorMat_axis1_rodrigues θ
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℂ => A 0 0) hR
    simpa [cyclicRep_one_oo, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply] using h
  · have h := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℂ => A 0 1) hR
    simpa [cyclicRep_one_ol, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply] using h
  · have h := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℂ => A 1 0) hR
    simpa [cyclicRep_one_lo, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply] using h
  · have h := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℂ => A 1 1) hR
    simpa [cyclicRep_one_ll, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply] using h

theorem perp_rotors_not_commute {θ : ℝ} (h0 : 0 < θ) (hθ : θ ≤ Real.pi) :
    dualRotorMat (EuclideanSpace.single 0 θ) *
        dualRotorMat (EuclideanSpace.single 1 θ) ≠
      dualRotorMat (EuclideanSpace.single 1 θ) *
        dualRotorMat (EuclideanSpace.single 0 θ) := by
  set c : ℝ := Real.cos (θ / 2)
  set s : ℝ := Real.sin (θ / 2)
  intro h
  have hU := axis0_entry θ
  have hV := axis1_entry θ
  have h00 := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℂ => A 0 0) h
  simp only [Matrix.mul_apply, Fin.sum_univ_two] at h00
  rw [hU.1, hU.2.1, hV.1, hV.2.1] at h00
  rw [hV.2.2.1, hU.2.2.1] at h00
  have hnamed : (c : ℂ) * c + -Complex.I * (s : ℂ) * (s : ℂ) =
      (c : ℂ) * c + -(s : ℂ) * (-Complex.I * (s : ℂ)) := by
    simpa [c, s] using h00
  have hsub := congrArg (fun z : ℂ => z - ((c : ℂ) * c + -(s : ℂ) * (-Complex.I * (s : ℂ)))) hnamed
  have hzero : (c : ℂ) * c + -Complex.I * (s : ℂ) * (s : ℂ) -
      ((c : ℂ) * c + -(s : ℂ) * (-Complex.I * (s : ℂ))) = 0 := by
    simpa using hsub
  have hfac : (c : ℂ) * c + -Complex.I * (s : ℂ) * (s : ℂ) -
      ((c : ℂ) * c + -(s : ℂ) * (-Complex.I * (s : ℂ))) =
        (-2 * Complex.I) * ((s : ℂ) * (s : ℂ)) := by ring
  have hprod : (-2 * Complex.I) * ((s : ℂ) * (s : ℂ)) = 0 := by
    rw [← hfac, hzero]
  have hs0 : (s : ℂ) * (s : ℂ) = 0 := by
    rcases mul_eq_zero.mp hprod with hcoe | hs0
    · exact absurd hcoe (by simp [Complex.I_ne_zero])
    · exact hs0
  have hs : (s : ℂ) ≠ 0 := by
    intro hs0
    have hhalf : 0 < θ / 2 := by linarith
    have hle : θ / 2 ≤ Real.pi / 2 := by linarith
    have hpos := Real.sin_pos_of_pos_of_lt_pi hhalf (by linarith [hle, Real.pi_pos])
    exact absurd (by simpa [s] using hs0) (Complex.ofReal_ne_zero.mpr (ne_of_gt hpos))
  exact absurd hs0 (mul_ne_zero hs hs)

theorem perp_gravitons_not_commute {N : ℕ} (hN : 3 ≤ N) :
    dualRotorMat (EuclideanSpace.single 0 (stepAngle N)) *
        dualRotorMat (EuclideanSpace.single 1 (stepAngle N)) ≠
      dualRotorMat (EuclideanSpace.single 1 (stepAngle N)) *
        dualRotorMat (EuclideanSpace.single 0 (stepAngle N)) := by
  have hpos : 0 < N := lt_of_lt_of_le (by decide : 0 < 3) hN
  have hθ : stepAngle N ≤ Real.pi := by
    unfold stepAngle
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hpos
    rw [div_le_iff₀ hN0]
    have h3 : (2 : ℝ) ≤ N := by exact_mod_cast (le_trans (by decide : (2 : ℕ) ≤ 3) hN)
    nlinarith [Real.pi_pos]
  exact perp_rotors_not_commute (stepAngle_pos hpos) hθ

theorem fullTurn_commute :
    dualRotorMat (EuclideanSpace.single 0 (2 * Real.pi)) = -1 ∧
      dualRotorMat (EuclideanSpace.single 1 (2 * Real.pi)) = -1 ∧
      dualRotorMat (EuclideanSpace.single 0 (2 * Real.pi)) *
          dualRotorMat (EuclideanSpace.single 1 (2 * Real.pi)) =
        dualRotorMat (EuclideanSpace.single 1 (2 * Real.pi)) *
          dualRotorMat (EuclideanSpace.single 0 (2 * Real.pi)) := by
  have h0 : dualRotorMat (EuclideanSpace.single 0 (2 * Real.pi)) = -1 := by
    rw [dualRotorMat_axis0_rodrigues]
    have hhalf : (2 * Real.pi) / 2 = Real.pi := by ring
    rw [hhalf, Real.cos_pi, Real.sin_pi]
    simp
  have h1 : dualRotorMat (EuclideanSpace.single 1 (2 * Real.pi)) = -1 := by
    rw [dualRotorMat_axis1_rodrigues]
    have hhalf : (2 * Real.pi) / 2 = Real.pi := by ring
    rw [hhalf, Real.cos_pi, Real.sin_pi]
    simp
  refine ⟨h0, h1, ?_⟩
  rw [h0, h1]

/-! ### A split across the three axes -/

/-- `n₀` gravitons on axis 0, `n₁` on axis 1, `n₂` on axis 2. -/
def occupation (n0 n1 n2 N : ℕ) : TorsionParams where
  alpha := fun
    | 0 => 0
    | 1 => 0
    | 2 => 0
  beta := fun
    | 0 => (n0 : ℝ) * stepAngle N
    | 1 => (n1 : ℝ) * stepAngle N
    | 2 => (n2 : ℝ) * stepAngle N

theorem J_occupation (n0 n1 n2 N : ℕ) :
    J (occupation n0 n1 n2 N) =
      -(((n0 : ℝ) ^ 2 + (n1 : ℝ) ^ 2 + (n2 : ℝ) ^ 2) * (stepAngle N) ^ 2) / 2 := by
  rw [J_coef]
  simp [occupation, Fin.sum_univ_three]
  ring

theorem occupation_sq {n0 n1 n2 N : ℕ} :
    JNormalized (occupation n0 n1 n2 N) =
      ((n0 : ℝ) ^ 2 + (n1 : ℝ) ^ 2 + (n2 : ℝ) ^ 2) * farHeight N := by
  unfold JNormalized farHeight
  rw [J_occupation]
  have hone : JNormalized (oneAxisDual (stepAngle N)) =
      (8 / (3 * Real.pi ^ 2)) * (-(stepAngle N ^ 2) / 2) := by
    unfold JNormalized
    rw [J_oneAxisDual]
  rw [hone]
  ring

theorem occupation_missing_cross {n0 n1 n2 N : ℕ} (hN : 0 < N) :
    JNormalized (alignedSteps (n0 + n1 + n2) N) =
      JNormalized (occupation n0 n1 n2 N) +
        (2 * ((n0 : ℝ) * n1 + (n0 : ℝ) * n2 + (n1 : ℝ) * n2)) * farHeight N := by
  rw [collective_square hN, occupation_sq]
  have hsum : ((n0 + n1 + n2 : ℕ) : ℝ) = (n0 : ℝ) + n1 + n2 := by norm_cast
  have hfar : JNormalized (oneAxisDual (stepAngle N)) = farHeight N := rfl
  rw [hsum, hfar]
  ring

theorem occupation_above_aligned {n0 n1 n2 N : ℕ} (hN : 0 < N)
    (hcross : 0 < n0 * n1 + n0 * n2 + n1 * n2) :
    JNormalized (alignedSteps (n0 + n1 + n2) N) <
      JNormalized (occupation n0 n1 n2 N) := by
  rw [occupation_missing_cross hN]
  have hpos : (0 : ℝ) < (n0 : ℝ) * n1 + (n0 : ℝ) * n2 + (n1 : ℝ) * n2 := by
    exact_mod_cast hcross
  have hneg := farHeight_neg hN
  have hprod : (2 * ((n0 : ℝ) * n1 + (n0 : ℝ) * n2 + (n1 : ℝ) * n2)) * farHeight N < 0 :=
    mul_neg_of_pos_of_neg (by positivity) hneg
  linarith

theorem occupation_admissible_legacy {n0 n1 n2 N : ℕ}
    (h0 : 4 * n0 ≤ N) (h1 : 4 * n1 ≤ N) (h2 : 4 * n2 ≤ N) :
    IsAdmissibleContinuousLegacy (occupation n0 n1 n2 N) := by
  have hβ {n : ℕ} (hn : 4 * n ≤ N) :
      0 ≤ (n : ℝ) * stepAngle N ∧ (n : ℝ) * stepAngle N ≤ Real.pi / 2 := by
    refine ⟨?_, alignedAngle_le_half_pi hn⟩
    exact mul_nonneg (Nat.cast_nonneg _) (stepAngle_nonneg N)
  intro a
  fin_cases a
  · simp only [occupation]
    exact ⟨le_rfl, (hβ h0).1, by simpa using (hβ h0).2⟩
  · simp only [occupation]
    exact ⟨le_rfl, (hβ h1).1, by simpa using (hβ h1).2⟩
  · simp only [occupation]
    exact ⟨le_rfl, (hβ h2).1, by simpa using (hβ h2).2⟩

theorem occupation_admissible {n0 n1 n2 N : ℕ}
    (h0 : 4 * n0 ≤ N) (h1 : 4 * n1 ≤ N) (h2 : 4 * n2 ≤ N) :
    IsAdmissibleContinuous (occupation n0 n1 n2 N) :=
  legacy_admissible_implies_mismatch _ (occupation_admissible_legacy h0 h1 h2)

theorem move_height_delta {n m k N : ℕ} (hn : 0 < n) (_hN : 0 < N) :
    JNormalized (occupation (n - 1) (m + 1) k N) -
        JNormalized (occupation n m k N) =
      (2 * ((m : ℝ) + 1 - n)) * farHeight N := by
  rw [occupation_sq, occupation_sq]
  have hn' : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (Nat.succ_le_of_lt hn)]
    simp
  have hm' : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by norm_cast
  rw [hn', hm']
  ring

theorem move_to_thinner_raises {n m k N : ℕ} (hn : 0 < n) (hN : 0 < N)
    (hthin : m + 1 < n) :
    JNormalized (occupation n m k N) <
      JNormalized (occupation (n - 1) (m + 1) k N) := by
  have hδ := move_height_delta (n := n) (m := m) (k := k) hn hN
  have hcoef : (m : ℝ) + 1 - (n : ℝ) < 0 := by
    have hm : (m : ℝ) + 1 < (n : ℝ) := by exact_mod_cast hthin
    linarith
  have hneg := farHeight_neg hN
  have hprod : (2 * ((m : ℝ) + 1 - (n : ℝ))) * farHeight N > 0 :=
    mul_pos_of_neg_of_neg (by nlinarith) hneg
  linarith

theorem move_to_fuller_lowers {n m k N : ℕ} (hn : 0 < n) (hN : 0 < N)
    (hfull : n ≤ m) :
    JNormalized (occupation (n - 1) (m + 1) k N) <
      JNormalized (occupation n m k N) := by
  have hδ := move_height_delta (n := n) (m := m) (k := k) hn hN
  have hcoef : (0 : ℝ) < (m : ℝ) + 1 - (n : ℝ) := by
    have hm : (n : ℝ) < (m : ℝ) + 1 := by exact_mod_cast (Nat.lt_succ_of_le hfull)
    linarith
  have hneg := farHeight_neg hN
  have hprod : (2 * ((m : ℝ) + 1 - (n : ℝ))) * farHeight N < 0 :=
    mul_neg_of_pos_of_neg (by nlinarith) hneg
  linarith

theorem move_balances {n m k N : ℕ} (hn : 0 < n) (hN : 0 < N) (heq : n = m + 1) :
    JNormalized (occupation (n - 1) (m + 1) k N) =
      JNormalized (occupation n m k N) := by
  have hδ := move_height_delta (n := n) (m := m) (k := k) hn hN
  have hcoef : (m : ℝ) + 1 - (n : ℝ) = 0 := by
    have hn' : (n : ℝ) = (m : ℝ) + 1 := by exact_mod_cast heq
    linarith
  rw [hcoef] at hδ
  simp only [mul_zero, zero_mul] at hδ
  linarith

/-! ### The expressed foot of a census -/

theorem pureDual_foot {θ : ℝ} (hθ : 0 ≤ θ) :
    (axisExpress 0 θ).1 = 0 ∧
      ((θ ≤ Real.pi / 2 ∧ (axisExpress 0 θ).2 = θ) ∨
        (Real.pi / 2 < θ ∧ (axisExpress 0 θ).2 = Real.pi / 2)) := by
  by_cases hle : θ ≤ Real.pi / 2
  · have ht : InTriangle 0 θ := ⟨le_rfl, hθ, by simpa [zero_add] using hle⟩
    have hax := axisExpress_triangle ht
    refine ⟨?_, Or.inl ⟨hle, ?_⟩⟩
    · simpa using congrArg Prod.fst hax
    · simpa using congrArg Prod.snd hax
  · have hgt : Real.pi / 2 < θ := lt_of_not_ge hle
    have hpure : InPureDual 0 θ := ⟨hgt.le, by linarith⟩
    have hax := axisExpress_pureDual hpure
    refine ⟨?_, Or.inr ⟨hgt, ?_⟩⟩
    · simpa using congrArg Prod.fst hax
    · simpa using congrArg Prod.snd hax

theorem J_expressedOneAxis {θ : ℝ} (hθ : 0 ≤ θ) :
    J (expressedOneAxis θ) = -((axisExpress 0 θ).2 ^ 2) / 2 := by
  have hα := (pureDual_foot hθ).1
  rw [J_coef]
  simp only [expressedOneAxis, Fin.sum_univ_three, hα]
  ring

theorem J_express_occupation (n0 n1 n2 N : ℕ) :
    J (express (occupation n0 n1 n2 N)) =
      J (expressedOneAxis ((n0 : ℝ) * stepAngle N)) +
      J (expressedOneAxis ((n1 : ℝ) * stepAngle N)) +
      J (expressedOneAxis ((n2 : ℝ) * stepAngle N)) := by
  set θ0 : ℝ := (n0 : ℝ) * stepAngle N
  set θ1 : ℝ := (n1 : ℝ) * stepAngle N
  set θ2 : ℝ := (n2 : ℝ) * stepAngle N
  have h0 : 0 ≤ θ0 := mul_nonneg (Nat.cast_nonneg _) (stepAngle_nonneg N)
  have h1 : 0 ≤ θ1 := mul_nonneg (Nat.cast_nonneg _) (stepAngle_nonneg N)
  have h2 : 0 ≤ θ2 := mul_nonneg (Nat.cast_nonneg _) (stepAngle_nonneg N)
  rw [J_expressedOneAxis h0, J_expressedOneAxis h1, J_expressedOneAxis h2]
  have ha0 : (axisExpress 0 θ0).1 = 0 := (pureDual_foot h0).1
  have ha1 : (axisExpress 0 θ1).1 = 0 := (pureDual_foot h1).1
  have ha2 : (axisExpress 0 θ2).1 = 0 := (pureDual_foot h2).1
  rw [J_coef]
  simp only [express, occupation, Fin.sum_univ_three]
  rw [ha0, ha1, ha2]
  ring

theorem expressed_occupation_sum (n0 n1 n2 N : ℕ) :
    JNormalized (express (occupation n0 n1 n2 N)) =
      JNormalized (express (alignedSteps n0 N)) +
      JNormalized (express (alignedSteps n1 N)) +
      JNormalized (express (alignedSteps n2 N)) := by
  unfold JNormalized
  rw [J_express_occupation, express_aligned, express_aligned, express_aligned]
  ring

theorem express_empty (N : ℕ) :
    JNormalized (express (alignedSteps 0 N)) = 0 := by
  rw [express_eq_of_admissible (collective_admissible_legacy (n := 0) (Nat.zero_le N))]
  simp [alignedSteps, JNormalized_oneAxisDual]

theorem expressed_two_locks {n0 n1 N : ℕ} (hN : 0 < N)
    (h0 : N ≤ 4 * n0) (h1 : N ≤ 4 * n1) :
    JNormalized (express (occupation n0 n1 0 N)) = -((2 : ℝ) / 3) := by
  rw [expressed_occupation_sum, express_aligned, express_aligned, express_empty]
  rw [collective_locks hN h0, collective_locks hN h1]
  norm_num

theorem expressed_three_locks {n0 n1 n2 N : ℕ} (hN : 0 < N)
    (h0 : N ≤ 4 * n0) (h1 : N ≤ 4 * n1) (h2 : N ≤ 4 * n2) :
    JNormalized (express (occupation n0 n1 n2 N)) = -1 := by
  rw [expressed_occupation_sum, express_aligned, express_aligned, express_aligned]
  rw [collective_locks hN h0, collective_locks hN h1, collective_locks hN h2]
  norm_num

theorem expressed_floor_stable {n0 n1 n2 m0 m1 m2 N : ℕ} (hN : 0 < N)
    (h0 : N ≤ 4 * n0) (h1 : N ≤ 4 * n1) (h2 : N ≤ 4 * n2)
    (hm0 : n0 ≤ m0) (hm1 : n1 ≤ m1) (hm2 : n2 ≤ m2) :
    JNormalized (express (occupation m0 m1 m2 N)) = -1 := by
  have h0' : N ≤ 4 * m0 := le_trans h0 (Nat.mul_le_mul_left 4 hm0)
  have h1' : N ≤ 4 * m1 := le_trans h1 (Nat.mul_le_mul_left 4 hm1)
  have h2' : N ≤ 4 * m2 := le_trans h2 (Nat.mul_le_mul_left 4 hm2)
  exact expressed_three_locks hN h0' h1' h2'

theorem equal_split_floor {n : ℕ} (hn : 0 < n) :
    JNormalized (express (occupation n n n (4 * n))) = -1 := by
  have hN : 0 < 4 * n := Nat.mul_pos (by decide : 0 < 4) hn
  exact expressed_three_locks hN le_rfl le_rfl le_rfl

theorem expressed_occupation_squares {n0 n1 n2 N : ℕ}
    (h0 : 4 * n0 ≤ N) (h1 : 4 * n1 ≤ N) (h2 : 4 * n2 ≤ N) :
    JNormalized (express (occupation n0 n1 n2 N)) =
      ((n0 : ℝ) ^ 2 + (n1 : ℝ) ^ 2 + (n2 : ℝ) ^ 2) * farHeight N := by
  rw [express_eq_of_admissible (occupation_admissible_legacy h0 h1 h2), occupation_sq]

theorem expressed_lock_plus {n0 n1 n2 N : ℕ} (hN : 0 < N)
    (h0 : N ≤ 4 * n0) (h1 : 4 * n1 ≤ N) (h2 : 4 * n2 ≤ N) :
    JNormalized (express (occupation n0 n1 n2 N)) =
      -((1 : ℝ) / 3) + ((n1 : ℝ) ^ 2 + (n2 : ℝ) ^ 2) * farHeight N := by
  have ha : JNormalized (express (alignedSteps n0 N)) = -((1 : ℝ) / 3) := by
    rw [express_aligned]
    exact collective_locks hN h0
  have hb : JNormalized (express (alignedSteps n1 N)) = (n1 : ℝ) ^ 2 * farHeight N := by
    rw [express_eq_of_admissible (collective_admissible_legacy h1), collective_square hN]
    rfl
  have hc : JNormalized (express (alignedSteps n2 N)) = (n2 : ℝ) ^ 2 * farHeight N := by
    rw [express_eq_of_admissible (collective_admissible_legacy h2), collective_square hN]
    rfl
  rw [expressed_occupation_sum, ha, hb, hc]
  ring

theorem spread_past_wall {n0 n1 N : ℕ} (hN : 0 < N)
    (h0 : N ≤ 4 * n0) (h1 : 4 * n1 ≤ N) (hn1 : 0 < n1) :
    JNormalized (express (occupation n0 n1 0 N)) =
      -((1 : ℝ) / 3) + ((n1 : ℝ) ^ 2) * farHeight N ∧
      JNormalized (express (occupation n0 n1 0 N)) <
        JNormalized (express (alignedSteps (n0 + n1) N)) ∧
      JNormalized (express (alignedSteps (n0 + n1) N)) = -((1 : ℝ) / 3) := by
  have hwall : N ≤ 4 * (n0 + n1) := le_trans h0 (Nat.mul_le_mul_left 4 (Nat.le_add_right n0 n1))
  have hlock : JNormalized (express (alignedSteps (n0 + n1) N)) = -((1 : ℝ) / 3) := by
    rw [express_aligned]
    exact collective_locks hN hwall
  have hraw := expressed_lock_plus (n2 := 0) hN h0 h1 (Nat.zero_le N)
  have hsum : JNormalized (express (occupation n0 n1 0 N)) =
      -((1 : ℝ) / 3) + ((n1 : ℝ) ^ 2) * farHeight N := by
    rw [hraw]
    ring
  refine ⟨hsum, ?_, hlock⟩
  rw [hsum, hlock]
  have hsq : (0 : ℝ) < (n1 : ℝ) ^ 2 := by
    have hpos : (0 : ℝ) < n1 := by exact_mod_cast hn1
    positivity
  have hneg := farHeight_neg hN
  nlinarith [mul_neg_of_pos_of_neg hsq hneg]

theorem expressed_aligned_lowest {n0 n1 n2 N : ℕ}
    (hsum : 4 * (n0 + n1 + n2) ≤ N)
    (hcross : 0 < n0 * n1 + n0 * n2 + n1 * n2) :
    JNormalized (express (alignedSteps (n0 + n1 + n2) N)) <
      JNormalized (express (occupation n0 n1 n2 N)) := by
  have htwo : 2 ≤ n0 + n1 + n2 := by
    rcases Nat.eq_zero_or_pos n0 with hn0 | hn0
    · rcases Nat.eq_zero_or_pos n1 with hn1 | hn1
      · simp [hn0, hn1] at hcross
      · rcases Nat.eq_zero_or_pos n2 with hn2 | hn2
        · simp [hn0, hn2] at hcross
        · omega
    · rcases Nat.eq_zero_or_pos n1 with hn1 | hn1
      · rcases Nat.eq_zero_or_pos n2 with hn2 | hn2
        · simp [hn1, hn2] at hcross
        · omega
      · omega
  have hN : 0 < N := by
    have h8 : 8 ≤ 4 * (n0 + n1 + n2) := by omega
    exact lt_of_lt_of_le (by decide : (0 : ℕ) < 8) (le_trans h8 hsum)
  have h0 : 4 * n0 ≤ N := by
    have hle : n0 ≤ n0 + n1 + n2 := by omega
    exact le_trans (Nat.mul_le_mul_left 4 hle) hsum
  have h1 : 4 * n1 ≤ N := by
    have hle : n1 ≤ n0 + n1 + n2 := by omega
    exact le_trans (Nat.mul_le_mul_left 4 hle) hsum
  have h2 : 4 * n2 ≤ N := by
    have hle : n2 ≤ n0 + n1 + n2 := by omega
    exact le_trans (Nat.mul_le_mul_left 4 hle) hsum
  rw [express_eq_of_admissible (collective_admissible_legacy hsum),
    express_eq_of_admissible (occupation_admissible_legacy h0 h1 h2)]
  exact occupation_above_aligned hN hcross

theorem equal_vs_aligned {n N : ℕ} (hn : 0 < n) (h : 12 * n ≤ N) :
    JNormalized (express (alignedSteps (3 * n) N)) = (9 * (n : ℝ) ^ 2) * farHeight N ∧
      JNormalized (express (occupation n n n N)) = (3 * (n : ℝ) ^ 2) * farHeight N ∧
      JNormalized (express (alignedSteps (3 * n) N)) =
        JNormalized (express (occupation n n n N)) + (6 * (n : ℝ) ^ 2) * farHeight N ∧
      JNormalized (express (alignedSteps (3 * n) N)) <
        JNormalized (express (occupation n n n N)) := by
  have hN : 0 < N := lt_of_lt_of_le (Nat.mul_pos (by decide : 0 < 12) hn) h
  have hcone : 4 * n ≤ N := by
    have h4 : 4 * n ≤ 12 * n := by omega
    exact le_trans h4 h
  have hthree : 4 * (3 * n) ≤ N := by simpa [show 4 * (3 * n) = 12 * n by omega] using h
  have halign : JNormalized (express (alignedSteps (3 * n) N)) =
      (9 * (n : ℝ) ^ 2) * farHeight N := by
    rw [express_eq_of_admissible (collective_admissible_legacy hthree), collective_square hN]
    have hcast : ((3 * n : ℕ) : ℝ) = 3 * (n : ℝ) := by norm_cast
    rw [hcast]
    unfold farHeight
    ring
  have hequal : JNormalized (express (occupation n n n N)) =
      (3 * (n : ℝ) ^ 2) * farHeight N := by
    rw [expressed_occupation_squares hcone hcone hcone]
    ring
  refine ⟨halign, hequal, ?_, ?_⟩
  · rw [halign, hequal]
    ring
  · rw [halign, hequal]
    have hneg := farHeight_neg hN
    have hsq : (0 : ℝ) < (n : ℝ) ^ 2 := by
      have hpos : (0 : ℝ) < n := by exact_mod_cast hn
      positivity
    nlinarith [mul_neg_of_pos_of_neg hsq hneg]

theorem expressed_move_raises {n m k N : ℕ} (hn : 0 < n) (hN : 0 < N)
    (hthin : m + 1 < n) (h0 : 4 * n ≤ N) (h1 : 4 * (m + 1) ≤ N) (hk : 4 * k ≤ N) :
    JNormalized (express (occupation n m k N)) <
      JNormalized (express (occupation (n - 1) (m + 1) k N)) := by
  have hm : 4 * m ≤ N := le_trans (Nat.mul_le_mul_left 4 (Nat.le_succ m)) h1
  have hsrc : 4 * (n - 1) ≤ N := le_trans (Nat.mul_le_mul_left 4 (Nat.sub_le n 1)) h0
  rw [express_eq_of_admissible (occupation_admissible_legacy h0 hm hk),
    express_eq_of_admissible (occupation_admissible_legacy hsrc h1 hk)]
  exact move_to_thinner_raises hn hN hthin

theorem expressed_move_lowers {n m k N : ℕ} (hn : 0 < n) (hN : 0 < N)
    (hfull : n ≤ m) (h0 : 4 * n ≤ N) (h1 : 4 * (m + 1) ≤ N) (hk : 4 * k ≤ N) :
    JNormalized (express (occupation (n - 1) (m + 1) k N)) <
      JNormalized (express (occupation n m k N)) := by
  have hm : 4 * m ≤ N := le_trans (Nat.mul_le_mul_left 4 (Nat.le_succ m)) h1
  have hsrc : 4 * (n - 1) ≤ N := le_trans (Nat.mul_le_mul_left 4 (Nat.sub_le n 1)) h0
  rw [express_eq_of_admissible (occupation_admissible_legacy hsrc h1 hk),
    express_eq_of_admissible (occupation_admissible_legacy h0 hm hk)]
  exact move_to_fuller_lowers hn hN hfull

theorem expressed_move_balances {n m k N : ℕ} (hn : 0 < n) (hN : 0 < N)
    (heq : n = m + 1) (h0 : 4 * n ≤ N) (hk : 4 * k ≤ N) :
    JNormalized (express (occupation (n - 1) (m + 1) k N)) =
      JNormalized (express (occupation n m k N)) := by
  have hm : 4 * m ≤ N := by
    have hle : m ≤ n := by omega
    exact le_trans (Nat.mul_le_mul_left 4 hle) h0
  have hdest : 4 * (m + 1) ≤ N := by simpa [heq] using h0
  have hsrc : 4 * (n - 1) ≤ N := le_trans (Nat.mul_le_mul_left 4 (Nat.sub_le n 1)) h0
  rw [express_eq_of_admissible (occupation_admissible_legacy hsrc hdest hk),
    express_eq_of_admissible (occupation_admissible_legacy h0 hm hk)]
  exact move_balances hn hN heq

/-! ### The same aligned steps, read on a spinor -/

private theorem sin_step_lt {k : ℕ} {x : ℝ} (hk : 1 ≤ k) (hx : 0 < x)
    (hbound : ((k + 1 : ℕ) : ℝ) * x ≤ Real.pi)
    (ih : Real.sin ((k : ℝ) * x) ≤ (k : ℝ) * Real.sin x) :
    Real.sin (((k + 1 : ℕ) : ℝ) * x) < ((k + 1 : ℕ) : ℝ) * Real.sin x := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hxpi : x < Real.pi := by
    have hpos : (0 : ℝ) < (k + 1 : ℕ) := by exact_mod_cast (Nat.succ_pos k)
    have hstep : x ≤ Real.pi / (k + 1 : ℕ) := by
      rw [le_div_iff₀ hpos]
      simpa [mul_comm] using hbound
    exact lt_of_le_of_lt hstep (div_lt_self Real.pi_pos (by exact_mod_cast Nat.succ_le_succ hk))
  have hcos : Real.cos x < 1 := by
    have hlt : Real.cos x < Real.cos 0 :=
      Real.cos_lt_cos_of_nonneg_of_le_pi (le_refl 0) (by linarith) hx
    simpa [Real.cos_zero] using hlt
  have hkAngle : 0 < (k : ℝ) * x := mul_pos hk0 hx
  have hklt : (k : ℝ) * x < Real.pi := by
    have hcoe : (k : ℝ) < (k + 1 : ℕ) := by exact_mod_cast (Nat.lt_succ_self k)
    have hmul : (k : ℝ) * x < ((k + 1 : ℕ) : ℝ) * x :=
      mul_lt_mul_of_pos_right hcoe hx
    exact lt_of_lt_of_le hmul hbound
  have hsinK : 0 < Real.sin ((k : ℝ) * x) :=
    Real.sin_pos_of_pos_of_lt_pi hkAngle hklt
  have hprod : Real.sin ((k : ℝ) * x) * Real.cos x < Real.sin ((k : ℝ) * x) := by
    have hlt := mul_lt_mul_of_pos_left hcos hsinK
    simpa [mul_one] using hlt
  have hsinx : 0 < Real.sin x :=
    Real.sin_pos_of_pos_of_lt_pi hx (by linarith)
  have hcosK : Real.cos ((k : ℝ) * x) * Real.sin x ≤ Real.sin x := by
    have hle : Real.cos ((k : ℝ) * x) ≤ 1 := Real.cos_le_one _
    have hmul := mul_le_mul_of_nonneg_right hle hsinx.le
    simpa [one_mul] using hmul
  have hadd : ((k + 1 : ℕ) : ℝ) * x = (k : ℝ) * x + x := by
    have h1 : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by norm_cast
    rw [h1]
    ring
  have hsin : Real.sin (((k + 1 : ℕ) : ℝ) * x) =
      Real.sin ((k : ℝ) * x) * Real.cos x + Real.cos ((k : ℝ) * x) * Real.sin x := by
    rw [hadd, Real.sin_add]
  have hlt : Real.sin (((k + 1 : ℕ) : ℝ) * x) < Real.sin ((k : ℝ) * x) + Real.sin x := by
    rw [hsin]
    linarith [hprod, hcosK]
  have hright : Real.sin ((k : ℝ) * x) + Real.sin x ≤ ((k + 1 : ℕ) : ℝ) * Real.sin x := by
    have h1 : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by norm_cast
    rw [h1]
    linarith [ih]
  linarith

private theorem sin_mul_nat_le {n : ℕ} {x : ℝ} (hx : 0 ≤ x)
    (hbound : (n : ℝ) * x ≤ Real.pi) :
    Real.sin ((n : ℝ) * x) ≤ (n : ℝ) * Real.sin x := by
  induction n with
  | zero => simp
  | succ n ih =>
    cases n with
    | zero =>
      simp [one_mul]
    | succ n =>
      by_cases hx0 : x = 0
      · simp [hx0]
      · have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
        have hprev : ((n + 1 : ℕ) : ℝ) * x ≤ Real.pi := by
          have hcoe : ((n + 1 : ℕ) : ℝ) ≤ ((n + 2 : ℕ) : ℝ) := by exact_mod_cast (by omega)
          exact (mul_le_mul_of_nonneg_right hcoe hx).trans hbound
        have hih := ih hprev
        exact (sin_step_lt (k := n + 1) (by omega) hxpos hbound hih).le

private theorem sin_mul_nat_lt {n : ℕ} {x : ℝ} (hn : 2 ≤ n) (hx : 0 < x)
    (hbound : (n : ℝ) * x ≤ Real.pi) :
    Real.sin ((n : ℝ) * x) < (n : ℝ) * Real.sin x := by
  have hpred : 1 ≤ n - 1 := by omega
  have hprev : ((n - 1 : ℕ) : ℝ) * x ≤ Real.pi := by
    have hcoe : ((n - 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Nat.sub_le n 1)
    exact (mul_le_mul_of_nonneg_right hcoe hx.le).trans hbound
  have hih : Real.sin (((n - 1 : ℕ) : ℝ) * x) ≤ ((n - 1 : ℕ) : ℝ) * Real.sin x :=
    sin_mul_nat_le hx.le hprev
  have hk : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]
    simp
  have hstep := sin_step_lt (k := n - 1) hpred hx ?_ ?_
  · have hcast : ((n - 1 + 1 : ℕ) : ℝ) = (n : ℝ) := by
      have h1 : n - 1 + 1 = n := by omega
      rw [h1]
    simpa [hcast] using hstep
  · simpa [Nat.sub_add_cancel (by omega : 1 ≤ n)] using hbound
  · simpa [hk] using hih

private theorem axis0_single_smul (s θ : ℝ) :
    s • (EuclideanSpace.single (0 : Fin 3) θ : DualRapidity) =
      EuclideanSpace.single 0 (s * θ) := by
  ext i
  fin_cases i <;> simp

theorem aligned_rotors_add (θ φ : ℝ) :
    dualRotorMat (EuclideanSpace.single 0 θ) * dualRotorMat (EuclideanSpace.single 0 φ) =
      dualRotorMat (EuclideanSpace.single 0 (θ + φ)) := by
  have hθ : θ • (EuclideanSpace.single (0 : Fin 3) 1 : DualRapidity) =
      EuclideanSpace.single 0 θ := by
    simpa using axis0_single_smul θ 1
  have hφ : φ • (EuclideanSpace.single (0 : Fin 3) 1 : DualRapidity) =
      EuclideanSpace.single 0 φ := by
    simpa using axis0_single_smul φ 1
  have hsum : (θ + φ) • (EuclideanSpace.single (0 : Fin 3) 1 : DualRapidity) =
      EuclideanSpace.single 0 (θ + φ) := by
    simpa [add_mul] using axis0_single_smul (θ + φ) 1
  rw [← hθ, ← hφ, ← hsum]
  exact (dualRotorMat_ray_add θ φ (EuclideanSpace.single (0 : Fin 3) 1)).symm

theorem aligned_rotors_commute (θ φ : ℝ) :
    dualRotorMat (EuclideanSpace.single 0 θ) * dualRotorMat (EuclideanSpace.single 0 φ) =
      dualRotorMat (EuclideanSpace.single 0 φ) * dualRotorMat (EuclideanSpace.single 0 θ) := by
  rw [aligned_rotors_add, aligned_rotors_add, add_comm]

theorem aligned_transverse_weight {n N : ℕ} (hn : 0 < n) (hN : 0 < N) :
    computationalWeight
        (applyMat (dualRotorMat (EuclideanSpace.single 0 ((n : ℝ) * stepAngle N))) spinUp) =
      Real.cos ((n : ℝ) * Real.pi / N) ^ 2 := by
  rw [computationalWeight_eq_cos_sq (mul_pos (by exact_mod_cast hn) (stepAngle_pos hN))]
  congr 1
  congr 1
  have hhalf : (n : ℝ) * stepAngle N / 2 = (n : ℝ) * (stepAngle N / 2) := by ring
  rw [hhalf, stepAngle_half hN]
  ring

theorem aligned_transverse_defect {n N : ℕ} (hn : 0 < n) (hN : 0 < N) :
    1 - computationalWeight
        (applyMat (dualRotorMat (EuclideanSpace.single 0 ((n : ℝ) * stepAngle N))) spinUp) =
      Real.sin ((n : ℝ) * Real.pi / N) ^ 2 := by
  rw [aligned_transverse_weight hn hN]
  have h := Real.cos_sq_add_sin_sq ((n : ℝ) * Real.pi / N)
  linarith

theorem aligned_defect_below_square {n N : ℕ} (hn : 2 ≤ n) (hN : n < N) :
    1 - computationalWeight
        (applyMat (dualRotorMat (EuclideanSpace.single 0 ((n : ℝ) * stepAngle N))) spinUp) <
      (n : ℝ) ^ 2 * (1 - computationalWeight
        (applyMat (dualRotorMat (EuclideanSpace.single 0 (stepAngle N))) spinUp)) := by
  have hpos : 0 < N := lt_trans (by decide : (0 : ℕ) < 2) (lt_of_le_of_lt hn hN)
  have hnpos : 0 < n := lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hn
  rw [aligned_transverse_defect hnpos hpos, transverseStep_defect hpos]
  set x : ℝ := Real.pi / (N : ℝ)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hpos
  have hx : 0 < x := div_pos Real.pi_pos hN0
  have hbound : (n : ℝ) * x ≤ Real.pi := by
    have hle : (n : ℝ) ≤ N := by exact_mod_cast le_of_lt hN
    have hxeq : (n : ℝ) * x = (n : ℝ) / N * Real.pi := by
      unfold x
      ring
    rw [hxeq]
    have hdiv : (n : ℝ) / N ≤ 1 := by
      rw [div_le_one hN0]
      exact hle
    have hmul := mul_le_mul_of_nonneg_right hdiv Real.pi_pos.le
    simpa [one_mul] using hmul
  have hsin := sin_mul_nat_lt hn hx hbound
  have hsinx : 0 < Real.sin x := by
    refine Real.sin_pos_of_pos_of_lt_pi hx ?_
    have h2 : (2 : ℝ) ≤ N := by exact_mod_cast (le_trans hn (le_of_lt hN))
    unfold x
    rw [div_lt_iff₀ hN0]
    nlinarith [Real.pi_pos, h2]
  have hleft : 0 ≤ Real.sin ((n : ℝ) * x) := by
    have hangle : 0 ≤ (n : ℝ) * x := mul_nonneg (by exact_mod_cast hnpos.le) hx.le
    have hltpi : (n : ℝ) * x < Real.pi := by
      have hlt : (n : ℝ) < N := by exact_mod_cast hN
      have hxeq : (n : ℝ) * x = (n : ℝ) / N * Real.pi := by unfold x; ring
      rw [hxeq]
      have hdiv : (n : ℝ) / N < 1 := (div_lt_one hN0).mpr hlt
      have hmul := mul_lt_mul_of_pos_right hdiv Real.pi_pos
      simpa [one_mul] using hmul
    exact (Real.sin_pos_of_pos_of_lt_pi (mul_pos (by exact_mod_cast hnpos) hx) hltpi).le
  have hright0 : 0 ≤ (n : ℝ) * Real.sin x := mul_nonneg (by exact_mod_cast hnpos.le) hsinx.le
  have hsq := (sq_lt_sq₀ hleft hright0).mpr hsin
  have hform : ((n : ℝ) * Real.sin x) ^ 2 = (n : ℝ) ^ 2 * Real.sin x ^ 2 := by ring
  rw [hform] at hsq
  have hxeq : (n : ℝ) * Real.pi / N = (n : ℝ) * x := by
    unfold x
    ring
  simpa [hxeq] using hsq

theorem fullCount_restores {N : ℕ} (hN : 0 < N) :
    (N : ℝ) * stepAngle N = 2 * Real.pi ∧
      dualRotorMat (EuclideanSpace.single 0 ((N : ℝ) * stepAngle N)) = -1 ∧
      computationalWeight
        (applyMat (dualRotorMat (EuclideanSpace.single 0 ((N : ℝ) * stepAngle N))) spinUp) = 1 ∧
      1 - computationalWeight
        (applyMat (dualRotorMat (EuclideanSpace.single 0 ((N : ℝ) * stepAngle N))) spinUp) = 0 := by
  have hangle : (N : ℝ) * stepAngle N = 2 * Real.pi := by
    unfold stepAngle
    field_simp
  refine ⟨hangle, ?_, ?_, ?_⟩
  · rw [hangle, dualRotorMat_axis0_rodrigues]
    have hhalf : (2 * Real.pi) / 2 = Real.pi := by ring
    rw [hhalf, Real.cos_pi, Real.sin_pi]
    simp
  · have hpos : 0 < (N : ℝ) * stepAngle N :=
      mul_pos (by exact_mod_cast hN) (stepAngle_pos hN)
    rw [computationalWeight_eq_cos_sq hpos, hangle]
    have hhalf : (2 * Real.pi) / 2 = Real.pi := by ring
    rw [hhalf, Real.cos_pi]
    norm_num
  · have hweight : computationalWeight
        (applyMat (dualRotorMat (EuclideanSpace.single 0 ((N : ℝ) * stepAngle N))) spinUp) = 1 := by
      have hpos : 0 < (N : ℝ) * stepAngle N :=
        mul_pos (by exact_mod_cast hN) (stepAngle_pos hN)
      rw [computationalWeight_eq_cos_sq hpos, hangle]
      have hhalf : (2 * Real.pi) / 2 = Real.pi := by ring
      rw [hhalf, Real.cos_pi]
      norm_num
    linarith [hweight]

theorem height_square_defect_below {n N : ℕ} (hn : 2 ≤ n) (hcone : 4 * n ≤ N) :
    JNormalized (express (alignedSteps n N)) = (n : ℝ) ^ 2 * farHeight N ∧
      1 - computationalWeight
          (applyMat (dualRotorMat (EuclideanSpace.single 0 ((n : ℝ) * stepAngle N))) spinUp) <
        (n : ℝ) ^ 2 *
          (1 - computationalWeight
            (applyMat (dualRotorMat (EuclideanSpace.single 0 (stepAngle N))) spinUp)) := by
  have hpos : 0 < N := by
    have h8 : (8 : ℕ) ≤ 4 * n := by omega
    exact lt_of_lt_of_le (by decide : (0 : ℕ) < 8) (le_trans h8 hcone)
  have hlt : n < N := by omega
  refine ⟨?_, aligned_defect_below_square hn hlt⟩
  rw [express_eq_of_admissible (collective_admissible_legacy hcone), collective_square hpos]
  rfl

theorem full_turn_locks {N : ℕ} (hN : 0 < N) :
    dualRotorMat (EuclideanSpace.single 0 ((N : ℝ) * stepAngle N)) = -1 ∧
      computationalWeight
          (applyMat (dualRotorMat (EuclideanSpace.single 0 ((N : ℝ) * stepAngle N))) spinUp) =
        1 ∧
      1 - computationalWeight
          (applyMat (dualRotorMat (EuclideanSpace.single 0 ((N : ℝ) * stepAngle N))) spinUp) =
        0 ∧
      JNormalized (express (alignedSteps N N)) = -((1 : ℝ) / 3) := by
  have hfull := fullCount_restores hN
  have hwall : N ≤ 4 * N := by
    have hmul : 1 * N ≤ 4 * N := Nat.mul_le_mul_right N (by decide : 1 ≤ 4)
    simpa using hmul
  refine ⟨hfull.2.1, hfull.2.2.1, hfull.2.2.2, ?_⟩
  rw [express_aligned]
  exact collective_locks hN hwall

/-! ### Past the lock the carrier keeps turning -/

theorem quarterTurn_angle {N : ℕ} (hdiv : 4 ∣ N) (hN : 0 < N) :
    ((N / 4 : ℕ) : ℝ) * stepAngle N = Real.pi / 2 := by
  have h4 : (N : ℝ) = 4 * ((N / 4 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.mul_div_cancel' hdiv).symm
  have hNz : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_iff_ne_zero.mp hN)
  have hmul : ((N / 4 : ℕ) : ℝ) * (2 * Real.pi) = (Real.pi / 2) * N := by
    rw [h4]
    ring
  have hdiv' : ((N / 4 : ℕ) : ℝ) * (2 * Real.pi) / N = Real.pi / 2 := by
    rw [div_eq_iff hNz]
    exact hmul
  simpa [stepAngle, mul_div_assoc] using hdiv'

theorem halfTurn_angle {N : ℕ} (hdiv : 4 ∣ N) (hN : 0 < N) :
    ((N / 2 : ℕ) : ℝ) * stepAngle N = Real.pi := by
  have h2dvd : 2 ∣ N := dvd_trans (by decide : 2 ∣ 4) hdiv
  have h2 : (N : ℝ) = 2 * ((N / 2 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.mul_div_cancel' h2dvd).symm
  have hNz : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_iff_ne_zero.mp hN)
  have hmul : ((N / 2 : ℕ) : ℝ) * (2 * Real.pi) = Real.pi * N := by
    rw [h2]
    ring
  have hdiv' : ((N / 2 : ℕ) : ℝ) * (2 * Real.pi) / N = Real.pi := by
    rw [div_eq_iff hNz]
    exact hmul
  simpa [stepAngle, mul_div_assoc] using hdiv'

theorem threeQuarterTurn_angle {N : ℕ} (hdiv : 4 ∣ N) (hN : 0 < N) :
    ((3 * (N / 4) : ℕ) : ℝ) * stepAngle N = 3 * Real.pi / 2 := by
  have hcoe : ((3 * (N / 4) : ℕ) : ℝ) = 3 * ((N / 4 : ℕ) : ℝ) := by norm_cast
  rw [hcoe, mul_assoc, quarterTurn_angle hdiv hN]
  ring_nf

private theorem countHalfAngle {n N : ℕ} (hN : 0 < N) :
    (n : ℝ) * Real.pi / N = (n : ℝ) * stepAngle N / 2 := by
  unfold stepAngle
  have hNz : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_iff_ne_zero.mp hN)
  field_simp [hNz]

private theorem quarterCount_pos {N : ℕ} (hdiv : 4 ∣ N) (hN : 4 ≤ N) :
    0 < N / 4 := by
  have hmul : 4 * (N / 4) = N := Nat.mul_div_cancel' hdiv
  have h1 : 4 * 1 ≤ 4 * (N / 4) := by
    rw [hmul]
    exact hN
  exact Nat.succ_le_iff.mp (Nat.le_of_mul_le_mul_left h1 (by decide : 0 < 4))

private theorem half_of_quarter {N : ℕ} (hdiv : 4 ∣ N) :
    N / 2 = 2 * (N / 4) := by
  have h2dvd : 2 ∣ N := dvd_trans (by decide : 2 ∣ 4) hdiv
  have h4 : 4 * (N / 4) = N := Nat.mul_div_cancel' hdiv
  have h2 : 2 * (N / 2) = N := Nat.mul_div_cancel' h2dvd
  apply Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2)
  calc
    2 * (N / 2) = N := h2
    _ = 4 * (N / 4) := h4.symm
    _ = 2 * (2 * (N / 4)) := by ring

private theorem three_of_quarter {N : ℕ} (hdiv : 4 ∣ N) (hN : 4 ≤ N) :
    N / 4 < N / 2 ∧ N / 2 < 3 * (N / 4) ∧ 3 * (N / 4) < N := by
  have hpos := quarterCount_pos hdiv hN
  have hhalf := half_of_quarter hdiv
  have h4 : 4 * (N / 4) = N := Nat.mul_div_cancel' hdiv
  refine ⟨?_, ?_, ?_⟩
  · rw [hhalf]
    omega
  · rw [hhalf]
    omega
  · have hlt : 3 * (N / 4) < 4 * (N / 4) := by omega
    simpa [h4] using hlt

private theorem lock_from_quarter {n N : ℕ} (hdiv : 4 ∣ N) (hN : 0 < N)
    (hn : N / 4 ≤ n) :
    JNormalized (express (alignedSteps n N)) = -((1 : ℝ) / 3) := by
  rw [express_aligned]
  have hwall : N ≤ 4 * n := by
    calc
      N = 4 * (N / 4) := (Nat.mul_div_cancel' hdiv).symm
      _ ≤ 4 * n := Nat.mul_le_mul_left 4 hn
  exact collective_locks hN hwall

private theorem sin_increasing_on_right {a b : ℝ} (ha : 0 ≤ a) (hlt : a < b)
    (hb : b ≤ Real.pi / 2) : Real.sin a < Real.sin b := by
  have hsub : Real.sin b - Real.sin a =
      2 * Real.sin ((b - a) / 2) * Real.cos ((b + a) / 2) := by
    simpa [add_comm] using Real.sin_sub_sin b a
  have hda : 0 < (b - a) / 2 := by linarith
  have hda_pi : (b - a) / 2 < Real.pi := by
    have hle : b - a ≤ Real.pi / 2 := by linarith [ha, hb]
    linarith [Real.pi_pos]
  have hsinp : 0 < Real.sin ((b - a) / 2) :=
    Real.sin_pos_of_pos_of_lt_pi hda hda_pi
  have hmid_gt : -(Real.pi / 2) < (b + a) / 2 := by linarith [Real.pi_pos]
  have hmid_lt : (b + a) / 2 < Real.pi / 2 := by
    have hltb : (a + b) / 2 < b := by linarith
    have hab : (b + a) / 2 = (a + b) / 2 := by ring
    rw [hab]
    exact lt_of_lt_of_le hltb hb
  have hcos : 0 < Real.cos ((b + a) / 2) :=
    Real.cos_pos_of_mem_Ioo ⟨hmid_gt, hmid_lt⟩
  have hpos : 0 < Real.sin b - Real.sin a := by
    rw [hsub]
    positivity
  linarith

private theorem sin_decreasing_on_left {a b : ℝ} (ha : Real.pi / 2 ≤ a) (hlt : a < b)
    (hb : b ≤ Real.pi) : Real.sin b < Real.sin a := by
  have hsub : Real.sin a - Real.sin b =
      2 * Real.sin ((a - b) / 2) * Real.cos ((a + b) / 2) :=
    Real.sin_sub_sin a b
  have hx : 0 < (b - a) / 2 := by linarith
  have hsinneg : Real.sin ((a - b) / 2) < 0 := by
    rw [show (a - b) / 2 = -((b - a) / 2) by ring, Real.sin_neg]
    have hsinp : 0 < Real.sin ((b - a) / 2) := by
      refine Real.sin_pos_of_pos_of_lt_pi hx ?_
      linarith [Real.pi_pos, ha, hb]
    linarith
  have hmid_gt : Real.pi / 2 < (a + b) / 2 := by linarith
  have hmid_lt : (a + b) / 2 < Real.pi + Real.pi / 2 := by
    have hltpi : (a + b) / 2 < Real.pi := by
      have hltb : (a + b) / 2 < b := by linarith
      exact lt_of_lt_of_le hltb hb
    linarith [Real.pi_pos]
  have hcos : Real.cos ((a + b) / 2) < 0 :=
    Real.cos_neg_of_pi_div_two_lt_of_lt hmid_gt hmid_lt
  have hpos : 0 < Real.sin a - Real.sin b := by
    rw [hsub]
    have hprod : 0 < Real.sin ((a - b) / 2) * Real.cos ((a + b) / 2) :=
      mul_pos_of_neg_of_neg hsinneg hcos
    linarith
  linarith

private theorem arg_mono {n m N : ℕ} (hN : 0 < N) (hlt : n < m) :
    (n : ℝ) * Real.pi / N < (m : ℝ) * Real.pi / N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  rw [div_lt_div_iff₀ hN0 hN0]
  have hnm : (n : ℝ) < m := by exact_mod_cast hlt
  have hmul := mul_lt_mul_of_pos_right hnm (mul_pos Real.pi_pos hN0)
  convert hmul using 1 <;> ring

private theorem arg_le_half {m N : ℕ} (hdiv : 4 ∣ N) (hN : 0 < N) (hm : m ≤ N / 2) :
    (m : ℝ) * Real.pi / N ≤ Real.pi / 2 := by
  have h2dvd : 2 ∣ N := dvd_trans (by decide : 2 ∣ 4) hdiv
  have hcancel : 2 * (N / 2) = N := Nat.mul_div_cancel' h2dvd
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  rw [div_le_div_iff₀ hN0 (by norm_num : (0 : ℝ) < 2)]
  have hmle : (2 : ℝ) * m ≤ N := by
    exact_mod_cast (Nat.mul_le_mul_left 2 hm).trans_eq hcancel
  have hmul := mul_le_mul_of_nonneg_right hmle Real.pi_pos.le
  convert hmul using 1 <;> ring

private theorem arg_ge_half {n N : ℕ} (hdiv : 4 ∣ N) (hN : 0 < N) (hn : N / 2 ≤ n) :
    Real.pi / 2 ≤ (n : ℝ) * Real.pi / N := by
  have h2dvd : 2 ∣ N := dvd_trans (by decide : 2 ∣ 4) hdiv
  have hcancel : 2 * (N / 2) = N := Nat.mul_div_cancel' h2dvd
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2) hN0]
  have hnle : (N : ℝ) ≤ (2 : ℝ) * n := by
    exact_mod_cast hcancel.symm.trans_le (Nat.mul_le_mul_left 2 hn)
  have hmul := mul_le_mul_of_nonneg_left hnle Real.pi_pos.le
  convert hmul using 1 ; ring

private theorem arg_le_pi {n N : ℕ} (hN : 0 < N) (hn : n ≤ N) :
    (n : ℝ) * Real.pi / N ≤ Real.pi := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hle : (n : ℝ) / N ≤ 1 := by
    rw [div_le_one hN0]
    exact_mod_cast hn
  have hmul := mul_le_mul_of_nonneg_right hle Real.pi_pos.le
  have hform : (n : ℝ) * Real.pi / N = (n : ℝ) / N * Real.pi := by ring
  linarith [hform, hmul]

private theorem defect_eq_sin {n N : ℕ} (hn : 0 < n) (hN : 0 < N) :
    1 - computationalWeight
        (applyMat (dualRotorMat (EuclideanSpace.single 0 ((n : ℝ) * stepAngle N))) spinUp) =
      Real.sin ((n : ℝ) * Real.pi / N) ^ 2 :=
  aligned_transverse_defect hn hN

private theorem sq_sin_lt {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hlt : a < b) :
    a ^ 2 < b ^ 2 :=
  (sq_lt_sq₀ ha hb).mpr hlt

theorem locked_error_rises {N n m : ℕ} (hdiv : 4 ∣ N) (hN : 4 ≤ N)
    (hn : N / 4 ≤ n) (hm : m ≤ N / 2) (hlt : n < m) :
    JNormalized (express (alignedSteps n N)) = -((1 : ℝ) / 3) ∧
      JNormalized (express (alignedSteps m N)) = -((1 : ℝ) / 3) ∧
      1 - computationalWeight
          (applyMat (dualRotorMat (EuclideanSpace.single 0 ((n : ℝ) * stepAngle N))) spinUp) <
        1 - computationalWeight
          (applyMat (dualRotorMat (EuclideanSpace.single 0 ((m : ℝ) * stepAngle N))) spinUp) ∧
      mutualSum m N < mutualSum n N := by
  have hpos : 0 < N := lt_of_lt_of_le (by decide : (0 : ℕ) < 4) hN
  have hn0 : 0 < n := lt_of_lt_of_le (quarterCount_pos hdiv hN) hn
  have hm0 : 0 < m := lt_trans hn0 hlt
  have hlockn := lock_from_quarter hdiv hpos hn
  have hlockm := lock_from_quarter hdiv hpos (le_trans hn (le_of_lt hlt))
  refine ⟨hlockn, hlockm, ?_, mutual_grows hpos (Nat.succ_le_of_lt hn0) hlt⟩
  rw [defect_eq_sin hn0 hpos, defect_eq_sin hm0 hpos]
  have ha0 : 0 ≤ (n : ℝ) * Real.pi / N :=
    div_nonneg (mul_nonneg (by exact_mod_cast hn0.le) Real.pi_pos.le) (by exact_mod_cast hpos.le)
  have hltArg := arg_mono hpos hlt
  have hb := arg_le_half hdiv hpos hm
  have hsin := sin_increasing_on_right ha0 hltArg hb
  have hpi : Real.pi / 2 ≤ Real.pi := half_le_self Real.pi_nonneg
  have hsn := Real.sin_nonneg_of_nonneg_of_le_pi ha0
    (le_trans (arg_le_half hdiv hpos (le_trans (le_of_lt hlt) hm)) hpi)
  have hsm := Real.sin_nonneg_of_nonneg_of_le_pi (le_of_lt (lt_of_le_of_lt ha0 hltArg))
    (le_trans hb hpi)
  exact sq_sin_lt hsn hsm hsin

theorem locked_error_falls {N n m : ℕ} (hdiv : 4 ∣ N) (hN : 4 ≤ N)
    (hn : N / 2 ≤ n) (hm : m ≤ N) (hlt : n < m) :
    JNormalized (express (alignedSteps n N)) = -((1 : ℝ) / 3) ∧
      JNormalized (express (alignedSteps m N)) = -((1 : ℝ) / 3) ∧
      1 - computationalWeight
          (applyMat (dualRotorMat (EuclideanSpace.single 0 ((m : ℝ) * stepAngle N))) spinUp) <
        1 - computationalWeight
          (applyMat (dualRotorMat (EuclideanSpace.single 0 ((n : ℝ) * stepAngle N))) spinUp) ∧
      mutualSum m N < mutualSum n N := by
  have hpos : 0 < N := lt_of_lt_of_le (by decide : (0 : ℕ) < 4) hN
  have hhalf : N / 4 ≤ N / 2 := le_of_lt (three_of_quarter hdiv hN).1
  have hn0 : 0 < n := lt_of_lt_of_le (quarterCount_pos hdiv hN) (le_trans hhalf hn)
  have hm0 : 0 < m := lt_trans hn0 hlt
  have hlockn := lock_from_quarter hdiv hpos (le_trans hhalf hn)
  have hlockm := lock_from_quarter hdiv hpos (le_trans hhalf (le_trans hn (le_of_lt hlt)))
  refine ⟨hlockn, hlockm, ?_, mutual_grows hpos (Nat.succ_le_of_lt hn0) hlt⟩
  rw [defect_eq_sin hn0 hpos, defect_eq_sin hm0 hpos]
  have ha : Real.pi / 2 ≤ (n : ℝ) * Real.pi / N := arg_ge_half hdiv hpos hn
  have hltArg := arg_mono hpos hlt
  have hb : (m : ℝ) * Real.pi / N ≤ Real.pi := arg_le_pi hpos hm
  have hsin := sin_decreasing_on_left ha hltArg hb
  have hsn := Real.sin_nonneg_of_nonneg_of_le_pi (le_trans (by linarith [Real.pi_pos]) ha)
    (le_trans (le_of_lt hltArg) hb)
  have hsm := Real.sin_nonneg_of_nonneg_of_le_pi
    (le_trans (by linarith [Real.pi_pos]) (le_of_lt hltArg)) hb
  exact sq_sin_lt hsm hsn hsin

private theorem quarter_arg {N : ℕ} (hdiv : 4 ∣ N) (hN : 0 < N) :
    ((N / 4 : ℕ) : ℝ) * Real.pi / N = Real.pi / 4 := by
  rw [countHalfAngle (n := N / 4) hN, quarterTurn_angle hdiv hN]
  ring

private theorem half_arg {N : ℕ} (hdiv : 4 ∣ N) (hN : 0 < N) :
    ((N / 2 : ℕ) : ℝ) * Real.pi / N = Real.pi / 2 := by
  rw [countHalfAngle (n := N / 2) hN, halfTurn_angle hdiv hN]

private theorem threeQuarter_arg {N : ℕ} (hdiv : 4 ∣ N) (hN : 0 < N) :
    ((3 * (N / 4) : ℕ) : ℝ) * Real.pi / N = 3 * Real.pi / 4 := by
  have hcoe : ((3 * (N / 4) : ℕ) : ℝ) = 3 * ((N / 4 : ℕ) : ℝ) := by norm_cast
  rw [hcoe]
  have hquarter := quarter_arg hdiv hN
  calc
    (3 * ((N / 4 : ℕ) : ℝ)) * Real.pi / N =
        3 * (((N / 4 : ℕ) : ℝ) * Real.pi / N) := by ring
    _ = 3 * (Real.pi / 4) := by rw [hquarter]
    _ = 3 * Real.pi / 4 := by ring

private theorem full_arg {N : ℕ} (hN : 0 < N) :
    (N : ℝ) * Real.pi / N = Real.pi := by
  have hNz : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_iff_ne_zero.mp hN)
  field_simp [hNz]

private theorem sinSq_quarter :
    Real.sin (Real.pi / 4) ^ 2 = (1 : ℝ) / 2 := by
  rw [Real.sin_pi_div_four, div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

theorem fourCounts_lock {N : ℕ} (hdiv : 4 ∣ N) (hN : 4 ≤ N) :
    JNormalized (express (alignedSteps (N / 4) N)) = -((1 : ℝ) / 3) ∧
      JNormalized (express (alignedSteps (N / 2) N)) = -((1 : ℝ) / 3) ∧
      JNormalized (express (alignedSteps (3 * (N / 4)) N)) = -((1 : ℝ) / 3) ∧
      JNormalized (express (alignedSteps N N)) = -((1 : ℝ) / 3) ∧
      1 - computationalWeight
          (applyMat (dualRotorMat
            (EuclideanSpace.single 0 (((N / 4 : ℕ) : ℝ) * stepAngle N))) spinUp) = 1 / 2 ∧
      1 - computationalWeight
          (applyMat (dualRotorMat
            (EuclideanSpace.single 0 (((N / 2 : ℕ) : ℝ) * stepAngle N))) spinUp) = 1 ∧
      1 - computationalWeight
          (applyMat (dualRotorMat
            (EuclideanSpace.single 0 (((3 * (N / 4) : ℕ) : ℝ) * stepAngle N))) spinUp) =
        1 / 2 ∧
      1 - computationalWeight
          (applyMat (dualRotorMat
            (EuclideanSpace.single 0 ((N : ℝ) * stepAngle N))) spinUp) = 0 ∧
      mutualSum (N / 2) N < mutualSum (N / 4) N ∧
      mutualSum (3 * (N / 4)) N < mutualSum (N / 2) N ∧
      mutualSum N N < mutualSum (3 * (N / 4)) N := by
  have hpos : 0 < N := lt_of_lt_of_le (by decide : (0 : ℕ) < 4) hN
  have hord := three_of_quarter hdiv hN
  have hq : 1 ≤ N / 4 := Nat.succ_le_of_lt (quarterCount_pos hdiv hN)
  have hhalfLe : N / 4 ≤ N / 2 := le_of_lt hord.1
  have hthreeLe : N / 4 ≤ 3 * (N / 4) := le_of_lt (lt_trans hord.1 hord.2.1)
  have hfullLe : N / 4 ≤ N := le_trans hthreeLe (le_of_lt hord.2.2)
  refine ⟨lock_from_quarter hdiv hpos le_rfl, lock_from_quarter hdiv hpos hhalfLe,
    lock_from_quarter hdiv hpos hthreeLe, lock_from_quarter hdiv hpos hfullLe, ?_, ?_, ?_, ?_,
    mutual_grows hpos hq hord.1, mutual_grows hpos (le_trans hq hhalfLe) hord.2.1,
    mutual_grows hpos (le_trans hq hthreeLe) hord.2.2⟩
  · rw [defect_eq_sin (quarterCount_pos hdiv hN) hpos, quarter_arg hdiv hpos, sinSq_quarter]
  · have hhalfPos : 0 < N / 2 := lt_trans (quarterCount_pos hdiv hN) hord.1
    rw [defect_eq_sin hhalfPos hpos, half_arg hdiv hpos, Real.sin_pi_div_two]
    norm_num
  · have hthreePos : 0 < 3 * (N / 4) :=
      lt_trans (quarterCount_pos hdiv hN) (lt_trans hord.1 hord.2.1)
    rw [defect_eq_sin hthreePos hpos, threeQuarter_arg hdiv hpos,
      show (3 : ℝ) * Real.pi / 4 = Real.pi - Real.pi / 4 by ring, Real.sin_pi_sub, sinSq_quarter]
  · rw [defect_eq_sin hpos hpos, full_arg hpos, Real.sin_pi]
    norm_num

end DstDiophantine.Gravity.GravitonQuantum

end
