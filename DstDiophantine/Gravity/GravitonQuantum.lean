import DstDiophantine.Algebra.SourceSuperposition
import DstDiophantine.Gravity.TorsionalLayer
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

A graviton is one pure dual step on a single axis, of angle `2π/N`. For
`N ≥ 4` it lies in the admissible cone, and its normalized height is the
floor `-ε_N = -16/(3N²)`.

## Aligned gravitons

`n` copies aligned on that axis add in the rapidity. The square of the sum
splits into `n` own shares and `n(n-1)` ordered-pair shares. Every share
equals `farHeight`, the height of the one graviton that travels alone, and
that height does not depend on `n`. The ordered-pair sum vanishes for one
graviton. Once `n ≥ 1` are present, one further graviton keeps its own
share equal to `farHeight` and makes the ordered-pair sum strictly more
negative, by `2n` shares. For `n ≥ 3` the ordered-pair sum is strictly more
negative than the own sum.

While `4n ≤ N` the copies stay in the cone, and the height they express is
this split, `n²` times one graviton. Once `4n ≥ N` the nearest admissible
point on that axis is the pure dual corner: the expressed height locks at
`-1/3`, and any further mutual growth remains in the internal sum. For
`N ≥ 5` one graviton stays strictly above that lock. For `N ≥ 8` two
gravitons stay in the cone, and their height is four times one.

## The same step, read on a spinor

The step is the dual rotor of that angle. About an axis transverse to a
computational eigenstate it replaces the Born weight `1` by `cos²(π/N)`.
The orthogonal outcome has probability `sin²(π/N)`. For `N ≥ 3` that
probability lies strictly between `(3/4)ε_N` and `(3π²/16)ε_N`, and
strictly above `ε_N` itself. For `N ≥ 5` it lies strictly below `1/2`, so
the original outcome remains the majority. About the eigenaxis the step
multiplies the eigenstate by a phase, leaves the weight equal to `1`, and
the orthogonal probability is `0`. On every compactification with
`N > 10¹⁹` the orthogonal probability lies strictly below `10⁻³⁷`. Three
hundred aligned gravitons on that compactification remain in the cone,
express `300²` times one, and stay strictly above `-10⁻³²`.

## Same angle, other carriers

The usual step, the dual step, and the equal-scale step are three
admissible carriers of one lattice angle, with heights `+ε_N`, `-ε_N`, and
`0`. The equal-scale phase `π` makes the interference negative and is not
admissible. No mass is assigned to any carrier. A meson spectrum is not
read off them.

The charged-pion mass is an external stand-in, compared with the floors in
`NuclearLayer`. The mass ratio read from the channel length, with no meson
mass as an input, is `SignReversal.channelMassRatio`. Neither is a graviton.

## Not claimed

* A derivation of `G`, of `α_G`, or of a laboratory error rate. The integer
  `N` is not fixed. `NuclearLayer.alphaG_bounds` is a separate window, and
  it is not this Born weight. What is fixed, once a compactification lies
  under that window, is the size: `floor_at_most_proton_planck`.
* That every device error is one transverse step. The orthogonal
  probability is not the height `ε_N`.
* A Newtonian multi-body law, or a force between bodies at separated
  positions. The mutual share is the cross term of aligned rapidities on
  one axis. The expressed point is the admissible foot already constructed
  in `SourceSuperposition`.
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

/-- Two aligned gravitons stay in the cone, and their height is four times one.
`two_fourfold_split` writes that height as two own shares and two ordered-pair
shares. -/
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

/-- One graviton stays strictly above the lock `-1/3`. -/
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

/-- Orthogonal probability of one transverse step. -/
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

/-- `sin²(π/N)` against the floor `ε_N = 16/(3N²)`, for `N ≥ 3`. -/
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

/-- The orthogonal probability strictly exceeds the height `ε_N`. -/
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

/-- A transverse step registers a probability strictly above its height. -/
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

/-- On every compactification past `10¹⁹`, one transverse step errs by less than `10⁻³⁷`. -/
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

/-- Three hundred aligned steps on a compactification past `10¹⁹` express the
square and stay strictly above `-10⁻³²`. -/
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

/-! ### Own shares and mutual shares

The normalized height is quadratic in the rapidity, so `n` aligned gravitons
split into `n` own shares and `n(n-1)` ordered-pair shares. Each share
equals `farHeight`, the height of the one graviton that travels alone.
Adding one graviton contributes one own share and `2n` new ordered-pair
shares. Inside the cone the expressed height is this split
(`expressed_own_plus_mutual`). On and past the wall the expressed height is
the lock `-1/3`, while the mutual sum of the internal rapidities keeps
becoming more negative.
-/

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

/-- One graviton carries only its own height, equal to the graviton that travels alone. -/
theorem lone_eq_far {N : ℕ} (hN : 0 < N) :
    JNormalized (alignedSteps 1 N) = farHeight N ∧ mutualSum 1 N = 0 := by
  refine ⟨?_, mutualSum_one N⟩
  rw [height_own_plus_mutual (n := 1) hN]
  unfold ownSum mutualSum
  ring

/-- One further graviton adds its own share and `2n` ordered-pair shares. -/
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

/-- Once one graviton is present, one further graviton makes the mutual sum strictly
more negative. -/
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

/-- For `1 ≤ n < m` the mutual sum of the larger count is strictly more negative. -/
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

/-- For `n ≥ 3` the mutual sum is strictly more negative than the own sum. -/
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

/-- Two aligned gravitons are two own shares and two ordered-pair shares. -/
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

/-- Inside the cone the expressed height is the own sum plus the mutual sum. -/
theorem expressed_own_plus_mutual {n N : ℕ} (hN : 0 < N) (h : 4 * n ≤ N) :
    JNormalized (express (alignedSteps n N)) = ownSum n N + mutualSum n N := by
  rw [express_eq_of_admissible (collective_admissible h)]
  exact height_own_plus_mutual hN

/-- On and past the wall the expressed height stays at the lock, while one further
graviton still makes the internal mutual sum strictly more negative. -/
theorem expressed_locks_while_mutual_grows {n N : ℕ} (hN : 0 < N) (h : N ≤ 4 * n)
    (hn : 0 < n) :
    JNormalized (express (alignedSteps n N)) = -((1 : ℝ) / 3) ∧
      mutualSum (n + 1) N < mutualSum n N := by
  refine ⟨?_, mutual_strict hN hn⟩
  rw [express_aligned]
  exact collective_locks hN h

/-! ### Carriers of one angle

One lattice angle builds three admissible carriers, and none is a mass.
The usual step has height `+ε_N` and interference strictly above `1`. The
dual step, one graviton, has height `-ε_N` and lies in the repulsive regime
of `J`, while its interference on the cone stays strictly between `0` and
`1`. The equal-scale step has height `0` and positive interference. The
equal-scale phase `π`, where the interference is negative, is not
admissible. Past the wall the expressed height locks at `-1/3` and the
internal height lies strictly below that lock.
-/

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

theorem usualStep_admissible {N : ℕ} (hN : 4 ≤ N) :
    IsAdmissibleContinuous (oneAxisUsual (stepAngle N)) := by
  have hθ : 0 ≤ stepAngle N :=
    (stepAngle_pos (lt_of_lt_of_le (by decide : 0 < 4) hN)).le
  have hle := stepAngle_le_half_pi hN
  intro a
  fin_cases a
  · simp only [oneAxisUsual]
    exact ⟨hθ, le_rfl, by simpa using hle⟩
  · simp only [oneAxisUsual]
    exact ⟨le_rfl, le_rfl, by simpa using (div_nonneg Real.pi_nonneg (by norm_num : (0 : ℝ) ≤ 2))⟩
  · simp only [oneAxisUsual]
    exact ⟨le_rfl, le_rfl, by simpa using (div_nonneg Real.pi_nonneg (by norm_num : (0 : ℝ) ≤ 2))⟩

theorem balancedStep_admissible {N : ℕ} (hN : 4 ≤ N) :
    IsAdmissibleContinuous (oneAxisBalanced (stepAngle N / 2)) := by
  have hsum := stepAngle_le_half_pi hN
  have hhalf : 0 ≤ stepAngle N / 2 :=
    div_nonneg (stepAngle_nonneg N) (by norm_num)
  intro a
  fin_cases a
  · simp only [oneAxisBalanced]
    exact ⟨hhalf, hhalf, by simpa using hsum⟩
  · simp only [oneAxisBalanced]
    exact ⟨le_rfl, le_rfl, by simpa using (div_nonneg Real.pi_nonneg (by norm_num : (0 : ℝ) ≤ 2))⟩
  · simp only [oneAxisBalanced]
    exact ⟨le_rfl, le_rfl, by simpa using (div_nonneg Real.pi_nonneg (by norm_num : (0 : ℝ) ≤ 2))⟩

theorem gammaS_usual (θ : ℝ) : gammaS θ 0 = Real.cosh (θ / 2) := by
  unfold gammaS
  simp

theorem gammaS_dual (θ : ℝ) : gammaS 0 θ = Real.cos (θ / 2) := by
  unfold gammaS
  simp

theorem gammaS_balanced (θ : ℝ) : gammaS θ θ = gammaSEqual (θ / 2) := by
  have h := gammaSEqual_eq_gammaS (θ / 2)
  have htwice : 2 * (θ / 2) = θ := by ring
  simpa [htwice] using h.symm

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

theorem gammaSEqual_pos_up_to_quarter {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ Real.pi / 4) :
    0 < gammaSEqual x := by
  rcases hx0.eq_or_lt with rfl | hxpos
  · simp [gammaSEqual_zero]
  · have hsin_pos : 0 < Real.sin x :=
      Real.sin_pos_of_pos_of_lt_pi hxpos (by linarith [hx, Real.pi_pos])
    have hsin_le : Real.sin x ≤ Real.sin (Real.pi / 4) := by
      refine Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [hx0, Real.pi_pos])
        (by linarith [Real.pi_pos]) hx
    have hcos_ge : Real.cos (Real.pi / 4) ≤ Real.cos x := by
      refine Real.cos_le_cos_of_nonneg_of_le_pi ?_ (by linarith [Real.pi_pos]) hx
      linarith
    have hid : Real.sin (Real.pi / 4) = Real.cos (Real.pi / 4) := by
      rw [Real.sin_pi_div_four, Real.cos_pi_div_four]
    have hsc : Real.sin x ≤ Real.cos x := by linarith [hsin_le, hcos_ge, hid]
    have hsub : Real.cosh x - Real.sinh x = Real.exp (-x) := by
      rw [Real.cosh_eq, Real.sinh_eq]
      ring
    unfold gammaSEqual
    have hsplit : Real.cosh x * Real.cos x - Real.sinh x * Real.sin x =
        Real.cosh x * (Real.cos x - Real.sin x) + Real.exp (-x) * Real.sin x := by
      rw [← hsub]
      ring
    have hrest : 0 ≤ Real.cosh x * (Real.cos x - Real.sin x) :=
      mul_nonneg (Real.cosh_pos x).le (sub_nonneg.mpr hsc)
    have hmain : 0 < Real.exp (-x) * Real.sin x :=
      mul_pos (Real.exp_pos _) hsin_pos
    linarith [hsplit, hrest, hmain]

theorem balanced_interference_pos {N : ℕ} (hN : 4 ≤ N) :
    0 < gammaS (stepAngle N / 2) (stepAngle N / 2) := by
  rw [gammaS_balanced]
  have hstep := stepAngle_le_half_pi hN
  refine gammaSEqual_pos_up_to_quarter ?_ ?_
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

theorem gammaSEqual_pi_neg : gammaSEqual Real.pi < 0 := by
  have h := gammaSEqual_nat_mul_pi 1
  simp only [Nat.cast_one, one_mul, pow_one] at h
  rw [h]
  linarith [Real.cosh_pos Real.pi]

theorem negative_interference_not_admissible :
    gammaS (2 * Real.pi) (2 * Real.pi) < 0 ∧
      ¬ IsAdmissibleContinuous (oneAxisBalanced (2 * Real.pi)) := by
  refine ⟨?_, ?_⟩
  · rw [gammaS_balanced]
    simpa using gammaSEqual_pi_neg
  · intro h
    have hsum := (h 0).2.2
    simp [oneAxisBalanced] at hsum
    linarith [Real.pi_pos]

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

/-- The three admissible carriers have heights `+ε_N`, `-ε_N`, and `0`. The
usual interference stays above `1`, the dual interference stays between `0`
and `1`, and the equal-scale interference stays positive. -/
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

/-- The usual, dual, and equal-scale carriers of one angle are separated by height and by
interference. -/
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

end DstDiophantine.Gravity.GravitonQuantum

end
