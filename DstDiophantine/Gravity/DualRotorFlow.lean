import DstDiophantine.Gravity.DualRotorDynamics
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# Closed flows of the three neighbouring rotor systems

`DualRotorDynamics` records the Euler–Lagrange jets. Here those jets are
integrated.

The written opposite-sign action has free mismatch, so the general
one-axis solution is the affine lag `δ(t) = δ₀ + ν t` together with the
cubic common rapidity
`σ(t) = σ₀ + σ̇₀ t - m δ₀ t² - (m ν / 3) t³`.
Along that flow the Jacobi integral collapses to the initial value
`½ ν σ̇₀ + (m/2) δ₀²`.

The neighbouring runaway `δ̈ = 2 m δ`, for a rate `κ` with `κ² = 2 m`,
is the hyperbolic motion `A cosh(κ t) + B sinh(κ t)`. A nonzero seed is
unbounded. The same-sign oscillator at the same rate is the bounded
motion `A cos(ω t) + B sin(ω t)`, with squared amplitude `A² + B²` and
with Jacobi integral `¼ σ̇₀² + (m/2)(A² + B²)`. In units `ℏ = c = 1`
the lines `√(2 m)` and the Compton frequency `m` meet only at `m = 0`
and `m = 2`.

No derivation of `m` from the dual-rotor algebra is claimed, and the
de Broglie reading of `ν` remains out of scope.
-/

namespace DstDiophantine

namespace Gravity

open Filter

private theorem hasDerivAt_const_mul_id (c t : ℝ) :
    HasDerivAt (fun s : ℝ => c * s) c t := by
  refine ((hasDerivAt_id t).const_mul c).congr_of_eventuallyEq ?_ |>.congr_deriv (by ring)
  refine Eventually.of_forall ?_
  intro s
  simp

private theorem hasDerivAt_pointwise_add {f g : ℝ → ℝ} {f' g' x : ℝ}
    (hf : HasDerivAt f f' x) (hg : HasDerivAt g g' x) :
    HasDerivAt (fun s => f s + g s) (f' + g') x := by
  refine (hf.add hg).congr_of_eventuallyEq ?_
  refine Eventually.of_forall ?_
  intro s
  simp [Pi.add_apply]

private theorem hasDerivAt_pointwise_sub {f g : ℝ → ℝ} {f' g' x : ℝ}
    (hf : HasDerivAt f f' x) (hg : HasDerivAt g g' x) :
    HasDerivAt (fun s => f s - g s) (f' - g') x := by
  refine (hf.sub hg).congr_of_eventuallyEq ?_
  refine Eventually.of_forall ?_
  intro s
  simp [Pi.sub_apply]

/-! ### Affine lag and cubic common rapidity -/

/-- Affine mismatch `δ(t) = δ₀ + ν t`. -/
noncomputable def affineMismatch (δ₀ ν t : ℝ) : ℝ :=
  δ₀ + ν * t

/-- Speed of the cubic common rapidity. -/
noncomputable def cubicRapiditySpeed (σd₀ m δ₀ ν t : ℝ) : ℝ :=
  σd₀ - 2 * m * δ₀ * t - m * ν * t ^ 2

/-- Common rapidity sourced by an affine lag:
`σ(t) = σ₀ + σ̇₀ t - m δ₀ t² - (m ν / 3) t³`. -/
noncomputable def cubicRapidity (σ₀ σd₀ m δ₀ ν t : ℝ) : ℝ :=
  σ₀ + σd₀ * t - m * δ₀ * t ^ 2 - (m * ν / 3) * t ^ 3

theorem hasDerivAt_affineMismatch (δ₀ ν t : ℝ) :
    HasDerivAt (affineMismatch δ₀ ν) ν t := by
  unfold affineMismatch
  exact (hasDerivAt_pointwise_add (hasDerivAt_const t δ₀)
    (hasDerivAt_const_mul_id ν t)).congr_deriv (by ring)

theorem deriv_affineMismatch (δ₀ ν : ℝ) :
    deriv (affineMismatch δ₀ ν) = fun _ => ν := by
  funext t
  exact (hasDerivAt_affineMismatch δ₀ ν t).deriv

theorem deriv2_affineMismatch (δ₀ ν t : ℝ) :
    deriv (deriv (affineMismatch δ₀ ν)) t = 0 := by
  rw [deriv_affineMismatch]
  exact (hasDerivAt_const t ν).deriv

theorem hasDerivAt_cubicRapidity (σ₀ σd₀ m δ₀ ν t : ℝ) :
    HasDerivAt (cubicRapidity σ₀ σd₀ m δ₀ ν) (cubicRapiditySpeed σd₀ m δ₀ ν t) t := by
  unfold cubicRapidity cubicRapiditySpeed
  have h0 : HasDerivAt (fun _ : ℝ => σ₀) 0 t := hasDerivAt_const t σ₀
  have h1 : HasDerivAt (fun s : ℝ => σd₀ * s) σd₀ t := hasDerivAt_const_mul_id σd₀ t
  have h2 : HasDerivAt (fun s : ℝ => (m * δ₀) * s ^ 2) ((m * δ₀) * (2 * t)) t :=
    ((hasDerivAt_pow 2 t).const_mul (m * δ₀)).congr_deriv (by simp [pow_one])
  have h3 : HasDerivAt (fun s : ℝ => (m * ν / 3) * s ^ 3) (m * ν * t ^ 2) t :=
    ((hasDerivAt_pow 3 t).const_mul (m * ν / 3)).congr_deriv (by simp [pow_two]; ring)
  have h :=
    hasDerivAt_pointwise_sub
      (hasDerivAt_pointwise_sub (hasDerivAt_pointwise_add h0 h1) h2) h3
  refine h.congr_deriv ?_
  ring

theorem hasDerivAt_cubicRapiditySpeed (σd₀ m δ₀ ν t : ℝ) :
    HasDerivAt (cubicRapiditySpeed σd₀ m δ₀ ν) (-2 * m * affineMismatch δ₀ ν t) t := by
  unfold cubicRapiditySpeed affineMismatch
  have h0 : HasDerivAt (fun _ : ℝ => σd₀) 0 t := hasDerivAt_const t σd₀
  have h1 : HasDerivAt (fun s : ℝ => (2 * m * δ₀) * s) (2 * m * δ₀) t :=
    hasDerivAt_const_mul_id (2 * m * δ₀) t
  have h2 : HasDerivAt (fun s : ℝ => (m * ν) * s ^ 2) ((m * ν) * (2 * t)) t :=
    ((hasDerivAt_pow 2 t).const_mul (m * ν)).congr_deriv (by simp [pow_one])
  have h := hasDerivAt_pointwise_sub (hasDerivAt_pointwise_sub h0 h1) h2
  refine h.congr_deriv ?_
  ring

theorem deriv_cubicRapidity (σ₀ σd₀ m δ₀ ν : ℝ) :
    deriv (cubicRapidity σ₀ σd₀ m δ₀ ν) = cubicRapiditySpeed σd₀ m δ₀ ν := by
  funext t
  exact (hasDerivAt_cubicRapidity σ₀ σd₀ m δ₀ ν t).deriv

theorem deriv2_cubicRapidity (σ₀ σd₀ m δ₀ ν t : ℝ) :
    deriv (deriv (cubicRapidity σ₀ σd₀ m δ₀ ν)) t =
      -2 * m * affineMismatch δ₀ ν t := by
  rw [deriv_cubicRapidity]
  exact (hasDerivAt_cubicRapiditySpeed σd₀ m δ₀ ν t).deriv

/-- Usual angle reconstructed from `(σ, δ)`. -/
noncomputable def usualFrom (σ δ : ℝ → ℝ) : ℝ → ℝ :=
  fun t => (σ t + δ t) / 2

/-- Dual angle reconstructed from `(σ, δ)`. -/
noncomputable def dualFrom (σ δ : ℝ → ℝ) : ℝ → ℝ :=
  fun t => (σ t - δ t) / 2

theorem hasDerivAt_usualFrom {σ δ : ℝ → ℝ} {σ' δ' t : ℝ}
    (hσ : HasDerivAt σ σ' t) (hδ : HasDerivAt δ δ' t) :
    HasDerivAt (usualFrom σ δ) ((σ' + δ') / 2) t := by
  unfold usualFrom
  exact (hasDerivAt_pointwise_add hσ hδ).div_const 2

theorem hasDerivAt_dualFrom {σ δ : ℝ → ℝ} {σ' δ' t : ℝ}
    (hσ : HasDerivAt σ σ' t) (hδ : HasDerivAt δ δ' t) :
    HasDerivAt (dualFrom σ δ) ((σ' - δ') / 2) t := by
  unfold dualFrom
  exact (hasDerivAt_pointwise_sub hσ hδ).div_const 2

theorem usualFrom_sub_dualFrom (σ δ : ℝ → ℝ) (t : ℝ) :
    usualFrom σ δ t - dualFrom σ δ t = δ t := by
  unfold usualFrom dualFrom
  ring

theorem usualFrom_add_dualFrom (σ δ : ℝ → ℝ) (t : ℝ) :
    usualFrom σ δ t + dualFrom σ δ t = σ t := by
  unfold usualFrom dualFrom
  ring

/-- Written one-axis flow: affine mismatch, cubic common rapidity. -/
noncomputable def writtenDelta (δ₀ ν : ℝ) : ℝ → ℝ :=
  affineMismatch δ₀ ν

noncomputable def writtenSigma (σ₀ σd₀ m δ₀ ν : ℝ) : ℝ → ℝ :=
  cubicRapidity σ₀ σd₀ m δ₀ ν

noncomputable def writtenUsual (σ₀ σd₀ m δ₀ ν : ℝ) : ℝ → ℝ :=
  usualFrom (writtenSigma σ₀ σd₀ m δ₀ ν) (writtenDelta δ₀ ν)

noncomputable def writtenDual (σ₀ σd₀ m δ₀ ν : ℝ) : ℝ → ℝ :=
  dualFrom (writtenSigma σ₀ σd₀ m δ₀ ν) (writtenDelta δ₀ ν)

theorem hasDerivAt_writtenSigma (σ₀ σd₀ m δ₀ ν t : ℝ) :
    HasDerivAt (writtenSigma σ₀ σd₀ m δ₀ ν) (cubicRapiditySpeed σd₀ m δ₀ ν t) t :=
  hasDerivAt_cubicRapidity σ₀ σd₀ m δ₀ ν t

theorem hasDerivAt_writtenDelta (δ₀ ν t : ℝ) :
    HasDerivAt (writtenDelta δ₀ ν) ν t :=
  hasDerivAt_affineMismatch δ₀ ν t

theorem deriv_writtenSigma (σ₀ σd₀ m δ₀ ν : ℝ) :
    deriv (writtenSigma σ₀ σd₀ m δ₀ ν) = cubicRapiditySpeed σd₀ m δ₀ ν :=
  deriv_cubicRapidity σ₀ σd₀ m δ₀ ν

theorem deriv_writtenDelta (δ₀ ν : ℝ) :
    deriv (writtenDelta δ₀ ν) = fun _ => ν :=
  deriv_affineMismatch δ₀ ν

theorem deriv2_writtenSigma (σ₀ σd₀ m δ₀ ν t : ℝ) :
    deriv (deriv (writtenSigma σ₀ σd₀ m δ₀ ν)) t = -2 * m * writtenDelta δ₀ ν t :=
  deriv2_cubicRapidity σ₀ σd₀ m δ₀ ν t

theorem deriv2_writtenDelta (δ₀ ν t : ℝ) :
    deriv (deriv (writtenDelta δ₀ ν)) t = 0 :=
  deriv2_affineMismatch δ₀ ν t

theorem deriv_writtenUsual (σ₀ σd₀ m δ₀ ν t : ℝ) :
    deriv (writtenUsual σ₀ σd₀ m δ₀ ν) t =
      (cubicRapiditySpeed σd₀ m δ₀ ν t + ν) / 2 :=
  (hasDerivAt_usualFrom (hasDerivAt_writtenSigma σ₀ σd₀ m δ₀ ν t)
    (hasDerivAt_writtenDelta δ₀ ν t)).deriv

theorem deriv_writtenDual (σ₀ σd₀ m δ₀ ν t : ℝ) :
    deriv (writtenDual σ₀ σd₀ m δ₀ ν) t =
      (cubicRapiditySpeed σd₀ m δ₀ ν t - ν) / 2 :=
  (hasDerivAt_dualFrom (hasDerivAt_writtenSigma σ₀ σd₀ m δ₀ ν t)
    (hasDerivAt_writtenDelta δ₀ ν t)).deriv

theorem deriv_writtenUsual_fun (σ₀ σd₀ m δ₀ ν : ℝ) :
    deriv (writtenUsual σ₀ σd₀ m δ₀ ν) =
      fun t => (cubicRapiditySpeed σd₀ m δ₀ ν t + ν) / 2 := by
  funext t
  exact deriv_writtenUsual σ₀ σd₀ m δ₀ ν t

theorem deriv_writtenDual_fun (σ₀ σd₀ m δ₀ ν : ℝ) :
    deriv (writtenDual σ₀ σd₀ m δ₀ ν) =
      fun t => (cubicRapiditySpeed σd₀ m δ₀ ν t - ν) / 2 := by
  funext t
  exact deriv_writtenDual σ₀ σd₀ m δ₀ ν t

theorem deriv2_writtenUsual (σ₀ σd₀ m δ₀ ν t : ℝ) :
    deriv (deriv (writtenUsual σ₀ σd₀ m δ₀ ν)) t = -m * writtenDelta δ₀ ν t := by
  rw [deriv_writtenUsual_fun]
  have hσ : HasDerivAt (cubicRapiditySpeed σd₀ m δ₀ ν) (-2 * m * writtenDelta δ₀ ν t) t :=
    hasDerivAt_cubicRapiditySpeed σd₀ m δ₀ ν t
  have hδ : HasDerivAt (fun _ : ℝ => ν) 0 t := hasDerivAt_const t ν
  have h := (hasDerivAt_pointwise_add hσ hδ).div_const 2
  rw [h.deriv]
  ring

theorem deriv2_writtenDual (σ₀ σd₀ m δ₀ ν t : ℝ) :
    deriv (deriv (writtenDual σ₀ σd₀ m δ₀ ν)) t = -m * writtenDelta δ₀ ν t := by
  rw [deriv_writtenDual_fun]
  have hσ : HasDerivAt (cubicRapiditySpeed σd₀ m δ₀ ν) (-2 * m * writtenDelta δ₀ ν t) t :=
    hasDerivAt_cubicRapiditySpeed σd₀ m δ₀ ν t
  have hδ : HasDerivAt (fun _ : ℝ => ν) 0 t := hasDerivAt_const t ν
  have h := (hasDerivAt_pointwise_sub hσ hδ).div_const 2
  rw [h.deriv]
  ring

/-- The cubic flow solves the written Euler–Lagrange system at every time. -/
theorem written_flow_actualEL (σ₀ σd₀ m δ₀ ν t : ℝ) :
    PaperActualEL m (writtenUsual σ₀ σd₀ m δ₀ ν t) (writtenDual σ₀ σd₀ m δ₀ ν t)
      (deriv (deriv (writtenUsual σ₀ σd₀ m δ₀ ν)) t)
      (deriv (deriv (writtenDual σ₀ σd₀ m δ₀ ν)) t) := by
  rw [paperActualEL_eq]
  refine ⟨?_, ?_⟩
  · rw [deriv2_writtenUsual, writtenUsual, writtenDual, usualFrom_sub_dualFrom]
  · rw [deriv2_writtenDual, writtenUsual, writtenDual, usualFrom_sub_dualFrom]

/-- Initial data of the cubic flow. -/
theorem written_flow_initial (σ₀ σd₀ m δ₀ ν : ℝ) :
    writtenDelta δ₀ ν 0 = δ₀ ∧
      deriv (writtenDelta δ₀ ν) 0 = ν ∧
        writtenSigma σ₀ σd₀ m δ₀ ν 0 = σ₀ ∧
          deriv (writtenSigma σ₀ σd₀ m δ₀ ν) 0 = σd₀ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [writtenDelta, affineMismatch]
  · rw [deriv_writtenDelta]
  · simp [writtenSigma, cubicRapidity]
  · rw [deriv_writtenSigma, cubicRapiditySpeed]; ring

/-- Along the cubic flow the Jacobi integral equals its initial value. -/
theorem written_flow_energy (σ₀ σd₀ m δ₀ ν t : ℝ) :
    paperEnergy m (writtenUsual σ₀ σd₀ m δ₀ ν t) (writtenDual σ₀ σd₀ m δ₀ ν t)
        (deriv (writtenUsual σ₀ σd₀ m δ₀ ν) t)
        (deriv (writtenDual σ₀ σd₀ m δ₀ ν) t) =
      (1 / 2) * ν * σd₀ + (m / 2) * δ₀ ^ 2 := by
  rw [paperEnergy_eq_mixed, deriv_writtenUsual, deriv_writtenDual, writtenUsual, writtenDual,
    usualFrom_sub_dualFrom]
  unfold cubicRapiditySpeed writtenDelta affineMismatch
  ring

/-! ### Harmonic oscillator and hyperbolic runaway -/

/-- Harmonic mismatch `A cos(ω t) + B sin(ω t)`. -/
noncomputable def harmonicMismatch (A B ω t : ℝ) : ℝ :=
  A * Real.cos (ω * t) + B * Real.sin (ω * t)

/-- Speed of the harmonic mismatch. -/
noncomputable def harmonicSpeed (A B ω t : ℝ) : ℝ :=
  -A * ω * Real.sin (ω * t) + B * ω * Real.cos (ω * t)

/-- Inertial common rapidity `σ(t) = σ₀ + σ̇₀ t`. -/
noncomputable def inertialRapidity (σ₀ σd₀ t : ℝ) : ℝ :=
  σ₀ + σd₀ * t

/-- Hyperbolic mismatch `A cosh(κ t) + B sinh(κ t)`. -/
noncomputable def hyperbolicMismatch (A B κ t : ℝ) : ℝ :=
  A * Real.cosh (κ * t) + B * Real.sinh (κ * t)

/-- Speed of the hyperbolic mismatch. -/
noncomputable def hyperbolicSpeed (A B κ t : ℝ) : ℝ :=
  A * κ * Real.sinh (κ * t) + B * κ * Real.cosh (κ * t)

private theorem hasDerivAt_cos_mul (ω t : ℝ) :
    HasDerivAt (fun s : ℝ => Real.cos (ω * s)) (-Real.sin (ω * t) * ω) t := by
  simpa [Function.comp_def] using
    (Real.hasDerivAt_cos (ω * t)).comp t (hasDerivAt_const_mul_id ω t)

private theorem hasDerivAt_sin_mul (ω t : ℝ) :
    HasDerivAt (fun s : ℝ => Real.sin (ω * s)) (Real.cos (ω * t) * ω) t := by
  simpa [Function.comp_def] using
    (Real.hasDerivAt_sin (ω * t)).comp t (hasDerivAt_const_mul_id ω t)

private theorem hasDerivAt_cosh_mul (κ t : ℝ) :
    HasDerivAt (fun s : ℝ => Real.cosh (κ * s)) (Real.sinh (κ * t) * κ) t := by
  simpa [Function.comp_def] using
    (Real.hasDerivAt_cosh (κ * t)).comp t (hasDerivAt_const_mul_id κ t)

private theorem hasDerivAt_sinh_mul (κ t : ℝ) :
    HasDerivAt (fun s : ℝ => Real.sinh (κ * s)) (Real.cosh (κ * t) * κ) t := by
  simpa [Function.comp_def] using
    (Real.hasDerivAt_sinh (κ * t)).comp t (hasDerivAt_const_mul_id κ t)

theorem hasDerivAt_harmonicMismatch (A B ω t : ℝ) :
    HasDerivAt (harmonicMismatch A B ω) (harmonicSpeed A B ω t) t := by
  unfold harmonicMismatch harmonicSpeed
  have hc := (hasDerivAt_cos_mul ω t).const_mul A
  have hs := (hasDerivAt_sin_mul ω t).const_mul B
  refine (hc.add hs).congr_deriv ?_
  ring

theorem hasDerivAt_harmonicSpeed (A B ω t : ℝ) :
    HasDerivAt (harmonicSpeed A B ω) (-(ω ^ 2) * harmonicMismatch A B ω t) t := by
  unfold harmonicSpeed harmonicMismatch
  have hs := (hasDerivAt_sin_mul ω t).const_mul (-A * ω)
  have hc := (hasDerivAt_cos_mul ω t).const_mul (B * ω)
  refine (hs.add hc).congr_deriv ?_
  ring

theorem hasDerivAt_inertialRapidity (σ₀ σd₀ t : ℝ) :
    HasDerivAt (inertialRapidity σ₀ σd₀) σd₀ t := by
  unfold inertialRapidity
  exact (hasDerivAt_pointwise_add (hasDerivAt_const t σ₀)
    (hasDerivAt_const_mul_id σd₀ t)).congr_deriv (by ring)

theorem deriv_inertialRapidity (σ₀ σd₀ : ℝ) :
    deriv (inertialRapidity σ₀ σd₀) = fun _ => σd₀ := by
  funext t
  exact (hasDerivAt_inertialRapidity σ₀ σd₀ t).deriv

theorem deriv2_inertialRapidity (σ₀ σd₀ t : ℝ) :
    deriv (deriv (inertialRapidity σ₀ σd₀)) t = 0 := by
  rw [deriv_inertialRapidity]
  exact (hasDerivAt_const t σd₀).deriv

theorem hasDerivAt_hyperbolicMismatch (A B κ t : ℝ) :
    HasDerivAt (hyperbolicMismatch A B κ) (hyperbolicSpeed A B κ t) t := by
  unfold hyperbolicMismatch hyperbolicSpeed
  have hc := (hasDerivAt_cosh_mul κ t).const_mul A
  have hs := (hasDerivAt_sinh_mul κ t).const_mul B
  refine (hc.add hs).congr_deriv ?_
  ring

theorem hasDerivAt_hyperbolicSpeed (A B κ t : ℝ) :
    HasDerivAt (hyperbolicSpeed A B κ) (κ ^ 2 * hyperbolicMismatch A B κ t) t := by
  unfold hyperbolicSpeed hyperbolicMismatch
  have hs := (hasDerivAt_sinh_mul κ t).const_mul (A * κ)
  have hc := (hasDerivAt_cosh_mul κ t).const_mul (B * κ)
  refine (hs.add hc).congr_deriv ?_
  ring

theorem deriv_harmonicMismatch (A B ω : ℝ) :
    deriv (harmonicMismatch A B ω) = harmonicSpeed A B ω := by
  funext t
  exact (hasDerivAt_harmonicMismatch A B ω t).deriv

theorem deriv2_harmonicMismatch (A B ω t : ℝ) :
    deriv (deriv (harmonicMismatch A B ω)) t =
      -(ω ^ 2) * harmonicMismatch A B ω t := by
  rw [deriv_harmonicMismatch]
  exact (hasDerivAt_harmonicSpeed A B ω t).deriv

theorem deriv_hyperbolicMismatch (A B κ : ℝ) :
    deriv (hyperbolicMismatch A B κ) = hyperbolicSpeed A B κ := by
  funext t
  exact (hasDerivAt_hyperbolicMismatch A B κ t).deriv

theorem deriv2_hyperbolicMismatch (A B κ t : ℝ) :
    deriv (deriv (hyperbolicMismatch A B κ)) t =
      κ ^ 2 * hyperbolicMismatch A B κ t := by
  rw [deriv_hyperbolicMismatch]
  exact (hasDerivAt_hyperbolicSpeed A B κ t).deriv

/-- Squared harmonic amplitude is constant: `(A cos + B sin)² ≤ A² + B²`. -/
theorem harmonicMismatch_sq_le (A B ω t : ℝ) :
    harmonicMismatch A B ω t ^ 2 ≤ A ^ 2 + B ^ 2 := by
  unfold harmonicMismatch
  have hsc : Real.sin (ω * t) ^ 2 + Real.cos (ω * t) ^ 2 = 1 :=
    Real.sin_sq_add_cos_sq (ω * t)
  have hnn : 0 ≤ (A * Real.sin (ω * t) - B * Real.cos (ω * t)) ^ 2 := sq_nonneg _
  nlinarith [hsc, hnn]

/-- Mismatch part of the oscillator energy, reduced by `ω² = 2 m`. -/
theorem harmonic_energy_identity (A B ω m θ : ℝ) (hω : ω ^ 2 = 2 * m) :
    (1 / 4) * (-A * ω * Real.sin θ + B * ω * Real.cos θ) ^ 2 +
        (m / 2) * (A * Real.cos θ + B * Real.sin θ) ^ 2 =
      (m / 2) * (A ^ 2 + B ^ 2) := by
  have hsc : Real.sin θ ^ 2 + Real.cos θ ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
  have hm : m = ω ^ 2 / 2 := by
    rw [hω]
    ring
  rw [hm]
  set s := Real.sin θ
  set c := Real.cos θ
  simp only [s, c] at hsc
  have hquad : (-A * s + B * c) ^ 2 + (A * c + B * s) ^ 2 = A ^ 2 + B ^ 2 := by
    have : (-A * s + B * c) ^ 2 + (A * c + B * s) ^ 2 =
        (A ^ 2 + B ^ 2) * (s ^ 2 + c ^ 2) := by ring
    rw [this, hsc, mul_one]
  have hlin : -A * ω * s + B * ω * c = ω * (-A * s + B * c) := by ring
  rw [hlin]
  have hsq : (1 / 4) * (ω * (-A * s + B * c)) ^ 2 =
      (ω ^ 2 / 4) * (-A * s + B * c) ^ 2 := by ring
  rw [hsq]
  have hcoeff : ω ^ 2 / 2 / 2 = ω ^ 2 / 4 := by ring
  rw [hcoeff]
  have hgather :
      (ω ^ 2 / 4) * (-A * s + B * c) ^ 2 + (ω ^ 2 / 4) * (A * c + B * s) ^ 2 =
        (ω ^ 2 / 4) * ((-A * s + B * c) ^ 2 + (A * c + B * s) ^ 2) := by ring
  rw [hgather, hquad]

noncomputable def oscillatorDelta (A B ω : ℝ) : ℝ → ℝ :=
  harmonicMismatch A B ω

noncomputable def oscillatorSigma (σ₀ σd₀ : ℝ) : ℝ → ℝ :=
  inertialRapidity σ₀ σd₀

noncomputable def oscillatorUsual (σ₀ σd₀ A B ω : ℝ) : ℝ → ℝ :=
  usualFrom (oscillatorSigma σ₀ σd₀) (oscillatorDelta A B ω)

noncomputable def oscillatorDual (σ₀ σd₀ A B ω : ℝ) : ℝ → ℝ :=
  dualFrom (oscillatorSigma σ₀ σd₀) (oscillatorDelta A B ω)

theorem deriv_oscillatorSigma (σ₀ σd₀ : ℝ) :
    deriv (oscillatorSigma σ₀ σd₀) = fun _ => σd₀ :=
  deriv_inertialRapidity σ₀ σd₀

theorem deriv_oscillatorDelta (A B ω : ℝ) :
    deriv (oscillatorDelta A B ω) = harmonicSpeed A B ω :=
  deriv_harmonicMismatch A B ω

theorem deriv_oscillatorUsual (σ₀ σd₀ A B ω t : ℝ) :
    deriv (oscillatorUsual σ₀ σd₀ A B ω) t =
      (σd₀ + harmonicSpeed A B ω t) / 2 := by
  exact (hasDerivAt_usualFrom (hasDerivAt_inertialRapidity σ₀ σd₀ t)
    (hasDerivAt_harmonicMismatch A B ω t)).deriv

theorem deriv_oscillatorDual (σ₀ σd₀ A B ω t : ℝ) :
    deriv (oscillatorDual σ₀ σd₀ A B ω) t =
      (σd₀ - harmonicSpeed A B ω t) / 2 := by
  exact (hasDerivAt_dualFrom (hasDerivAt_inertialRapidity σ₀ σd₀ t)
    (hasDerivAt_harmonicMismatch A B ω t)).deriv

theorem deriv_oscillatorUsual_fun (σ₀ σd₀ A B ω : ℝ) :
    deriv (oscillatorUsual σ₀ σd₀ A B ω) =
      fun t => (σd₀ + harmonicSpeed A B ω t) / 2 := by
  funext t
  exact deriv_oscillatorUsual σ₀ σd₀ A B ω t

theorem deriv_oscillatorDual_fun (σ₀ σd₀ A B ω : ℝ) :
    deriv (oscillatorDual σ₀ σd₀ A B ω) =
      fun t => (σd₀ - harmonicSpeed A B ω t) / 2 := by
  funext t
  exact deriv_oscillatorDual σ₀ σd₀ A B ω t

theorem deriv2_oscillatorUsual (σ₀ σd₀ A B ω t : ℝ) :
    deriv (deriv (oscillatorUsual σ₀ σd₀ A B ω)) t =
      -(ω ^ 2) * oscillatorDelta A B ω t / 2 := by
  rw [deriv_oscillatorUsual_fun]
  have hσ : HasDerivAt (fun _ : ℝ => σd₀) 0 t := hasDerivAt_const t σd₀
  have hδ : HasDerivAt (harmonicSpeed A B ω) (-(ω ^ 2) * oscillatorDelta A B ω t) t :=
    hasDerivAt_harmonicSpeed A B ω t
  have h := (hasDerivAt_pointwise_add hσ hδ).div_const 2
  rw [h.deriv]
  ring

theorem deriv2_oscillatorDual (σ₀ σd₀ A B ω t : ℝ) :
    deriv (deriv (oscillatorDual σ₀ σd₀ A B ω)) t =
      (ω ^ 2) * oscillatorDelta A B ω t / 2 := by
  rw [deriv_oscillatorDual_fun]
  have hσ : HasDerivAt (fun _ : ℝ => σd₀) 0 t := hasDerivAt_const t σd₀
  have hδ : HasDerivAt (harmonicSpeed A B ω) (-(ω ^ 2) * oscillatorDelta A B ω t) t :=
    hasDerivAt_harmonicSpeed A B ω t
  have h := (hasDerivAt_pointwise_sub hσ hδ).div_const 2
  rw [h.deriv]
  ring

/-- The harmonic flow solves the same-sign oscillator when `ω² = 2 m`. -/
theorem oscillator_flow_EL (σ₀ σd₀ A B ω m t : ℝ) (hω : ω ^ 2 = 2 * m) :
    OscillatorEL m (oscillatorUsual σ₀ σd₀ A B ω t) (oscillatorDual σ₀ σd₀ A B ω t)
      (deriv (deriv (oscillatorUsual σ₀ σd₀ A B ω)) t)
      (deriv (deriv (oscillatorDual σ₀ σd₀ A B ω)) t) := by
  rw [oscillatorEL_eq]
  refine ⟨?_, ?_⟩
  · rw [deriv2_oscillatorUsual, oscillatorUsual, oscillatorDual, usualFrom_sub_dualFrom, hω]
    ring
  · rw [deriv2_oscillatorDual, oscillatorUsual, oscillatorDual, usualFrom_sub_dualFrom, hω]
    ring

/-- Oscillator energy along the harmonic flow. -/
theorem oscillator_flow_energy (σ₀ σd₀ A B ω m t : ℝ) (hω : ω ^ 2 = 2 * m) :
    oscillatorEnergy m (oscillatorUsual σ₀ σd₀ A B ω t) (oscillatorDual σ₀ σd₀ A B ω t)
        (deriv (oscillatorUsual σ₀ σd₀ A B ω) t)
        (deriv (oscillatorDual σ₀ σd₀ A B ω) t) =
      (1 / 4) * σd₀ ^ 2 + (m / 2) * (A ^ 2 + B ^ 2) := by
  unfold oscillatorEnergy
  rw [deriv_oscillatorUsual, deriv_oscillatorDual, oscillatorUsual, oscillatorDual,
    usualFrom_sub_dualFrom]
  have hkin :
      (1 / 2) * ((σd₀ + harmonicSpeed A B ω t) / 2) ^ 2 +
          (1 / 2) * ((σd₀ - harmonicSpeed A B ω t) / 2) ^ 2 =
        (1 / 4) * σd₀ ^ 2 + (1 / 4) * harmonicSpeed A B ω t ^ 2 := by
    ring
  rw [hkin]
  unfold harmonicSpeed oscillatorDelta harmonicMismatch
  have hrest := harmonic_energy_identity A B ω m (ω * t) hω
  linarith

/-- In units `ℏ = c = 1`, `√(2 m)` meets the Compton frequency `m`
only at the isolated values `m = 0` and `m = 2`. -/
theorem sqrt_two_mul_eq_compton_iff {m : ℝ} (hm : 0 ≤ m) :
    Real.sqrt (2 * m) = m ↔ m = 0 ∨ m = 2 := by
  constructor
  · intro h
    have hsq : 2 * m = m ^ 2 := by
      have hpow : (Real.sqrt (2 * m)) ^ 2 = m ^ 2 := congrArg (fun x : ℝ => x ^ 2) h
      rwa [Real.sq_sqrt (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hm)] at hpow
    have hfac : m * (m - 2) = 0 := by
      have : m * (m - 2) = m ^ 2 - 2 * m := by ring
      rw [this]
      linarith
    rcases mul_eq_zero.mp hfac with h0 | h2
    · exact Or.inl h0
    · exact Or.inr (sub_eq_zero.mp h2)
  · rintro (rfl | rfl)
    · simp [Real.sqrt_zero]
    · rw [show (2 : ℝ) * 2 = 2 ^ 2 by ring, Real.sqrt_sq (by norm_num)]

noncomputable def runawayDelta (A B κ : ℝ) : ℝ → ℝ :=
  hyperbolicMismatch A B κ

noncomputable def runawaySigma (σ₀ σd₀ : ℝ) : ℝ → ℝ :=
  inertialRapidity σ₀ σd₀

noncomputable def runawayUsual (σ₀ σd₀ A B κ : ℝ) : ℝ → ℝ :=
  usualFrom (runawaySigma σ₀ σd₀) (runawayDelta A B κ)

noncomputable def runawayDual (σ₀ σd₀ A B κ : ℝ) : ℝ → ℝ :=
  dualFrom (runawaySigma σ₀ σd₀) (runawayDelta A B κ)

theorem deriv_runawayUsual (σ₀ σd₀ A B κ t : ℝ) :
    deriv (runawayUsual σ₀ σd₀ A B κ) t =
      (σd₀ + hyperbolicSpeed A B κ t) / 2 :=
  (hasDerivAt_usualFrom (hasDerivAt_inertialRapidity σ₀ σd₀ t)
    (hasDerivAt_hyperbolicMismatch A B κ t)).deriv

theorem deriv_runawayDual (σ₀ σd₀ A B κ t : ℝ) :
    deriv (runawayDual σ₀ σd₀ A B κ) t =
      (σd₀ - hyperbolicSpeed A B κ t) / 2 :=
  (hasDerivAt_dualFrom (hasDerivAt_inertialRapidity σ₀ σd₀ t)
    (hasDerivAt_hyperbolicMismatch A B κ t)).deriv

theorem deriv_runawayUsual_fun (σ₀ σd₀ A B κ : ℝ) :
    deriv (runawayUsual σ₀ σd₀ A B κ) =
      fun t => (σd₀ + hyperbolicSpeed A B κ t) / 2 := by
  funext t
  exact deriv_runawayUsual σ₀ σd₀ A B κ t

theorem deriv_runawayDual_fun (σ₀ σd₀ A B κ : ℝ) :
    deriv (runawayDual σ₀ σd₀ A B κ) =
      fun t => (σd₀ - hyperbolicSpeed A B κ t) / 2 := by
  funext t
  exact deriv_runawayDual σ₀ σd₀ A B κ t

theorem deriv2_runawayUsual (σ₀ σd₀ A B κ t : ℝ) :
    deriv (deriv (runawayUsual σ₀ σd₀ A B κ)) t =
      κ ^ 2 * runawayDelta A B κ t / 2 := by
  rw [deriv_runawayUsual_fun]
  have hσ : HasDerivAt (fun _ : ℝ => σd₀) 0 t := hasDerivAt_const t σd₀
  have hδ : HasDerivAt (hyperbolicSpeed A B κ) (κ ^ 2 * runawayDelta A B κ t) t :=
    hasDerivAt_hyperbolicSpeed A B κ t
  have h := (hasDerivAt_pointwise_add hσ hδ).div_const 2
  rw [h.deriv]
  ring

theorem deriv2_runawayDual (σ₀ σd₀ A B κ t : ℝ) :
    deriv (deriv (runawayDual σ₀ σd₀ A B κ)) t =
      -(κ ^ 2) * runawayDelta A B κ t / 2 := by
  rw [deriv_runawayDual_fun]
  have hσ : HasDerivAt (fun _ : ℝ => σd₀) 0 t := hasDerivAt_const t σd₀
  have hδ : HasDerivAt (hyperbolicSpeed A B κ) (κ ^ 2 * runawayDelta A B κ t) t :=
    hasDerivAt_hyperbolicSpeed A B κ t
  have h := (hasDerivAt_pointwise_sub hσ hδ).div_const 2
  rw [h.deriv]
  ring

/-- The hyperbolic flow solves the neighbouring runaway system when `κ² = 2 m`. -/
theorem runaway_flow_claimedEL (σ₀ σd₀ A B κ m t : ℝ) (hκ : κ ^ 2 = 2 * m) :
    PaperClaimedEL m (runawayUsual σ₀ σd₀ A B κ t) (runawayDual σ₀ σd₀ A B κ t)
      (deriv (deriv (runawayUsual σ₀ σd₀ A B κ)) t)
      (deriv (deriv (runawayDual σ₀ σd₀ A B κ)) t) := by
  refine ⟨?_, ?_⟩
  · rw [deriv2_runawayUsual, runawayUsual, runawayDual, usualFrom_sub_dualFrom, hκ]
    ring
  · rw [deriv2_runawayDual, runawayUsual, runawayDual, usualFrom_sub_dualFrom, hκ]
    ring

theorem hyperbolicMismatch_eq_exp (A B κ t : ℝ) :
    hyperbolicMismatch A B κ t =
      ((A + B) / 2) * Real.exp (κ * t) + ((A - B) / 2) * Real.exp (-(κ * t)) := by
  unfold hyperbolicMismatch
  rw [Real.cosh_eq, Real.sinh_eq]
  ring

/-- A nonzero hyperbolic seed is unbounded in time. -/
theorem exists_abs_hyperbolicMismatch_gt {A B κ : ℝ} (hκ : 0 < κ)
    (hAB : A ≠ 0 ∨ B ≠ 0) (C : ℝ) :
    ∃ t, C < |hyperbolicMismatch A B κ t| := by
  set P := (A + B) / 2
  set Q := (A - B) / 2
  have hA : P + Q = A := by
    unfold P Q
    ring
  have hB : P - Q = B := by
    unfold P Q
    ring
  have hPQ : P ≠ 0 ∨ Q ≠ 0 := by
    by_contra hboth
    have hP0 : P = 0 := by
      by_contra hP
      exact hboth (Or.inl hP)
    have hQ0 : Q = 0 := by
      by_contra hQ
      exact hboth (Or.inr hQ)
    have hA0 : A = 0 := by linarith
    have hB0 : B = 0 := by linarith
    cases hAB <;> contradiction
  have habs (a b : ℝ) : |a| - |b| ≤ |a + b| := by
    have h := abs_add_le (a + b) (-b)
    have h' : |a| ≤ |a + b| + |b| := by
      simpa [add_neg_cancel_right, abs_neg] using h
    linarith
  by_cases hP : P = 0
  · have hQ : Q ≠ 0 := by
      cases hPQ with
      | inl h => exact absurd hP h
      | inr h => exact h
    have hpos : 0 < (|C| + 1) / |Q| := by
      have : 0 < |Q| := abs_pos.mpr hQ
      positivity
    let y : ℝ := Real.log ((|C| + 1) / |Q|)
    have hy : Real.exp y = (|C| + 1) / |Q| := Real.exp_log hpos
    refine ⟨-y / κ, ?_⟩
    have ht : κ * (-y / κ) = -y := by
      field_simp
    rw [hyperbolicMismatch_eq_exp, ht]
    rw [show (A + B) / 2 = P by rfl, show (A - B) / 2 = Q by rfl, hP]
    simp only [neg_neg, zero_mul, zero_add]
    rw [abs_mul, abs_of_pos (Real.exp_pos y), hy]
    have hscale : |Q| * ((|C| + 1) / |Q|) = |C| + 1 := by
      field_simp
    linarith [le_abs_self C, hscale]
  · set target := (|C| + |Q| + 1) / |P|
    have htarget : 0 < target := by
      have : 0 < |C| + |Q| + 1 := by positivity
      exact div_pos this (abs_pos.mpr hP)
    have hpos : 0 < target + 1 := by linarith
    let y : ℝ := Real.log (target + 1)
    have hy : Real.exp y = target + 1 := Real.exp_log hpos
    have hypos : 0 < y := by
      have hgt : Real.exp 0 < Real.exp y := by
        rw [Real.exp_zero, hy]
        linarith
      exact Real.exp_lt_exp.mp hgt
    refine ⟨y / κ, ?_⟩
    have ht : κ * (y / κ) = y := by
      field_simp
    rw [hyperbolicMismatch_eq_exp, ht]
    have hlower :
        |P| * Real.exp y - |Q| * Real.exp (-y) ≤
          |P * Real.exp y + Q * Real.exp (-y)| := by
      simpa [abs_mul, abs_of_pos (Real.exp_pos y), abs_of_pos (Real.exp_pos (-y))] using
        habs (P * Real.exp y) (Q * Real.exp (-y))
    have hexp_le : Real.exp (-y) ≤ 1 := by
      have : -y ≤ 0 := by linarith
      exact (Real.exp_le_exp.mpr this).trans_eq Real.exp_zero
    have hgrow : |C| < |P| * Real.exp y - |Q| * Real.exp (-y) := by
      have hstep : |C| + |Q| < |P| * Real.exp y := by
        rw [hy]
        have : |P| * ((|C| + |Q| + 1) / |P| + 1) = |C| + |Q| + 1 + |P| := by
          field_simp
        linarith [abs_pos.mpr hP]
      have hQle : |Q| * Real.exp (-y) ≤ |Q| := by
        nlinarith [abs_nonneg Q, hexp_le]
      linarith
    linarith [le_abs_self C]

end Gravity

end DstDiophantine
