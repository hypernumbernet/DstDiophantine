import DoubleSpacetime.Logic.Quantum.PhaseFisher
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Fisher information of a chart displacement

`PhaseFisher` reads the projective Fisher information of a dimensionless relative phase. A chart
displacement along axis `μ` advances that phase at the rate `(q − p) μ`. The common plane-wave
phase is a `U(1)` factor, and the projective metric drops it. The chart Fisher information is

`chartFisher_μ(θ) = phaseFisher(θ) · ((q − p) μ)²`.

At a quadrature phase this is the carrier deficit times the squared momentum split. It is `0` on
every axis when the two momenta agree, even if the phase information is `1`. It repeats after one
fringe period, while `positionOp` multiplies by a different coordinate.

Mean rest, mass 3: the time component of the relative momentum vanishes, so the time-axis chart
Fisher information is `0`, while the quadrature phase Fisher information is `544/625`. Axis `1`
reads `34816/625`, which is not `64 · 81/625`. Rest against `(5, 4, 0, 0)`: the time axis reads
`324/289` at quadrature, and `324/841` and `324/25` at the extreme times. The opposite Weyl seed
reads `64` on axis `1`. `ChartScore` multiplies that number by the Born density and obtains the
squared length of a vector orthogonal to the state. `positionOp` multiplies the state by the
coordinate.
-/

namespace DoubleSpacetime

namespace Logic

open Complex Filter InnerProductSpace

/-! ### The packet is a common phase times the relative curve -/

/-- Carrier at a common phase `φ` and a relative phase `θ`. -/
noncomputable def chartState (r s : ℝ) (u v : DiracSpinor) (φ θ : ℝ) : DiracSpinor :=
  exp (I * (φ : ℂ)) • phaseCurve r s u v θ

theorem shellPacket_eq_chartState (r s α : ℝ) (p q : Vec4) (u v : DiracSpinor) (x : Vec4) :
    shellPacket r s α p q u v x =
      chartState r s u v (wavePhase p x) (wavePhase (q - p) x + α) := by
  unfold chartState shellPacket phaseCurve planeWave
  have hsum : wavePhase p x + (wavePhase (q - p) x + α) = wavePhase q x + α := by
    rw [wavePhase_sub_left]
    ring
  have hphase :
      exp (I * (wavePhase p x : ℂ)) * exp (I * ((wavePhase (q - p) x + α : ℝ) : ℂ)) =
        exp (I * (α : ℂ)) * exp (I * (wavePhase q x : ℂ)) := by
    rw [← exp_add, ← exp_add]
    congr 1
    have hcast :
        (wavePhase p x : ℂ) + ((wavePhase (q - p) x + α : ℝ) : ℂ) =
          (α : ℂ) + (wavePhase q x : ℂ) := by
      rw [← ofReal_add, hsum, ofReal_add, add_comm]
    rw [← mul_add, ← mul_add, hcast]
  rw [smul_add, smul_smul, smul_smul, smul_smul, smul_smul]
  refine congr_arg₂ (fun a b => a + b) ?_ ?_
  · apply congrArg (fun z : ℂ => z • u)
    ring
  · apply congrArg (fun z : ℂ => z • v)
    calc
      (s : ℂ) * exp (I * (α : ℂ)) * exp (I * (wavePhase q x : ℂ)) =
          exp (I * (α : ℂ)) * exp (I * (wavePhase q x : ℂ)) * (s : ℂ) := by ring
      _ = exp (I * (wavePhase p x : ℂ)) *
            exp (I * ((wavePhase (q - p) x + α : ℝ) : ℂ)) * (s : ℂ) := by rw [← hphase]
      _ = exp (I * (wavePhase p x : ℂ)) *
            (exp (I * ((wavePhase (q - p) x + α : ℝ) : ℂ)) * (s : ℂ)) := by ring

theorem wavePhase_axis (p : Vec4) (μ : Fin 4) (x : Vec4) (t : ℝ) :
    wavePhase p (x + t • Pi.single μ (1 : ℝ)) = wavePhase p x + t * p μ := by
  rw [wavePhase_add_right, wavePhase_smul_right, wavePhase_single]

theorem shellPacket_axis (r s α : ℝ) (p q : Vec4) (u v : DiracSpinor) (μ : Fin 4) (x : Vec4)
    (t : ℝ) :
    shellPacket r s α p q u v (x + t • Pi.single μ (1 : ℝ)) =
      chartState r s u v (wavePhase p x + t * p μ)
        (wavePhase (q - p) x + α + t * (q - p) μ) := by
  rw [shellPacket_eq_chartState, wavePhase_axis, wavePhase_axis, add_right_comm]

theorem chartState_normSq (r s : ℝ) (u v : DiracSpinor) (φ θ : ℝ) :
    ‖chartState r s u v φ θ‖ ^ 2 = phaseCurveNormSq r s u v θ := by
  unfold chartState
  rw [norm_smul, norm_exp_I, one_mul, phaseCurve_normSq_eq]

theorem shellPacket_ne_zero_of_normSq {r s α : ℝ} {p q : Vec4} {u v : DiracSpinor} {x : Vec4}
    (hden : phaseCurveNormSq r s u v (wavePhase (q - p) x + α) ≠ 0) :
    shellPacket r s α p q u v x ≠ 0 := by
  intro hz
  have hsq : ‖shellPacket r s α p q u v x‖ ^ 2 = 0 := by simp [hz]
  rw [shellPacket_eq_chartState, chartState_normSq] at hsq
  exact hden hsq

/-! ### The axis derivative drops the common phase -/

/-- Velocity of `e^{i(φ + t speed)} χ(θ + t rel)` at `t = 0`. -/
noncomputable def chartVelocity (r s : ℝ) (u v : DiracSpinor) (φ θ speed rel : ℝ) :
    DiracSpinor :=
  (I * (speed : ℂ) * exp (I * (φ : ℂ))) • phaseCurve r s u v θ +
    ((rel : ℂ) * exp (I * (φ : ℂ))) • phaseCurveDeriv r s u v θ

private theorem hasDerivAt_phaseFactor (a b : ℝ) :
    HasDerivAt (fun t : ℝ => exp (I * ((a + t * b : ℝ) : ℂ)))
      (exp (I * (a : ℂ)) * (I * (b : ℂ))) 0 := by
  have hid : HasDerivAt (fun t : ℝ => t * b) b 0 := by
    have h := (hasDerivAt_id (0 : ℝ)).mul_const b
    convert h using 1
    · ext t
      simp [id]
    · simp
  have hlin := (hasDerivAt_const (0 : ℝ) a).add hid
  have hexp := (hlin.ofReal_comp.const_mul I).cexp
  convert hexp using 1
  simp [zero_mul, add_zero]

private theorem hasDerivAt_phaseCurve (r s : ℝ) (u v : DiracSpinor) (θ rel : ℝ) :
    HasDerivAt (fun t : ℝ => phaseCurve r s u v (θ + t * rel))
      ((rel : ℂ) • phaseCurveDeriv r s u v θ) 0 := by
  have hexp := hasDerivAt_phaseFactor θ rel
  have hsecond := hexp.smul_const ((s : ℂ) • v)
  have hfirst : HasDerivAt (fun _ : ℝ => (r : ℂ) • u) 0 0 := hasDerivAt_const 0 _
  have hadd := hfirst.add hsecond
  have hvec :
      (0 : DiracSpinor) +
          (exp (I * (θ : ℂ)) * (I * (rel : ℂ))) • ((s : ℂ) • v) =
        (rel : ℂ) • phaseCurveDeriv r s u v θ := by
    rw [zero_add, phaseCurveDeriv, smul_smul, smul_smul]
    congr 1
    ring
  refine (hadd.congr_deriv hvec).congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
  simp only [Pi.add_apply]
  unfold phaseCurve
  rw [← smul_smul]

private theorem chartVelocity_expand (r s : ℝ) (u v : DiracSpinor) (φ θ speed rel : ℝ) :
    exp (I * (φ : ℂ)) • ((rel : ℂ) • phaseCurveDeriv r s u v θ) +
        (exp (I * (φ : ℂ)) * (I * (speed : ℂ))) • phaseCurve r s u v θ =
      chartVelocity r s u v φ θ speed rel := by
  rw [add_comm]
  unfold chartVelocity
  have h1 :
      (exp (I * (φ : ℂ)) * (I * (speed : ℂ))) • phaseCurve r s u v θ =
        (I * (speed : ℂ) * exp (I * (φ : ℂ))) • phaseCurve r s u v θ := by
    apply congrArg (fun z : ℂ => z • phaseCurve r s u v θ)
    ring
  have h2 :
      exp (I * (φ : ℂ)) • ((rel : ℂ) • phaseCurveDeriv r s u v θ) =
        ((rel : ℂ) * exp (I * (φ : ℂ))) • phaseCurveDeriv r s u v θ := by
    rw [smul_smul]
    apply congrArg (fun z : ℂ => z • phaseCurveDeriv r s u v θ)
    ring
  rw [h1, h2]

theorem hasDerivAt_chartState (r s : ℝ) (u v : DiracSpinor) (φ θ speed rel : ℝ) :
    HasDerivAt (fun t : ℝ => chartState r s u v (φ + t * speed) (θ + t * rel))
      (chartVelocity r s u v φ θ speed rel) 0 := by
  have hz := hasDerivAt_phaseFactor φ speed
  have hχ := hasDerivAt_phaseCurve r s u v θ rel
  refine (hz.smul hχ).congr_deriv ?_
  simp only [zero_mul, add_zero]
  exact chartVelocity_expand r s u v φ θ speed rel

theorem hasDerivAt_shellPacket_axis (r s α : ℝ) (p q : Vec4) (u v : DiracSpinor) (μ : Fin 4)
    (x : Vec4) :
    HasDerivAt (fun t : ℝ =>
        shellPacket r s α p q u v (x + t • Pi.single μ (1 : ℝ)))
      (chartVelocity r s u v (wavePhase p x) (wavePhase (q - p) x + α) (p μ)
        ((q - p) μ)) 0 := by
  refine (hasDerivAt_chartState r s u v (wavePhase p x) (wavePhase (q - p) x + α)
      (p μ) ((q - p) μ)).congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
  exact shellPacket_axis r s α p q u v μ x t

/-! ### The projective metric is the phase metric times the squared rate -/

private theorem projectiveNum_parallel (χ u : DiracSpinor) (lam : ℂ) :
    ‖lam • χ + u‖ ^ 2 * ‖χ‖ ^ 2 - ‖inner ℂ χ (lam • χ + u)‖ ^ 2 =
      ‖u‖ ^ 2 * ‖χ‖ ^ 2 - ‖inner ℂ χ u‖ ^ 2 := by
  set n : ℝ := ‖χ‖ ^ 2
  set c : ℂ := inner ℂ χ u
  have hself : inner ℂ χ χ = (n : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]
    exact (Complex.ofReal_pow ‖χ‖ 2).symm
  have hleft : inner ℂ χ (lam • χ + u) = lam * (n : ℂ) + c := by
    rw [inner_add_right, inner_smul_right, hself]
  have hnorm : ‖lam • χ + u‖ ^ 2 =
      ‖lam‖ ^ 2 * n + ‖u‖ ^ 2 + 2 * (star lam * c).re := by
    rw [norm_add_sq (𝕜 := ℂ), norm_smul, mul_pow, inner_smul_left, starRingEnd_apply,
      RCLike.re_eq_complex_re]
    rw [show ‖χ‖ ^ 2 = n from rfl, show inner ℂ χ u = c from rfl]
    ring
  have hmod : ‖lam * (n : ℂ) + c‖ ^ 2 =
      ‖lam‖ ^ 2 * n ^ 2 + ‖c‖ ^ 2 + 2 * n * (star lam * c).re := by
    rw [← normSq_eq_norm_sq, normSq_add]
    have hlam : normSq (lam * (n : ℂ)) = ‖lam‖ ^ 2 * n ^ 2 := by
      rw [normSq_eq_norm_sq, norm_mul, mul_pow]
      have hn : ‖(n : ℂ)‖ = n :=
        (RCLike.norm_ofReal n).trans (abs_of_nonneg (sq_nonneg ‖χ‖))
      rw [hn]
    have hcross : (lam * (n : ℂ) * starRingEnd ℂ c).re = n * (star lam * c).re := by
      have hcomm : lam * (n : ℂ) * starRingEnd ℂ c = (n : ℂ) * (lam * starRingEnd ℂ c) := by ring
      rw [hcomm, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, starRingEnd_apply]
      have hre : (lam * star c).re = (star lam * c).re := by
        simp [Complex.conj_re]
      rw [hre]
      ring
    rw [hlam, normSq_eq_norm_sq, hcross]
    ring
  rw [hleft, hnorm, hmod]
  ring

private theorem projectiveNum_real_smul (χ u : DiracSpinor) (t : ℝ) :
    ‖(t : ℂ) • u‖ ^ 2 * ‖χ‖ ^ 2 - ‖inner ℂ χ ((t : ℂ) • u)‖ ^ 2 =
      t ^ 2 * (‖u‖ ^ 2 * ‖χ‖ ^ 2 - ‖inner ℂ χ u‖ ^ 2) := by
  rw [norm_smul, inner_smul_right, norm_mul]
  have ht : ‖(t : ℂ)‖ = |t| := RCLike.norm_ofReal t
  rw [ht, mul_pow, mul_pow, sq_abs]
  ring

private theorem rotate_norm (z : ℂ) (hz : ‖z‖ = 1) (a : DiracSpinor) : ‖z • a‖ = ‖a‖ := by
  rw [norm_smul, hz, one_mul]

private theorem rotate_inner (z : ℂ) (hz : ‖z‖ = 1) (a b : DiracSpinor) :
    inner ℂ (z • a) (z • b) = inner ℂ a b := by
  rw [inner_smul_left, inner_smul_right, ← mul_assoc]
  have hzz : starRingEnd ℂ z * z = 1 := by
    rw [starRingEnd_apply, Complex.star_def, RCLike.conj_mul, hz]
    norm_num
  rw [hzz, one_mul]

theorem chartVelocity_numerator (r s : ℝ) (u v : DiracSpinor) (φ θ speed rel : ℝ) :
    ‖chartVelocity r s u v φ θ speed rel‖ ^ 2 * ‖chartState r s u v φ θ‖ ^ 2 -
        ‖inner ℂ (chartState r s u v φ θ) (chartVelocity r s u v φ θ speed rel)‖ ^ 2 =
      rel ^ 2 * phaseFisherNum r s u v := by
  set χ : DiracSpinor := phaseCurve r s u v θ
  set χ' : DiracSpinor := phaseCurveDeriv r s u v θ
  set z : ℂ := exp (I * (φ : ℂ))
  have hz : ‖z‖ = 1 := norm_exp_I φ
  have hw : chartVelocity r s u v φ θ speed rel = z • ((I * (speed : ℂ)) • χ + (rel : ℂ) • χ') := by
    unfold chartVelocity
    rw [smul_add, smul_smul, smul_smul]
    dsimp only [z, χ, χ']
    refine congr_arg₂ (fun a b => a + b) ?_ ?_
    · apply congrArg (fun w : ℂ => w • χ)
      ring
    · apply congrArg (fun w : ℂ => w • χ')
      ring
  have hstate : chartState r s u v φ θ = z • χ := rfl
  rw [hw, hstate, rotate_norm z hz, rotate_norm z hz, rotate_inner z hz]
  have hpar := projectiveNum_parallel χ ((rel : ℂ) • χ') (I * (speed : ℂ))
  rw [hpar, projectiveNum_real_smul, phaseCurve_numerator]

/-- Fisher information of a displacement whose relative-phase rate is `δ μ`. -/
noncomputable def chartFisher (r s : ℝ) (u v : DiracSpinor) (δ : Vec4) (μ : Fin 4) (θ : ℝ) : ℝ :=
  phaseFisher r s u v θ * (δ μ) ^ 2

theorem chartFisher_eq_velocity (r s : ℝ) (u v : DiracSpinor) (φ θ speed : ℝ) (δ : Vec4)
    (μ : Fin 4) (hden : phaseCurveNormSq r s u v θ ≠ 0) :
    4 * (‖chartVelocity r s u v φ θ speed (δ μ)‖ ^ 2 * ‖chartState r s u v φ θ‖ ^ 2 -
          ‖inner ℂ (chartState r s u v φ θ) (chartVelocity r s u v φ θ speed (δ μ))‖ ^ 2) /
        ‖chartState r s u v φ θ‖ ^ 4 =
      chartFisher r s u v δ μ θ := by
  rw [chartVelocity_numerator]
  have hpow : ‖chartState r s u v φ θ‖ ^ 4 = phaseCurveNormSq r s u v θ ^ 2 := by
    rw [show ‖chartState r s u v φ θ‖ ^ 4 = (‖chartState r s u v φ θ‖ ^ 2) ^ 2 by ring,
      chartState_normSq]
  unfold chartFisher phaseFisher
  rw [hpow]
  field_simp [hden]

theorem chartFisher_quadrature {r s : ℝ} {u v : DiracSpinor} {δ : Vec4} {μ : Fin 4} {θ : ℝ}
    (hcross : phaseCross r s u v θ = 0) (hden : phaseCurveNormSq r s u v θ ≠ 0) :
    chartFisher r s u v δ μ θ = shellDeficit r s u v * (δ μ) ^ 2 := by
  rw [chartFisher, phaseFisher_quadrature hcross hden]

theorem chartFisher_of_zero_component {δ : Vec4} {μ : Fin 4} (hμ : δ μ = 0) (r s : ℝ)
    (u v : DiracSpinor) (θ : ℝ) :
    chartFisher r s u v δ μ θ = 0 := by
  unfold chartFisher
  rw [hμ]
  simp

theorem phaseCross_add_two_pi (r s : ℝ) (u v : DiracSpinor) (θ : ℝ) :
    phaseCross r s u v (θ + 2 * Real.pi) = phaseCross r s u v θ := by
  unfold phaseCross
  have hper : exp ((((θ : ℂ) + (2 * Real.pi : ℂ)) * I)) = exp ((θ : ℂ) * I) :=
    Complex.exp_mul_I_periodic (θ : ℂ)
  have hleft : I * ((θ + 2 * Real.pi : ℝ) : ℂ) = ((θ : ℂ) + (2 * Real.pi : ℂ)) * I := by
    push_cast
    ring
  have hright : I * (θ : ℂ) = (θ : ℂ) * I := by ring
  rw [hleft, hright, hper]

theorem phaseFisher_add_two_pi (r s : ℝ) (u v : DiracSpinor) (θ : ℝ) :
    phaseFisher r s u v (θ + 2 * Real.pi) = phaseFisher r s u v θ := by
  unfold phaseFisher phaseCurveNormSq
  rw [phaseCross_add_two_pi]

theorem chartFisher_add_two_pi (r s : ℝ) (u v : DiracSpinor) (δ : Vec4) (μ : Fin 4) (θ : ℝ) :
    chartFisher r s u v δ μ (θ + 2 * Real.pi) = chartFisher r s u v δ μ θ := by
  unfold chartFisher
  rw [phaseFisher_add_two_pi]

theorem sameMomentum_chartFisher {r : ℝ} (hr : r ≠ 0) (u : DiracSpinor) (p : Vec4) (μ : Fin 4)
    (θ : ℝ) :
    phaseInformation r r = 1 ∧ chartFisher r r u u (p - p) μ θ = 0 := by
  refine ⟨phaseInformation_equal hr, ?_⟩
  unfold chartFisher
  rw [sub_self]
  simp

/-! ### One fringe period does not move the information -/

/-- Chart point displaced by `t` along axis `μ`. -/
noncomputable def axisShift (x : Vec4) (μ : Fin 4) (t : ℝ) : Vec4 :=
  x + t • Pi.single μ (1 : ℝ)

theorem axisShift_coord (x : Vec4) (μ : Fin 4) (t : ℝ) :
    axisShift x μ t μ = x μ + t := by
  simp [axisShift, Pi.add_apply, Pi.smul_apply, Pi.single_eq_same]

theorem fringeShift_phase {δ : Vec4} {μ : Fin 4} (hμ : δ μ ≠ 0) (x : Vec4) :
    wavePhase δ (axisShift x μ (2 * Real.pi / δ μ)) =
      wavePhase δ x + 2 * Real.pi := by
  rw [axisShift, wavePhase_add_right, wavePhase_smul_right, wavePhase_single]
  have hτ : (2 * Real.pi / δ μ) * δ μ = 2 * Real.pi := div_mul_cancel₀ (2 * Real.pi) hμ
  rw [hτ]

theorem fringeShift_coord {δ : Vec4} {μ : Fin 4} (hμ : δ μ ≠ 0) (x : Vec4) :
    axisShift x μ (2 * Real.pi / δ μ) μ ≠ x μ := by
  have hτ : 2 * Real.pi / δ μ ≠ 0 :=
    div_ne_zero (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero) hμ
  intro h
  rw [axisShift_coord] at h
  exact hτ (by linarith)

theorem positionOp_fringe_ne (μ : Fin 4) (Ψ : Vec4 → DiracSpinor) (x : Vec4) {τ : ℝ}
    (hτ : τ ≠ 0) (hΨ : Ψ (axisShift x μ τ) ≠ 0) :
    positionOp μ Ψ (axisShift x μ τ) ≠ (x μ : ℂ) • Ψ (axisShift x μ τ) := by
  intro h
  have hy : axisShift x μ τ μ = x μ + τ := axisShift_coord x μ τ
  unfold positionOp at h
  rw [hy, ← sub_eq_zero, ← sub_smul, ← ofReal_sub] at h
  have hsub : ((x μ + τ - x μ : ℝ) : ℂ) = (τ : ℂ) := by ring_nf
  rw [hsub] at h
  rcases smul_eq_zero.mp h with hτ0 | hψ
  · exact hτ (ofReal_eq_zero.mp hτ0)
  · exact hΨ hψ

theorem chartFisher_repeats_positionOp_splits (r s α : ℝ) (p q : Vec4) (u v : DiracSpinor)
    (μ : Fin 4) (hμ : (q - p) μ ≠ 0) (x : Vec4)
    (hΨ : shellPacket r s α p q u v (axisShift x μ (2 * Real.pi / (q - p) μ)) ≠ 0) :
    let δ := q - p
    let τ := 2 * Real.pi / δ μ
    let θ := wavePhase δ x + α
    chartFisher r s u v δ μ (θ + 2 * Real.pi) = chartFisher r s u v δ μ θ ∧
      wavePhase δ (axisShift x μ τ) + α = θ + 2 * Real.pi ∧
        axisShift x μ τ μ ≠ x μ ∧
          positionOp μ (shellPacket r s α p q u v) (axisShift x μ τ) ≠
            (x μ : ℂ) • shellPacket r s α p q u v (axisShift x μ τ) := by
  intro δ τ θ
  have hτ : τ ≠ 0 :=
    div_ne_zero (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero) hμ
  refine ⟨chartFisher_add_two_pi r s u v δ μ θ, ?_, fringeShift_coord hμ x,
      positionOp_fringe_ne μ (shellPacket r s α p q u v) x hτ hΨ⟩
  have hphase := fringeShift_phase hμ x
  rw [hphase]
  ring

/-! ### Mass 3 -/

theorem shellRest_relative :
    (shellRestQ - shellRestP) 0 = 0 ∧ (shellRestQ - shellRestP) 1 = -8 ∧
      (shellRestQ - shellRestP) 2 = 0 ∧ (shellRestQ - shellRestP) 3 = 0 := by
  refine ⟨shellRest_geometry.2.2.2.2.2.1, ?_, ?_, ?_⟩
  · simp [shellRestP, shellRestQ, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, Pi.single_eq_of_ne]
    norm_num
  · simp [shellRestP, shellRestQ, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, Pi.single_eq_of_ne]
  · simp [shellRestP, shellRestQ, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, Pi.single_eq_of_ne]

theorem shellLab_relative :
    (restMomentum 3 - shellRestP) 0 = -2 ∧ (restMomentum 3 - shellRestP) 1 = -4 ∧
      (restMomentum 3 - shellRestP) 2 = 0 ∧ (restMomentum 3 - shellRestP) 3 = 0 := by
  refine ⟨shellLab_geometry.2.1, ?_, ?_, ?_⟩
  all_goals
    simp [restMomentum, shellRestP, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, Pi.single_eq_same,
      Pi.single_eq_of_ne]

theorem abs_phaseCross_le (r s : ℝ) (u v : DiracSpinor) (θ : ℝ) :
    |phaseCross r s u v θ| ≤ ‖inner ℂ ((r : ℂ) • u) ((s : ℂ) • v)‖ := by
  unfold phaseCross
  calc
    |(exp (I * (θ : ℂ)) * inner ℂ ((r : ℂ) • u) ((s : ℂ) • v)).re| ≤
        ‖exp (I * (θ : ℂ)) * inner ℂ ((r : ℂ) • u) ((s : ℂ) • v)‖ := abs_re_le_norm _
    _ = ‖inner ℂ ((r : ℂ) • u) ((s : ℂ) • v)‖ := by
      rw [norm_mul, norm_exp_I, one_mul]

private theorem shellRest_amplitude :
    ‖inner ℂ (((1 : ℝ) : ℂ) • shellParticleP) (((1 : ℝ) : ℂ) • shellParticleQ)‖ = 2 := by
  rw [phaseAmplitude_norm, shellRest_fidelity]
  simp only [abs_one, one_mul]
  have hprod : ‖shellParticleP‖ * ‖shellParticleQ‖ = 50 / 9 := by
    have heq : ‖shellParticleP‖ = ‖shellParticleQ‖ :=
      (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
        (shellRest_norms.1.trans shellRest_norms.2.symm)
    rw [heq, ← sq, shellRest_norms.2]
  calc
    (9 / 25) * ‖shellParticleP‖ * ‖shellParticleQ‖ =
        (9 / 25) * (‖shellParticleP‖ * ‖shellParticleQ‖) := by ring
    _ = (9 / 25) * (50 / 9) := by rw [hprod]
    _ = 2 := by norm_num

theorem shellRest_curve_pos (θ : ℝ) :
    64 / 9 ≤ phaseCurveNormSq 1 1 shellParticleP shellParticleQ θ := by
  have habs := abs_phaseCross_le 1 1 shellParticleP shellParticleQ θ
  rw [shellRest_amplitude] at habs
  have hcross : -(4 : ℝ) ≤ 2 * phaseCross 1 1 shellParticleP shellParticleQ θ := by
    linarith [neg_le_of_abs_le habs]
  unfold phaseCurveNormSq
  rw [bornWeight_eq, bornWeight_eq]
  simp only [abs_one, one_mul, shellRest_norms.1, shellRest_norms.2]
  linarith

theorem shellRest_packet_ne_zero (α : ℝ) (x : Vec4) :
    shellPacket 1 1 α shellRestP shellRestQ shellParticleP shellParticleQ x ≠ 0 := by
  apply shellPacket_ne_zero_of_normSq
  exact ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 64 / 9) (shellRest_curve_pos _))

theorem shellRest_time_chartFisher (θ : ℝ) :
    chartFisher 1 1 shellParticleP shellParticleQ (shellRestQ - shellRestP) 0 θ = 0 :=
  chartFisher_of_zero_component shellRest_relative.1 1 1 shellParticleP shellParticleQ θ

theorem shellRest_chartFisher :
    (∃ θ : ℝ, phaseCross 1 1 shellParticleP shellParticleQ θ = 0 ∧
        phaseFisher 1 1 shellParticleP shellParticleQ θ = 544 / 625 ∧
          chartFisher 1 1 shellParticleP shellParticleQ (shellRestQ - shellRestP) 0 θ = 0 ∧
            chartFisher 1 1 shellParticleP shellParticleQ (shellRestQ - shellRestP) 1 θ =
              34816 / 625) ∧
      (81 / 625 : ℝ) * 64 = 5184 / 625 ∧ (5184 / 625 : ℝ) ≠ 34816 / 625 := by
  obtain ⟨θ, hcross, hF⟩ := shellRest_phaseFisher.1
  refine ⟨⟨θ, hcross, hF, shellRest_time_chartFisher θ, ?_⟩, by norm_num, by norm_num⟩
  unfold chartFisher
  rw [hF, shellRest_relative.2.1]
  norm_num

theorem shellRest_fringe_not_position (α : ℝ) (x : Vec4) :
    let δ := shellRestQ - shellRestP
    let τ := 2 * Real.pi / δ 1
    chartFisher 1 1 shellParticleP shellParticleQ δ 1
          (wavePhase δ x + α + 2 * Real.pi) =
        chartFisher 1 1 shellParticleP shellParticleQ δ 1 (wavePhase δ x + α) ∧
      axisShift x 1 τ 1 ≠ x 1 ∧
        positionOp 1 (shellPacket 1 1 α shellRestP shellRestQ shellParticleP shellParticleQ)
            (axisShift x 1 τ) ≠
          (x 1 : ℂ) •
            shellPacket 1 1 α shellRestP shellRestQ shellParticleP shellParticleQ
              (axisShift x 1 τ) := by
  have hμ : (shellRestQ - shellRestP) 1 ≠ 0 := by
    rw [shellRest_relative.2.1]
    norm_num
  have hsplit := chartFisher_repeats_positionOp_splits 1 1 α shellRestP shellRestQ
      shellParticleP shellParticleQ 1 hμ x (shellRest_packet_ne_zero α _)
  exact ⟨hsplit.1, hsplit.2.2.1, hsplit.2.2.2⟩

theorem shellLab_chartFisher :
    (∃ θ : ℝ, phaseCross 1 1 shellParticleP shellLabSpinor θ = 0 ∧
        chartFisher 1 1 shellParticleP shellLabSpinor (restMomentum 3 - shellRestP) 0 θ =
          324 / 289) ∧
      chartFisher 1 1 shellParticleP shellLabSpinor (restMomentum 3 - shellRestP) 0
          (wavePhase (restMomentum 3 - shellRestP) (timeShift 0)) = 324 / 841 ∧
        chartFisher 1 1 shellParticleP shellLabSpinor (restMomentum 3 - shellRestP) 0
            (wavePhase (restMomentum 3 - shellRestP) (timeShift (-Real.pi / 2))) = 324 / 25 := by
  obtain ⟨t, hcross, _, hF⟩ := shellLab_phaseFisher.2.2.1
  refine ⟨⟨wavePhase (restMomentum 3 - shellRestP) (timeShift t), hcross, ?_⟩, ?_, ?_⟩
  · unfold chartFisher
    rw [hF, shellLab_relative.1]
    norm_num
  · unfold chartFisher
    rw [shellLab_phaseFisher.1, shellLab_relative.1]
    norm_num
  · unfold chartFisher
    rw [shellLab_phaseFisher.2.1, shellLab_relative.1]
    norm_num

theorem shellOrth_chartFisher (θ : ℝ) :
    chartFisher 1 1 shellParticleP shellOrthQ (shellRestQ - shellRestP) 0 θ = 0 ∧
      chartFisher 1 1 shellParticleP shellOrthQ (shellRestQ - shellRestP) 1 θ = 64 := by
  have hF := (shellOrth_phaseFisher θ).1
  refine ⟨?_, ?_⟩
  · unfold chartFisher
    rw [hF, shellRest_relative.1]
    norm_num
  · unfold chartFisher
    rw [hF, shellRest_relative.2.1]
    norm_num

end Logic

end DoubleSpacetime
