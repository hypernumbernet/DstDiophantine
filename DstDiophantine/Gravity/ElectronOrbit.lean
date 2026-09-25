import DstDiophantine.Gravity.TorsionalLayer
import DstDiophantine.Gravity.ElectronShell
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Coulombic circular orbits and the equal-scale / Bohr mismatch

## Paper boundary (do **not** claim)

The characteristic length `ℓ`, the Bohr radius `a₀`, and the identification of
the electromagnetic channel with atomic shells are **not** theorems of the
dual-rotor algebra. This module records algebraic identities of the written
Coulombic force \(F=ke^2/(\gamma_s r^2)\) and of the equal-scale layer radii.

No theorem asserts `dst_derives_lambda` or a Rydberg \(n^2\) spectrum from
\(\gamma_s=0\).

## What is proved

* The first equal-scale node lies in \((\pi/4,\,1)\). Identifying that node
  with \(a_0\) forces \(\pi a_0/2<\lambda<2a_0\).
* Coulombic circular balance \(mv^2/r=ke^2/(\gamma_s r^2)\) yields a positive
  \(v^2\) only on attractive layers \(\gamma_s>0\). Repulsive layers give
  \(v^2<0\); a node makes the written force undefined.
* The outermost well \(0<x<x_1\) is attractive; the first inner interval
  \(x_1<x<\pi\) is repulsive. Barriers are force divergences, not clock freezes.
* Equal-scale \(r_2/r_1\in(1/6,\,4/(5\pi))\subset(0,1)\) cannot equal the Bohr
  ratio \(4\). The equal-scale tower is inward; Bohr shells are outward.
* \(Z\)-contraction is the algebraic identity \(\ell\mapsto Z\ell\) \(\iff\)
  \(r\mapsto r/Z\).
* The first node is a simple zero. On \([\pi/4,x_1)\) one has
  \(c_-(x_1-x)<\gamma_s(x)<c_+(x_1-x)\) with positive slopes built from
  \(\pi/4\) and \(1\). The layer integral of \(1/\gamma_s\) is therefore
  logarithmic, and it is unbounded as the upper limit approaches \(x_1\).
  The equal-scale Coulomb increment equals \(-(2ke^2/\lambda)\) times that
  integral, so the radial potential falls without a lower bound. The node
  is not a wall of finite height.
-/

namespace DstDiophantine

namespace Gravity

open Real Set SI

/-! ### First-root window and labelled characteristic length -/

/-- Combined first-root window: \(\pi/4<x_1<1\). -/
theorem firstNode_window :
    π / 4 < resonanceRoot1 ∧ resonanceRoot1 < 1 :=
  resonanceRoot1_sharp_bounds

/-- If the outermost node is placed at \(a_0\), then
\(\tfrac\pi2 a_0<\lambda<2a_0\). -/
theorem lambdaHyp_sharp_bounds :
    (π / 2) * (bohrRadiusApprox : ℝ) < lambdaHyp ∧
      lambdaHyp < 2 * (bohrRadiusApprox : ℝ) := by
  unfold lambdaHyp
  have ha0 : (0 : ℝ) < (bohrRadiusApprox : ℝ) := by exact_mod_cast bohrRadiusApprox_pos
  have hx := resonanceRoot1_sharp_bounds
  constructor
  · have : (π / 2) * (bohrRadiusApprox : ℝ) = 2 * (π / 4) * (bohrRadiusApprox : ℝ) := by
      ring
    rw [this]
    nlinarith [hx.1, ha0]
  · nlinarith [hx.2, ha0]

/-! ### Coulombic circular balance -/

/-- Written Coulombic force \(F=ke^2/(\gamma_s r^2)\). The sign of \(F\) is
the sign of \(\gamma_s\). -/
noncomputable def coulombForce (k e γs r : ℝ) : ℝ :=
  k * e ^ 2 / (γs * r ^ 2)

/-- Circular-orbit identity \(v^2=ke^2/(m\gamma_s r)\). -/
noncomputable def circularSpeedSq (k e m γs r : ℝ) : ℝ :=
  k * e ^ 2 / (m * γs * r)

theorem circularSpeedSq_eq_force_balance
    {k e m γs r : ℝ} (hm : m ≠ 0) (hr : r ≠ 0) :
    circularSpeedSq k e m γs r = coulombForce k e γs r * r / m := by
  unfold circularSpeedSq coulombForce
  have hr2 : r ^ 2 ≠ 0 := pow_ne_zero 2 hr
  field_simp [hm, hr, hr2]

/-- Attractive layers \(\gamma_s>0\) yield a real circular speed. -/
theorem circularSpeedSq_pos
    {k e m γs r : ℝ} (hk : 0 < k) (he : e ≠ 0) (hm : 0 < m)
    (hγ : 0 < γs) (hr : 0 < r) :
    0 < circularSpeedSq k e m γs r := by
  unfold circularSpeedSq
  exact div_pos (mul_pos hk (sq_pos_of_ne_zero he))
    (mul_pos (mul_pos hm hγ) hr)

/-- Repulsive layers \(\gamma_s<0\) make the written circular \(v^2\) negative. -/
theorem circularSpeedSq_neg_of_repulsive
    {k e m γs r : ℝ} (hk : 0 < k) (he : e ≠ 0) (hm : 0 < m)
    (hγ : γs < 0) (hr : 0 < r) :
    circularSpeedSq k e m γs r < 0 := by
  unfold circularSpeedSq
  have hnum : 0 < k * e ^ 2 := mul_pos hk (sq_pos_of_ne_zero he)
  have hden : m * γs * r < 0 := by
    have : m * γs < 0 := mul_neg_of_pos_of_neg hm hγ
    exact mul_neg_of_neg_of_pos this hr
  exact div_neg_of_pos_of_neg hnum hden

/-- The written force is undefined at a torsional node. -/
theorem coulombForce_denom_zero_at_node (r γs : ℝ) (hγ : γs = 0) :
    γs * r ^ 2 = 0 := by
  simp [hγ]

theorem circularSpeedSq_coulomb_limit (k e m r : ℝ) :
    circularSpeedSq k e m 1 r = k * e ^ 2 / (m * r) := by
  unfold circularSpeedSq
  ring

/-! ### Sign of the outermost well -/

theorem gammaSEqual_pos_left_of_first_node {x : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) resonanceRoot1) :
    0 < gammaSEqual x := by
  obtain ⟨h0, hx1⟩ := hx
  have hxIcc : x ∈ Icc (0 : ℝ) π :=
    ⟨h0.le, le_of_lt (lt_trans hx1 (lt_trans resonanceRoot1_sharp_bounds.2
      (by linarith [pi_gt_three] : (1 : ℝ) < π)))⟩
  have hrootIcc : resonanceRoot1 ∈ Icc (0 : ℝ) π :=
    ⟨le_of_lt (lt_trans (by norm_num : (0 : ℝ) < 1 / 2) resonanceRoot1_bounds.1),
      le_of_lt (lt_trans resonanceRoot1_sharp_bounds.2
        (by linarith [pi_gt_three] : (1 : ℝ) < π))⟩
  have hanti := strictAntiOn_gammaSEqual_even 0
  have hlt := hanti (by simpa using hxIcc) (by simpa using hrootIcc) hx1
  rw [resonanceRoot1_gammaSEqual_zero] at hlt
  exact hlt

theorem gammaSEqual_neg_right_of_first_node {x : ℝ}
    (hx : x ∈ Ioo resonanceRoot1 π) :
    gammaSEqual x < 0 := by
  obtain ⟨hx1, hπ⟩ := hx
  have hxIcc : x ∈ Icc (0 : ℝ) π :=
    ⟨le_of_lt (lt_trans (by positivity : (0 : ℝ) < π / 4)
        (lt_trans resonanceRoot1_sharp_bounds.1 hx1)), hπ.le⟩
  have hrootIcc : resonanceRoot1 ∈ Icc (0 : ℝ) π :=
    ⟨le_of_lt (lt_trans (by positivity : (0 : ℝ) < π / 4)
        resonanceRoot1_sharp_bounds.1),
      le_of_lt (lt_trans resonanceRoot1_sharp_bounds.2
        (by linarith [pi_gt_three] : (1 : ℝ) < π))⟩
  have hanti := strictAntiOn_gammaSEqual_even 0
  have hlt := hanti (by simpa using hrootIcc) (by simpa using hxIcc) hx1
  rw [resonanceRoot1_gammaSEqual_zero] at hlt
  exact hlt

/-- A Coulombic node is a force divergence, not a clock freeze. -/
theorem node_is_force_divergence_not_clock_freeze {x : ℝ}
    (h : gammaSEqual x = 0) :
    gammaS (2 * x) (2 * x) = 0 ∧ 0 < gammaEff (2 * x) (2 * x) :=
  ⟨by rw [← gammaSEqual_eq_gammaS]; exact h, gammaEff_pos _ _⟩

/-! ### Inward equal-scale tower versus outward Bohr shells -/

theorem equalScale_first_second_ratio_window
    {x₂ : ℝ} (hx₂ : x₂ ∈ Ioo (π + π / 4) (π + π / 2)) :
    resonanceRoot1 / x₂ ∈ Ioo (1 / 6 : ℝ) (4 / (5 * π)) := by
  obtain ⟨hlo, hhi⟩ := resonanceRoot1_sharp_bounds
  simp only [mem_Ioo] at hx₂ ⊢
  have hx₂pos : (0 : ℝ) < x₂ := by linarith [pi_pos]
  constructor
  · rw [div_lt_div_iff₀ (by norm_num) hx₂pos]
    nlinarith [hlo, hx₂.2]
  · rw [div_lt_div_iff₀ hx₂pos (by positivity)]
    nlinarith [hhi, hx₂.1, pi_pos]

theorem exists_equalScale_ratio_in_sharp_window :
    ∃ x₂ : ℝ, x₂ ∈ Ioo (π + π / 4) (π + π / 2) ∧ gammaSEqual x₂ = 0 ∧
      resonanceRoot1 / x₂ ∈ Ioo (1 / 6 : ℝ) (4 / (5 * π)) := by
  obtain ⟨x₂, hx₂, hzero⟩ := exists_second_node_sharp
  exact ⟨x₂, hx₂, hzero, equalScale_first_second_ratio_window hx₂⟩

theorem equalScale_ratio_lt_one
    {x₂ : ℝ} (hx₂ : x₂ ∈ Ioo (π + π / 4) (π + π / 2)) :
    resonanceRoot1 / x₂ < 1 := by
  have h := equalScale_first_second_ratio_window hx₂
  have hπ := pi_pos
  have : (4 / (5 * π) : ℝ) < 1 := by
    rw [div_lt_iff₀ (by positivity)]
    nlinarith [pi_gt_three]
  exact lt_trans h.2 this

theorem bohrShellRadius_ratio_two :
    bohrShellRadius 2 / bohrShellRadius 1 = 4 := by
  unfold bohrShellRadius
  have ha0 : (bohrRadiusApprox : ℝ) ≠ 0 :=
    (by exact_mod_cast bohrRadiusApprox_pos : (0 : ℝ) < (bohrRadiusApprox : ℝ)).ne'
  field_simp [ha0]
  norm_num

/-- Equal-scale Coulombic nodes cannot reproduce the Bohr radius ratio. -/
theorem equalScale_ratio_ne_bohr
    {x₂ : ℝ} (hx₂ : x₂ ∈ Ioo (π + π / 4) (π + π / 2)) :
    resonanceRoot1 / x₂ ≠ bohrShellRadius 2 / bohrShellRadius 1 := by
  rw [bohrShellRadius_ratio_two]
  exact ne_of_lt (lt_trans (equalScale_ratio_lt_one hx₂) (by norm_num : (1 : ℝ) < 4))

/-! ### \(Z\)-contraction -/

/-- Scaling \(\ell\mapsto\ell/Z\) contracts every equal-scale radius by \(Z\).
The substitution \(\alpha,\beta\propto Z/r\) at fixed \(\ell\) is the inverse
scaling and moves nodes *outward* by \(Z\). Observed shell shrinkage is the
labelled identification \(\ell(Z)=\ell/Z\). -/
theorem Z_contracts_layerRadius {ℓ Z x : ℝ} (hZ : Z ≠ 0) :
    layerRadius (ℓ / Z) x = layerRadius ℓ x / Z := by
  unfold layerRadius
  field_simp [hZ]

/-- Inverse: \(\ell\mapsto Z\ell\) expands every equal-scale radius by \(Z\). -/
theorem Z_expands_layerRadius {ℓ Z x : ℝ} (hZ : Z ≠ 0) :
    layerRadius (Z * ℓ) x = Z * layerRadius ℓ x := by
  unfold layerRadius
  field_simp [hZ]

theorem Z_contraction_equalScale (ℓ Z r : ℝ) (hZ : Z ≠ 0) :
    equalScaleRapidity (Z * ℓ) r = equalScaleRapidity ℓ (r / Z) :=
  equalScale_Z_contraction ℓ Z r hZ

/-! ### A simple zero, and a logarithmic fall of the potential -/

open intervalIntegral

/-- Lower comparison slope \(2\cosh(\pi/4)\sin(\pi/4)\). -/
noncomputable def nodeSlopeLo : ℝ := 2 * cosh (π / 4) * sin (π / 4)

/-- Upper comparison slope \(2\cosh 1\sin 1\). -/
noncomputable def nodeSlopeHi : ℝ := 2 * cosh 1 * sin 1

theorem gammaSEqual_differentiable : Differentiable ℝ gammaSEqual :=
  fun x => (hasDerivAt_gammaSEqual x).differentiableAt

private theorem strictMonoOn_cosh_Ici : StrictMonoOn cosh (Ici 0) :=
  strictMonoOn_of_deriv_pos (convex_Ici 0) continuous_cosh.continuousOn fun x hx => by
    rw [interior_Ici] at hx
    have hderiv : deriv cosh x = sinh x := congrFun deriv_cosh x
    rw [hderiv]
    exact sinh_pos_iff.mpr hx

theorem nodeSlopeLo_pos : 0 < nodeSlopeLo := by
  unfold nodeSlopeLo
  refine mul_pos (mul_pos (by norm_num) (cosh_pos _)) ?_
  exact sin_pos_of_mem_Ioo ⟨by positivity, by linarith [pi_gt_three]⟩

theorem nodeSlopeHi_pos : 0 < nodeSlopeHi := by
  unfold nodeSlopeHi
  refine mul_pos (mul_pos (by norm_num) (cosh_pos _)) ?_
  exact sin_pos_of_mem_Ioo ⟨by positivity, by linarith [pi_gt_three]⟩

/-- On \((\pi/4,1)\) the derivative sits strictly between the two slopes. -/
theorem deriv_gammaSEqual_slope_bounds {ξ : ℝ} (hξ : ξ ∈ Ioo (π / 4) 1) :
    -nodeSlopeHi < deriv gammaSEqual ξ ∧ deriv gammaSEqual ξ < -nodeSlopeLo := by
  rw [deriv_gammaSEqual]
  have h1 : (1 : ℝ) < π / 2 := by linarith [pi_gt_three]
  have hξI : ξ ∈ Icc (-(π / 2)) (π / 2) :=
    ⟨by linarith [pi_pos, hξ.1], le_of_lt (lt_trans hξ.2 h1)⟩
  have hquarter : (π / 4) ∈ Icc (-(π / 2)) (π / 2) :=
    ⟨by linarith [pi_pos], by linarith [pi_gt_three]⟩
  have hone : (1 : ℝ) ∈ Icc (-(π / 2)) (π / 2) := ⟨by linarith [pi_pos], h1.le⟩
  have hsin_lo : sin (π / 4) < sin ξ := strictMonoOn_sin hquarter hξI hξ.1
  have hsin_hi : sin ξ < sin 1 := strictMonoOn_sin hξI hone hξ.2
  have hcosh_lo : cosh (π / 4) < cosh ξ :=
    strictMonoOn_cosh_Ici (le_of_lt (by positivity : (0 : ℝ) < π / 4))
      (le_of_lt (lt_trans (by positivity) hξ.1)) hξ.1
  have hcosh_hi : cosh ξ < cosh 1 :=
    strictMonoOn_cosh_Ici (le_of_lt (lt_trans (by positivity) hξ.1)) (by norm_num) hξ.2
  have hsinpos : 0 < sin ξ :=
    sin_pos_of_mem_Ioo ⟨lt_trans (by positivity) hξ.1, lt_trans hξ.2 (by linarith [pi_gt_three])⟩
  have hprod_lo : cosh (π / 4) * sin (π / 4) < cosh ξ * sin ξ := by
    calc cosh (π / 4) * sin (π / 4)
        < cosh ξ * sin (π / 4) := mul_lt_mul_of_pos_right hcosh_lo
            (sin_pos_of_mem_Ioo ⟨by positivity, by linarith [pi_gt_three]⟩)
      _ < cosh ξ * sin ξ := mul_lt_mul_of_pos_left hsin_lo (cosh_pos _)
  have hprod_hi : cosh ξ * sin ξ < cosh 1 * sin 1 := by
    calc cosh ξ * sin ξ
        < cosh 1 * sin ξ := mul_lt_mul_of_pos_right hcosh_hi hsinpos
      _ < cosh 1 * sin 1 := mul_lt_mul_of_pos_left hsin_hi (cosh_pos _)
  constructor
  · unfold nodeSlopeHi
    linarith
  · unfold nodeSlopeLo
    linarith

theorem gammaSEqual_pos_of_lt_firstNode {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < resonanceRoot1) :
    0 < gammaSEqual x := by
  rcases eq_or_lt_of_le hx0 with rfl | hx
  · simp [gammaSEqual_zero]
  · exact gammaSEqual_pos_left_of_first_node ⟨hx, hx1⟩

/-- Simple-zero comparison on the approach to the first node. -/
theorem gammaSEqual_linear_firstNode {x : ℝ} (hx : x ∈ Ico (π / 4) resonanceRoot1) :
    nodeSlopeLo * (resonanceRoot1 - x) < gammaSEqual x ∧
      gammaSEqual x < nodeSlopeHi * (resonanceRoot1 - x) := by
  have hx1 : π / 4 < resonanceRoot1 := resonanceRoot1_sharp_bounds.1
  have hxlt : x < resonanceRoot1 := hx.2
  let D := Icc (π / 4) resonanceRoot1
  have hD : Convex ℝ D := convex_Icc _ _
  have hxD : x ∈ D := ⟨hx.1, hxlt.le⟩
  have hyD : resonanceRoot1 ∈ D := ⟨hx1.le, le_rfl⟩
  have hint : ∀ ξ ∈ interior D, -nodeSlopeHi < deriv gammaSEqual ξ ∧
      deriv gammaSEqual ξ < -nodeSlopeLo := by
    intro ξ hξ
    rw [interior_Icc] at hξ
    exact deriv_gammaSEqual_slope_bounds
      ⟨hξ.1, lt_trans hξ.2 resonanceRoot1_sharp_bounds.2⟩
  have hcont : ContinuousOn gammaSEqual D := continuous_gammaSEqual.continuousOn
  have hdiff : DifferentiableOn ℝ gammaSEqual (interior D) :=
    gammaSEqual_differentiable.differentiableOn
  have hlo := hD.image_sub_lt_mul_sub_of_deriv_lt hcont hdiff
    (fun ξ hξ => (hint ξ hξ).2) x hxD resonanceRoot1 hyD hxlt
  have hhi := hD.mul_sub_lt_image_sub_of_lt_deriv hcont hdiff
    (fun ξ hξ => (hint ξ hξ).1) x hxD resonanceRoot1 hyD hxlt
  rw [resonanceRoot1_gammaSEqual_zero] at hlo hhi
  constructor
  · linarith
  · linarith

private theorem integral_inv_gap {a b c : ℝ} (hab : a < b) (hbc : b < c) :
    ∫ x in a..b, (1 / (c - x)) = log ((c - a) / (c - b)) := by
  have hsub : ∫ x in a..b, (1 / (c - x)) = ∫ u in c - b..c - a, (1 / u) :=
    integral_comp_sub_left (fun u : ℝ => 1 / u) c
  rw [hsub]
  exact integral_one_div_of_pos (by linarith) (by linarith)

private theorem integral_inv_mul_factor (c d a b : ℝ) (hc : c ≠ 0) :
    ∫ x in a..b, 1 / (c * (d - x)) = (1 / c) * ∫ x in a..b, 1 / (d - x) := by
  have hfun : (fun x => 1 / (c * (d - x))) = fun x => (1 / c) * (1 / (d - x)) := by
    funext x
    field_simp [hc]
  rw [hfun, intervalIntegral.integral_const_mul]

private theorem continuousOn_inv_slope_gap {c d a b : ℝ} (hc : 0 < c)
    (hgap : ∀ x ∈ Icc a b, 0 < d - x) :
    ContinuousOn (fun x => 1 / (c * (d - x))) (Icc a b) := by
  refine continuousOn_const.div
    (continuousOn_const.mul (continuousOn_const.sub continuousOn_id))
    fun x hx => (mul_pos hc (hgap x hx)).ne'

/-- The layer integral of \(1/\gamma_s\) grows exactly like a logarithm. -/
theorem firstNode_layer_integral_log_bounds {a b : ℝ} (ha : π / 4 ≤ a) (hab : a < b)
    (hb : b < resonanceRoot1) :
    (1 / nodeSlopeHi) * log ((resonanceRoot1 - a) / (resonanceRoot1 - b)) ≤
        ∫ x in a..b, (1 / gammaSEqual x) ∧
      ∫ x in a..b, (1 / gammaSEqual x) ≤
        (1 / nodeSlopeLo) * log ((resonanceRoot1 - a) / (resonanceRoot1 - b)) := by
  have hposγ : ∀ x ∈ Icc a b, 0 < gammaSEqual x := fun x hx =>
    gammaSEqual_pos_of_lt_firstNode
      (le_trans (le_of_lt (by positivity : (0 : ℝ) < π / 4)) (ha.trans hx.1))
      (lt_of_le_of_lt hx.2 hb)
  have hlin : ∀ x ∈ Icc a b,
      nodeSlopeLo * (resonanceRoot1 - x) < gammaSEqual x ∧
        gammaSEqual x < nodeSlopeHi * (resonanceRoot1 - x) := fun x hx =>
    gammaSEqual_linear_firstNode ⟨ha.trans hx.1, lt_of_le_of_lt hx.2 hb⟩
  have hgap : ∀ x ∈ Icc a b, 0 < resonanceRoot1 - x := fun x hx => by
    linarith [hx.2, hb]
  have hinv : ∀ x ∈ Icc a b,
      1 / (nodeSlopeHi * (resonanceRoot1 - x)) ≤ 1 / gammaSEqual x ∧
        1 / gammaSEqual x ≤ 1 / (nodeSlopeLo * (resonanceRoot1 - x)) := by
    intro x hx
    obtain ⟨hlo, hhi⟩ := hlin x hx
    have hγ := hposγ x hx
    have hslo := nodeSlopeLo_pos
    have hshi := nodeSlopeHi_pos
    have hdenlo : 0 < nodeSlopeLo * (resonanceRoot1 - x) := mul_pos hslo (hgap x hx)
    have hdenhi : 0 < nodeSlopeHi * (resonanceRoot1 - x) := mul_pos hshi (hgap x hx)
    constructor
    · exact (one_div_lt_one_div_of_lt hγ hhi).le
    · exact (one_div_lt_one_div_of_lt hdenlo hlo).le
  have hcontγ : ContinuousOn (fun x => 1 / gammaSEqual x) (Icc a b) :=
    continuousOn_const.div continuous_gammaSEqual.continuousOn fun x hx => (hposγ x hx).ne'
  have hcontHi := continuousOn_inv_slope_gap nodeSlopeHi_pos hgap
  have hcontLo := continuousOn_inv_slope_gap nodeSlopeLo_pos hgap
  have hintγ := hcontγ.intervalIntegrable_of_Icc (μ := MeasureTheory.volume) hab.le
  have hintHi := hcontHi.intervalIntegrable_of_Icc (μ := MeasureTheory.volume) hab.le
  have hintLo := hcontLo.intervalIntegrable_of_Icc (μ := MeasureTheory.volume) hab.le
  have hmonoHi :=
    integral_mono_on (μ := MeasureTheory.volume) hab.le hintHi hintγ fun x hx => (hinv x hx).1
  have hmonoLo :=
    integral_mono_on (μ := MeasureTheory.volume) hab.le hintγ hintLo fun x hx => (hinv x hx).2
  have hfactorHi :=
    integral_inv_mul_factor nodeSlopeHi resonanceRoot1 a b nodeSlopeHi_pos.ne'
  have hfactorLo :=
    integral_inv_mul_factor nodeSlopeLo resonanceRoot1 a b nodeSlopeLo_pos.ne'
  have hlog := integral_inv_gap hab hb
  constructor
  · rw [hfactorHi, hlog] at hmonoHi
    exact hmonoHi
  · rw [hfactorLo, hlog] at hmonoLo
    exact hmonoLo

/-- Approaching the first node, the layer integral of \(1/\gamma_s\) is unbounded. -/
theorem firstNode_layer_integral_unbounded {a : ℝ} (ha : π / 4 ≤ a) (ha1 : a < resonanceRoot1) :
    ∀ C : ℝ, ∃ b, a < b ∧ b < resonanceRoot1 ∧
      C < ∫ x in a..b, (1 / gammaSEqual x) := by
  intro C
  have hshi := nodeSlopeHi_pos
  let s := max (nodeSlopeHi * C) 0 + 1
  let t := exp s
  have hs_gt : nodeSlopeHi * C < s := by
    have hmax : nodeSlopeHi * C ≤ max (nodeSlopeHi * C) 0 := le_max_left _ _
    linarith
  have hs_pos : 0 < s := by
    have : (1 : ℝ) ≤ s := by
      have : (0 : ℝ) ≤ max (nodeSlopeHi * C) 0 := le_max_right _ _
      linarith
    linarith
  have ht : 1 < t := by
    rw [show (1 : ℝ) = exp 0 by simp]
    exact exp_strictMono hs_pos
  let b := resonanceRoot1 - (resonanceRoot1 - a) / t
  have hgap : 0 < resonanceRoot1 - a := by linarith
  have hb_lt : b < resonanceRoot1 := by
    unfold b
    linarith [div_pos hgap (exp_pos s)]
  have hb_gt : a < b := by
    have hlt : (resonanceRoot1 - a) / t < resonanceRoot1 - a := by
      rw [div_lt_iff₀ (exp_pos s)]
      nlinarith [ht, hgap]
    unfold b
    linarith
  refine ⟨b, hb_gt, hb_lt, ?_⟩
  have hlogb := (firstNode_layer_integral_log_bounds ha hb_gt hb_lt).1
  have hratio : (resonanceRoot1 - a) / (resonanceRoot1 - b) = t := by
    have hbdef : resonanceRoot1 - b = (resonanceRoot1 - a) / t := by
      unfold b
      ring
    rw [hbdef]
    field_simp [hgap.ne', (exp_pos s).ne']
  rw [hratio, log_exp] at hlogb
  have hdivC : C < s / nodeSlopeHi := by
    apply (lt_div_iff₀ hshi).mpr
    simpa [mul_comm] using hs_gt
  have : s / nodeSlopeHi = (1 / nodeSlopeHi) * s := by field_simp [hshi.ne']
  linarith

private theorem hasDerivAt_halfInv (lam x : ℝ) (hx : x ≠ 0) :
    HasDerivAt (fun t => lam / (2 * t)) (-lam / (2 * x ^ 2)) x := by
  have hfun : (fun t => lam / (2 * t)) = fun t => (lam / 2) * t⁻¹ := by
    funext t
    field_simp
  rw [hfun]
  have hderiv := (hasDerivAt_inv hx).const_mul (lam / 2)
  simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm, sq] using hderiv

private theorem coulomb_layer_integrand {k e lam x : ℝ} (hx : x ≠ 0) (hlam : lam ≠ 0)
    (hγ : gammaSEqual x ≠ 0) :
    coulombForce k e (gammaSEqual x) (lam / (2 * x)) * (-lam / (2 * x ^ 2)) =
      -((2 * k * e ^ 2) / lam) * (1 / gammaSEqual x) := by
  unfold coulombForce
  have hx2 : x ^ 2 ≠ 0 := pow_ne_zero 2 hx
  field_simp [hx, hlam, hγ, hx2]

/-- Moving inward in an equal-scale Coulomb layer drops the potential by a
positive multiple of \(\int dx/\gamma_s\). The multiple is \(2ke^2/\lambda\). -/
theorem coulomb_potential_increment {k e lam a b : ℝ} (hlam : 0 < lam) (ha : 0 < a) (hab : a ≤ b)
    (hγ : ∀ x ∈ Icc a b, gammaSEqual x ≠ 0) :
    (∫ r in lam / (2 * a)..lam / (2 * b),
        coulombForce k e (gammaSEqual (lam / (2 * r))) r) =
      -((2 * k * e ^ 2) / lam) * ∫ x in a..b, (1 / gammaSEqual x) := by
  let f : ℝ → ℝ := fun t => lam / (2 * t)
  let f' : ℝ → ℝ := fun t => -lam / (2 * t ^ 2)
  let g : ℝ → ℝ := fun r => coulombForce k e (gammaSEqual (lam / (2 * r))) r
  have hder : ∀ x ∈ uIcc a b, HasDerivAt f (f' x) x := by
    intro x hx
    have hx0 : x ≠ 0 := by
      have hxpos : 0 < x := lt_of_lt_of_le ha (uIcc_of_le hab ▸ hx).1
      exact hxpos.ne'
    simpa [f, f'] using hasDerivAt_halfInv lam x hx0
  have hcont' : ContinuousOn f' (uIcc a b) := by
    refine ContinuousOn.div continuousOn_const
      (continuousOn_const.mul (continuous_pow 2).continuousOn) ?_
    intro x hx
    have hx0 : x ≠ 0 := (lt_of_lt_of_le ha (uIcc_of_le hab ▸ hx).1).ne'
    exact mul_ne_zero (by norm_num) (pow_ne_zero 2 hx0)
  have hg : ContinuousOn g (f '' uIcc a b) := by
    have hsub : f '' uIcc a b ⊆ {r | r ≠ 0 ∧ gammaSEqual (lam / (2 * r)) ≠ 0} := by
      intro r hr
      rw [uIcc_of_le hab] at hr
      obtain ⟨x, hx, rfl⟩ := hr
      refine ⟨?_, ?_⟩
      · have hx0 : x ≠ 0 := (lt_of_lt_of_le ha hx.1).ne'
        exact div_ne_zero hlam.ne' (mul_ne_zero (by norm_num) hx0)
      · have hxγ : gammaSEqual (lam / (2 * (lam / (2 * x)))) ≠ 0 := by
          have : lam / (2 * (lam / (2 * x))) = x := by field_simp [hlam.ne']
          simpa [this] using hγ x hx
        simpa using hxγ
    have hcontg : ContinuousOn g {r | r ≠ 0 ∧ gammaSEqual (lam / (2 * r)) ≠ 0} := by
      unfold g coulombForce
      refine ContinuousOn.div ?_ ?_ ?_
      · exact continuousOn_const
      · refine ContinuousOn.mul ?_ (continuousOn_id.pow 2)
        refine continuous_gammaSEqual.comp_continuousOn ?_
        refine ContinuousOn.div continuousOn_const ?_ ?_
        · exact continuousOn_const.mul continuousOn_id
        · intro r hr
          exact mul_ne_zero (by norm_num) hr.1
      · intro r hr
        exact mul_ne_zero hr.2 (pow_ne_zero 2 hr.1)
    exact hcontg.mono hsub
  have hsub := integral_comp_mul_deriv' hder hcont' hg
  have hpoint : ∀ x ∈ Icc a b,
      (g ∘ f) x * f' x = -((2 * k * e ^ 2) / lam) * (1 / gammaSEqual x) := by
    intro x hx
    have hx0 : x ≠ 0 := (lt_of_lt_of_le ha hx.1).ne'
    have hxeq : lam / (2 * (lam / (2 * x))) = x := by field_simp [hlam.ne']
    have hpoint' := coulomb_layer_integrand (k := k) (e := e) (lam := lam)
      hx0 hlam.ne' (hγ x hx)
    simpa [g, f, f', hxeq] using hpoint'
  have hint : ∫ x in a..b, (g ∘ f) x * f' x =
      ∫ x in a..b, -((2 * k * e ^ 2) / lam) * (1 / gammaSEqual x) := by
    refine integral_congr ?_
    intro x hx
    exact hpoint x (uIcc_of_le hab ▸ hx)
  rw [← hsub, hint, intervalIntegral.integral_const_mul]

/-- In the outer attractive layer the equal-scale Coulomb potential falls
without a lower bound as the first node is approached. -/
theorem coulomb_potential_unbounded_below {k e lam a : ℝ} (hk : 0 < k) (he : e ≠ 0)
    (hlam : 0 < lam) (ha : π / 4 ≤ a) (ha1 : a < resonanceRoot1) :
    ∀ C : ℝ, ∃ b, a < b ∧ b < resonanceRoot1 ∧
      (∫ r in lam / (2 * a)..lam / (2 * b),
          coulombForce k e (gammaSEqual (lam / (2 * r))) r) < C := by
  intro C
  have hke : 0 < k * e ^ 2 := mul_pos hk (sq_pos_of_ne_zero he)
  obtain ⟨b, hab, hb, hI⟩ := firstNode_layer_integral_unbounded ha ha1
    (-C * lam / (2 * k * e ^ 2))
  refine ⟨b, hab, hb, ?_⟩
  have hγ : ∀ x ∈ Icc a b, gammaSEqual x ≠ 0 := fun x hx =>
    (gammaSEqual_pos_of_lt_firstNode
      (le_trans (le_of_lt (by positivity : (0 : ℝ) < π / 4)) (ha.trans hx.1))
      (lt_of_le_of_lt hx.2 hb)).ne'
  have hid := coulomb_potential_increment (k := k) (e := e) (lam := lam) hlam
    (lt_of_lt_of_le (by positivity) ha) hab.le hγ
  rw [hid]
  have hc : -((2 * k * e ^ 2) / lam) < 0 := by
    have hpos : 0 < (2 * k * e ^ 2) / lam := by positivity
    linarith
  have hcmp := mul_lt_mul_of_neg_left hI hc
  have hcancel : -((2 * k * e ^ 2) / lam) * (-C * lam / (2 * k * e ^ 2)) = C := by
    field_simp [hlam.ne', hke.ne']
  linarith

end Gravity

end DstDiophantine
