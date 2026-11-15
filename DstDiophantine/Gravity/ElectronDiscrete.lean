import DstDiophantine.Gravity.ElectronForce
import DstDiophantine.Gravity.ElectronOrbit
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Dual-step ceiling on the first Coulomb node

## Paper boundary (do **not** claim)

The compactification integer `N` is not derived. A lattice sample is not
proved to stay a full step `π/N` away from a node: the node may fall
arbitrarily close to a sample. Nothing here removes the continuum pole, caps
the second node, or places a radius. No angular momentum is assigned.

## What is proved

The dual angle of the discrete torus advances by `2π/N`, so the equal-scale
phase `x = ℓ/(2r)` advances by `π/N`. On `[π/4, 1]`, every phase at least
that far from the first node has dimensionless force strictly smaller than
`N` in absolute value. One step before the node, once the step still lies
beyond `π/4`, the force exceeds `π N / (4 s₁)` with
`s₁ = 2 cosh 1 sin 1`. The outer-well integral of `1/γ_s`, cut off one step
short of the node, does not exceed
`(π √2 / 4) e^{π/4} + (1/s₀) log(N (x₁ - π/4) / π)`, where
`s₀ = 2 cosh(π/4) sin(π/4)`. The continuum divergence is the limit that
removes this step.
-/

namespace DstDiophantine

namespace Gravity

open Real Set intervalIntegral MeasureTheory

/-! ### Value at the quarter phase -/

theorem gammaSEqual_pi_div_four :
    gammaSEqual (π / 4) = exp (-π / 4) / sqrt 2 := by
  unfold gammaSEqual
  rw [sin_pi_div_four, cos_pi_div_four]
  have hfac : cosh (π / 4) * (sqrt 2 / 2) - sinh (π / 4) * (sqrt 2 / 2) =
      (sqrt 2 / 2) * (cosh (π / 4) - sinh (π / 4)) := by ring
  rw [hfac, cosh_sub_sinh]
  have hhalf : sqrt 2 / 2 = 1 / sqrt 2 := by
    field_simp
    exact sq_sqrt (by norm_num)
  rw [hhalf, one_div, mul_comm, ← div_eq_mul_inv]
  refine congrArg (fun t => t / sqrt 2) ?_
  rw [show -(π / 4) = -π / 4 by ring]

theorem pairAttraction_pi_div_four :
    pairAttraction (π / 4) = (π ^ 2 * sqrt 2 / 4) * exp (π / 4) := by
  unfold pairAttraction
  rw [gammaSEqual_pi_div_four]
  have hs : (sqrt 2) ^ 2 = 2 := sq_sqrt (by norm_num)
  field_simp [hs, (exp_pos (-π / 4)).ne']
  rw [← exp_add, show -(π / 4) + π / 4 = 0 by ring, exp_zero]

/-! ### Slope comparison on both sides of the first node -/

private theorem four_lt_nodeSlopeLo_mul_pi : 4 < nodeSlopeLo * π := by
  have hcosh : 1 < cosh (π / 4) := (one_lt_cosh).mpr (by positivity : π / 4 ≠ 0)
  have hsq : (2 * sqrt 2) ^ 2 < (3 : ℝ) ^ 2 := by
    rw [mul_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have h23 : 2 * sqrt 2 < 3 := by
    have habs : |2 * sqrt 2| < |(3 : ℝ)| := (sq_lt_sq).mp hsq
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * sqrt 2)] at habs
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 3)] at habs
    exact habs
  have hπ : 2 * sqrt 2 < π := lt_trans h23 pi_gt_three
  have hsqrt : 0 < sqrt 2 := by positivity
  have hprod : 4 < sqrt 2 * π := by
    have hmul : sqrt 2 * (2 * sqrt 2) < sqrt 2 * π := mul_lt_mul_of_pos_left hπ hsqrt
    have hid : sqrt 2 * (2 * sqrt 2) = 4 := by
      have hself : sqrt 2 * sqrt 2 = 2 := mul_self_sqrt (by norm_num)
      calc
        sqrt 2 * (2 * sqrt 2) = 2 * (sqrt 2 * sqrt 2) := by ring
        _ = 2 * 2 := by rw [hself]
        _ = 4 := by norm_num
    linarith
  unfold nodeSlopeLo
  rw [sin_pi_div_four]
  have hform : 2 * cosh (π / 4) * (sqrt 2 / 2) * π = sqrt 2 * cosh (π / 4) * π := by ring
  rw [hform]
  have hcoshπ : sqrt 2 * π < sqrt 2 * cosh (π / 4) * π := by
    have hmul : sqrt 2 * 1 * π < sqrt 2 * cosh (π / 4) * π := by
      refine mul_lt_mul_of_pos_right ?_ pi_pos
      exact mul_lt_mul_of_pos_left hcosh hsqrt
    simpa [mul_one] using hmul
  linarith

/-- To the right of the first node, still inside the slope window `(π/4, 1)`. -/
theorem gammaSEqual_linear_right_firstNode {x : ℝ} (hx : x ∈ Ioc resonanceRoot1 1) :
    nodeSlopeLo * (x - resonanceRoot1) < -gammaSEqual x ∧
      -gammaSEqual x < nodeSlopeHi * (x - resonanceRoot1) := by
  have hx1 : π / 4 < resonanceRoot1 := resonanceRoot1_sharp_bounds.1
  have hxlt : resonanceRoot1 < x := hx.1
  have hx1lt : resonanceRoot1 < 1 := resonanceRoot1_sharp_bounds.2
  let D := Icc resonanceRoot1 1
  have hD : Convex ℝ D := convex_Icc _ _
  have hxD : x ∈ D := ⟨hxlt.le, hx.2⟩
  have hyD : resonanceRoot1 ∈ D := ⟨le_rfl, hx1lt.le⟩
  have hint : ∀ ξ ∈ interior D, -nodeSlopeHi < deriv gammaSEqual ξ ∧
      deriv gammaSEqual ξ < -nodeSlopeLo := by
    intro ξ hξ
    rw [interior_Icc] at hξ
    exact deriv_gammaSEqual_slope_bounds ⟨lt_trans hx1 hξ.1, hξ.2⟩
  have hcont : ContinuousOn gammaSEqual D := continuous_gammaSEqual.continuousOn
  have hdiff : DifferentiableOn ℝ gammaSEqual (interior D) :=
    gammaSEqual_differentiable.differentiableOn
  have hlo := hD.image_sub_lt_mul_sub_of_deriv_lt hcont hdiff
    (fun ξ hξ => (hint ξ hξ).2) resonanceRoot1 hyD x hxD hxlt
  have hhi := hD.mul_sub_lt_image_sub_of_lt_deriv hcont hdiff
    (fun ξ hξ => (hint ξ hξ).1) resonanceRoot1 hyD x hxD hxlt
  rw [resonanceRoot1_gammaSEqual_zero] at hlo hhi
  constructor
  · linarith
  · linarith

theorem gammaSEqual_abs_firstNode {x : ℝ} (hx : x ∈ Icc (π / 4) 1)
    (hne : x ≠ resonanceRoot1) :
    nodeSlopeLo * |x - resonanceRoot1| < |gammaSEqual x| ∧
      |gammaSEqual x| < nodeSlopeHi * |x - resonanceRoot1| := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hxI : x ∈ Ico (π / 4) resonanceRoot1 := ⟨hx.1, hlt⟩
    obtain ⟨hlo, hhi⟩ := gammaSEqual_linear_firstNode hxI
    have hpos : 0 < gammaSEqual x := gammaSEqual_pos_of_lt_firstNode
      (le_trans (by positivity : (0 : ℝ) ≤ π / 4) hx.1) hlt
    have hsub : |x - resonanceRoot1| = resonanceRoot1 - x := by
      rw [abs_sub_comm, abs_of_pos (sub_pos.mpr hlt)]
    rw [hsub, abs_of_pos hpos]
    exact ⟨hlo, hhi⟩
  · have hxI : x ∈ Ioc resonanceRoot1 1 := ⟨hgt, hx.2⟩
    obtain ⟨hlo, hhi⟩ := gammaSEqual_linear_right_firstNode hxI
    have hneg : gammaSEqual x < 0 :=
      neg_pos.mp (lt_trans (mul_pos nodeSlopeLo_pos (sub_pos.mpr hgt)) hlo)
    have hsub : |x - resonanceRoot1| = x - resonanceRoot1 := abs_of_pos (sub_pos.mpr hgt)
    rw [hsub, abs_of_neg hneg]
    exact ⟨hlo, hhi⟩

/-! ### Force ceiling -/

/-- On `[π/4, 1]`, one equal-scale step `π/N` from the first node keeps the
dimensionless force strictly below `N`. -/
theorem pairAttraction_abs_lt_step {N : ℕ} (hN : N ≠ 0) {x : ℝ}
    (hx : x ∈ Icc (π / 4) 1)
    (hgap : π / (N : ℝ) ≤ |x - resonanceRoot1|) :
    |pairAttraction x| < (N : ℝ) := by
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN)
  have hstep : 0 < π / (N : ℝ) := div_pos pi_pos hNpos
  have hgap0 : 0 < |x - resonanceRoot1| := lt_of_lt_of_le hstep hgap
  have hne : x ≠ resonanceRoot1 := by
    intro h
    rw [h, sub_self, abs_zero] at hgap0
    exact lt_irrefl _ hgap0
  obtain ⟨habs, _⟩ := gammaSEqual_abs_firstNode hx hne
  have hslo : 0 < nodeSlopeLo := nodeSlopeLo_pos
  have hden : 0 < nodeSlopeLo * |x - resonanceRoot1| := mul_pos hslo hgap0
  have hx0 : 0 < x := lt_of_lt_of_le (by positivity : (0 : ℝ) < π / 4) hx.1
  have hnum : 0 < 4 * x ^ 2 := by nlinarith [sq_pos_of_pos hx0]
  unfold pairAttraction
  rw [abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4), abs_of_nonneg (sq_nonneg x)]
  have hlt : 4 * x ^ 2 / |gammaSEqual x| < 4 * x ^ 2 / (nodeSlopeLo * |x - resonanceRoot1|) :=
    div_lt_div_of_pos_left hnum hden habs
  have hx1 : x ≤ 1 := hx.2
  have hxsq : x ^ 2 ≤ 1 := by nlinarith
  have hle1 : 4 * x ^ 2 / (nodeSlopeLo * |x - resonanceRoot1|) ≤
      4 / (nodeSlopeLo * |x - resonanceRoot1|) := by
    refine div_le_div_of_nonneg_right ?_ hden.le
    linarith
  have hle2 : 4 / (nodeSlopeLo * |x - resonanceRoot1|) ≤
      4 / (nodeSlopeLo * (π / (N : ℝ))) := by
    have hdenπ : 0 < nodeSlopeLo * (π / (N : ℝ)) := mul_pos hslo hstep
    refine div_le_div_of_nonneg_left (by norm_num) hdenπ ?_
    exact mul_le_mul_of_nonneg_left hgap hslo.le
  have hform : 4 / (nodeSlopeLo * (π / (N : ℝ))) = 4 * (N : ℝ) / (nodeSlopeLo * π) := by
    field_simp [hslo.ne', pi_ne_zero, hNpos.ne']
  have hfin : 4 * (N : ℝ) / (nodeSlopeLo * π) < (N : ℝ) := by
    rw [div_lt_iff₀ (mul_pos hslo pi_pos)]
    have h4 := four_lt_nodeSlopeLo_mul_pi
    nlinarith
  linarith

/-- One step before the node the force still grows linearly in `N`. -/
theorem pairAttraction_step_before_node {N : ℕ} (hN : 0 < N)
    (hfit : π / (N : ℝ) ≤ resonanceRoot1 - π / 4) :
    (π / (4 * nodeSlopeHi)) * (N : ℝ) <
      pairAttraction (resonanceRoot1 - π / (N : ℝ)) := by
  set x : ℝ := resonanceRoot1 - π / (N : ℝ)
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hstep : 0 < π / (N : ℝ) := div_pos pi_pos hNpos
  have hx1 : π / 4 ≤ x := by
    unfold x
    linarith
  have hxlt : x < resonanceRoot1 := by
    unfold x
    linarith
  have hxI : x ∈ Ico (π / 4) resonanceRoot1 := ⟨hx1, hxlt⟩
  obtain ⟨_, hhi⟩ := gammaSEqual_linear_firstNode hxI
  have hγ : 0 < gammaSEqual x :=
    gammaSEqual_pos_of_lt_firstNode (le_trans (by positivity) hx1) hxlt
  have hshi : 0 < nodeSlopeHi := nodeSlopeHi_pos
  have hden : 0 < nodeSlopeHi * (resonanceRoot1 - x) := mul_pos hshi (by linarith)
  have hforce : 4 * x ^ 2 / (nodeSlopeHi * (resonanceRoot1 - x)) < pairAttraction x := by
    unfold pairAttraction
    exact div_lt_div_of_pos_left (by nlinarith [sq_nonneg x, hx1, pi_pos]) hγ hhi
  have hgap : resonanceRoot1 - x = π / (N : ℝ) := by
    unfold x
    ring
  have hxpos : 0 < x := lt_of_lt_of_le (by positivity : (0 : ℝ) < π / 4) hx1
  have hxsq : (π / 4) ^ 2 ≤ x ^ 2 := by
    have habs : |π / 4| ≤ |x| := by
      rw [abs_of_pos (by positivity : (0 : ℝ) < π / 4), abs_of_pos hxpos]
      exact hx1
    exact sq_le_sq.mpr habs
  have hnum : 4 * (π / 4) ^ 2 / (nodeSlopeHi * (π / (N : ℝ))) ≤
      4 * x ^ 2 / (nodeSlopeHi * (resonanceRoot1 - x)) := by
    rw [← hgap]
    refine div_le_div_of_nonneg_right ?_ hden.le
    nlinarith [hxsq]
  have hconst : 4 * (π / 4) ^ 2 / (nodeSlopeHi * (π / (N : ℝ))) =
      (π / (4 * nodeSlopeHi)) * (N : ℝ) := by
    field_simp [hshi.ne', pi_ne_zero, hNpos.ne']
  linarith

/-! ### Outer-well integral, one step short of the node -/

private theorem continuousOn_inv_gamma_quarter :
    ContinuousOn (fun x => 1 / gammaSEqual x) (Icc 0 (π / 4)) := by
  refine continuousOn_const.div continuous_gammaSEqual.continuousOn fun x hx => ?_
  exact (gammaSEqual_pos_of_lt_firstNode hx.1
    (lt_of_le_of_lt hx.2 resonanceRoot1_sharp_bounds.1)).ne'

private theorem inv_gamma_le_quarter {x : ℝ} (hx : x ∈ Icc 0 (π / 4)) :
    1 / gammaSEqual x ≤ 1 / gammaSEqual (π / 4) := by
  have hxπ : x ∈ Icc 0 π := ⟨hx.1, le_trans hx.2 (by linarith [pi_pos])⟩
  have hπ : (π / 4) ∈ Icc 0 π := ⟨by positivity, by linarith [pi_pos]⟩
  have hγ : gammaSEqual (π / 4) ≤ gammaSEqual x := by
    rcases eq_or_lt_of_le hx.2 with rfl | hlt
    · exact le_rfl
    · have hlo0 : (((2 * 0 : ℕ) : ℝ) * π) = 0 := by norm_num
      have hxI : x ∈ Icc (((2 * 0 : ℕ) : ℝ) * π) (((2 * 0 : ℕ) : ℝ) * π + π) := by
        rw [hlo0, zero_add]; exact hxπ
      have hπI : π / 4 ∈ Icc (((2 * 0 : ℕ) : ℝ) * π) (((2 * 0 : ℕ) : ℝ) * π + π) := by
        rw [hlo0, zero_add]; exact hπ
      exact (strictAntiOn_gammaSEqual_even 0 hxI hπI hlt).le
  have hpos : 0 < gammaSEqual (π / 4) :=
    gammaSEqual_pos_of_lt_firstNode (by positivity) resonanceRoot1_sharp_bounds.1
  exact div_le_div_of_nonneg_left zero_le_one hpos hγ

/-- The outer-well integral of \(1/\gamma_s\), cut off one step \(\pi/N\) short of
the first node, grows at most logarithmically in \(N\). -/
theorem outerWell_integral_oneStep {N : ℕ} (hN : 0 < N)
    (hfit : π / (N : ℝ) < resonanceRoot1 - π / 4) :
    ∫ x in (0 : ℝ)..(resonanceRoot1 - π / (N : ℝ)), (1 / gammaSEqual x) ≤
      (π / 4) * sqrt 2 * exp (π / 4) +
        (1 / nodeSlopeLo) * log ((N : ℝ) * (resonanceRoot1 - π / 4) / π) := by
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  set b : ℝ := resonanceRoot1 - π / (N : ℝ)
  have hbq : π / 4 < b := by
    unfold b
    linarith
  have hb1 : b < resonanceRoot1 := by
    unfold b
    linarith [div_pos pi_pos hNpos]
  have hintQ := (continuousOn_inv_gamma_quarter.intervalIntegrable_of_Icc
    (μ := volume) (by positivity : (0 : ℝ) ≤ π / 4))
  have hposTail : ∀ x ∈ Icc (π / 4) b, 0 < gammaSEqual x := fun x hx =>
    gammaSEqual_pos_of_lt_firstNode
      (le_trans (by positivity : (0 : ℝ) ≤ π / 4) hx.1) (lt_of_le_of_lt hx.2 hb1)
  have hintT : IntervalIntegrable (fun x => 1 / gammaSEqual x) volume (π / 4) b :=
    (continuousOn_const.div continuous_gammaSEqual.continuousOn
      fun x hx => (hposTail x hx).ne').intervalIntegrable_of_Icc (μ := volume) hbq.le
  have hadd := integral_add_adjacent_intervals hintQ hintT
  have hconstInt : IntervalIntegrable (fun _ : ℝ => 1 / gammaSEqual (π / 4)) volume 0 (π / 4) :=
    intervalIntegrable_const
  have hmono := integral_mono_on (μ := volume) (by positivity : (0 : ℝ) ≤ π / 4)
    hintQ hconstInt (fun x hx => inv_gamma_le_quarter hx)
  have hconst : ∫ x in (0 : ℝ)..(π / 4), (fun _ : ℝ => 1 / gammaSEqual (π / 4)) x =
      (π / 4) * (1 / gammaSEqual (π / 4)) := by
    simp [intervalIntegral.integral_const]
  rw [hconst, gammaSEqual_pi_div_four] at hmono
  have hquarter : (π / 4) * (1 / (exp (-π / 4) / sqrt 2)) =
      (π / 4) * sqrt 2 * exp (π / 4) := by
    have hsign : -π / 4 = -(π / 4) := by ring
    rw [hsign, exp_neg]
    field_simp [(exp_pos (π / 4)).ne', (sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne']
  rw [hquarter] at hmono
  have hlog := (firstNode_layer_integral_log_bounds (le_rfl : π / 4 ≤ π / 4) hbq hb1).2
  have hratio : (resonanceRoot1 - π / 4) / (resonanceRoot1 - b) =
      (N : ℝ) * (resonanceRoot1 - π / 4) / π := by
    have hbdef : resonanceRoot1 - b = π / (N : ℝ) := by
      unfold b
      ring
    rw [hbdef]
    field_simp [hNpos.ne', pi_ne_zero]
  rw [hratio] at hlog
  have hsplit : ∫ x in (0 : ℝ)..b, (1 / gammaSEqual x) =
      (∫ x in (0 : ℝ)..(π / 4), (1 / gammaSEqual x)) +
        ∫ x in (π / 4)..b, (1 / gammaSEqual x) := hadd.symm
  linarith

end Gravity

end DstDiophantine
