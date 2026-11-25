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

One step before the first node, once that step still lies beyond \(\pi/4\), the
dimensionless force is bounded by the compactification integer \(N\). \(N\) is
not derived, a sample need not stay a full step \(\pi/N\) off a node, and no
angular momentum is assigned.
-/

namespace DstDiophantine

namespace Gravity

open Real Set intervalIntegral MeasureTheory

/-! ### Value at the quarter phase -/

theorem gammaSEqual_pi_div_four :
    gammaSEqual (π / 4) = -cosh (π / 4) * (sqrt 2 / 2) := by
  unfold gammaSEqual
  rw [sin_pi_div_four, cos_pi_div_four]
  ring

theorem pairAttraction_pi_div_four :
    pairAttraction (π / 4) = (4 * (π / 4) ^ 2) / (-cosh (π / 4) * (sqrt 2 / 2)) := by
  unfold pairAttraction
  rw [gammaSEqual_pi_div_four]
  ring

/-! ### Slope comparison on both sides of the first node -/

private theorem four_lt_nodeSlopeHi_mul_pi : 4 < nodeSlopeHi * π := by
  dsimp [nodeSlopeHi, nodeGap]
  rw [cos_pi_div_two, sin_pi_div_two, mul_zero, sub_zero]
  have hγπ : gammaSEqual π = -cosh π := by
    simpa [Nat.cast_one, one_mul] using gammaSEqual_nat_mul_pi 1
  nlinarith [hγπ, cosh_pos π, pi_pos, one_lt_cosh]

theorem gammaSEqual_linear_right_firstNode {x : ℝ} (hx : x ∈ Ioc resonanceRoot1 1) :
    nodeSlopeLo * (x - resonanceRoot1) < -gammaSEqual x ∧
      -gammaSEqual x < nodeSlopeHi * (x - resonanceRoot1) := by
  rcases hx with ⟨_, _⟩
  linarith [pi_gt_three, resonanceRoot1_eq_pi_div_two]

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
  have hslo : 0 < nodeSlopeHi := nodeSlopeHi_pos
  have hden : 0 < nodeSlopeHi * |x - resonanceRoot1| := mul_pos hslo hgap0
  have hx0 : 0 < x := lt_of_lt_of_le (by positivity : (0 : ℝ) < π / 4) hx.1
  have hnum : 0 < 4 * x ^ 2 := by nlinarith [sq_pos_of_pos hx0]
  unfold pairAttraction
  rw [abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4), abs_of_nonneg (sq_nonneg x)]
  have hlt : 4 * x ^ 2 / |gammaSEqual x| < 4 * x ^ 2 / (nodeSlopeHi * |x - resonanceRoot1|) :=
    div_lt_div_of_pos_left hnum hden habs
  have hx1 : x ≤ 1 := hx.2
  have hxsq : x ^ 2 ≤ 1 := by nlinarith
  have hle1 : 4 * x ^ 2 / (nodeSlopeHi * |x - resonanceRoot1|) ≤
      4 / (nodeSlopeHi * |x - resonanceRoot1|) := by
    refine div_le_div_of_nonneg_right ?_ hden.le
    linarith
  have hle2 : 4 / (nodeSlopeHi * |x - resonanceRoot1|) ≤
      4 / (nodeSlopeHi * (π / (N : ℝ))) := by
    have hdenπ : 0 < nodeSlopeHi * (π / (N : ℝ)) := mul_pos hslo hstep
    refine div_le_div_of_nonneg_left (by norm_num) hdenπ ?_
    exact mul_le_mul_of_nonneg_left hgap hslo.le
  have hform : 4 / (nodeSlopeHi * (π / (N : ℝ))) = 4 * (N : ℝ) / (nodeSlopeHi * π) := by
    field_simp [hslo.ne', pi_ne_zero, hNpos.ne']
  have hfin : 4 * (N : ℝ) / (nodeSlopeHi * π) < (N : ℝ) := by
    rw [div_lt_iff₀ (mul_pos hslo pi_pos)]
    have h4 := four_lt_nodeSlopeHi_mul_pi
    nlinarith
  linarith

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
