import DstDiophantine.Gravity.ElectronForce
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Numerical windows for the electron-shell radii

## Paper boundary (do **not** claim)

The length `ℓ` is not derived. Nothing here identifies a side of the square
with the Bohr radius, or assigns a dissociation energy.

## What is proved

* The first node lies in `(14/15, 19/20)`, so its radius lies in
  `(10/19, 15/28)` in units of `ℓ`.
* The restoring square lies in `(153/100, 157/100)`, so the diagonal lies in
  `(50/157, 50/153)`. The side lies strictly below `50/157` and strictly
  above `1/5`.
* At that square the diagonal force, in units of `k e²/ℓ²`, is strictly
  greater than `4`. The side force is that force divided by `√2`, hence
  strictly greater than `2√2`.
* The outward force at `x = π` is `4π²/cosh π`, strictly less than `7/2`
  and, as already recorded, strictly greater than `3`.
* Placing the side at one Bohr radius would put the first node strictly
  between `91/40` and `12/5` Bohr radii.
* The circular radius, the first node, the diagonal, the side, the
  one-electron extremum, and the second node stand in that order.
-/

namespace DstDiophantine

namespace Gravity

open Real Set Finset

/-! ### Exponential brackets -/

private lemma exp_fourteen_fifteenths_bounds :
    (2542 / 1000 : ℝ) < exp (14 / 15) ∧ exp (14 / 15) < 2543 / 1000 := by
  refine exp_between (x := 14 / 15) (n := 8) (by norm_num) (by norm_num) (by decide) ?_ ?_
  · norm_num [sum_range_succ, Nat.factorial]
  · norm_num [sum_range_succ, Nat.factorial]

private lemma exp_nineteen_twentieths_bounds :
    (2585 / 1000 : ℝ) < exp (19 / 20) ∧ exp (19 / 20) < 2586 / 1000 := by
  refine exp_between (x := 19 / 20) (n := 8) (by norm_num) (by norm_num) (by decide) ?_ ?_
  · norm_num [sum_range_succ, Nat.factorial]
  · norm_num [sum_range_succ, Nat.factorial]

private lemma exp_fiftyThree_hundredths_bounds :
    (1698 / 1000 : ℝ) < exp (53 / 100) ∧ exp (53 / 100) < 1699 / 1000 := by
  refine exp_between (x := 53 / 100) (n := 8) (by norm_num) (by norm_num) (by decide) ?_ ?_
  · norm_num [sum_range_succ, Nat.factorial]
  · norm_num [sum_range_succ, Nat.factorial]

private lemma exp_fiftySeven_hundredths_bounds :
    (1768 / 1000 : ℝ) < exp (57 / 100) ∧ exp (57 / 100) < 1769 / 1000 := by
  refine exp_between (x := 57 / 100) (n := 8) (by norm_num) (by norm_num) (by decide) ?_ ?_
  · norm_num [sum_range_succ, Nat.factorial]
  · norm_num [sum_range_succ, Nat.factorial]

private lemma exp_oneSixThree_thousandths_bounds :
    (1177 / 1000 : ℝ) < exp (163 / 1000) ∧ exp (163 / 1000) < 1178 / 1000 := by
  refine exp_between (x := 163 / 1000) (n := 6) (by norm_num) (by norm_num) (by decide) ?_ ?_
  · norm_num [sum_range_succ, Nat.factorial]
  · norm_num [sum_range_succ, Nat.factorial]

private lemma exp_twoTwoOne_thousandths_bounds :
    (1247 / 1000 : ℝ) < exp (221 / 1000) ∧ exp (221 / 1000) < 1248 / 1000 := by
  refine exp_between (x := 221 / 1000) (n := 6) (by norm_num) (by norm_num) (by decide) ?_ ?_
  · norm_num [sum_range_succ, Nat.factorial]
  · norm_num [sum_range_succ, Nat.factorial]

private lemma exp_oneFiveThree_bounds :
    (2.7182818283 : ℝ) * (1698 / 1000) < exp (153 / 100) ∧
      exp (153 / 100) < (2.7182818286 : ℝ) * (1699 / 1000) := by
  have hid : exp (153 / 100) = exp 1 * exp (53 / 100) := by
    rw [show (153 / 100 : ℝ) = 1 + 53 / 100 by norm_num, exp_add]
  constructor
  · rw [hid]
    nlinarith [exp_one_gt_d9, exp_fiftyThree_hundredths_bounds.1, exp_pos 1,
      exp_pos (53 / 100)]
  · rw [hid]
    nlinarith [exp_one_lt_d9, exp_fiftyThree_hundredths_bounds.2, exp_pos 1]

private lemma exp_oneFiveSeven_bounds :
    (2.7182818283 : ℝ) * (1768 / 1000) < exp (157 / 100) ∧
      exp (157 / 100) < (2.7182818286 : ℝ) * (1769 / 1000) := by
  have hid : exp (157 / 100) = exp 1 * exp (57 / 100) := by
    rw [show (157 / 100 : ℝ) = 1 + 57 / 100 by norm_num, exp_add]
  constructor
  · rw [hid]
    nlinarith [exp_one_gt_d9, exp_fiftySeven_hundredths_bounds.1, exp_pos 1,
      exp_pos (57 / 100)]
  · rw [hid]
    nlinarith [exp_one_lt_d9, exp_fiftySeven_hundredths_bounds.2, exp_pos 1]

private lemma exp_twoOneSixThree_bounds :
    (2.7182818283 : ℝ) ^ 2 * (1177 / 1000) < exp (2163 / 1000) ∧
      exp (2163 / 1000) < (2.7182818286 : ℝ) ^ 2 * (1178 / 1000) := by
  have hid : exp (2163 / 1000) = exp 1 ^ 2 * exp (163 / 1000) := by
    have : (2163 / 1000 : ℝ) = 1 + 1 + 163 / 1000 := by norm_num
    rw [this, exp_add, exp_add]
    ring
  constructor
  · rw [hid]
    nlinarith [exp_one_gt_d9, exp_oneSixThree_thousandths_bounds.1, exp_pos 1,
      exp_pos (163 / 1000)]
  · rw [hid]
    nlinarith [exp_one_lt_d9, exp_oneSixThree_thousandths_bounds.2, exp_pos 1]

private lemma exp_twoTwoTwoOne_bounds :
    (2.7182818283 : ℝ) ^ 2 * (1247 / 1000) < exp (2221 / 1000) ∧
      exp (2221 / 1000) < (2.7182818286 : ℝ) ^ 2 * (1248 / 1000) := by
  have hid : exp (2221 / 1000) = exp 1 ^ 2 * exp (221 / 1000) := by
    have : (2221 / 1000 : ℝ) = 1 + 1 + 221 / 1000 := by norm_num
    rw [this, exp_add, exp_add]
    ring
  constructor
  · rw [hid]
    nlinarith [exp_one_gt_d9, exp_twoTwoOne_thousandths_bounds.1, exp_pos 1,
      exp_pos (221 / 1000)]
  · rw [hid]
    nlinarith [exp_one_lt_d9, exp_twoTwoOne_thousandths_bounds.2, exp_pos 1]

/-! ### First node -/

private lemma gamma_fourteen_fifteenths_pos : 0 < gammaSEqual (14 / 15) := by
  have hbounds := gamma_before (x := 14 / 15) (ε := π / 2 - 14 / 15)
    (a := 3.141592 / 2 - 14 / 15) (b := 3.141593 / 2 - 14 / 15)
    (E0 := 2542 / 1000) (E1 := 2543 / 1000)
    (by ring) (by norm_num) (by norm_num) (by linarith [pi_gt_d6]) (by linarith [pi_lt_d6])
    (by norm_num) exp_fourteen_fifteenths_bounds.1.le exp_fourteen_fifteenths_bounds.2.le
    (by simp only [sinHi, cosLo]; norm_num)
    (by simp only [sinLo, cosLo]; norm_num)
  have hlo : 0 < gammaLower (2543 / 1000)
      (sinLo (3.141592 / 2 - 14 / 15) (3.141593 / 2 - 14 / 15) -
        cosHi (3.141592 / 2 - 14 / 15) (3.141593 / 2 - 14 / 15))
      (sinLo (3.141592 / 2 - 14 / 15) (3.141593 / 2 - 14 / 15) +
        cosLo (3.141593 / 2 - 14 / 15)) := by
    simp only [gammaLower, sinLo, cosLo, cosHi]
    norm_num
  linarith [hbounds.1]

private lemma gamma_nineteen_twentieths_neg : gammaSEqual (19 / 20) < 0 := by
  have hbounds := gamma_before (x := 19 / 20) (ε := π / 2 - 19 / 20)
    (a := 3.141592 / 2 - 19 / 20) (b := 3.141593 / 2 - 19 / 20)
    (E0 := 2585 / 1000) (E1 := 2586 / 1000)
    (by ring) (by norm_num) (by norm_num) (by linarith [pi_gt_d6]) (by linarith [pi_lt_d6])
    (by norm_num) exp_nineteen_twentieths_bounds.1.le exp_nineteen_twentieths_bounds.2.le
    (by simp only [sinHi, cosLo]; norm_num)
    (by simp only [sinLo, cosLo]; norm_num)
  have hhi : gammaUpper (2585 / 1000)
      (sinHi (3.141593 / 2 - 19 / 20) - cosLo (3.141593 / 2 - 19 / 20))
      (sinHi (3.141593 / 2 - 19 / 20) +
        cosHi (3.141592 / 2 - 19 / 20) (3.141593 / 2 - 19 / 20)) < 0 := by
    simp only [gammaUpper, sinHi, cosLo, cosHi]
    norm_num
  linarith [hbounds.2]

/-- The first equal-scale node lies strictly between `14/15` and `19/20`. -/
theorem firstNode_num_window :
    (14 / 15 : ℝ) < resonanceRoot1 ∧ resonanceRoot1 < 19 / 20 := by
  have hroot : gammaSEqual resonanceRoot1 = 0 := resonanceRoot1_gammaSEqual_zero
  have hrootI := mem_gamma_Icc
    (le_of_lt (lt_trans (by norm_num : (0 : ℝ) < 1 / 2) resonanceRoot1_bounds.1))
    (le_of_lt (lt_trans resonanceRoot1_sharp_bounds.2
      (by linarith [pi_gt_three] : (1 : ℝ) < π)))
  have hanti := strictAntiOn_gammaSEqual_even 0
  constructor
  · have h14I := mem_gamma_Icc (by norm_num : (0 : ℝ) ≤ 14 / 15)
      (by linarith [pi_gt_three] : (14 / 15 : ℝ) ≤ π)
    by_contra hge
    have hle : resonanceRoot1 ≤ 14 / 15 := le_of_not_gt hge
    rcases eq_or_lt_of_le hle with hEq | hlt
    · exact (ne_of_gt gamma_fourteen_fifteenths_pos) (hEq ▸ hroot)
    · have := hanti hrootI h14I hlt
      linarith [gamma_fourteen_fifteenths_pos, hroot]
  · have h19I := mem_gamma_Icc (by norm_num : (0 : ℝ) ≤ 19 / 20)
      (by linarith [pi_gt_three] : (19 / 20 : ℝ) ≤ π)
    by_contra hle
    have hge : 19 / 20 ≤ resonanceRoot1 := le_of_not_gt hle
    rcases eq_or_lt_of_le hge with hEq | hlt
    · exact (ne_of_lt gamma_nineteen_twentieths_neg) (hEq.symm ▸ hroot)
    · have := hanti h19I hrootI hlt
      linarith [gamma_nineteen_twentieths_neg, hroot]

/-- In units of `ℓ`, the first-node radius lies strictly between `10/19` and `15/28`. -/
theorem firstNode_radius_window :
    (10 / 19 : ℝ) < 1 / (2 * resonanceRoot1) ∧ 1 / (2 * resonanceRoot1) < 15 / 28 := by
  have h := firstNode_num_window
  have hx : 0 < resonanceRoot1 := lt_trans (by norm_num) h.1
  constructor
  · rw [div_lt_div_iff₀ (by norm_num) (mul_pos (by norm_num) hx)]
    nlinarith
  · rw [div_lt_div_iff₀ (mul_pos (by norm_num) hx) (by norm_num)]
    nlinarith

/-! ### The restoring square -/

private lemma proxy_lt_side_low : (2163 / 1000 : ℝ) < sqrt 2 * (153 / 100) := by
  have h := sqrt_two_bounds.1
  have hrat : (2163 / 1000 : ℝ) < (140 / 99) * (153 / 100) := by norm_num
  nlinarith

private lemma side_high_lt_proxy : sqrt 2 * (157 / 100) < (2221 / 1000 : ℝ) := by
  have h := sqrt_two_bounds.2
  have hrat : (99 / 70) * (157 / 100) < (2221 / 1000 : ℝ) := by norm_num
  nlinarith

private lemma gamma_oneFiveThree_lower :
    gammaLower ((2.7182818286 : ℝ) * (1699 / 1000))
      (sinLo (3.141592 / 2 - 153 / 100) (3.141593 / 2 - 153 / 100) -
        cosHi (3.141592 / 2 - 153 / 100) (3.141593 / 2 - 153 / 100))
      (sinLo (3.141592 / 2 - 153 / 100) (3.141593 / 2 - 153 / 100) +
        cosLo (3.141593 / 2 - 153 / 100)) ≤ gammaSEqual (153 / 100) := by
  have hD : sinHi (3.141593 / 2 - 153 / 100) - cosLo (3.141593 / 2 - 153 / 100) < 0 := by
    simp only [sinHi, cosLo]; norm_num
  have hS : 0 < sinLo (3.141592 / 2 - 153 / 100) (3.141593 / 2 - 153 / 100) +
      cosLo (3.141593 / 2 - 153 / 100) := by
    simp only [sinLo, cosLo]; norm_num
  exact (gamma_before (x := 153 / 100) (ε := π / 2 - 153 / 100)
    (a := 3.141592 / 2 - 153 / 100) (b := 3.141593 / 2 - 153 / 100)
    (E0 := (2.7182818283 : ℝ) * (1698 / 1000))
    (E1 := (2.7182818286 : ℝ) * (1699 / 1000))
    (by ring) (by norm_num) (by norm_num) (by linarith [pi_gt_d6]) (by linarith [pi_lt_d6])
    (by positivity) exp_oneFiveThree_bounds.1.le exp_oneFiveThree_bounds.2.le hD hS).1

private lemma gamma_twoOneSixThree_upper :
    gammaSEqual (2163 / 1000) ≤
      gammaUpper ((2.7182818283 : ℝ) ^ 2 * (1177 / 1000))
        (-(sinLo (2163 / 1000 - 3.141593 / 2) (2163 / 1000 - 3.141592 / 2) +
          cosLo (2163 / 1000 - 3.141592 / 2)))
        (-sinLo (2163 / 1000 - 3.141593 / 2) (2163 / 1000 - 3.141592 / 2) +
          cosHi (2163 / 1000 - 3.141593 / 2) (2163 / 1000 - 3.141592 / 2)) := by
  have hD : -(sinLo (2163 / 1000 - 3.141593 / 2) (2163 / 1000 - 3.141592 / 2) +
      cosLo (2163 / 1000 - 3.141592 / 2)) < 0 := by
    simp only [sinLo, cosLo]; norm_num
  have hS : 0 < -sinHi (2163 / 1000 - 3.141592 / 2) +
      cosLo (2163 / 1000 - 3.141592 / 2) := by
    simp only [sinHi, cosLo]; norm_num
  exact (gamma_after (x := 2163 / 1000) (ε := 2163 / 1000 - π / 2)
    (a := 2163 / 1000 - 3.141593 / 2) (b := 2163 / 1000 - 3.141592 / 2)
    (E0 := (2.7182818283 : ℝ) ^ 2 * (1177 / 1000))
    (E1 := (2.7182818286 : ℝ) ^ 2 * (1178 / 1000))
    (by ring) (by norm_num) (by norm_num) (by linarith [pi_lt_d6]) (by linarith [pi_gt_d6])
    (by positivity) exp_twoOneSixThree_bounds.1.le exp_twoOneSixThree_bounds.2.le hD hS).2

private lemma gamma_oneFiveSeven_upper :
    gammaSEqual (157 / 100) ≤
      gammaUpper ((2.7182818283 : ℝ) * (1768 / 1000))
        (sinHi (3.141593 / 2 - 157 / 100) - cosLo (3.141593 / 2 - 157 / 100))
        (sinHi (3.141593 / 2 - 157 / 100) +
          cosHi (3.141592 / 2 - 157 / 100) (3.141593 / 2 - 157 / 100)) := by
  have hD : sinHi (3.141593 / 2 - 157 / 100) - cosLo (3.141593 / 2 - 157 / 100) < 0 := by
    simp only [sinHi, cosLo]; norm_num
  have hS : 0 < sinLo (3.141592 / 2 - 157 / 100) (3.141593 / 2 - 157 / 100) +
      cosLo (3.141593 / 2 - 157 / 100) := by
    simp only [sinLo, cosLo]; norm_num
  exact (gamma_before (x := 157 / 100) (ε := π / 2 - 157 / 100)
    (a := 3.141592 / 2 - 157 / 100) (b := 3.141593 / 2 - 157 / 100)
    (E0 := (2.7182818283 : ℝ) * (1768 / 1000))
    (E1 := (2.7182818286 : ℝ) * (1769 / 1000))
    (by ring) (by norm_num) (by norm_num) (by linarith [pi_gt_d6]) (by linarith [pi_lt_d6])
    (by positivity) exp_oneFiveSeven_bounds.1.le exp_oneFiveSeven_bounds.2.le hD hS).2

private lemma gamma_oneFiveSeven_lower :
    gammaLower ((2.7182818286 : ℝ) * (1769 / 1000))
      (sinLo (3.141592 / 2 - 157 / 100) (3.141593 / 2 - 157 / 100) -
        cosHi (3.141592 / 2 - 157 / 100) (3.141593 / 2 - 157 / 100))
      (sinLo (3.141592 / 2 - 157 / 100) (3.141593 / 2 - 157 / 100) +
        cosLo (3.141593 / 2 - 157 / 100)) ≤ gammaSEqual (157 / 100) := by
  have hD : sinHi (3.141593 / 2 - 157 / 100) - cosLo (3.141593 / 2 - 157 / 100) < 0 := by
    simp only [sinHi, cosLo]; norm_num
  have hS : 0 < sinLo (3.141592 / 2 - 157 / 100) (3.141593 / 2 - 157 / 100) +
      cosLo (3.141593 / 2 - 157 / 100) := by
    simp only [sinLo, cosLo]; norm_num
  exact (gamma_before (x := 157 / 100) (ε := π / 2 - 157 / 100)
    (a := 3.141592 / 2 - 157 / 100) (b := 3.141593 / 2 - 157 / 100)
    (E0 := (2.7182818283 : ℝ) * (1768 / 1000))
    (E1 := (2.7182818286 : ℝ) * (1769 / 1000))
    (by ring) (by norm_num) (by norm_num) (by linarith [pi_gt_d6]) (by linarith [pi_lt_d6])
    (by positivity) exp_oneFiveSeven_bounds.1.le exp_oneFiveSeven_bounds.2.le hD hS).1

private lemma gamma_twoTwoTwoOne_lower :
    gammaLower ((2.7182818286 : ℝ) ^ 2 * (1248 / 1000))
      (-(sinHi (2221 / 1000 - 3.141592 / 2) +
        cosHi (2221 / 1000 - 3.141593 / 2) (2221 / 1000 - 3.141592 / 2)))
      (-sinHi (2221 / 1000 - 3.141592 / 2) + cosLo (2221 / 1000 - 3.141592 / 2)) ≤
      gammaSEqual (2221 / 1000) := by
  have hD : -(sinLo (2221 / 1000 - 3.141593 / 2) (2221 / 1000 - 3.141592 / 2) +
      cosLo (2221 / 1000 - 3.141592 / 2)) < 0 := by
    simp only [sinLo, cosLo]; norm_num
  have hS : 0 < -sinHi (2221 / 1000 - 3.141592 / 2) +
      cosLo (2221 / 1000 - 3.141592 / 2) := by
    simp only [sinHi, cosLo]; norm_num
  exact (gamma_after (x := 2221 / 1000) (ε := 2221 / 1000 - π / 2)
    (a := 2221 / 1000 - 3.141593 / 2) (b := 2221 / 1000 - 3.141592 / 2)
    (E0 := (2.7182818283 : ℝ) ^ 2 * (1247 / 1000))
    (E1 := (2.7182818286 : ℝ) ^ 2 * (1248 / 1000))
    (by ring) (by norm_num) (by norm_num) (by linarith [pi_lt_d6]) (by linarith [pi_gt_d6])
    (by positivity) exp_twoTwoTwoOne_bounds.1.le exp_twoTwoTwoOne_bounds.2.le hD hS).1

private lemma lowPhase_mem_shell :
    (153 / 100 : ℝ) ∈ Ioo resonanceRoot1 (branchNode 1 / sqrt 2) := by
  refine ⟨by linarith [resonanceRoot1_sharp_bounds.2], ?_⟩
  have hs : 0 < sqrt 2 := sqrt_pos.mpr (by norm_num)
  rw [lt_div_iff₀ hs]
  have h8 : (8 / 5 : ℝ) ∈ Ioo resonanceRoot1 (branchNode 1 / sqrt 2) := by
    have hnode : π < branchNode 1 := by
      simpa [Nat.cast_one, one_mul] using (branchNode_spec 1).1.1
    refine ⟨by linarith [resonanceRoot1_sharp_bounds.2], ?_⟩
    rw [lt_div_iff₀ hs]
    have : sqrt 2 * (8 / 5) < 3 := by
      have h := sqrt_two_bounds.2
      nlinarith
    linarith [pi_gt_three, hnode]
  have hlt : (153 / 100 : ℝ) < 8 / 5 := by norm_num
  have hcmp : sqrt 2 * (153 / 100) < sqrt 2 * (8 / 5) :=
    mul_lt_mul_of_pos_left hlt hs
  have h8side : sqrt 2 * (8 / 5) < branchNode 1 := by
    have h := h8.2
    rw [lt_div_iff₀ hs] at h
    simpa [mul_comm] using h
  linarith

private lemma highPhase_mem_shell :
    (157 / 100 : ℝ) ∈ Ioo resonanceRoot1 (branchNode 1 / sqrt 2) := by
  refine ⟨by linarith [resonanceRoot1_sharp_bounds.2], ?_⟩
  have hs : 0 < sqrt 2 := sqrt_pos.mpr (by norm_num)
  have hnode : π < branchNode 1 := by
    simpa [Nat.cast_one, one_mul] using (branchNode_spec 1).1.1
  rw [lt_div_iff₀ hs]
  have : sqrt 2 * (157 / 100) < 3 := by
    have h := sqrt_two_bounds.2
    nlinarith
  linarith [pi_gt_three, hnode]

theorem squareBalance_oneFiveThree_neg : squareBalance (153 / 100) < 0 := by
  have hy := proxy_lt_side_low
  have hyπ : sqrt 2 * (153 / 100) < π := by
    have : sqrt 2 * (153 / 100) < 3 := by
      have h := sqrt_two_bounds.2
      nlinarith
    linarith [pi_gt_three]
  have hy0 : 0 < sqrt 2 * (153 / 100) := by positivity
  have hdec : gammaSEqual (sqrt 2 * (153 / 100)) < gammaSEqual (2163 / 1000) :=
    strictAntiOn_gammaSEqual_even 0
      (mem_gamma_Icc (by norm_num) (by linarith [pi_gt_three]))
      (mem_gamma_Icc hy0.le hyπ.le) hy
  have hlo := gamma_oneFiveThree_lower
  have hhi := gamma_twoOneSixThree_upper
  have hcmp :
      gammaUpper ((2.7182818283 : ℝ) ^ 2 * (1177 / 1000))
        (-(sinLo (2163 / 1000 - 3.141593 / 2) (2163 / 1000 - 3.141592 / 2) +
          cosLo (2163 / 1000 - 3.141592 / 2)))
        (-sinLo (2163 / 1000 - 3.141593 / 2) (2163 / 1000 - 3.141592 / 2) +
          cosHi (2163 / 1000 - 3.141593 / 2) (2163 / 1000 - 3.141592 / 2)) <
      (99 / 35) * gammaLower ((2.7182818286 : ℝ) * (1699 / 1000))
        (sinLo (3.141592 / 2 - 153 / 100) (3.141593 / 2 - 153 / 100) -
          cosHi (3.141592 / 2 - 153 / 100) (3.141593 / 2 - 153 / 100))
        (sinLo (3.141592 / 2 - 153 / 100) (3.141593 / 2 - 153 / 100) +
          cosLo (3.141593 / 2 - 153 / 100)) := by
    simp only [gammaUpper, gammaLower, sinLo, cosLo, cosHi]
    norm_num
  have hγneg : gammaSEqual (153 / 100) < 0 :=
    gammaSEqual_neg_right_of_first_node
      ⟨by linarith [resonanceRoot1_sharp_bounds.2], by linarith [pi_gt_three]⟩
  have hA : 2 * sqrt 2 < 99 / 35 := two_sqrt_two_bounds.2
  have hP : (99 / 35) * gammaSEqual (153 / 100) < 2 * sqrt 2 * gammaSEqual (153 / 100) := by
    nlinarith
  unfold squareBalance
  linarith

theorem squareBalance_oneFiveSeven_pos : 0 < squareBalance (157 / 100) := by
  have hy := side_high_lt_proxy
  have hy0 : 0 < sqrt 2 * (157 / 100) := by positivity
  have hyπ : sqrt 2 * (157 / 100) < π := by
    have : sqrt 2 * (157 / 100) < 3 := by
      have h := sqrt_two_bounds.2
      nlinarith
    linarith [pi_gt_three]
  have hUπ : (2221 / 1000 : ℝ) < π := by linarith [pi_gt_three]
  have hdec : gammaSEqual (2221 / 1000) < gammaSEqual (sqrt 2 * (157 / 100)) :=
    strictAntiOn_gammaSEqual_even 0 (mem_gamma_Icc hy0.le hyπ.le)
      (mem_gamma_Icc (by norm_num) hUπ.le) hy
  have hhi := gamma_oneFiveSeven_upper
  have hlo := gamma_twoTwoTwoOne_lower
  have hγneg : gammaSEqual (157 / 100) < 0 :=
    gammaSEqual_neg_right_of_first_node
      ⟨by linarith [resonanceRoot1_sharp_bounds.2], by linarith [pi_gt_three]⟩
  have hcmp : (280 / 99) * gammaUpper ((2.7182818283 : ℝ) * (1768 / 1000))
      (sinHi (3.141593 / 2 - 157 / 100) - cosLo (3.141593 / 2 - 157 / 100))
      (sinHi (3.141593 / 2 - 157 / 100) +
        cosHi (3.141592 / 2 - 157 / 100) (3.141593 / 2 - 157 / 100)) <
      gammaLower ((2.7182818286 : ℝ) ^ 2 * (1248 / 1000))
        (-(sinHi (2221 / 1000 - 3.141592 / 2) +
          cosHi (2221 / 1000 - 3.141593 / 2) (2221 / 1000 - 3.141592 / 2)))
        (-sinHi (2221 / 1000 - 3.141592 / 2) +
          cosLo (2221 / 1000 - 3.141592 / 2)) := by
    simp only [gammaUpper, gammaLower, sinHi, cosLo, cosHi]
    norm_num
  have hA : 280 / 99 < 2 * sqrt 2 := two_sqrt_two_bounds.1
  have hP : 2 * sqrt 2 * gammaSEqual (157 / 100) < (280 / 99) * gammaSEqual (157 / 100) := by
    nlinarith
  unfold squareBalance
  linarith

noncomputable def squarePhase : ℝ :=
  Classical.choose (exists_unique_square_shell).exists

theorem squarePhase_spec :
    squarePhase ∈ Ioo resonanceRoot1 (branchNode 1 / sqrt 2) ∧
      squareBalance squarePhase = 0 :=
  Classical.choose_spec (exists_unique_square_shell).exists

/-- The restoring square lies strictly between `153/100` and `157/100`. -/
theorem squarePhase_num_window :
    (153 / 100 : ℝ) < squarePhase ∧ squarePhase < 157 / 100 := by
  obtain ⟨hx, h0⟩ := squarePhase_spec
  have hmono := squareBalance_strictMonoOn_shell
  constructor
  · by_contra hge
    have hle : squarePhase ≤ 153 / 100 := le_of_not_gt hge
    have hmem := lowPhase_mem_shell
    rcases eq_or_lt_of_le hle with hEq | hlt
    · exact (ne_of_lt squareBalance_oneFiveThree_neg) (hEq ▸ h0)
    · have := hmono hx hmem hlt
      linarith [squareBalance_oneFiveThree_neg, h0]
  · by_contra hle
    have hge : 157 / 100 ≤ squarePhase := le_of_not_gt hle
    have hmem := highPhase_mem_shell
    rcases eq_or_lt_of_le hge with hEq | hlt
    · exact (ne_of_gt squareBalance_oneFiveSeven_pos) (hEq.symm ▸ h0)
    · have := hmono hmem hx hlt
      linarith [squareBalance_oneFiveSeven_pos, h0]

/-- Diagonal and side, in units of `ℓ`. -/
theorem square_radius_window :
    (50 / 157 : ℝ) < 1 / (2 * squarePhase) ∧ 1 / (2 * squarePhase) < 50 / 153 ∧
      1 / 5 < 1 / (2 * sqrt 2 * squarePhase) ∧
      1 / (2 * sqrt 2 * squarePhase) < 50 / 157 := by
  have h := squarePhase_num_window
  have hx : 0 < squarePhase := lt_trans (by norm_num) h.1
  have hs : 0 < sqrt 2 := sqrt_pos.mpr (by norm_num)
  have hside_lo : (1 / 5 : ℝ) < 50 / (157 * sqrt 2) := by
    have hsq : ((157 : ℝ) * sqrt 2) ^ 2 < 250 ^ 2 := by
      rw [mul_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    have hlt : (157 : ℝ) * sqrt 2 < 250 :=
      lt_of_pow_lt_pow_left₀ 2 (by positivity) hsq
    rw [lt_div_iff₀ (by positivity)]
    nlinarith
  have hside_hi : 50 / (153 * sqrt 2) < (50 / 157 : ℝ) := by
    have hsq : (157 : ℝ) ^ 2 < (153 * sqrt 2) ^ 2 := by
      rw [mul_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    have hlt : (157 : ℝ) < 153 * sqrt 2 :=
      lt_of_pow_lt_pow_left₀ 2 (by norm_num) hsq
    rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [div_lt_div_iff₀ (by norm_num) (mul_pos (by norm_num) hx)]
    nlinarith
  · rw [div_lt_div_iff₀ (mul_pos (by norm_num) hx) (by norm_num)]
    nlinarith
  · have hden : 0 < 2 * sqrt 2 * squarePhase := by positivity
    have hrad : 50 / (157 * sqrt 2) < 1 / (2 * sqrt 2 * squarePhase) := by
      rw [div_lt_div_iff₀ (mul_pos (by norm_num) hs) hden]
      have : 50 * (2 * sqrt 2 * squarePhase) < 157 * sqrt 2 := by
        have : 100 * squarePhase < 157 := by nlinarith
        nlinarith [hs]
      simpa [mul_assoc, mul_left_comm, mul_comm] using this
    linarith
  · have hden : 0 < 2 * sqrt 2 * squarePhase := by positivity
    have hrad : 1 / (2 * sqrt 2 * squarePhase) < 50 / (153 * sqrt 2) := by
      rw [div_lt_div_iff₀ hden (mul_pos (by norm_num) hs)]
      have : 153 * sqrt 2 < 50 * (2 * sqrt 2 * squarePhase) := by
        have : (153 : ℝ) < 100 * squarePhase := by nlinarith
        nlinarith [hs]
      simpa [mul_assoc, mul_left_comm, mul_comm] using this
    linarith

/-! ### Forces -/

/-- At `x = π` the outward factor `4π²/cosh π` is strictly less than `7/2`. -/
theorem plateau_lt_seven_halves : 4 * π ^ 2 / cosh π < 7 / 2 := by
  have hπlo : 3141592 / 1000000 < π := by
    have h := pi_gt_d6
    norm_num at h
    have heq : (392699 / 125000 : ℝ) = 3141592 / 1000000 := by norm_num
    linarith
  have hπhi : π < 3141593 / 1000000 := by
    have h := pi_lt_d6
    norm_num at h
    exact h
  have hδ : (141592 / 1000000 : ℝ) < π - 3 := by linarith
  have hexpδ : 1 + 141592 / 1000000 < exp (π - 3) := by
    have hle := Real.add_one_le_exp (141592 / 1000000 : ℝ)
    have hlt : exp (141592 / 1000000 : ℝ) < exp (π - 3) :=
      exp_strictMono hδ
    linarith
  have he3 : (2.7182818283 : ℝ) ^ 3 < exp 3 := by
    have hid : exp 3 = exp 1 ^ 3 := by
      rw [show (3 : ℝ) = (3 : ℕ) * 1 by norm_num, exp_nat_mul]
    rw [hid]
    exact pow_lt_pow_left₀ exp_one_gt_d9 (by norm_num) (by decide)
  have hsplit : exp π = exp 3 * exp (π - 3) := by
    rw [← exp_add]
    ring_nf
  have hexp : (2.7182818283 : ℝ) ^ 3 * (1 + 141592 / 1000000) < exp π := by
    rw [hsplit]
    exact mul_lt_mul he3 hexpδ.le (by positivity) (exp_pos _).le
  have hnum : 16 * (3141593 / 1000000 : ℝ) ^ 2 <
      7 * ((2.7182818283 : ℝ) ^ 3 * (1 + 141592 / 1000000)) := by
    norm_num
  have hπsq : π ^ 2 < (3141593 / 1000000 : ℝ) ^ 2 :=
    pow_lt_pow_left₀ hπhi pi_nonneg (by decide)
  have h16 : 16 * π ^ 2 < 7 * exp π := by
    have hleft : 16 * π ^ 2 < 16 * (3141593 / 1000000 : ℝ) ^ 2 := by
      nlinarith
    linarith
  have hc : 0 < cosh π := cosh_pos π
  have hcosh : exp π < exp π + exp (-π) := by
    linarith [exp_pos (-π)]
  have h14 : 7 * exp π < 14 * cosh π := by
    rw [cosh_eq]
    linarith
  have hgoal : 16 * π ^ 2 < 14 * cosh π := lt_trans h16 h14
  rw [div_lt_iff₀ hc]
  linarith

private lemma gamma_high_gt_neg_sq :
    -((153 / 100 : ℝ) ^ 2) < gammaSEqual (157 / 100) := by
  have hlo := gamma_oneFiveSeven_lower
  have hcmp : -((153 / 100 : ℝ) ^ 2) <
      gammaLower ((2.7182818286 : ℝ) * (1769 / 1000))
        (sinLo (3.141592 / 2 - 157 / 100) (3.141593 / 2 - 157 / 100) -
          cosHi (3.141592 / 2 - 157 / 100) (3.141593 / 2 - 157 / 100))
        (sinLo (3.141592 / 2 - 157 / 100) (3.141593 / 2 - 157 / 100) +
          cosLo (3.141593 / 2 - 157 / 100)) := by
    simp only [gammaLower, sinLo, cosLo, cosHi]
    norm_num
  linarith

/-- The diagonal force at the square, in units of `k e²/ℓ²`, exceeds `4`. -/
theorem square_diag_force_gt_four :
    4 < 4 * squarePhase ^ 2 / -gammaSEqual squarePhase := by
  have hwin := squarePhase_num_window
  have hx : squarePhase ∈ Ioo resonanceRoot1 π :=
    ⟨squarePhase_spec.1.1, lt_trans hwin.2 (by linarith [pi_gt_three])⟩
  have hγ : gammaSEqual squarePhase < 0 := gammaSEqual_neg_right_of_first_node hx
  have hanti := strictAntiOn_gammaSEqual_even 0
  have hγlt : gammaSEqual (157 / 100) < gammaSEqual squarePhase :=
    hanti
      (mem_gamma_Icc (le_of_lt (lt_trans (by norm_num) hwin.1))
        (le_of_lt (lt_trans hwin.2 (by linarith [pi_gt_three]))))
      (mem_gamma_Icc (by norm_num : (0 : ℝ) ≤ 157 / 100) (by linarith [pi_gt_three]))
      hwin.2
  have habs : -gammaSEqual squarePhase < (153 / 100 : ℝ) ^ 2 := by
    linarith [gamma_high_gt_neg_sq, hγlt]
  have hsq : (153 / 100 : ℝ) ^ 2 < squarePhase ^ 2 := by
    have hpos : (0 : ℝ) ≤ 153 / 100 := by norm_num
    exact pow_lt_pow_left₀ hwin.1 hpos (by decide)
  have hden : 0 < -gammaSEqual squarePhase := by linarith
  rw [lt_div_iff₀ hden]
  nlinarith

/-- The side force exceeds `2√2` in the same units. -/
theorem square_side_force_gt_two_sqrt_two :
    2 * sqrt 2 <
      (4 * squarePhase ^ 2 / -gammaSEqual squarePhase) / sqrt 2 := by
  have h := square_diag_force_gt_four
  have hs : 0 < sqrt 2 := sqrt_pos.mpr (by norm_num)
  have hid : 4 / sqrt 2 = 2 * sqrt 2 := by
    field_simp [hs.ne']
    rw [sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hdiv : 4 / sqrt 2 <
      (4 * squarePhase ^ 2 / -gammaSEqual squarePhase) / sqrt 2 :=
    div_lt_div_of_pos_right h hs
  linarith [hid]

/-- Identifying the side with one Bohr radius would place the first node
strictly between `91/40` and `12/5` Bohr radii. -/
theorem bohr_side_ratio_window :
    (91 / 40 : ℝ) < sqrt 2 * squarePhase / resonanceRoot1 ∧
      sqrt 2 * squarePhase / resonanceRoot1 < 12 / 5 := by
  have hx := squarePhase_num_window
  have hr := firstNode_num_window
  have hslo := sqrt_two_bounds.1
  have hshi := sqrt_two_bounds.2
  have hroot : 0 < resonanceRoot1 := lt_trans (by norm_num) hr.1
  constructor
  · have hlow : (91 / 40 : ℝ) < (140 / 99) * (153 / 100) / (19 / 20) := by
      norm_num
    have hcmp : (140 / 99) * (153 / 100) / (19 / 20) <
        sqrt 2 * squarePhase / resonanceRoot1 := by
      have hnum : (140 / 99) * (153 / 100) < sqrt 2 * squarePhase := by
        have h1 : (140 / 99) * (153 / 100) < sqrt 2 * (153 / 100) := by
          exact mul_lt_mul_of_pos_right hslo (by norm_num)
        have h2 : sqrt 2 * (153 / 100) < sqrt 2 * squarePhase :=
          mul_lt_mul_of_pos_left hx.1 (sqrt_pos.mpr (by norm_num))
        linarith
      have hden : resonanceRoot1 < 19 / 20 := hr.2
      rw [div_lt_div_iff₀ (by norm_num) hroot]
      nlinarith
    linarith
  · have hhigh : (99 / 70) * (157 / 100) / (14 / 15) < (12 / 5 : ℝ) := by
      norm_num
    have hcmp : sqrt 2 * squarePhase / resonanceRoot1 <
        (99 / 70) * (157 / 100) / (14 / 15) := by
      have hnum : sqrt 2 * squarePhase < (99 / 70) * (157 / 100) := by
        have h1 : sqrt 2 * squarePhase < sqrt 2 * (157 / 100) :=
          mul_lt_mul_of_pos_left hx.2 (sqrt_pos.mpr (by norm_num))
        have h2 : sqrt 2 * (157 / 100) < (99 / 70) * (157 / 100) :=
          mul_lt_mul_of_pos_right hshi (by norm_num)
        linarith
      rw [div_lt_div_iff₀ hroot (by norm_num)]
      nlinarith [hr.1]
    linarith

/-! ### The radii in one order -/

noncomputable def quietPhase : ℝ :=
  Classical.choose (exists_unique_forceQuiet).exists

theorem quietPhase_spec :
    quietPhase ∈ Ioo (5 / 2) π ∧ forceCrit quietPhase = 0 :=
  Classical.choose_spec (exists_unique_forceQuiet).exists

theorem secondNode_radius_window :
    1 / (3 * π) < 1 / (2 * branchNode 1) ∧ 1 / (2 * branchNode 1) < 2 / (5 * π) := by
  have hspec := branchNode_spec 1
  have hsharp := node_mem_sharp_branch 1 hspec.1 hspec.2
  simp only [Nat.cast_one, one_mul] at hsharp
  have hx : 0 < branchNode 1 := by linarith [pi_pos, hsharp.1]
  constructor
  · rw [div_lt_div_iff₀ (mul_pos (by norm_num) pi_pos) (mul_pos (by norm_num) hx)]
    nlinarith [hsharp.2]
  · rw [div_lt_div_iff₀ (mul_pos (by norm_num) hx) (mul_pos (by norm_num) pi_pos)]
    nlinarith [hsharp.1]

/-- Circular radius, first node, diagonal, side, one-electron extremum, and
second node, each outside the next. Radii are in units of `ℓ`. -/
theorem shell_radius_order :
    1 / (2 * resonanceRoot1) < 5 / 6 ∧
      1 / (2 * squarePhase) < 1 / (2 * resonanceRoot1) ∧
      1 / (2 * sqrt 2 * squarePhase) < 1 / (2 * squarePhase) ∧
      1 / (2 * quietPhase) < 1 / (2 * sqrt 2 * squarePhase) ∧
      1 / (2 * branchNode 1) < 1 / (2 * quietPhase) := by
  have hnode := firstNode_radius_window
  have hsq := square_radius_window
  have hquiet := forceQuiet_radius quietPhase_spec.1
  have hsec := secondNode_radius_window
  have hfive : (15 / 28 : ℝ) < 5 / 6 := by norm_num
  have hsep : (50 / 153 : ℝ) < 10 / 19 := by norm_num
  have hpi : (2 / (5 * π) : ℝ) < 1 / (2 * π) := by
    rw [div_lt_div_iff₀ (mul_pos (by norm_num) pi_pos) (mul_pos (by norm_num) pi_pos)]
    nlinarith [pi_pos]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · linarith
  · linarith
  · have hs : (1 : ℝ) < sqrt 2 := one_lt_sqrt_two
    have hx : 0 < squarePhase := lt_trans (by norm_num) squarePhase_num_window.1
    rw [div_lt_div_iff₀ (mul_pos (mul_pos (by norm_num) (sqrt_pos.mpr (by norm_num))) hx)
      (mul_pos (by norm_num) hx)]
    nlinarith
  · linarith [hquiet.2, hsq.2.2.1]
  · linarith [hquiet.1]

end Gravity

end DstDiophantine
