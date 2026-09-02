import DstDiophantine.Framework.Spectrum
import Mathlib.Tactic.NormNum

set_option linter.style.nativeDecide false

/-!
# Finite certificates for the discrete mismatch spectrum

One-axis and three-axis mismatch sets are finite `Finset`s, so occupancy of
any given integer slot is decidable.  The certificates below record:

* `K = 1` (`N = 4`): the bound interval is fully occupied;
* `K = 2` (`N = 8`): holes at `|Δ| ∈ {10, 11}`;
* `K = 3` (`N = 12`): a strictly larger hole set inside `[-27, 27]`;
* zero-height counts strictly above the balanced cube once `K ≥ 1`.
-/

namespace DstDiophantine

namespace Framework

open Finset

/-! ### `K = 1` (`N = 4`): no holes -/

theorem axisMismatchSet_one : axisMismatchSet 1 = {(-1 : ℤ), 0, 1} := by
  native_decide

theorem threeMismatchSet_one :
    threeMismatchSet 1 = mismatchInterval 1 := by
  native_decide

theorem mismatchHoles_one : mismatchHoles 1 = ∅ := by
  native_decide

theorem zeroHeight_card_one : (zeroHeightTriples 1).card = 7 := by
  native_decide

theorem balanced_card_one : (balancedTriples 1).card = 1 := by
  native_decide

/-! ### `K = 2` (`N = 8`): first spectral holes -/

theorem axisMismatchSet_two : axisMismatchSet 2 = {(-4 : ℤ), -1, 0, 1, 4} := by
  native_decide

theorem ten_not_mem_threeMismatchSet_two : (10 : ℤ) ∉ threeMismatchSet 2 := by
  native_decide

theorem eleven_not_mem_threeMismatchSet_two : (11 : ℤ) ∉ threeMismatchSet 2 := by
  native_decide

theorem neg_ten_not_mem_threeMismatchSet_two : (-10 : ℤ) ∉ threeMismatchSet 2 := by
  native_decide

theorem neg_eleven_not_mem_threeMismatchSet_two : (-11 : ℤ) ∉ threeMismatchSet 2 := by
  native_decide

theorem mismatchHoles_two :
    mismatchHoles 2 = {(-11 : ℤ), -10, 10, 11} := by
  native_decide

theorem threeMismatchSet_two_card : (threeMismatchSet 2).card = 21 := by
  native_decide

theorem zeroHeight_card_two : (zeroHeightTriples 2).card = 32 := by
  native_decide

theorem balanced_card_two : (balancedTriples 2).card = 8 := by
  native_decide

/-! ### `K = 3` (`N = 12`) -/

theorem one_mem_threeMismatchSet_three : (1 : ℤ) ∈ threeMismatchSet 3 := by
  native_decide

theorem mismatchHoles_three_nonempty : mismatchHoles 3 ≠ ∅ := by
  native_decide

theorem mismatchHoles_three :
    mismatchHoles 3 =
      {(-26 : ℤ), -25, -24, -23, -20, 20, 23, 24, 25, 26} := by
  native_decide

theorem mismatchHoles_three_card : (mismatchHoles 3).card = 10 := by
  native_decide

theorem twenty_not_mem_threeMismatchSet_three : (20 : ℤ) ∉ threeMismatchSet 3 := by
  native_decide

theorem twenty_three_not_mem_threeMismatchSet_three :
    (23 : ℤ) ∉ threeMismatchSet 3 := by
  native_decide

theorem twenty_four_not_mem_threeMismatchSet_three :
    (24 : ℤ) ∉ threeMismatchSet 3 := by
  native_decide

theorem twenty_five_not_mem_threeMismatchSet_three :
    (25 : ℤ) ∉ threeMismatchSet 3 := by
  native_decide

theorem twenty_six_not_mem_threeMismatchSet_three :
    (26 : ℤ) ∉ threeMismatchSet 3 := by
  native_decide

theorem threeMismatchSet_three_card : (threeMismatchSet 3).card = 45 := by
  native_decide

theorem zeroHeight_card_three : (zeroHeightTriples 3).card = 68 := by
  native_decide

theorem balanced_card_three : (balancedTriples 3).card = 8 := by
  native_decide

/-- Occupied three-axis mismatches form a proper subset of the bound interval
as soon as `K = 2`. -/
theorem threeMismatchSet_proper_subset_interval_two :
    threeMismatchSet 2 ⊂ mismatchInterval 2 := by
  refine Finset.ssubset_iff_subset_ne.2 ⟨threeMismatchSet_subset_interval 2, ?_⟩
  intro h
  have h10 : (10 : ℤ) ∈ mismatchInterval 2 :=
    mem_mismatchInterval.2 (by norm_num)
  exact ten_not_mem_threeMismatchSet_two (h ▸ h10)

end Framework

end DstDiophantine
