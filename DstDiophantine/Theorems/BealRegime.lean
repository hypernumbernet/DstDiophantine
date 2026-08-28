import DstDiophantine.Logic.Amplitude
import DstDiophantine.Logic.BalancedResidual
import DstDiophantine.Logic.Example.BealRegime
import DstDiophantine.Theorems.BealResidualSearch
import DstDiophantine.Algebra.Amplification

set_option linter.style.nativeDecide false

/-!
# Phase 7p / 7r: Beal regime witnesses (D4L ↔ Theorems)

Connects `Logic.Example.BealRegime` to the open-residual Bool filter and the
L3 balanced class. **Not** re-exported from `Basic`.

Unconditional classical Beal is **not** claimed.
-/

namespace DstDiophantine

namespace Theorems

open Logic Amplification Admissible Invariant

/-! ### Open-residual Bool ↔ regime label `U` -/

/--
* `U` — open residual (`isOpenResidualExponents`)
* `T` — Beal-range exponents not flagged open
* `F` — exponents outside Beal range (`min < 3`)
-/
def classifyBealExponents (x y z : ℕ) : TruthValue :=
  if isOpenResidualExponents x y z then .U
  else if 3 ≤ x ∧ 3 ≤ y ∧ 3 ≤ z then .T
  else .F

theorem classifyBealExponents_eq_U_iff {x y z : ℕ} :
    classifyBealExponents x y z = .U ↔
      isOpenResidualExponents x y z = true := by
  unfold classifyBealExponents
  split_ifs <;> simp_all

theorem open_residual_hit_is_coprime_beal
    {A B x y z : ℕ}
    (h : isOpenResidualBealPerfectPower A B x y z = true) :
    ∃ C' : ℕ,
      3 ≤ x ∧ 3 ≤ y ∧ 3 ≤ z ∧
        0 < A ∧ 0 < B ∧ 0 < C' ∧
          A ^ x + B ^ y = C' ^ z ∧
            Nat.gcd A (Nat.gcd B C') = 1 ∧
              isOpenResidualExponents x y z = true ∧
                classifyBealExponents x y z = .U := by
  obtain ⟨hopen, ⟨C', hx, hy, hz, hA, hB, hC', hsol, hgcd⟩⟩ :=
    isOpenResidualBealPerfectPower_sound h
  exact ⟨C', hx, hy, hz, hA, hB, hC', hsol, hgcd, hopen,
    classifyBealExponents_eq_U_iff.mpr hopen⟩

/-! ### L3 seat vs open-residual `U` -/

theorem beal_balanced_diagnostic_seat :
    balancedAmplitude.IsBalancedMassive ∧ ¬ balancedAmplitude.IsVacuum :=
  ⟨balancedAmplitude_isBalancedMassive,
    Amplitude.not_vacuum_of_balancedMassive balancedAmplitude_isBalancedMassive⟩

/-- Open-residual `U` is not sufficient for the L3 balanced seat. -/
theorem open_residual_U_not_implies_balancedSeat :
    classifyBealExponents 3 4 5 = .U ∧
      IsWindowSeed halfWindowSeed ∧
        ¬ BalancedResidualClass halfWindowSeed := by
  refine ⟨?_, halfWindowSeed_isWindowSeed, halfWindowSeed_not_balanced⟩
  exact classifyBealExponents_eq_U_iff.mpr (by native_decide)

/-! ### Model rapidity `pureBoost (log 2 / m)` is outside L3 -/

private theorem log_two_nonneg_beal : 0 ≤ Real.log 2 :=
  Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)

private theorem log_two_lt_one_beal : Real.log 2 < 1 := by
  have h := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) (by norm_num)
  linarith [h]

theorem isAdmissibleContinuous_beal_model_rapidity {m : ℕ} (hm : 0 < m) :
    Admissible.IsAdmissibleContinuous (Amplification.pureBoost (Real.log 2 / (m : ℝ))) := by
  refine (Amplification.isAdmissibleContinuous_pureBoost_iff _).mpr ?_
  have hmpos : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hθ0 : 0 ≤ Real.log 2 / (m : ℝ) := div_nonneg log_two_nonneg_beal hmpos.le
  have hone_pi : (1 : ℝ) < Real.pi / 2 := by nlinarith [Real.pi_gt_three]
  have hθπ : Real.log 2 / (m : ℝ) ≤ Real.pi / 2 := by
    have hle : Real.log 2 / (m : ℝ) ≤ Real.log 2 :=
      div_le_self log_two_nonneg_beal (Nat.one_le_cast.mpr (Nat.succ_le_of_lt hm))
    exact le_trans hle (log_two_lt_one_beal.trans hone_pi).le
  exact ⟨hθ0, hθπ⟩

theorem beal_model_rapidity_measure_pos {m : ℕ} (hm : 0 < m) :
    0 < Invariant.JNormalized (Amplification.pureBoost (Real.log 2 / (m : ℝ))) := by
  rw [Amplification.JNormalized_pureBoost]
  refine mul_pos (by positivity) (sq_pos_of_pos ?_)
  exact div_pos (Real.log_pos (by norm_num : (1 : ℝ) < 2)) (Nat.cast_pos.mpr hm)

/-- Beal model rapidity is boost-dominant (`J > 0`), not `BalancedResidualClass`. -/
theorem beal_model_rapidity_not_mem_balancedResidualClass {m : ℕ} (hm : 0 < m) :
    ¬ BalancedResidualClass
        ⟨Amplification.pureBoost (Real.log 2 / (m : ℝ)),
          isAdmissibleContinuous_beal_model_rapidity hm⟩ := by
  intro h
  have hmeas := (balancedResidualClass_iff_measure _).mp h
  have hpos := beal_model_rapidity_measure_pos hm
  exact (ne_of_gt hpos) hmeas.1

end Theorems

end DstDiophantine
