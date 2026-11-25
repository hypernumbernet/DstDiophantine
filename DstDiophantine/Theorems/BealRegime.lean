import DstDiophantine.Logic.Amplitude
import DstDiophantine.Logic.BalancedResidual
import DstDiophantine.Logic.Example.BealRegime
import DstDiophantine.Theorems.BealResidualSearch
import DstDiophantine.Algebra.Amplification

set_option linter.style.native false

/-!
# Exponent regime labels

`classifyBealExponents` marks a closed shape `T` or the open residual `U`, and never bookkeeping
`B`. A `.U` label does not claim classical Beal.
-/

namespace DstDiophantine

namespace Theorems

open Logic Amplification Admissible Invariant

/-! ### Open-residual Bool ↔ regime label `U` -/

/-- `T` closed shape, `U` open residual, `F` off range. Never bookkeeping `B`. -/
def classifyBealExponents (x y z : ℕ) : TruthValue :=
  if isOpenResidualExponents x y z then .U
  else if 3 ≤ x ∧ 3 ≤ y ∧ 3 ≤ z then .T
  else .F

theorem classifyBealExponents_ne_B (x y z : ℕ) :
    classifyBealExponents x y z ≠ .B := by
  unfold classifyBealExponents
  split_ifs <;> decide

theorem classifyBealExponents_eq_U_iff {x y z : ℕ} :
    classifyBealExponents x y z = .U ↔
      isOpenResidualExponents x y z = true := by
  unfold classifyBealExponents
  split_ifs <;> simp_all

theorem classifyBealExponents_eq_T_iff {x y z : ℕ} :
    classifyBealExponents x y z = .T ↔ IsClosedShapeExponents x y z := by
  constructor
  · intro h
    unfold classifyBealExponents at h
    by_cases hopen : isOpenResidualExponents x y z = true
    · simp [hopen] at h
    · have hfalse : isOpenResidualExponents x y z = false :=
        Bool.eq_false_iff.mpr hopen
      by_cases hrange : 3 ≤ x ∧ 3 ≤ y ∧ 3 ≤ z
      · simp [hfalse, hrange] at h
        exact isClosedShapeExponents_of_range_not_open
          hrange.1 hrange.2.1 hrange.2.2 hfalse
      · simp [hfalse, hrange] at h
  · intro hclosed
    unfold classifyBealExponents
    have hfalse := isOpenResidualExponents_eq_false_of_closed hclosed
    have hrange : 3 ≤ x ∧ 3 ≤ y ∧ 3 ≤ z :=
      ⟨hclosed.1, hclosed.2.1, hclosed.2.2.1⟩
    simp [hfalse, hrange]

theorem classifyBealExponents_eq_F_iff {x y z : ℕ} :
    classifyBealExponents x y z = .F ↔ ¬ (3 ≤ x ∧ 3 ≤ y ∧ 3 ≤ z) := by
  constructor
  · intro h
    unfold classifyBealExponents at h
    by_cases hopen : isOpenResidualExponents x y z = true
    · simp [hopen] at h
    · have hfalse : isOpenResidualExponents x y z = false :=
        Bool.eq_false_iff.mpr hopen
      by_cases hrange : 3 ≤ x ∧ 3 ≤ y ∧ 3 ≤ z
      · simp [hfalse, hrange] at h
      · exact hrange
  · intro hrange
    unfold classifyBealExponents
    by_cases hopen : isOpenResidualExponents x y z = true
    · have hop := isOpenResidualExponents_iff.mp hopen
      exact (hrange ⟨hop.1, hop.2.1, hop.2.2.1⟩).elim
    · have hfalse : isOpenResidualExponents x y z = false :=
        Bool.eq_false_iff.mpr hopen
      simp [hfalse, hrange]

theorem classifyBealExponents_eq_T_or_U_or_F (x y z : ℕ) :
    classifyBealExponents x y z = .T ∨
      classifyBealExponents x y z = .U ∨
        classifyBealExponents x y z = .F := by
  cases h : classifyBealExponents x y z with
  | T => exact Or.inl rfl
  | U => exact Or.inr (Or.inl rfl)
  | F => exact Or.inr (Or.inr rfl)
  | B => exact absurd h (classifyBealExponents_ne_B x y z)

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

/-! ### Shape examples: closed slices vs even permutations that stay live -/

theorem classifyBealExponents_three_three_three :
    classifyBealExponents 3 3 3 = .T := by native_decide

theorem classifyBealExponents_four_four_three :
    classifyBealExponents 4 4 3 = .T := by native_decide

theorem classifyBealExponents_three_five_five :
    classifyBealExponents 3 5 5 = .T := by native_decide

theorem classifyBealExponents_four_four_five :
    classifyBealExponents 4 4 5 = .T := by native_decide

/-- `(3,4,4)` is not Darmon–Merel; it is even two-equal. -/
theorem classifyBealExponents_three_four_four :
    classifyBealExponents 3 4 4 = .U := by native_decide

theorem classifyBealExponents_four_three_four :
    classifyBealExponents 4 3 4 = .U := by native_decide

/-- `(5,4,4)` is not signature `(n,n,5)`. -/
theorem classifyBealExponents_five_four_four :
    classifyBealExponents 5 4 4 = .U := by native_decide

theorem classifyBealExponents_three_three_five :
    classifyBealExponents 3 3 5 = .T := by native_decide

theorem classifyBealExponents_three_three_four :
    classifyBealExponents 3 3 4 = .T := by native_decide

theorem classifyBealExponents_five_three_three :
    classifyBealExponents 5 3 3 = .T := by native_decide

theorem classifyBealExponents_three_four_three :
    classifyBealExponents 3 4 3 = .T := by native_decide

theorem classifyBealExponents_three_three_seven :
    classifyBealExponents 3 3 7 = .T := by native_decide

/-- Even `8` is closed with no appeal to the `10^9` bound. -/
theorem classifyBealExponents_three_three_eight :
    classifyBealExponents 3 3 8 = .T := by native_decide

/-- An even companion past `10^9` stays closed; the next odd companion does not. -/
theorem classifyBealExponents_three_three_past_bound :
    classifyBealExponents 3 3 1000000002 = .T ∧
      classifyBealExponents 3 3 1000000001 = .U := by
  native_decide

theorem classifyBealExponents_three_four_five :
    classifyBealExponents 3 4 5 = .T := by native_decide

theorem classifyBealExponents_five_three_four :
    classifyBealExponents 5 3 4 = .T := by native_decide

/-- `(3,5,7)` stays in the all-distinct body. -/
theorem classifyBealExponents_three_five_seven :
    classifyBealExponents 3 5 7 = .U := by native_decide

theorem classifyBealExponents_repeated_fifth :
    classifyBealExponents 5 5 7 = .T ∧ classifyBealExponents 7 5 5 = .T ∧
      classifyBealExponents 5 7 5 = .T ∧ classifyBealExponents 5 5 19 = .T ∧
        classifyBealExponents 19 5 5 = .T ∧ classifyBealExponents 5 5 11 = .U := by
  native_decide

theorem classifyBealExponents_six_six_seven :
    classifyBealExponents 6 6 7 = .T := by native_decide

theorem classifyBealExponents_nine_nine_four :
    classifyBealExponents 9 9 4 = .T := by native_decide

theorem classifyBealExponents_three_six_five :
    classifyBealExponents 3 6 5 = .T := by native_decide

/-- `(5,6,6)` is closed because the common exponent is divisible by `3`. -/
theorem classifyBealExponents_five_six_six :
    classifyBealExponents 5 6 6 = .T := by native_decide

theorem classifyBealExponents_four_four_seven :
    classifyBealExponents 4 4 7 = .T := by native_decide

/-- `(4,7,7)` stays open; it is not a fourth-power sum. -/
theorem classifyBealExponents_fourth_sum :
    classifyBealExponents 8 8 7 = .T ∧ classifyBealExponents 4 4 9 = .T ∧
      classifyBealExponents 4 7 7 = .U := by
  native_decide

theorem classifyBealExponents_fifth_pair :
    classifyBealExponents 10 10 7 = .T ∧ classifyBealExponents 10 10 19 = .T ∧
      classifyBealExponents 7 10 10 = .T ∧ classifyBealExponents 5 10 7 = .T ∧
        classifyBealExponents 25 25 7 = .T ∧ classifyBealExponents 5 5 21 = .T ∧
          classifyBealExponents 10 10 14 = .T ∧
            classifyBealExponents 22 22 7 = .U ∧
              classifyBealExponents 5 5 11 = .U := by
  native_decide

/-- `(10,10,9)` is a shared exponent beside a multiple of `3`.
`(5,5,11)` and `(3,5,7)` stay open. -/
theorem classifyBealExponents_shared_exp :
    classifyBealExponents 10 10 9 = .T ∧ classifyBealExponents 14 14 9 = .T ∧
      classifyBealExponents 14 14 25 = .T ∧ classifyBealExponents 8 12 9 = .T ∧
        classifyBealExponents 9 7 7 = .T ∧ classifyBealExponents 10 10 11 = .U ∧
          classifyBealExponents 5 5 11 = .U ∧ classifyBealExponents 3 5 7 = .U ∧
            classifyBealExponents 22 22 7 = .U := by
  native_decide

theorem classifyBealExponents_nine_nine_past_bound :
    classifyBealExponents 9 9 1000000001 = .U := by native_decide

theorem classifyBealExponents_two_three_three :
    classifyBealExponents 2 3 3 = .F := by native_decide

/-! ### L3 seat vs open-residual `U` -/

theorem beal_balanced_diagnostic_seat :
    balancedAmplitude.IsBalancedMassive ∧ ¬ balancedAmplitude.IsVacuum :=
  ⟨balancedAmplitude_isBalancedMassive,
    Amplitude.not_vacuum_of_balancedMassive balancedAmplitude_isBalancedMassive⟩

theorem open_residual_U_not_implies_balancedSeat :
    classifyBealExponents 3 5 7 = .U ∧
      IsWindowSeed halfWindowSeed ∧
        ¬ BalancedResidualClass halfWindowSeed := by
  refine ⟨?_, halfWindowSeed_isWindowSeed, halfWindowSeed_not_balanced⟩
  exact classifyBealExponents_three_five_seven

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
  have hθπ : Real.log 2 / (m : ℝ) ≤ Real.pi / 2 := by
    have hle : Real.log 2 / (m : ℝ) ≤ Real.log 2 :=
      div_le_self log_two_nonneg_beal (Nat.one_le_cast.mpr (Nat.succ_le_of_lt hm))
    have hlt : Real.log 2 < Real.pi / 2 :=
      lt_trans log_two_lt_one_beal (by linarith [Real.pi_gt_three])
    exact hle.trans (le_of_lt hlt)
  exact ⟨hθ0, hθπ⟩

theorem beal_model_rapidity_measure_pos {m : ℕ} (hm : 0 < m) :
    0 < Invariant.JNormalized (Amplification.pureBoost (Real.log 2 / (m : ℝ))) := by
  rw [Amplification.JNormalized_pureBoost]
  refine mul_pos (by positivity) (sq_pos_of_pos ?_)
  exact div_pos (Real.log_pos (by norm_num : (1 : ℝ) < 2)) (Nat.cast_pos.mpr hm)

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
