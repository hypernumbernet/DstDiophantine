import DstDiophantine.Logic.Amplitude
import DstDiophantine.Logic.BalancedResidual
import DstDiophantine.Logic.Example.BealRegime
import DstDiophantine.Theorems.BealResidualSearch
import DstDiophantine.Algebra.Amplification

set_option linter.style.nativeDecide false

/-!
# Phase 7p / 7r: Beal regime witnesses (D4L ↔ Theorems)

Connects `Logic.Example.BealRegime` to the exponent-shape filter
`IsClosedShapeExponents` and the L3 balanced class.

**Not** re-exported from `Basic`. The Diophantine public API exposes residual
types and the shape filter; this module is the witness layer that reads those
shapes as D4L labels. A `.U → .T` atlas update lives in
`Logic.Example.BealRegime` and does not silently promote classical Beal
(`artefacts_not_entailsTR_beal`).

Unconditional classical Beal is **not** claimed.
-/

namespace DstDiophantine

namespace Theorems

open Logic Amplification Admissible Invariant

/-! ### Open-residual Bool ↔ regime label `U` -/

/--
Classifier of exponent triples, landing in `{T, U, F}` and never `B`:

* `U` — Beal-range open residual (`isOpenResidualExponents`)
* `T` — Beal-range closed *shape* (`IsClosedShapeExponents`)
* `F` — exponents outside Beal range (`min < 3`)

Bookkeeping `B` is an atlas status for identities, not for exponent triples.
The `|u| = 1` Mihăilescu slice is `T` on the atlas and does not force `T` here.
-/
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

/-- Even permutation `(3,4,4)` is *not* Darmon–Merel; it is even two-equal. -/
theorem classifyBealExponents_three_four_four :
    classifyBealExponents 3 4 4 = .U := by native_decide

theorem classifyBealExponents_four_three_four :
    classifyBealExponents 4 3 4 = .U := by native_decide

/-- Even permutation `(5,4,4)` is *not* signature `(n,n,5)`. -/
theorem classifyBealExponents_five_four_four :
    classifyBealExponents 5 4 4 = .U := by native_decide

theorem classifyBealExponents_three_three_five :
    classifyBealExponents 3 3 5 = .U := by native_decide

theorem classifyBealExponents_two_three_three :
    classifyBealExponents 2 3 3 = .F := by native_decide

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
