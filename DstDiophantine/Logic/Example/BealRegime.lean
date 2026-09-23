import DstDiophantine.Logic.Regime
import Mathlib.Tactic.IntervalCases

/-!
# Phase 7p / 7r / 7s: abstract Beal residual atlas (D4L regime layer)

Atoms are names only (no `Theorems` import). Arithmetic witnesses live in
`Theorems.BealRegime`. Layout: slices `T` (0–3), diagnostics `F` (4–5),
bookkeeping `B` (6), live residuals `U` (7–13; Odd/AllDistinct/UnequalOdd
split at 11–13), conjecture `U` (14), closed `(n,n,5)` slice `T` (15),
closed two-cube fourth/fifth-power slice `T` (16).

Correspondence with residual *types* (comments only; types live in Theorems):

* `sliceFLT` — `d ≥ 3` (`not_beal_sol_of_expGcd_ge_three`)
* `sliceDM` — Darmon–Merel cube positions (`not_beal_two_equal_cube_slice`)
* `sliceAbsOne` — equal-odd `|u| = 1` (Mihăilescu; coefficient, not a shape)
* `sliceFourth` — `d = 2` with two fourth-divisible exponents
* `sliceNN5` — signature `(n,n,5)` (`not_beal_two_equal_fifth_slice`)
* `sliceBruin` — two cubes summing to a fourth or fifth power
  (`not_beal_bruin_two_cube_shape`)
* `diagModular` / `diagBalanced` — demoted winding / balanced-seed diagnostics
* `bookRealization` — CGA discrete closure ≡ `|A| = 1`
* `liveMordell` — `BealMordellCubeAddTwoResidual`
* `liveGeFive` — `BealEqualOddTwoFactorExpGeFiveResidual`
* `liveDiffPP` — `BealTwoEqualEvenDiffPerfectPowerResidual`
* `liveSumOut` — `BealTwoEqualEvenSumExpGeSevenResidual`
* `liveOdd` — `BealTwoEqualOddResidual`
* `liveAllDistinct` — `BealAllDistinctExpResidual`
* `liveUnequalOdd` — `BealPythagoreanUnequalOddResidual`
* `bealConjecture` — positive coprime Beal

The status board does **not** encode the arithmetic assembly
`beal_conjecture_pos_of_fine_residuals_even_split`. Promoting a live atom
from `U` to `T` therefore cannot silently `T`-entail the conjecture; even
the full artefact set fails to. Unconditional classical Beal is not claimed.
-/

namespace DstDiophantine

namespace Logic

open RegimeFormula

/-! ### Named atoms -/

/-- Closed slice: `bealExpGcd ≥ 3` (FLT axiom). -/
def sliceFLT : RegimeFormula := atom 0
/-- Closed slice: Darmon–Merel cube positions. -/
def sliceDM : RegimeFormula := atom 1
/-- Closed slice: equal-odd `|u| = 1` (Mihăilescu). -/
def sliceAbsOne : RegimeFormula := atom 2
/-- Closed slice: `d = 2` with at least two exponents divisible by 4. -/
def sliceFourth : RegimeFormula := atom 3

/-- Diagnostic: modular payload incompatible with conformal gauge. -/
def diagModular : RegimeFormula := atom 4
/-- Diagnostic: balanced seed below continuous threshold. -/
def diagBalanced : RegimeFormula := atom 5

/-- Bookkeeping: CGA discrete closure ≡ `|A| = 1`. -/
def bookRealization : RegimeFormula := atom 6

/-- Live residual: Mordell `y² = x³ - 1728` rank. -/
def liveMordell : RegimeFormula := atom 7
/-- Live residual: equal-odd `e ≥ 5` and `|u| ≥ 3`. -/
def liveGeFive : RegimeFormula := atom 8
/-- Live residual: even-difference perfect-power descent. -/
def liveDiffPP : RegimeFormula := atom 9
/-- Live residual: even-sum `z ≥ 7` (phase 7s: `z = 5` closed by `(n,n,5)`). -/
def liveSumOut : RegimeFormula := atom 10
/-- Live residual: odd two-equal (outside Darmon–Merel and two-cube fourth/fifth). -/
def liveOdd : RegimeFormula := atom 11
/-- Live residual: all-distinct mixed exponents. -/
def liveAllDistinct : RegimeFormula := atom 12
/-- Live residual: Pythagorean unequal-odd. -/
def liveUnequalOdd : RegimeFormula := atom 13

/-- Classical Beal conjecture (positive coprime form). -/
def bealConjecture : RegimeFormula := atom 14

/-- Closed slice: generalised Fermat signature `(n,n,5)` (phase 7s). -/
def sliceNN5 : RegimeFormula := atom 15

/-- Closed slice: two cubes as a fourth or fifth power (phase 7v). -/
def sliceBruin : RegimeFormula := atom 16

/-- Honest atlas status list (indices match the atoms above). -/
def bealAtlasStatuses : List TruthValue :=
  [.T, .T, .T, .T, .F, .F, .B, .U, .U, .U, .U, .U, .U, .U, .U, .T, .T]

/-- Honest Beal atlas valuation. -/
def bealAtlasVal : RegimeValuation :=
  RegimeValuation.ofList bealAtlasStatuses

theorem bealAtlasStatuses_length : bealAtlasStatuses.length = 17 := by
  simp [bealAtlasStatuses]

theorem bealAtlasVal_at (n : ℕ) (hn : n < 17) :
    bealAtlasVal.assign n = bealAtlasStatuses[n] :=
  RegimeValuation.ofList_get _ _ (by rw [bealAtlasStatuses_length]; exact hn)

theorem bealAtlasVal_sliceFLT : sliceFLT.eval bealAtlasVal.assign = .T :=
  bealAtlasVal_at 0 (by decide)

theorem bealAtlasVal_sliceDM : sliceDM.eval bealAtlasVal.assign = .T :=
  bealAtlasVal_at 1 (by decide)

theorem bealAtlasVal_sliceAbsOne : sliceAbsOne.eval bealAtlasVal.assign = .T :=
  bealAtlasVal_at 2 (by decide)

theorem bealAtlasVal_sliceFourth : sliceFourth.eval bealAtlasVal.assign = .T :=
  bealAtlasVal_at 3 (by decide)

theorem bealAtlasVal_diagModular : diagModular.eval bealAtlasVal.assign = .F :=
  bealAtlasVal_at 4 (by decide)

theorem bealAtlasVal_diagBalanced : diagBalanced.eval bealAtlasVal.assign = .F :=
  bealAtlasVal_at 5 (by decide)

theorem bealAtlasVal_bookRealization :
    bookRealization.eval bealAtlasVal.assign = .B :=
  bealAtlasVal_at 6 (by decide)

theorem bealAtlasVal_liveMordell : liveMordell.eval bealAtlasVal.assign = .U :=
  bealAtlasVal_at 7 (by decide)

theorem bealAtlasVal_liveGeFive : liveGeFive.eval bealAtlasVal.assign = .U :=
  bealAtlasVal_at 8 (by decide)

theorem bealAtlasVal_liveDiffPP : liveDiffPP.eval bealAtlasVal.assign = .U :=
  bealAtlasVal_at 9 (by decide)

theorem bealAtlasVal_liveSumOut : liveSumOut.eval bealAtlasVal.assign = .U :=
  bealAtlasVal_at 10 (by decide)

theorem bealAtlasVal_liveOdd : liveOdd.eval bealAtlasVal.assign = .U :=
  bealAtlasVal_at 11 (by decide)

theorem bealAtlasVal_liveAllDistinct :
    liveAllDistinct.eval bealAtlasVal.assign = .U :=
  bealAtlasVal_at 12 (by decide)

theorem bealAtlasVal_liveUnequalOdd :
    liveUnequalOdd.eval bealAtlasVal.assign = .U :=
  bealAtlasVal_at 13 (by decide)

theorem bealAtlasVal_conjecture : bealConjecture.eval bealAtlasVal.assign = .U :=
  bealAtlasVal_at 14 (by decide)

theorem bealAtlasVal_sliceNN5 : sliceNN5.eval bealAtlasVal.assign = .T :=
  bealAtlasVal_at 15 (by decide)

theorem bealAtlasVal_sliceBruin : sliceBruin.eval bealAtlasVal.assign = .T :=
  bealAtlasVal_at 16 (by decide)

/-- Closed-slice statuses under the honest atlas (atoms 0–3). -/
def closedSliceStatuses : List TruthValue :=
  List.replicate 4 .T

theorem meetRList_closed_slices : meetRList closedSliceStatuses = .T :=
  meetRList_all_T 4

/-- Closed slices packaged with any live residual stay live. -/
theorem meetRList_closed_with_live :
    meetRList (closedSliceStatuses ++ [.U]) = .U :=
  meetRList_T_append_U 4

/-- Named `{T,F}` cannot host a live residual atom. -/
theorem not_exists_named_beal_live :
    ¬ ∃ v : RegimeValuation,
        IsNamedRegime (v.assign 7) ∧
          liveMordell.eval v.assign = .U := by
  rintro ⟨v, hn, hl⟩
  have : v.assign 7 = .U := by simpa [liveMordell] using hl
  exact namedRegime_not_U hn this

/-- Wall `{B,F}` cannot host a proved closed slice. -/
theorem not_exists_wall_beal_slice :
    ¬ ∃ v : RegimeValuation,
        IsWallRegime (v.assign 0) ∧
          sliceFLT.eval v.assign = .T := by
  rintro ⟨v, hw, hc⟩
  have : v.assign 0 = .T := by simpa [sliceFLT] using hc
  exact wallRegime_not_T hw this

/-- The honest atlas realises closed `T`, diagnostic `F`, bookkeeping `B`, live `U`. -/
theorem exists_beal_atlas_valuation :
    ∃ v : RegimeValuation,
      sliceFLT.eval v.assign = .T ∧
        diagModular.eval v.assign = .F ∧
          bookRealization.eval v.assign = .B ∧
            liveMordell.eval v.assign = .U ∧
              liveOdd.eval v.assign = .U ∧
                liveAllDistinct.eval v.assign = .U ∧
                  liveUnequalOdd.eval v.assign = .U ∧
                    bealConjecture.eval v.assign = .U ∧
                      sliceNN5.eval v.assign = .T ∧
                        sliceBruin.eval v.assign = .T :=
  ⟨bealAtlasVal, bealAtlasVal_sliceFLT, bealAtlasVal_diagModular,
    bealAtlasVal_bookRealization, bealAtlasVal_liveMordell, bealAtlasVal_liveOdd,
    bealAtlasVal_liveAllDistinct, bealAtlasVal_liveUnequalOdd,
    bealAtlasVal_conjecture, bealAtlasVal_sliceNN5, bealAtlasVal_sliceBruin⟩

/-- Closed slices alone do not T-entail classical Beal. -/
theorem closed_slices_not_entailsTR_beal :
    ¬ EntailsTR {sliceFLT, sliceDM, sliceAbsOne, sliceFourth, sliceNN5, sliceBruin}
        bealConjecture := by
  intro h
  have hmod : ModelsTR bealAtlasVal
      {sliceFLT, sliceDM, sliceAbsOne, sliceFourth, sliceNN5, sliceBruin} := by
    intro φ hφ
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hφ
    rcases hφ with rfl | rfl | rfl | rfl | rfl | rfl
    · exact bealAtlasVal_sliceFLT
    · exact bealAtlasVal_at 1 (by decide)
    · exact bealAtlasVal_at 2 (by decide)
    · exact bealAtlasVal_at 3 (by decide)
    · exact bealAtlasVal_sliceNN5
    · exact bealAtlasVal_sliceBruin
  have := h bealAtlasVal hmod
  simp [HoldsTR, bealAtlasVal_conjecture] at this

/--
Window reading: closed slice `T` with bookkeeping conflict `B` still fails to
force the conjecture off `F` (non-explosion of status packaging).
-/
def bealWindowBookVal : RegimeValuation :=
  RegimeValuation.ofList
    (bealAtlasStatuses.set 14 .F)

theorem window_book_not_entailsNotFR_beal :
    ¬ EntailsNotFR {sliceFLT, bookRealization} bealConjecture := by
  intro h
  have hmod : ModelsNotFR bealWindowBookVal {sliceFLT, bookRealization} := by
    intro φ hφ
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hφ
    rcases hφ with rfl | rfl
    · simp [HoldsNotFR, sliceFLT, bealWindowBookVal, RegimeValuation.ofList,
        bealAtlasStatuses]
    · simp [HoldsNotFR, bookRealization, bealWindowBookVal, RegimeValuation.ofList,
        bealAtlasStatuses]
  have := h bealWindowBookVal hmod
  simp [HoldsNotFR, bealConjecture, bealWindowBookVal, RegimeValuation.ofList,
    bealAtlasStatuses] at this

/-! ### Safe `.U → .T` packaging -/

/-- Named closed-slice atoms (indices 0–3, 15, and 16). -/
def bealClosedSliceAtomSet : Set RegimeFormula :=
  {sliceFLT, sliceDM, sliceAbsOne, sliceFourth, sliceNN5, sliceBruin}

/-- Live residual atoms (indices 7–13). -/
def bealLiveResidualAtomSet : Set RegimeFormula :=
  {liveMordell, liveGeFive, liveDiffPP, liveSumOut, liveOdd, liveAllDistinct,
    liveUnequalOdd}

/-- Every named artefact except the classical conjecture. -/
def bealArtefactAtomSet : Set RegimeFormula :=
  {sliceFLT, sliceDM, sliceAbsOne, sliceFourth, diagModular, diagBalanced,
    bookRealization, liveMordell, liveGeFive, liveDiffPP, liveSumOut,
    liveOdd, liveAllDistinct, liveUnequalOdd, sliceNN5, sliceBruin}

/-- Establishedness of the seven live residuals is live. -/
theorem meetRList_beal_live_residuals :
    meetRList [.U, .U, .U, .U, .U, .U, .U] = .U :=
  rfl

/-- Promoting a single live residual to `T` still packages as live. -/
theorem meetRList_beal_promote_one_live :
    meetRList [.T, .U, .U, .U, .U, .U, .U] = .U :=
  rfl

/-- Honest atlas with `liveMordell` promoted `U → T`. Conjecture stays `U`. -/
def bealPromoteMordellVal : RegimeValuation :=
  RegimeValuation.ofList (bealAtlasStatuses.set 7 .T)

theorem bealPromoteMordellVal_liveMordell :
    liveMordell.eval bealPromoteMordellVal.assign = .T := by
  simp [liveMordell, bealPromoteMordellVal, RegimeValuation.ofList,
    bealAtlasStatuses, List.set]

theorem bealPromoteMordellVal_conjecture :
    bealConjecture.eval bealPromoteMordellVal.assign = .U := by
  simp [bealConjecture, bealPromoteMordellVal, RegimeValuation.ofList,
    bealAtlasStatuses, List.set]

/-- Closing one live residual does not `T`-entail classical Beal. -/
theorem promote_liveMordell_not_entailsTR_beal :
    ¬ EntailsTR (bealClosedSliceAtomSet ∪ {liveMordell}) bealConjecture := by
  intro h
  have hmod : ModelsTR bealPromoteMordellVal
      (bealClosedSliceAtomSet ∪ {liveMordell}) := by
    intro φ hφ
    simp only [bealClosedSliceAtomSet, Set.mem_union, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hφ
    rcases hφ with (rfl | rfl | rfl | rfl | rfl | rfl) | rfl
    · simp [HoldsTR, sliceFLT, bealPromoteMordellVal, RegimeValuation.ofList,
        bealAtlasStatuses, List.set]
    · simp [HoldsTR, sliceDM, bealPromoteMordellVal, RegimeValuation.ofList,
        bealAtlasStatuses, List.set]
    · simp [HoldsTR, sliceAbsOne, bealPromoteMordellVal, RegimeValuation.ofList,
        bealAtlasStatuses, List.set]
    · simp [HoldsTR, sliceFourth, bealPromoteMordellVal, RegimeValuation.ofList,
        bealAtlasStatuses, List.set]
    · simp [HoldsTR, sliceNN5, bealPromoteMordellVal, RegimeValuation.ofList,
        bealAtlasStatuses, List.set]
    · simp [HoldsTR, sliceBruin, bealPromoteMordellVal, RegimeValuation.ofList,
        bealAtlasStatuses, List.set]
    · simpa [HoldsTR] using bealPromoteMordellVal_liveMordell
  have := h bealPromoteMordellVal hmod
  simp [HoldsTR, bealPromoteMordellVal_conjecture] at this

/-- Status board with every artefact at `T` and the conjecture still `U`. -/
def bealAllArtefactsClosedStatuses : List TruthValue :=
  List.replicate 14 .T ++ [.U, .T, .T]

def bealAllArtefactsClosedVal : RegimeValuation :=
  RegimeValuation.ofList bealAllArtefactsClosedStatuses

private theorem bealAllArtefactsClosedVal_eval_T {n : ℕ} (hn : n < 14) :
    bealAllArtefactsClosedVal.assign n = .T := by
  interval_cases n <;>
    simp [bealAllArtefactsClosedVal, RegimeValuation.ofList,
      bealAllArtefactsClosedStatuses]

private theorem bealAllArtefactsClosedVal_eval_U :
    bealAllArtefactsClosedVal.assign 14 = .U := by
  simp [bealAllArtefactsClosedVal, RegimeValuation.ofList,
    bealAllArtefactsClosedStatuses]

private theorem bealAllArtefactsClosedVal_eval_NN5 :
    bealAllArtefactsClosedVal.assign 15 = .T := by
  simp [bealAllArtefactsClosedVal, RegimeValuation.ofList,
    bealAllArtefactsClosedStatuses]

private theorem bealAllArtefactsClosedVal_eval_Bruin :
    bealAllArtefactsClosedVal.assign 16 = .T := by
  simp [bealAllArtefactsClosedVal, RegimeValuation.ofList,
    bealAllArtefactsClosedStatuses]

/--
The status algebra does not encode the arithmetic assembly. Even with every
named artefact forced to `T`, classical Beal is not `T`-entailed.
-/
theorem artefacts_not_entailsTR_beal :
    ¬ EntailsTR bealArtefactAtomSet bealConjecture := by
  intro h
  have hmod : ModelsTR bealAllArtefactsClosedVal bealArtefactAtomSet := by
    intro φ hφ
    simp only [bealArtefactAtomSet, Set.mem_insert_iff, Set.mem_singleton_iff]
      at hφ
    rcases hφ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl | rfl | rfl | rfl | rfl
    · simpa [HoldsTR, sliceFLT] using
        bealAllArtefactsClosedVal_eval_T (n := 0) (by decide)
    · simpa [HoldsTR, sliceDM] using
        bealAllArtefactsClosedVal_eval_T (n := 1) (by decide)
    · simpa [HoldsTR, sliceAbsOne] using
        bealAllArtefactsClosedVal_eval_T (n := 2) (by decide)
    · simpa [HoldsTR, sliceFourth] using
        bealAllArtefactsClosedVal_eval_T (n := 3) (by decide)
    · simpa [HoldsTR, diagModular] using
        bealAllArtefactsClosedVal_eval_T (n := 4) (by decide)
    · simpa [HoldsTR, diagBalanced] using
        bealAllArtefactsClosedVal_eval_T (n := 5) (by decide)
    · simpa [HoldsTR, bookRealization] using
        bealAllArtefactsClosedVal_eval_T (n := 6) (by decide)
    · simpa [HoldsTR, liveMordell] using
        bealAllArtefactsClosedVal_eval_T (n := 7) (by decide)
    · simpa [HoldsTR, liveGeFive] using
        bealAllArtefactsClosedVal_eval_T (n := 8) (by decide)
    · simpa [HoldsTR, liveDiffPP] using
        bealAllArtefactsClosedVal_eval_T (n := 9) (by decide)
    · simpa [HoldsTR, liveSumOut] using
        bealAllArtefactsClosedVal_eval_T (n := 10) (by decide)
    · simpa [HoldsTR, liveOdd] using
        bealAllArtefactsClosedVal_eval_T (n := 11) (by decide)
    · simpa [HoldsTR, liveAllDistinct] using
        bealAllArtefactsClosedVal_eval_T (n := 12) (by decide)
    · simpa [HoldsTR, liveUnequalOdd] using
        bealAllArtefactsClosedVal_eval_T (n := 13) (by decide)
    · simpa [HoldsTR, sliceNN5] using bealAllArtefactsClosedVal_eval_NN5
    · simpa [HoldsTR, sliceBruin] using bealAllArtefactsClosedVal_eval_Bruin
  have := h bealAllArtefactsClosedVal hmod
  simp [HoldsTR, bealConjecture, bealAllArtefactsClosedVal_eval_U] at this

end Logic

end DstDiophantine
