/-
Copyright (c) 2026 DstDiophantine contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DstDiophantine contributors
-/
import DstDiophantine.Logic.Regime

/-!
# Phase 7p / 7r: abstract Beal residual atlas (D4L regime layer)

Atoms are names only (no `Theorems` import). Witnesses live in
`Theorems.BealRegime`. Layout: slices `T` (0–3), diagnostics `F` (4–5),
bookkeeping `B` (6), live residuals `U` (7–13; Odd/AllDistinct/UnequalOdd
split at 11–13), conjecture `U` (14). Unconditional classical Beal is not claimed.
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
/-- Live residual: even-sum outside cube (`z = 5` / `z ≥ 7`). -/
def liveSumOut : RegimeFormula := atom 10
/-- Live residual: odd two-equal (outside Darmon–Merel cubes). -/
def liveOdd : RegimeFormula := atom 11
/-- Live residual: all-distinct mixed exponents. -/
def liveAllDistinct : RegimeFormula := atom 12
/-- Live residual: Pythagorean unequal-odd. -/
def liveUnequalOdd : RegimeFormula := atom 13

/-- Classical Beal conjecture (positive coprime form). -/
def bealConjecture : RegimeFormula := atom 14

/-- Honest atlas status list (indices match the atoms above). -/
def bealAtlasStatuses : List TruthValue :=
  [.T, .T, .T, .T, .F, .F, .B, .U, .U, .U, .U, .U, .U, .U, .U]

/-- Honest Beal atlas valuation. -/
def bealAtlasVal : RegimeValuation :=
  RegimeValuation.ofList bealAtlasStatuses

private theorem bealAtlasStatuses_length : bealAtlasStatuses.length = 15 := by
  simp [bealAtlasStatuses]

private theorem bealAtlasVal_at (n : ℕ) (hn : n < 15) :
    bealAtlasVal.assign n = bealAtlasStatuses[n] :=
  RegimeValuation.ofList_get _ _ (by rw [bealAtlasStatuses_length]; exact hn)

theorem bealAtlasVal_sliceFLT : sliceFLT.eval bealAtlasVal.assign = .T :=
  bealAtlasVal_at 0 (by decide)

theorem bealAtlasVal_diagModular : diagModular.eval bealAtlasVal.assign = .F :=
  bealAtlasVal_at 4 (by decide)

theorem bealAtlasVal_bookRealization :
    bookRealization.eval bealAtlasVal.assign = .B :=
  bealAtlasVal_at 6 (by decide)

theorem bealAtlasVal_liveMordell : liveMordell.eval bealAtlasVal.assign = .U :=
  bealAtlasVal_at 7 (by decide)

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

/-- Closed-slice statuses under the honest atlas. -/
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
                    bealConjecture.eval v.assign = .U :=
  ⟨bealAtlasVal, bealAtlasVal_sliceFLT, bealAtlasVal_diagModular,
    bealAtlasVal_bookRealization, bealAtlasVal_liveMordell, bealAtlasVal_liveOdd,
    bealAtlasVal_liveAllDistinct, bealAtlasVal_liveUnequalOdd,
    bealAtlasVal_conjecture⟩

/-- Closed slices alone do not T-entail classical Beal. -/
theorem closed_slices_not_entailsTR_beal :
    ¬ EntailsTR {sliceFLT, sliceDM, sliceAbsOne, sliceFourth} bealConjecture := by
  intro h
  have hmod : ModelsTR bealAtlasVal
      {sliceFLT, sliceDM, sliceAbsOne, sliceFourth} := by
    intro φ hφ
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hφ
    rcases hφ with rfl | rfl | rfl | rfl
    · exact bealAtlasVal_sliceFLT
    · exact bealAtlasVal_at 1 (by decide)
    · exact bealAtlasVal_at 2 (by decide)
    · exact bealAtlasVal_at 3 (by decide)
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

end Logic

end DstDiophantine
