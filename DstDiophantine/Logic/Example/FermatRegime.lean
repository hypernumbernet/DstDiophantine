/-
Copyright (c) 2026 DstDiophantine contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DstDiophantine contributors
-/
import DstDiophantine.Logic.Regime

/-!
# Dual-axis FLT regime atlas (D4L)

Atoms are names only (no `Theorems` import). Layout:

* slice `T` (0) — additive faithfulness / shared no-go core
* slice `T` (1) — real Lᵖ dichotomy (`n = 2` pure cyclic / `n ≥ 3` mixed)
* diagnostic `F` (2) — single-axis modular winding (demoted)
* diagnostic `F` (3) — continuous balanced-seed obstruction
* live residual `U` (4) — `FermatMixedMotorResidual` (sandwich / commutator)
* conjecture `U` (5) — classical FLT

Closed slices alone do not T-entail classical FLT. Unconditional FLT is not claimed.
-/

namespace DstDiophantine

namespace Logic

open RegimeFormula

/-- Closed slice: additive null faithfulness + shared amplification no-go. -/
def sliceCore : RegimeFormula := atom 0
/-- Closed slice: real Lᵖ dichotomy (pure cyclic ↔ Pythagorean; n≥3 ⇒ mixed). -/
def sliceLp : RegimeFormula := atom 1

/-- Diagnostic: single-axis modular winding (demoted; geometric seed winds 0). -/
def diagSingleAxisModular : RegimeFormula := atom 2
/-- Diagnostic: continuous balanced seed below `1/p²`. -/
def diagBalancedSeed : RegimeFormula := atom 3

/-- Live residual: mixed dual-axis motor vs additive null constraint. -/
def liveMixedMotor : RegimeFormula := atom 4

/-- Classical Fermat's Last Theorem. -/
def fltConjecture : RegimeFormula := atom 5

/-- Honest atlas status list. -/
def fermatAtlasStatuses : List TruthValue :=
  [.T, .T, .F, .F, .U, .U]

/-- Honest FLT atlas valuation. -/
def fermatAtlasVal : RegimeValuation :=
  RegimeValuation.ofList fermatAtlasStatuses

private theorem fermatAtlasStatuses_length : fermatAtlasStatuses.length = 6 := by
  simp [fermatAtlasStatuses]

private theorem fermatAtlasVal_at (n : ℕ) (hn : n < 6) :
    fermatAtlasVal.assign n = fermatAtlasStatuses[n] :=
  RegimeValuation.ofList_get _ _ (by rw [fermatAtlasStatuses_length]; exact hn)

theorem fermatAtlasVal_sliceCore : sliceCore.eval fermatAtlasVal.assign = .T :=
  fermatAtlasVal_at 0 (by decide)

theorem fermatAtlasVal_sliceLp : sliceLp.eval fermatAtlasVal.assign = .T :=
  fermatAtlasVal_at 1 (by decide)

theorem fermatAtlasVal_diagSingleAxisModular :
    diagSingleAxisModular.eval fermatAtlasVal.assign = .F :=
  fermatAtlasVal_at 2 (by decide)

theorem fermatAtlasVal_diagBalancedSeed :
    diagBalancedSeed.eval fermatAtlasVal.assign = .F :=
  fermatAtlasVal_at 3 (by decide)

theorem fermatAtlasVal_liveMixedMotor :
    liveMixedMotor.eval fermatAtlasVal.assign = .U :=
  fermatAtlasVal_at 4 (by decide)

theorem fermatAtlasVal_conjecture : fltConjecture.eval fermatAtlasVal.assign = .U :=
  fermatAtlasVal_at 5 (by decide)

/-- Named `{T,F}` cannot host the live mixed-motor residual. -/
theorem not_exists_named_fermat_live :
    ¬ ∃ v : RegimeValuation,
        IsNamedRegime (v.assign 4) ∧
          liveMixedMotor.eval v.assign = .U := by
  rintro ⟨v, hn, hl⟩
  have : v.assign 4 = .U := by simpa [liveMixedMotor] using hl
  exact namedRegime_not_U hn this

/-- Wall `{B,F}` cannot host a proved closed slice. -/
theorem not_exists_wall_fermat_slice :
    ¬ ∃ v : RegimeValuation,
        IsWallRegime (v.assign 0) ∧
          sliceCore.eval v.assign = .T := by
  rintro ⟨v, hw, hc⟩
  have : v.assign 0 = .T := by simpa [sliceCore] using hc
  exact wallRegime_not_T hw this

/-- The honest atlas realises closed `T`, diagnostic `F`, live `U`. -/
theorem exists_fermat_atlas_valuation :
    ∃ v : RegimeValuation,
      sliceCore.eval v.assign = .T ∧
        sliceLp.eval v.assign = .T ∧
          diagSingleAxisModular.eval v.assign = .F ∧
            diagBalancedSeed.eval v.assign = .F ∧
              liveMixedMotor.eval v.assign = .U ∧
                fltConjecture.eval v.assign = .U :=
  ⟨fermatAtlasVal, fermatAtlasVal_sliceCore, fermatAtlasVal_sliceLp,
    fermatAtlasVal_diagSingleAxisModular, fermatAtlasVal_diagBalancedSeed,
    fermatAtlasVal_liveMixedMotor, fermatAtlasVal_conjecture⟩

/-- Closed slices alone do not T-entail classical FLT. -/
theorem closed_slices_not_entailsTR_flt :
    ¬ EntailsTR {sliceCore, sliceLp} fltConjecture := by
  intro h
  have hmod : ModelsTR fermatAtlasVal {sliceCore, sliceLp} := by
    intro φ hφ
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hφ
    rcases hφ with rfl | rfl
    · exact fermatAtlasVal_sliceCore
    · exact fermatAtlasVal_sliceLp
  have := h fermatAtlasVal hmod
  simp [HoldsTR, fermatAtlasVal_conjecture] at this

end Logic

end DstDiophantine
