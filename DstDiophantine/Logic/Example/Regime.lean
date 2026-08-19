/-
Copyright (c) 2026 DstDiophantine contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DstDiophantine contributors
-/
import DstDiophantine.Logic.Regime

/-!
# Example 5: Diophantine regime classification

Two-valued fragments cannot host the DST three-layer split. D4L's regime
layer can. This is a change of semantics for *proof artefacts*, not a new
theorem of Peano arithmetic. Unconditional FLT / Beal / abc are not claimed.

Abstract atoms (no import of `Theorems`):

* atom `0` — proved core (additive faithfulness / shared no-go)
* atom `1` — diagnostic (coarse witness, continuous abc, ill-posed NoGo)
* atom `2` — live unproved bridge
* atom `3` — classical conjecture

Honest assignment: core `T`, diagnostic `F`, live `U`, conjecture `U`.
-/

namespace DstDiophantine

namespace Logic

open RegimeFormula

private def core : RegimeFormula := atom 0
private def diagnostic : RegimeFormula := atom 1
private def live : RegimeFormula := atom 2
private def conjecture : RegimeFormula := atom 3

/-- Honest three-layer assignment. -/
def threeLayerVal : RegimeValuation :=
  RegimeValuation.quad .T .F .U .U

theorem threeLayerVal_core : core.eval threeLayerVal.assign = .T := by
  simp [core, threeLayerVal]

theorem threeLayerVal_diagnostic : diagnostic.eval threeLayerVal.assign = .F := by
  simp [diagnostic, threeLayerVal]

theorem threeLayerVal_live : live.eval threeLayerVal.assign = .U := by
  simp [live, threeLayerVal]

theorem threeLayerVal_conjecture : conjecture.eval threeLayerVal.assign = .U := by
  simp [conjecture, threeLayerVal]

/-- D4L realises the three-layer split. -/
theorem exists_three_layer_valuation :
    ∃ v : RegimeValuation,
      core.eval v.assign = .T ∧
        diagnostic.eval v.assign = .F ∧
          live.eval v.assign = .U ∧
            conjecture.eval v.assign = .U :=
  ⟨threeLayerVal, threeLayerVal_core, threeLayerVal_diagnostic,
    threeLayerVal_live, threeLayerVal_conjecture⟩

/-- Named `{T,F}` cannot host the live status `U`. -/
theorem not_exists_named_three_layer :
    ¬ ∃ v : RegimeValuation,
        IsNamedRegime (v.assign 0) ∧
          IsNamedRegime (v.assign 1) ∧
            IsNamedRegime (v.assign 2) ∧
              live.eval v.assign = .U := by
  rintro ⟨v, _, _, h2, hl⟩
  have : v.assign 2 = .U := by simpa [live] using hl
  exact namedRegime_not_U h2 this

/-- Wall `{B,F}` cannot host the proved core `T`. -/
theorem not_exists_wall_core :
    ¬ ∃ v : RegimeValuation,
        IsWallRegime (v.assign 0) ∧
          core.eval v.assign = .T := by
  rintro ⟨v, hw, hc⟩
  have : v.assign 0 = .T := by simpa [core] using hc
  exact wallRegime_not_T hw this

/-- Core alone does not T-entail the classical conjecture. -/
theorem core_not_entailsTR_conjecture :
    ¬ EntailsTR {core} conjecture := by
  intro h
  have hmod : ModelsTR threeLayerVal {core} := by
    intro φ hφ
    have : φ = core := by simpa using hφ
    subst this
    simp [HoldsTR, threeLayerVal_core]
  have := h threeLayerVal hmod
  simp [HoldsTR, threeLayerVal_conjecture] at this

/-- Live-to-theorem implication is not designated. -/
theorem live_imp_conjecture_not_holdsTR :
    ¬ HoldsTR (impR .U .T) := by
  simp [HoldsTR, impR_U_T]

/-- Window (`T`) and ill-posed NoGo (`B`) do not force the conjecture off `F`. -/
def windowNogoVal : RegimeValuation :=
  RegimeValuation.quad .T .B .U .F

theorem window_nogo_not_entailsNotFR_conjecture :
    ¬ EntailsNotFR {core, diagnostic} conjecture := by
  intro h
  have hmod : ModelsNotFR windowNogoVal {core, diagnostic} := by
    intro φ hφ
    rcases hφ with hφ | hφ
    · subst hφ
      simp [HoldsNotFR, core, windowNogoVal]
    · have : φ = diagnostic := by simpa using hφ
      subst this
      simp [HoldsNotFR, diagnostic, windowNogoVal]
  have := h windowNogoVal hmod
  simp [HoldsNotFR, conjecture, windowNogoVal] at this

/-- Composite of a proved core and a live bridge is still live, not established. -/
theorem core_and_live_is_U :
    meetR .T .U = .U :=
  meetR_T_U

end Logic

end DstDiophantine
