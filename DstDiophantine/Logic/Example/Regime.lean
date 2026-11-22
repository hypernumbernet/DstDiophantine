import DstDiophantine.Logic.Regime

/-!
# Three-layer proof status

Atoms: `0` core, `1` diagnostic, `2` live bridge, `3` conjecture. Honest assignment `T`, `F`, `U`,
`U`. A semantics for proof artefacts, not a theorem of arithmetic.
-/

namespace DstDiophantine

namespace Logic

open RegimeFormula

private def core : RegimeFormula := atom 0
private def diagnostic : RegimeFormula := atom 1
private def live : RegimeFormula := atom 2
private def conjecture : RegimeFormula := atom 3

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

theorem exists_three_layer_valuation :
    ∃ v : RegimeValuation,
      core.eval v.assign = .T ∧
        diagnostic.eval v.assign = .F ∧
          live.eval v.assign = .U ∧
            conjecture.eval v.assign = .U :=
  ⟨threeLayerVal, threeLayerVal_core, threeLayerVal_diagnostic,
    threeLayerVal_live, threeLayerVal_conjecture⟩

theorem not_exists_named_three_layer :
    ¬ ∃ v : RegimeValuation,
        IsNamedRegime (v.assign 0) ∧
          IsNamedRegime (v.assign 1) ∧
            IsNamedRegime (v.assign 2) ∧
              live.eval v.assign = .U := by
  rintro ⟨v, _, _, h2, hl⟩
  have : v.assign 2 = .U := by simpa [live] using hl
  exact namedRegime_not_U h2 this

theorem not_exists_wall_core :
    ¬ ∃ v : RegimeValuation,
        IsWallRegime (v.assign 0) ∧
          core.eval v.assign = .T := by
  rintro ⟨v, hw, hc⟩
  have : v.assign 0 = .T := by simpa [core] using hc
  exact wallRegime_not_T hw this

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

theorem live_imp_conjecture_not_holdsTR :
    ¬ HoldsTR (impR .U .T) := by
  simp [HoldsTR, impR_U_T]

/-- Core `T`, diagnostic `B`, live `U`, conjecture `F`. -/
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

theorem core_and_live_is_U :
    meetR .T .U = .U :=
  meetR_T_U

end Logic

end DstDiophantine
