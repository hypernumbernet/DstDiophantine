import DoubleSpacetime.Logic.Consequence
import Mathlib.Tactic.NormNum

/-!
# Contradiction without explosion

`{P, ¬P}` does not entail an unrelated atom under `EntailsT` or `EntailsNotF`.
-/

namespace DoubleSpacetime

namespace Logic

theorem bool_not_both (P : Bool) : ¬ (P = true ∧ (!P) = true) := by
  cases P <;> simp

theorem bool_efq (P Q : Bool) (hP : P = true) (hn : (!P) = true) : Q = true :=
  (bool_not_both P ⟨hP, hn⟩).elim

private def p : Formula := Formula.atom 0
private def q : Formula := Formula.atom 1

/-- `P ↦ 0`, `Q ↦ 1`. -/
def explosionWitness : Valuation :=
  Valuation.pair 0 1 (by norm_num) (by norm_num)

theorem explosionWitness_modelsT :
    ModelsT explosionWitness (contradict p) := by
  rw [modelsT_contradict]
  simp [p, explosionWitness, HoldsT]

theorem contradict_not_entailsT_atom :
    ¬ EntailsT (contradict p) q := by
  intro h
  have := h explosionWitness explosionWitness_modelsT
  simp [HoldsT, q, explosionWitness] at this

/-- `P ↦ -1/2`, `Q ↦ 1`. -/
noncomputable def explosionWitnessOffT : Valuation :=
  Valuation.pair (-1 / 2) 1 (by norm_num) (by norm_num)

theorem explosionWitnessOffT_modelsNotF :
    ModelsNotF explosionWitnessOffT (contradict p) := by
  rw [modelsNotF_contradict]
  simp [p, explosionWitnessOffT, HoldsNotF, negJ]; norm_num

theorem contradict_not_entailsNotF_atom :
    ¬ EntailsNotF (contradict p) q := by
  intro h
  have := h explosionWitnessOffT explosionWitnessOffT_modelsNotF
  simp [HoldsNotF, q, explosionWitnessOffT] at this

end Logic

end DoubleSpacetime
