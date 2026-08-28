import DstDiophantine.Logic.Consequence
import Mathlib.Tactic.NormNum

/-!
# Example 2: contradiction without explosion

Classical two-valued logic has *ex falso quodlibet*: `{P, ¬P}` entails
every `Q`. D4L does not.

* On `Bool`, `P = true` and `!P = true` is already impossible, so the
  implication to any `Q` is vacuous.
* On the wall fragment, `P` and `¬P` cannot both be the positive wall.
* In D4L, `{P, ¬P}` may both hold at `T` (the negation fixed point), or
  both be non-refuted (`B` and `U`), while an unrelated atom saturates `F`.

The conjunction `P ∧ ¬P` itself never saturates `F`
(`classify_conj_neg_ne_F`).
-/

namespace DstDiophantine

namespace Logic

/-- Classical Boolean explosion is vacuous: `P` and `¬P` cannot both be `true`. -/
theorem bool_not_both (P : Bool) : ¬ (P = true ∧ (!P) = true) := by
  cases P <;> simp

/-- Vacuous EFQ on `Bool`. -/
theorem bool_efq (P Q : Bool) (hP : P = true) (hn : (!P) = true) : Q = true :=
  (bool_not_both P ⟨hP, hn⟩).elim

private def p : Formula := Formula.atom 0
private def q : Formula := Formula.atom 1

/-- Witness: `P` is `T` (hence so is `¬P`) while `Q` is `F`. -/
def explosionWitness : Valuation :=
  Valuation.pair 0 1 (by norm_num) (by norm_num)

theorem explosionWitness_modelsT :
    ModelsT explosionWitness (contradict p) := by
  rw [modelsT_contradict]
  simp [p, explosionWitness, HoldsT]

/-- `{P, ¬P}` does not T-entail an unrelated atom. -/
theorem contradict_not_entailsT_atom :
    ¬ EntailsT (contradict p) q := by
  intro h
  have := h explosionWitness explosionWitness_modelsT
  simp [HoldsT, q, explosionWitness] at this

/-- Off the fixed point: `P` is interior `B`, `¬P` is `U`, `Q` is `F`. -/
noncomputable def explosionWitnessOffT : Valuation :=
  Valuation.pair (-1 / 2) 1 (by norm_num) (by norm_num)

theorem explosionWitnessOffT_modelsNotF :
    ModelsNotF explosionWitnessOffT (contradict p) := by
  rw [modelsNotF_contradict]
  simp [p, explosionWitnessOffT, HoldsNotF, negJ]; norm_num

/-- `{P, ¬P}` does not force an unrelated atom even off the fixed point. -/
theorem contradict_not_entailsNotF_atom :
    ¬ EntailsNotF (contradict p) q := by
  intro h
  have := h explosionWitnessOffT explosionWitnessOffT_modelsNotF
  simp [HoldsNotF, q, explosionWitnessOffT] at this

end Logic

end DstDiophantine
