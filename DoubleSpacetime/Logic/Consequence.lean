import DoubleSpacetime.Logic.Valuation
import Mathlib.Data.Set.Basic
import Mathlib.Tactic.NormNum

/-!
# Consequence relations

`EntailsT` preserves synchrony. `EntailsNotF` preserves non-refutation.
Neither is classical entailment.
-/

namespace DoubleSpacetime

namespace Logic

open scoped Set

def ModelsT (v : Valuation) (Γ : Set Formula) : Prop :=
  ∀ φ ∈ Γ, HoldsT (φ.eval v.assign)

def ModelsNotF (v : Valuation) (Γ : Set Formula) : Prop :=
  ∀ φ ∈ Γ, HoldsNotF (φ.eval v.assign)

/-- Synchronising models synchronise the conclusion. -/
def EntailsT (Γ : Set Formula) (ψ : Formula) : Prop :=
  ∀ v : Valuation, ModelsT v Γ → HoldsT (ψ.eval v.assign)

/-- Non-refuting models do not refute the conclusion. -/
def EntailsNotF (Γ : Set Formula) (ψ : Formula) : Prop :=
  ∀ v : Valuation, ModelsNotF v Γ → HoldsNotF (ψ.eval v.assign)

theorem modelsT_mono {v : Valuation} {Γ Δ : Set Formula} (h : Γ ⊆ Δ)
    (hΔ : ModelsT v Δ) : ModelsT v Γ :=
  fun φ hφ => hΔ φ (h hφ)

theorem modelsNotF_mono {v : Valuation} {Γ Δ : Set Formula} (h : Γ ⊆ Δ)
    (hΔ : ModelsNotF v Δ) : ModelsNotF v Γ :=
  fun φ hφ => hΔ φ (h hφ)

theorem modelsT_to_modelsNotF {v : Valuation} {Γ : Set Formula}
    (h : ModelsT v Γ) : ModelsNotF v Γ :=
  fun φ hφ => holdsT_holdsNotF (h φ hφ)

def contradict (φ : Formula) : Set Formula :=
  {φ, φ.neg}

theorem modelsT_contradict {v : Valuation} {φ : Formula} :
    ModelsT v (contradict φ) ↔
      HoldsT (φ.eval v.assign) ∧ HoldsT (φ.neg.eval v.assign) := by
  constructor
  · intro h
    exact ⟨h φ (Set.mem_insert _ _),
      h φ.neg (Set.mem_insert_of_mem _ (Set.mem_singleton _))⟩
  · intro ⟨hp, hn⟩ ψ hψ
    rcases hψ with h | h
    · simpa [h] using hp
    · simpa [Set.eq_of_mem_singleton h] using hn

theorem modelsNotF_contradict {v : Valuation} {φ : Formula} :
    ModelsNotF v (contradict φ) ↔
      HoldsNotF (φ.eval v.assign) ∧ HoldsNotF (φ.neg.eval v.assign) := by
  constructor
  · intro h
    exact ⟨h φ (Set.mem_insert _ _),
      h φ.neg (Set.mem_insert_of_mem _ (Set.mem_singleton _))⟩
  · intro ⟨hp, hn⟩ ψ hψ
    rcases hψ with h | h
    · simpa [h] using hp
    · simpa [Set.eq_of_mem_singleton h] using hn

theorem entailsNotF_conj_neg (φ : Formula) :
    EntailsNotF ∅ (φ.conj φ.neg) := by
  intro v _
  simpa [Formula.eval] using conj_neg_holdsNotF (φ.eval v.assign)

theorem entailsT_excluded_middle (φ : Formula) :
    EntailsT {φ} (φ.disj φ.neg) := by
  intro v hv
  have hj : HoldsT (φ.eval v.assign) := hv φ (Set.mem_singleton _)
  simpa [Formula.eval] using (holdsT_excluded_middle (φ.eval v.assign)).mpr hj

theorem not_entailsNotF_excluded_middle :
    ¬ EntailsNotF {(Formula.atom 0)}
        ((Formula.atom 0).disj (Formula.atom 0).neg) := by
  intro h
  let v := Valuation.const (-1) (by norm_num)
  have hM : ModelsNotF v {(Formula.atom 0)} := by
    intro φ hφ
    rw [Set.eq_of_mem_singleton hφ]
    simp [v, HoldsNotF]
  have hE := h v hM
  simp [Formula.eval, v, HoldsNotF, disjJ, negJ] at hE

theorem not_entailsT_conj_neg :
    ¬ EntailsT ∅ ((Formula.atom 0).conj (Formula.atom 0).neg) := by
  intro h
  let v := Valuation.const (1 / 2) (by norm_num)
  have hE := h v (by intro _ hφ; simp at hφ)
  simp [Formula.eval, v, HoldsT, conjJ, negJ] at hE

end Logic

end DoubleSpacetime
