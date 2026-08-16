/-
Copyright (c) 2026 DstDiophantine contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DstDiophantine contributors
-/
import DstDiophantine.Logic.Valuation
import Mathlib.Data.Set.Basic

/-!
# Consequence relations for D4L

`EntailsT` uses designated synchrony (`HoldsT`). `EntailsNotF` uses
non-refutation (`HoldsNotF`). Neither is classical entailment. Implication
as a connective is not introduced here.
-/

namespace DstDiophantine

namespace Logic

open scoped Set

/-- Every premise is synchronised. -/
def ModelsT (v : Valuation) (Γ : Set Formula) : Prop :=
  ∀ φ ∈ Γ, HoldsT (φ.eval v.assign)

/-- Every premise is not refuted. -/
def ModelsNotF (v : Valuation) (Γ : Set Formula) : Prop :=
  ∀ φ ∈ Γ, HoldsNotF (φ.eval v.assign)

/-- T-consequence: every synchronising model synchronises the conclusion. -/
def EntailsT (Γ : Set Formula) (ψ : Formula) : Prop :=
  ∀ v : Valuation, ModelsT v Γ → HoldsT (ψ.eval v.assign)

/-- Non-refutation consequence. -/
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

/-- The pair `{φ, ¬φ}`. -/
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

end Logic

end DstDiophantine
