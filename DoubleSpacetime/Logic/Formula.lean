import DoubleSpacetime.Logic.Connective
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.Linarith

/-!
# Propositional syntax

Atoms, negation, conjunction, and disjunction on signed heights.
No implication connective.
-/

namespace DoubleSpacetime

namespace Logic

inductive Formula
  | atom : ℕ → Formula
  | neg : Formula → Formula
  | conj : Formula → Formula → Formula
  | disj : Formula → Formula → Formula
  deriving DecidableEq, Repr

namespace Formula

def eval (φ : Formula) (v : ℕ → ℝ) : ℝ :=
  match φ with
  | atom n => v n
  | neg ψ => negJ (ψ.eval v)
  | conj ψ χ => conjJ (ψ.eval v) (χ.eval v)
  | disj ψ χ => disjJ (ψ.eval v) (χ.eval v)

@[simp] theorem eval_atom (n : ℕ) (v : ℕ → ℝ) : (atom n).eval v = v n :=
  rfl

@[simp] theorem eval_neg (φ : Formula) (v : ℕ → ℝ) :
    φ.neg.eval v = negJ (φ.eval v) :=
  rfl

@[simp] theorem eval_conj (φ ψ : Formula) (v : ℕ → ℝ) :
    (φ.conj ψ).eval v = conjJ (φ.eval v) (ψ.eval v) :=
  rfl

@[simp] theorem eval_disj (φ ψ : Formula) (v : ℕ → ℝ) :
    (φ.disj ψ).eval v = disjJ (φ.eval v) (ψ.eval v) :=
  rfl

theorem eval_mem (φ : Formula) {v : ℕ → ℝ} (hv : ∀ n, |v n| ≤ 1) :
    |φ.eval v| ≤ 1 := by
  induction φ with
  | atom n => exact hv n
  | neg ψ ih =>
    simpa [eval, negJ, abs_neg] using ih
  | conj ψ χ ihψ ihχ =>
    have ha := abs_le.mp ihψ
    have hb := abs_le.mp ihχ
    refine abs_le.mpr ⟨le_min ha.1 hb.1, ?_⟩
    exact (min_le_left _ _).trans ha.2
  | disj ψ χ ihψ ihχ =>
    have ha := abs_le.mp ihψ
    have hb := abs_le.mp ihχ
    refine abs_le.mpr ⟨?_, max_le ha.2 hb.2⟩
    exact ha.1.trans (le_max_left _ _)

def atoms : Formula → Finset ℕ
  | atom n => {n}
  | neg φ => φ.atoms
  | conj φ ψ => φ.atoms ∪ ψ.atoms
  | disj φ ψ => φ.atoms ∪ ψ.atoms

@[simp] theorem atoms_atom (n : ℕ) : (atom n).atoms = {n} := rfl

@[simp] theorem atoms_neg (φ : Formula) : φ.neg.atoms = φ.atoms := rfl

@[simp] theorem atoms_conj (φ ψ : Formula) :
    (φ.conj ψ).atoms = φ.atoms ∪ ψ.atoms := rfl

@[simp] theorem atoms_disj (φ ψ : Formula) :
    (φ.disj ψ).atoms = φ.atoms ∪ ψ.atoms := rfl

theorem eval_eq_of_agree_on_atoms {φ : Formula} {v w : ℕ → ℝ}
    (h : ∀ n ∈ φ.atoms, v n = w n) : φ.eval v = φ.eval w := by
  induction φ with
  | atom n =>
    exact h n (by simp)
  | neg ψ ih =>
    simpa using congrArg negJ (ih h)
  | conj ψ χ ihψ ihχ =>
    have hψ := ihψ (fun n hn => h n (Finset.mem_union.mpr (Or.inl hn)))
    have hχ := ihχ (fun n hn => h n (Finset.mem_union.mpr (Or.inr hn)))
    simpa using congrArg₂ conjJ hψ hχ
  | disj ψ χ ihψ ihχ =>
    have hψ := ihψ (fun n hn => h n (Finset.mem_union.mpr (Or.inl hn)))
    have hχ := ihχ (fun n hn => h n (Finset.mem_union.mpr (Or.inr hn)))
    simpa using congrArg₂ disjJ hψ hχ

end Formula

end Logic

end DoubleSpacetime
