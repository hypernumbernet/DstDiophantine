import DstDiophantine.Logic.Connective
import Mathlib.Tactic.Linarith

/-!
# Propositional syntax for D4L

Formulas are built from atoms, negation, conjunction, and disjunction.
Evaluation is on signed heights via `negJ` / `conjJ` / `disjJ`. There is
no implication connective: the designated-value layer does not need one.

This is not a Hilbert-space syntax and not Belnap FOUR.
-/

namespace DstDiophantine

namespace Logic

/-- Propositional formulas over `ℕ`-indexed atoms. -/
inductive Formula
  | atom : ℕ → Formula
  | neg : Formula → Formula
  | conj : Formula → Formula → Formula
  | disj : Formula → Formula → Formula
  deriving DecidableEq, Repr

namespace Formula

/-- Scalar evaluation along an assignment of signed heights. -/
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

/-- Evaluation stays in `[-1,1]` when every atom does. -/
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

end Formula

end Logic

end DstDiophantine
