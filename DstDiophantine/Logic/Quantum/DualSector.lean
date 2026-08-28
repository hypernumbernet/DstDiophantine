import DstDiophantine.Algebra.Invariant
import DstDiophantine.Algebra.Operations
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Dual and usual sectors as Euclidean 3-spaces

The parameter Killing form has signature `(3,3)`. Restricted to the dual
sector (`α = 0`) it is negative definite; restricted to the usual sector
(`β = 0`) it is positive definite. Flipping the dual sign yields a genuine
inner product on `ℝ³`.

The inner-product space is the *linear span* of each sector, not the
admissible cube. Superposition is a statement about that span, not about
admissible amplitudes.
-/

namespace DstDiophantine

namespace Logic

open Invariant Operations InnerProductSpace

/-- Componentwise sum of torsion parameters. Not an operation on amplitudes. -/
def addParams (p q : TorsionParams) : TorsionParams where
  alpha := fun a => p.alpha a + q.alpha a
  beta := fun a => p.beta a + q.beta a

/-- Scalar multiplication on parameter space. -/
def smulParams (c : ℝ) (p : TorsionParams) : TorsionParams where
  alpha := fun a => c * p.alpha a
  beta := fun a => c * p.beta a

def zeroParams' : TorsionParams :=
  ⟨fun _ => 0, fun _ => 0⟩

theorem killingForm_add_left (p q r : TorsionParams) :
    killingForm (addParams p q) r = killingForm p r + killingForm q r := by
  unfold killingForm addParams
  simp only [Fin.sum_univ_three]
  ring

theorem killingForm_add_right (p q r : TorsionParams) :
    killingForm p (addParams q r) = killingForm p q + killingForm p r := by
  unfold killingForm addParams
  simp only [Fin.sum_univ_three]
  ring

theorem killingForm_smul_left (c : ℝ) (p q : TorsionParams) :
    killingForm (smulParams c p) q = c * killingForm p q := by
  unfold killingForm smulParams
  simp only [Fin.sum_univ_three]
  ring

theorem killingForm_smul_right (c : ℝ) (p q : TorsionParams) :
    killingForm p (smulParams c q) = c * killingForm p q := by
  unfold killingForm smulParams
  simp only [Fin.sum_univ_three]
  ring

/-- Dual sector: vanishing usual-sector (boost) rapidities. -/
def IsDualSector (p : TorsionParams) : Prop :=
  ∀ a : Fin 3, p.alpha a = 0

/-- Usual sector: vanishing dual-sector (rotation) rapidities. -/
def IsUsualSector (p : TorsionParams) : Prop :=
  ∀ a : Fin 3, p.beta a = 0

/-- Dual-sector rapidity as a Euclidean 3-vector. -/
abbrev DualRapidity := EuclideanSpace ℝ (Fin 3)

/-- Usual-sector rapidity as a Euclidean 3-vector. -/
abbrev UsualRapidity := EuclideanSpace ℝ (Fin 3)

/-- Embed a dual rapidity as a torsion configuration with `α = 0`. -/
def ofDual (β : DualRapidity) : TorsionParams where
  alpha := fun _ => 0
  beta := fun a => β a

/-- Embed a usual rapidity as a torsion configuration with `β = 0`. -/
def ofUsual (α : UsualRapidity) : TorsionParams where
  alpha := fun a => α a
  beta := fun _ => 0

theorem isDualSector_ofDual (β : DualRapidity) : IsDualSector (ofDual β) := by
  intro a
  rfl

theorem isUsualSector_ofUsual (α : UsualRapidity) : IsUsualSector (ofUsual α) := by
  intro a
  rfl

/-- Extract the dual rapidity. Meaningful on the dual sector. -/
def toDual (p : TorsionParams) : DualRapidity :=
  WithLp.toLp 2 p.beta

/-- Extract the usual rapidity. Meaningful on the usual sector. -/
def toUsual (p : TorsionParams) : UsualRapidity :=
  WithLp.toLp 2 p.alpha

theorem toDual_ofDual (β : DualRapidity) : toDual (ofDual β) = β := by
  rw [WithLp.ext_iff]
  ext a
  simp [toDual, ofDual]

theorem toUsual_ofUsual (α : UsualRapidity) : toUsual (ofUsual α) = α := by
  rw [WithLp.ext_iff]
  ext a
  simp [toUsual, ofUsual]

theorem ofDual_toDual {p : TorsionParams} (h : IsDualSector p) :
    ofDual (toDual p) = p := by
  obtain ⟨α, β⟩ := p
  refine congrArg₂ TorsionParams.mk ?_ ?_
  · funext a; exact (h a).symm
  · funext a; rfl

theorem ofUsual_toUsual {p : TorsionParams} (h : IsUsualSector p) :
    ofUsual (toUsual p) = p := by
  obtain ⟨α, β⟩ := p
  refine congrArg₂ TorsionParams.mk ?_ ?_
  · funext a; rfl
  · funext a; exact (h a).symm

private theorem sum_inner (β γ : DualRapidity) :
    (∑ a : Fin 3, β a * γ a) = inner ℝ β γ := by
  simp only [inner]
  refine Finset.sum_congr rfl fun _ _ => mul_comm _ _

theorem killingForm_ofDual (β γ : DualRapidity) :
    killingForm (ofDual β) (ofDual γ) = -8 * inner ℝ β γ := by
  unfold killingForm ofDual
  simp only [zero_mul, zero_sub, Finset.sum_neg_distrib]
  rw [← sum_inner β γ]
  ring

theorem killingForm_ofUsual (α γ : UsualRapidity) :
    killingForm (ofUsual α) (ofUsual γ) = 8 * inner ℝ α γ := by
  unfold killingForm ofUsual
  simp only [mul_zero, sub_zero]
  rw [← sum_inner α γ]

/-- On the dual sector the Killing form is negative definite. -/
theorem killingForm_ofDual_neg_def {β : DualRapidity} (h : killingForm (ofDual β) (ofDual β) = 0) :
    β = 0 := by
  have : inner ℝ β β = 0 := by
    have := killingForm_ofDual β β
    linarith
  exact inner_self_eq_zero.mp this

/-- On the usual sector the Killing form is positive definite. -/
theorem killingForm_ofUsual_pos_def {α : UsualRapidity}
    (h : killingForm (ofUsual α) (ofUsual α) = 0) :
    α = 0 := by
  have : inner ℝ α α = 0 := by
    have := killingForm_ofUsual α α
    linarith
  exact inner_self_eq_zero.mp this

theorem killingForm_ofDual_le_zero (β : DualRapidity) :
    killingForm (ofDual β) (ofDual β) ≤ 0 := by
  rw [killingForm_ofDual]
  have : 0 ≤ inner ℝ β β := real_inner_self_nonneg
  linarith

theorem killingForm_ofUsual_nonneg (α : UsualRapidity) :
    0 ≤ killingForm (ofUsual α) (ofUsual α) := by
  rw [killingForm_ofUsual]
  have : 0 ≤ inner ℝ α α := real_inner_self_nonneg
  linarith

/-- Flipped dual pairing, a genuine Euclidean inner product. -/
noncomputable def dualInner (β γ : DualRapidity) : ℝ :=
  inner ℝ β γ

theorem dualInner_eq_neg_killing (β γ : DualRapidity) :
    dualInner β γ = -(1 / 8) * killingForm (ofDual β) (ofDual γ) := by
  unfold dualInner
  rw [killingForm_ofDual]
  ring

end Logic

end DstDiophantine
