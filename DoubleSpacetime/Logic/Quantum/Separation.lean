import DoubleSpacetime.Logic.Quantum.DualSector
import DoubleSpacetime.Logic.Geometric
import DoubleSpacetime.Logic.Connective
import DoubleSpacetime.Logic.Amplitude
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# D4L is not Hilbert, Born, or Birkhoff–von Neumann

The Killing form is indefinite, so self-overlap is not a Born probability. Distributive `min`/`max`
is not the subspace lattice of `ℂ²`.
-/

namespace DoubleSpacetime

namespace Logic

open Invariant Operations Real

theorem killingForm_symm (p q : TorsionParams) :
    killingForm p q = killingForm q p :=
  overlap_symm p q

theorem killingForm_pos_pureHyperbolic :
    0 < killingForm (pureHyperbolicRay 1) (pureHyperbolicRay 1) := by
  have hJ : J (pureHyperbolicRay 1) = 3 * Real.pi ^ 2 / 8 := by
    have hN : JNormalized (pureHyperbolicRay 1) = 1 := by
      rw [JNormalized_pureHyperbolicRay]; norm_num
    have hcoef : (8 / (3 * Real.pi ^ 2) : ℝ) ≠ 0 := by positivity
    unfold JNormalized at hN
    have : (8 / (3 * Real.pi ^ 2)) * J (pureHyperbolicRay 1) = 1 := hN
    field_simp [hcoef] at this
    linarith
  have : killingForm (pureHyperbolicRay 1) (pureHyperbolicRay 1) = 16 * J (pureHyperbolicRay 1) :=
    overlap_self _
  rw [this, hJ]
  positivity

theorem killingForm_neg_pureElliptic :
    killingForm (pureEllipticRay 1) (pureEllipticRay 1) < 0 := by
  have hJ : J (pureEllipticRay 1) = -(3 * Real.pi ^ 2 / 8) := by
    have hN : JNormalized (pureEllipticRay 1) = -1 := by
      rw [JNormalized_pureEllipticRay]; norm_num
    unfold JNormalized at hN
    have hcoef : (8 / (3 * Real.pi ^ 2) : ℝ) ≠ 0 := by positivity
    have : (8 / (3 * Real.pi ^ 2)) * J (pureEllipticRay 1) = -1 := hN
    field_simp [hcoef] at this
    linarith
  have : killingForm (pureEllipticRay 1) (pureEllipticRay 1) = 16 * J (pureEllipticRay 1) :=
    overlap_self _
  rw [this, hJ]
  nlinarith [Real.pi_pos]

theorem killingForm_indefinite :
    (∃ p : TorsionParams, 0 < killingForm p p) ∧
      (∃ q : TorsionParams, killingForm q q < 0) :=
  ⟨⟨pureHyperbolicRay 1, killingForm_pos_pureHyperbolic⟩,
    ⟨pureEllipticRay 1, killingForm_neg_pureElliptic⟩⟩

theorem killingForm_not_positive_definite :
    ¬ ∀ p : TorsionParams, 0 ≤ killingForm p p := by
  intro h
  have := h (pureEllipticRay 1)
  have := killingForm_neg_pureElliptic
  linarith

/-- Not a Born probability. -/
theorem overlap_self_can_be_neg :
    ∃ p : TorsionParams, overlap p p < 0 :=
  ⟨pureEllipticRay 1, killingForm_neg_pureElliptic⟩

/-- Not a Born probability. -/
theorem overlap_self_not_born_probability :
    ¬ ∀ p : TorsionParams, 0 ≤ overlap p p := by
  intro h
  obtain ⟨p, hp⟩ := overlap_self_can_be_neg
  have := h p
  linarith

/-- Already proved. Obstruction to Birkhoff–von Neumann. -/
theorem scalar_connectives_distributive (a b c : ℝ) :
    conjJ a (disjJ b c) = disjJ (conjJ a b) (conjJ a c) :=
  conj_distrib_left a b c

/-- Not an identification with four orthogonal lines. -/
theorem four_labels_inhabited (tv : TruthValue) : ∃ a : Amplitude, a.collapse = tv :=
  exists_amplitude tv

end Logic

end DoubleSpacetime
