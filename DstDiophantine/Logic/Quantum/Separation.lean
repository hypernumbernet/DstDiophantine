/-
Copyright (c) 2026 DstDiophantine contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DstDiophantine contributors
-/
import DstDiophantine.Logic.Quantum.DualSector
import DstDiophantine.Logic.Geometric
import DstDiophantine.Logic.Connective
import DstDiophantine.Logic.Amplitude
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# Separation theorems: D4L is not Hilbert / Born / BvN

The parameter Killing form is an indefinite pairing of signature `(3,3)`.
Self-overlap can be negative, so it is not a Born probability. The scalar
connectives `min`/`max` are distributive, so they cannot present the
non-distributive subspace lattice of a Hilbert space of dimension ≥ 2.

These theorems are the reason the dual-sector Hilbert space is a *sibling*
of D4L, not a rebranding of it.
-/

namespace DstDiophantine

namespace Logic

open Invariant Operations Real

theorem killingForm_symm (p q : TorsionParams) :
    killingForm p q = killingForm q p :=
  overlap_symm p q

/-- The Killing form takes a strictly positive value on the pure-boost extremal. -/
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

/-- The Killing form takes a strictly negative value on the pure-rotation extremal. -/
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

/-- Signature witness: the pairing is indefinite. -/
theorem killingForm_indefinite :
    (∃ p : TorsionParams, 0 < killingForm p p) ∧
      (∃ q : TorsionParams, killingForm q q < 0) :=
  ⟨⟨pureHyperbolicRay 1, killingForm_pos_pureHyperbolic⟩,
    ⟨pureEllipticRay 1, killingForm_neg_pureElliptic⟩⟩

/-- The Killing form is not a positive-definite inner product. -/
theorem killingForm_not_positive_definite :
    ¬ ∀ p : TorsionParams, 0 ≤ killingForm p p := by
  intro h
  have := h (pureEllipticRay 1)
  have := killingForm_neg_pureElliptic
  linarith

/-- Self-overlap equals `16 J` and can be negative. Not a Born probability. -/
theorem overlap_self_can_be_neg :
    ∃ p : TorsionParams, overlap p p < 0 :=
  ⟨pureEllipticRay 1, killingForm_neg_pureElliptic⟩

/-- A quantity that takes a negative value cannot be a Born probability. -/
theorem overlap_self_not_born_probability :
    ¬ ∀ p : TorsionParams, 0 ≤ overlap p p := by
  intro h
  obtain ⟨p, hp⟩ := overlap_self_can_be_neg
  have := h p
  linarith

/-- Scalar conjunction and disjunction distribute. Already proved; recorded here
as the lattice-theoretic obstruction to Birkhoff–von Neumann. -/
theorem scalar_connectives_distributive (a b c : ℝ) :
    conjJ a (disjJ b c) = disjJ (conjJ a b) (conjJ a c) :=
  conj_distrib_left a b c

/-- The four D4L labels are inhabited, so any identification with Hilbert
propositions would need four distinct atoms. Dimension 2 cannot supply four
pairwise orthogonal lines; that fact is proved on `DualSpinor` in
`Logic.Quantum.QuantumLogic`. -/
theorem four_labels_inhabited (tv : TruthValue) : ∃ a : Amplitude, a.collapse = tv :=
  exists_amplitude tv

end Logic

end DstDiophantine
