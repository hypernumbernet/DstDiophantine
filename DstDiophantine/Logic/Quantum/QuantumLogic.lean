/-
Copyright (c) 2026 DstDiophantine contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DstDiophantine contributors
-/
import DstDiophantine.Logic.Quantum.Spinor
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Orthogonal
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Tactic.Linarith

/-!
# Birkhoff–von Neumann quantum logic of `DualSpinor`

Propositions are linear subspaces of `ℂ²` (closed automatically). Meet is
intersection, join is the sum, negation is the orthogonal complement.
The orthomodular law is the orthogonal decomposition of a finite-dimensional
subspace.

This lattice is D4L's dual Hilbert layer. It is not identified with
`{T,U,F,B}` or with `min`/`max`.
-/

namespace DstDiophantine

namespace Logic

open scoped InnerProductSpace
open Submodule Module

/-- A quantum proposition: a linear subspace of the dual spinor space. -/
abbrev QProp := Submodule ℂ DualSpinor

noncomputable def qMeet (A B : QProp) : QProp := A ⊓ B

noncomputable def qJoin (A B : QProp) : QProp := A ⊔ B

noncomputable def qNot (A : QProp) : QProp := Aᗮ

/-- Orthomodular law on `DualSpinor`: if `A ≤ B` then `A ∨ (A⊥ ∧ B) = B`. -/
theorem orthomodular {A B : QProp} (h : A ≤ B) : A ⊔ Aᗮ ⊓ B = B :=
  Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection h

noncomputable def e0 : DualSpinor := EuclideanSpace.single (0 : Fin 2) (1 : ℂ)

noncomputable def e1 : DualSpinor := EuclideanSpace.single (1 : Fin 2) (1 : ℂ)

noncomputable def d01 : DualSpinor := e0 + e1

noncomputable def lineE0 : QProp := ℂ ∙ e0

noncomputable def lineE1 : QProp := ℂ ∙ e1

noncomputable def lineD : QProp := ℂ ∙ d01

theorem e0_ne_zero : e0 ≠ 0 := by
  intro h
  simp [e0, PiLp.single_eq_zero_iff] at h

theorem e1_ne_zero : e1 ≠ 0 := by
  intro h
  simp [e1, PiLp.single_eq_zero_iff] at h

theorem d01_ne_zero : d01 ≠ 0 := by
  intro h
  have h0 : (d01 : DualSpinor) 0 = 0 := by simp [h]
  simp [d01, e0, e1, PiLp.add_apply] at h0

theorem lineE0_finrank : finrank ℂ lineE0 = 1 :=
  finrank_span_singleton e0_ne_zero

theorem lineE1_finrank : finrank ℂ lineE1 = 1 :=
  finrank_span_singleton e1_ne_zero

theorem lineD_finrank : finrank ℂ lineD = 1 :=
  finrank_span_singleton d01_ne_zero

private theorem coord_e0 (a : ℂ) :
    (a • e0) 0 = a ∧ (a • e0) 1 = 0 := by
  simp [e0, PiLp.smul_apply]

private theorem coord_e1 (b : ℂ) :
    (b • e1) 0 = 0 ∧ (b • e1) 1 = b := by
  simp [e1, PiLp.smul_apply]

private theorem coord_d01 (c : ℂ) :
    (c • d01) 0 = c ∧ (c • d01) 1 = c := by
  simp [d01, e0, e1, PiLp.smul_apply, PiLp.add_apply]

theorem lineE0_inf_lineE1 : lineE0 ⊓ lineE1 = (⊥ : QProp) := by
  refine eq_bot_iff.mpr ?_
  intro x hx
  obtain ⟨a, rfl⟩ := mem_span_singleton.mp hx.1
  obtain ⟨b, hb⟩ := mem_span_singleton.mp hx.2
  have h1 := congrArg (fun v : DualSpinor => v 1) hb
  have hb0 : b = 0 := by
    have hL := (coord_e0 a).2
    have hR := (coord_e1 b).2
    rw [hL, hR] at h1
    exact h1
  have h0 := congrArg (fun v : DualSpinor => v 0) hb
  have ha0 : a = 0 := by
    have hL := (coord_e0 a).1
    have hR := (coord_e1 b).1
    rw [hL, hR] at h0
    exact h0.symm
  simp [ha0]

theorem lineE0_inf_lineD : lineE0 ⊓ lineD = (⊥ : QProp) := by
  refine eq_bot_iff.mpr ?_
  intro x hx
  obtain ⟨a, rfl⟩ := mem_span_singleton.mp hx.1
  obtain ⟨c, hc⟩ := mem_span_singleton.mp hx.2
  have h1 := congrArg (fun v : DualSpinor => v 1) hc
  have hc0 : c = 0 := by
    have hL := (coord_e0 a).2
    have hR := (coord_d01 c).2
    rw [hL, hR] at h1
    exact h1
  have h0 := congrArg (fun v : DualSpinor => v 0) hc
  have ha0 : a = 0 := by
    have hL := (coord_e0 a).1
    have hR := (coord_d01 c).1
    rw [hL, hR, hc0] at h0
    exact h0.symm
  simp [ha0]

theorem lineE1_inf_lineD : lineE1 ⊓ lineD = (⊥ : QProp) := by
  refine eq_bot_iff.mpr ?_
  intro x hx
  obtain ⟨b, rfl⟩ := mem_span_singleton.mp hx.1
  obtain ⟨c, hc⟩ := mem_span_singleton.mp hx.2
  have h0 := congrArg (fun v : DualSpinor => v 0) hc
  have hc0 : c = 0 := by
    have hL := (coord_e1 b).1
    have hR := (coord_d01 c).1
    rw [hL, hR] at h0
    exact h0
  have h1 := congrArg (fun v : DualSpinor => v 1) hc
  have hb0 : b = 0 := by
    have hL := (coord_e1 b).2
    have hR := (coord_d01 c).2
    rw [hL, hR, hc0] at h1
    exact h1.symm
  simp [hb0]

private theorem finrank_top_qprop : finrank ℂ (⊤ : QProp) = 2 := by
  rw [finrank_top]
  exact dualSpinor_finrank

theorem lineE1_sup_lineD : (lineE1 ⊔ lineD : QProp) = ⊤ := by
  have hdim : finrank ℂ (lineE1 ⊔ lineD : QProp) = 2 := by
    have h := finrank_sup_add_finrank_inf_eq (s := lineE1) (t := lineD)
    rw [lineE1_finrank, lineD_finrank, lineE1_inf_lineD, finrank_bot] at h
    linarith
  exact eq_of_le_of_finrank_eq le_top (hdim.trans finrank_top_qprop.symm)

/-- Standard non-distributivity of the subspace lattice of `ℂ²`. -/
theorem not_distributive :
    (lineE0 ⊓ (lineE1 ⊔ lineD) : QProp) ≠
      ((lineE0 ⊓ lineE1) ⊔ (lineE0 ⊓ lineD) : QProp) := by
  rw [lineE1_sup_lineD, inf_top_eq, lineE0_inf_lineE1, lineE0_inf_lineD, bot_sup_eq]
  intro h
  have : finrank ℂ lineE0 = 0 := by rw [h, finrank_bot]
  rw [lineE0_finrank] at this
  exact (by decide : ¬ (1 : ℕ) = 0) this

/-- There are no three pairwise orthogonal lines in `ℂ²`. -/
theorem no_three_pairwise_orthogonal_lines
    {A B C : QProp}
    (hA : finrank ℂ A = 1) (hB : finrank ℂ B = 1) (hC : finrank ℂ C = 1)
    (hAB : A ⟂ B) (hAC : A ⟂ C) (hBC : B ⟂ C) : False := by
  have hinf : A ⊓ B = (⊥ : QProp) := hAB.disjoint.eq_bot
  have hdim : finrank ℂ (A ⊔ B : QProp) = 2 := by
    have h := finrank_sup_add_finrank_inf_eq (s := A) (t := B)
    rw [hA, hB, hinf, finrank_bot] at h
    linarith
  have htop : (A ⊔ B : QProp) = ⊤ :=
    eq_of_le_of_finrank_eq le_top (hdim.trans finrank_top_qprop.symm)
  have hCle : C ≤ Aᗮ ⊓ Bᗮ := le_inf hAC.ge hBC.ge
  have hCbot : C = (⊥ : QProp) := by
    rw [inf_orthogonal, htop, top_orthogonal_eq_bot] at hCle
    exact le_bot_iff.mp hCle
  rw [hCbot, finrank_bot] at hC
  exact (by decide : ¬ (0 : ℕ) = 1) hC

end Logic

end DstDiophantine
