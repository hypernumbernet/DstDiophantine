/-
Copyright (c) 2026 DstDiophantine contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DstDiophantine contributors
-/
import DstDiophantine.Logic.TruthValue
import DstDiophantine.Framework.Lattice
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-!
# Discrete D4L amplitudes

The amplitude layer on the finite torus. When `¬ 4 ∣ N` the sharp discrete
bound is strict, so the label `F` is uninhabited — a discrete strengthening
of Example 3. When `4 ∣ N` both walls are attained.

Does not import `Theorems`.
-/

namespace DstDiophantine

namespace Logic

open Discrete Framework Invariant

variable {N : ℕ} [NeZero N]

/-- An admissible discrete configuration, viewed as a D4L amplitude. -/
structure DiscreteAmplitude (N : ℕ) [NeZero N] where
  point : AdmissibleClass N

namespace DiscreteAmplitude

noncomputable def measure (a : DiscreteAmplitude N) : ℝ :=
  JNormalized (AdmissibleClass.toParams a.point)

theorem abs_measure (a : DiscreteAmplitude N) : |a.measure| ≤ 1 :=
  torsion_bound_discrete_sharp_le_one a.point.val a.point.property

noncomputable def collapse (a : DiscreteAmplitude N) : TruthValue :=
  classifyOfMem a.measure a.abs_measure

/-- If `4` does not divide `N`, no discrete amplitude saturates `F`. -/
theorem collapse_ne_F_of_not_four_dvd (h4 : ¬ 4 ∣ N) (a : DiscreteAmplitude N) :
    a.collapse ≠ .F := by
  intro hf
  have h1 : a.measure = 1 := (classifyOfMem_eq_F_iff a.abs_measure).mp hf
  have hlt : |a.measure| < 1 :=
    torsion_bound_discrete_strict h4 a.point.val a.point.property
  rw [h1] at hlt
  norm_num at hlt

end DiscreteAmplitude

/-- The zero lattice point is admissible. -/
theorem zeroDiscrete_admissible : IsAdmissible (N := N) ⟨fun _ => 0, fun _ => 0⟩ := by
  intro a
  have hπ : (0 : ℝ) ≤ Real.pi / 2 := by positivity
  refine ⟨?_, ?_, ?_⟩
  · simp [toTorsionParams]
  · simp [toTorsionParams]
  · simpa [toTorsionParams] using hπ

/-- Discrete `T` is inhabited at every compactification. -/
noncomputable def discreteZero : DiscreteAmplitude N :=
  ⟨⟨⟨fun _ => 0, fun _ => 0⟩, zeroDiscrete_admissible⟩⟩

theorem discreteZero_collapse_T : (discreteZero (N := N)).collapse = .T := by
  have hJ : JNormalized (toTorsionParams (N := N) ⟨fun _ => 0, fun _ => 0⟩) = 0 := by
    -- `latticeMismatch` of the origin is 0, hence `JNormalized = 0`.
    have hzm : latticeMismatch (N := N) ⟨fun _ => 0, fun _ => 0⟩ = 0 := by
      simp [latticeMismatch]
    have := JNormalized_eq_sixteen_lattice (N := N) ⟨fun _ => 0, fun _ => 0⟩
    simpa [hzm] using this
  have habs := (discreteZero (N := N)).abs_measure
  have hmeas : (discreteZero (N := N)).measure = 0 := by
    simpa [DiscreteAmplitude.measure, AdmissibleClass.toParams, discreteZero] using hJ
  exact (classifyOfMem_eq_T_iff habs).mpr hmeas

/-- When `4 ∣ N`, the discrete all-boost wall realises `F`. -/
noncomputable def discreteF (h4 : 4 ∣ N) : DiscreteAmplitude N :=
  ⟨⟨pureHyperbolicDiscrete N, pureHyperbolicDiscrete_admissible h4⟩⟩

theorem discreteF_collapse (h4 : 4 ∣ N) : (discreteF h4).collapse = .F := by
  have hJ := JNormalized_pureHyperbolicDiscrete h4
  have habs := (discreteF h4).abs_measure
  have hmeas : (discreteF h4).measure = 1 := by
    simpa [DiscreteAmplitude.measure, AdmissibleClass.toParams, discreteF] using hJ
  exact (classifyOfMem_eq_F_iff habs).mpr hmeas

end Logic

end DstDiophantine
