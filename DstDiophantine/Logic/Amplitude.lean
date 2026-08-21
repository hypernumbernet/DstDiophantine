/-
Copyright (c) 2026 DstDiophantine contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DstDiophantine contributors
-/
import DstDiophantine.Logic.Interpretation
import DstDiophantine.Algebra.Motor

/-!
# D4L amplitudes

A proposition's primary carrier is an admissible torsion configuration, not a
scalar in `[-1,1]`. The four labels appear only after measurement.

* `measure` is `JNormalized`.
* `collapse` is the existing classifier `ofParams`.
* `adjoint` is the usual–dual swap, already known to flip the sign of `J`.
* `mass` is the unsigned second observable. `IsVacuum` / `IsBalancedMassive`
  split label `T`; they are predicates, not a fifth name.

This module does **not** introduce a Hilbert space, a Born rule, or a new
Clifford algebra. The PGA objects `omega` / `rotor` are the ones already
proved in `Algebra.Motor`.
-/

namespace DstDiophantine

namespace Logic

open Admissible Invariant Motor Operations

/-- Usual–dual swap is an involution on parameter space. -/
@[simp] theorem daggerParams_involutive (p : TorsionParams) :
    daggerParams (daggerParams p) = p :=
  rfl

/-- Bundled admissible configuration: the D4L amplitude. -/
@[ext]
structure Amplitude where
  params : TorsionParams
  admissible : IsAdmissibleContinuous params

namespace Amplitude

/-- Scalar observable: the already-proved normalised torsional height. -/
noncomputable def measure (a : Amplitude) : ℝ :=
  JNormalized a.params

/-- Four-state collapse. -/
noncomputable def collapse (a : Amplitude) : TruthValue :=
  ofParams a.params a.admissible

/-- Usual–dual adjoint. -/
def adjoint (a : Amplitude) : Amplitude :=
  ⟨daggerParams a.params, isAdmissibleContinuous_dagger a.admissible⟩

/-- Torsion bivector carrier. -/
noncomputable def omega (a : Amplitude) : PGA :=
  omegaTorsion a.params

/-- Torsion rotor `exp(Ω)`. -/
noncomputable def rotor (a : Amplitude) : PGA :=
  rotorTorsion a.params

@[simp] theorem adjoint_params (a : Amplitude) :
    a.adjoint.params = daggerParams a.params :=
  rfl

theorem adjoint_involutive (a : Amplitude) : a.adjoint.adjoint = a := by
  ext
  exact daggerParams_involutive a.params

theorem measure_adjoint (a : Amplitude) : a.adjoint.measure = -a.measure :=
  JNormalized_dagger a.params

theorem abs_measure (a : Amplitude) : |a.measure| ≤ 1 :=
  torsion_bound_continuous a.params a.admissible

theorem collapse_eq_classify (a : Amplitude) :
    a.collapse = classifyOfMem a.measure a.abs_measure :=
  rfl

theorem collapse_adjoint (a : Amplitude) :
    a.adjoint.collapse =
      classifyOfMem (negJ a.measure) (by simpa [negJ, abs_neg] using a.abs_measure) :=
  ofParams_dagger a.admissible

theorem measure_eq_zero_iff (a : Amplitude) :
    a.measure = 0 ↔ a.collapse = .T :=
  (ofParams_eq_T_iff a.admissible).symm

theorem measure_eq_one_iff (a : Amplitude) :
    a.measure = 1 ↔ a.collapse = .F :=
  (ofParams_eq_F_iff a.admissible).symm

/-- Unsigned mass of the underlying torsion configuration. -/
noncomputable def mass (a : Amplitude) : ℝ :=
  Invariant.mass a.params

noncomputable def massNormalized (a : Amplitude) : ℝ :=
  Invariant.massNormalized a.params

theorem mass_nonneg (a : Amplitude) : 0 ≤ a.mass :=
  Invariant.mass_nonneg a.params

theorem massNormalized_nonneg (a : Amplitude) : 0 ≤ a.massNormalized :=
  Invariant.massNormalized_nonneg a.params

theorem massNormalized_le_one (a : Amplitude) : a.massNormalized ≤ 1 :=
  massNormalized_bound_continuous a.params a.admissible

theorem mass_adjoint (a : Amplitude) : a.adjoint.mass = a.mass :=
  mass_dagger a.params

/--
Vacuum: label `T` with vanishing mass. A predicate on amplitudes, not a
fifth D4L name. Equivalent to all six rapidities being zero.
-/
def IsVacuum (a : Amplitude) : Prop :=
  a.collapse = .T ∧ a.mass = 0

/--
Balanced massive: label `T` with positive mass. The geometric seat of
balanced Beal seeds, conflated with vacuum by signed height alone.
-/
def IsBalancedMassive (a : Amplitude) : Prop :=
  a.collapse = .T ∧ 0 < a.mass

theorem isVacuum_iff_mass_eq_zero (a : Amplitude) :
    a.IsVacuum ↔ a.mass = 0 := by
  constructor
  · exact And.right
  · intro hM
    refine ⟨a.measure_eq_zero_iff.mp ?_, hM⟩
    have hJ : J a.params = 0 := J_eq_zero_of_mass_eq_zero hM
    simp [Amplitude.measure, JNormalized, hJ]

theorem isVacuum_iff_zero_rapidities (a : Amplitude) :
    a.IsVacuum ↔ ∀ ax : Fin 3, a.params.alpha ax = 0 ∧ a.params.beta ax = 0 := by
  rw [isVacuum_iff_mass_eq_zero, Amplitude.mass, mass_eq_zero_iff]

theorem isBalancedMassive_iff (a : Amplitude) :
    a.IsBalancedMassive ↔ a.measure = 0 ∧ 0 < a.mass := by
  constructor
  · intro h
    exact ⟨a.measure_eq_zero_iff.mpr h.1, h.2⟩
  · intro h
    exact ⟨a.measure_eq_zero_iff.mp h.1, h.2⟩

theorem not_vacuum_of_balancedMassive {a : Amplitude} (h : a.IsBalancedMassive) :
    ¬ a.IsVacuum := by
  intro hv
  exact (not_le.mpr h.2) (le_of_eq hv.2)

end Amplitude

/-- Every label is realised by some amplitude. -/
theorem exists_amplitude (tv : TruthValue) : ∃ a : Amplitude, a.collapse = tv := by
  obtain ⟨p, h, hp⟩ := exists_ofParams tv
  exact ⟨⟨p, h⟩, hp⟩

/-- Vacuum is inhabited (the origin of the admissible cone). -/
noncomputable def vacuumAmplitude : Amplitude :=
  ⟨pureHyperbolicRay 0, isAdmissibleContinuous_pureHyperbolicRay (by norm_num) (by norm_num)⟩

theorem vacuumAmplitude_isVacuum : vacuumAmplitude.IsVacuum :=
  (Amplitude.isVacuum_iff_mass_eq_zero _).mpr <|
    (mass_eq_zero_iff _).mpr fun _ => by simp [vacuumAmplitude, pureHyperbolicRay]

/-- Balanced massive configurations inhabit label `T` with positive mass. -/
noncomputable def balancedAmplitude : Amplitude :=
  ⟨balancedRay 1, isAdmissibleContinuous_balancedRay (by norm_num) (by norm_num)⟩

theorem balancedAmplitude_isBalancedMassive : balancedAmplitude.IsBalancedMassive := by
  refine ⟨?_, ?_⟩
  · exact (Amplitude.measure_eq_zero_iff _).mp <| by
      simpa [Amplitude.measure, balancedAmplitude] using JNormalized_balancedRay 1
  · simpa [Amplitude.mass, balancedAmplitude] using
      mass_balancedRay_pos (by norm_num : (1 : ℝ) ≠ 0)

theorem exists_balancedMassive : ∃ a : Amplitude, a.IsBalancedMassive :=
  ⟨balancedAmplitude, balancedAmplitude_isBalancedMassive⟩

/-- Label `T` is not a single geometric point: vacuum and balanced massive coexist. -/
theorem T_splits_vacuum_and_balancedMassive :
    (∃ a : Amplitude, a.collapse = .T ∧ a.IsVacuum) ∧
      (∃ b : Amplitude, b.collapse = .T ∧ b.IsBalancedMassive) :=
  ⟨⟨vacuumAmplitude, vacuumAmplitude_isVacuum.1, vacuumAmplitude_isVacuum⟩,
    ⟨balancedAmplitude, balancedAmplitude_isBalancedMassive.1,
      balancedAmplitude_isBalancedMassive⟩⟩

end Logic

end DstDiophantine
