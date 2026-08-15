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

end Amplitude

/-- Every label is realised by some amplitude. -/
theorem exists_amplitude (tv : TruthValue) : ∃ a : Amplitude, a.collapse = tv := by
  obtain ⟨p, h, hp⟩ := exists_ofParams tv
  exact ⟨⟨p, h⟩, hp⟩

end Logic

end DstDiophantine
