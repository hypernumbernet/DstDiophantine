import DoubleSpacetime.Logic.TruthValue
import DoubleSpacetime.Logic.Connective
import DoubleSpacetime.Algebra.Invariant
import DoubleSpacetime.Algebra.Motor
import DoubleSpacetime.Framework.Lattice
import Mathlib.Tactic.Linarith

/-!
# Geometric-algebra reading of D4L

The four states are the sign and saturation of `JNormalized`. Signed negation is the usual–dual
swap, not a new connective.
-/

namespace DoubleSpacetime

namespace Logic

open Admissible Invariant Motor Operations Real Framework

theorem J_dagger (p : TorsionParams) : J (daggerParams p) = -J p :=
  Invariant.J_dagger p

theorem JNormalized_dagger (p : TorsionParams) :
    JNormalized (daggerParams p) = -JNormalized p :=
  Invariant.JNormalized_dagger p

theorem isAdmissibleContinuous_dagger {p : TorsionParams}
    (h : IsAdmissibleContinuous p) :
    IsAdmissibleContinuous (daggerParams p) := by
  intro a
  have ha := h a
  refine ⟨ha.2.1, ha.1, ?_⟩
  simpa [daggerParams, add_comm] using ha.2.2

theorem ofParams_dagger {p : TorsionParams} (h : IsAdmissibleContinuous p) :
    ofParams (daggerParams p) (isAdmissibleContinuous_dagger h) =
      classifyOfMem (negJ (JNormalized p))
        (by simpa [negJ, abs_neg] using torsion_bound_continuous p h) := by
  unfold ofParams
  exact classifyOfMem_eq_of_eq (by rw [JNormalized_dagger]; rfl) _ _

theorem ofParams_T_iff_zeroHeight {p : TorsionParams} (h : IsAdmissibleContinuous p) :
    ofParams p h = .T ↔ IsZeroHeight p := by
  rw [ofParams_eq_T_iff, isZeroHeight_iff_JNormalized]

/-- The coefficient `8∑(α²-β²)` is rejected. -/
theorem J_of_omegaTorsion (p : TorsionParams) :
    J p = 4 * ((1 / 16) * omegaTorsionGeneratorKilling p) :=
  J_eq_four_times_one_sixteenth_omegaKilling p

end Logic

end DoubleSpacetime
