import DstDiophantine.Logic.TruthValue
import DstDiophantine.Logic.Connective
import DstDiophantine.Algebra.Invariant
import DstDiophantine.Algebra.Motor
import DstDiophantine.Framework.Lattice
import Mathlib.Tactic.Linarith

/-!
# Geometric-algebra reading of D4L

The four states are the sign and saturation of `JNormalized`, itself the
(normalised) Killing quadratic of the PGA torsion bivector `omegaTorsion`.

Usual–dual swap `daggerParams` (`α ↔ β`) sends `JNormalized ↦ -JNormalized`,
so signed negation is the algebra involution, not a new connective.
-/

namespace DstDiophantine

namespace Logic

open Admissible Invariant Motor Operations Real Framework

/-- Dagger / usual–dual swap flips the sign of raw and normalised \(J\). -/
theorem J_dagger (p : TorsionParams) : J (daggerParams p) = -J p := by
  rw [J_coef, J_coef]
  simp only [daggerParams, Fin.sum_univ_three]
  ring

theorem JNormalized_dagger (p : TorsionParams) :
    JNormalized (daggerParams p) = -JNormalized p := by
  unfold JNormalized
  rw [J_dagger]
  ring

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

/-- The torsion bivector is the PGA carrier of the height that is classified.
Coefficient dictionary: project `J` is *not* `(1/16) B(Ω,Ω)` under the
generator expansion; see `paper_appendix_killing_coeff_false`. -/
theorem J_of_omegaTorsion (p : TorsionParams) :
    J p = 4 * ((1 / 16) * omegaTorsionGeneratorKilling p) :=
  J_eq_four_times_one_sixteenth_omegaKilling p

end Logic

end DstDiophantine
