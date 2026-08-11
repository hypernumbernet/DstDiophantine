import DstDiophantine.Embedding.IntegerRotor
import DstDiophantine.Embedding.RotorClass
import DstDiophantine.Algebra.Amplification
import DstDiophantine.Algebra.Invariant
import DstDiophantine.Algebra.Operations

/-!
# Torsional height and one-step descent infrastructure
-/

namespace DstDiophantine

namespace Embedding

open Amplification Invariant Operations Real UnitGroup

variable {N : ℕ} [NeZero N]

/-- Normalised torsion height on parameter space. -/
noncomputable def torsionHeight (p : TorsionParams) : ℝ :=
  |JNormalized p|

/-- Height of the canonical integer rotor embedding. -/
noncomputable def integerHeight (n : ℤ) (_hn : n ≠ 0) : ℝ :=
  torsionHeight (pureBoost (2 * Real.log (Int.natAbs n)))

theorem integerHeight_eq (n : ℤ) (_hn : n ≠ 0) :
    integerHeight n _hn =
      |(16 / (3 * Real.pi ^ 2)) * (Real.log (Int.natAbs n)) ^ 2| := by
  unfold integerHeight torsionHeight
  rw [JNormalized_coef]
  simp only [pureBoost, Fin.sum_univ_three, pow_two, zero_pow two_ne_zero, sub_zero, mul_zero,
    add_zero]
  ring_nf

/-- Dual-sector parameters extracted by the dagger involution. -/
def descentCandidate (p : TorsionParams) : TorsionParams :=
  daggerParams p

theorem descentCandidate_swap (p : TorsionParams) :
    descentCandidate (descentCandidate p) = p := by
  cases p
  simp [descentCandidate, daggerParams]

def IsUnitClass (c : RotorClass N) : Prop :=
  rotorOfClass c ∈ DiscreteUnit N

theorem isUnitClass_of_any (c : RotorClass N) : IsUnitClass c :=
  mem_discreteUnit_of_class c

private theorem JNormalized_dagger_neg (p : TorsionParams) :
    JNormalized (daggerParams p) = -JNormalized p := by
  unfold JNormalized
  rw [J_coef, J_coef, daggerParams]
  simp only [Fin.sum_univ_three]
  ring_nf

/-- Dagger extraction does not increase torsion height (involutive swap). -/
theorem descent_height_eq (p : TorsionParams) :
    torsionHeight (descentCandidate p) = torsionHeight p := by
  unfold torsionHeight descentCandidate
  rw [JNormalized_dagger_neg, abs_neg]

theorem descent_height_le (p : TorsionParams) :
    torsionHeight (descentCandidate p) ≤ torsionHeight p := by
  rw [descent_height_eq]

end Embedding

end DstDiophantine
