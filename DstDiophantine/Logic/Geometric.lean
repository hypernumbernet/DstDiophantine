import DstDiophantine.Logic.Amplitude
import DstDiophantine.Algebra.Generators
import DstDiophantine.Algebra.Motor
import DstDiophantine.Algebra.Sandwich
import DstDiophantine.Algebra.Invariant
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# Geometric operations on amplitudes

The Killing pairing is the commutative overlap and the bivector commutator is the interference.
Rotor composition stays in `PGA` and is not pulled back through BCH; metric preservation is not
claimed.
-/

namespace DstDiophantine

namespace Logic

open Admissible Generators Invariant Motor Operations CliffordAlgebra
open Sandwich (sandwich)

export Sandwich (sandwich sandwich_one)

/-- Parameter Killing form. -/
def overlap (p q : TorsionParams) : ℝ :=
  killingForm p q

theorem overlap_symm (p q : TorsionParams) : overlap p q = overlap q p := by
  unfold overlap killingForm
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

theorem overlap_self (p : TorsionParams) : overlap p p = 16 * J p := by
  unfold overlap J
  ring

/-- A multiple of `JNormalized`. Not a Born probability. -/
theorem overlap_self_normalized (p : TorsionParams) :
    overlap p p = (6 * Real.pi ^ 2) * JNormalized p := by
  rw [overlap_self, JNormalized]
  field_simp
  ring

/-- Commutator of torsion bivectors. -/
noncomputable def interfere (p q : TorsionParams) : PGA :=
  Generators.commutator (omegaTorsion p) (omegaTorsion q)

theorem interfere_antisymm (p q : TorsionParams) :
    interfere p q = -interfere q p := by
  unfold interfere Generators.commutator
  abel

/-- Product in `PGA`. Not an operation on `TorsionParams`. -/
noncomputable def composeRotor (p q : TorsionParams) : PGA :=
  rotorTorsion p * rotorTorsion q

/-- Sandwich of a test vector by the torsion rotor. -/
noncomputable def eval (p : TorsionParams) (v : PGA) : PGA :=
  sandwich (rotorTorsion p) v

/-! ### Zero configuration and identity composition -/

def zeroParams : TorsionParams :=
  ⟨fun _ => 0, fun _ => 0⟩

theorem omegaTorsion_zero : omegaTorsion zeroParams = 0 := by
  simp [omegaTorsion, zeroParams]

theorem rotorTorsion_zero : rotorTorsion zeroParams = 1 := by
  simp [rotorTorsion, omegaTorsion_zero]

theorem composeRotor_zero_right (p : TorsionParams) :
    composeRotor p zeroParams = rotorTorsion p := by
  simp [composeRotor, rotorTorsion_zero]

theorem composeRotor_zero_left (p : TorsionParams) :
    composeRotor zeroParams p = rotorTorsion p := by
  simp [composeRotor, rotorTorsion_zero]

theorem eval_zero (v : PGA) : eval zeroParams v = v := by
  simp [eval, sandwich, rotorTorsion_zero]

/-! ### Non-commutativity of interference -/

/-- Axis-0 pure boost of rapidity `2`. Not required to be admissible. -/
def axis0Boost : TorsionParams :=
  ⟨fun a => if a = 0 then 2 else 0, fun _ => 0⟩

/-- Axis-1 pure rotation of rapidity `2`. Not required to be admissible. -/
def axis1Rotation : TorsionParams :=
  ⟨fun _ => 0, fun a => if a = 1 then 2 else 0⟩

private theorem omegaTorsion_axis0Boost :
    omegaTorsion axis0Boost = hyperbolic 0 := by
  simp [omegaTorsion, axis0Boost, Fin.sum_univ_three]

private theorem omegaTorsion_axis1Rotation :
    omegaTorsion axis1Rotation = cyclic 1 := by
  simp [omegaTorsion, axis1Rotation, Fin.sum_univ_three]

/-- Invisible to scalar `min`/`max`. -/
theorem interfere_axis0_axis1_ne_zero :
    interfere axis0Boost axis1Rotation ≠ 0 := by
  unfold interfere
  rw [omegaTorsion_axis0Boost, omegaTorsion_axis1Rotation]
  exact commutator_hyperbolic0_cyclic1_ne_zero

theorem interfere_axis0_self (α β : ℝ) :
    interfere
        ⟨fun a => if a = 0 then α else 0, fun _ => 0⟩
        ⟨fun _ => 0, fun a => if a = 0 then β else 0⟩ = 0 := by
  have hΩp :
      omegaTorsion ⟨fun a => if a = 0 then α else 0, fun _ => 0⟩ =
        (α / 2) • hyperbolic 0 := by
    simp [omegaTorsion, Fin.sum_univ_three]
  have hΩq :
      omegaTorsion ⟨fun _ => 0, fun a => if a = 0 then β else 0⟩ =
        (β / 2) • cyclic 0 := by
    simp [omegaTorsion, Fin.sum_univ_three]
  have hcomm : hyperbolic 0 * cyclic 0 = cyclic 0 * hyperbolic 0 :=
    sub_eq_zero.mp (commutator_hyperbolic_cyclic_same 0)
  have hmul (c d : ℝ) (x y : PGA) :
      (c • x) * (d • y) = (c * d) • (x * y) := by
    rw [smul_mul_assoc, mul_smul_comm, smul_smul]
  unfold interfere Generators.commutator
  rw [hΩp, hΩq, hmul, hmul, hcomm, mul_comm (α / 2) (β / 2), sub_self]

end Logic

end DstDiophantine
