import DstDiophantine.Embedding.IntegerRotor
import DstDiophantine.Algebra.Discrete
import DstDiophantine.Algebra.UnitGroup
import DstDiophantine.Algebra.Motor
import Mathlib.Data.Fintype.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation

/-!
# Rotor equivalence classes modulo the discrete unit group

Each admissible rotor class is represented by a point on `(ℤ/Nℤ)⁶`. Continuous
integer rotors are quantised to the nearest lattice representative.
-/

namespace DstDiophantine

namespace Embedding

open Discrete UnitGroup Operations Motor Real CliffordAlgebra PGA

variable {N : ℕ} [NeZero N]

/-- The zero point on the discrete torsion torus. -/
def zeroTorsion (N : ℕ) [NeZero N] : DiscreteTorsion N :=
  { n := fun _ => 0, m := fun _ => 0 }

theorem discreteRotor_zero (N : ℕ) [NeZero N] : discreteRotor (zeroTorsion N) = 1 := by
  simp [discreteRotor, rotorTorsion, toTorsionParams, zeroTorsion, omegaTorsion]

/-- Right-multiplication by a discrete unit: `r ~ s` when `r = s · u`. -/
def RotorRel (N : ℕ) [NeZero N] (r s : PGA) : Prop :=
  ∃ u ∈ DiscreteUnit N, r = s * u

theorem rotorRel_refl (r : PGA) : RotorRel N r r := by
  refine ⟨discreteRotor (zeroTorsion N), ⟨zeroTorsion N, rfl⟩, ?_⟩
  simp [discreteRotor_zero]

/-- Rotor class represented by a discrete torus point (canonical representative). -/
structure RotorClass (N : ℕ) [NeZero N] where
  rep : DiscreteTorsion N

def rotorClassOf (t : DiscreteTorsion N) : RotorClass N := ⟨t⟩

noncomputable def rotorOfClass (c : RotorClass N) : PGA :=
  discreteRotor c.rep

/-- Quantise `log|n|` to the nearest lattice rapidity on axis `0`. -/
noncomputable def quantizeInt (N : ℕ) [NeZero N] (n : ℤ) (_hn : n ≠ 0) : DiscreteTorsion N :=
  { n := fun a => match a with
      | 0 => (⌊2 * Real.log (Int.natAbs n) * N / (2 * Real.pi)⌋ : ZMod N)
      | _ => 0
    m := fun _ => 0 }

noncomputable def integerClass (n : ℤ) (hn : n ≠ 0) : RotorClass N :=
  rotorClassOf (quantizeInt N n hn)

theorem mem_discreteUnit_of_class (c : RotorClass N) :
    rotorOfClass c ∈ DiscreteUnit N :=
  ⟨c.rep, rfl⟩

noncomputable def rotorClassEquiv : RotorClass N ≃ DiscreteTorsion N where
  toFun c := c.rep
  invFun t := ⟨t⟩
  left_inv c := by cases c; rfl
  right_inv _ := rfl

noncomputable instance : Fintype (RotorClass N) :=
  Fintype.ofEquiv _ rotorClassEquiv.symm

theorem rotorClass_finite : (Set.univ : Set (RotorClass N)).Finite :=
  Set.finite_univ

end Embedding

end DstDiophantine
