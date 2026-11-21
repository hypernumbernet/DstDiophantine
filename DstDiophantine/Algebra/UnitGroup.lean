import DstDiophantine.Algebra.Discrete
import DstDiophantine.Algebra.Motor

/-!
# Finite discrete torsion-rotor image

`DiscreteUnit` is the image of `(ℤ/Nℤ)⁶`, not the unit group of an integer biquaternion order.
-/

namespace DstDiophantine

open Discrete Motor Operations CliffordAlgebra

namespace UnitGroup

variable {N : ℕ} [NeZero N]

noncomputable def discreteRotor (t : DiscreteTorsion N) : PGA :=
  rotorTorsion (toTorsionParams t)

/-- Finite image of discrete rotors on `(ℤ/Nℤ)⁶`, not `Units`. -/
def DiscreteUnit (N : ℕ) [NeZero N] : Set PGA :=
  Set.range (discreteRotor (N := N))

/-- Finite image alias, not `Rˣ`. -/
abbrev DiscreteRotorImage (N : ℕ) [NeZero N] := DiscreteUnit N

theorem mem_discreteUnit_iff {x : PGA} :
    x ∈ DiscreteUnit N ↔ ∃ t : DiscreteTorsion N, discreteRotor t = x :=
  Set.mem_range

theorem discreteUnit_finite : (DiscreteUnit N).Finite :=
  Set.finite_range _

theorem discreteRotorImage_finite : (DiscreteRotorImage N).Finite :=
  discreteUnit_finite

noncomputable instance : Fintype {x // x ∈ DiscreteUnit N} :=
  discreteUnit_finite.fintype

/-- Sign-flipped torsion parameters (generator of the reverse rotor). -/
def negTorsionParams (p : TorsionParams) : TorsionParams where
  alpha := fun a => -p.alpha a
  beta := fun a => -p.beta a

theorem omegaTorsion_neg (p : TorsionParams) :
    omegaTorsion (negTorsionParams p) = -omegaTorsion p := by
  simp only [omegaTorsion, negTorsionParams, neg_div]
  rw [← Finset.sum_neg_distrib]
  congr 1
  ext a
  simp [neg_add_rev, add_comm]

theorem reverse_discreteRotor (t : DiscreteTorsion N) :
    reverse (discreteRotor t) =
      rotorTorsion (negTorsionParams (toTorsionParams t)) := by
  dsimp [discreteRotor, rotorTorsion]
  rw [reverse_exp_of_reverse_neg (omegaTorsion_reverse _), ← omegaTorsion_neg]

theorem discreteRotor_mul_reverse (t : DiscreteTorsion N) :
    discreteRotor t * reverse (discreteRotor t) = 1 :=
  rotor_unitary (toTorsionParams t)

/-- The zero rotor's reverse lies in the image; a general reverse need not. -/
theorem reverse_discreteRotor_zero_mem
    (t0 : DiscreteTorsion N)
    (h0 : toTorsionParams t0 = ⟨fun _ => 0, fun _ => 0⟩) :
    reverse (discreteRotor t0) ∈ DiscreteUnit N := by
  have h : discreteRotor t0 = 1 := by
    simp [discreteRotor, rotorTorsion, h0, omegaTorsion]
  refine ⟨t0, ?_⟩
  rw [reverse_discreteRotor, h0]
  simp [negTorsionParams, rotorTorsion, omegaTorsion, h]

/-- Image of *admissible* discrete rotors. A subset of `DiscreteRotorImage`. -/
def AdmissibleRotorImage (N : ℕ) [NeZero N] : Set PGA :=
  { x | ∃ t : DiscreteTorsion N, IsAdmissible t ∧ discreteRotor t = x }

theorem mem_admissibleRotorImage_iff {x : PGA} :
    x ∈ AdmissibleRotorImage N ↔
      ∃ t : DiscreteTorsion N, IsAdmissible t ∧ discreteRotor t = x :=
  Iff.rfl

theorem admissibleRotorImage_subset_discrete :
    AdmissibleRotorImage N ⊆ DiscreteRotorImage N := by
  rintro x ⟨t, _, rfl⟩
  exact ⟨t, rfl⟩

theorem admissibleRotorImage_finite : (AdmissibleRotorImage N).Finite :=
  discreteUnit_finite.subset admissibleRotorImage_subset_discrete

end UnitGroup

end DstDiophantine
