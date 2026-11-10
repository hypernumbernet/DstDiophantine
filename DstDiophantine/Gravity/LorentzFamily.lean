import DstDiophantine.Algebra.Amplification
import DstDiophantine.Algebra.Generators
import DstDiophantine.Algebra.Motor
import DstDiophantine.Algebra.Sandwich
import DstDiophantine.Gravity.Coframe
import DstDiophantine.Gravity.PlaneTorsion
import DstDiophantine.Gravity.Weitzenbock
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring

/-!
# The six inertial planes, and one-parameter curvature

Each coordinate plane carries a one-parameter coframe. Boosts are the three
`hyperbolic` axes and rotations the three `cyclic` axes. In every case the
induced metric is Minkowski, the plane block has determinant one, the
coordinate torsion remembers only the jet of the angle, and the teleparallel
scalar vanishes for an arbitrary four-component jet. The same parameter has
mismatch `+½φ²` on a boost and `-½θ²` on a rotation.

The Maurer–Cartan coefficient `(dR/dφ) R̃` of a one-parameter rotor is the
constant generator. A connection proportional to one `dφ` therefore has
vanishing curvature. That curvature is not the teleparallel scalar.
-/

namespace DstDiophantine

namespace Gravity

open Finset PlaneTorsion Real PGA Generators Motor
open Amplification Invariant

def axis4 (i : Fin 3) : Fin 4 := i.succ

def boostCoeff (i : Fin 3) : Fin 6 → ℝ :=
  fun k => if k = i.castLE (by decide : 3 ≤ 6) then 1 else 0

/-- Boost generator in the `(t, axis)` plane. `0,1,2` are `hyperbolic 0,1,2`. -/
def axisBoostGen (i : Fin 3) : Fin 4 → Fin 4 → ℝ :=
  soK (boostCoeff i)

def rotSlot : Fin 3 → Fin 6
  | 0 => 5
  | 1 => 4
  | 2 => 3

def rotCoeff (i : Fin 3) : Fin 6 → ℝ :=
  fun k => if k = rotSlot i then 1 else 0

/-- Rotation generator. `0,1,2` are the `(y,z)`, `(z,x)`, `(x,y)` planes. -/
def axisRotGen (i : Fin 3) : Fin 4 → Fin 4 → ℝ :=
  soK (rotCoeff i)

def rotP : Fin 3 → Fin 4
  | 0 => 2
  | 1 => 1
  | 2 => 1

def rotQ : Fin 3 → Fin 4
  | 0 => 3
  | 1 => 3
  | 2 => 2

theorem axisBoostGen_antisym (i : Fin 3) : MinkowskiAntisym (axisBoostGen i) :=
  soK_minkowskiAntisym _

theorem axisRotGen_antisym (i : Fin 3) : MinkowskiAntisym (axisRotGen i) :=
  soK_minkowskiAntisym _

/-- Teleparallel scalar of a boost jet, including derivatives off the plane. -/
theorem axisBoostTeleparallel_eq_zero (i : Fin 3) (d : Fin 4 → ℝ) :
    genTeleparallel (axisBoostGen i) d = 0 :=
  genTeleparallel_eq_zero (axisBoostGen_antisym i) d

/-- Teleparallel scalar of a rotation jet, including derivatives off the plane. -/
theorem axisRotTeleparallel_eq_zero (i : Fin 3) (d : Fin 4 → ℝ) :
    genTeleparallel (axisRotGen i) d = 0 :=
  genTeleparallel_eq_zero (axisRotGen_antisym i) d

def axisBoostParams (i : Fin 3) (φ : ℝ) : Operations.TorsionParams where
  alpha := fun a => if a = i then φ else 0
  beta := fun _ => 0

def axisRotParams (i : Fin 3) (θ : ℝ) : Operations.TorsionParams where
  alpha := fun _ => 0
  beta := fun a => if a = i then θ else 0

theorem J_axisBoost (i : Fin 3) (φ : ℝ) :
    J (axisBoostParams i φ) = (1 / 2) * φ ^ 2 := by
  rw [J_coef]
  fin_cases i <;> simp [axisBoostParams]

theorem J_axisRot (i : Fin 3) (θ : ℝ) :
    J (axisRotParams i θ) = -((1 / 2) * θ ^ 2) := by
  rw [J_coef]
  fin_cases i <;> simp [axisRotParams]

theorem J_axisRot_eq_neg_boost (i : Fin 3) (θ : ℝ) :
    J (axisRotParams i θ) = -J (axisBoostParams i θ) := by
  rw [J_axisRot, J_axisBoost]

noncomputable def axisBoostCoframe (i : Fin 3) (φ : ℝ) : Coframe :=
  fun a μ =>
    if a = 0 ∧ μ = 0 then Real.cosh φ
    else if a = 0 ∧ μ = axis4 i then Real.sinh φ
    else if a = axis4 i ∧ μ = 0 then Real.sinh φ
    else if a = axis4 i ∧ μ = axis4 i then Real.cosh φ
    else if a = μ then 1
    else 0

noncomputable def axisBoostFrame (i : Fin 3) (φ : ℝ) (μ a : Fin 4) : ℝ :=
  if a = 0 ∧ μ = 0 then Real.cosh φ
  else if a = 0 ∧ μ = axis4 i then -Real.sinh φ
  else if a = axis4 i ∧ μ = 0 then -Real.sinh φ
  else if a = axis4 i ∧ μ = axis4 i then Real.cosh φ
  else if a = μ then 1
  else 0

noncomputable def axisBoostDφ (i : Fin 3) (φ : ℝ) (a ν : Fin 4) : ℝ :=
  if a = 0 ∧ ν = 0 then Real.sinh φ
  else if a = 0 ∧ ν = axis4 i then Real.cosh φ
  else if a = axis4 i ∧ ν = 0 then Real.cosh φ
  else if a = axis4 i ∧ ν = axis4 i then Real.sinh φ
  else 0

theorem axisBoost_blockDet (i : Fin 3) (φ : ℝ) :
    axisBoostCoframe i φ 0 0 * axisBoostCoframe i φ (axis4 i) (axis4 i) -
        axisBoostCoframe i φ 0 (axis4 i) * axisBoostCoframe i φ (axis4 i) 0 = 1 := by
  fin_cases i <;> simp [axisBoostCoframe, axis4] <;>
    ring_nf <;> exact Real.cosh_sq_sub_sinh_sq φ

theorem inducedMetric_axisBoost (i : Fin 3) (φ : ℝ) (μ ν : Fin 4) :
    inducedMetric (axisBoostCoframe i φ) μ ν = if μ = ν then w31 μ else 0 := by
  rw [inducedMetric_eq_weighted]
  have h := Real.cosh_sq_sub_sinh_sq φ
  fin_cases i <;> fin_cases μ <;> fin_cases ν <;>
    simp [Fin.sum_univ_four, axisBoostCoframe, axis4, w31] <;>
    ring_nf <;> linarith

theorem axisBoost_frame_dφ (i : Fin 3) (φ : ℝ) (ρ ν : Fin 4) :
    ∑ a : Fin 4, axisBoostFrame i φ ρ a * axisBoostDφ i φ a ν = axisBoostGen i ρ ν := by
  have h := Real.cosh_sq_sub_sinh_sq φ
  fin_cases i <;> fin_cases ρ <;> fin_cases ν <;>
    simp [Fin.sum_univ_four, axisBoostFrame, axisBoostDφ, axisBoostGen, boostCoeff, soK,
      axis4] <;>
    ring_nf <;> linarith

theorem axisBoostCoordTorsion_eq (i : Fin 3) (φ : ℝ) (d : Fin 4 → ℝ) (ρ μ ν : Fin 4) :
    (∑ a : Fin 4, axisBoostFrame i φ ρ a *
        (d μ * axisBoostDφ i φ a ν - d ν * axisBoostDφ i φ a μ)) =
      genTorsion (axisBoostGen i) d ρ μ ν := by
  have hlin : ∀ a,
      axisBoostFrame i φ ρ a * (d μ * axisBoostDφ i φ a ν - d ν * axisBoostDφ i φ a μ) =
        d μ * (axisBoostFrame i φ ρ a * axisBoostDφ i φ a ν) -
          d ν * (axisBoostFrame i φ ρ a * axisBoostDφ i φ a μ) := by
    intro a; ring
  simp_rw [hlin, sum_sub_distrib, ← Finset.mul_sum, axisBoost_frame_dφ]
  rfl

noncomputable def axisRotCoframe (i : Fin 3) (θ : ℝ) : Coframe :=
  fun a μ =>
    if a = rotP i ∧ μ = rotP i then Real.cos θ
    else if a = rotP i ∧ μ = rotQ i then Real.sin θ
    else if a = rotQ i ∧ μ = rotP i then -Real.sin θ
    else if a = rotQ i ∧ μ = rotQ i then Real.cos θ
    else if a = μ then 1
    else 0

noncomputable def axisRotFrame (i : Fin 3) (θ : ℝ) (μ a : Fin 4) : ℝ :=
  if a = rotP i ∧ μ = rotP i then Real.cos θ
  else if a = rotQ i ∧ μ = rotP i then -Real.sin θ
  else if a = rotP i ∧ μ = rotQ i then Real.sin θ
  else if a = rotQ i ∧ μ = rotQ i then Real.cos θ
  else if a = μ then 1
  else 0

noncomputable def axisRotDθ (i : Fin 3) (θ : ℝ) (a ν : Fin 4) : ℝ :=
  if a = rotP i ∧ ν = rotP i then -Real.sin θ
  else if a = rotP i ∧ ν = rotQ i then Real.cos θ
  else if a = rotQ i ∧ ν = rotP i then -Real.cos θ
  else if a = rotQ i ∧ ν = rotQ i then -Real.sin θ
  else 0

theorem axisRot_blockDet (i : Fin 3) (θ : ℝ) :
    axisRotCoframe i θ (rotP i) (rotP i) * axisRotCoframe i θ (rotQ i) (rotQ i) -
        axisRotCoframe i θ (rotP i) (rotQ i) *
          axisRotCoframe i θ (rotQ i) (rotP i) = 1 := by
  fin_cases i <;> simp [axisRotCoframe, rotP, rotQ] <;>
    ring_nf <;> exact Real.cos_sq_add_sin_sq θ

theorem inducedMetric_axisRot (i : Fin 3) (θ : ℝ) (μ ν : Fin 4) :
    inducedMetric (axisRotCoframe i θ) μ ν = if μ = ν then w31 μ else 0 := by
  rw [inducedMetric_eq_weighted]
  have h := Real.cos_sq_add_sin_sq θ
  fin_cases i <;> fin_cases μ <;> fin_cases ν <;>
    simp [Fin.sum_univ_four, axisRotCoframe, rotP, rotQ, w31] <;>
    ring_nf <;> linarith

theorem axisRot_frame_dθ (i : Fin 3) (θ : ℝ) (ρ ν : Fin 4) :
    ∑ a : Fin 4, axisRotFrame i θ ρ a * axisRotDθ i θ a ν = axisRotGen i ρ ν := by
  have h := Real.cos_sq_add_sin_sq θ
  fin_cases i <;> fin_cases ρ <;> fin_cases ν <;>
    simp [Fin.sum_univ_four, axisRotFrame, axisRotDθ, axisRotGen, rotCoeff, rotSlot, soK,
      rotP, rotQ] <;>
    ring_nf <;> linarith

theorem axisRotCoordTorsion_eq (i : Fin 3) (θ : ℝ) (d : Fin 4 → ℝ) (ρ μ ν : Fin 4) :
    (∑ a : Fin 4, axisRotFrame i θ ρ a *
        (d μ * axisRotDθ i θ a ν - d ν * axisRotDθ i θ a μ)) =
      genTorsion (axisRotGen i) d ρ μ ν := by
  have hlin : ∀ a,
      axisRotFrame i θ ρ a * (d μ * axisRotDθ i θ a ν - d ν * axisRotDθ i θ a μ) =
        d μ * (axisRotFrame i θ ρ a * axisRotDθ i θ a ν) -
          d ν * (axisRotFrame i θ ρ a * axisRotDθ i θ a μ) := by
    intro a; ring
  simp_rw [hlin, sum_sub_distrib, ← Finset.mul_sum, axisRot_frame_dθ]
  rfl

/-! ### Constant boost coframe is the dual of the sandwich -/

theorem sandwich_pureBoost_coframe_ι0 (φ : ℝ) :
    Sandwich.sandwich (rotorTorsion (pureBoost φ)) (ι 0) =
      axisBoostCoframe 0 φ 0 0 • ι 0 + axisBoostCoframe 0 φ 0 1 • ι 1 +
        axisBoostCoframe 0 φ 0 2 • ι 2 + axisBoostCoframe 0 φ 0 3 • ι 3 := by
  rw [Sandwich.sandwich_pureBoost_ι0]
  simp [axisBoostCoframe, axis4]

theorem sandwich_pureBoost_coframe_ι1 (φ : ℝ) :
    Sandwich.sandwich (rotorTorsion (pureBoost φ)) (ι 1) =
      axisBoostCoframe 0 φ 1 0 • ι 0 + axisBoostCoframe 0 φ 1 1 • ι 1 +
        axisBoostCoframe 0 φ 1 2 • ι 2 + axisBoostCoframe 0 φ 1 3 • ι 3 := by
  rw [Sandwich.sandwich_pureBoost_ι1]
  simp [axisBoostCoframe, axis4]

theorem sandwich_pureBoost_coframe_ι2 (φ : ℝ) :
    Sandwich.sandwich (rotorTorsion (pureBoost φ)) (ι 2) = ι 2 := by
  rw [Sandwich.sandwich_pureBoost_ι2]

theorem sandwich_pureBoost_coframe_ι3 (φ : ℝ) :
    Sandwich.sandwich (rotorTorsion (pureBoost φ)) (ι 3) = ι 3 := by
  rw [Sandwich.sandwich_pureBoost_ι3]

theorem sandwich_rotation2_coframe_ι1 (θ : ℝ) :
    Sandwich.sandwich (rotorTorsion (Sandwich.pureRotation2 θ)) (ι 1) =
      axisRotCoframe 2 θ 1 1 • ι 1 + axisRotCoframe 2 θ 1 2 • ι 2 := by
  rw [Sandwich.sandwich_pureRotation2_ι1]
  simp [axisRotCoframe, rotP, rotQ]

theorem sandwich_rotation2_coframe_ι2 (θ : ℝ) :
    Sandwich.sandwich (rotorTorsion (Sandwich.pureRotation2 θ)) (ι 2) =
      axisRotCoframe 2 θ 2 1 • ι 1 + axisRotCoframe 2 θ 2 2 • ι 2 := by
  rw [Sandwich.sandwich_pureRotation2_ι2]
  simp [axisRotCoframe, rotP, rotQ]

theorem sandwich_rotation1_coframe_ι1 (θ : ℝ) :
    Sandwich.sandwich (rotorTorsion (pureRotation1 θ)) (ι 1) =
      axisRotCoframe 1 (-θ) 1 1 • ι 1 + axisRotCoframe 1 (-θ) 1 3 • ι 3 := by
  rw [Sandwich.sandwich_pureRotation1_ι1]
  simp [axisRotCoframe, rotP, rotQ, Real.cos_neg, Real.sin_neg]
  abel

theorem sandwich_rotation1_coframe_ι3 (θ : ℝ) :
    Sandwich.sandwich (rotorTorsion (pureRotation1 θ)) (ι 3) =
      axisRotCoframe 1 (-θ) 3 1 • ι 1 + axisRotCoframe 1 (-θ) 3 3 • ι 3 := by
  rw [Sandwich.sandwich_pureRotation1_ι3]
  simp [axisRotCoframe, rotP, rotQ, Real.cos_neg, Real.sin_neg]

/-! ### Maurer–Cartan coefficient of a one-parameter rotor -/

private theorem boost_half_expand (c s : ℝ) :
    ((((1 : ℝ) / 2) * s) • (1 : PGA) + (((1 : ℝ) / 2) * c) • hyperbolic 0) *
        (c • (1 : PGA) - s • hyperbolic 0) =
      (((1 : ℝ) / 2) * (c ^ 2 - s ^ 2)) • hyperbolic 0 := by
  have hsq : hyperbolic 0 * hyperbolic 0 = (1 : PGA) := hyperbolic_sq 0
  simp only [sub_eq_add_neg, mul_add, add_mul, smul_mul_assoc, mul_smul_comm, one_mul, mul_one,
    smul_smul, hsq, mul_neg, neg_smul, smul_add, add_smul]
  module

/-- `(dR/dφ) R̃ = ½ B` for the pure `(t,x)` boost. The coefficient does not depend on `φ`. -/
theorem pureBoost_mc (φ : ℝ) :
    ((((1 : ℝ) / 2) * Real.sinh (φ / 2)) • (1 : PGA) +
        (((1 : ℝ) / 2) * Real.cosh (φ / 2)) • hyperbolic 0) *
        (Real.cosh (φ / 2) • (1 : PGA) - Real.sinh (φ / 2) • hyperbolic 0) =
      ((1 : ℝ) / 2) • hyperbolic 0 := by
  rw [boost_half_expand, Real.cosh_sq_sub_sinh_sq, mul_one]

private theorem rot_half_expand (c s : ℝ) (B : PGA) (hB : B * B = -1) :
    ((((1 : ℝ) / 2) * (-s)) • (1 : PGA) + (((1 : ℝ) / 2) * c) • B) *
        (c • (1 : PGA) - s • B) =
      (((1 : ℝ) / 2) * (c ^ 2 + s ^ 2)) • B := by
  simp only [sub_eq_add_neg]
  have hexpand :
      ((((1 : ℝ) / 2) * (-s)) • (1 : PGA) + (((1 : ℝ) / 2) * c) • B) *
          (c • (1 : PGA) + -(s • B)) =
        ((((1 : ℝ) / 2) * (-s)) • (1 : PGA)) * (c • (1 : PGA)) +
          ((((1 : ℝ) / 2) * (-s)) • (1 : PGA)) * (-(s • B)) +
          ((((1 : ℝ) / 2) * c) • B) * (c • (1 : PGA)) +
          ((((1 : ℝ) / 2) * c) • B) * (-(s • B)) := by
    rw [add_mul, mul_add, mul_add]; abel
  rw [hexpand]
  have a1 : ((((1 : ℝ) / 2) * (-s)) • (1 : PGA)) * (c • (1 : PGA)) =
      ((((1 : ℝ) / 2) * (-s) * c) • (1 : PGA)) := by
    rw [mul_smul_comm, smul_mul_assoc, mul_one, smul_smul]
    congr 1
    ring
  have a2 : ((((1 : ℝ) / 2) * (-s)) • (1 : PGA)) * (-(s • B)) =
      -(((((1 : ℝ) / 2) * (-s) * s) • B)) := by
    rw [mul_neg, smul_mul_assoc, one_mul, smul_smul]
  have a3 : ((((1 : ℝ) / 2) * c) • B) * (c • (1 : PGA)) =
      ((((1 : ℝ) / 2) * c * c) • B) := by
    rw [mul_smul_comm, smul_mul_assoc, mul_one, smul_smul]
    congr 1
    ring
  have a4 : ((((1 : ℝ) / 2) * c) • B) * (-(s • B)) =
      ((((1 : ℝ) / 2) * c * s) • (1 : PGA)) := by
    rw [mul_neg, smul_mul_assoc, mul_smul_comm, hB]
    simp only [smul_neg, neg_neg, smul_smul]
  rw [a1, a2, a3, a4]
  module

/-- `(dR/dθ) R̃ = ½ B` for the pure rotation on `cyclic 2`. -/
theorem pureRotation2_mc (θ : ℝ) :
    ((((1 : ℝ) / 2) * (-Real.sin (θ / 2))) • (1 : PGA) +
        (((1 : ℝ) / 2) * Real.cos (θ / 2)) • cyclic 2) *
        (Real.cos (θ / 2) • (1 : PGA) - Real.sin (θ / 2) • cyclic 2) =
      ((1 : ℝ) / 2) • cyclic 2 := by
  rw [rot_half_expand _ _ _ (cyclic_sq 2), Real.cos_sq_add_sin_sq, mul_one]

/-- Curvature coefficient of a connection `c dφ`. The parameter derivative of a
constant coefficient vanishes, and `dφ ∧ dφ` contributes the commutator `[c,c]`. -/
theorem oneParam_curvature (c : PGA) : (0 : PGA) + (c * c - c * c) = 0 := by
  simp

theorem pureBoost_curvature (φ : ℝ) :
    ((((1 : ℝ) / 2) * Real.sinh (φ / 2)) • (1 : PGA) +
        (((1 : ℝ) / 2) * Real.cosh (φ / 2)) • hyperbolic 0) *
        (Real.cosh (φ / 2) • (1 : PGA) - Real.sinh (φ / 2) • hyperbolic 0) =
      ((1 : ℝ) / 2) • hyperbolic 0 ∧
      (0 : PGA) + (((1 : ℝ) / 2) • hyperbolic 0 * (((1 : ℝ) / 2) • hyperbolic 0) -
          ((1 : ℝ) / 2) • hyperbolic 0 * (((1 : ℝ) / 2) • hyperbolic 0)) = 0 :=
  ⟨pureBoost_mc φ, oneParam_curvature _⟩

theorem pureRotation2_curvature (θ : ℝ) :
    ((((1 : ℝ) / 2) * (-Real.sin (θ / 2))) • (1 : PGA) +
        (((1 : ℝ) / 2) * Real.cos (θ / 2)) • cyclic 2) *
        (Real.cos (θ / 2) • (1 : PGA) - Real.sin (θ / 2) • cyclic 2) =
      ((1 : ℝ) / 2) • cyclic 2 ∧
      (0 : PGA) + (((1 : ℝ) / 2) • cyclic 2 * (((1 : ℝ) / 2) • cyclic 2) -
          ((1 : ℝ) / 2) • cyclic 2 * (((1 : ℝ) / 2) • cyclic 2)) = 0 :=
  ⟨pureRotation2_mc θ, oneParam_curvature _⟩

end Gravity

end DstDiophantine
