import DstDiophantine.Algebra.Motor
import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Isometry

/-!
# Brackets of coordinate planes

The resulting translation, and the boost a displaced plane acquires, are not identified with the
torsional mismatch.
-/

namespace DstDiophantine.Gravity.PlaneBracket

open PGA Generators Motor

private theorem e2_sq : ι 2 * ι 2 = (1 : PGA) := by
  simp [e_sq, Q311_e5vec, w311]

private theorem e3_sq : ι 3 * ι 3 = (1 : PGA) := by
  simp [e_sq, Q311_e5vec, w311]

/-- Spatial volume `k = e₁ e₂ e₃`, the dual of the time axis. -/
noncomputable def spatialVolume : PGA :=
  ι 1 * ι 2 * ι 3

/-- Ideal coordinate plane `e₄ ∧ eᵢ ∧ eⱼ` whose right-handed normal is `e_{a+1}`. -/
noncomputable def idealPlane : Fin 3 → PGA
  | 0 => ι e4Index * ι 2 * ι 3
  | 1 => ι e4Index * ι 3 * ι 1
  | 2 => ι e4Index * ι 1 * ι 2

/-- Dual trivector of the normal `e_{a+1}`: `jI`, `jJ`, `jK` in that order. -/
noncomputable def dualNormal : Fin 3 → PGA
  | 0 => ι 0 * ι 3 * ι 2
  | 1 => ι 0 * ι 1 * ι 3
  | 2 => ι 0 * ι 2 * ι 1

/-! ### Products with the spatial volume -/

private theorem mul_plane2_volume :
    (ι e4Index * ι 1 * ι 2) * (ι 1 * ι 2 * ι 3) = -null 3 := by
  have h21 : ι 2 * ι 1 = -(ι 1 * ι 2) := e_mul_anticomm (by decide)
  calc
    (ι e4Index * ι 1 * ι 2) * (ι 1 * ι 2 * ι 3)
        = ι e4Index * ι 1 * (ι 2 * ι 1) * ι 2 * ι 3 := by simp [mul_assoc]
      _ = ι e4Index * ι 1 * (-(ι 1 * ι 2)) * ι 2 * ι 3 := by rw [h21]
      _ = -(ι e4Index * ι 1 * ι 1 * ι 2 * ι 2 * ι 3) := by simp [mul_neg, mul_assoc]
      _ = -(ι e4Index * (ι 1 * ι 1) * (ι 2 * ι 2) * ι 3) := by simp [mul_assoc]
      _ = -(ι e4Index * ι 3) := by simp [e1_sq, e2_sq]
      _ = ι 3 * ι e4Index := by
          have h3 : ι 3 * ι e4Index = -(ι e4Index * ι 3) := e4_inner_anticomm 3
          exact h3.symm
      _ = -null 3 := by
          have h3 : ι 3 * ι e4Index = -(ι e4Index * ι 3) := e4_inner_anticomm 3
          rw [h3]; simp [null]

private theorem mul_plane0_volume :
    (ι e4Index * ι 2 * ι 3) * (ι 1 * ι 2 * ι 3) = -null 1 := by
  have h31 : ι 3 * ι 1 = -(ι 1 * ι 3) := e_mul_anticomm (by decide)
  have h21 : ι 2 * ι 1 = -(ι 1 * ι 2) := e_mul_anticomm (by decide)
  have h32 : ι 3 * ι 2 = -(ι 2 * ι 3) := e_mul_anticomm (by decide)
  calc
    (ι e4Index * ι 2 * ι 3) * (ι 1 * ι 2 * ι 3)
        = ι e4Index * ι 2 * (ι 3 * ι 1) * ι 2 * ι 3 := by simp [mul_assoc]
      _ = ι e4Index * ι 2 * (-(ι 1 * ι 3)) * ι 2 * ι 3 := by rw [h31]
      _ = -(ι e4Index * (ι 2 * ι 1) * ι 3 * ι 2 * ι 3) := by simp [mul_neg, mul_assoc]
      _ = -(ι e4Index * (-(ι 1 * ι 2)) * ι 3 * ι 2 * ι 3) := by rw [h21]
      _ = ι e4Index * ι 1 * ι 2 * (ι 3 * ι 2) * ι 3 := by simp [mul_neg, mul_assoc]
      _ = ι e4Index * ι 1 * ι 2 * (-(ι 2 * ι 3)) * ι 3 := by rw [h32]
      _ = -(ι e4Index * ι 1 * (ι 2 * ι 2) * (ι 3 * ι 3)) := by simp [mul_neg, mul_assoc]
      _ = -(ι e4Index * ι 1) := by simp [e2_sq, e3_sq]
      _ = ι 1 * ι e4Index := by
          have h1 : ι 1 * ι e4Index = -(ι e4Index * ι 1) := e4_inner_anticomm 1
          exact h1.symm
      _ = -null 1 := by
          have h1 : ι 1 * ι e4Index = -(ι e4Index * ι 1) := e4_inner_anticomm 1
          rw [h1]; simp [null]

private theorem mul_plane1_volume :
    (ι e4Index * ι 3 * ι 1) * (ι 1 * ι 2 * ι 3) = -null 2 := by
  have h32 : ι 3 * ι 2 = -(ι 2 * ι 3) := e_mul_anticomm (by decide)
  calc
    (ι e4Index * ι 3 * ι 1) * (ι 1 * ι 2 * ι 3)
        = ι e4Index * ι 3 * (ι 1 * ι 1) * ι 2 * ι 3 := by simp [mul_assoc]
      _ = ι e4Index * (ι 3 * ι 2) * ι 3 := by simp [e1_sq, mul_assoc]
      _ = ι e4Index * (-(ι 2 * ι 3)) * ι 3 := by rw [h32]
      _ = -(ι e4Index * ι 2 * (ι 3 * ι 3)) := by simp [mul_neg, mul_assoc]
      _ = -(ι e4Index * ι 2) := by simp [e3_sq]
      _ = ι 2 * ι e4Index := by
          have h2 : ι 2 * ι e4Index = -(ι e4Index * ι 2) := e4_inner_anticomm 2
          exact h2.symm
      _ = -null 2 := by
          have h2 : ι 2 * ι e4Index = -(ι e4Index * ι 2) := e4_inner_anticomm 2
          rw [h2]; simp [null]

private theorem plane12_blade :
    ι 1 * ι 2 * ι e4Index = ι e4Index * ι 1 * ι 2 := by
  calc
    ι 1 * ι 2 * ι e4Index
        = ι 1 * (ι 2 * ι e4Index) := by simp [mul_assoc]
      _ = ι 1 * -(ι e4Index * ι 2) := by
          rw [show ι 2 * ι e4Index = -(ι e4Index * ι 2) from e4_inner_anticomm 2]
      _ = -(ι 1 * ι e4Index * ι 2) := by simp [mul_neg, mul_assoc]
      _ = -(-(ι e4Index * ι 1) * ι 2) := by
          rw [show ι 1 * ι e4Index = -(ι e4Index * ι 1) from e4_inner_anticomm 1]
      _ = ι e4Index * ι 1 * ι 2 := by simp [mul_assoc]

private theorem mul_volume_blade12 :
    (ι 1 * ι 2 * ι 3) * (ι 1 * ι 2 * ι e4Index) = null 3 := by
  have h31 : ι 3 * ι 1 = -(ι 1 * ι 3) := e_mul_anticomm (by decide)
  have h21 : ι 2 * ι 1 = -(ι 1 * ι 2) := e_mul_anticomm (by decide)
  have h32 : ι 3 * ι 2 = -(ι 2 * ι 3) := e_mul_anticomm (by decide)
  calc
    (ι 1 * ι 2 * ι 3) * (ι 1 * ι 2 * ι e4Index)
        = ι 1 * ι 2 * (ι 3 * ι 1) * ι 2 * ι e4Index := by simp [mul_assoc]
      _ = ι 1 * ι 2 * (-(ι 1 * ι 3)) * ι 2 * ι e4Index := by rw [h31]
      _ = -(ι 1 * (ι 2 * ι 1) * ι 3 * ι 2 * ι e4Index) := by simp [mul_neg, mul_assoc]
      _ = -(ι 1 * (-(ι 1 * ι 2)) * ι 3 * ι 2 * ι e4Index) := by rw [h21]
      _ = (ι 1 * ι 1) * ι 2 * (ι 3 * ι 2) * ι e4Index := by simp [mul_neg, mul_assoc]
      _ = ι 2 * (-(ι 2 * ι 3)) * ι e4Index := by rw [h32]; simp [e1_sq, mul_assoc]
      _ = -(ι 2 * ι 2 * ι 3 * ι e4Index) := by simp [mul_neg, mul_assoc]
      _ = -(ι 3 * ι e4Index) := by simp [e2_sq]
      _ = null 3 := by
          rw [← show ι e4Index * ι 3 = -(ι 3 * ι e4Index) from e4_mul_anticomm 3]
          simp [null]

private theorem mul_volume_plane2 :
    spatialVolume * (ι e4Index * ι 1 * ι 2) = null 3 := by
  simpa [spatialVolume, plane12_blade] using mul_volume_blade12

private theorem mul_volume_plane0 :
    (ι 1 * ι 2 * ι 3) * (ι e4Index * ι 2 * ι 3) = null 1 := by
  have h34 : ι 3 * ι e4Index = -(ι e4Index * ι 3) := e4_inner_anticomm 3
  have h32 : ι 3 * ι 2 = -(ι 2 * ι 3) := e_mul_anticomm (by decide)
  have h24 : ι 2 * ι e4Index = -(ι e4Index * ι 2) := e4_inner_anticomm 2
  calc
    (ι 1 * ι 2 * ι 3) * (ι e4Index * ι 2 * ι 3)
        = ι 1 * ι 2 * (ι 3 * ι e4Index) * ι 2 * ι 3 := by simp [mul_assoc]
      _ = ι 1 * ι 2 * (-(ι e4Index * ι 3)) * ι 2 * ι 3 := by rw [h34]
      _ = -(ι 1 * ι 2 * ι e4Index * (ι 3 * ι 2) * ι 3) := by simp [mul_neg, mul_assoc]
      _ = -(ι 1 * ι 2 * ι e4Index * (-(ι 2 * ι 3)) * ι 3) := by rw [h32]
      _ = ι 1 * ι 2 * (ι e4Index * ι 2) * (ι 3 * ι 3) := by simp [mul_neg, mul_assoc]
      _ = ι 1 * (ι 2 * ι e4Index) * ι 2 := by simp [e3_sq, mul_assoc]
      _ = ι 1 * (-(ι e4Index * ι 2)) * ι 2 := by rw [h24]
      _ = -(ι 1 * ι e4Index * (ι 2 * ι 2)) := by simp [mul_neg, mul_assoc]
      _ = -(ι 1 * ι e4Index) := by simp [e2_sq]
      _ = null 1 := by
          rw [← show ι e4Index * ι 1 = -(ι 1 * ι e4Index) from e4_mul_anticomm 1]
          simp [null]

private theorem mul_volume_plane1 :
    (ι 1 * ι 2 * ι 3) * (ι e4Index * ι 3 * ι 1) = null 2 := by
  have h34 : ι 3 * ι e4Index = -(ι e4Index * ι 3) := e4_inner_anticomm 3
  have h24 : ι 2 * ι e4Index = -(ι e4Index * ι 2) := e4_inner_anticomm 2
  have h21 : ι 2 * ι 1 = -(ι 1 * ι 2) := e_mul_anticomm (by decide)
  have h41 : ι e4Index * ι 1 = -(ι 1 * ι e4Index) := (e4_mul_anticomm 1)
  calc
    (ι 1 * ι 2 * ι 3) * (ι e4Index * ι 3 * ι 1)
        = ι 1 * ι 2 * (ι 3 * ι e4Index) * ι 3 * ι 1 := by simp [mul_assoc]
      _ = ι 1 * ι 2 * (-(ι e4Index * ι 3)) * ι 3 * ι 1 := by rw [h34]
      _ = -(ι 1 * ι 2 * ι e4Index * (ι 3 * ι 3) * ι 1) := by simp [mul_neg, mul_assoc]
      _ = -(ι 1 * (ι 2 * ι e4Index) * ι 1) := by simp [e3_sq, mul_assoc]
      _ = -(ι 1 * (-(ι e4Index * ι 2)) * ι 1) := by rw [h24]
      _ = ι 1 * ι e4Index * (ι 2 * ι 1) := by simp [mul_neg, mul_assoc]
      _ = ι 1 * ι e4Index * (-(ι 1 * ι 2)) := by rw [h21]
      _ = -(ι 1 * (ι e4Index * ι 1) * ι 2) := by simp [mul_neg, mul_assoc]
      _ = -(ι 1 * (-(ι 1 * ι e4Index)) * ι 2) := by rw [h41]
      _ = (ι 1 * ι 1) * ι e4Index * ι 2 := by simp [mul_neg, mul_assoc]
      _ = ι e4Index * ι 2 := by simp [e1_sq]
      _ = null 2 := by simp [null]

/-! ### Products with the dual of the normal -/

private theorem mul_plane2_dual :
    (ι e4Index * ι 1 * ι 2) * (ι 0 * ι 2 * ι 1) = null 0 := by
  have h20 : ι 2 * ι 0 = -(ι 0 * ι 2) := e_mul_anticomm (by decide)
  have h10 : ι 1 * ι 0 = -(ι 0 * ι 1) := e_mul_anticomm (by decide)
  calc
    (ι e4Index * ι 1 * ι 2) * (ι 0 * ι 2 * ι 1)
        = ι e4Index * ι 1 * (ι 2 * ι 0) * ι 2 * ι 1 := by simp [mul_assoc]
      _ = ι e4Index * ι 1 * (-(ι 0 * ι 2)) * ι 2 * ι 1 := by rw [h20]
      _ = -(ι e4Index * (ι 1 * ι 0) * (ι 2 * ι 2) * ι 1) := by simp [mul_neg, mul_assoc]
      _ = -(ι e4Index * (ι 1 * ι 0) * ι 1) := by simp [e2_sq]
      _ = -(ι e4Index * (-(ι 0 * ι 1)) * ι 1) := by rw [h10]
      _ = ι e4Index * ι 0 * (ι 1 * ι 1) := by simp [mul_neg, mul_assoc]
      _ = null 0 := by simp [e1_sq, null]

private theorem mul_dual_plane2 :
    (ι 0 * ι 2 * ι 1) * (ι e4Index * ι 1 * ι 2) = -null 0 := by
  have h14 : ι 1 * ι e4Index = -(ι e4Index * ι 1) := e4_inner_anticomm 1
  have h24 : ι 2 * ι e4Index = -(ι e4Index * ι 2) := e4_inner_anticomm 2
  calc
    (ι 0 * ι 2 * ι 1) * (ι e4Index * ι 1 * ι 2)
        = ι 0 * ι 2 * (ι 1 * ι e4Index) * ι 1 * ι 2 := by simp [mul_assoc]
      _ = ι 0 * ι 2 * (-(ι e4Index * ι 1)) * ι 1 * ι 2 := by rw [h14]
      _ = -(ι 0 * (ι 2 * ι e4Index) * (ι 1 * ι 1) * ι 2) := by simp [mul_neg, mul_assoc]
      _ = -(ι 0 * (ι 2 * ι e4Index) * ι 2) := by simp [e1_sq]
      _ = -(ι 0 * (-(ι e4Index * ι 2)) * ι 2) := by rw [h24]
      _ = ι 0 * ι e4Index * (ι 2 * ι 2) := by simp [mul_neg, mul_assoc]
      _ = ι 0 * ι e4Index := by simp [e2_sq]
      _ = -null 0 := (e4_inner_anticomm 0)

private theorem mul_plane0_dual :
    (ι e4Index * ι 2 * ι 3) * (ι 0 * ι 3 * ι 2) = null 0 := by
  have h30 : ι 3 * ι 0 = -(ι 0 * ι 3) := e_mul_anticomm (by decide)
  have h20 : ι 2 * ι 0 = -(ι 0 * ι 2) := e_mul_anticomm (by decide)
  calc
    (ι e4Index * ι 2 * ι 3) * (ι 0 * ι 3 * ι 2)
        = ι e4Index * ι 2 * (ι 3 * ι 0) * ι 3 * ι 2 := by simp [mul_assoc]
      _ = ι e4Index * ι 2 * (-(ι 0 * ι 3)) * ι 3 * ι 2 := by rw [h30]
      _ = -(ι e4Index * (ι 2 * ι 0) * (ι 3 * ι 3) * ι 2) := by simp [mul_neg, mul_assoc]
      _ = -(ι e4Index * (ι 2 * ι 0) * ι 2) := by simp [e3_sq]
      _ = -(ι e4Index * (-(ι 0 * ι 2)) * ι 2) := by rw [h20]
      _ = ι e4Index * ι 0 * (ι 2 * ι 2) := by simp [mul_neg, mul_assoc]
      _ = null 0 := by simp [e2_sq, null]

private theorem mul_dual_plane0 :
    (ι 0 * ι 3 * ι 2) * (ι e4Index * ι 2 * ι 3) = -null 0 := by
  have h24 : ι 2 * ι e4Index = -(ι e4Index * ι 2) := e4_inner_anticomm 2
  have h34 : ι 3 * ι e4Index = -(ι e4Index * ι 3) := e4_inner_anticomm 3
  calc
    (ι 0 * ι 3 * ι 2) * (ι e4Index * ι 2 * ι 3)
        = ι 0 * ι 3 * (ι 2 * ι e4Index) * ι 2 * ι 3 := by simp [mul_assoc]
      _ = ι 0 * ι 3 * (-(ι e4Index * ι 2)) * ι 2 * ι 3 := by rw [h24]
      _ = -(ι 0 * (ι 3 * ι e4Index) * (ι 2 * ι 2) * ι 3) := by simp [mul_neg, mul_assoc]
      _ = -(ι 0 * (ι 3 * ι e4Index) * ι 3) := by simp [e2_sq]
      _ = -(ι 0 * (-(ι e4Index * ι 3)) * ι 3) := by rw [h34]
      _ = ι 0 * ι e4Index * (ι 3 * ι 3) := by simp [mul_neg, mul_assoc]
      _ = ι 0 * ι e4Index := by simp [e3_sq]
      _ = -null 0 := e4_inner_anticomm 0

private theorem mul_plane1_dual :
    (ι e4Index * ι 3 * ι 1) * (ι 0 * ι 1 * ι 3) = null 0 := by
  have h10 : ι 1 * ι 0 = -(ι 0 * ι 1) := e_mul_anticomm (by decide)
  have h30 : ι 3 * ι 0 = -(ι 0 * ι 3) := e_mul_anticomm (by decide)
  calc
    (ι e4Index * ι 3 * ι 1) * (ι 0 * ι 1 * ι 3)
        = ι e4Index * ι 3 * (ι 1 * ι 0) * ι 1 * ι 3 := by simp [mul_assoc]
      _ = ι e4Index * ι 3 * (-(ι 0 * ι 1)) * ι 1 * ι 3 := by rw [h10]
      _ = -(ι e4Index * (ι 3 * ι 0) * (ι 1 * ι 1) * ι 3) := by simp [mul_neg, mul_assoc]
      _ = -(ι e4Index * (ι 3 * ι 0) * ι 3) := by simp [e1_sq]
      _ = -(ι e4Index * (-(ι 0 * ι 3)) * ι 3) := by rw [h30]
      _ = ι e4Index * ι 0 * (ι 3 * ι 3) := by simp [mul_neg, mul_assoc]
      _ = null 0 := by simp [e3_sq, null]

private theorem mul_dual_plane1 :
    (ι 0 * ι 1 * ι 3) * (ι e4Index * ι 3 * ι 1) = -null 0 := by
  have h34 : ι 3 * ι e4Index = -(ι e4Index * ι 3) := e4_inner_anticomm 3
  have h14 : ι 1 * ι e4Index = -(ι e4Index * ι 1) := e4_inner_anticomm 1
  calc
    (ι 0 * ι 1 * ι 3) * (ι e4Index * ι 3 * ι 1)
        = ι 0 * ι 1 * (ι 3 * ι e4Index) * ι 3 * ι 1 := by simp [mul_assoc]
      _ = ι 0 * ι 1 * (-(ι e4Index * ι 3)) * ι 3 * ι 1 := by rw [h34]
      _ = -(ι 0 * (ι 1 * ι e4Index) * (ι 3 * ι 3) * ι 1) := by simp [mul_neg, mul_assoc]
      _ = -(ι 0 * (ι 1 * ι e4Index) * ι 1) := by simp [e3_sq]
      _ = -(ι 0 * (-(ι e4Index * ι 1)) * ι 1) := by rw [h14]
      _ = ι 0 * ι e4Index * (ι 1 * ι 1) := by simp [mul_neg, mul_assoc]
      _ = ι 0 * ι e4Index := by simp [e1_sq]
      _ = -null 0 := e4_inner_anticomm 0

/-! ### The in-plane dual has vanishing bracket -/

private theorem sort_e4301 :
    ι e4Index * ι 3 * ι 0 * ι 1 = -(ι 0 * ι 1 * ι 3 * ι e4Index) := by
  have h43 : ι e4Index * ι 3 = -(ι 3 * ι e4Index) := e4_mul_anticomm 3
  have h40 : ι e4Index * ι 0 = -(ι 0 * ι e4Index) := e4_mul_anticomm 0
  have h41 : ι e4Index * ι 1 = -(ι 1 * ι e4Index) := e4_mul_anticomm 1
  have h30 : ι 3 * ι 0 = -(ι 0 * ι 3) := e_mul_anticomm (by decide)
  have h31 : ι 3 * ι 1 = -(ι 1 * ι 3) := e_mul_anticomm (by decide)
  have h01 : ι 0 * ι 1 = -(ι 1 * ι 0) := e_mul_anticomm (by decide)
  calc
    ι e4Index * ι 3 * ι 0 * ι 1
        = -(ι 3 * ι e4Index) * ι 0 * ι 1 := by rw [h43]
      _ = -(ι 3 * (ι e4Index * ι 0) * ι 1) := by simp [mul_assoc]
      _ = -(ι 3 * -(ι 0 * ι e4Index) * ι 1) := by rw [h40]
      _ = ι 3 * ι 0 * (ι e4Index * ι 1) := by simp [mul_neg, mul_assoc]
      _ = ι 3 * ι 0 * -(ι 1 * ι e4Index) := by rw [h41]
      _ = -(ι 3 * (ι 0 * ι 1) * ι e4Index) := by simp [mul_neg, mul_assoc]
      _ = -(ι 3 * -(ι 1 * ι 0) * ι e4Index) := by rw [h01]
      _ = ι 3 * ι 1 * ι 0 * ι e4Index := by simp [mul_neg, mul_assoc]
      _ = -(ι 1 * ι 3) * ι 0 * ι e4Index := by rw [h31]
      _ = -(ι 1 * (ι 3 * ι 0) * ι e4Index) := by simp [mul_assoc]
      _ = -(ι 1 * -(ι 0 * ι 3) * ι e4Index) := by rw [h30]
      _ = ι 1 * ι 0 * ι 3 * ι e4Index := by simp [mul_neg, mul_assoc]
      _ = -(ι 0 * ι 1) * ι 3 * ι e4Index := by
          rw [show ι 1 * ι 0 = -(ι 0 * ι 1) from e_mul_anticomm (by decide)]
      _ = -(ι 0 * ι 1 * ι 3 * ι e4Index) := by simp [neg_mul, mul_assoc]


private theorem mul_plane2_inPlane :
    (ι e4Index * ι 1 * ι 2) * (ι 0 * ι 3 * ι 2) = ι 0 * ι 1 * ι 3 * ι e4Index := by
  have h20 : ι 2 * ι 0 = -(ι 0 * ι 2) := e_mul_anticomm (by decide)
  have h23 : ι 2 * ι 3 = -(ι 3 * ι 2) := e_mul_anticomm (by decide)
  have h10 : ι 1 * ι 0 = -(ι 0 * ι 1) := e_mul_anticomm (by decide)
  have h13 : ι 1 * ι 3 = -(ι 3 * ι 1) := e_mul_anticomm (by decide)
  have h03 : ι 0 * ι 3 = -(ι 3 * ι 0) := e_mul_anticomm (by decide)
  calc
    (ι e4Index * ι 1 * ι 2) * (ι 0 * ι 3 * ι 2)
        = ι e4Index * ι 1 * (ι 2 * ι 0) * ι 3 * ι 2 := by simp [mul_assoc]
      _ = ι e4Index * ι 1 * (-(ι 0 * ι 2)) * ι 3 * ι 2 := by rw [h20]
      _ = -(ι e4Index * ι 1 * ι 0 * (ι 2 * ι 3) * ι 2) := by simp [mul_neg, mul_assoc]
      _ = -(ι e4Index * ι 1 * ι 0 * (-(ι 3 * ι 2)) * ι 2) := by rw [h23]
      _ = ι e4Index * ι 1 * ι 0 * ι 3 * (ι 2 * ι 2) := by simp [mul_neg, mul_assoc]
      _ = ι e4Index * (ι 1 * ι 0) * ι 3 := by simp [e2_sq, mul_assoc]
      _ = ι e4Index * (-(ι 0 * ι 1)) * ι 3 := by rw [h10]
      _ = -(ι e4Index * ι 0 * (ι 1 * ι 3)) := by simp [mul_neg, mul_assoc]
      _ = -(ι e4Index * ι 0 * -(ι 3 * ι 1)) := by rw [h13]
      _ = ι e4Index * (ι 0 * ι 3) * ι 1 := by simp [mul_neg, mul_assoc]
      _ = ι e4Index * (-(ι 3 * ι 0)) * ι 1 := by rw [h03]
      _ = -((ι e4Index * ι 3) * ι 0 * ι 1) := by simp [mul_neg, mul_assoc]
      _ = -(ι e4Index * ι 3 * ι 0 * ι 1) := by simp [mul_assoc]
      _ = ι 0 * ι 1 * ι 3 * ι e4Index := by rw [sort_e4301, neg_neg]

private theorem mul_inPlane_plane2 :
    (ι 0 * ι 3 * ι 2) * (ι e4Index * ι 1 * ι 2) = ι 0 * ι 1 * ι 3 * ι e4Index := by
  have h24 : ι 2 * ι e4Index = -(ι e4Index * ι 2) := e4_inner_anticomm 2
  have h21 : ι 2 * ι 1 = -(ι 1 * ι 2) := e_mul_anticomm (by decide)
  have h34 : ι 3 * ι e4Index = -(ι e4Index * ι 3) := e4_inner_anticomm 3
  have h04 : ι 0 * ι e4Index = -(ι e4Index * ι 0) := e4_inner_anticomm 0
  have h03 : ι 0 * ι 3 = -(ι 3 * ι 0) := e_mul_anticomm (by decide)
  calc
    (ι 0 * ι 3 * ι 2) * (ι e4Index * ι 1 * ι 2)
        = ι 0 * ι 3 * (ι 2 * ι e4Index) * ι 1 * ι 2 := by simp [mul_assoc]
      _ = ι 0 * ι 3 * (-(ι e4Index * ι 2)) * ι 1 * ι 2 := by rw [h24]
      _ = -(ι 0 * ι 3 * ι e4Index * (ι 2 * ι 1) * ι 2) := by simp [mul_neg, mul_assoc]
      _ = -(ι 0 * ι 3 * ι e4Index * (-(ι 1 * ι 2)) * ι 2) := by rw [h21]
      _ = ι 0 * ι 3 * ι e4Index * ι 1 * (ι 2 * ι 2) := by simp [mul_neg, mul_assoc]
      _ = ι 0 * (ι 3 * ι e4Index) * ι 1 := by simp [e2_sq, mul_assoc]
      _ = ι 0 * (-(ι e4Index * ι 3)) * ι 1 := by rw [h34]
      _ = -(ι 0 * ι e4Index * ι 3 * ι 1) := by simp [mul_neg, mul_assoc]
      _ = -(-(ι e4Index * ι 0) * ι 3 * ι 1) := by rw [h04]
      _ = ι e4Index * (ι 0 * ι 3) * ι 1 := by simp [mul_assoc]
      _ = ι e4Index * (-(ι 3 * ι 0)) * ι 1 := by rw [h03]
      _ = -(ι e4Index * ι 3 * ι 0 * ι 1) := by simp [mul_neg, mul_assoc]
      _ = ι 0 * ι 1 * ι 3 * ι e4Index := by rw [sort_e4301, neg_neg]

/-! ### The three coordinate planes -/

theorem idealPlane_mul_volume (a : Fin 3) :
    idealPlane a * spatialVolume = -null (Fin.succ a) := by
  fin_cases a
  · simpa [idealPlane, spatialVolume] using mul_plane0_volume
  · simpa [idealPlane, spatialVolume] using mul_plane1_volume
  · simpa [idealPlane, spatialVolume] using mul_plane2_volume

theorem volume_mul_idealPlane (a : Fin 3) :
    spatialVolume * idealPlane a = null (Fin.succ a) := by
  fin_cases a
  · simpa [idealPlane, spatialVolume] using mul_volume_plane0
  · simpa [idealPlane, spatialVolume] using mul_volume_plane1
  · simpa [idealPlane, spatialVolume] using mul_volume_plane2

theorem idealPlane_mul_dualNormal (a : Fin 3) :
    idealPlane a * dualNormal a = null 0 := by
  fin_cases a
  · simpa [idealPlane, dualNormal] using mul_plane0_dual
  · simpa [idealPlane, dualNormal] using mul_plane1_dual
  · simpa [idealPlane, dualNormal] using mul_plane2_dual

theorem dualNormal_mul_idealPlane (a : Fin 3) :
    dualNormal a * idealPlane a = -null 0 := by
  fin_cases a
  · simpa [idealPlane, dualNormal] using mul_dual_plane0
  · simpa [idealPlane, dualNormal] using mul_dual_plane1
  · simpa [idealPlane, dualNormal] using mul_dual_plane2

/-- `Πᵢⱼ ∨̲ k` is not yet halved: the commutator is `-2 Nₙ`. -/
theorem commutator_ideal_volume (a : Fin 3) :
    commutator (idealPlane a) spatialVolume = (-2 : ℝ) • null (Fin.succ a) := by
  rw [Generators.commutator, idealPlane_mul_volume, volume_mul_idealPlane]
  module

theorem sym_ideal_volume (a : Fin 3) :
    idealPlane a * spatialVolume + spatialVolume * idealPlane a = 0 := by
  rw [idealPlane_mul_volume, volume_mul_idealPlane]
  module

theorem vee_ideal_volume (a : Fin 3) :
    (1 / 2 : ℝ) • commutator (idealPlane a) spatialVolume = -null (Fin.succ a) := by
  rw [commutator_ideal_volume, smul_smul]
  norm_num

theorem commutator_ideal_dualNormal (a : Fin 3) :
    commutator (idealPlane a) (dualNormal a) = (2 : ℝ) • null 0 := by
  rw [Generators.commutator, idealPlane_mul_dualNormal, dualNormal_mul_idealPlane,
    sub_neg_eq_add]
  module

theorem sym_ideal_dualNormal (a : Fin 3) :
    idealPlane a * dualNormal a + dualNormal a * idealPlane a = 0 := by
  rw [idealPlane_mul_dualNormal, dualNormal_mul_idealPlane]
  module

theorem vee_ideal_dualNormal (a : Fin 3) :
    (1 / 2 : ℝ) • commutator (idealPlane a) (dualNormal a) = null 0 := by
  rw [commutator_ideal_dualNormal, smul_smul]
  norm_num

theorem blade12_eq_idealPlane :
    ι 1 * ι 2 * ι e4Index = idealPlane 2 := by
  simpa [idealPlane] using plane12_blade

theorem vee_volume_blade12 :
    (1 / 2 : ℝ) • commutator spatialVolume (ι 1 * ι 2 * ι e4Index) = null 3 := by
  have hmul : (ι 1 * ι 2 * ι e4Index) * (ι 1 * ι 2 * ι 3) = -null 3 := by
    simpa [spatialVolume, plane12_blade] using mul_plane2_volume
  rw [Generators.commutator, spatialVolume, mul_volume_blade12, hmul, sub_neg_eq_add,
    ← two_smul ℝ, smul_smul]
  norm_num

theorem sym_volume_blade12 :
    spatialVolume * (ι 1 * ι 2 * ι e4Index) +
      (ι 1 * ι 2 * ι e4Index) * spatialVolume = 0 := by
  have hmul : (ι 1 * ι 2 * ι e4Index) * (ι 1 * ι 2 * ι 3) = -null 3 := by
    simpa [spatialVolume, plane12_blade] using mul_plane2_volume
  rw [spatialVolume, mul_volume_blade12, hmul]
  module

theorem mul_plane12_inPlane :
    idealPlane 2 * dualNormal 0 = ι 0 * ι 1 * ι 3 * ι e4Index := by
  simpa [idealPlane, dualNormal] using mul_plane2_inPlane

theorem mul_inPlane_plane12 :
    dualNormal 0 * idealPlane 2 = ι 0 * ι 1 * ι 3 * ι e4Index := by
  simpa [idealPlane, dualNormal] using mul_inPlane_plane2

theorem commutator_plane12_inPlane :
    commutator (idealPlane 2) (dualNormal 0) = 0 := by
  rw [Generators.commutator, mul_plane12_inPlane, mul_inPlane_plane12, sub_self]

theorem sym_plane12_inPlane :
    idealPlane 2 * dualNormal 0 + dualNormal 0 * idealPlane 2 =
      (2 : ℝ) • (ι 0 * ι 1 * ι 3 * ι e4Index) := by
  rw [mul_plane12_inPlane, mul_inPlane_plane12, two_smul]

/-! ### The translation is the translational half of a motor -/

/-- Pure shift: torsion zero, one translational coefficient. -/
def pureShift (μ : Fin 4) (c : ℝ) : OmegaParams where
  torsion := ⟨fun _ => 0, fun _ => 0⟩
  trans := ⟨Pi.single μ c⟩

theorem omegaTrans_single (μ : Fin 4) (c : ℝ) :
    omegaTrans ⟨Pi.single μ c⟩ = (c / 2) • null μ := by
  fin_cases μ <;>
    simp [omegaTrans, Fin.sum_univ_four, Pi.single, null]

theorem omegaBiv_pureShift (μ : Fin 4) (c : ℝ) :
    omegaBiv (pureShift μ c) = (c / 2) • null μ := by
  simp [omegaBiv, pureShift, omegaTorsion, omegaTrans_single]

theorem vee_ideal_volume_eq_biv (a : Fin 3) :
    (1 / 2 : ℝ) • commutator (idealPlane a) spatialVolume =
      omegaBiv (pureShift (Fin.succ a) (-2)) := by
  rw [vee_ideal_volume, omegaBiv_pureShift]
  have : (-2 : ℝ) / 2 = -1 := by norm_num
  rw [this, neg_one_smul]

theorem vee_ideal_dualNormal_eq_biv (a : Fin 3) :
    (1 / 2 : ℝ) • commutator (idealPlane a) (dualNormal a) =
      omegaBiv (pureShift 0 2) := by
  rw [vee_ideal_dualNormal, omegaBiv_pureShift]
  have : (2 : ℝ) / 2 = 1 := by norm_num
  rw [this, one_smul]

theorem vee_volume_blade12_eq_biv :
    (1 / 2 : ℝ) • commutator spatialVolume (ι 1 * ι 2 * ι e4Index) =
      omegaBiv (pureShift 3 2) := by
  rw [vee_volume_blade12, omegaBiv_pureShift]
  have : (2 : ℝ) / 2 = 1 := by norm_num
  rw [this, one_smul]

/-! ### A plane rotated off the axes -/

/-- `Π(n) = n₁ Π₂₃ + n₂ Π₃₁ + n₃ Π₁₂`. -/
noncomputable def idealPlaneOf (n : Fin 3 → ℝ) : PGA :=
  n 0 • idealPlane 0 + n 1 • idealPlane 1 + n 2 • idealPlane 2

/-- Translation `n₁ N₁ + n₂ N₂ + n₃ N₃`. -/
noncomputable def spatialTranslation (n : Fin 3 → ℝ) : PGA :=
  n 0 • null 1 + n 1 • null 2 + n 2 • null 3

/-- Dual trivector `n₁ jI + n₂ jJ + n₃ jK`. -/
noncomputable def dualOf (n : Fin 3 → ℝ) : PGA :=
  n 0 • dualNormal 0 + n 1 • dualNormal 1 + n 2 • dualNormal 2

/-- Squared Euclidean length of a spatial vector. -/
def spatialNormSq (n : Fin 3 → ℝ) : ℝ :=
  n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2

/-- Pure spatial shift `λ⁰ = 0`, `λ^{a+1} = -2 nₐ`. -/
def pureSpatialShift (n : Fin 3 → ℝ) : OmegaParams where
  torsion := ⟨fun _ => 0, fun _ => 0⟩
  trans := ⟨fun
    | 0 => 0
    | 1 => -2 * n 0
    | 2 => -2 * n 1
    | 3 => -2 * n 2⟩

theorem commutator_idealPlaneOf_volume (n : Fin 3 → ℝ) :
    commutator (idealPlaneOf n) spatialVolume = (-2 : ℝ) • spatialTranslation n := by
  rw [idealPlaneOf, spatialTranslation]
  simp only [commutator_add_left, commutator_smul_left, commutator_ideal_volume, smul_smul]
  have hmul (c : ℝ) : c * (-2) = (-2) * c := by ring
  simp only [hmul, ← smul_smul, smul_add]
  have s0 : Fin.succ (0 : Fin 3) = 1 := rfl
  have s1 : Fin.succ (1 : Fin 3) = 2 := rfl
  have s2 : Fin.succ (2 : Fin 3) = 3 := rfl
  simp only [s0, s1, s2]

theorem sym_idealPlaneOf_volume (n : Fin 3 → ℝ) :
    idealPlaneOf n * spatialVolume + spatialVolume * idealPlaneOf n = 0 := by
  rw [idealPlaneOf]
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm]
  have regroup :
      n 0 • (idealPlane 0 * spatialVolume) + n 1 • (idealPlane 1 * spatialVolume) +
          n 2 • (idealPlane 2 * spatialVolume) +
          (n 0 • (spatialVolume * idealPlane 0) + n 1 • (spatialVolume * idealPlane 1) +
            n 2 • (spatialVolume * idealPlane 2)) =
        n 0 • (idealPlane 0 * spatialVolume + spatialVolume * idealPlane 0) +
          n 1 • (idealPlane 1 * spatialVolume + spatialVolume * idealPlane 1) +
          n 2 • (idealPlane 2 * spatialVolume + spatialVolume * idealPlane 2) := by
    module
  rw [regroup, sym_ideal_volume, sym_ideal_volume, sym_ideal_volume]
  module

theorem vee_idealPlaneOf_volume (n : Fin 3 → ℝ) :
    (1 / 2 : ℝ) • commutator (idealPlaneOf n) spatialVolume = -spatialTranslation n := by
  rw [commutator_idealPlaneOf_volume, smul_smul]
  have : (1 / 2 : ℝ) * (-2) = -1 := by norm_num
  rw [this, neg_one_smul]

theorem omegaTrans_pureSpatialShift (n : Fin 3 → ℝ) :
    omegaTrans (pureSpatialShift n).trans = -spatialTranslation n := by
  rw [omegaTrans, Fin.sum_univ_four]
  have h0 : (pureSpatialShift n).trans.lambda 0 = 0 := rfl
  have h1 : (pureSpatialShift n).trans.lambda 1 = -2 * n 0 := rfl
  have h2 : (pureSpatialShift n).trans.lambda 2 = -2 * n 1 := rfl
  have h3 : (pureSpatialShift n).trans.lambda 3 = -2 * n 2 := rfl
  rw [h0, h1, h2, h3, spatialTranslation]
  have hdiv (c : ℝ) : (-2 * c) / 2 = -c := by ring
  simp only [hdiv, zero_div, zero_smul, neg_smul]
  module

theorem omegaTorsion_zeroParams :
    omegaTorsion ⟨fun _ => 0, fun _ => 0⟩ = 0 := by
  simp [omegaTorsion]

theorem vee_idealPlaneOf_volume_eq_biv (n : Fin 3 → ℝ) :
    (1 / 2 : ℝ) • commutator (idealPlaneOf n) spatialVolume =
      omegaBiv (pureSpatialShift n) := by
  rw [vee_idealPlaneOf_volume, omegaBiv]
  have ht : (pureSpatialShift n).torsion = ⟨fun _ => 0, fun _ => 0⟩ := rfl
  rw [ht, omegaTorsion_zeroParams, zero_add, omegaTrans_pureSpatialShift]

/-! ### Cycling the spatial axes -/

/-- `e₁ ↦ e₂`, `e₂ ↦ e₃`, `e₃ ↦ e₁`, with `e₀` and `e₄` fixed. -/
def cycleCoord : Fin 5 → Fin 5
  | 0 => 0
  | 1 => 2
  | 2 => 3
  | 3 => 1
  | 4 => 4

/-- Inverse permutation: component `j` of the image is component `cycleInv j`. -/
def cycleInv : Fin 5 → Fin 5
  | 0 => 0
  | 1 => 3
  | 2 => 1
  | 3 => 2
  | 4 => 4

def cycleSpatial (v : Vec5) : Vec5 :=
  fun i => v (cycleInv i)

noncomputable def cycleSpatialLm : Vec5 →ₗ[ℝ] Vec5 where
  toFun := cycleSpatial
  map_add' x y := by
    ext i
    simp [cycleSpatial, Pi.add_apply]
  map_smul' c x := by
    ext i
    simp [cycleSpatial, Pi.smul_apply]

theorem cycleSpatial_Q (v : Vec5) : Q311 (cycleSpatialLm v) = Q311 v := by
  simp only [Q311, QuadraticMap.weightedSumSquares_apply, cycleSpatialLm,
    LinearMap.coe_mk, AddHom.coe_mk, cycleSpatial]
  rw [Fin.sum_univ_five, Fin.sum_univ_five]
  simp only [w311, cycleInv]
  ring

noncomputable def cycleSpatialIsometry : Q311 →qᵢ Q311 where
  toLinearMap := cycleSpatialLm
  map_app' := cycleSpatial_Q

noncomputable def cycleAlg : PGA →ₐ[ℝ] PGA :=
  CliffordAlgebra.map cycleSpatialIsometry

theorem cycleSpatial_basis (i : Fin 5) :
    cycleSpatialLm (e5vec i) = e5vec (cycleCoord i) := by
  ext j
  fin_cases i <;> fin_cases j <;>
    simp [cycleSpatialLm, cycleSpatial, cycleInv, cycleCoord, e5vec]

theorem cycleAlg_ι (i : Fin 5) : cycleAlg (ι i) = ι (cycleCoord i) := by
  unfold cycleAlg ι
  rw [CliffordAlgebra.map_apply_ι]
  have hcoe : (cycleSpatialIsometry : Vec5 →ₗ[ℝ] Vec5) = cycleSpatialLm := rfl
  have happ : cycleSpatialIsometry (e5vec i) = cycleSpatialLm (e5vec i) :=
    congrArg (fun f : Vec5 →ₗ[ℝ] Vec5 => f (e5vec i)) hcoe
  rw [happ, cycleSpatial_basis]

theorem cycleAlg_mul3 (a b c : Fin 5) :
    cycleAlg (ι a * ι b * ι c) = ι (cycleCoord a) * ι (cycleCoord b) * ι (cycleCoord c) := by
  rw [map_mul, map_mul, cycleAlg_ι, cycleAlg_ι, cycleAlg_ι]

/-- `0 ↦ 1 ↦ 2 ↦ 0` on the three coordinate planes. -/
def cyclePlane : Fin 3 → Fin 3
  | 0 => 1
  | 1 => 2
  | 2 => 0

theorem cycleAlg_idealPlane (a : Fin 3) :
    cycleAlg (idealPlane a) = idealPlane (cyclePlane a) := by
  fin_cases a <;> simp only [idealPlane, cyclePlane] <;>
    rw [cycleAlg_mul3] <;> simp [cycleCoord, e4Index]

theorem cycleAlg_dualNormal (a : Fin 3) :
    cycleAlg (dualNormal a) = dualNormal (cyclePlane a) := by
  fin_cases a <;> simp only [dualNormal, cyclePlane] <;>
    rw [cycleAlg_mul3] <;> simp [cycleCoord]

theorem cycleAlg_commutator (x y : PGA) :
    cycleAlg (commutator x y) = commutator (cycleAlg x) (cycleAlg y) := by
  simp [Generators.commutator, map_sub, map_mul]

private theorem mul_plane2_dual1 :
    (ι e4Index * ι 1 * ι 2) * (ι 0 * ι 1 * ι 3) = ι 0 * ι 2 * ι 3 * ι e4Index := by
  have h20 : ι 2 * ι 0 = -(ι 0 * ι 2) := e_mul_anticomm (by decide)
  have h21 : ι 2 * ι 1 = -(ι 1 * ι 2) := e_mul_anticomm (by decide)
  have h01 : ι 0 * ι 1 = -(ι 1 * ι 0) := e_mul_anticomm (by decide)
  have h40 : ι e4Index * ι 0 = -(ι 0 * ι e4Index) := e4_mul_anticomm 0
  have h42 : ι e4Index * ι 2 = -(ι 2 * ι e4Index) := e4_mul_anticomm 2
  have h43 : ι e4Index * ι 3 = -(ι 3 * ι e4Index) := e4_mul_anticomm 3
  calc
    (ι e4Index * ι 1 * ι 2) * (ι 0 * ι 1 * ι 3)
        = ι e4Index * ι 1 * (ι 2 * ι 0) * ι 1 * ι 3 := by simp [mul_assoc]
      _ = ι e4Index * ι 1 * (-(ι 0 * ι 2)) * ι 1 * ι 3 := by rw [h20]
      _ = -(ι e4Index * ι 1 * ι 0 * (ι 2 * ι 1) * ι 3) := by simp [mul_neg, mul_assoc]
      _ = -(ι e4Index * ι 1 * ι 0 * (-(ι 1 * ι 2)) * ι 3) := by rw [h21]
      _ = ι e4Index * ι 1 * ι 0 * ι 1 * ι 2 * ι 3 := by simp [mul_neg, mul_assoc]
      _ = ι e4Index * ι 1 * (ι 0 * ι 1) * ι 2 * ι 3 := by simp [mul_assoc]
      _ = ι e4Index * ι 1 * (-(ι 1 * ι 0)) * ι 2 * ι 3 := by rw [h01]
      _ = -(ι e4Index * (ι 1 * ι 1) * ι 0 * ι 2 * ι 3) := by simp [mul_neg, mul_assoc]
      _ = -(ι e4Index * ι 0 * ι 2 * ι 3) := by simp [e1_sq]
      _ = -(-(ι 0 * ι e4Index) * ι 2 * ι 3) := by rw [h40]
      _ = ι 0 * ι e4Index * ι 2 * ι 3 := by simp [mul_assoc]
      _ = ι 0 * (ι e4Index * ι 2) * ι 3 := by simp [mul_assoc]
      _ = ι 0 * (-(ι 2 * ι e4Index)) * ι 3 := by rw [h42]
      _ = -(ι 0 * ι 2 * (ι e4Index * ι 3)) := by simp [mul_neg, mul_assoc]
      _ = -(ι 0 * ι 2 * -(ι 3 * ι e4Index)) := by rw [h43]
      _ = ι 0 * ι 2 * ι 3 * ι e4Index := by simp [mul_neg, mul_assoc]

private theorem mul_dual1_plane2 :
    (ι 0 * ι 1 * ι 3) * (ι e4Index * ι 1 * ι 2) = ι 0 * ι 2 * ι 3 * ι e4Index := by
  have h34 : ι 3 * ι e4Index = -(ι e4Index * ι 3) := e4_inner_anticomm 3
  have h31 : ι 3 * ι 1 = -(ι 1 * ι 3) := e_mul_anticomm (by decide)
  have h41 : ι e4Index * ι 1 = -(ι 1 * ι e4Index) := e4_mul_anticomm 1
  have h32 : ι 3 * ι 2 = -(ι 2 * ι 3) := e_mul_anticomm (by decide)
  have h42 : ι e4Index * ι 2 = -(ι 2 * ι e4Index) := e4_mul_anticomm 2
  have h43 : ι e4Index * ι 3 = -(ι 3 * ι e4Index) := e4_mul_anticomm 3
  calc
    (ι 0 * ι 1 * ι 3) * (ι e4Index * ι 1 * ι 2)
        = ι 0 * ι 1 * (ι 3 * ι e4Index) * ι 1 * ι 2 := by simp [mul_assoc]
      _ = ι 0 * ι 1 * (-(ι e4Index * ι 3)) * ι 1 * ι 2 := by rw [h34]
      _ = -(ι 0 * ι 1 * ι e4Index * (ι 3 * ι 1) * ι 2) := by simp [mul_neg, mul_assoc]
      _ = -(ι 0 * ι 1 * ι e4Index * (-(ι 1 * ι 3)) * ι 2) := by rw [h31]
      _ = ι 0 * ι 1 * ι e4Index * ι 1 * ι 3 * ι 2 := by simp [mul_neg, mul_assoc]
      _ = ι 0 * ι 1 * (ι e4Index * ι 1) * ι 3 * ι 2 := by simp [mul_assoc]
      _ = ι 0 * ι 1 * (-(ι 1 * ι e4Index)) * ι 3 * ι 2 := by rw [h41]
      _ = -(ι 0 * (ι 1 * ι 1) * ι e4Index * ι 3 * ι 2) := by simp [mul_neg, mul_assoc]
      _ = -(ι 0 * ι e4Index * ι 3 * ι 2) := by simp [e1_sq]
      _ = -(ι 0 * ι e4Index * (ι 3 * ι 2)) := by simp [mul_assoc]
      _ = -(ι 0 * ι e4Index * (-(ι 2 * ι 3))) := by rw [h32]
      _ = ι 0 * ι e4Index * ι 2 * ι 3 := by simp [mul_neg, mul_assoc]
      _ = ι 0 * (ι e4Index * ι 2) * ι 3 := by simp [mul_assoc]
      _ = ι 0 * (-(ι 2 * ι e4Index)) * ι 3 := by rw [h42]
      _ = -(ι 0 * ι 2 * (ι e4Index * ι 3)) := by simp [mul_neg, mul_assoc]
      _ = -(ι 0 * ι 2 * -(ι 3 * ι e4Index)) := by rw [h43]
      _ = ι 0 * ι 2 * ι 3 * ι e4Index := by simp [mul_neg, mul_assoc]

theorem commutator_plane2_dual1 :
    commutator (idealPlane 2) (dualNormal 1) = 0 := by
  rw [Generators.commutator, idealPlane, dualNormal, mul_plane2_dual1, mul_dual1_plane2, sub_self]

private theorem commutator_cycled {a b : Fin 3}
    (h : commutator (idealPlane a) (dualNormal b) = 0) :
    commutator (idealPlane (cyclePlane a)) (dualNormal (cyclePlane b)) = 0 := by
  have hmap := congrArg cycleAlg h
  rw [cycleAlg_commutator, cycleAlg_idealPlane, cycleAlg_dualNormal, map_zero] at hmap
  exact hmap

theorem commutator_ideal_dual_off {a b : Fin 3} (hab : a ≠ b) :
    commutator (idealPlane a) (dualNormal b) = 0 := by
  fin_cases a <;> fin_cases b
  · exact absurd rfl hab
  · exact commutator_cycled commutator_plane12_inPlane
  · exact commutator_cycled commutator_plane2_dual1
  · exact commutator_cycled (commutator_cycled commutator_plane2_dual1)
  · exact absurd rfl hab
  · exact commutator_cycled (commutator_cycled commutator_plane12_inPlane)
  · exact commutator_plane12_inPlane
  · exact commutator_plane2_dual1
  · exact absurd rfl hab

private theorem cycleAlg_mul4 (a b c d : Fin 5) :
    cycleAlg (ι a * ι b * ι c * ι d) =
      ι (cycleCoord a) * ι (cycleCoord b) * ι (cycleCoord c) * ι (cycleCoord d) := by
  have hassoc : ι a * ι b * ι c * ι d = (ι a * ι b * ι c) * ι d := by simp [mul_assoc]
  rw [hassoc, map_mul, cycleAlg_mul3, cycleAlg_ι, mul_assoc]

private theorem sort_e0314 :
    ι 0 * ι 3 * ι 1 * ι e4Index = -(ι 0 * ι 1 * ι 3 * ι e4Index) := by
  have h31 : ι 3 * ι 1 = -(ι 1 * ι 3) := e_mul_anticomm (by decide)
  calc
    ι 0 * ι 3 * ι 1 * ι e4Index
        = ι 0 * (ι 3 * ι 1) * ι e4Index := by simp [mul_assoc]
      _ = ι 0 * (-(ι 1 * ι 3)) * ι e4Index := by rw [h31]
      _ = -(ι 0 * ι 1 * ι 3 * ι e4Index) := by simp [mul_neg, mul_assoc]

private theorem sort_e0214 :
    ι 0 * ι 2 * ι 1 * ι e4Index = -(ι 0 * ι 1 * ι 2 * ι e4Index) := by
  have h21 : ι 2 * ι 1 = -(ι 1 * ι 2) := e_mul_anticomm (by decide)
  calc
    ι 0 * ι 2 * ι 1 * ι e4Index
        = ι 0 * (ι 2 * ι 1) * ι e4Index := by simp [mul_assoc]
      _ = ι 0 * (-(ι 1 * ι 2)) * ι e4Index := by rw [h21]
      _ = -(ι 0 * ι 1 * ι 2 * ι e4Index) := by simp [mul_neg, mul_assoc]

theorem mul_plane0_dual2_neg :
    idealPlane 0 * dualNormal 2 = -(idealPlane 2 * dualNormal 0) := by
  have hcyc := congrArg cycleAlg mul_plane2_dual1
  rw [map_mul, cycleAlg_mul3, cycleAlg_mul3, cycleAlg_mul4] at hcyc
  simp only [cycleCoord, e4Index] at hcyc
  have hform : idealPlane 0 * dualNormal 2 = ι 4 * ι 2 * ι 3 * (ι 0 * ι 2 * ι 1) := by
    simp [idealPlane, dualNormal, e4Index, mul_assoc]
  rw [hform, hcyc]
  rw [show (4 : Fin 5) = e4Index from rfl]
  rw [sort_e0314, mul_plane12_inPlane]

private theorem mul_antisym_cycled {a b : Fin 3}
    (h : idealPlane a * dualNormal b = -(idealPlane b * dualNormal a)) :
    idealPlane (cyclePlane a) * dualNormal (cyclePlane b) =
      -(idealPlane (cyclePlane b) * dualNormal (cyclePlane a)) := by
  have hmap := congrArg cycleAlg h
  rw [map_mul, map_neg, map_mul, cycleAlg_idealPlane, cycleAlg_dualNormal,
    cycleAlg_idealPlane, cycleAlg_dualNormal] at hmap
  exact hmap

theorem mul_plane0_dual1_neg :
    idealPlane 0 * dualNormal 1 = -(idealPlane 1 * dualNormal 0) := by
  have hLeft := congrArg cycleAlg mul_plane12_inPlane
  rw [map_mul, cycleAlg_idealPlane, cycleAlg_dualNormal, cycleAlg_mul4] at hLeft
  simp only [cyclePlane, cycleCoord, e4Index] at hLeft
  have hOnce := congrArg cycleAlg mul_plane2_dual1
  rw [map_mul, cycleAlg_mul3, cycleAlg_mul3, cycleAlg_mul4] at hOnce
  simp only [cycleCoord, e4Index] at hOnce
  have hTwice := congrArg cycleAlg hOnce
  rw [map_mul, cycleAlg_mul3, cycleAlg_mul3, cycleAlg_mul4] at hTwice
  simp only [cycleCoord] at hTwice
  rw [hLeft]
  rw [show (4 : Fin 5) = e4Index from rfl]
  rw [sort_e0214]
  have hform : idealPlane 1 * dualNormal 0 = ι 0 * ι 1 * ι 2 * ι e4Index := by
    simpa [idealPlane, dualNormal, e4Index, mul_assoc] using hTwice
  rw [hform]

theorem mul_cross_antisym {a b : Fin 3} (hab : a ≠ b) :
    idealPlane a * dualNormal b = -(idealPlane b * dualNormal a) := by
  fin_cases a <;> fin_cases b
  · exact absurd rfl hab
  · exact mul_plane0_dual1_neg
  · exact mul_plane0_dual2_neg
  · exact mul_antisym_cycled mul_plane0_dual2_neg
  · exact absurd rfl hab
  · exact mul_antisym_cycled mul_plane0_dual1_neg
  · have h := mul_plane0_dual2_neg
    simpa using (neg_eq_iff_eq_neg.mp h.symm)
  · exact mul_antisym_cycled (mul_antisym_cycled mul_plane0_dual2_neg)
  · exact absurd rfl hab

theorem sym_cross {a b : Fin 3} (hab : a ≠ b) :
    idealPlane a * dualNormal b + dualNormal b * idealPlane a +
        (idealPlane b * dualNormal a + dualNormal a * idealPlane b) = 0 := by
  have hcomm_ab : dualNormal b * idealPlane a = idealPlane a * dualNormal b := by
    have h := commutator_ideal_dual_off hab
    rw [Generators.commutator, sub_eq_zero] at h
    exact h.symm
  have hba : b ≠ a := hab.symm
  have hcomm_ba : dualNormal a * idealPlane b = idealPlane b * dualNormal a := by
    have h := commutator_ideal_dual_off hba
    rw [Generators.commutator, sub_eq_zero] at h
    exact h.symm
  rw [hcomm_ab, hcomm_ba, mul_cross_antisym hab]
  module

@[simp] private theorem mul_smul_smul (c d : ℝ) (x y : PGA) :
    (c • x) * (d • y) = (c * d) • (x * y) := by
  rw [smul_mul_assoc, mul_smul_comm, ← smul_smul]

theorem sym_idealPlaneOf_dualOf (n : Fin 3 → ℝ) :
    idealPlaneOf n * dualOf n + dualOf n * idealPlaneOf n = 0 := by
  rw [idealPlaneOf, dualOf]
  simp only [add_mul, mul_add, mul_smul_smul]
  have hdiag (a : Fin 3) :
      (n a * n a) • (idealPlane a * dualNormal a + dualNormal a * idealPlane a) = 0 := by
    rw [sym_ideal_dualNormal, smul_zero]
  have h01 := sym_cross (a := 0) (b := 1) (by decide)
  have h02 := sym_cross (a := 0) (b := 2) (by decide)
  have h12 := sym_cross (a := 1) (b := 2) (by decide)
  have pair01 :
      (n 0 * n 1) • (idealPlane 0 * dualNormal 1 + dualNormal 1 * idealPlane 0) +
          (n 1 * n 0) • (idealPlane 1 * dualNormal 0 + dualNormal 0 * idealPlane 1) = 0 := by
    rw [mul_comm (n 1) (n 0), ← smul_add, h01, smul_zero]
  have pair02 :
      (n 0 * n 2) • (idealPlane 0 * dualNormal 2 + dualNormal 2 * idealPlane 0) +
          (n 2 * n 0) • (idealPlane 2 * dualNormal 0 + dualNormal 0 * idealPlane 2) = 0 := by
    rw [mul_comm (n 2) (n 0), ← smul_add, h02, smul_zero]
  have pair12 :
      (n 1 * n 2) • (idealPlane 1 * dualNormal 2 + dualNormal 2 * idealPlane 1) +
          (n 2 * n 1) • (idealPlane 2 * dualNormal 1 + dualNormal 1 * idealPlane 2) = 0 := by
    rw [mul_comm (n 2) (n 1), ← smul_add, h12, smul_zero]
  have regroup :
      (n 0 * n 0) • (idealPlane 0 * dualNormal 0) + (n 1 * n 0) • (idealPlane 1 * dualNormal 0) +
            (n 2 * n 0) • (idealPlane 2 * dualNormal 0) +
          ((n 0 * n 1) • (idealPlane 0 * dualNormal 1) +
              (n 1 * n 1) • (idealPlane 1 * dualNormal 1) +
            (n 2 * n 1) • (idealPlane 2 * dualNormal 1)) +
        ((n 0 * n 2) • (idealPlane 0 * dualNormal 2) +
            (n 1 * n 2) • (idealPlane 1 * dualNormal 2) +
          (n 2 * n 2) • (idealPlane 2 * dualNormal 2)) +
      ((n 0 * n 0) • (dualNormal 0 * idealPlane 0) + (n 1 * n 0) • (dualNormal 1 * idealPlane 0) +
            (n 2 * n 0) • (dualNormal 2 * idealPlane 0) +
          ((n 0 * n 1) • (dualNormal 0 * idealPlane 1) +
              (n 1 * n 1) • (dualNormal 1 * idealPlane 1) +
            (n 2 * n 1) • (dualNormal 2 * idealPlane 1)) +
        ((n 0 * n 2) • (dualNormal 0 * idealPlane 2) +
            (n 1 * n 2) • (dualNormal 1 * idealPlane 2) +
          (n 2 * n 2) • (dualNormal 2 * idealPlane 2))) =
        (n 0 * n 0) • (idealPlane 0 * dualNormal 0 + dualNormal 0 * idealPlane 0) +
          (n 1 * n 1) • (idealPlane 1 * dualNormal 1 + dualNormal 1 * idealPlane 1) +
          (n 2 * n 2) • (idealPlane 2 * dualNormal 2 + dualNormal 2 * idealPlane 2) +
          ((n 0 * n 1) • (idealPlane 0 * dualNormal 1 + dualNormal 1 * idealPlane 0) +
            (n 1 * n 0) • (idealPlane 1 * dualNormal 0 + dualNormal 0 * idealPlane 1)) +
          ((n 0 * n 2) • (idealPlane 0 * dualNormal 2 + dualNormal 2 * idealPlane 0) +
            (n 2 * n 0) • (idealPlane 2 * dualNormal 0 + dualNormal 0 * idealPlane 2)) +
          ((n 1 * n 2) • (idealPlane 1 * dualNormal 2 + dualNormal 2 * idealPlane 1) +
            (n 2 * n 1) • (idealPlane 2 * dualNormal 1 + dualNormal 1 * idealPlane 2)) := by
    module
  rw [regroup, hdiag, hdiag, hdiag, pair01, pair02, pair12]
  module

theorem commutator_idealPlaneOf_dualOf (n : Fin 3 → ℝ) :
    commutator (idealPlaneOf n) (dualOf n) =
      (2 * spatialNormSq n) • null 0 := by
  rw [idealPlaneOf, dualOf, spatialNormSq]
  have e (c d : ℝ) (x y : PGA) :
      commutator (c • x) (d • y) = (c * d) • commutator x y := by
    rw [commutator_smul_left, commutator_smul_right, ← smul_smul]
  simp only [commutator_add_left, commutator_add_right, e]
  have hoff {a b : Fin 3} (hab : a ≠ b) :
      (n a * n b) • commutator (idealPlane a) (dualNormal b) = 0 := by
    rw [commutator_ideal_dual_off hab, smul_zero]
  simp only [commutator_ideal_dualNormal, hoff (a := 0) (b := 1) (by decide),
    hoff (a := 0) (b := 2) (by decide), hoff (a := 1) (b := 0) (by decide),
    hoff (a := 1) (b := 2) (by decide), hoff (a := 2) (b := 0) (by decide),
    hoff (a := 2) (b := 1) (by decide), add_zero, zero_add]
  module

theorem vee_idealPlaneOf_dualOf (n : Fin 3 → ℝ) :
    (1 / 2 : ℝ) • commutator (idealPlaneOf n) (dualOf n) =
      spatialNormSq n • null 0 := by
  rw [commutator_idealPlaneOf_dualOf, smul_smul]
  have : (1 / 2 : ℝ) * (2 * spatialNormSq n) = spatialNormSq n := by ring
  rw [this]

theorem vee_idealPlaneOf_dualOf_eq_biv (n : Fin 3 → ℝ) :
    (1 / 2 : ℝ) • commutator (idealPlaneOf n) (dualOf n) =
      omegaBiv (pureShift 0 (2 * spatialNormSq n)) := by
  rw [vee_idealPlaneOf_dualOf, omegaBiv_pureShift]
  have : (2 * spatialNormSq n) / 2 = spatialNormSq n := by ring
  rw [this]

/-! ### A plane displaced from the origin -/

/-- Spatial boost `∑ nₐ B⁺ₐ`. -/
noncomputable def spatialBoost (n : Fin 3 → ℝ) : PGA :=
  n 0 • hyperbolic 0 + n 1 • hyperbolic 1 + n 2 • hyperbolic 2

/-- `Π(n, δ) = Π(n) + δ k`. The coefficient `δ` displaces the normal off the origin. -/
noncomputable def displacedPlane (n : Fin 3 → ℝ) (δ : ℝ) : PGA :=
  idealPlaneOf n + δ • spatialVolume

/-- Boost parameters `αₐ = -2 δ nₐ`, together with the time shift `λ⁰ = 2 |n|²`. -/
def displacedMotor (n : Fin 3 → ℝ) (δ : ℝ) : OmegaParams where
  torsion := ⟨fun a => -2 * δ * n a, fun _ => 0⟩
  trans := ⟨Pi.single 0 (2 * spatialNormSq n)⟩

theorem spatialVolume_sq : spatialVolume * spatialVolume = (-1 : PGA) := by
  have h21 : ι 2 * ι 1 = -(ι 1 * ι 2) := e_mul_anticomm (by decide)
  have h31 : ι 3 * ι 1 = -(ι 1 * ι 3) := e_mul_anticomm (by decide)
  have h32 : ι 3 * ι 2 = -(ι 2 * ι 3) := e_mul_anticomm (by decide)
  rw [spatialVolume]
  calc
    (ι 1 * ι 2 * ι 3) * (ι 1 * ι 2 * ι 3)
        = ι 1 * ι 2 * (ι 3 * ι 1) * ι 2 * ι 3 := by simp [mul_assoc]
      _ = ι 1 * ι 2 * (-(ι 1 * ι 3)) * ι 2 * ι 3 := by rw [h31]
      _ = -(ι 1 * ι 2 * ι 1 * ι 3 * ι 2 * ι 3) := by simp [mul_neg, mul_assoc]
      _ = -(ι 1 * (ι 2 * ι 1) * ι 3 * ι 2 * ι 3) := by simp [mul_assoc]
      _ = -(ι 1 * (-(ι 1 * ι 2)) * ι 3 * ι 2 * ι 3) := by rw [h21]
      _ = ι 1 * ι 1 * ι 2 * ι 3 * ι 2 * ι 3 := by simp [mul_neg, mul_assoc]
      _ = ι 2 * (ι 3 * ι 2) * ι 3 := by simp [e1_sq, mul_assoc]
      _ = ι 2 * (-(ι 2 * ι 3)) * ι 3 := by rw [h32]
      _ = -(ι 2 * ι 2 * ι 3 * ι 3) := by simp [mul_neg, mul_assoc]
      _ = -1 := by simp [e2_sq, e3_sq]

private theorem volume_mul_dual0 :
    spatialVolume * dualNormal 0 = -hyperbolic 0 := by
  have h30 : ι 3 * ι 0 = -(ι 0 * ι 3) := e_mul_anticomm (by decide)
  have h20 : ι 2 * ι 0 = -(ι 0 * ι 2) := e_mul_anticomm (by decide)
  have h10 : ι 1 * ι 0 = -(ι 0 * ι 1) := e_mul_anticomm (by decide)
  rw [spatialVolume, dualNormal]
  calc
    (ι 1 * ι 2 * ι 3) * (ι 0 * ι 3 * ι 2)
        = ι 1 * ι 2 * (ι 3 * ι 0) * ι 3 * ι 2 := by simp [mul_assoc]
      _ = ι 1 * ι 2 * (-(ι 0 * ι 3)) * ι 3 * ι 2 := by rw [h30]
      _ = -(ι 1 * ι 2 * ι 0 * ι 3 * ι 3 * ι 2) := by simp [mul_neg, mul_assoc]
      _ = -(ι 1 * ι 2 * ι 0 * ι 2) := by simp [e3_sq, mul_assoc]
      _ = -(ι 1 * (ι 2 * ι 0) * ι 2) := by simp [mul_assoc]
      _ = -(ι 1 * (-(ι 0 * ι 2)) * ι 2) := by rw [h20]
      _ = ι 1 * ι 0 * ι 2 * ι 2 := by simp [mul_neg, mul_assoc]
      _ = ι 1 * ι 0 := by simp [e2_sq, mul_assoc]
      _ = -(ι 0 * ι 1) := by rw [h10]
      _ = -hyperbolic 0 := by simp [hyperbolic]

private theorem dual0_mul_volume :
    dualNormal 0 * spatialVolume = hyperbolic 0 := by
  have h21 : ι 2 * ι 1 = -(ι 1 * ι 2) := e_mul_anticomm (by decide)
  have h31 : ι 3 * ι 1 = -(ι 1 * ι 3) := e_mul_anticomm (by decide)
  rw [dualNormal, spatialVolume]
  calc
    (ι 0 * ι 3 * ι 2) * (ι 1 * ι 2 * ι 3)
        = ι 0 * ι 3 * (ι 2 * ι 1) * ι 2 * ι 3 := by simp [mul_assoc]
      _ = ι 0 * ι 3 * (-(ι 1 * ι 2)) * ι 2 * ι 3 := by rw [h21]
      _ = -(ι 0 * ι 3 * ι 1 * ι 2 * ι 2 * ι 3) := by simp [mul_neg, mul_assoc]
      _ = -(ι 0 * ι 3 * ι 1 * ι 3) := by simp [e2_sq, mul_assoc]
      _ = -(ι 0 * (ι 3 * ι 1) * ι 3) := by simp [mul_assoc]
      _ = -(ι 0 * (-(ι 1 * ι 3)) * ι 3) := by rw [h31]
      _ = ι 0 * ι 1 * ι 3 * ι 3 := by simp [mul_neg, mul_assoc]
      _ = ι 0 * ι 1 := by simp [e3_sq, mul_assoc]
      _ = hyperbolic 0 := by simp [hyperbolic]

theorem cycleAlg_spatialVolume : cycleAlg spatialVolume = spatialVolume := by
  have h31 : ι 3 * ι 1 = -(ι 1 * ι 3) := e_mul_anticomm (by decide)
  have h21 : ι 2 * ι 1 = -(ι 1 * ι 2) := e_mul_anticomm (by decide)
  rw [spatialVolume, cycleAlg_mul3]
  simp only [cycleCoord]
  calc
    ι 2 * ι 3 * ι 1 = ι 2 * (ι 3 * ι 1) := by simp [mul_assoc]
      _ = ι 2 * (-(ι 1 * ι 3)) := by rw [h31]
      _ = -(ι 2 * ι 1 * ι 3) := by simp [mul_neg, mul_assoc]
      _ = -((-(ι 1 * ι 2)) * ι 3) := by rw [h21]
      _ = ι 1 * ι 2 * ι 3 := by simp [mul_assoc]

theorem cycleAlg_hyperbolic (a : Fin 3) :
    cycleAlg (hyperbolic a) = hyperbolic (cyclePlane a) := by
  fin_cases a <;> simp [hyperbolic, cyclePlane, map_mul, cycleAlg_ι, cycleCoord]

theorem volume_mul_dualNormal (a : Fin 3) :
    spatialVolume * dualNormal a = -hyperbolic a := by
  have h0 := volume_mul_dual0
  fin_cases a
  · exact h0
  · have h := congrArg cycleAlg h0
    rw [map_mul, map_neg, cycleAlg_spatialVolume, cycleAlg_dualNormal, cycleAlg_hyperbolic] at h
    simpa [cyclePlane] using h
  · have h := congrArg (cycleAlg ∘ cycleAlg) h0
    rw [Function.comp_apply, Function.comp_apply, map_mul, map_neg, map_mul, map_neg,
      cycleAlg_spatialVolume, cycleAlg_dualNormal, cycleAlg_hyperbolic,
      cycleAlg_spatialVolume, cycleAlg_dualNormal, cycleAlg_hyperbolic] at h
    simpa [cyclePlane] using h

theorem dualNormal_mul_volume (a : Fin 3) :
    dualNormal a * spatialVolume = hyperbolic a := by
  have h0 := dual0_mul_volume
  fin_cases a
  · exact h0
  · have h := congrArg cycleAlg h0
    rw [map_mul, cycleAlg_spatialVolume, cycleAlg_dualNormal, cycleAlg_hyperbolic] at h
    simpa [cyclePlane] using h
  · have h := congrArg (cycleAlg ∘ cycleAlg) h0
    rw [Function.comp_apply, Function.comp_apply, map_mul, map_mul,
      cycleAlg_spatialVolume, cycleAlg_dualNormal, cycleAlg_hyperbolic,
      cycleAlg_spatialVolume, cycleAlg_dualNormal, cycleAlg_hyperbolic] at h
    simpa [cyclePlane] using h

theorem commutator_volume_dualNormal (a : Fin 3) :
    commutator spatialVolume (dualNormal a) = (-2 : ℝ) • hyperbolic a := by
  rw [Generators.commutator, volume_mul_dualNormal, dualNormal_mul_volume]
  module

theorem sym_volume_dualNormal (a : Fin 3) :
    spatialVolume * dualNormal a + dualNormal a * spatialVolume = 0 := by
  rw [volume_mul_dualNormal, dualNormal_mul_volume]
  module

theorem commutator_volume_dualOf (n : Fin 3 → ℝ) :
    commutator spatialVolume (dualOf n) = (-2 : ℝ) • spatialBoost n := by
  rw [dualOf, spatialBoost]
  simp only [commutator_add_right, commutator_smul_right, commutator_volume_dualNormal, smul_smul]
  have hmul (c : ℝ) : c * (-2) = (-2) * c := by ring
  simp only [hmul, ← smul_smul, smul_add]

theorem sym_volume_dualOf (n : Fin 3 → ℝ) :
    spatialVolume * dualOf n + dualOf n * spatialVolume = 0 := by
  rw [dualOf]
  have pair (c : ℝ) (x : PGA) (hx : spatialVolume * x + x * spatialVolume = 0) :
      spatialVolume * (c • x) + (c • x) * spatialVolume = 0 := by
    rw [mul_smul_comm, smul_mul_assoc, ← smul_add, hx, smul_zero]
  have h0 := pair (n 0) (dualNormal 0) (sym_volume_dualNormal 0)
  have h1 := pair (n 1) (dualNormal 1) (sym_volume_dualNormal 1)
  have h2 := pair (n 2) (dualNormal 2) (sym_volume_dualNormal 2)
  simp only [mul_add, add_mul]
  have regroup :
      spatialVolume * (n 0 • dualNormal 0) + spatialVolume * (n 1 • dualNormal 1) +
          spatialVolume * (n 2 • dualNormal 2) +
        ((n 0 • dualNormal 0) * spatialVolume + (n 1 • dualNormal 1) * spatialVolume +
          (n 2 • dualNormal 2) * spatialVolume) =
      (spatialVolume * (n 0 • dualNormal 0) + (n 0 • dualNormal 0) * spatialVolume) +
        (spatialVolume * (n 1 • dualNormal 1) + (n 1 • dualNormal 1) * spatialVolume) +
        (spatialVolume * (n 2 • dualNormal 2) + (n 2 • dualNormal 2) * spatialVolume) := by
    abel
  rw [regroup, h0, h1, h2]
  abel

theorem omegaTorsion_displaced (n : Fin 3 → ℝ) (δ : ℝ) :
    omegaTorsion (displacedMotor n δ).torsion = (-δ) • spatialBoost n := by
  simp only [omegaTorsion, displacedMotor, spatialBoost, Fin.sum_univ_three]
  have hdiv (c : ℝ) : (-2 * δ * c) / 2 = -δ * c := by ring
  simp only [hdiv, zero_div, zero_smul, add_zero]
  have hpull (c : ℝ) (x : PGA) : (-δ * c) • x = (-δ) • (c • x) := by
    rw [← smul_smul]
  rw [hpull, hpull, hpull, ← smul_add, ← smul_add]

theorem commutator_displaced_volume (n : Fin 3 → ℝ) (δ : ℝ) :
    commutator (displacedPlane n δ) spatialVolume = (-2 : ℝ) • spatialTranslation n := by
  rw [displacedPlane, commutator_add_left, commutator_smul_left, commutator_self, smul_zero,
    add_zero, commutator_idealPlaneOf_volume]

theorem vee_displaced_volume_eq_biv (n : Fin 3 → ℝ) (δ : ℝ) :
    (1 / 2 : ℝ) • commutator (displacedPlane n δ) spatialVolume =
      omegaBiv (pureSpatialShift n) := by
  have h : commutator (displacedPlane n δ) spatialVolume =
      commutator (idealPlaneOf n) spatialVolume := by
    rw [commutator_displaced_volume, commutator_idealPlaneOf_volume]
  rw [h, vee_idealPlaneOf_volume_eq_biv]

theorem sym_displaced_volume (n : Fin 3 → ℝ) (δ : ℝ) :
    (1 / 2 : ℝ) • (displacedPlane n δ * spatialVolume +
      spatialVolume * displacedPlane n δ) = (-δ) • (1 : PGA) := by
  have hscale : (δ • spatialVolume) * spatialVolume = δ • (spatialVolume * spatialVolume) :=
    smul_mul_assoc δ spatialVolume spatialVolume
  have hscale' : spatialVolume * (δ • spatialVolume) = δ • (spatialVolume * spatialVolume) :=
    mul_smul_comm δ spatialVolume spatialVolume
  rw [displacedPlane, add_mul, mul_add, hscale, hscale']
  have hsum :
      idealPlaneOf n * spatialVolume + δ • (spatialVolume * spatialVolume) +
          (spatialVolume * idealPlaneOf n + δ • (spatialVolume * spatialVolume)) =
        (idealPlaneOf n * spatialVolume + spatialVolume * idealPlaneOf n) +
          (δ • (spatialVolume * spatialVolume) + δ • (spatialVolume * spatialVolume)) := by
    abel
  rw [hsum, sym_idealPlaneOf_volume, zero_add, spatialVolume_sq]
  have hscale (c : ℝ) : c • (-1 : PGA) = (-c) • (1 : PGA) := by
    have hneg : (-1 : PGA) = (-1 : ℝ) • (1 : PGA) := by
      simp
    rw [hneg, smul_smul]
    congr 1
    ring
  rw [hscale, ← add_smul, smul_smul]
  have hcoef : (1 / 2 : ℝ) * (-δ + -δ) = -δ := by ring
  rw [hcoef]

theorem commutator_displaced_dualOf (n : Fin 3 → ℝ) (δ : ℝ) :
    commutator (displacedPlane n δ) (dualOf n) =
      (2 * spatialNormSq n) • null 0 + (-(2 * δ)) • spatialBoost n := by
  rw [displacedPlane, commutator_add_left, commutator_smul_left, commutator_idealPlaneOf_dualOf,
    commutator_volume_dualOf, smul_smul]
  have hmul : δ * (-2) = -(2 * δ) := by ring
  rw [hmul]

theorem sym_displaced_dualOf (n : Fin 3 → ℝ) (δ : ℝ) :
    displacedPlane n δ * dualOf n + dualOf n * displacedPlane n δ = 0 := by
  have hscale (x : PGA) :
      (δ • spatialVolume) * x + x * (δ • spatialVolume) =
        δ • (spatialVolume * x + x * spatialVolume) := by
    rw [smul_mul_assoc, mul_smul_comm, smul_add]
  rw [displacedPlane, add_mul, mul_add]
  have hsum :
      idealPlaneOf n * dualOf n + (δ • spatialVolume) * dualOf n +
          (dualOf n * idealPlaneOf n + dualOf n * (δ • spatialVolume)) =
        (idealPlaneOf n * dualOf n + dualOf n * idealPlaneOf n) +
          ((δ • spatialVolume) * dualOf n + dualOf n * (δ • spatialVolume)) := by
    abel
  rw [hsum, sym_idealPlaneOf_dualOf, zero_add, hscale, sym_volume_dualOf, smul_zero]

theorem vee_displaced_dualOf (n : Fin 3 → ℝ) (δ : ℝ) :
    (1 / 2 : ℝ) • commutator (displacedPlane n δ) (dualOf n) =
      spatialNormSq n • null 0 + (-δ) • spatialBoost n := by
  rw [commutator_displaced_dualOf, smul_add, smul_smul, smul_smul]
  have h1 : (1 / 2 : ℝ) * (2 * spatialNormSq n) = spatialNormSq n := by ring
  have h2 : (1 / 2 : ℝ) * -(2 * δ) = -δ := by ring
  rw [h1, h2]

theorem vee_displaced_dualOf_eq_biv (n : Fin 3 → ℝ) (δ : ℝ) :
    (1 / 2 : ℝ) • commutator (displacedPlane n δ) (dualOf n) =
      omegaBiv (displacedMotor n δ) := by
  rw [vee_displaced_dualOf, omegaBiv, omegaTorsion_displaced, displacedMotor, omegaTrans_single]
  have hdiv : (2 * spatialNormSq n) / 2 = spatialNormSq n := by ring
  rw [hdiv]
  abel

end DstDiophantine.Gravity.PlaneBracket
