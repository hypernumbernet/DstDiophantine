import DstDiophantine.Algebra.Motor

/-!
# Brackets of coordinate planes

Planes in `G(3,1,1)` are three-blades. On the coordinate planes the
antisymmetric product
`A ∨̲ B = (1/2) (A B - B A)`
is a pure translation, and that translation is the translational half of a
motor.

Write `Πᵢⱼ = e₄ ∧ eᵢ ∧ eⱼ` and let `n` be the unit normal of `(eᵢ, eⱼ)`,
oriented so that `(eᵢ, eⱼ, n)` is right-handed. The spatial volume
`k = e₁ e₂ e₃`, the dual of the time axis, brackets with the plane to the
translation along the normal,
`Πᵢⱼ ∨̲ k = -Nₙ`.
The dual trivector of the normal brackets to the time translation,
`Πᵢⱼ ∨̲ ẽₙ = N₀`,
the same generator for every coordinate plane. The dual trivector of an
axis lying in the plane has vanishing bracket. For `Π₁₂` and `jI = e₀ e₃ e₂`,
the dual of `e₁`, the product equals the grade-four element `e₀ e₁ e₃ e₄`.

`N_μ` is `Ω_trans` of the pure shift with coefficient `2` on axis `μ` and
with vanishing torsion.

## Not claimed

* A bracket for a plane rotated off the coordinate axes, or for a plane
  displaced from the origin.
* An identification of the resulting translation with the torsional mismatch
  of the parent theory.
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


/-- `Π₁₂` against `jI = e₀ e₃ e₂` is the four-vector `e₀ e₁ e₃ e₄`. -/
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

/-- The symmetric product with the spatial volume vanishes. -/
theorem sym_ideal_volume (a : Fin 3) :
    idealPlane a * spatialVolume + spatialVolume * idealPlane a = 0 := by
  rw [idealPlane_mul_volume, volume_mul_idealPlane]
  module

/-- `Πᵢⱼ ∨̲ k = -Nₙ`. -/
theorem vee_ideal_volume (a : Fin 3) :
    (1 / 2 : ℝ) • commutator (idealPlane a) spatialVolume = -null (Fin.succ a) := by
  rw [commutator_ideal_volume, smul_smul]
  norm_num

/-- `Πᵢⱼ` against the dual of its normal has commutator `2 N₀`. -/
theorem commutator_ideal_dualNormal (a : Fin 3) :
    commutator (idealPlane a) (dualNormal a) = (2 : ℝ) • null 0 := by
  rw [Generators.commutator, idealPlane_mul_dualNormal, dualNormal_mul_idealPlane,
    sub_neg_eq_add]
  module

theorem sym_ideal_dualNormal (a : Fin 3) :
    idealPlane a * dualNormal a + dualNormal a * idealPlane a = 0 := by
  rw [idealPlane_mul_dualNormal, dualNormal_mul_idealPlane]
  module

/-- `Πᵢⱼ ∨̲ ẽₙ = N₀`. -/
theorem vee_ideal_dualNormal (a : Fin 3) :
    (1 / 2 : ℝ) • commutator (idealPlane a) (dualNormal a) = null 0 := by
  rw [commutator_ideal_dualNormal, smul_smul]
  norm_num

/-- The blade `e₁ e₂ e₄` is the ideal plane normal to `e₃`. -/
theorem blade12_eq_idealPlane :
    ι 1 * ι 2 * ι e4Index = idealPlane 2 := by
  simpa [idealPlane] using plane12_blade

/-- Appendix order: `(e₁ e₂ e₃) ∨̲ (e₁ e₂ e₄) = N₃`. -/
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

/-- `Π₁₂` against `jI`, the dual of the in-plane axis `e₁`, is grade four. -/
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

/-- `Πᵢⱼ ∨̲ k = Ω_biv` of the pure shift `λⁿ = -2`. -/
theorem vee_ideal_volume_eq_biv (a : Fin 3) :
    (1 / 2 : ℝ) • commutator (idealPlane a) spatialVolume =
      omegaBiv (pureShift (Fin.succ a) (-2)) := by
  rw [vee_ideal_volume, omegaBiv_pureShift]
  have : (-2 : ℝ) / 2 = -1 := by norm_num
  rw [this, neg_one_smul]

/-- `Πᵢⱼ ∨̲ ẽₙ = Ω_biv` of the pure time shift `λ⁰ = 2`. -/
theorem vee_ideal_dualNormal_eq_biv (a : Fin 3) :
    (1 / 2 : ℝ) • commutator (idealPlane a) (dualNormal a) =
      omegaBiv (pureShift 0 2) := by
  rw [vee_ideal_dualNormal, omegaBiv_pureShift]
  have : (2 : ℝ) / 2 = 1 := by norm_num
  rw [this, one_smul]

/-- The appendix order is the pure shift `λ³ = 2`. -/
theorem vee_volume_blade12_eq_biv :
    (1 / 2 : ℝ) • commutator spatialVolume (ι 1 * ι 2 * ι e4Index) =
      omegaBiv (pureShift 3 2) := by
  rw [vee_volume_blade12, omegaBiv_pureShift]
  have : (2 : ℝ) / 2 = 1 := by norm_num
  rw [this, one_smul]

end DstDiophantine.Gravity.PlaneBracket
