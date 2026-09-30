import DstDiophantine.Algebra.BivectorBasis
import DstDiophantine.Algebra.RelativeRotor
import DstDiophantine.Algebra.Sandwich
import DstDiophantine.Gravity.DualRotorFlow
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# One axis splits the null ideal

On one axis the usual generator is the boost bivector `B⁺₀ = e₀e₁` and the
dual generator is the rotation `B⁻₀ = e₃e₂`. They commute, so the torsional
exponential factorises. The two factors stabilise complementary planes of
the translational ideal:

* `R_usual(φ)` scales `N₀ ± N₁` by `e^{±φ}` and fixes `N₂`, `N₃`;
* `R_dual(θ)` rotates the `(N₂, N₃)` plane through `θ` and fixes `N₀`, `N₁`.

The common rapidity `σ = φ + θ` therefore dresses both planes by the same
function, and the mismatch `δ = φ - θ` is the split between them. Along the
written flow that split is the affine lag and the common dressing is the
cubic rapidity. The stiffness accelerates both planes together.

The relative rotor `Ω = R_usual† R_dual` acts by the inverse boost `−φ` on
the first plane and by the rotation `θ` on the second. Neither action is a
function of `δ` alone. Its derivative at the identity along the ray `(φ, θ)`
is `−(φ/2) B⁺₀ + (θ/2) B⁻₀`, which in `(σ, δ)` retains a term in `σ`.
Alignment `δ = 0` with `σ ≠ 0` still moves the null ideal.
-/

namespace DstDiophantine

namespace Gravity

open CliffordAlgebra (reverse)
open PGA Generators Motor Amplification Operations
open RelativeRotor Sandwich BivectorBasis Real
open Filter

/-! ### `cyclic 0` on the frame -/

private theorem cyclic0_mul_ι2 : cyclic 0 * ι 2 = ι 3 := by
  dsimp [cyclic]
  calc (ι 3 * ι 2) * ι 2
      = ι 3 * (ι 2 * ι 2) := by rw [mul_assoc]
    _ = ι 3 := by
        have : ι 2 * ι 2 = (1 : PGA) := by simp [e_sq, Q311_e5vec, w311]
        rw [this, mul_one]

private theorem cyclic0_mul_ι3 : cyclic 0 * ι 3 = -ι 2 := by
  dsimp [cyclic]
  have h23 : ι 2 * ι 3 = -(ι 3 * ι 2) := e_mul_anticomm (by decide)
  have h3sq : ι 3 * ι 3 = (1 : PGA) := by simp [e_sq, Q311_e5vec, w311]
  calc (ι 3 * ι 2) * ι 3
      = ι 3 * (ι 2 * ι 3) := by rw [mul_assoc]
    _ = ι 3 * (-(ι 3 * ι 2)) := by rw [h23]
    _ = -(ι 3 * ι 3 * ι 2) := by simp [mul_assoc]
    _ = -ι 2 := by rw [h3sq]; simp

private theorem ι2_mul_cyclic0 : ι 2 * cyclic 0 = -ι 3 := by
  dsimp [cyclic]
  have h23 : ι 2 * ι 3 = -(ι 3 * ι 2) := e_mul_anticomm (by decide)
  have h2sq : ι 2 * ι 2 = (1 : PGA) := by simp [e_sq, Q311_e5vec, w311]
  calc ι 2 * (ι 3 * ι 2)
      = (ι 2 * ι 3) * ι 2 := (mul_assoc _ _ _).symm
    _ = (-(ι 3 * ι 2)) * ι 2 := by rw [h23]
    _ = -(ι 3 * (ι 2 * ι 2)) := by simp [mul_assoc]
    _ = -ι 3 := by rw [h2sq, mul_one]

private theorem ι3_mul_cyclic0 : ι 3 * cyclic 0 = ι 2 := by
  dsimp [cyclic]
  have h3sq : ι 3 * ι 3 = (1 : PGA) := by simp [e_sq, Q311_e5vec, w311]
  calc ι 3 * (ι 3 * ι 2)
      = (ι 3 * ι 3) * ι 2 := (mul_assoc _ _ _).symm
    _ = ι 2 := by rw [h3sq, one_mul]

private theorem commute_cyclic0_ι {μ : Fin 5} (h2 : μ ≠ 2) (h3 : μ ≠ 3) :
    Commute (cyclic 0) (ι μ) := by
  dsimp [cyclic, Commute, SemiconjBy]
  have h2μ : ι 2 * ι μ = -(ι μ * ι 2) := e_mul_anticomm h2.symm
  have h3μ : ι 3 * ι μ = -(ι μ * ι 3) := e_mul_anticomm h3.symm
  calc
    (ι 3 * ι 2) * ι μ = ι 3 * (ι 2 * ι μ) := by rw [mul_assoc]
    _ = ι 3 * (-(ι μ * ι 2)) := by rw [h2μ]
    _ = -(ι 3 * ι μ) * ι 2 := by simp [mul_assoc]
    _ = -(-(ι μ * ι 3)) * ι 2 := by rw [h3μ]
    _ = ι μ * ι 3 * ι 2 := by simp [mul_assoc]
    _ = ι μ * (ι 3 * ι 2) := by rw [mul_assoc]

private theorem cyclic0_commute_ι0 : Commute (cyclic 0) (ι 0) :=
  commute_cyclic0_ι (by decide) (by decide)

private theorem cyclic0_commute_ι1 : Commute (cyclic 0) (ι 1) :=
  commute_cyclic0_ι (by decide) (by decide)

private theorem cyclic0_commute_ι4 : Commute (cyclic 0) (ι e4Index) :=
  commute_cyclic0_ι (by decide : (e4Index : Fin 5) ≠ 2)
    (by decide : (e4Index : Fin 5) ≠ 3)

private theorem reverse_cs_cyclic0 (c s : ℝ) :
    reverse (c • (1 : PGA) + s • cyclic 0) =
      c • (1 : PGA) - s • cyclic 0 := by
  rw [map_add, map_smul, map_smul, reverse.map_one, cyclic_reverse, smul_neg]
  abel

private theorem cos_sq_add_sin_sq_half (θ : ℝ) :
    Real.cos (θ / 2) ^ 2 + Real.sin (θ / 2) ^ 2 = 1 := by
  simp [Real.cos_sq_add_sin_sq (θ / 2)]

private theorem sandwich_cs_cyclic0_commuting (c s : ℝ) (v : PGA)
    (hv : Commute (cyclic 0) v) (hcs : c ^ 2 + s ^ 2 = 1) :
    (c • (1 : PGA) + s • cyclic 0) * v * (c • (1 : PGA) - s • cyclic 0) = v := by
  have hvB : v * cyclic 0 = cyclic 0 * v := hv.symm.eq
  have hvR : v * (c • (1 : PGA) - s • cyclic 0) =
      (c • (1 : PGA) - s • cyclic 0) * v := by
    simp only [sub_eq_add_neg, mul_add, add_mul, smul_mul_assoc, mul_smul_comm, one_mul,
      mul_neg, neg_mul, mul_one]
    rw [hvB]
  rw [mul_assoc, hvR, ← mul_assoc]
  have hprod : (c • (1 : PGA) + s • cyclic 0) *
      (c • (1 : PGA) - s • cyclic 0) = (1 : PGA) := by
    simp only [sub_eq_add_neg]
    have hexpand :
        (c • (1 : PGA) + s • cyclic 0) * (c • (1 : PGA) + -(s • cyclic 0)) =
          (c • (1 : PGA)) * (c • (1 : PGA)) + (c • (1 : PGA)) * (-(s • cyclic 0)) +
            (s • cyclic 0) * (c • (1 : PGA)) +
            (s • cyclic 0) * (-(s • cyclic 0)) := by
      rw [add_mul, mul_add, mul_add]; abel
    rw [hexpand]
    have a1 : (c • (1 : PGA)) * (c • (1 : PGA)) = (c * c) • (1 : PGA) := by
      rw [mul_smul_comm, smul_mul_assoc, mul_one, smul_smul]
    have a2 : (c • (1 : PGA)) * (-(s • cyclic 0)) = (-(c * s)) • cyclic 0 := by
      rw [mul_neg, smul_mul_assoc, one_mul, smul_smul, ← neg_smul]
    have a3 : (s • cyclic 0) * (c • (1 : PGA)) = (c * s) • cyclic 0 := by
      rw [mul_smul_comm, smul_mul_assoc, mul_one, smul_smul, mul_comm]
    have a4 : (s • cyclic 0) * (-(s • cyclic 0)) = (s * s) • (1 : PGA) := by
      rw [mul_neg, smul_mul_assoc, mul_smul_comm, cyclic_sq 0, smul_smul, smul_neg,
        neg_neg]
    rw [a1, a2, a3, a4]
    have hmid : (-(c * s)) • cyclic 0 + (c * s) • cyclic 0 = (0 : PGA) := by
      rw [← add_smul, neg_add_cancel, zero_smul]
    have hreduce :
        (c * c) • (1 : PGA) + (-(c * s)) • cyclic 0 + (c * s) • cyclic 0 +
            (s * s) • (1 : PGA) = (c * c + s * s) • (1 : PGA) := by
      calc
        (c * c) • (1 : PGA) + (-(c * s)) • cyclic 0 + (c * s) • cyclic 0 +
              (s * s) • (1 : PGA)
            = (c * c) • (1 : PGA) + ((-(c * s)) • cyclic 0 + (c * s) • cyclic 0) +
                (s * s) • (1 : PGA) := by
              ac_rfl
        _ = (c * c) • (1 : PGA) + 0 + (s * s) • (1 : PGA) := by rw [hmid]
        _ = (c * c) • (1 : PGA) + (s * s) • (1 : PGA) := by rw [add_zero]
        _ = (c * c + s * s) • (1 : PGA) := by
              simp [add_smul]
    rw [hreduce]
    have hcs' : (c * c + s * s : ℝ) = 1 := by simpa [pow_two] using hcs
    rw [hcs', one_smul]
  rw [hprod, one_mul]

private theorem sandwich_cs_cyclic0_ι2 (c s : ℝ) :
    (c • (1 : PGA) + s • cyclic 0) * ι 2 *
        (c • (1 : PGA) - s • cyclic 0) =
      (c ^ 2 - s ^ 2) • ι 2 + (2 * c * s) • ι 3 := by
  have hL : (c • (1 : PGA) + s • cyclic 0) * ι 2 = c • ι 2 + s • ι 3 := by
    rw [add_mul, smul_mul_assoc, one_mul, smul_mul_assoc, cyclic0_mul_ι2]
  rw [hL, sub_eq_add_neg]
  have hexpand :
      (c • ι 2 + s • ι 3) * (c • (1 : PGA) + -(s • cyclic 0)) =
        (c • ι 2) * (c • (1 : PGA)) + (c • ι 2) * (-(s • cyclic 0)) +
          (s • ι 3) * (c • (1 : PGA)) + (s • ι 3) * (-(s • cyclic 0)) := by
    rw [add_mul, mul_add, mul_add]; abel
  rw [hexpand]
  have t11 : (c • ι 2) * (c • (1 : PGA)) = (c ^ 2) • ι 2 := by
    rw [mul_smul_comm, smul_mul_assoc, mul_one, smul_smul, pow_two]
  have t12 : (c • ι 2) * (-(s • cyclic 0)) = (c * s) • ι 3 := by
    rw [mul_neg, smul_mul_assoc, mul_smul_comm, ι2_mul_cyclic0]
    simp [smul_neg, neg_neg, smul_smul]
  have t21 : (s • ι 3) * (c • (1 : PGA)) = (c * s) • ι 3 := by
    rw [mul_smul_comm, smul_mul_assoc, mul_one, smul_smul, mul_comm]
  have t22 : (s • ι 3) * (-(s • cyclic 0)) = (-(s ^ 2)) • ι 2 := by
    rw [mul_neg, smul_mul_assoc, mul_smul_comm, ι3_mul_cyclic0]
    simp [smul_smul, pow_two, neg_smul]
  rw [t11, t12, t21, t22]
  module

private theorem sandwich_cs_cyclic0_ι3 (c s : ℝ) :
    (c • (1 : PGA) + s • cyclic 0) * ι 3 *
        (c • (1 : PGA) - s • cyclic 0) =
      (-(2 * c * s)) • ι 2 + (c ^ 2 - s ^ 2) • ι 3 := by
  have hL : (c • (1 : PGA) + s • cyclic 0) * ι 3 = -(s • ι 2) + c • ι 3 := by
    rw [add_mul, smul_mul_assoc, one_mul, smul_mul_assoc, cyclic0_mul_ι3, smul_neg]
    abel
  rw [hL, sub_eq_add_neg]
  have hexpand :
      (-(s • ι 2) + c • ι 3) * (c • (1 : PGA) + -(s • cyclic 0)) =
        (-(s • ι 2)) * (c • (1 : PGA)) + (-(s • ι 2)) * (-(s • cyclic 0)) +
          (c • ι 3) * (c • (1 : PGA)) + (c • ι 3) * (-(s • cyclic 0)) := by
    rw [add_mul, mul_add, mul_add]; abel
  rw [hexpand]
  have t11 : (-(s • ι 2)) * (c • (1 : PGA)) = (-(c * s)) • ι 2 := by
    rw [neg_mul, smul_mul_assoc, mul_smul_comm, mul_one, smul_smul, mul_comm, neg_smul]
  have t12 : (-(s • ι 2)) * (-(s • cyclic 0)) = (-(s ^ 2)) • ι 3 := by
    rw [neg_mul_neg, smul_mul_assoc, mul_smul_comm, ι2_mul_cyclic0]
    simp [smul_smul, pow_two, smul_neg, neg_smul]
  have t21 : (c • ι 3) * (c • (1 : PGA)) = (c ^ 2) • ι 3 := by
    rw [mul_smul_comm, smul_mul_assoc, mul_one, smul_smul, pow_two]
  have t22 : (c • ι 3) * (-(s • cyclic 0)) = (-(c * s)) • ι 2 := by
    rw [mul_neg, smul_mul_assoc, mul_smul_comm, ι3_mul_cyclic0, smul_smul, ← neg_smul]
  rw [t11, t12, t21, t22]
  module

private theorem cos_sq_sub_sin_sq_half (θ : ℝ) :
    Real.cos (θ / 2) ^ 2 - Real.sin (θ / 2) ^ 2 = Real.cos θ := by
  have h := Real.cos_add (θ / 2) (θ / 2)
  rw [show θ / 2 + θ / 2 = θ by ring] at h
  rw [pow_two, pow_two]
  exact h.symm

private theorem sin_half_two (θ : ℝ) :
    2 * Real.cos (θ / 2) * Real.sin (θ / 2) = Real.sin θ := by
  rw [mul_right_comm, ← Real.sin_two_mul, show 2 * (θ / 2) = θ by ring]

theorem sandwich_rotorDual_axis_ι0 (φ θ : ℝ) :
    sandwich (rotorDual (axisParams φ θ)) (ι 0) = ι 0 := by
  rw [sandwich, rotorDual_axis_closed, reverse_cs_cyclic0]
  exact sandwich_cs_cyclic0_commuting _ _ _ cyclic0_commute_ι0 (cos_sq_add_sin_sq_half θ)

theorem sandwich_rotorDual_axis_ι1 (φ θ : ℝ) :
    sandwich (rotorDual (axisParams φ θ)) (ι 1) = ι 1 := by
  rw [sandwich, rotorDual_axis_closed, reverse_cs_cyclic0]
  exact sandwich_cs_cyclic0_commuting _ _ _ cyclic0_commute_ι1 (cos_sq_add_sin_sq_half θ)

theorem sandwich_rotorDual_axis_ι2 (φ θ : ℝ) :
    sandwich (rotorDual (axisParams φ θ)) (ι 2) =
      Real.cos θ • ι 2 + Real.sin θ • ι 3 := by
  rw [sandwich, rotorDual_axis_closed, reverse_cs_cyclic0, sandwich_cs_cyclic0_ι2,
    cos_sq_sub_sin_sq_half, sin_half_two]

theorem sandwich_rotorDual_axis_ι3 (φ θ : ℝ) :
    sandwich (rotorDual (axisParams φ θ)) (ι 3) =
      -Real.sin θ • ι 2 + Real.cos θ • ι 3 := by
  rw [sandwich, rotorDual_axis_closed, reverse_cs_cyclic0, sandwich_cs_cyclic0_ι3,
    cos_sq_sub_sin_sq_half, sin_half_two]

theorem sandwich_rotorDual_axis_ι4 (φ θ : ℝ) :
    sandwich (rotorDual (axisParams φ θ)) (ι e4Index) = ι e4Index := by
  rw [sandwich, rotorDual_axis_closed, reverse_cs_cyclic0]
  exact sandwich_cs_cyclic0_commuting _ _ _ cyclic0_commute_ι4 (cos_sq_add_sin_sq_half θ)

theorem sandwich_rotorDual_axis_null0 (φ θ : ℝ) :
    sandwich (rotorDual (axisParams φ θ)) (null 0) = null 0 := by
  have hm := rotorDual_unitary (axisParams φ θ)
  have hnull : null 0 = ι e4Index * ι 0 := by simp [null]
  rw [hnull, sandwich_mul hm, sandwich_rotorDual_axis_ι4, sandwich_rotorDual_axis_ι0]

theorem sandwich_rotorDual_axis_null1 (φ θ : ℝ) :
    sandwich (rotorDual (axisParams φ θ)) (null 1) = null 1 := by
  have hm := rotorDual_unitary (axisParams φ θ)
  have hnull : null 1 = ι e4Index * ι 1 := by simp [null]
  rw [hnull, sandwich_mul hm, sandwich_rotorDual_axis_ι4, sandwich_rotorDual_axis_ι1]

theorem sandwich_rotorDual_axis_null2 (φ θ : ℝ) :
    sandwich (rotorDual (axisParams φ θ)) (null 2) =
      Real.cos θ • null 2 + Real.sin θ • null 3 := by
  have hm := rotorDual_unitary (axisParams φ θ)
  have hnull : null 2 = ι e4Index * ι 2 := by simp [null]
  rw [hnull, sandwich_mul hm, sandwich_rotorDual_axis_ι4, sandwich_rotorDual_axis_ι2, mul_add]
  simp only [mul_smul_comm]
  simp [null]

theorem sandwich_rotorDual_axis_null3 (φ θ : ℝ) :
    sandwich (rotorDual (axisParams φ θ)) (null 3) =
      -Real.sin θ • null 2 + Real.cos θ • null 3 := by
  have hm := rotorDual_unitary (axisParams φ θ)
  have hnull : null 3 = ι e4Index * ι 3 := by simp [null]
  rw [hnull, sandwich_mul hm, sandwich_rotorDual_axis_ι4, sandwich_rotorDual_axis_ι3, mul_add]
  simp only [mul_smul_comm]
  simp [null]

/-! ### The factorised axis rotor -/

theorem rotorUsual_axis_eq_pureBoost (φ θ : ℝ) :
    rotorUsual (axisParams φ θ) = rotorTorsion (pureBoost φ) := by
  rw [rotorUsual_axis_closed, rotorTorsion_pureBoost_closed]

theorem reverse_rotorUsual_axis_eq_negBoost (φ θ : ℝ) :
    reverse (rotorUsual (axisParams φ θ)) = rotorTorsion (pureBoost (-φ)) := by
  rw [rotorUsual_axis_eq_pureBoost, reverse_rotorTorsion_pureBoost_eq]

private theorem cosh_add_sinh (x : ℝ) : Real.cosh x + Real.sinh x = Real.exp x := by
  rw [Real.cosh_eq, Real.sinh_eq]
  ring

private theorem cosh_sub_sinh (x : ℝ) : Real.cosh x - Real.sinh x = Real.exp (-x) := by
  rw [Real.cosh_eq, Real.sinh_eq]
  ring

theorem sandwich_axis_null0 (φ θ : ℝ) :
    sandwich (rotorTorsion (axisParams φ θ)) (null 0) =
      Real.cosh φ • null 0 + Real.sinh φ • null 1 := by
  rw [rotorTorsion_axis_factor, sandwich_comp, sandwich_rotorDual_axis_null0,
    rotorUsual_axis_eq_pureBoost, sandwich_pureBoost_null0]

theorem sandwich_axis_null1 (φ θ : ℝ) :
    sandwich (rotorTorsion (axisParams φ θ)) (null 1) =
      Real.sinh φ • null 0 + Real.cosh φ • null 1 := by
  rw [rotorTorsion_axis_factor, sandwich_comp, sandwich_rotorDual_axis_null1,
    rotorUsual_axis_eq_pureBoost, sandwich_pureBoost_null1]

theorem sandwich_axis_null2 (φ θ : ℝ) :
    sandwich (rotorTorsion (axisParams φ θ)) (null 2) =
      Real.cos θ • null 2 + Real.sin θ • null 3 := by
  rw [rotorTorsion_axis_factor, sandwich_comp, sandwich_rotorDual_axis_null2, sandwich_add,
    sandwich_smul, sandwich_smul, rotorUsual_axis_eq_pureBoost, sandwich_pureBoost_null2,
    sandwich_pureBoost_null3]

theorem sandwich_axis_null3 (φ θ : ℝ) :
    sandwich (rotorTorsion (axisParams φ θ)) (null 3) =
      -Real.sin θ • null 2 + Real.cos θ • null 3 := by
  rw [rotorTorsion_axis_factor, sandwich_comp, sandwich_rotorDual_axis_null3, sandwich_add,
    sandwich_smul, sandwich_smul, rotorUsual_axis_eq_pureBoost, sandwich_pureBoost_null2,
    sandwich_pureBoost_null3]

/-- Lightlike combination in the boost plane, scaled by the usual rapidity alone. -/
theorem sandwich_axis_null_plus (φ θ : ℝ) :
    sandwich (rotorTorsion (axisParams φ θ)) (null 0 + null 1) =
      Real.exp φ • (null 0 + null 1) := by
  rw [sandwich_add, sandwich_axis_null0, sandwich_axis_null1]
  have h :
      Real.cosh φ • null 0 + Real.sinh φ • null 1 +
          (Real.sinh φ • null 0 + Real.cosh φ • null 1) =
        (Real.cosh φ + Real.sinh φ) • (null 0 + null 1) := by
    module
  rw [h, cosh_add_sinh]

/-- The opposite ray of the boost plane, scaled by `e^{-φ}`. -/
theorem sandwich_axis_null_minus (φ θ : ℝ) :
    sandwich (rotorTorsion (axisParams φ θ)) (null 0 - null 1) =
      Real.exp (-φ) • (null 0 - null 1) := by
  rw [sandwich_sub, sandwich_axis_null0, sandwich_axis_null1]
  have h :
      Real.cosh φ • null 0 + Real.sinh φ • null 1 -
          (Real.sinh φ • null 0 + Real.cosh φ • null 1) =
        (Real.cosh φ - Real.sinh φ) • (null 0 - null 1) := by
    module
  rw [h, cosh_sub_sinh]

/-! ### Relative rotor on the two planes -/

theorem sandwich_relative_null_plus (φ θ : ℝ) :
    sandwich (relativeRotor (axisParams φ θ)) (null 0 + null 1) =
      Real.exp (-φ) • (null 0 + null 1) := by
  rw [relativeRotor, sandwich_comp, sandwich_add, sandwich_rotorDual_axis_null0,
    sandwich_rotorDual_axis_null1, reverse_rotorUsual_axis_eq_negBoost, sandwich_add,
    sandwich_pureBoost_null0, sandwich_pureBoost_null1]
  have h :
      Real.cosh (-φ) • null 0 + Real.sinh (-φ) • null 1 +
          (Real.sinh (-φ) • null 0 + Real.cosh (-φ) • null 1) =
        (Real.cosh (-φ) + Real.sinh (-φ)) • (null 0 + null 1) := by
    module
  rw [h]
  have hcosh : Real.cosh (-φ) = Real.cosh φ := by rw [Real.cosh_neg]
  have hsinh : Real.sinh (-φ) = -Real.sinh φ := by rw [Real.sinh_neg]
  rw [hcosh, hsinh]
  have hsub : Real.cosh φ + -Real.sinh φ = Real.cosh φ - Real.sinh φ := by ring
  rw [hsub, cosh_sub_sinh]

theorem sandwich_relative_null2 (φ θ : ℝ) :
    sandwich (relativeRotor (axisParams φ θ)) (null 2) =
      Real.cos θ • null 2 + Real.sin θ • null 3 := by
  rw [relativeRotor, sandwich_comp, sandwich_rotorDual_axis_null2, sandwich_add, sandwich_smul,
    sandwich_smul, reverse_rotorUsual_axis_eq_negBoost, sandwich_pureBoost_null2,
    sandwich_pureBoost_null3]

theorem null01_ne_zero : null 0 + null 1 ≠ 0 := by
  intro h
  let l : Fin 4 → ℝ := fun μ => match μ with
    | 0 => 1
    | 1 => 1
    | _ => 0
  have hsum : ∑ μ : Fin 4, l μ • null μ = 0 := by
    rw [Fin.sum_univ_four]
    simpa [l] using h
  have hli := Fintype.linearIndependent_iff.mp linearIndependent_null l hsum
  have : (1 : ℝ) = 0 := by simpa [l] using hli 0
  norm_num at this

private theorem absurd_scale_fix {c : ℝ} {v : PGA} (hv : v ≠ 0) (hc : c ≠ 1)
    (h : v = c • v) : False := by
  have hzero : (1 - c) • v = 0 := by
    rw [sub_smul, one_smul]
    nth_rw 1 [h]
    exact sub_self _
  have hc0 : 1 - c ≠ 0 := sub_ne_zero.mpr (Ne.symm hc)
  have hv0 : v = 0 := by
    have hinv : v = (1 - c)⁻¹ • ((1 - c) • v) := by
      rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]
    rw [hzero, smul_zero] at hinv
    exact hinv
  exact hv hv0

/-- Equal mismatch, unequal action on the null ideal: both planes see `(φ, θ)`, not `δ`. -/
theorem same_lag_distinct_null :
    ((0 : ℝ) - 0 = (1 : ℝ) - 1) ∧
      sandwich (relativeRotor (axisParams 0 0)) (null 0 + null 1) ≠
        sandwich (relativeRotor (axisParams 1 1)) (null 0 + null 1) ∧
        sandwich (relativeRotor (axisParams 0 0)) (null 2) ≠
          sandwich (relativeRotor (axisParams 1 1)) (null 2) := by
  refine ⟨by ring, ?_, ?_⟩
  · rw [sandwich_relative_null_plus, sandwich_relative_null_plus]
    intro h
    rw [neg_zero, Real.exp_zero, one_smul] at h
    have hc : Real.exp (-(1 : ℝ)) ≠ 1 := by
      intro hexp
      rw [Real.exp_eq_one_iff] at hexp
      norm_num at hexp
    exact absurd_scale_fix null01_ne_zero hc h
  · rw [sandwich_relative_null2, sandwich_relative_null2]
    intro h
    rw [Real.cos_zero, Real.sin_zero, one_smul, zero_smul, add_zero] at h
    have hlin : (Real.cos 1 - 1) • null 2 + Real.sin 1 • null 3 = 0 := by
      calc
        (Real.cos 1 - 1) • null 2 + Real.sin 1 • null 3
            = Real.cos 1 • null 2 + Real.sin 1 • null 3 - null 2 := by
              rw [sub_smul, one_smul]; abel
          _ = null 2 - null 2 := by rw [← h]
          _ = 0 := sub_self _
    let l : Fin 4 → ℝ := fun μ => match μ with
      | 2 => Real.cos 1 - 1
      | 3 => Real.sin 1
      | _ => 0
    have hsum : ∑ μ : Fin 4, l μ • null μ = 0 := by
      rw [Fin.sum_univ_four]
      simpa [l] using hlin
    have hli := Fintype.linearIndependent_iff.mp linearIndependent_null l hsum
    have hsin : Real.sin 1 = 0 := by simpa [l] using hli 3
    have hpos : 0 < Real.sin 1 :=
      Real.sin_pos_of_pos_of_lt_pi (by norm_num : (0 : ℝ) < 1)
        (lt_trans (by norm_num : (1 : ℝ) < 3) Real.pi_gt_three)
    exact hpos.ne' hsin

/-! ### First order at the identity retains `σ` -/

private theorem hasDerivAt_const_mul_id (c t : ℝ) :
    HasDerivAt (fun s : ℝ => c * s) c t := by
  refine ((hasDerivAt_id t).const_mul c).congr_of_eventuallyEq ?_ |>.congr_deriv (by ring)
  refine Eventually.of_forall ?_
  intro s
  simp

private theorem hasDerivAt_cosh_mul (κ t : ℝ) :
    HasDerivAt (fun s : ℝ => Real.cosh (κ * s)) (Real.sinh (κ * t) * κ) t := by
  simpa [Function.comp_def] using
    (Real.hasDerivAt_cosh (κ * t)).comp t (hasDerivAt_const_mul_id κ t)

private theorem hasDerivAt_sinh_mul (κ t : ℝ) :
    HasDerivAt (fun s : ℝ => Real.sinh (κ * s)) (Real.cosh (κ * t) * κ) t := by
  simpa [Function.comp_def] using
    (Real.hasDerivAt_sinh (κ * t)).comp t (hasDerivAt_const_mul_id κ t)

private theorem hasDerivAt_cos_mul (ω t : ℝ) :
    HasDerivAt (fun s : ℝ => Real.cos (ω * s)) (-Real.sin (ω * t) * ω) t := by
  simpa [Function.comp_def] using
    (Real.hasDerivAt_cos (ω * t)).comp t (hasDerivAt_const_mul_id ω t)

private theorem hasDerivAt_sin_mul (ω t : ℝ) :
    HasDerivAt (fun s : ℝ => Real.sin (ω * s)) (Real.cos (ω * t) * ω) t := by
  simpa [Function.comp_def] using
    (Real.hasDerivAt_sin (ω * t)).comp t (hasDerivAt_const_mul_id ω t)

private theorem reverse_rotorUsual_ray (φ θ t : ℝ) :
    reverse (rotorUsual (axisParams (t * φ) (t * θ))) =
      Real.cosh ((φ / 2) * t) • (1 : PGA) -
        Real.sinh ((φ / 2) * t) • hyperbolic 0 := by
  rw [reverse_rotorUsual_axis]
  have hcosh : Real.cosh ((t * φ) / 2) = Real.cosh ((φ / 2) * t) := by
    congr 1
    ring
  have hsinh : Real.sinh ((t * φ) / 2) = Real.sinh ((φ / 2) * t) := by
    congr 1
    ring
  rw [hcosh, hsinh]

private theorem rotorDual_ray (φ θ t : ℝ) :
    rotorDual (axisParams (t * φ) (t * θ)) =
      Real.cos ((θ / 2) * t) • (1 : PGA) +
        Real.sin ((θ / 2) * t) • cyclic 0 := by
  rw [rotorDual_axis_closed]
  have hcos : Real.cos ((t * θ) / 2) = Real.cos ((θ / 2) * t) := by
    congr 1
    ring
  have hsin : Real.sin ((t * θ) / 2) = Real.sin ((θ / 2) * t) := by
    congr 1
    ring
  rw [hcos, hsin]

private theorem hasDerivAt_reverse_rotorUsual_ray (φ θ : ℝ) :
    HasDerivAt (fun t => reverse (rotorUsual (axisParams (t * φ) (t * θ))))
      (-(φ / 2) • hyperbolic 0) 0 := by
  have hfun :
      (fun t => reverse (rotorUsual (axisParams (t * φ) (t * θ)))) =
        fun t => Real.cosh ((φ / 2) * t) • (1 : PGA) -
          Real.sinh ((φ / 2) * t) • hyperbolic 0 := by
    funext t
    exact reverse_rotorUsual_ray φ θ t
  rw [hfun]
  have hc := (hasDerivAt_cosh_mul (φ / 2) 0).smul_const (1 : PGA)
  have hs := (hasDerivAt_sinh_mul (φ / 2) 0).smul_const (hyperbolic 0)
  refine (hc.sub hs).congr_deriv ?_
  simp [Real.sinh_zero, Real.cosh_zero, zero_smul, sub_eq_add_neg]

private theorem hasDerivAt_rotorDual_ray (φ θ : ℝ) :
    HasDerivAt (fun t => rotorDual (axisParams (t * φ) (t * θ)))
      ((θ / 2) • cyclic 0) 0 := by
  have hfun :
      (fun t => rotorDual (axisParams (t * φ) (t * θ))) =
        fun t => Real.cos ((θ / 2) * t) • (1 : PGA) +
          Real.sin ((θ / 2) * t) • cyclic 0 := by
    funext t
    exact rotorDual_ray φ θ t
  rw [hfun]
  have hc := (hasDerivAt_cos_mul (θ / 2) 0).smul_const (1 : PGA)
  have hs := (hasDerivAt_sin_mul (θ / 2) 0).smul_const (cyclic 0)
  refine (hc.add hs).congr_deriv ?_
  simp [Real.sin_zero, Real.cos_zero, zero_smul]

/-- Derivative at the identity along the ray of rapidities `(φ, θ)`. -/
theorem relativeRotor_ray_deriv (φ θ : ℝ) :
    deriv (fun t => relativeRotor (axisParams (t * φ) (t * θ))) 0 =
      -(φ / 2) • hyperbolic 0 + (θ / 2) • cyclic 0 := by
  have hf := hasDerivAt_reverse_rotorUsual_ray φ θ
  have hg := hasDerivAt_rotorDual_ray φ θ
  have hfun :
      (fun t => relativeRotor (axisParams (t * φ) (t * θ))) =
        fun t => reverse (rotorUsual (axisParams (t * φ) (t * θ))) *
          rotorDual (axisParams (t * φ) (t * θ)) := by
    funext t
    rfl
  rw [hfun]
  have hmul := hf.mul hg
  have h0u : reverse (rotorUsual (axisParams ((0 : ℝ) * φ) ((0 : ℝ) * θ))) = 1 := by
    rw [reverse_rotorUsual_ray]
    simp [Real.cosh_zero, Real.sinh_zero]
  have h0d : rotorDual (axisParams ((0 : ℝ) * φ) ((0 : ℝ) * θ)) = 1 := by
    rw [rotorDual_ray]
    simp [Real.cos_zero, Real.sin_zero]
  have hderiv :
      (-(φ / 2) • hyperbolic 0) * rotorDual (axisParams (0 * φ) (0 * θ)) +
          reverse (rotorUsual (axisParams (0 * φ) (0 * θ))) * ((θ / 2) • cyclic 0) =
        -(φ / 2) • hyperbolic 0 + (θ / 2) • cyclic 0 := by
    rw [h0u, h0d, mul_one, one_mul]
  exact (hmul.congr_deriv hderiv).deriv

/-- The same derivative in the sum `σ` and the difference `δ`. -/
theorem relativeRotor_ray_deriv_channels (σ δ : ℝ) :
    deriv (fun t => relativeRotor (axisParams (t * ((σ + δ) / 2)) (t * ((σ - δ) / 2)))) 0 =
      -(σ / 4) • (hyperbolic 0 - cyclic 0) - (δ / 4) • (hyperbolic 0 + cyclic 0) := by
  rw [relativeRotor_ray_deriv]
  module

theorem cyclic_sub_hyperbolic_ne_zero : cyclic 0 - hyperbolic 0 ≠ 0 := by
  intro h
  have : cyclic 0 = (1 : ℝ) • hyperbolic 0 := by
    rw [one_smul]
    exact sub_eq_zero.mp h
  exact cyclic_ne_smul_hyperbolic 0 1 this

/-- Along alignment the first-order mismatch is the common rapidity. -/
theorem aligned_linear_eq (σ : ℝ) :
    deriv (fun t => relativeRotor (axisParams (t * (σ / 2)) (t * (σ / 2)))) 0 =
      (σ / 4) • (cyclic 0 - hyperbolic 0) := by
  have h := relativeRotor_ray_deriv_channels σ 0
  have harg :
      (fun t => relativeRotor (axisParams (t * ((σ + 0) / 2)) (t * ((σ - 0) / 2)))) =
        fun t => relativeRotor (axisParams (t * (σ / 2)) (t * (σ / 2))) := by
    funext t
    ring_nf
  rw [harg] at h
  rw [h]
  simp only [zero_div, zero_smul, sub_zero]
  module

theorem aligned_linear_ne_zero {σ : ℝ} (hσ : σ ≠ 0) :
    deriv (fun t => relativeRotor (axisParams (t * (σ / 2)) (t * (σ / 2)))) 0 ≠ 0 := by
  rw [aligned_linear_eq]
  intro h
  have hc : σ / 4 ≠ 0 := by
    exact div_ne_zero hσ (by norm_num)
  have : cyclic 0 - hyperbolic 0 =
      (σ / 4)⁻¹ • ((σ / 4) • (cyclic 0 - hyperbolic 0)) := by
    rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
  rw [h, smul_zero] at this
  exact cyclic_sub_hyperbolic_ne_zero this

/-- Alignment with a nonzero common rapidity moves the boost plane of the null ideal. -/
theorem aligned_moves_null {σ : ℝ} (hσ : σ ≠ 0) :
    sandwich (rotorTorsion (axisParams (σ / 2) (σ / 2))) (null 0 + null 1) ≠
      null 0 + null 1 := by
  rw [sandwich_axis_null_plus]
  intro h
  have hc : Real.exp (σ / 2) ≠ 1 := by
    intro hexp
    rw [Real.exp_eq_one_iff] at hexp
    exact hσ (by linarith)
  exact absurd_scale_fix null01_ne_zero hc h.symm

/-! ### The written flow is this split -/

theorem written_plane_params (σ₀ σd₀ m δ₀ ν t : ℝ) :
    writtenUsual σ₀ σd₀ m δ₀ ν t =
        (writtenSigma σ₀ σd₀ m δ₀ ν t + writtenDelta δ₀ ν t) / 2 ∧
      writtenDual σ₀ σd₀ m δ₀ ν t =
        (writtenSigma σ₀ σd₀ m δ₀ ν t - writtenDelta δ₀ ν t) / 2 := by
  constructor
  · simp [writtenUsual, usualFrom, writtenSigma, writtenDelta]
  · simp [writtenDual, dualFrom, writtenSigma, writtenDelta]

theorem written_planes_accelerate (σ₀ σd₀ m δ₀ ν t : ℝ) :
    deriv (deriv (writtenUsual σ₀ σd₀ m δ₀ ν)) t = -m * writtenDelta δ₀ ν t ∧
      deriv (deriv (writtenDual σ₀ σd₀ m δ₀ ν)) t = -m * writtenDelta δ₀ ν t ∧
        deriv (deriv (fun s =>
          writtenUsual σ₀ σd₀ m δ₀ ν s - writtenDual σ₀ σd₀ m δ₀ ν s)) t = 0 := by
  refine ⟨deriv2_writtenUsual σ₀ σd₀ m δ₀ ν t, deriv2_writtenDual σ₀ σd₀ m δ₀ ν t, ?_⟩
  have hsub :
      (fun s => writtenUsual σ₀ σd₀ m δ₀ ν s - writtenDual σ₀ σd₀ m δ₀ ν s) =
        writtenDelta δ₀ ν := by
    funext s
    simp [writtenUsual, writtenDual, usualFrom_sub_dualFrom]
  rw [hsub, deriv2_writtenDelta]

theorem written_flow_boost_plane (σ₀ σd₀ m δ₀ ν t : ℝ) :
    sandwich (rotorTorsion (axisParams (writtenUsual σ₀ σd₀ m δ₀ ν t)
        (writtenDual σ₀ σd₀ m δ₀ ν t))) (null 0 + null 1) =
      Real.exp (writtenUsual σ₀ σd₀ m δ₀ ν t) • (null 0 + null 1) :=
  sandwich_axis_null_plus _ _

theorem written_flow_rotation_plane (σ₀ σd₀ m δ₀ ν t : ℝ) :
    sandwich (rotorTorsion (axisParams (writtenUsual σ₀ σd₀ m δ₀ ν t)
        (writtenDual σ₀ σd₀ m δ₀ ν t))) (null 2) =
      Real.cos (writtenDual σ₀ σd₀ m δ₀ ν t) • null 2 +
        Real.sin (writtenDual σ₀ σd₀ m δ₀ ν t) • null 3 :=
  sandwich_axis_null2 _ _

/-- The written flow dresses the boost plane by `(σ+δ)/2` and rotates the other by `(σ−δ)/2`. -/
theorem written_flow_null_split (σ₀ σd₀ m δ₀ ν t : ℝ) :
    writtenUsual σ₀ σd₀ m δ₀ ν t =
        (writtenSigma σ₀ σd₀ m δ₀ ν t + writtenDelta δ₀ ν t) / 2 ∧
      writtenDual σ₀ σd₀ m δ₀ ν t =
        (writtenSigma σ₀ σd₀ m δ₀ ν t - writtenDelta δ₀ ν t) / 2 ∧
      sandwich (rotorTorsion (axisParams (writtenUsual σ₀ σd₀ m δ₀ ν t)
          (writtenDual σ₀ σd₀ m δ₀ ν t))) (null 0 + null 1) =
        Real.exp (writtenUsual σ₀ σd₀ m δ₀ ν t) • (null 0 + null 1) ∧
      sandwich (rotorTorsion (axisParams (writtenUsual σ₀ σd₀ m δ₀ ν t)
          (writtenDual σ₀ σd₀ m δ₀ ν t))) (null 2) =
        Real.cos (writtenDual σ₀ σd₀ m δ₀ ν t) • null 2 +
          Real.sin (writtenDual σ₀ σd₀ m δ₀ ν t) • null 3 :=
  ⟨(written_plane_params σ₀ σd₀ m δ₀ ν t).1,
    (written_plane_params σ₀ σd₀ m δ₀ ν t).2,
    written_flow_boost_plane σ₀ σd₀ m δ₀ ν t,
    written_flow_rotation_plane σ₀ σd₀ m δ₀ ν t⟩

end Gravity

end DstDiophantine
