import DstDiophantine.Algebra.Motor
import DstDiophantine.Algebra.Amplification
import DstDiophantine.Algebra.Generators
import DstDiophantine.Algebra.Operations
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Geometric sandwich `M v M˜`

## Proved

* Algebraic laws: linearity in the second argument, composition, reverse intertwining.
* Unitary conjugation (`m * reverse m = 1`) is a geometric-product automorphism,
  hence preserves Clifford squares; in particular the Minkowski square of
  `minkowskiVector v` is unchanged.
* Closed-form pure-boost rotor and its action on the frame `{ι μ}` together with
  light-cone eigenvalues `e^{±φ}`.

## Not claimed

* General grade-1 projection for arbitrary multivectors (chart bridge uses
  closed-form pure-boost sandwiches; see `Gravity.Tetrad`).
* Isometry of the full degenerate quadratic form of `G(3,1,1)`.
-/

namespace DstDiophantine

open PGA
open Generators Motor Amplification Operations NormedSpace Real
open CliffordAlgebra (reverse reverse_reverse)

namespace Sandwich

/-- Geometric sandwich `M v M˜`. -/
noncomputable def sandwich (m v : PGA) : PGA :=
  m * v * reverse m

@[simp] theorem sandwich_one (v : PGA) : sandwich 1 v = v := by
  simp [sandwich]

theorem sandwich_smul (m : PGA) (c : ℝ) (v : PGA) :
    sandwich m (c • v) = c • sandwich m v := by
  simp [sandwich]

theorem sandwich_add (m : PGA) (v w : PGA) :
    sandwich m (v + w) = sandwich m v + sandwich m w := by
  simp [sandwich, mul_add, add_mul]

theorem sandwich_neg (m v : PGA) : sandwich m (-v) = -sandwich m v := by
  simp [sandwich]

theorem sandwich_sub (m : PGA) (v w : PGA) :
    sandwich m (v - w) = sandwich m v - sandwich m w := by
  simp [sub_eq_add_neg, sandwich_add, sandwich_neg]

theorem sandwich_comp (m n v : PGA) :
    sandwich (m * n) v = sandwich m (sandwich n v) := by
  simp only [sandwich, reverse.map_mul]
  ac_rfl

theorem sandwich_reverse (m v : PGA) :
    reverse (sandwich m v) = sandwich m (reverse v) := by
  simp only [sandwich, reverse.map_mul, reverse_reverse]
  rw [mul_assoc]

/-! ### Unitary conjugation -/

/-- Unitary sandwich preserves geometric products. -/
theorem sandwich_mul {m : PGA} (hm : m * reverse m = 1) (x y : PGA) :
    sandwich m (x * y) = sandwich m x * sandwich m y := by
  have hrm : reverse m * m = 1 := reverse_mul_of_mul_reverse hm
  simp only [sandwich]
  have hy : y = reverse m * m * y := by rw [hrm, one_mul]
  nth_rw 1 [hy]
  ac_rfl

theorem sandwich_sq {m : PGA} (hm : m * reverse m = 1) (v : PGA) :
    sandwich m v * sandwich m v = sandwich m (v * v) :=
  (sandwich_mul hm v v).symm

/-- Minkowski square is invariant under unitary sandwich (no grade claim). -/
theorem sandwich_minkowskiVector_sq {m : PGA} (hm : m * reverse m = 1) (v : Fin 4 → ℝ) :
    sandwich m (minkowskiVector v) * sandwich m (minkowskiVector v) =
      algebraMap ℝ PGA (Q31 v) := by
  rw [sandwich_sq hm, minkowskiVector_sq]
  simp only [sandwich]
  set a := algebraMap ℝ PGA (Q31 v)
  have hc : Commute a m := Algebra.commutes _ _
  calc
    m * a * reverse m = m * (a * reverse m) := by rw [mul_assoc]
    _ = (m * a) * reverse m := by rw [← mul_assoc]
    _ = (a * m) * reverse m := by rw [hc.eq]
    _ = a * (m * reverse m) := by rw [mul_assoc]
    _ = a := by rw [hm, mul_one]

/-! ### Pure-boost closed form -/

theorem rotorTorsion_pureBoost_closed (φ : ℝ) :
    rotorTorsion (pureBoost φ) =
      Real.cosh (φ / 2) • (1 : PGA) + Real.sinh (φ / 2) • hyperbolic 0 := by
  rw [rotorTorsion_pureBoost, exp_of_sq_one (hyperbolic_sq 0)]

private theorem reverse_cs (c s : ℝ) :
    reverse (c • (1 : PGA) + s • hyperbolic 0) =
      c • (1 : PGA) - s • hyperbolic 0 := by
  rw [map_add, map_smul, map_smul, reverse.map_one, hyperbolic_reverse, smul_neg]
  abel

theorem reverse_rotorTorsion_pureBoost (φ : ℝ) :
    reverse (rotorTorsion (pureBoost φ)) =
      Real.cosh (φ / 2) • (1 : PGA) - Real.sinh (φ / 2) • hyperbolic 0 := by
  rw [rotorTorsion_pureBoost_closed, reverse_cs]

/-! ### Frame multiplication by `B = hyperbolic 0` -/

private theorem hyperbolic0_mul_ι0 : hyperbolic 0 * ι 0 = ι 1 := by
  dsimp [hyperbolic]
  have h10 : ι 1 * ι 0 = -(ι 0 * ι 1) := e_mul_anticomm (by decide)
  calc
    (ι 0 * ι 1) * ι 0 = ι 0 * (ι 1 * ι 0) := by rw [mul_assoc]
    _ = ι 0 * (-(ι 0 * ι 1)) := by rw [h10]
    _ = -(ι 0 * ι 0 * ι 1) := by simp [mul_assoc]
    _ = ι 1 := by simp [e0_sq]

private theorem hyperbolic0_mul_ι1 : hyperbolic 0 * ι 1 = ι 0 := by
  dsimp [hyperbolic]
  calc
    (ι 0 * ι 1) * ι 1 = ι 0 * (ι 1 * ι 1) := by rw [mul_assoc]
    _ = ι 0 := by simp [e1_sq]

private theorem ι0_mul_hyperbolic0 : ι 0 * hyperbolic 0 = -ι 1 := by
  dsimp [hyperbolic]
  calc
    ι 0 * (ι 0 * ι 1) = (ι 0 * ι 0) * ι 1 := (mul_assoc _ _ _).symm
    _ = algebraMap ℝ PGA (-1) * ι 1 := by rw [e0_sq]
    _ = -ι 1 := by simp

private theorem ι1_mul_hyperbolic0 : ι 1 * hyperbolic 0 = -ι 0 := by
  dsimp [hyperbolic]
  have h10 : ι 1 * ι 0 = -(ι 0 * ι 1) := e_mul_anticomm (by decide)
  calc
    ι 1 * (ι 0 * ι 1) = (ι 1 * ι 0) * ι 1 := by rw [mul_assoc]
    _ = (-(ι 0 * ι 1)) * ι 1 := by rw [h10]
    _ = -(ι 0 * (ι 1 * ι 1)) := by simp [mul_assoc]
    _ = -ι 0 := by simp [e1_sq]

private theorem commute_hyperbolic0_ι {μ : Fin 5}
    (h0 : μ ≠ 0) (h1 : μ ≠ 1) : Commute (hyperbolic 0) (ι μ) := by
  dsimp [hyperbolic, Commute, SemiconjBy]
  have hμ0 : ι μ * ι 0 = -(ι 0 * ι μ) := e_mul_anticomm h0
  have h1μ : ι 1 * ι μ = -(ι μ * ι 1) := e_mul_anticomm h1.symm
  calc
    (ι 0 * ι 1) * ι μ = ι 0 * (ι 1 * ι μ) := by rw [mul_assoc]
    _ = ι 0 * (-(ι μ * ι 1)) := by rw [h1μ]
    _ = -(ι 0 * ι μ) * ι 1 := by simp [mul_assoc]
    _ = -(-(ι μ * ι 0)) * ι 1 := by rw [hμ0]; simp
    _ = ι μ * ι 0 * ι 1 := by simp [mul_assoc]
    _ = ι μ * (ι 0 * ι 1) := by rw [mul_assoc]

private theorem hyperbolic0_commute_ι2 : Commute (hyperbolic 0) (ι 2) :=
  commute_hyperbolic0_ι (by decide) (by decide)

private theorem hyperbolic0_commute_ι3 : Commute (hyperbolic 0) (ι 3) :=
  commute_hyperbolic0_ι (by decide) (by decide)

private theorem hyperbolic0_commute_ι4 : Commute (hyperbolic 0) (ι e4Index) :=
  commute_hyperbolic0_ι (by decide : (e4Index : Fin 5) ≠ 0) (by decide)

/-! ### Double-angle helpers -/

private theorem cosh_half_sq_add (φ : ℝ) :
    Real.cosh (φ / 2) ^ 2 + Real.sinh (φ / 2) ^ 2 = Real.cosh φ := by
  simpa [mul_div_cancel₀ φ (by norm_num : (2 : ℝ) ≠ 0)] using
    (Real.cosh_two_mul (φ / 2)).symm

private theorem sinh_half_two (φ : ℝ) :
    2 * Real.sinh (φ / 2) * Real.cosh (φ / 2) = Real.sinh φ := by
  simpa [mul_div_cancel₀ φ (by norm_num : (2 : ℝ) ≠ 0)] using
    (Real.sinh_two_mul (φ / 2)).symm

/-! ### Algebraic sandwich of the closed-form boost rotor -/

private theorem sandwich_cs_ι0 (c s : ℝ) :
    (c • (1 : PGA) + s • hyperbolic 0) * ι 0 *
        (c • (1 : PGA) - s • hyperbolic 0) =
      (c ^ 2 + s ^ 2) • ι 0 + (2 * c * s) • ι 1 := by
  have hL : (c • (1 : PGA) + s • hyperbolic 0) * ι 0 = c • ι 0 + s • ι 1 := by
    rw [add_mul, smul_mul_assoc, one_mul, smul_mul_assoc, hyperbolic0_mul_ι0]
  rw [hL, sub_eq_add_neg]
  have hexpand :
      (c • ι 0 + s • ι 1) * (c • (1 : PGA) + -(s • hyperbolic 0)) =
        (c • ι 0) * (c • (1 : PGA)) + (c • ι 0) * (-(s • hyperbolic 0)) +
          (s • ι 1) * (c • (1 : PGA)) + (s • ι 1) * (-(s • hyperbolic 0)) := by
    rw [add_mul, mul_add, mul_add]; abel
  rw [hexpand]
  have t11 : (c • ι 0) * (c • (1 : PGA)) = (c ^ 2) • ι 0 := by
    rw [mul_smul_comm, smul_mul_assoc, mul_one, smul_smul, pow_two]
  have t12 : (c • ι 0) * (-(s • hyperbolic 0)) = (c * s) • ι 1 := by
    rw [mul_neg, smul_mul_assoc, mul_smul_comm, ι0_mul_hyperbolic0]
    simp only [smul_neg, neg_neg, smul_smul]
  have t21 : (s • ι 1) * (c • (1 : PGA)) = (c * s) • ι 1 := by
    rw [mul_smul_comm, smul_mul_assoc, mul_one, smul_smul, mul_comm]
  have t22 : (s • ι 1) * (-(s • hyperbolic 0)) = (s ^ 2) • ι 0 := by
    rw [mul_neg, smul_mul_assoc, mul_smul_comm, ι1_mul_hyperbolic0]
    simp only [smul_neg, neg_neg, smul_smul, pow_two]
  rw [t11, t12, t21, t22]
  module

private theorem sandwich_cs_ι1 (c s : ℝ) :
    (c • (1 : PGA) + s • hyperbolic 0) * ι 1 *
        (c • (1 : PGA) - s • hyperbolic 0) =
      (2 * c * s) • ι 0 + (c ^ 2 + s ^ 2) • ι 1 := by
  have hL : (c • (1 : PGA) + s • hyperbolic 0) * ι 1 = s • ι 0 + c • ι 1 := by
    rw [add_mul, smul_mul_assoc, one_mul, smul_mul_assoc, hyperbolic0_mul_ι1, add_comm]
  rw [hL, sub_eq_add_neg]
  have hexpand :
      (s • ι 0 + c • ι 1) * (c • (1 : PGA) + -(s • hyperbolic 0)) =
        (s • ι 0) * (c • (1 : PGA)) + (s • ι 0) * (-(s • hyperbolic 0)) +
          (c • ι 1) * (c • (1 : PGA)) + (c • ι 1) * (-(s • hyperbolic 0)) := by
    rw [add_mul, mul_add, mul_add]; abel
  rw [hexpand]
  have t11 : (s • ι 0) * (c • (1 : PGA)) = (c * s) • ι 0 := by
    rw [mul_smul_comm, smul_mul_assoc, mul_one, smul_smul, mul_comm]
  have t12 : (s • ι 0) * (-(s • hyperbolic 0)) = (s ^ 2) • ι 1 := by
    rw [mul_neg, smul_mul_assoc, mul_smul_comm, ι0_mul_hyperbolic0]
    simp only [smul_neg, neg_neg, smul_smul, pow_two]
  have t21 : (c • ι 1) * (c • (1 : PGA)) = (c ^ 2) • ι 1 := by
    rw [mul_smul_comm, smul_mul_assoc, mul_one, smul_smul, pow_two]
  have t22 : (c • ι 1) * (-(s • hyperbolic 0)) = (c * s) • ι 0 := by
    rw [mul_neg, smul_mul_assoc, mul_smul_comm, ι1_mul_hyperbolic0]
    simp only [smul_neg, neg_neg, smul_smul]
  rw [t11, t12, t21, t22]
  module

private theorem sandwich_cs_commuting (c s : ℝ) (v : PGA)
    (hv : Commute (hyperbolic 0) v)
    (hcs : c ^ 2 - s ^ 2 = 1) :
    (c • (1 : PGA) + s • hyperbolic 0) * v *
        (c • (1 : PGA) - s • hyperbolic 0) = v := by
  have hvB : v * hyperbolic 0 = hyperbolic 0 * v := hv.symm.eq
  have hvR : v * (c • (1 : PGA) - s • hyperbolic 0) =
      (c • (1 : PGA) - s • hyperbolic 0) * v := by
    simp only [sub_eq_add_neg, mul_add, add_mul, smul_mul_assoc, mul_smul_comm, one_mul,
      mul_neg, neg_mul, mul_one]
    rw [hvB]
  rw [mul_assoc, hvR, ← mul_assoc]
  have hprod : (c • (1 : PGA) + s • hyperbolic 0) *
      (c • (1 : PGA) - s • hyperbolic 0) = (1 : PGA) := by
    simp only [sub_eq_add_neg]
    have hexpand :
        (c • (1 : PGA) + s • hyperbolic 0) * (c • (1 : PGA) + -(s • hyperbolic 0)) =
          (c • (1 : PGA)) * (c • (1 : PGA)) + (c • (1 : PGA)) * (-(s • hyperbolic 0)) +
            (s • hyperbolic 0) * (c • (1 : PGA)) +
            (s • hyperbolic 0) * (-(s • hyperbolic 0)) := by
      rw [add_mul, mul_add, mul_add]; abel
    rw [hexpand]
    have a1 : (c • (1 : PGA)) * (c • (1 : PGA)) = (c * c) • (1 : PGA) := by
      rw [mul_smul_comm, smul_mul_assoc, mul_one, smul_smul]
    have a2 : (c • (1 : PGA)) * (-(s • hyperbolic 0)) = (-(c * s)) • hyperbolic 0 := by
      rw [mul_neg, smul_mul_assoc, one_mul, smul_smul, ← neg_smul]
    have a3 : (s • hyperbolic 0) * (c • (1 : PGA)) = (c * s) • hyperbolic 0 := by
      rw [mul_smul_comm, smul_mul_assoc, mul_one, smul_smul, mul_comm]
    have a4 : (s • hyperbolic 0) * (-(s • hyperbolic 0)) = (-(s * s)) • (1 : PGA) := by
      rw [mul_neg, smul_mul_assoc, mul_smul_comm, hyperbolic_sq, smul_smul, ← neg_smul]
    rw [a1, a2, a3, a4]
    have hmid : (-(c * s)) • hyperbolic 0 + (c * s) • hyperbolic 0 = (0 : PGA) := by
      rw [← add_smul, neg_add_cancel, zero_smul]
    have hreduce :
        (c * c) • (1 : PGA) + (-(c * s)) • hyperbolic 0 + (c * s) • hyperbolic 0 +
            (-(s * s)) • (1 : PGA) = (c * c - s * s) • (1 : PGA) := by
      calc
        (c * c) • (1 : PGA) + (-(c * s)) • hyperbolic 0 + (c * s) • hyperbolic 0 +
              (-(s * s)) • (1 : PGA)
            = (c * c) • (1 : PGA) + ((-(c * s)) • hyperbolic 0 + (c * s) • hyperbolic 0) +
                (-(s * s)) • (1 : PGA) := by
              ac_rfl
        _ = (c * c) • (1 : PGA) + 0 + (-(s * s)) • (1 : PGA) := by rw [hmid]
        _ = (c * c) • (1 : PGA) + (-(s * s)) • (1 : PGA) := by rw [add_zero]
        _ = (c * c - s * s) • (1 : PGA) := by
              simp [sub_eq_add_neg, add_smul]
    rw [hreduce]
    have hcs' : (c * c - s * s : ℝ) = 1 := by simpa [pow_two] using hcs
    rw [hcs', one_smul]
  rw [hprod, one_mul]

/-! ### Pure-boost sandwich on the frame -/

theorem sandwich_pureBoost_ι0 (φ : ℝ) :
    sandwich (rotorTorsion (pureBoost φ)) (ι 0) =
      Real.cosh φ • ι 0 + Real.sinh φ • ι 1 := by
  rw [sandwich, rotorTorsion_pureBoost_closed, reverse_cs, sandwich_cs_ι0, cosh_half_sq_add]
  have : 2 * Real.cosh (φ / 2) * Real.sinh (φ / 2) = Real.sinh φ := by
    have h := sinh_half_two φ
    ring_nf at h ⊢
    exact h
  rw [this]

theorem sandwich_pureBoost_ι1 (φ : ℝ) :
    sandwich (rotorTorsion (pureBoost φ)) (ι 1) =
      Real.sinh φ • ι 0 + Real.cosh φ • ι 1 := by
  rw [sandwich, rotorTorsion_pureBoost_closed, reverse_cs, sandwich_cs_ι1, cosh_half_sq_add]
  have : 2 * Real.cosh (φ / 2) * Real.sinh (φ / 2) = Real.sinh φ := by
    have h := sinh_half_two φ
    ring_nf at h ⊢
    exact h
  rw [this]

private theorem cosh_sq_sub_sinh_sq_half (φ : ℝ) :
    Real.cosh (φ / 2) ^ 2 - Real.sinh (φ / 2) ^ 2 = 1 :=
  Real.cosh_sq_sub_sinh_sq (φ / 2)

theorem sandwich_pureBoost_ι2 (φ : ℝ) :
    sandwich (rotorTorsion (pureBoost φ)) (ι 2) = ι 2 := by
  rw [sandwich, rotorTorsion_pureBoost_closed, reverse_cs]
  exact sandwich_cs_commuting _ _ _ hyperbolic0_commute_ι2 (cosh_sq_sub_sinh_sq_half φ)

theorem sandwich_pureBoost_ι3 (φ : ℝ) :
    sandwich (rotorTorsion (pureBoost φ)) (ι 3) = ι 3 := by
  rw [sandwich, rotorTorsion_pureBoost_closed, reverse_cs]
  exact sandwich_cs_commuting _ _ _ hyperbolic0_commute_ι3 (cosh_sq_sub_sinh_sq_half φ)

theorem sandwich_pureBoost_ι4 (φ : ℝ) :
    sandwich (rotorTorsion (pureBoost φ)) (ι e4Index) = ι e4Index := by
  rw [sandwich, rotorTorsion_pureBoost_closed, reverse_cs]
  exact sandwich_cs_commuting _ _ _ hyperbolic0_commute_ι4 (cosh_sq_sub_sinh_sq_half φ)

/-! ### Light-cone eigenvalues -/

theorem sandwich_pureBoost_lightlike_plus (φ : ℝ) :
    sandwich (rotorTorsion (pureBoost φ)) (ι 0 + ι 1) =
      Real.exp φ • (ι 0 + ι 1) := by
  rw [sandwich_add, sandwich_pureBoost_ι0, sandwich_pureBoost_ι1]
  have h : Real.cosh φ • ι 0 + Real.sinh φ • ι 1 +
      (Real.sinh φ • ι 0 + Real.cosh φ • ι 1) =
        (Real.cosh φ + Real.sinh φ) • (ι 0 + ι 1) := by
    module
  rw [h, cosh_add_sinh, smul_add]

theorem sandwich_pureBoost_lightlike_minus (φ : ℝ) :
    sandwich (rotorTorsion (pureBoost φ)) (ι 0 - ι 1) =
      Real.exp (-φ) • (ι 0 - ι 1) := by
  rw [sandwich_sub, sandwich_pureBoost_ι0, sandwich_pureBoost_ι1]
  have h : Real.cosh φ • ι 0 + Real.sinh φ • ι 1 -
      (Real.sinh φ • ι 0 + Real.cosh φ • ι 1) =
        (Real.cosh φ - Real.sinh φ) • (ι 0 - ι 1) := by
    module
  rw [h, cosh_sub_sinh]

/-- Circular closed form for a pure spatial rotation about axis 0 (`cyclic 0`). -/
theorem rotorTorsion_pureRotation_closed (θ : ℝ) :
    rotorTorsion ⟨fun _ => 0, fun a => if a = 0 then θ else 0⟩ =
      Real.cos (θ / 2) • (1 : PGA) + Real.sin (θ / 2) • cyclic 0 := by
  have hω : omegaTorsion ⟨fun _ => 0, fun a => if a = 0 then θ else 0⟩ =
      (θ / 2) • cyclic 0 := by
    simp [omegaTorsion, Fin.sum_univ_three]
  rw [rotorTorsion, hω, exp_of_sq_neg_one (cyclic_sq 0)]

end Sandwich

end DstDiophantine
