import DstDiophantine.Algebra.Motor
import DstDiophantine.Algebra.Amplification
import DstDiophantine.Algebra.Generators
import DstDiophantine.Algebra.Operations
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.BigOperators.Fin

/-!
# Geometric sandwich `M v M˜`

## Proved

* Algebraic laws: linearity in the second argument, composition, reverse intertwining.
* Unitary conjugation (`m * reverse m = 1`) is a geometric-product automorphism,
  hence preserves Clifford squares; in particular the Minkowski square of
  `minkowskiVector v` is unchanged.
* Closed-form pure-boost rotor and its action on the frame `{ι μ}` together with
  light-cone eigenvalues `e^{±φ}`.
* The pure-boost translator conjugation `sandwich_pureBoost_expTrans` is the closed-form
  instance of a general fact proved in `DstDiophantine.Algebra.MotorGroup`: *every*
  torsion rotor conjugates translators to translators and torsion rotors to torsion
  rotors, because the sandwich by `exp Ω` is `exp(ad Ω)` on any `ad Ω`-invariant span.

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

/-! ### Pure-boost sandwich on null translators -/

theorem sandwich_pureBoost_null0 (φ : ℝ) :
    sandwich (rotorTorsion (pureBoost φ)) (null 0) =
      Real.cosh φ • null 0 + Real.sinh φ • null 1 := by
  have hm := rotor_unitary (pureBoost φ)
  have hnull : null 0 = ι e4Index * ι 0 := by simp [null]
  rw [hnull, sandwich_mul hm, sandwich_pureBoost_ι4, sandwich_pureBoost_ι0, mul_add]
  simp only [mul_smul_comm]
  simp [null]

theorem sandwich_pureBoost_null1 (φ : ℝ) :
    sandwich (rotorTorsion (pureBoost φ)) (null 1) =
      Real.sinh φ • null 0 + Real.cosh φ • null 1 := by
  have hm := rotor_unitary (pureBoost φ)
  have hnull : null 1 = ι e4Index * ι 1 := by simp [null]
  rw [hnull, sandwich_mul hm, sandwich_pureBoost_ι4, sandwich_pureBoost_ι1, mul_add]
  simp only [mul_smul_comm]
  simp [null]

theorem sandwich_pureBoost_null2 (φ : ℝ) :
    sandwich (rotorTorsion (pureBoost φ)) (null 2) = null 2 := by
  have hm := rotor_unitary (pureBoost φ)
  have hnull : null 2 = ι e4Index * ι 2 := by simp [null]
  rw [hnull, sandwich_mul hm, sandwich_pureBoost_ι4, sandwich_pureBoost_ι2]

theorem sandwich_pureBoost_null3 (φ : ℝ) :
    sandwich (rotorTorsion (pureBoost φ)) (null 3) = null 3 := by
  have hm := rotor_unitary (pureBoost φ)
  have hnull : null 3 = ι e4Index * ι 3 := by simp [null]
  rw [hnull, sandwich_mul hm, sandwich_pureBoost_ι4, sandwich_pureBoost_ι3]

/-- Lorentz action on translation coefficients in the radial-boost plane. -/
noncomputable def boostConjLambda (φ : ℝ) (lam : Fin 4 → ℝ) : Fin 4 → ℝ
  | 0 => lam 0 * Real.cosh φ + lam 1 * Real.sinh φ
  | 1 => lam 0 * Real.sinh φ + lam 1 * Real.cosh φ
  | 2 => lam 2
  | 3 => lam 3

theorem sandwich_pureBoost_omegaTrans (φ : ℝ) (p : TransParams) :
    sandwich (rotorTorsion (pureBoost φ)) (omegaTrans p) =
      omegaTrans ⟨boostConjLambda φ p.lambda⟩ := by
  simp only [omegaTrans, sandwich_add, sandwich_smul, Fin.sum_univ_four]
  rw [sandwich_pureBoost_null0, sandwich_pureBoost_null1,
    sandwich_pureBoost_null2, sandwich_pureBoost_null3]
  simp only [boostConjLambda]
  module

theorem sandwich_pureBoost_expTrans (φ : ℝ) (p : TransParams) :
    sandwich (rotorTorsion (pureBoost φ)) (expTrans p) =
      expTrans ⟨boostConjLambda φ p.lambda⟩ := by
  have h1 : sandwich (rotorTorsion (pureBoost φ)) 1 = 1 := by
    simp [sandwich, rotor_unitary]
  rw [expTrans, sandwich_add, sandwich_pureBoost_omegaTrans, h1]
  rfl

theorem reverse_rotorTorsion_pureBoost_eq (φ : ℝ) :
    reverse (rotorTorsion (pureBoost φ)) = rotorTorsion (pureBoost (-φ)) := by
  rw [reverse_rotorTorsion_pureBoost, rotorTorsion_pureBoost_closed]
  have hc : Real.cosh (-φ / 2) = Real.cosh (φ / 2) := by
    rw [show -φ / 2 = -(φ / 2) by ring, Real.cosh_neg]
  have hs : Real.sinh (-φ / 2) = -Real.sinh (φ / 2) := by
    rw [show -φ / 2 = -(φ / 2) by ring, Real.sinh_neg]
  rw [hc, hs, sub_eq_add_neg, neg_smul]

theorem rotorTorsion_pureBoost_mul (φ ψ : ℝ) :
    rotorTorsion (pureBoost φ) * rotorTorsion (pureBoost ψ) =
      rotorTorsion (pureBoost (φ + ψ)) := by
  rw [rotorTorsion_pureBoost, rotorTorsion_pureBoost, rotorTorsion_pureBoost]
  have hc : Commute ((φ / 2) • hyperbolic 0) ((ψ / 2) • hyperbolic 0) :=
    ((Commute.refl (hyperbolic 0)).smul_left _).smul_right _
  rw [← exp_add_of_commute hc, ← add_smul]
  have hcoeff : φ / 2 + ψ / 2 = (φ + ψ) / 2 := by ring
  rw [hcoeff]

/-- Circular closed form for a pure spatial rotation about axis 0 (`cyclic 0`). -/
theorem rotorTorsion_pureRotation_closed (θ : ℝ) :
    rotorTorsion ⟨fun _ => 0, fun a => if a = 0 then θ else 0⟩ =
      Real.cos (θ / 2) • (1 : PGA) + Real.sin (θ / 2) • cyclic 0 := by
  have hω : omegaTorsion ⟨fun _ => 0, fun a => if a = 0 then θ else 0⟩ =
      (θ / 2) • cyclic 0 := by
    simp [omegaTorsion, Fin.sum_univ_three]
  rw [rotorTorsion, hω, exp_of_sq_neg_one (cyclic_sq 0)]

/-! ### Axis-1 pure rotation (`cyclic 1 = e₁ e₃`) on the frame and translators -/

theorem rotorTorsion_pureRotation1_closed (θ : ℝ) :
    rotorTorsion (pureRotation1 θ) =
      Real.cos (θ / 2) • (1 : PGA) + Real.sin (θ / 2) • cyclic 1 := by
  rw [rotorTorsion_pureRotation1, exp_of_sq_neg_one (cyclic_sq 1)]

private theorem reverse_cs_cyclic1 (c s : ℝ) :
    reverse (c • (1 : PGA) + s • cyclic 1) =
      c • (1 : PGA) - s • cyclic 1 := by
  rw [map_add, map_smul, map_smul, reverse.map_one, cyclic_reverse, smul_neg]
  abel

theorem reverse_rotorTorsion_pureRotation1 (θ : ℝ) :
    reverse (rotorTorsion (pureRotation1 θ)) =
      Real.cos (θ / 2) • (1 : PGA) - Real.sin (θ / 2) • cyclic 1 := by
  rw [rotorTorsion_pureRotation1_closed, reverse_cs_cyclic1]

private theorem cyclic1_mul_ι1 : cyclic 1 * ι 1 = -ι 3 := by
  dsimp [cyclic]
  have h31 : ι 3 * ι 1 = -(ι 1 * ι 3) := e_mul_anticomm (by decide)
  calc (ι 1 * ι 3) * ι 1
      = ι 1 * (ι 3 * ι 1) := by rw [mul_assoc]
    _ = ι 1 * (-(ι 1 * ι 3)) := by rw [h31]
    _ = -(ι 1 * ι 1 * ι 3) := by simp [mul_assoc]
    _ = -ι 3 := by simp [e1_sq]

private theorem cyclic1_mul_ι3 : cyclic 1 * ι 3 = ι 1 := by
  dsimp [cyclic]
  calc (ι 1 * ι 3) * ι 3
      = ι 1 * (ι 3 * ι 3) := by rw [mul_assoc]
    _ = ι 1 := by
        have : ι 3 * ι 3 = (1 : PGA) := by simp [e_sq, Q311_e5vec, w311]
        rw [this, mul_one]

private theorem ι1_mul_cyclic1 : ι 1 * cyclic 1 = ι 3 := by
  dsimp [cyclic]
  calc ι 1 * (ι 1 * ι 3)
      = (ι 1 * ι 1) * ι 3 := (mul_assoc _ _ _).symm
    _ = ι 3 := by simp [e1_sq]

private theorem ι3_mul_cyclic1 : ι 3 * cyclic 1 = -ι 1 := by
  dsimp [cyclic]
  have h31 : ι 3 * ι 1 = -(ι 1 * ι 3) := e_mul_anticomm (by decide)
  have h3sq : ι 3 * ι 3 = (1 : PGA) := by simp [e_sq, Q311_e5vec, w311]
  calc ι 3 * (ι 1 * ι 3)
      = (ι 3 * ι 1) * ι 3 := (mul_assoc _ _ _).symm
    _ = (-(ι 1 * ι 3)) * ι 3 := by rw [h31]
    _ = -(ι 1 * (ι 3 * ι 3)) := by simp [mul_assoc]
    _ = -ι 1 := by rw [h3sq, mul_one]

private theorem commute_cyclic1_ι {μ : Fin 5}
    (h1 : μ ≠ 1) (h3 : μ ≠ 3) : Commute (cyclic 1) (ι μ) := by
  dsimp [cyclic, Commute, SemiconjBy]
  have hμ1 : ι μ * ι 1 = -(ι 1 * ι μ) := e_mul_anticomm h1
  have h3μ : ι 3 * ι μ = -(ι μ * ι 3) := e_mul_anticomm h3.symm
  calc
    (ι 1 * ι 3) * ι μ = ι 1 * (ι 3 * ι μ) := by rw [mul_assoc]
    _ = ι 1 * (-(ι μ * ι 3)) := by rw [h3μ]
    _ = -(ι 1 * ι μ) * ι 3 := by simp [mul_assoc]
    _ = -(-(ι μ * ι 1)) * ι 3 := by rw [hμ1]; simp
    _ = ι μ * ι 1 * ι 3 := by simp [mul_assoc]
    _ = ι μ * (ι 1 * ι 3) := by rw [mul_assoc]

private theorem cyclic1_commute_ι0 : Commute (cyclic 1) (ι 0) :=
  commute_cyclic1_ι (by decide) (by decide)

private theorem cyclic1_commute_ι2 : Commute (cyclic 1) (ι 2) :=
  commute_cyclic1_ι (by decide) (by decide)

private theorem cyclic1_commute_ι4 : Commute (cyclic 1) (ι e4Index) :=
  commute_cyclic1_ι (by decide : (e4Index : Fin 5) ≠ 1)
    (by decide : (e4Index : Fin 5) ≠ 3)

private theorem cos_sq_add_sin_sq_half (θ : ℝ) :
    Real.cos (θ / 2) ^ 2 + Real.sin (θ / 2) ^ 2 = 1 := by
    simp [Real.cos_sq_add_sin_sq (θ / 2)]

private theorem sandwich_cs_cyclic1_commuting (c s : ℝ) (v : PGA)
    (hv : Commute (cyclic 1) v)
    (hcs : c ^ 2 + s ^ 2 = 1) :
    (c • (1 : PGA) + s • cyclic 1) * v *
        (c • (1 : PGA) - s • cyclic 1) = v := by
  have hvB : v * cyclic 1 = cyclic 1 * v := hv.symm.eq
  have hvR : v * (c • (1 : PGA) - s • cyclic 1) =
      (c • (1 : PGA) - s • cyclic 1) * v := by
    simp only [sub_eq_add_neg, mul_add, add_mul, smul_mul_assoc, mul_smul_comm, one_mul,
      mul_neg, neg_mul, mul_one]
    rw [hvB]
  rw [mul_assoc, hvR, ← mul_assoc]
  have hprod : (c • (1 : PGA) + s • cyclic 1) *
      (c • (1 : PGA) - s • cyclic 1) = (1 : PGA) := by
    simp only [sub_eq_add_neg]
    have hexpand :
        (c • (1 : PGA) + s • cyclic 1) * (c • (1 : PGA) + -(s • cyclic 1)) =
          (c • (1 : PGA)) * (c • (1 : PGA)) + (c • (1 : PGA)) * (-(s • cyclic 1)) +
            (s • cyclic 1) * (c • (1 : PGA)) +
            (s • cyclic 1) * (-(s • cyclic 1)) := by
      rw [add_mul, mul_add, mul_add]; abel
    rw [hexpand]
    have a1 : (c • (1 : PGA)) * (c • (1 : PGA)) = (c * c) • (1 : PGA) := by
      rw [mul_smul_comm, smul_mul_assoc, mul_one, smul_smul]
    have a2 : (c • (1 : PGA)) * (-(s • cyclic 1)) = (-(c * s)) • cyclic 1 := by
      rw [mul_neg, smul_mul_assoc, one_mul, smul_smul, ← neg_smul]
    have a3 : (s • cyclic 1) * (c • (1 : PGA)) = (c * s) • cyclic 1 := by
      rw [mul_smul_comm, smul_mul_assoc, mul_one, smul_smul, mul_comm]
    have a4 : (s • cyclic 1) * (-(s • cyclic 1)) = (s * s) • (1 : PGA) := by
      rw [mul_neg, smul_mul_assoc, mul_smul_comm, cyclic_sq, smul_smul, smul_neg,
        neg_neg]
    rw [a1, a2, a3, a4]
    have hmid : (-(c * s)) • cyclic 1 + (c * s) • cyclic 1 = (0 : PGA) := by
      rw [← add_smul, neg_add_cancel, zero_smul]
    have hreduce :
        (c * c) • (1 : PGA) + (-(c * s)) • cyclic 1 + (c * s) • cyclic 1 +
            (s * s) • (1 : PGA) = (c * c + s * s) • (1 : PGA) := by
      calc
        (c * c) • (1 : PGA) + (-(c * s)) • cyclic 1 + (c * s) • cyclic 1 +
              (s * s) • (1 : PGA)
            = (c * c) • (1 : PGA) + ((-(c * s)) • cyclic 1 + (c * s) • cyclic 1) +
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

private theorem sandwich_cs_cyclic1_ι1 (c s : ℝ) :
    (c • (1 : PGA) + s • cyclic 1) * ι 1 *
        (c • (1 : PGA) - s • cyclic 1) =
      (c ^ 2 - s ^ 2) • ι 1 + (-(2 * c * s)) • ι 3 := by
  have hL : (c • (1 : PGA) + s • cyclic 1) * ι 1 = c • ι 1 + s • (-ι 3) := by
    rw [add_mul, smul_mul_assoc, one_mul, smul_mul_assoc, cyclic1_mul_ι1]
  rw [hL, smul_neg, sub_eq_add_neg]
  have hexpand :
      (c • ι 1 + -(s • ι 3)) * (c • (1 : PGA) + -(s • cyclic 1)) =
        (c • ι 1) * (c • (1 : PGA)) + (c • ι 1) * (-(s • cyclic 1)) +
          (-(s • ι 3)) * (c • (1 : PGA)) + (-(s • ι 3)) * (-(s • cyclic 1)) := by
    rw [add_mul, mul_add, mul_add]; abel
  rw [hexpand]
  have t11 : (c • ι 1) * (c • (1 : PGA)) = (c ^ 2) • ι 1 := by
    rw [mul_smul_comm, smul_mul_assoc, mul_one, smul_smul, pow_two]
  have t12 : (c • ι 1) * (-(s • cyclic 1)) = (-(c * s)) • ι 3 := by
    rw [mul_neg, smul_mul_assoc, mul_smul_comm, ι1_mul_cyclic1, smul_smul, ← neg_smul]
  have t21 : (-(s • ι 3)) * (c • (1 : PGA)) = (-(c * s)) • ι 3 := by
    rw [neg_mul, smul_mul_assoc, mul_smul_comm, mul_one, smul_smul, mul_comm, neg_smul]
  have t22 : (-(s • ι 3)) * (-(s • cyclic 1)) = (-(s ^ 2)) • ι 1 := by
    rw [neg_mul_neg, smul_mul_smul, ι3_mul_cyclic1, pow_two, smul_neg, neg_smul]
  rw [t11, t12, t21, t22]
  module

private theorem sandwich_cs_cyclic1_ι3 (c s : ℝ) :
    (c • (1 : PGA) + s • cyclic 1) * ι 3 *
        (c • (1 : PGA) - s • cyclic 1) =
      (2 * c * s) • ι 1 + (c ^ 2 - s ^ 2) • ι 3 := by
  have hL : (c • (1 : PGA) + s • cyclic 1) * ι 3 = s • ι 1 + c • ι 3 := by
    rw [add_mul, smul_mul_assoc, one_mul, smul_mul_assoc, cyclic1_mul_ι3, add_comm]
  rw [hL, sub_eq_add_neg]
  have hexpand :
      (s • ι 1 + c • ι 3) * (c • (1 : PGA) + -(s • cyclic 1)) =
        (s • ι 1) * (c • (1 : PGA)) + (s • ι 1) * (-(s • cyclic 1)) +
          (c • ι 3) * (c • (1 : PGA)) + (c • ι 3) * (-(s • cyclic 1)) := by
    rw [add_mul, mul_add, mul_add]; abel
  rw [hexpand]
  have t11 : (s • ι 1) * (c • (1 : PGA)) = (c * s) • ι 1 := by
    rw [mul_smul_comm, smul_mul_assoc, mul_one, smul_smul, mul_comm]
  have t12 : (s • ι 1) * (-(s • cyclic 1)) = (-(s ^ 2)) • ι 3 := by
    rw [mul_neg, smul_mul_smul, ι1_mul_cyclic1, pow_two, neg_smul]
  have t21 : (c • ι 3) * (c • (1 : PGA)) = (c ^ 2) • ι 3 := by
    rw [mul_smul_comm, smul_mul_assoc, mul_one, smul_smul, pow_two]
  have t22 : (c • ι 3) * (-(s • cyclic 1)) = (c * s) • ι 1 := by
    rw [mul_neg, smul_mul_assoc, mul_smul_comm, ι3_mul_cyclic1]
    simp only [smul_neg, neg_neg, smul_smul]
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

theorem sandwich_pureRotation1_ι0 (θ : ℝ) :
    sandwich (rotorTorsion (pureRotation1 θ)) (ι 0) = ι 0 := by
  rw [sandwich, rotorTorsion_pureRotation1_closed, reverse_cs_cyclic1]
  exact sandwich_cs_cyclic1_commuting _ _ _ cyclic1_commute_ι0 (cos_sq_add_sin_sq_half θ)

theorem sandwich_pureRotation1_ι1 (θ : ℝ) :
    sandwich (rotorTorsion (pureRotation1 θ)) (ι 1) =
      Real.cos θ • ι 1 - Real.sin θ • ι 3 := by
  rw [sandwich, rotorTorsion_pureRotation1_closed, reverse_cs_cyclic1,
    sandwich_cs_cyclic1_ι1, cos_sq_sub_sin_sq_half, sin_half_two]
  module

theorem sandwich_pureRotation1_ι2 (θ : ℝ) :
    sandwich (rotorTorsion (pureRotation1 θ)) (ι 2) = ι 2 := by
  rw [sandwich, rotorTorsion_pureRotation1_closed, reverse_cs_cyclic1]
  exact sandwich_cs_cyclic1_commuting _ _ _ cyclic1_commute_ι2 (cos_sq_add_sin_sq_half θ)

theorem sandwich_pureRotation1_ι3 (θ : ℝ) :
    sandwich (rotorTorsion (pureRotation1 θ)) (ι 3) =
      Real.sin θ • ι 1 + Real.cos θ • ι 3 := by
  rw [sandwich, rotorTorsion_pureRotation1_closed, reverse_cs_cyclic1,
    sandwich_cs_cyclic1_ι3, cos_sq_sub_sin_sq_half, sin_half_two]

theorem sandwich_pureRotation1_ι4 (θ : ℝ) :
    sandwich (rotorTorsion (pureRotation1 θ)) (ι e4Index) = ι e4Index := by
  rw [sandwich, rotorTorsion_pureRotation1_closed, reverse_cs_cyclic1]
  exact sandwich_cs_cyclic1_commuting _ _ _ cyclic1_commute_ι4 (cos_sq_add_sin_sq_half θ)

theorem sandwich_pureRotation1_null0 (θ : ℝ) :
    sandwich (rotorTorsion (pureRotation1 θ)) (null 0) = null 0 := by
  have hm := rotor_unitary (pureRotation1 θ)
  have hnull : null 0 = ι e4Index * ι 0 := by simp [null]
  rw [hnull, sandwich_mul hm, sandwich_pureRotation1_ι4, sandwich_pureRotation1_ι0]

theorem sandwich_pureRotation1_null1 (θ : ℝ) :
    sandwich (rotorTorsion (pureRotation1 θ)) (null 1) =
      Real.cos θ • null 1 - Real.sin θ • null 3 := by
  have hm := rotor_unitary (pureRotation1 θ)
  have hnull : null 1 = ι e4Index * ι 1 := by simp [null]
  rw [hnull, sandwich_mul hm, sandwich_pureRotation1_ι4, sandwich_pureRotation1_ι1, mul_sub]
  simp only [mul_smul_comm]
  simp [null]

theorem sandwich_pureRotation1_null2 (θ : ℝ) :
    sandwich (rotorTorsion (pureRotation1 θ)) (null 2) = null 2 := by
  have hm := rotor_unitary (pureRotation1 θ)
  have hnull : null 2 = ι e4Index * ι 2 := by simp [null]
  rw [hnull, sandwich_mul hm, sandwich_pureRotation1_ι4, sandwich_pureRotation1_ι2]

theorem sandwich_pureRotation1_null3 (θ : ℝ) :
    sandwich (rotorTorsion (pureRotation1 θ)) (null 3) =
      Real.sin θ • null 1 + Real.cos θ • null 3 := by
  have hm := rotor_unitary (pureRotation1 θ)
  have hnull : null 3 = ι e4Index * ι 3 := by simp [null]
  rw [hnull, sandwich_mul hm, sandwich_pureRotation1_ι4, sandwich_pureRotation1_ι3, mul_add]
  simp only [mul_smul_comm]
  simp [null]

/-- Rotation in the `(N₁, N₃)` translation plane. -/
noncomputable def rotation1ConjLambda (θ : ℝ) (lam : Fin 4 → ℝ) : Fin 4 → ℝ
  | 0 => lam 0
  | 1 => lam 1 * Real.cos θ + lam 3 * Real.sin θ
  | 2 => lam 2
  | 3 => -lam 1 * Real.sin θ + lam 3 * Real.cos θ

theorem sandwich_pureRotation1_omegaTrans (θ : ℝ) (p : TransParams) :
    sandwich (rotorTorsion (pureRotation1 θ)) (omegaTrans p) =
      omegaTrans ⟨rotation1ConjLambda θ p.lambda⟩ := by
  simp only [omegaTrans, sandwich_add, sandwich_smul, Fin.sum_univ_four]
  rw [sandwich_pureRotation1_null0, sandwich_pureRotation1_null1,
    sandwich_pureRotation1_null2, sandwich_pureRotation1_null3]
  simp only [rotation1ConjLambda]
  module

theorem sandwich_pureRotation1_expTrans (θ : ℝ) (p : TransParams) :
    sandwich (rotorTorsion (pureRotation1 θ)) (expTrans p) =
      expTrans ⟨rotation1ConjLambda θ p.lambda⟩ := by
  have h1 : sandwich (rotorTorsion (pureRotation1 θ)) 1 = 1 := by
    simp [sandwich, rotor_unitary]
  rw [expTrans, sandwich_add, sandwich_pureRotation1_omegaTrans, h1]
  rfl

private theorem null1_eq_smul_null3_false {k : ℝ} (h : null 1 = k • null 3) :
    False := by
  have he4 : ι e4Index = -k • (ι e4Index * cyclic 1) := by
    have hL : null 1 * ι 1 = ι e4Index := by
      have hcast : Fin.castAdd 1 (1 : Fin 4) = (1 : Fin 5) := by decide
      rw [null, hcast, mul_assoc, e1_sq, mul_one]
    have hR : (k • null 3) * ι 1 = k • (ι e4Index * (ι 3 * ι 1)) := by
      simp [null, mul_assoc]
    have h31 : ι 3 * ι 1 = -cyclic 1 := by
      dsimp [cyclic]
      exact e_mul_anticomm (by decide)
    calc ι e4Index
        = null 1 * ι 1 := hL.symm
      _ = (k • null 3) * ι 1 := by rw [h]
      _ = k • (ι e4Index * (ι 3 * ι 1)) := hR
      _ = k • (ι e4Index * (-cyclic 1)) := by rw [h31]
      _ = -k • (ι e4Index * cyclic 1) := by simp [smul_neg, neg_smul, mul_neg]
  have hann : ι e4Index * (1 + k • cyclic 1) = 0 := by
    calc ι e4Index * (1 + k • cyclic 1)
        = ι e4Index + k • (ι e4Index * cyclic 1) := by
          simp [mul_add, mul_one]
      _ = -k • (ι e4Index * cyclic 1) + k • (ι e4Index * cyclic 1) := by
          nth_rw 1 [he4]
      _ = 0 := by rw [← add_smul, neg_add_cancel, zero_smul]
  have hprod : ι e4Index * (1 + k • cyclic 1) * (1 - k • cyclic 1) =
      (1 + k ^ 2) • ι e4Index := by
    have hsq : (k • cyclic 1) * (k • cyclic 1) = -(k ^ 2) • (1 : PGA) := by
      rw [smul_mul_smul, cyclic_sq, pow_two, smul_neg, neg_smul]
    have hdiff :
        (1 + k • cyclic 1) * (1 - k • cyclic 1) =
          (1 + k ^ 2 : ℝ) • (1 : PGA) := by
      have hexp :
          (1 + k • cyclic 1) * (1 - k • cyclic 1) =
            (1 : PGA) - (k • cyclic 1) * (k • cyclic 1) := by
        simp only [sub_eq_add_neg, mul_add, add_mul, one_mul, mul_one, mul_neg]
        abel
      rw [hexp, hsq, sub_eq_add_neg, neg_smul, neg_neg]
      calc (1 : PGA) + k ^ 2 • (1 : PGA)
          = (1 : ℝ) • (1 : PGA) + k ^ 2 • (1 : PGA) := by rw [one_smul]
        _ = (1 + k ^ 2) • (1 : PGA) := (add_smul (1 : ℝ) (k ^ 2) _).symm
    have hscal :
        ι e4Index * ((1 + k ^ 2 : ℝ) • (1 : PGA)) = (1 + k ^ 2) • ι e4Index := by
      rw [mul_smul_comm, mul_one]
    rw [mul_assoc, hdiff, hscal]
  have : (1 + k ^ 2) • ι e4Index = 0 := by
    rw [← hprod, hann, zero_mul]
  have hk : (1 + k ^ 2 : ℝ) ≠ 0 :=
    (add_pos_of_pos_of_nonneg (by norm_num : (0 : ℝ) < 1) (sq_nonneg k)).ne'
  exact ι_e4_ne_zero ((smul_eq_zero.mp this).resolve_left hk)

/-- Axis-1 rotation moves `N₃` in the `(N₁,N₃)` plane; a pure boost of axis 0
leaves `N₃` inert. -/
theorem sandwich_pureRotation1_null3_ne_of_sin {θ : ℝ} (hsin : Real.sin θ ≠ 0) :
    sandwich (rotorTorsion (pureRotation1 θ)) (null 3) ≠ null 3 := by
  intro h
  rw [sandwich_pureRotation1_null3] at h
  have hlin : Real.sin θ • null 1 = (1 - Real.cos θ) • null 3 := by
    have : Real.sin θ • null 1 + Real.cos θ • null 3 = (1 : ℝ) • null 3 := by
      simpa [one_smul] using h
    have := congrArg (fun z => z - Real.cos θ • null 3) this
    simpa [add_sub_cancel_right, sub_smul] using this
  have hN : null 1 = ((1 - Real.cos θ) / Real.sin θ) • null 3 := by
    have h' := congrArg (fun z => (Real.sin θ)⁻¹ • z) hlin
    simpa [smul_smul, inv_mul_cancel₀ hsin, one_smul, ← div_eq_inv_mul] using h'
  exact null1_eq_smul_null3_false hN

end Sandwich

end DstDiophantine
