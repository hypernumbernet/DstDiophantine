import DstDiophantine.Algebra.Generators
import DstDiophantine.Algebra.Cl31
import Mathlib.LinearAlgebra.CliffordAlgebra.Basic

/-!
# Reverse, dual, and dagger operations

The dual map `X ↦ X · i` uses the Cl(3,1) pseudoscalar `i = e₀e₁e₂e₃`.

## Paper §2 coverage

* Proved: `i² = -1`, grade-1 Minkowski vectors anticommute with `i`,
  Minkowski vectors `X` satisfy `X² = Q(X)`, and `(X i)² = X²`.
* Proved: dual of a pure time vector flips sign onto the spatial trivector
  (paper: `(ct j) i = -ct k`).
* Rejected elsewhere: null-bivector ideal closure under dual (`dual_null`).
-/

namespace DstDiophantine

open PGA Generators CliffordAlgebra

namespace Operations

/-- Pseudoscalar `i = e₀e₁e₂e₃` of the embedded Cl(3,1) subalgebra. -/
noncomputable def pseudoscalar : PGA :=
  ι 0 * ι 1 * ι 2 * ι 3

/-- Biquaternion duality `X ↦ X i`. -/
noncomputable def dual (x : PGA) : PGA :=
  x * pseudoscalar

/-- Right multiplication by the pseudoscalar is a right-module morphism. -/
theorem dual_mul (x y : PGA) : dual (x * y) = x * dual y := by
  simp [dual, mul_assoc]

/-- Paper: the Cl(3,1) pseudoscalar satisfies `i² = -1`. -/
theorem pseudoscalar_sq : pseudoscalar * pseudoscalar = (-1 : PGA) := by
  dsimp [pseudoscalar]
  -- `(e₀e₁e₂e₃)² = e₀e₁e₂e₃ e₀e₁e₂e₃`; move each factor through with anticommutators.
  have h30 : ι 3 * ι 0 = -(ι 0 * ι 3) := e_mul_anticomm (by decide)
  have h31 : ι 3 * ι 1 = -(ι 1 * ι 3) := e_mul_anticomm (by decide)
  have h32 : ι 3 * ι 2 = -(ι 2 * ι 3) := e_mul_anticomm (by decide)
  have h20 : ι 2 * ι 0 = -(ι 0 * ι 2) := e_mul_anticomm (by decide)
  have h21 : ι 2 * ι 1 = -(ι 1 * ι 2) := e_mul_anticomm (by decide)
  have h10 : ι 1 * ι 0 = -(ι 0 * ι 1) := e_mul_anticomm (by decide)
  have e0s : ι 0 * ι 0 = algebraMap ℝ PGA (-1 : ℝ) := e0_sq
  have e1s : ι 1 * ι 1 = (1 : PGA) := e1_sq
  have e2s : ι 2 * ι 2 = (1 : PGA) := by simpa [Q311_e5vec, w311] using e_sq (2 : Fin 5)
  have e3s : ι 3 * ι 3 = (1 : PGA) := by simpa [Q311_e5vec, w311] using e_sq (3 : Fin 5)
  calc ι 0 * ι 1 * ι 2 * ι 3 * (ι 0 * ι 1 * ι 2 * ι 3)
      = ι 0 * ι 1 * ι 2 * (ι 3 * ι 0) * ι 1 * ι 2 * ι 3 := by simp [mul_assoc]
    _ = ι 0 * ι 1 * ι 2 * (-(ι 0 * ι 3)) * ι 1 * ι 2 * ι 3 := by rw [h30]
    _ = -(ι 0 * ι 1 * ι 2 * ι 0 * ι 3 * ι 1 * ι 2 * ι 3) := by simp [mul_neg, mul_assoc]
    _ = -(ι 0 * ι 1 * (ι 2 * ι 0) * ι 3 * ι 1 * ι 2 * ι 3) := by simp [mul_assoc]
    _ = -(ι 0 * ι 1 * (-(ι 0 * ι 2)) * ι 3 * ι 1 * ι 2 * ι 3) := by rw [h20]
    _ = ι 0 * ι 1 * ι 0 * ι 2 * ι 3 * ι 1 * ι 2 * ι 3 := by simp [mul_neg, mul_assoc]
    _ = ι 0 * (ι 1 * ι 0) * ι 2 * ι 3 * ι 1 * ι 2 * ι 3 := by simp [mul_assoc]
    _ = ι 0 * (-(ι 0 * ι 1)) * ι 2 * ι 3 * ι 1 * ι 2 * ι 3 := by rw [h10]
    _ = -(ι 0 * ι 0) * ι 1 * ι 2 * ι 3 * ι 1 * ι 2 * ι 3 := by simp [mul_neg, mul_assoc]
    _ = -algebraMap ℝ PGA (-1 : ℝ) * ι 1 * ι 2 * ι 3 * ι 1 * ι 2 * ι 3 := by rw [e0s]
    _ = ι 1 * ι 2 * ι 3 * ι 1 * ι 2 * ι 3 := by simp [map_neg, mul_assoc]
    _ = ι 1 * ι 2 * (ι 3 * ι 1) * ι 2 * ι 3 := by simp [mul_assoc]
    _ = ι 1 * ι 2 * (-(ι 1 * ι 3)) * ι 2 * ι 3 := by rw [h31]
    _ = -(ι 1 * ι 2 * ι 1 * ι 3 * ι 2 * ι 3) := by simp [mul_neg, mul_assoc]
    _ = -(ι 1 * (ι 2 * ι 1) * ι 3 * ι 2 * ι 3) := by simp [mul_assoc]
    _ = -(ι 1 * (-(ι 1 * ι 2)) * ι 3 * ι 2 * ι 3) := by rw [h21]
    _ = ι 1 * ι 1 * ι 2 * ι 3 * ι 2 * ι 3 := by simp [mul_neg, mul_assoc]
    _ = ι 2 * ι 3 * ι 2 * ι 3 := by simp [e1s, mul_assoc]
    _ = ι 2 * (ι 3 * ι 2) * ι 3 := by simp [mul_assoc]
    _ = ι 2 * (-(ι 2 * ι 3)) * ι 3 := by rw [h32]
    _ = -(ι 2 * ι 2) * ι 3 * ι 3 := by simp [mul_neg, mul_assoc]
    _ = -((1 : PGA) * (1 : PGA)) := by simp [e2s, e3s]
    _ = (-1 : PGA) := by simp

private theorem e2_sq : ι 2 * ι 2 = (1 : PGA) := by
  simpa [Q311_e5vec, w311] using e_sq (2 : Fin 5)

private theorem e3_sq : ι 3 * ι 3 = (1 : PGA) := by
  simpa [Q311_e5vec, w311] using e_sq (3 : Fin 5)

private theorem ι0_mul_pseudoscalar :
    ι 0 * pseudoscalar = -(ι 1 * ι 2 * ι 3) := by
  dsimp [pseudoscalar]
  calc ι 0 * (ι 0 * ι 1 * ι 2 * ι 3)
      = (ι 0 * ι 0) * ι 1 * ι 2 * ι 3 := by simp [mul_assoc]
    _ = algebraMap ℝ PGA (-1 : ℝ) * ι 1 * ι 2 * ι 3 := by rw [e0_sq]
    _ = -(ι 1 * ι 2 * ι 3) := by simp [map_neg, mul_assoc]

private theorem pseudoscalar_mul_ι0 :
    pseudoscalar * ι 0 = ι 1 * ι 2 * ι 3 := by
  dsimp [pseudoscalar]
  have h10 : ι 1 * ι 0 = -(ι 0 * ι 1) := e_mul_anticomm (by decide)
  have h20 : ι 2 * ι 0 = -(ι 0 * ι 2) := e_mul_anticomm (by decide)
  have h30 : ι 3 * ι 0 = -(ι 0 * ι 3) := e_mul_anticomm (by decide)
  calc ι 0 * ι 1 * ι 2 * ι 3 * ι 0
      = ι 0 * ι 1 * ι 2 * (ι 3 * ι 0) := by simp [mul_assoc]
    _ = ι 0 * ι 1 * ι 2 * (-(ι 0 * ι 3)) := by rw [h30]
    _ = -(ι 0 * ι 1 * (ι 2 * ι 0) * ι 3) := by simp [mul_neg, mul_assoc]
    _ = -(ι 0 * ι 1 * (-(ι 0 * ι 2)) * ι 3) := by rw [h20]
    _ = ι 0 * (ι 1 * ι 0) * ι 2 * ι 3 := by simp [mul_neg, mul_assoc]
    _ = ι 0 * (-(ι 0 * ι 1)) * ι 2 * ι 3 := by rw [h10]
    _ = -(ι 0 * ι 0) * ι 1 * ι 2 * ι 3 := by simp [mul_neg, mul_assoc]
    _ = ι 1 * ι 2 * ι 3 := by simp [e0_sq, map_neg, mul_assoc]

private theorem ι1_mul_pseudoscalar :
    ι 1 * pseudoscalar = -(ι 0 * ι 2 * ι 3) := by
  dsimp [pseudoscalar]
  calc ι 1 * (ι 0 * ι 1 * ι 2 * ι 3)
      = (ι 1 * ι 0) * ι 1 * ι 2 * ι 3 := by simp [mul_assoc]
    _ = (-(ι 0 * ι 1)) * ι 1 * ι 2 * ι 3 := by
        rw [e_mul_anticomm (by decide : (1 : Fin 5) ≠ 0)]
    _ = -(ι 0 * (ι 1 * ι 1) * ι 2 * ι 3) := by simp [mul_assoc]
    _ = -(ι 0 * ι 2 * ι 3) := by simp [e1_sq]

private theorem pseudoscalar_mul_ι1 :
    pseudoscalar * ι 1 = ι 0 * ι 2 * ι 3 := by
  dsimp [pseudoscalar]
  have h21 : ι 2 * ι 1 = -(ι 1 * ι 2) := e_mul_anticomm (by decide)
  have h31 : ι 3 * ι 1 = -(ι 1 * ι 3) := e_mul_anticomm (by decide)
  calc ι 0 * ι 1 * ι 2 * ι 3 * ι 1
      = ι 0 * ι 1 * ι 2 * (ι 3 * ι 1) := by simp [mul_assoc]
    _ = ι 0 * ι 1 * ι 2 * (-(ι 1 * ι 3)) := by rw [h31]
    _ = -(ι 0 * ι 1 * (ι 2 * ι 1) * ι 3) := by simp [mul_neg, mul_assoc]
    _ = -(ι 0 * ι 1 * (-(ι 1 * ι 2)) * ι 3) := by rw [h21]
    _ = ι 0 * (ι 1 * ι 1) * ι 2 * ι 3 := by simp [mul_neg, mul_assoc]
    _ = ι 0 * ι 2 * ι 3 := by simp [e1_sq]

private theorem ι2_mul_pseudoscalar :
    ι 2 * pseudoscalar = ι 0 * ι 1 * ι 3 := by
  dsimp [pseudoscalar]
  have h20 : ι 2 * ι 0 = -(ι 0 * ι 2) := e_mul_anticomm (by decide)
  have h21 : ι 2 * ι 1 = -(ι 1 * ι 2) := e_mul_anticomm (by decide)
  calc ι 2 * (ι 0 * ι 1 * ι 2 * ι 3)
      = (ι 2 * ι 0) * ι 1 * ι 2 * ι 3 := by simp [mul_assoc]
    _ = (-(ι 0 * ι 2)) * ι 1 * ι 2 * ι 3 := by rw [h20]
    _ = -(ι 0 * (ι 2 * ι 1) * ι 2 * ι 3) := by simp [mul_assoc]
    _ = -(ι 0 * (-(ι 1 * ι 2)) * ι 2 * ι 3) := by rw [h21]
    _ = ι 0 * ι 1 * (ι 2 * ι 2) * ι 3 := by simp [mul_assoc]
    _ = ι 0 * ι 1 * ι 3 := by simp [e2_sq]

private theorem pseudoscalar_mul_ι2 :
    pseudoscalar * ι 2 = -(ι 0 * ι 1 * ι 3) := by
  dsimp [pseudoscalar]
  have h32 : ι 3 * ι 2 = -(ι 2 * ι 3) := e_mul_anticomm (by decide)
  calc ι 0 * ι 1 * ι 2 * ι 3 * ι 2
      = ι 0 * ι 1 * ι 2 * (ι 3 * ι 2) := by simp [mul_assoc]
    _ = ι 0 * ι 1 * ι 2 * (-(ι 2 * ι 3)) := by rw [h32]
    _ = -(ι 0 * ι 1 * (ι 2 * ι 2) * ι 3) := by simp [mul_assoc]
    _ = -(ι 0 * ι 1 * ι 3) := by simp [e2_sq]

private theorem ι3_mul_pseudoscalar :
    ι 3 * pseudoscalar = -(ι 0 * ι 1 * ι 2) := by
  dsimp [pseudoscalar]
  have h30 : ι 3 * ι 0 = -(ι 0 * ι 3) := e_mul_anticomm (by decide)
  have h31 : ι 3 * ι 1 = -(ι 1 * ι 3) := e_mul_anticomm (by decide)
  have h32 : ι 3 * ι 2 = -(ι 2 * ι 3) := e_mul_anticomm (by decide)
  calc ι 3 * (ι 0 * ι 1 * ι 2 * ι 3)
      = (ι 3 * ι 0) * ι 1 * ι 2 * ι 3 := by simp [mul_assoc]
    _ = (-(ι 0 * ι 3)) * ι 1 * ι 2 * ι 3 := by rw [h30]
    _ = -(ι 0 * (ι 3 * ι 1) * ι 2 * ι 3) := by simp [mul_assoc]
    _ = -(ι 0 * (-(ι 1 * ι 3)) * ι 2 * ι 3) := by rw [h31]
    _ = ι 0 * ι 1 * (ι 3 * ι 2) * ι 3 := by simp [mul_neg, mul_assoc]
    _ = ι 0 * ι 1 * (-(ι 2 * ι 3)) * ι 3 := by rw [h32]
    _ = -(ι 0 * ι 1 * ι 2 * (ι 3 * ι 3)) := by simp [mul_neg, mul_assoc]
    _ = -(ι 0 * ι 1 * ι 2) := by simp [e3_sq]

private theorem pseudoscalar_mul_ι3 :
    pseudoscalar * ι 3 = ι 0 * ι 1 * ι 2 := by
  dsimp [pseudoscalar]
  simp [mul_assoc, e3_sq]

/-- Grade-1 Minkowski basis vectors anticommute with the pseudoscalar. -/
theorem ι_anticomm_pseudoscalar (μ : Fin 4) :
    ι (Fin.castAdd 1 μ) * pseudoscalar = -(pseudoscalar * ι (Fin.castAdd 1 μ)) := by
  fin_cases μ
  · change ι 0 * pseudoscalar = -(pseudoscalar * ι 0)
    rw [ι0_mul_pseudoscalar, pseudoscalar_mul_ι0]
  · change ι 1 * pseudoscalar = -(pseudoscalar * ι 1)
    rw [ι1_mul_pseudoscalar, pseudoscalar_mul_ι1]
  · change ι 2 * pseudoscalar = -(pseudoscalar * ι 2)
    rw [ι2_mul_pseudoscalar, pseudoscalar_mul_ι2]; simp
  · change ι 3 * pseudoscalar = -(pseudoscalar * ι 3)
    rw [ι3_mul_pseudoscalar, pseudoscalar_mul_ι3]

/-- Minkowski spacetime vector in the Cl(3,1) subalgebra of `G(3,1,1)`. -/
noncomputable def minkowskiVector (v : Fin 4 → ℝ) : PGA :=
  CliffordAlgebra.ι Q311 (extend4 v)

theorem minkowskiVector_eq_sum (v : Fin 4 → ℝ) :
    minkowskiVector v = ∑ μ : Fin 4, (v μ) • ι (Fin.castAdd 1 μ) := by
  have hv : extend4 v = ∑ μ : Fin 4, (v μ) • e5vec (Fin.castAdd 1 μ) := by
    funext i
    fin_cases i <;> simp [extend4, e5vec, Pi.single, Fin.sum_univ_four]
  simp only [minkowskiVector, hv, map_sum, map_smul, PGA.ι]

theorem minkowskiVector_sq (v : Fin 4 → ℝ) :
    minkowskiVector v * minkowskiVector v = algebraMap ℝ PGA (Q31 v) := by
  simp [minkowskiVector, ι_sq_scalar, Q311_extend4]

theorem Q31_eq_minkowskiDot (v : Fin 4 → ℝ) : Q31 v = minkowskiDot v := by
  simp only [Q31, QuadraticMap.weightedSumSquares_apply, w31, minkowskiDot, Fin.sum_univ_four]
  ring

theorem minkowskiVector_anticomm_pseudoscalar (v : Fin 4 → ℝ) :
    minkowskiVector v * pseudoscalar = -(pseudoscalar * minkowskiVector v) := by
  rw [minkowskiVector_eq_sum]
  simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm]
  rw [← Finset.sum_neg_distrib]
  congr 1
  ext μ
  rw [ι_anticomm_pseudoscalar μ, smul_neg]

/-- Paper: dual preserves the Minkowski square, `(X i)² = X²`. -/
theorem dual_minkowskiVector_sq (v : Fin 4 → ℝ) :
    dual (minkowskiVector v) * dual (minkowskiVector v) =
      minkowskiVector v * minkowskiVector v := by
  set X := minkowskiVector v
  have hanti : pseudoscalar * X = -(X * pseudoscalar) := by
    simpa [neg_eq_iff_eq_neg] using (minkowskiVector_anticomm_pseudoscalar v).symm
  calc dual X * dual X
      = X * pseudoscalar * (X * pseudoscalar) := by simp [dual]
    _ = X * (pseudoscalar * X) * pseudoscalar := by simp [mul_assoc]
    _ = X * (-(X * pseudoscalar)) * pseudoscalar := by rw [hanti]
    _ = -(X * X) * (pseudoscalar * pseudoscalar) := by simp [mul_neg, mul_assoc]
    _ = -(X * X) * (-1 : PGA) := by rw [pseudoscalar_sq]
    _ = X * X := by simp

/-- Paper: `(ct · e₀) i = -ct · (e₁e₂e₃)` (time arrow reversal). -/
theorem dual_time (c : ℝ) :
    dual (c • ι 0) = -((c : ℝ) • (ι 1 * ι 2 * ι 3)) := by
  simp [dual, ι0_mul_pseudoscalar, smul_neg]

theorem dual_hyperbolic (a : Fin 3) : dual (hyperbolic a) = -cyclic a := by
  fin_cases a
  · -- `(e₀e₁)·i = e₂e₃ = -e₃e₂`
    dsimp [dual, hyperbolic, cyclic, pseudoscalar]
    have hsq : (ι 0 * ι 1) * (ι 0 * ι 1) = 1 := by
      simpa [hyperbolic] using hyperbolic_sq (0 : Fin 3)
    calc ι 0 * ι 1 * (ι 0 * ι 1 * ι 2 * ι 3)
        = ((ι 0 * ι 1) * (ι 0 * ι 1)) * (ι 2 * ι 3) := by simp [mul_assoc]
      _ = (1 : PGA) * (ι 2 * ι 3) := by rw [hsq]
      _ = ι 2 * ι 3 := by simp
      _ = -(ι 3 * ι 2) := (e_mul_anticomm (by decide : (2 : Fin 5) ≠ 3))
  · -- `(e₀e₂)·i = -e₁e₃`
    dsimp [dual, hyperbolic, cyclic, pseudoscalar]
    calc ι 0 * ι 2 * (ι 0 * ι 1 * ι 2 * ι 3)
        = ι 0 * (ι 2 * ι 0) * ι 1 * ι 2 * ι 3 := by simp [mul_assoc]
      _ = ι 0 * (-(ι 0 * ι 2)) * ι 1 * ι 2 * ι 3 := by
          rw [e_mul_anticomm (by decide : (2 : Fin 5) ≠ 0)]
      _ = -(ι 0 * ι 0) * ι 2 * ι 1 * ι 2 * ι 3 := by simp [mul_neg, mul_assoc]
      _ = -algebraMap ℝ PGA (-1) * ι 2 * ι 1 * ι 2 * ι 3 := by rw [e0_sq]
      _ = ι 2 * ι 1 * ι 2 * ι 3 := by simp [map_neg, mul_assoc]
      _ = ι 2 * (ι 1 * ι 2) * ι 3 := by simp [mul_assoc]
      _ = ι 2 * (-(ι 2 * ι 1)) * ι 3 := by
          rw [e_mul_anticomm (by decide : (1 : Fin 5) ≠ 2)]
      _ = -((ι 2 * ι 2) * ι 1 * ι 3) := by simp [mul_neg, mul_assoc]
      _ = -(ι 1 * ι 3) := by simp [e2_sq]
  · -- `(e₀e₃)·i = -e₂e₁`
    dsimp [dual, hyperbolic, cyclic, pseudoscalar]
    calc ι 0 * ι 3 * (ι 0 * ι 1 * ι 2 * ι 3)
        = ι 0 * (ι 3 * ι 0) * ι 1 * ι 2 * ι 3 := by simp [mul_assoc]
      _ = ι 0 * (-(ι 0 * ι 3)) * ι 1 * ι 2 * ι 3 := by
          rw [e_mul_anticomm (by decide : (3 : Fin 5) ≠ 0)]
      _ = -(ι 0 * ι 0) * ι 3 * ι 1 * ι 2 * ι 3 := by simp [mul_neg, mul_assoc]
      _ = -algebraMap ℝ PGA (-1) * ι 3 * ι 1 * ι 2 * ι 3 := by rw [e0_sq]
      _ = ι 3 * ι 1 * ι 2 * ι 3 := by simp [map_neg, mul_assoc]
      _ = ι 3 * ι 1 * (ι 2 * ι 3) := by simp [mul_assoc]
      _ = ι 3 * ι 1 * (-(ι 3 * ι 2)) := by
          rw [e_mul_anticomm (by decide : (2 : Fin 5) ≠ 3)]
      _ = -(ι 3 * (ι 1 * ι 3) * ι 2) := by simp [mul_neg, mul_assoc]
      _ = -(ι 3 * (-(ι 3 * ι 1)) * ι 2) := by
          rw [e_mul_anticomm (by decide : (1 : Fin 5) ≠ 3)]
      _ = (ι 3 * ι 3) * ι 1 * ι 2 := by simp [mul_neg, mul_assoc]
      _ = ι 1 * ι 2 := by simp [e3_sq]
      _ = -(ι 2 * ι 1) := (e_mul_anticomm (by decide : (1 : Fin 5) ≠ 2))

theorem dual_cyclic (a : Fin 3) : dual (cyclic a) = hyperbolic a := by
  fin_cases a
  · -- `(e₃e₂)·i = e₀e₁`
    dsimp [dual, cyclic, hyperbolic, pseudoscalar]
    calc ι 3 * ι 2 * (ι 0 * ι 1 * ι 2 * ι 3)
        = ι 3 * (ι 2 * ι 0) * ι 1 * ι 2 * ι 3 := by simp [mul_assoc]
      _ = ι 3 * (-(ι 0 * ι 2)) * ι 1 * ι 2 * ι 3 := by
          rw [e_mul_anticomm (by decide : (2 : Fin 5) ≠ 0)]
      _ = -(ι 3 * ι 0) * ι 2 * ι 1 * ι 2 * ι 3 := by simp [mul_neg, mul_assoc]
      _ = -(-(ι 0 * ι 3)) * ι 2 * ι 1 * ι 2 * ι 3 := by
          rw [e_mul_anticomm (by decide : (3 : Fin 5) ≠ 0)]
      _ = ι 0 * ι 3 * ι 2 * ι 1 * ι 2 * ι 3 := by simp [mul_assoc]
      _ = ι 0 * ι 3 * (ι 2 * ι 1) * ι 2 * ι 3 := by simp [mul_assoc]
      _ = ι 0 * ι 3 * (-(ι 1 * ι 2)) * ι 2 * ι 3 := by
          rw [e_mul_anticomm (by decide : (2 : Fin 5) ≠ 1)]
      _ = -(ι 0 * ι 3 * ι 1 * (ι 2 * ι 2) * ι 3) := by simp [mul_neg, mul_assoc]
      _ = -(ι 0 * ι 3 * ι 1 * ι 3) := by simp [e2_sq]
      _ = -(ι 0 * (ι 3 * ι 1) * ι 3) := by simp [mul_assoc]
      _ = -(ι 0 * (-(ι 1 * ι 3)) * ι 3) := by
          rw [e_mul_anticomm (by decide : (3 : Fin 5) ≠ 1)]
      _ = ι 0 * ι 1 * (ι 3 * ι 3) := by simp [mul_neg, mul_assoc]
      _ = ι 0 * ι 1 := by simp [e3_sq]
  · -- `(e₁e₃)·i = e₀e₂`
    dsimp [dual, cyclic, hyperbolic, pseudoscalar]
    calc ι 1 * ι 3 * (ι 0 * ι 1 * ι 2 * ι 3)
        = ι 1 * (ι 3 * ι 0) * ι 1 * ι 2 * ι 3 := by simp [mul_assoc]
      _ = ι 1 * (-(ι 0 * ι 3)) * ι 1 * ι 2 * ι 3 := by
          rw [e_mul_anticomm (by decide : (3 : Fin 5) ≠ 0)]
      _ = -(ι 1 * ι 0) * ι 3 * ι 1 * ι 2 * ι 3 := by simp [mul_neg, mul_assoc]
      _ = -(-(ι 0 * ι 1)) * ι 3 * ι 1 * ι 2 * ι 3 := by
          rw [e_mul_anticomm (by decide : (1 : Fin 5) ≠ 0)]
      _ = ι 0 * ι 1 * ι 3 * ι 1 * ι 2 * ι 3 := by simp [mul_assoc]
      _ = ι 0 * ι 1 * (ι 3 * ι 1) * ι 2 * ι 3 := by simp [mul_assoc]
      _ = ι 0 * ι 1 * (-(ι 1 * ι 3)) * ι 2 * ι 3 := by
          rw [e_mul_anticomm (by decide : (3 : Fin 5) ≠ 1)]
      _ = -(ι 0 * (ι 1 * ι 1) * ι 3 * ι 2 * ι 3) := by simp [mul_neg, mul_assoc]
      _ = -(ι 0 * ι 3 * ι 2 * ι 3) := by simp [e1_sq]
      _ = -(ι 0 * ι 3 * (ι 2 * ι 3)) := by simp [mul_assoc]
      _ = -(ι 0 * ι 3 * (-(ι 3 * ι 2))) := by
          rw [e_mul_anticomm (by decide : (2 : Fin 5) ≠ 3)]
      _ = ι 0 * (ι 3 * ι 3) * ι 2 := by simp [mul_neg, mul_assoc]
      _ = ι 0 * ι 2 := by simp [e3_sq]
  · -- `(e₂e₁)·i = e₀e₃`
    dsimp [dual, cyclic, hyperbolic, pseudoscalar]
    calc ι 2 * ι 1 * (ι 0 * ι 1 * ι 2 * ι 3)
        = ι 2 * (ι 1 * ι 0) * ι 1 * ι 2 * ι 3 := by simp [mul_assoc]
      _ = ι 2 * (-(ι 0 * ι 1)) * ι 1 * ι 2 * ι 3 := by
          rw [e_mul_anticomm (by decide : (1 : Fin 5) ≠ 0)]
      _ = -(ι 2 * ι 0 * (ι 1 * ι 1) * ι 2 * ι 3) := by simp [mul_neg, mul_assoc]
      _ = -(ι 2 * ι 0 * ι 2 * ι 3) := by simp [e1_sq]
      _ = -((ι 2 * ι 0) * ι 2 * ι 3) := by simp [mul_assoc]
      _ = -((-(ι 0 * ι 2)) * ι 2 * ι 3) := by
          rw [e_mul_anticomm (by decide : (2 : Fin 5) ≠ 0)]
      _ = ι 0 * (ι 2 * ι 2) * ι 3 := by simp [mul_assoc]
      _ = ι 0 * ι 3 := by simp [e2_sq]

/-! ### Duality on the null sector (does **not** close as bivectors) -/

/--
`e₄` commutes with the Cl(3,1) pseudoscalar `i = e₀e₁e₂e₃` because it
anticommutes with each of the four factors (four sign flips).
-/
theorem e4_commute_pseudoscalar :
    ι e4Index * pseudoscalar = pseudoscalar * ι e4Index := by
  dsimp [pseudoscalar, e4Index]
  have h0 : ι 4 * ι 0 = -(ι 0 * ι 4) := e_mul_anticomm (by decide)
  have h1 : ι 4 * ι 1 = -(ι 1 * ι 4) := e_mul_anticomm (by decide)
  have h2 : ι 4 * ι 2 = -(ι 2 * ι 4) := e_mul_anticomm (by decide)
  have h3 : ι 4 * ι 3 = -(ι 3 * ι 4) := e_mul_anticomm (by decide)
  calc ι 4 * (ι 0 * ι 1 * ι 2 * ι 3)
      = (ι 4 * ι 0) * ι 1 * ι 2 * ι 3 := by simp [mul_assoc]
    _ = (-(ι 0 * ι 4)) * ι 1 * ι 2 * ι 3 := by rw [h0]
    _ = -(ι 0 * (ι 4 * ι 1) * ι 2 * ι 3) := by simp [mul_assoc]
    _ = -(ι 0 * (-(ι 1 * ι 4)) * ι 2 * ι 3) := by rw [h1]
    _ = ι 0 * ι 1 * (ι 4 * ι 2) * ι 3 := by simp [mul_assoc]
    _ = ι 0 * ι 1 * (-(ι 2 * ι 4)) * ι 3 := by rw [h2]
    _ = -(ι 0 * ι 1 * ι 2 * (ι 4 * ι 3)) := by simp [mul_neg, mul_assoc]
    _ = -(ι 0 * ι 1 * ι 2 * (-(ι 3 * ι 4))) := by rw [h3]
    _ = ι 0 * ι 1 * ι 2 * ι 3 * ι 4 := by simp [mul_neg, mul_assoc]

/--
Dual of a null generator: `N_μ · i = e₄ · (e_μ · i)` by associativity.

**Grade warning:** `e_μ · i` is grade 3 in the Cl(3,1) subalgebra, so the
right-hand side is grade 4 in `G(3,1,1)`.  Duality therefore does **not** map
the null *bivector* sector into itself.  The paper claim that duality closes
the four-dimensional null bivector ideal is rejected at the grade level.
-/
theorem dual_null (μ : Fin 4) :
    dual (null μ) = ι e4Index * (ι (Fin.castAdd 1 μ) * pseudoscalar) := by
  simp [dual, null, mul_assoc]

structure TorsionParams where
  alpha : Fin 3 → ℝ
  beta : Fin 3 → ℝ

def daggerParams (p : TorsionParams) : TorsionParams where
  alpha := p.beta
  beta := p.alpha

theorem reverse_odd_generators :
    (∀ a, CliffordAlgebra.reverse (hyperbolic a) = -hyperbolic a) ∧
    (∀ a, CliffordAlgebra.reverse (cyclic a) = -cyclic a) ∧
    (∀ μ, CliffordAlgebra.reverse (null μ) = -null μ) :=
  ⟨hyperbolic_reverse, cyclic_reverse, null_reverse⟩

end Operations

end DstDiophantine
