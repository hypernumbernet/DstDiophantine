import DstDiophantine.Algebra.Generators
import DstDiophantine.Algebra.Cl31

/-!
# Reverse, dual, and dagger operations

The dual map `X ↦ X · i` uses the Cl(3,1) pseudoscalar `i = e₀e₁e₂e₃`.
-/

namespace DstDiophantine

open PGA Generators

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

private theorem e2_sq : ι 2 * ι 2 = (1 : PGA) := by
  simpa [Q311_e5vec, w311] using e_sq (2 : Fin 5)

private theorem e3_sq : ι 3 * ι 3 = (1 : PGA) := by
  simpa [Q311_e5vec, w311] using e_sq (3 : Fin 5)

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
