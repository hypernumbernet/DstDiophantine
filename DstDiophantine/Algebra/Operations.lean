import DstDiophantine.Algebra.Generators
import DstDiophantine.Algebra.Cl31

/-!
# Reverse, dual, and dagger operations

The dual map `X ↦ X · i` uses the Cl(3,1) pseudoscalar `i = e₀e₁e₂e₃`.
-/

namespace DstDiophantine

open CliffordAlgebra PGA Generators

namespace Operations

/-- Pseudoscalar `i = e₀e₁e₂e₃` of the embedded Cl(3,1) subalgebra. -/
noncomputable def pseudoscalar : PGA :=
  ι 0 * ι 1 * ι 2 * ι 3

/-- Biquaternion duality `X ↦ X i`. -/
noncomputable def dual (x : PGA) : PGA :=
  x * pseudoscalar

theorem dual_mul (x y : PGA) : dual (x * y) = dual x * dual y := by
  sorry

theorem dual_hyperbolic (a : Fin 3) : dual (hyperbolic a) = -cyclic a := by
  sorry

theorem dual_cyclic (a : Fin 3) : dual (cyclic a) = hyperbolic a := by
  sorry

structure TorsionParams where
  alpha : Fin 3 → ℝ
  beta : Fin 3 → ℝ

def daggerParams (p : TorsionParams) : TorsionParams where
  alpha := p.beta
  beta := p.alpha

theorem reverse_odd_generators :
    (∀ a, reverse (hyperbolic a) = -hyperbolic a) ∧
    (∀ a, reverse (cyclic a) = -cyclic a) ∧
    (∀ μ, reverse (null μ) = -null μ) :=
  ⟨hyperbolic_reverse, cyclic_reverse, null_reverse⟩

end Operations

end DstDiophantine
