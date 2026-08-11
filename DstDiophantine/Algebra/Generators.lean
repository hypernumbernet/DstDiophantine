import DstDiophantine.Algebra.PGA
import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation

/-!
# Ten bivector generators of G(3,1,1)

Hyperbolic (`iI,iJ,iK`), cyclic (`I,J,K`), and null (`N₀…N₃`) generators.
-/

namespace DstDiophantine

open CliffordAlgebra PGA

namespace Generators

/-- Hyperbolic boost generators `B⁺ₐ = e₀ e_{a+1}` for `a = 0,1,2`. -/
noncomputable def hyperbolic : Fin 3 → PGA
  | 0 => ι 0 * ι 1
  | 1 => ι 0 * ι 2
  | 2 => ι 0 * ι 3

/-- Cyclic rotation generators `B⁻₀ = e₃ e₂`, `B⁻₁ = e₁ e₃`, `B⁻₂ = e₂ e₁`. -/
noncomputable def cyclic : Fin 3 → PGA
  | 0 => ι 3 * ι 2
  | 1 => ι 1 * ι 3
  | 2 => ι 2 * ι 1

/-- Null translation generators `N_μ = e₄ ∧ e_μ`. -/
noncomputable def null (μ : Fin 4) : PGA :=
  ι e4Index * ι (Fin.castAdd 1 μ)

theorem hyperbolic_sq (a : Fin 3) : hyperbolic a * hyperbolic a = 1 := by
  sorry

theorem cyclic_sq (a : Fin 3) : cyclic a * cyclic a = -1 := by
  sorry

theorem null_sq (μ : Fin 4) : null μ * null μ = 0 := by
  dsimp [null]
  calc ι e4Index * ι (Fin.castAdd 1 μ) * (ι e4Index * ι (Fin.castAdd 1 μ))
      = ι e4Index * (ι (Fin.castAdd 1 μ) * ι e4Index) * ι (Fin.castAdd 1 μ) := by simp [mul_assoc]
    _ = ι e4Index * (-(ι e4Index * ι (Fin.castAdd 1 μ))) * ι (Fin.castAdd 1 μ) := by
        rw [e4_inner_anticomm μ]
    _ = -(ι e4Index * ι e4Index * ι (Fin.castAdd 1 μ) * ι (Fin.castAdd 1 μ)) := by
        simp [mul_assoc]
    _ = 0 := by simp [e4_sq_zero, mul_assoc]

/-- Strong null vanishing: `N_μ N_ν = 0` for all `μ, ν`. -/
theorem null_mul_null (μ ν : Fin 4) : null μ * null ν = 0 := by
  dsimp [null]
  calc ι e4Index * ι (Fin.castAdd 1 μ) * (ι e4Index * ι (Fin.castAdd 1 ν))
      = ι e4Index * (ι (Fin.castAdd 1 μ) * ι e4Index) * ι (Fin.castAdd 1 ν) := by simp [mul_assoc]
    _ = ι e4Index * (-(ι e4Index * ι (Fin.castAdd 1 μ))) * ι (Fin.castAdd 1 ν) := by
        rw [e4_inner_anticomm μ]
    _ = -(ι e4Index * ι e4Index * ι (Fin.castAdd 1 μ) * ι (Fin.castAdd 1 ν)) := by
        simp [mul_assoc]
    _ = 0 := by simp [e4_sq_zero, mul_assoc]

theorem null_reverse (μ : Fin 4) : reverse (null μ) = -null μ := by
  sorry

theorem hyperbolic_reverse (a : Fin 3) : reverse (hyperbolic a) = -hyperbolic a := by
  sorry

theorem cyclic_reverse (a : Fin 3) : reverse (cyclic a) = -cyclic a := by
  sorry

end Generators

end DstDiophantine
