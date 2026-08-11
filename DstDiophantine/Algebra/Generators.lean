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

@[simp] theorem reverse_ι (μ : Fin 5) : reverse (ι μ) = ι μ := by
  simp only [PGA.ι, CliffordAlgebra.reverse_ι]

/-- Square of a simple bivector: `(eᵢ eⱼ)² = -Q(eᵢ) Q(eⱼ)`. -/
theorem ι_mul_ι_sq (i j : Fin 5) (hij : i ≠ j) :
    (ι i * ι j) * (ι i * ι j) =
      -(algebraMap ℝ PGA (Q311 (e5vec i)) * algebraMap ℝ PGA (Q311 (e5vec j))) := by
  calc (ι i * ι j) * (ι i * ι j)
      = ι i * (ι j * ι i) * ι j := by simp [mul_assoc]
    _ = ι i * (-(ι i * ι j)) * ι j := by rw [e_mul_anticomm hij.symm]
    _ = -(ι i * ι i * (ι j * ι j)) := by simp [mul_neg, mul_assoc]
    _ = -(algebraMap ℝ PGA (Q311 (e5vec i)) * algebraMap ℝ PGA (Q311 (e5vec j))) := by
        rw [e_sq i, e_sq j]

/-- Reverse of a simple bivector: `(eᵢ eⱼ)˜ = -eᵢ eⱼ` when `i ≠ j`. -/
theorem reverse_ι_mul_ι (i j : Fin 5) (hij : i ≠ j) :
    reverse (ι i * ι j) = -(ι i * ι j) := by
  rw [CliffordAlgebra.reverse.map_mul, reverse_ι, reverse_ι, e_mul_anticomm hij.symm]

private theorem hyperbolic_sq_of {i j : Fin 5} (hij : i ≠ j)
    (hi : Q311 (e5vec i) = -1) (hj : Q311 (e5vec j) = 1) :
    (ι i * ι j) * (ι i * ι j) = 1 := by
  rw [ι_mul_ι_sq i j hij, hi, hj]
  simp

private theorem cyclic_sq_of {i j : Fin 5} (hij : i ≠ j)
    (hi : Q311 (e5vec i) = 1) (hj : Q311 (e5vec j) = 1) :
    (ι i * ι j) * (ι i * ι j) = -1 := by
  rw [ι_mul_ι_sq i j hij, hi, hj]
  simp

theorem hyperbolic_sq (a : Fin 3) : hyperbolic a * hyperbolic a = 1 := by
  fin_cases a
  · exact hyperbolic_sq_of (by decide : (0 : Fin 5) ≠ 1) (by simp [Q311_e5vec, w311])
      (by simp [Q311_e5vec, w311])
  · exact hyperbolic_sq_of (by decide : (0 : Fin 5) ≠ 2) (by simp [Q311_e5vec, w311])
      (by simp [Q311_e5vec, w311])
  · exact hyperbolic_sq_of (by decide : (0 : Fin 5) ≠ 3) (by simp [Q311_e5vec, w311])
      (by simp [Q311_e5vec, w311])

theorem cyclic_sq (a : Fin 3) : cyclic a * cyclic a = -1 := by
  fin_cases a
  · exact cyclic_sq_of (by decide : (3 : Fin 5) ≠ 2) (by simp [Q311_e5vec, w311])
      (by simp [Q311_e5vec, w311])
  · exact cyclic_sq_of (by decide : (1 : Fin 5) ≠ 3) (by simp [Q311_e5vec, w311])
      (by simp [Q311_e5vec, w311])
  · exact cyclic_sq_of (by decide : (2 : Fin 5) ≠ 1) (by simp [Q311_e5vec, w311])
      (by simp [Q311_e5vec, w311])

theorem null_sq (μ : Fin 4) : null μ * null μ = 0 := by
  dsimp [null]
  calc ι e4Index * ι (Fin.castAdd 1 μ) * (ι e4Index * ι (Fin.castAdd 1 μ))
      = ι e4Index * (ι (Fin.castAdd 1 μ) * ι e4Index) * ι (Fin.castAdd 1 μ) := by simp [mul_assoc]
    _ = ι e4Index * (-(ι e4Index * ι (Fin.castAdd 1 μ))) * ι (Fin.castAdd 1 μ) := by
        rw [e4_inner_anticomm μ]
    _ = -(ι e4Index * ι e4Index * ι (Fin.castAdd 1 μ) * ι (Fin.castAdd 1 μ)) := by
        simp [mul_assoc]
    _ = 0 := by simp [e4_sq_zero]

/-- Strong null vanishing: `N_μ N_ν = 0` for all `μ, ν`. -/
theorem null_mul_null (μ ν : Fin 4) : null μ * null ν = 0 := by
  dsimp [null]
  calc ι e4Index * ι (Fin.castAdd 1 μ) * (ι e4Index * ι (Fin.castAdd 1 ν))
      = ι e4Index * (ι (Fin.castAdd 1 μ) * ι e4Index) * ι (Fin.castAdd 1 ν) := by simp [mul_assoc]
    _ = ι e4Index * (-(ι e4Index * ι (Fin.castAdd 1 μ))) * ι (Fin.castAdd 1 ν) := by
        rw [e4_inner_anticomm μ]
    _ = -(ι e4Index * ι e4Index * ι (Fin.castAdd 1 μ) * ι (Fin.castAdd 1 ν)) := by
        simp [mul_assoc]
    _ = 0 := by simp [e4_sq_zero]

theorem null_reverse (μ : Fin 4) : reverse (null μ) = -null μ := by
  dsimp [null]
  exact reverse_ι_mul_ι _ _ (e4_ne_cast μ)

theorem hyperbolic_reverse (a : Fin 3) : reverse (hyperbolic a) = -hyperbolic a := by
  fin_cases a
  · exact reverse_ι_mul_ι 0 1 (by decide)
  · exact reverse_ι_mul_ι 0 2 (by decide)
  · exact reverse_ι_mul_ι 0 3 (by decide)

theorem cyclic_reverse (a : Fin 3) : reverse (cyclic a) = -cyclic a := by
  fin_cases a
  · exact reverse_ι_mul_ι 3 2 (by decide)
  · exact reverse_ι_mul_ι 1 3 (by decide)
  · exact reverse_ι_mul_ι 2 1 (by decide)

end Generators

end DstDiophantine
