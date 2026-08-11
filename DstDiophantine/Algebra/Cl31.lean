import DstDiophantine.Algebra.PGA
import Mathlib.LinearAlgebra.CliffordAlgebra.Basic

/-!
# The Cl(3,1) subalgebra inside G(3,1,1)

Vectors `e₀…e₃` generate the Minkowski subalgebra; `e₄` is the adjoined null direction.
-/

namespace DstDiophantine

open CliffordAlgebra

abbrev Cl31 := CliffordAlgebra Q31

namespace Cl31

noncomputable def ι (μ : Fin 4) : Cl31 :=
  CliffordAlgebra.ι Q31 (e4vec μ)

theorem e_sq (μ : Fin 4) : ι μ * ι μ = algebraMap ℝ Cl31 (Q31 (e4vec μ)) :=
  ι_sq_scalar (Q := Q31) (e4vec μ)

theorem e_anticomm {i j : Fin 4} (hij : i ≠ j) :
    ι i * ι j + ι j * ι i = 0 :=
  ι_mul_ι_add_swap_of_isOrtho (Q := Q31) (Q31_isOrtho_basis i j hij)

noncomputable def extend4LM : Vec4 →ₗ[ℝ] Vec5 where
  toFun := extend4
  map_add' := fun x y => by ext i; fin_cases i <;> simp [extend4, Pi.add_apply]
  map_smul' := fun c x => by ext i; fin_cases i <;> simp [extend4, Pi.smul_apply]

@[simp] theorem extend4LM_apply (v : Vec4) : extend4LM v = extend4 v := rfl

/-- Embed `Cl(3,1)` into `G(3,1,1)` via `v ↦ (v, 0)`. -/
noncomputable def toPGA : Cl31 →ₐ[ℝ] PGA :=
  CliffordAlgebra.lift Q31
    ⟨(CliffordAlgebra.ι Q311).comp extend4LM, fun m => by
      simp only [LinearMap.comp_apply, extend4LM_apply, ι_sq_scalar, Q311_extend4]⟩

@[simp] theorem toPGA_ι (μ : Fin 4) : toPGA (ι μ) = PGA.ι (Fin.castAdd 1 μ) := by
  change toPGA (CliffordAlgebra.ι Q31 (e4vec μ)) = PGA.ι (Fin.castAdd 1 μ)
  unfold toPGA PGA.ι
  rw [CliffordAlgebra.lift_ι_apply]
  simp [LinearMap.comp_apply, extend4LM_apply, extend4_e4vec]

end Cl31

end DstDiophantine
