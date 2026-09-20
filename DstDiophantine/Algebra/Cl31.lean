import DstDiophantine.Algebra.PGA
import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Isometry

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

noncomputable def restrict4LM : Vec5 →ₗ[ℝ] Vec4 where
  toFun := restrict4
  map_add' := fun x y => by ext i; simp [restrict4, Pi.add_apply]
  map_smul' := fun c x => by ext i; simp [restrict4, Pi.smul_apply]

@[simp] theorem restrict4LM_apply (v : Vec5) : restrict4LM v = restrict4 v := rfl

/-- The Minkowski inclusion is a quadratic-form isometry. -/
noncomputable def extend4Isometry : Q31 →qᵢ Q311 where
  toLinearMap := extend4LM
  map_app' := Q311_extend4

/-- Dropping the null coordinate is a quadratic-form isometry. -/
noncomputable def restrict4Isometry : Q311 →qᵢ Q31 where
  toLinearMap := restrict4LM
  map_app' := Q31_restrict4

theorem restrict4Isometry_leftInverse_extend4 :
    Function.LeftInverse restrict4Isometry extend4Isometry :=
  restrict4_extend4

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

theorem toPGA_eq_map : toPGA = CliffordAlgebra.map extend4Isometry := by
  refine CliffordAlgebra.hom_ext ?_
  ext m
  simp [toPGA, extend4Isometry]

/-- Drop the null generator: an algebra retraction of `toPGA`. -/
noncomputable def ofPGA : PGA →ₐ[ℝ] Cl31 :=
  CliffordAlgebra.map restrict4Isometry

theorem ofPGA_comp_toPGA : Function.LeftInverse ofPGA toPGA := by
  rw [toPGA_eq_map]
  exact CliffordAlgebra.leftInverse_map_of_leftInverse
    extend4Isometry restrict4Isometry restrict4Isometry_leftInverse_extend4

@[simp] theorem ofPGA_toPGA (c : Cl31) : ofPGA (toPGA c) = c :=
  ofPGA_comp_toPGA c

/-- The Minkowski embedding is injective: restriction is an algebra retraction. -/
theorem toPGA_injective : Function.Injective toPGA :=
  ofPGA_comp_toPGA.injective

theorem ofPGA_ι_e4 : ofPGA (PGA.ι PGA.e4Index) = 0 := by
  unfold ofPGA PGA.ι PGA.e4Index
  rw [CliffordAlgebra.map_apply_ι]
  have h0 : (restrict4Isometry : Vec5 → Vec4) (e5vec 4) = 0 :=
    restrict4_e5vec_last
  rw [h0, map_zero]

theorem ofPGA_mul_e4 (x : PGA) : ofPGA (PGA.ι PGA.e4Index * x) = 0 := by
  rw [map_mul, ofPGA_ι_e4, zero_mul]

end Cl31

end DstDiophantine
