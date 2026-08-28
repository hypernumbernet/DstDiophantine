import DstDiophantine.Algebra.Cl31
import Mathlib.Algebra.CharP.Invertible
import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

/-!
# Textbook Clifford algebra `Cl(9,1)`

Used by the string-comparison layer. Embeds `Cl(3,1)` on the first four
coordinates. Real dimensions: `dimℝ Cl(3,1) = 16`, `dimℝ Cl(9,1) = 1024`.
-/

namespace DstDiophantine

open CliffordAlgebra Module

abbrev Cl91 := CliffordAlgebra Q91

namespace Cl91

noncomputable def ι (μ : Fin 10) : Cl91 :=
  CliffordAlgebra.ι Q91 (e10vec μ)

theorem e_sq (μ : Fin 10) : ι μ * ι μ = algebraMap ℝ Cl91 (Q91 (e10vec μ)) :=
  ι_sq_scalar (Q := Q91) (e10vec μ)

theorem e_anticomm {i j : Fin 10} (hij : i ≠ j) :
    ι i * ι j + ι j * ι i = 0 :=
  ι_mul_ι_add_swap_of_isOrtho (Q := Q91) (Q91_isOrtho_basis i j hij)

noncomputable def extend4to10LM : Vec4 →ₗ[ℝ] Vec10 where
  toFun := extend4to10
  map_add' := fun x y => by
    ext i
    fin_cases i <;> simp [extend4to10, Pi.add_apply]
  map_smul' := fun c x => by
    ext i
    fin_cases i <;> simp [extend4to10, Pi.smul_apply]

@[simp] theorem extend4to10LM_apply (v : Vec4) : extend4to10LM v = extend4to10 v := rfl

private theorem finrank_exterior (n : ℕ) :
    finrank ℝ (ExteriorAlgebra ℝ (Fin n → ℝ)) = 2 ^ n := by
  classical
  have b := (Pi.basisFun ℝ (Fin n)).ExteriorAlgebra
  rw [finrank_eq_card_basis b, Fintype.card_finset, Fintype.card_fin]

instance instFiniteExterior4 : Module.Finite ℝ (ExteriorAlgebra ℝ Vec4) := by
  classical
  exact Module.Finite.of_basis (Pi.basisFun ℝ (Fin 4)).ExteriorAlgebra

instance instFiniteExterior10 : Module.Finite ℝ (ExteriorAlgebra ℝ Vec10) := by
  classical
  exact Module.Finite.of_basis (Pi.basisFun ℝ (Fin 10)).ExteriorAlgebra

instance instFiniteCl31 : Module.Finite ℝ Cl31 :=
  Module.Finite.equiv (CliffordAlgebra.equivExterior Q31).symm

instance instFiniteCl91 : Module.Finite ℝ Cl91 :=
  Module.Finite.equiv (CliffordAlgebra.equivExterior Q91).symm

/-- Real dimension of `Cl(3,1)`. -/
theorem finrank_cl31 : finrank ℝ Cl31 = 16 := by
  have h := LinearEquiv.finrank_eq (CliffordAlgebra.equivExterior Q31)
  rw [h, finrank_exterior 4]
  norm_num

/-- Real dimension of `Cl(9,1)`. -/
theorem finrank_cl91 : finrank ℝ Cl91 = 1024 := by
  have h := LinearEquiv.finrank_eq (CliffordAlgebra.equivExterior Q91)
  rw [h, finrank_exterior 10]
  norm_num

theorem finrank_cl31_ne_cl91 : finrank ℝ Cl31 ≠ finrank ℝ Cl91 := by
  rw [finrank_cl31, finrank_cl91]
  norm_num

/-- The algebras are not isomorphic: dimensions differ. -/
theorem not_algEquiv_cl31 :
    ¬ Nonempty (Cl31 ≃ₐ[ℝ] Cl91) := by
  intro ⟨e⟩
  have h := LinearEquiv.finrank_eq e.toLinearEquiv
  exact finrank_cl31_ne_cl91 h

end Cl91

/-- Embed `Cl(3,1)` into `Cl(9,1)` via padding with six zeros. -/
noncomputable def Cl31.toCl91 : Cl31 →ₐ[ℝ] Cl91 :=
  CliffordAlgebra.lift Q31
    ⟨(CliffordAlgebra.ι Q91).comp Cl91.extend4to10LM, fun m => by
      simp only [LinearMap.comp_apply, Cl91.extend4to10LM_apply, ι_sq_scalar,
        Q91_extend4to10]⟩

namespace Cl91

@[simp] theorem toCl91_ι (μ : Fin 4) :
    Cl31.toCl91 (Cl31.ι μ) = ι (Fin.castAdd 6 μ) := by
  change Cl31.toCl91 (CliffordAlgebra.ι Q31 (e4vec μ)) = ι (Fin.castAdd 6 μ)
  unfold Cl31.toCl91 ι
  rw [CliffordAlgebra.lift_ι_apply]
  simp [LinearMap.comp_apply, extend4to10LM_apply, extend4to10_e4vec]

end Cl91

end DstDiophantine
