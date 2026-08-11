import DstDiophantine.Algebra.QuadraticForm
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation
import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.Algebra.Ring.Defs

/-!
# Projective geometric algebra G(3,1,1)

`G(3,1,1)` is realised as `CliffordAlgebra Q311` with basis vectors `e₀…e₄`.
-/

namespace DstDiophantine

open CliffordAlgebra

abbrev PGA := CliffordAlgebra Q311

namespace PGA

/-- Null basis index `e₄`. -/
def e4Index : Fin 5 := 4

noncomputable def ι (μ : Fin 5) : PGA :=
  CliffordAlgebra.ι Q311 (e5vec μ)

theorem e_sq (μ : Fin 5) : ι μ * ι μ = algebraMap ℝ PGA (Q311 (e5vec μ)) :=
  ι_sq_scalar (Q := Q311) (e5vec μ)

theorem e0_sq : ι 0 * ι 0 = algebraMap ℝ PGA (-1 : ℝ) := by
  simp [e_sq, Q311_e5vec, w311]

theorem e1_sq : ι 1 * ι 1 = (1 : PGA) := by
  simp [e_sq, Q311_e5vec, w311]

theorem e4_sq : ι e4Index * ι e4Index = 0 := by
  simp [e_sq, Q311_e5vec, w311, e4Index]

theorem e4_sq_zero : ι e4Index * ι e4Index = 0 := e4_sq

theorem e_anticomm {i j : Fin 5} (hij : i ≠ j) :
    ι i * ι j + ι j * ι i = 0 :=
  ι_mul_ι_add_swap_of_isOrtho (Q := Q311) (Q311_isOrtho_basis i j hij)

theorem e_mul_anticomm {i j : Fin 5} (hij : i ≠ j) :
    ι i * ι j = -(ι j * ι i) :=
  (neg_eq_of_add_eq_zero_left (e_anticomm hij)).symm

theorem e4_ne_cast (μ : Fin 4) : (4 : Fin 5) ≠ Fin.castAdd 1 μ := by
  fin_cases μ <;> decide

theorem e4_anticomm (μ : Fin 4) :
    ι e4Index * ι (Fin.castAdd 1 μ) + ι (Fin.castAdd 1 μ) * ι e4Index = 0 :=
  e_anticomm (e4_ne_cast μ)

theorem e4_mul_anticomm (μ : Fin 4) :
    ι e4Index * ι (Fin.castAdd 1 μ) = -(ι (Fin.castAdd 1 μ) * ι e4Index) :=
  (neg_eq_of_add_eq_zero_left (e4_anticomm μ)).symm

theorem e4_inner_anticomm (μ : Fin 4) :
    ι (Fin.castAdd 1 μ) * ι e4Index = -(ι e4Index * ι (Fin.castAdd 1 μ)) := by
  exact (neg_eq_iff_eq_neg.mpr (e4_mul_anticomm μ)).symm

theorem ι_e4_ne_zero : ι e4Index ≠ 0 := by
  intro h
  have : Invertible (2 : ℝ) := ⟨2⁻¹, by norm_num, by norm_num⟩
  have h' : (CliffordAlgebra.equivExterior Q311) (ι e4Index) = 0 := by
    rw [h]
    exact map_zero (CliffordAlgebra.equivExterior Q311)
  rw [show (CliffordAlgebra.equivExterior Q311) = CliffordAlgebra.changeFormEquiv
      CliffordAlgebra.changeForm.associated_neg_proof from rfl,
    CliffordAlgebra.changeFormEquiv_apply] at h'
  dsimp [ι] at h'
  rw [CliffordAlgebra.changeForm_ι] at h'
  exact absurd (Iff.mp (ExteriorAlgebra.ι_eq_zero_iff (e5vec e4Index)) h')
    (by simp [e5vec, e4Index, Pi.single])

end PGA

end DstDiophantine
