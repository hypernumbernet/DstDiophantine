/-
Copyright (c) 2026 DstDiophantine contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DstDiophantine contributors
-/
import DstDiophantine.Logic.Quantum.Spinor
import DstDiophantine.Algebra.Cl91
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.Free

/-!
# 10D Majorana–Weyl type and dimensional reduction label

`MajoranaWeyl10` is the real 16-dimensional type of the massless R-sector
ground state. `WeylSU4` is the complex 8-dimensional space `ℂ⁸`
(real dimension 16), the bookkeeping carrier for a `(2,4)` branching.
**No** `Spin(9,1)`-equivariance is claimed.
`DualSpinor ≃ ℂ²` is deliberately not identified with `MajoranaWeyl10`.
-/

namespace DstDiophantine

namespace Logic

open Module Complex

/-- Textbook 10D Majorana–Weyl spinor carrier (real 16). -/
abbrev MajoranaWeyl10 := EuclideanSpace ℝ (Fin 16)

/-- Complex 8-fold label for 10D → 4D branching bookkeeping (`ℂ² ⊗ ℂ⁴` dim). -/
abbrev WeylSU4 := Fin 8 → ℂ

theorem majoranaWeyl10_finrank : finrank ℝ MajoranaWeyl10 = 16 := by
  simp

theorem weylSU4_finrank_complex : finrank ℂ WeylSU4 = 8 := by
  simp

/-- Real dimension of `WeylSU4` is 16. -/
theorem weylSU4_finrank_real : finrank ℝ WeylSU4 = 16 := by
  have h := Module.finrank_mul_finrank ℝ ℂ WeylSU4
  have hc : finrank ℝ ℂ = 2 := Complex.finrank_real_complex
  have hW : finrank ℂ WeylSU4 = 8 := weylSU4_finrank_complex
  calc finrank ℝ WeylSU4 = finrank ℝ ℂ * finrank ℂ WeylSU4 := h.symm
    _ = 2 * 8 := by rw [hc, hW]
    _ = 16 := by norm_num

/-- Real-linear equivalence witnessing equal real dimension (not Spin-equivariant). -/
noncomputable def majoranaWeyl10_equiv_weylSU4 :
    MajoranaWeyl10 ≃ₗ[ℝ] WeylSU4 :=
  LinearEquiv.ofFinrankEq _ _ (majoranaWeyl10_finrank.trans weylSU4_finrank_real.symm)

/-- Dual-sector `ℂ²` is not the 10D Majorana–Weyl carrier. -/
theorem dualSpinor_finrank_ne_majorana :
    finrank ℂ DualSpinor ≠ finrank ℝ MajoranaWeyl10 := by
  rw [dualSpinor_finrank, majoranaWeyl10_finrank]
  norm_num

/-- Algebra dimension of `Cl(3,1)` equals the MW count numerically. -/
theorem cl31_finrank_eq_majorana_count :
    finrank ℝ Cl31 = finrank ℝ MajoranaWeyl10 := by
  rw [Cl91.finrank_cl31, majoranaWeyl10_finrank]

end Logic

end DstDiophantine
