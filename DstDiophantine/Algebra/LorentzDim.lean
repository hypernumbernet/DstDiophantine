/-
Copyright (c) 2026 DstDiophantine contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DstDiophantine contributors
-/
import Mathlib.Tactic.NormNum

/-!
# Lorentz and Poincaré dimension counts

Pure `ℕ` identities used by the 10D comparison layer. No Lie-algebra
isomorphism theorems are claimed here.
-/

namespace DstDiophantine

namespace LorentzDim

/-- Dimension of `𝔰𝔬(n)` as `n(n-1)/2`. -/
def soDim (n : ℕ) : ℕ := n * (n - 1) / 2

/-- Dimension of the Poincaré algebra `𝔦𝔰𝔬(n-1,1) ≅ 𝔰𝔬(n-1,1) ⋉ ℝⁿ`. -/
def isoDim (n : ℕ) : ℕ := soDim n + n

/-- Little-group `SO(8)` dimension (massless 10D). -/
def so8Dim : ℕ := soDim 8

/-- Lorentz `𝔰𝔬(3,1)` dimension label. -/
def so31Dim : ℕ := soDim 4

/-- Lorentz `𝔰𝔬(9,1)` dimension label. -/
def so91Dim : ℕ := soDim 10

/-- Poincaré `𝔦𝔰𝔬(3,1)` dimension label. -/
def iso31Dim : ℕ := isoDim 4

/-- Poincaré `𝔦𝔰𝔬(9,1)` dimension label. -/
def iso91Dim : ℕ := isoDim 10

/-- PGA hyperbolic + cyclic + null generator count (not a Lie isomorphism claim). -/
def pgaGeneratorCount : ℕ := 6 + 4

@[simp] theorem soDim_zero : soDim 0 = 0 := by simp [soDim]
@[simp] theorem soDim_one : soDim 1 = 0 := by simp [soDim]
@[simp] theorem soDim_two : soDim 2 = 1 := by decide
@[simp] theorem soDim_three : soDim 3 = 3 := by decide
@[simp] theorem soDim_four : soDim 4 = 6 := by decide
@[simp] theorem soDim_eight : soDim 8 = 28 := by decide
@[simp] theorem soDim_ten : soDim 10 = 45 := by decide

theorem so31Dim_eq : so31Dim = 6 := by simp [so31Dim]
theorem so91Dim_eq : so91Dim = 45 := by simp [so91Dim]
theorem so8Dim_eq : so8Dim = 28 := by simp [so8Dim]
theorem iso31Dim_eq : iso31Dim = 10 := by simp [iso31Dim, isoDim]
theorem iso91Dim_eq : iso91Dim = 55 := by simp [iso91Dim, isoDim]
theorem pgaGeneratorCount_eq : pgaGeneratorCount = 10 := by simp [pgaGeneratorCount]

theorem so31Dim_ne_so91Dim : so31Dim ≠ so91Dim := by
  rw [so31Dim_eq, so91Dim_eq]; decide

theorem iso31Dim_ne_iso91Dim : iso31Dim ≠ iso91Dim := by
  rw [iso31Dim_eq, iso91Dim_eq]; decide

theorem pgaGeneratorCount_eq_iso31Dim : pgaGeneratorCount = iso31Dim := by
  rw [pgaGeneratorCount_eq, iso31Dim_eq]

theorem pgaGeneratorCount_ne_iso91Dim : pgaGeneratorCount ≠ iso91Dim := by
  rw [pgaGeneratorCount_eq, iso91Dim_eq]; decide

/-- Light-cone physical dof `8 + 8` versus DST's six torsion generators. -/
theorem lightCone_ne_torsionGenerators : 8 + 8 ≠ 6 := by decide

end LorentzDim

end DstDiophantine
