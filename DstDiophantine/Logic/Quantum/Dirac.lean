import DstDiophantine.Algebra.Cl31
import DstDiophantine.Algebra.Generators
import DstDiophantine.Algebra.QuadraticForm
import DstDiophantine.Algebra.PGA.Normed
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NoncommRing

/-!
# Dirac Clifford relations inside `Cl(3,1)`

The Dirac matrices of signature `(-,+,+,+)` are the grade-1 generators
`Cl31.ι μ`. They are **not** the hyperbolic bivectors `e₀eₐ` (which square
to `+1`). The paper draft's reuse of `j` for both `P_spin = (1+j)/2`
(`j² = +1`) and `γ⁰` is therefore rejected.

The Dirac *equation* (a first-order PDE, mass term, rotor covariance) is
not formalised here.
-/

namespace DstDiophantine

namespace Logic

open Cl31 Generators

/-- Dirac gamma: the Minkowski grade-1 basis of `Cl(3,1)`. -/
noncomputable def diracGamma (μ : Fin 4) : Cl31 :=
  Cl31.ι μ

/-- Minkowski fibre metric `η_μν = diag(-1,+1,+1,+1)`. -/
def minkowskiEta (μ ν : Fin 4) : ℝ :=
  if μ = ν then w31 μ else 0

@[simp] theorem minkowskiEta_diag (μ : Fin 4) : minkowskiEta μ μ = w31 μ := by
  simp [minkowskiEta]

@[simp] theorem minkowskiEta_off {μ ν : Fin 4} (h : μ ≠ ν) :
    minkowskiEta μ ν = 0 := by
  simp [minkowskiEta, h]

theorem diracGamma_sq (μ : Fin 4) :
    diracGamma μ * diracGamma μ = algebraMap ℝ Cl31 (w31 μ) := by
  simp [diracGamma, Cl31.e_sq, Q31_e4vec]

theorem diracGamma_zero_sq :
    diracGamma 0 * diracGamma 0 = algebraMap ℝ Cl31 (-1) := by
  simpa [w31] using diracGamma_sq 0

theorem diracGamma_spatial_sq (a : Fin 3) :
    diracGamma a.succ * diracGamma a.succ = 1 := by
  have h : w31 a.succ = 1 := by fin_cases a <;> simp [w31]
  simpa [h, map_one] using diracGamma_sq a.succ

private theorem add_self_eq_two_smul (x : Cl31) :
    x + x = algebraMap ℝ Cl31 2 * x := by
  have h : (1 + 1 : Cl31) = algebraMap ℝ Cl31 2 := by
    calc (1 + 1 : Cl31)
        = algebraMap ℝ Cl31 1 + algebraMap ℝ Cl31 1 := by
            simp [Algebra.algebraMap_eq_smul_one]
      _ = algebraMap ℝ Cl31 (1 + 1) := (map_add _ _ _).symm
      _ = algebraMap ℝ Cl31 2 := by norm_num
  calc x + x = (1 + 1 : Cl31) * x := by noncomm_ring
    _ = algebraMap ℝ Cl31 2 * x := by rw [h]

/-- Clifford relation `{γ^μ, γ^ν} = 2 η^{μν}`. -/
theorem diracGamma_clifford (μ ν : Fin 4) :
    diracGamma μ * diracGamma ν + diracGamma ν * diracGamma μ =
      algebraMap ℝ Cl31 (2 * minkowskiEta μ ν) := by
  by_cases h : μ = ν
  · subst h
    simp only [minkowskiEta_diag]
    calc diracGamma μ * diracGamma μ + diracGamma μ * diracGamma μ
        = algebraMap ℝ Cl31 2 * (diracGamma μ * diracGamma μ) :=
          add_self_eq_two_smul _
      _ = algebraMap ℝ Cl31 2 * algebraMap ℝ Cl31 (w31 μ) := by
            rw [diracGamma_sq]
      _ = algebraMap ℝ Cl31 (2 * w31 μ) := by rw [← map_mul]
  · simp [minkowskiEta, h, diracGamma, Cl31.e_anticomm h]

/-- Time gamma squares to `-1`, so it is not a hyperbolic (`j² = +1`) generator. -/
theorem diracGamma_zero_sq_ne_one :
    diracGamma 0 * diracGamma 0 ≠ 1 := by
  intro h
  have hmap : Cl31.toPGA (diracGamma 0 * diracGamma 0) = Cl31.toPGA 1 :=
    congrArg Cl31.toPGA h
  rw [diracGamma_zero_sq, AlgHom.commutes, map_one] at hmap
  have heq : algebraMap ℝ PGA (-1 : ℝ) = algebraMap ℝ PGA 1 := by
    simpa using hmap
  have : algebraMap ℝ PGA ((-1 : ℝ) - 1) = 0 := by
    rw [map_sub, heq, sub_self]
  have hR : (-1 : ℝ) - 1 = 0 :=
    (FaithfulSMul.algebraMap_eq_zero_iff (R := ℝ) (A := PGA)).mp this
  norm_num at hR

/-- Embedding of `γ⁰` is the time vector `e₀`, not the boost bivector `e₀e₁`. -/
theorem toPGA_diracGamma_zero :
    Cl31.toPGA (diracGamma 0) = PGA.ι 0 := by
  simp [diracGamma]

/-- Paper identification `γ⁰ = j` with `j = hyperbolic 0` is false. -/
theorem paper_gamma0_not_hyperbolic :
    Cl31.toPGA (diracGamma 0) ≠ hyperbolic 0 := by
  intro h
  have hsq := congrArg (fun x : PGA => x * x) h
  have hL : Cl31.toPGA (diracGamma 0) * Cl31.toPGA (diracGamma 0) =
      algebraMap ℝ PGA (-1) := by
    rw [← map_mul, diracGamma_zero_sq, AlgHom.commutes]
  have hR : hyperbolic 0 * hyperbolic 0 = 1 := hyperbolic_sq 0
  rw [hL, hR] at hsq
  have heq : algebraMap ℝ PGA (-1 : ℝ) = algebraMap ℝ PGA 1 := by
    simpa using hsq
  have : algebraMap ℝ PGA ((-1 : ℝ) - 1) = 0 := by
    rw [map_sub, heq, sub_self]
  have hR' : (-1 : ℝ) - 1 = 0 :=
    (FaithfulSMul.algebraMap_eq_zero_iff (R := ℝ) (A := PGA)).mp this
  norm_num at hR'

end Logic

end DstDiophantine
