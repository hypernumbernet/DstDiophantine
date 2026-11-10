import DstDiophantine.Gravity.Coframe
import DstDiophantine.Gravity.PlaneTorsion
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# A local Lorentz 1-jet whose teleparallel scalar does not vanish

Preserving the Minkowski metric is the definition of a Lorentz matrix. The
teleparallel scalar of a single generator vanishes for every jet, but two
generators with independent jets need not. At the identity,
`exp(y K_{tx}) exp(t K_{xy})` has `∂_y` along the boost and `∂_t` along the
rotation, and the teleparallel scalar of that 1-jet is `-2`.
-/

namespace DstDiophantine

namespace Gravity

open Finset PlaneTorsion

/-- `Λᵀ η Λ = η` forces the induced metric to be Minkowski. -/
theorem inducedMetric_of_lorentz (Λ : Coframe)
    (h : ∀ μ ν, ∑ a : Fin 4, w31 a * Λ a μ * Λ a ν = if μ = ν then w31 μ else 0)
    (μ ν : Fin 4) :
    inducedMetric Λ μ ν = if μ = ν then w31 μ else 0 := by
  rw [inducedMetric_eq_weighted, h]

def txCoeff : Fin 6 → ℝ := fun k => if k = 0 then 1 else 0

def xyCoeff : Fin 6 → ℝ := fun k => if k = 3 then 1 else 0

def txGen : Fin 4 → Fin 4 → ℝ := soK txCoeff

def xyGen : Fin 4 → Fin 4 → ℝ := soK xyCoeff

/-- Jet with only `∂_y = 1`. -/
def jetY : Fin 4 → ℝ
  | 2 => 1
  | _ => 0

/-- Jet with only `∂_t = 1`. -/
def jetT : Fin 4 → ℝ
  | 0 => 1
  | _ => 0

/-- Sum of the boost torsion and the rotation torsion. -/
def mixedTorsion (ρ μ ν : Fin 4) : ℝ :=
  genTorsion txGen jetY ρ μ ν + genTorsion xyGen jetT ρ μ ν

theorem txGen_antisym : MinkowskiAntisym txGen :=
  soK_minkowskiAntisym _

theorem xyGen_antisym : MinkowskiAntisym xyGen :=
  soK_minkowskiAntisym _

theorem mixedTorsion_support (ρ μ ν : Fin 4) :
    mixedTorsion ρ μ ν =
      if ρ = 0 ∧ μ = 2 ∧ ν = 1 then 1
      else if ρ = 0 ∧ μ = 1 ∧ ν = 2 then -1
      else if ρ = 2 ∧ μ = 0 ∧ ν = 1 then -1
      else if ρ = 2 ∧ μ = 1 ∧ ν = 0 then 1
      else 0 := by
  fin_cases ρ <;> fin_cases μ <;> fin_cases ν <;>
    simp [mixedTorsion, genTorsion, txGen, xyGen, txCoeff, xyCoeff, soK, jetY, jetT]

def mixedDown (ρ μ ν : Fin 4) : ℝ :=
  w31 ρ * mixedTorsion ρ μ ν

def mixedUp (ρ μ ν : Fin 4) : ℝ :=
  w31 ρ * w31 μ * w31 ν * mixedDown ρ μ ν

def mixedTrace (ρ : Fin 4) : ℝ :=
  ∑ σ : Fin 4, mixedTorsion σ ρ σ

def mixedSquare : ℝ :=
  ∑ ρ : Fin 4, ∑ μ : Fin 4, ∑ ν : Fin 4, mixedDown ρ μ ν * mixedUp ρ μ ν

def mixedCross : ℝ :=
  ∑ ρ : Fin 4, ∑ μ : Fin 4, ∑ ν : Fin 4, mixedDown ρ μ ν * mixedUp ν μ ρ

def mixedTraceContr : ℝ :=
  ∑ ρ : Fin 4, mixedTrace ρ * (w31 ρ * mixedTrace ρ)

/-- Teleparallel scalar of the summed torsion. -/
noncomputable def mixedTeleparallel : ℝ :=
  (1 / 4) * mixedSquare + (1 / 2) * mixedCross - mixedTraceContr

theorem mixedSquare_eq : mixedSquare = -4 := by
  simp [mixedSquare, mixedDown, mixedUp, mixedTorsion_support, w31, Fin.sum_univ_four]
  norm_num

theorem mixedCross_eq : mixedCross = -2 := by
  simp [mixedCross, mixedDown, mixedUp, mixedTorsion_support, w31, Fin.sum_univ_four]
  norm_num

theorem mixedTrace_eq (ρ : Fin 4) : mixedTrace ρ = 0 := by
  fin_cases ρ <;>
    simp [mixedTrace, mixedTorsion_support, Fin.sum_univ_four]

theorem mixedTraceContr_eq : mixedTraceContr = 0 := by
  simp [mixedTraceContr, mixedTrace_eq]

theorem mixedTeleparallel_eq : mixedTeleparallel = -2 := by
  rw [mixedTeleparallel, mixedSquare_eq, mixedCross_eq, mixedTraceContr_eq]
  norm_num

/-- Two Minkowski-antisymmetric generators, with independent jets, can produce
a nonzero teleparallel scalar. An arbitrary local Lorentz transformation is
therefore not claimed to kill `T`. -/
theorem localLorentz_teleparallel_not_always_zero :
    MinkowskiAntisym txGen ∧ MinkowskiAntisym xyGen ∧ mixedTeleparallel = -2 :=
  ⟨txGen_antisym, xyGen_antisym, mixedTeleparallel_eq⟩

end Gravity

end DstDiophantine
