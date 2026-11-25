import DstDiophantine.Algebra.Admissible
import DstDiophantine.Algebra.MismatchAngle
import DstDiophantine.Algebra.RelativeRotor

set_option linter.style.whitespace false

/-!
# Repulsion cone vs mismatch half-norm box

Mismatch admissibility (`α+β ≤ π`, `β ≤ π`) implies the per-axis half-norm box
`(α/2)²+(β/2)² ≤ (π/2)²`. The converse is **false** (e.g. `β > π` or `α+β > π` with small half-norms).
Legacy `α+β ≤ π/2` is strictly stronger (`IsAdmissibleContinuousLegacy`).
-/

namespace DstDiophantine

open Admissible MismatchAngle RelativeRotor Operations Real

namespace RepulsionCone

noncomputable def mismatchHalfNormSq (α β : ℝ) : ℝ :=
  mismatchBoostHalf α β ^ 2 + mismatchRotationHalf α β ^ 2

@[simp] theorem mismatchHalfNormSq_eq (α β : ℝ) :
    mismatchHalfNormSq α β = (α / 2) ^ 2 + (β / 2) ^ 2 := by
  simp [mismatchHalfNormSq, mismatchBoostHalf, mismatchRotationHalf]

theorem admissible_axis_implies_mismatch_half_box {α β : ℝ}
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hsum : α + β ≤ Real.pi / 2) :
    mismatchHalfNormSq α β ≤ (Real.pi / 2) ^ 2 := by
  rw [mismatchHalfNormSq_eq]
  have h : α ^ 2 + β ^ 2 ≤ Real.pi ^ 2 := by
    nlinarith [sq_nonneg (α + β), sq_nonneg (α - β)]
  nlinarith

theorem admissible_axis_implies_mismatch_half_box_pi {α β : ℝ}
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hsum : α + β ≤ Real.pi) :
    mismatchHalfNormSq α β ≤ (Real.pi / 2) ^ 2 := by
  have h : α ^ 2 + β ^ 2 ≤ Real.pi ^ 2 := by nlinarith [sq_nonneg (α - β)]
  rw [mismatchHalfNormSq_eq]
  nlinarith

theorem admissibleContinuous_implies_mismatch_half_box (p : TorsionParams)
    (h : IsAdmissibleContinuous p) (a : Fin 3) :
    mismatchBoostHalf (p.alpha a) (p.beta a) ^ 2 +
        mismatchRotationHalf (p.alpha a) (p.beta a) ^ 2 ≤
      (Real.pi / 2) ^ 2 := by
  exact admissible_axis_implies_mismatch_half_box (h a).1 (h a).2.1 (h a).2.2.2

/-- Counterexample: mismatch half-box on every axis does **not** imply admissibility. -/
theorem mismatch_half_box_not_implies_admissible :
    (∃ p : TorsionParams,
        (∀ a : Fin 3,
            mismatchBoostHalf (p.alpha a) (p.beta a) ^ 2 +
                mismatchRotationHalf (p.alpha a) (p.beta a) ^ 2 ≤
              (Real.pi / 2) ^ 2) ∧
          ¬ IsAdmissibleContinuous p) := by
  set α := Real.pi / 2
  set β := (0.6 : ℝ) * Real.pi
  refine ⟨axisParams α β, ?_, ?_⟩
  · intro a
    fin_cases a
    · dsimp [axisParams, mismatchHalfNormSq, mismatchBoostHalf, mismatchRotationHalf, α, β]
      nlinarith [Real.pi_pos, sq_nonneg (Real.pi / 2)]
    · dsimp [axisParams, mismatchHalfNormSq, mismatchBoostHalf, mismatchRotationHalf, α, β]
      nlinarith [Real.pi_pos, sq_nonneg (Real.pi / 2)]
    · dsimp [axisParams, mismatchHalfNormSq, mismatchBoostHalf, mismatchRotationHalf, α, β]
      nlinarith [Real.pi_pos, sq_nonneg (Real.pi / 2)]
  · intro hAdm
    have hsum := (hAdm 0).2.2.2
    dsimp [axisParams, α, β] at hsum
    nlinarith [Real.pi_pos]

end RepulsionCone
end DstDiophantine