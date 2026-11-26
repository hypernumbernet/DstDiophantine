import DstDiophantine.Algebra.Admissible
import DstDiophantine.Algebra.MismatchAngle
import DstDiophantine.Algebra.RelativeRotor

set_option linter.style.whitespace false

/-!
# Repulsion cone vs mismatch half-norm box

Admissibility `α+β ≤ π/2` (per axis, nonnegative) implies each axis lies inside the
mismatch half-coefficient box `‖(−α/2, β/2)‖₂ ≤ π/2`. The converse is **false**:
large boost with zero dual rotation can violate `α ≤ π/2` while still fitting the box.
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
  have hαle : α ≤ Real.pi / 2 := by linarith [hβ, hsum]
  have hβle : β ≤ Real.pi / 2 := by linarith [hα, hsum]
  have hαdiv : α / 2 ≤ Real.pi / 4 := by linarith
  have hβdiv : β / 2 ≤ Real.pi / 4 := by linarith
  have hαhalf : (α / 2) ^ 2 ≤ (Real.pi / 4) ^ 2 :=
    pow_le_pow_left₀ (div_nonneg hα (by norm_num)) hαdiv 2
  have hβhalf : (β / 2) ^ 2 ≤ (Real.pi / 4) ^ 2 :=
    pow_le_pow_left₀ (div_nonneg hβ (by norm_num)) hβdiv 2
  nlinarith [sq_nonneg (α - β)]

theorem admissibleContinuous_implies_mismatch_half_box (p : TorsionParams)
    (h : IsAdmissibleContinuous p) (a : Fin 3) :
    mismatchBoostHalf (p.alpha a) (p.beta a) ^ 2 +
        mismatchRotationHalf (p.alpha a) (p.beta a) ^ 2 ≤
      (Real.pi / 2) ^ 2 := by
  have := (h a)
  exact admissible_axis_implies_mismatch_half_box (h a).1 (h a).2.1 (h a).2.2

/-- Counterexample: mismatch half-box on every axis does **not** imply admissibility. -/
theorem mismatch_half_box_not_implies_admissible :
    (∃ p : TorsionParams,
        (∀ a : Fin 3,
            mismatchBoostHalf (p.alpha a) (p.beta a) ^ 2 +
                mismatchRotationHalf (p.alpha a) (p.beta a) ^ 2 ≤
              (Real.pi / 2) ^ 2) ∧
          ¬ IsAdmissibleContinuous p) := by
  refine ⟨axisParams (0.9 * Real.pi) 0, ?_, ?_⟩
  · intro a
    fin_cases a <;>
      simp [axisParams, mismatchBoostHalf, mismatchRotationHalf, mul_pow, sq]
    all_goals
      have hπ : 0 < Real.pi := Real.pi_pos
      nlinarith [Real.pi_pos, sq_nonneg (0.9 * Real.pi), sq_nonneg (Real.pi / 2)]
  · intro h
    have hsum := (h 0).2.2
    simp [axisParams] at hsum
    linarith [Real.pi_pos]

end RepulsionCone
end DstDiophantine