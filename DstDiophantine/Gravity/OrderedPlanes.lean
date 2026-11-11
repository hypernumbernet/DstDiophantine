import DstDiophantine.Gravity.Coframe
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Order of a noncommuting boost and rotation

The `(t,x)` boost and the `(x,y)` rotation do not commute. Let the rapidity
`φ` depend only on `y`, with derivative `u`, and the angle `θ` only on `t`,
with derivative `v`. Both orders of the product coframe induce the Minkowski
metric. The teleparallel scalar keeps the order.

* Boost on the left: `T = -2 u v cos θ`.
* Rotation on the left: `T = -2 u v cosh φ`.

At vanishing rapidity and angle both equal `-2 u v`. For `u v ≠ 0` they agree
if and only if `φ = 0` and `cos θ = 1`. When `u v > 0`, the rotation-on-the-left
scalar is negative at every rapidity and every angle, the sign of the
attractive vacuum. The boost-on-the-left scalar has that sign exactly when
`cos θ > 0`.

## Not claimed

* Profiles in which either parameter depends on a coordinate other than the
  one named above.
* That the sign of this `T` is the sign of the mismatch `J`.
-/

namespace DstDiophantine

namespace Gravity

open Finset Real

/-- Jet with `∂_y = u`. -/
def profileJetY (u : ℝ) : Fin 4 → ℝ
  | 2 => u
  | _ => 0

/-- Jet with `∂_t = v`. -/
def profileJetT (v : ℝ) : Fin 4 → ℝ
  | 0 => v
  | _ => 0

/-! ### Boost on the left: `B(φ) R(θ)` -/

/-- Coframe `(B(φ) R(θ))^a_μ`. The boost stands on the left. -/
noncomputable def boostLeftCoframe (φ θ : ℝ) : Coframe :=
  fun a μ =>
    if a = 0 ∧ μ = 0 then Real.cosh φ
    else if a = 0 ∧ μ = 1 then Real.sinh φ * Real.cos θ
    else if a = 0 ∧ μ = 2 then Real.sinh φ * Real.sin θ
    else if a = 1 ∧ μ = 0 then Real.sinh φ
    else if a = 1 ∧ μ = 1 then Real.cosh φ * Real.cos θ
    else if a = 1 ∧ μ = 2 then Real.cosh φ * Real.sin θ
    else if a = 2 ∧ μ = 1 then -Real.sin θ
    else if a = 2 ∧ μ = 2 then Real.cos θ
    else if a = 3 ∧ μ = 3 then 1
    else 0

/-- `∂_φ` of `boostLeftCoframe`. -/
noncomputable def boostLeftDφ (φ θ : ℝ) : Coframe :=
  fun a μ =>
    if a = 0 ∧ μ = 0 then Real.sinh φ
    else if a = 0 ∧ μ = 1 then Real.cosh φ * Real.cos θ
    else if a = 0 ∧ μ = 2 then Real.cosh φ * Real.sin θ
    else if a = 1 ∧ μ = 0 then Real.cosh φ
    else if a = 1 ∧ μ = 1 then Real.sinh φ * Real.cos θ
    else if a = 1 ∧ μ = 2 then Real.sinh φ * Real.sin θ
    else 0

/-- `∂_θ` of `boostLeftCoframe`. -/
noncomputable def boostLeftDθ (φ θ : ℝ) : Coframe :=
  fun a μ =>
    if a = 0 ∧ μ = 1 then -(Real.sinh φ * Real.sin θ)
    else if a = 0 ∧ μ = 2 then Real.sinh φ * Real.cos θ
    else if a = 1 ∧ μ = 1 then -(Real.cosh φ * Real.sin θ)
    else if a = 1 ∧ μ = 2 then Real.cosh φ * Real.cos θ
    else if a = 2 ∧ μ = 1 then -Real.cos θ
    else if a = 2 ∧ μ = 2 then -Real.sin θ
    else 0

theorem inducedMetric_boostLeft (φ θ : ℝ) (μ ν : Fin 4) :
    inducedMetric (boostLeftCoframe φ θ) μ ν = if μ = ν then w31 μ else 0 := by
  rw [inducedMetric_eq_weighted]
  have hφ : Real.cosh φ ^ 2 = 1 + Real.sinh φ ^ 2 := by
    linarith [Real.cosh_sq_sub_sinh_sq φ]
  have hθ : Real.cos θ ^ 2 = 1 - Real.sin θ ^ 2 := by
    linarith [Real.cos_sq_add_sin_sq θ]
  fin_cases μ <;> fin_cases ν <;>
    simp [Fin.sum_univ_four, boostLeftCoframe, w31]
  all_goals ring_nf
  all_goals try rw [hφ]
  all_goals try rw [hθ]
  all_goals ring

/-- Inverse frame `(η Λᵀ η)^ρ_a` of the boost-on-the-left coframe. -/
noncomputable def boostLeftFrame (φ θ : ℝ) (ρ a : Fin 4) : ℝ :=
  w31 ρ * w31 a * boostLeftCoframe φ θ a ρ

theorem boostLeft_dual (φ θ : ℝ) (μ ν : Fin 4) :
    ∑ a : Fin 4, boostLeftCoframe φ θ a μ * boostLeftFrame φ θ ν a =
      if μ = ν then (1 : ℝ) else 0 := by
  have h := inducedMetric_boostLeft φ θ μ ν
  rw [inducedMetric_eq_weighted] at h
  have hsum :
      ∑ a : Fin 4, boostLeftCoframe φ θ a μ * boostLeftFrame φ θ ν a =
        w31 ν * ∑ a : Fin 4, w31 a * boostLeftCoframe φ θ a μ * boostLeftCoframe φ θ a ν := by
    simp only [boostLeftFrame, mul_assoc, mul_left_comm]
    rw [← Finset.mul_sum]
  rw [hsum, h]
  fin_cases μ <;> fin_cases ν <;> simp [w31]

/-- `e_a^ρ ∂_φ e^a_ν`, the boost generator conjugated by the rotation. -/
noncomputable def boostLeftKφ (φ θ : ℝ) (ρ ν : Fin 4) : ℝ :=
  ∑ a : Fin 4, boostLeftFrame φ θ ρ a * boostLeftDφ φ θ a ν

/-- `e_a^ρ ∂_θ e^a_ν`. On this order the rotation generator is unchanged. -/
noncomputable def boostLeftKθ (φ θ : ℝ) (ρ ν : Fin 4) : ℝ :=
  ∑ a : Fin 4, boostLeftFrame φ θ ρ a * boostLeftDθ φ θ a ν

set_option maxHeartbeats 800000 in
-- Sixteen index cases, each a four-term sum.
theorem boostLeftKφ_support (φ θ : ℝ) (ρ ν : Fin 4) :
    boostLeftKφ φ θ ρ ν =
      if ρ = 0 ∧ ν = 1 then Real.cos θ
      else if ρ = 0 ∧ ν = 2 then Real.sin θ
      else if ρ = 1 ∧ ν = 0 then Real.cos θ
      else if ρ = 2 ∧ ν = 0 then Real.sin θ
      else 0 := by
  have hφ : Real.cosh φ ^ 2 = 1 + Real.sinh φ ^ 2 := by
    linarith [Real.cosh_sq_sub_sinh_sq φ]
  fin_cases ρ <;> fin_cases ν <;>
    simp [boostLeftKφ, boostLeftFrame, boostLeftDφ, boostLeftCoframe, Fin.sum_univ_four, w31]
  all_goals ring_nf
  all_goals try rw [hφ]
  all_goals ring

set_option maxHeartbeats 800000 in
-- Sixteen index cases, each a four-term sum.
theorem boostLeftKθ_support (φ θ : ℝ) (ρ ν : Fin 4) :
    boostLeftKθ φ θ ρ ν =
      if ρ = 1 ∧ ν = 2 then 1
      else if ρ = 2 ∧ ν = 1 then -1
      else 0 := by
  have hφ : Real.cosh φ ^ 2 = 1 + Real.sinh φ ^ 2 := by
    linarith [Real.cosh_sq_sub_sinh_sq φ]
  have hθ : Real.cos θ ^ 2 = 1 - Real.sin θ ^ 2 := by
    linarith [Real.cos_sq_add_sin_sq θ]
  fin_cases ρ <;> fin_cases ν <;>
    simp [boostLeftKθ, boostLeftFrame, boostLeftDθ, boostLeftCoframe, Fin.sum_univ_four, w31]
  all_goals ring_nf
  all_goals try rw [hφ]
  all_goals try rw [hθ]
  all_goals ring

/-- Closed form of the boost-on-the-left coordinate torsion. Rapidity cancels. -/
noncomputable def boostLeftTorsionVal (θ u v : ℝ) : Fin 4 → Fin 4 → Fin 4 → ℝ
  | 0, 1, 2 => -(u * Real.cos θ)
  | 0, 2, 1 => u * Real.cos θ
  | 1, 0, 2 => -(u * Real.cos θ) + v
  | 1, 2, 0 => u * Real.cos θ - v
  | 2, 0, 1 => -v
  | 2, 1, 0 => v
  | 2, 0, 2 => -(u * Real.sin θ)
  | 2, 2, 0 => u * Real.sin θ
  | _, _, _ => 0

/-- Coordinate torsion of `∂_y φ = u` and `∂_t θ = v`. -/
noncomputable def boostLeftTorsion (φ θ u v : ℝ) (ρ μ ν : Fin 4) : ℝ :=
  profileJetY u μ * boostLeftKφ φ θ ρ ν - profileJetY u ν * boostLeftKφ φ θ ρ μ +
    (profileJetT v μ * boostLeftKθ φ θ ρ ν - profileJetT v ν * boostLeftKθ φ θ ρ μ)

set_option maxHeartbeats 800000 in
-- Sixteen index cases, each a four-term sum.
theorem boostLeftTorsion_support (φ θ u v : ℝ) (ρ μ ν : Fin 4) :
    boostLeftTorsion φ θ u v ρ μ ν = boostLeftTorsionVal θ u v ρ μ ν := by
  fin_cases ρ <;> fin_cases μ <;> fin_cases ν <;>
    simp [boostLeftTorsion, boostLeftTorsionVal, profileJetY, profileJetT, boostLeftKφ_support,
      boostLeftKθ_support] ; ring

noncomputable def boostLeftDown (φ θ u v : ℝ) (ρ μ ν : Fin 4) : ℝ :=
  w31 ρ * boostLeftTorsion φ θ u v ρ μ ν

noncomputable def boostLeftUp (φ θ u v : ℝ) (ρ μ ν : Fin 4) : ℝ :=
  w31 ρ * w31 μ * w31 ν * boostLeftDown φ θ u v ρ μ ν

noncomputable def boostLeftTrace (φ θ u v : ℝ) (ρ : Fin 4) : ℝ :=
  ∑ σ : Fin 4, boostLeftTorsion φ θ u v σ ρ σ

noncomputable def boostLeftTeleparallel (φ θ u v : ℝ) : ℝ :=
  (1 / 4) * (∑ ρ : Fin 4, ∑ μ : Fin 4, ∑ ν : Fin 4,
      boostLeftDown φ θ u v ρ μ ν * boostLeftUp φ θ u v ρ μ ν) +
    (1 / 2) * (∑ ρ : Fin 4, ∑ μ : Fin 4, ∑ ν : Fin 4,
      boostLeftDown φ θ u v ρ μ ν * boostLeftUp φ θ u v ν μ ρ) -
    ∑ ρ : Fin 4, boostLeftTrace φ θ u v ρ * (w31 ρ * boostLeftTrace φ θ u v ρ)

set_option maxHeartbeats 2000000 in
-- The teleparallel sum expands to sixty-four monomials before `field_simp`.
theorem boostLeftTeleparallel_eq (φ θ u v : ℝ) :
    boostLeftTeleparallel φ θ u v = -2 * u * v * Real.cos θ := by
  simp only [boostLeftTeleparallel, boostLeftDown, boostLeftUp, boostLeftTrace,
    boostLeftTorsion_support]
  repeat rw [Fin.sum_univ_four]
  dsimp only [boostLeftTorsionVal, w31]
  field_simp
  ring

/-! ### Rotation on the left: `R(θ) B(φ)` -/

/-- Coframe `(R(θ) B(φ))^a_μ`. The rotation stands on the left. -/
noncomputable def rotLeftCoframe (φ θ : ℝ) : Coframe :=
  fun a μ =>
    if a = 0 ∧ μ = 0 then Real.cosh φ
    else if a = 0 ∧ μ = 1 then Real.sinh φ
    else if a = 1 ∧ μ = 0 then Real.cos θ * Real.sinh φ
    else if a = 1 ∧ μ = 1 then Real.cos θ * Real.cosh φ
    else if a = 1 ∧ μ = 2 then Real.sin θ
    else if a = 2 ∧ μ = 0 then -(Real.sin θ * Real.sinh φ)
    else if a = 2 ∧ μ = 1 then -(Real.sin θ * Real.cosh φ)
    else if a = 2 ∧ μ = 2 then Real.cos θ
    else if a = 3 ∧ μ = 3 then 1
    else 0

/-- `∂_φ` of `rotLeftCoframe`. -/
noncomputable def rotLeftDφ (φ θ : ℝ) : Coframe :=
  fun a μ =>
    if a = 0 ∧ μ = 0 then Real.sinh φ
    else if a = 0 ∧ μ = 1 then Real.cosh φ
    else if a = 1 ∧ μ = 0 then Real.cos θ * Real.cosh φ
    else if a = 1 ∧ μ = 1 then Real.cos θ * Real.sinh φ
    else if a = 2 ∧ μ = 0 then -(Real.sin θ * Real.cosh φ)
    else if a = 2 ∧ μ = 1 then -(Real.sin θ * Real.sinh φ)
    else 0

/-- `∂_θ` of `rotLeftCoframe`. -/
noncomputable def rotLeftDθ (φ θ : ℝ) : Coframe :=
  fun a μ =>
    if a = 1 ∧ μ = 0 then -(Real.sin θ * Real.sinh φ)
    else if a = 1 ∧ μ = 1 then -(Real.sin θ * Real.cosh φ)
    else if a = 1 ∧ μ = 2 then Real.cos θ
    else if a = 2 ∧ μ = 0 then -(Real.cos θ * Real.sinh φ)
    else if a = 2 ∧ μ = 1 then -(Real.cos θ * Real.cosh φ)
    else if a = 2 ∧ μ = 2 then -Real.sin θ
    else 0

theorem inducedMetric_rotLeft (φ θ : ℝ) (μ ν : Fin 4) :
    inducedMetric (rotLeftCoframe φ θ) μ ν = if μ = ν then w31 μ else 0 := by
  rw [inducedMetric_eq_weighted]
  have hφ : Real.cosh φ ^ 2 = 1 + Real.sinh φ ^ 2 := by
    linarith [Real.cosh_sq_sub_sinh_sq φ]
  have hθ : Real.cos θ ^ 2 = 1 - Real.sin θ ^ 2 := by
    linarith [Real.cos_sq_add_sin_sq θ]
  fin_cases μ <;> fin_cases ν <;>
    simp [Fin.sum_univ_four, rotLeftCoframe, w31]
  all_goals ring_nf
  all_goals try rw [hφ]
  all_goals try rw [hθ]
  all_goals ring

noncomputable def rotLeftFrame (φ θ : ℝ) (ρ a : Fin 4) : ℝ :=
  w31 ρ * w31 a * rotLeftCoframe φ θ a ρ

theorem rotLeft_dual (φ θ : ℝ) (μ ν : Fin 4) :
    ∑ a : Fin 4, rotLeftCoframe φ θ a μ * rotLeftFrame φ θ ν a =
      if μ = ν then (1 : ℝ) else 0 := by
  have h := inducedMetric_rotLeft φ θ μ ν
  rw [inducedMetric_eq_weighted] at h
  have hsum :
      ∑ a : Fin 4, rotLeftCoframe φ θ a μ * rotLeftFrame φ θ ν a =
        w31 ν * ∑ a : Fin 4, w31 a * rotLeftCoframe φ θ a μ * rotLeftCoframe φ θ a ν := by
    simp only [rotLeftFrame, mul_assoc, mul_left_comm]
    rw [← Finset.mul_sum]
  rw [hsum, h]
  fin_cases μ <;> fin_cases ν <;> simp [w31]

noncomputable def rotLeftKφ (φ θ : ℝ) (ρ ν : Fin 4) : ℝ :=
  ∑ a : Fin 4, rotLeftFrame φ θ ρ a * rotLeftDφ φ θ a ν

noncomputable def rotLeftKθ (φ θ : ℝ) (ρ ν : Fin 4) : ℝ :=
  ∑ a : Fin 4, rotLeftFrame φ θ ρ a * rotLeftDθ φ θ a ν

set_option maxHeartbeats 800000 in
-- Sixteen index cases, each a four-term sum.
theorem rotLeftKφ_support (φ θ : ℝ) (ρ ν : Fin 4) :
    rotLeftKφ φ θ ρ ν =
      if ρ = 0 ∧ ν = 1 then 1
      else if ρ = 1 ∧ ν = 0 then 1
      else 0 := by
  have hφ : Real.cosh φ ^ 2 = 1 + Real.sinh φ ^ 2 := by
    linarith [Real.cosh_sq_sub_sinh_sq φ]
  have hθ : Real.cos θ ^ 2 = 1 - Real.sin θ ^ 2 := by
    linarith [Real.cos_sq_add_sin_sq θ]
  fin_cases ρ <;> fin_cases ν <;>
    simp [rotLeftKφ, rotLeftFrame, rotLeftDφ, rotLeftCoframe, Fin.sum_univ_four, w31]
  all_goals ring_nf
  all_goals try rw [hφ]
  all_goals try rw [hθ]
  all_goals ring

set_option maxHeartbeats 800000 in
-- Sixteen index cases, each a four-term sum.
theorem rotLeftKθ_support (φ θ : ℝ) (ρ ν : Fin 4) :
    rotLeftKθ φ θ ρ ν =
      if ρ = 0 ∧ ν = 2 then -Real.sinh φ
      else if ρ = 1 ∧ ν = 2 then Real.cosh φ
      else if ρ = 2 ∧ ν = 0 then -Real.sinh φ
      else if ρ = 2 ∧ ν = 1 then -Real.cosh φ
      else 0 := by
  have hθ : Real.cos θ ^ 2 = 1 - Real.sin θ ^ 2 := by
    linarith [Real.cos_sq_add_sin_sq θ]
  fin_cases ρ <;> fin_cases ν <;>
    simp [rotLeftKθ, rotLeftFrame, rotLeftDθ, rotLeftCoframe, Fin.sum_univ_four, w31]
  all_goals ring_nf
  all_goals try rw [hθ]
  all_goals ring

/-- Closed form of the rotation-on-the-left coordinate torsion. The angle cancels. -/
noncomputable def rotLeftTorsionVal (φ u v : ℝ) : Fin 4 → Fin 4 → Fin 4 → ℝ
  | 0, 0, 2 => -(v * Real.sinh φ)
  | 0, 2, 0 => v * Real.sinh φ
  | 0, 1, 2 => -u
  | 0, 2, 1 => u
  | 1, 0, 2 => -u + v * Real.cosh φ
  | 1, 2, 0 => u - v * Real.cosh φ
  | 2, 0, 1 => -(v * Real.cosh φ)
  | 2, 1, 0 => v * Real.cosh φ
  | _, _, _ => 0

noncomputable def rotLeftTorsion (φ θ u v : ℝ) (ρ μ ν : Fin 4) : ℝ :=
  profileJetY u μ * rotLeftKφ φ θ ρ ν - profileJetY u ν * rotLeftKφ φ θ ρ μ +
    (profileJetT v μ * rotLeftKθ φ θ ρ ν - profileJetT v ν * rotLeftKθ φ θ ρ μ)

set_option maxHeartbeats 800000 in
-- Sixteen index cases, each a four-term sum.
theorem rotLeftTorsion_support (φ θ u v : ℝ) (ρ μ ν : Fin 4) :
    rotLeftTorsion φ θ u v ρ μ ν = rotLeftTorsionVal φ u v ρ μ ν := by
  fin_cases ρ <;> fin_cases μ <;> fin_cases ν <;>
    simp [rotLeftTorsion, rotLeftTorsionVal, profileJetY, profileJetT,
      rotLeftKφ_support, rotLeftKθ_support] ; ring

noncomputable def rotLeftDown (φ θ u v : ℝ) (ρ μ ν : Fin 4) : ℝ :=
  w31 ρ * rotLeftTorsion φ θ u v ρ μ ν

noncomputable def rotLeftUp (φ θ u v : ℝ) (ρ μ ν : Fin 4) : ℝ :=
  w31 ρ * w31 μ * w31 ν * rotLeftDown φ θ u v ρ μ ν

noncomputable def rotLeftTrace (φ θ u v : ℝ) (ρ : Fin 4) : ℝ :=
  ∑ σ : Fin 4, rotLeftTorsion φ θ u v σ ρ σ

noncomputable def rotLeftTeleparallel (φ θ u v : ℝ) : ℝ :=
  (1 / 4) * (∑ ρ : Fin 4, ∑ μ : Fin 4, ∑ ν : Fin 4,
      rotLeftDown φ θ u v ρ μ ν * rotLeftUp φ θ u v ρ μ ν) +
    (1 / 2) * (∑ ρ : Fin 4, ∑ μ : Fin 4, ∑ ν : Fin 4,
      rotLeftDown φ θ u v ρ μ ν * rotLeftUp φ θ u v ν μ ρ) -
    ∑ ρ : Fin 4, rotLeftTrace φ θ u v ρ * (w31 ρ * rotLeftTrace φ θ u v ρ)

set_option maxHeartbeats 2000000 in
-- The teleparallel sum expands to sixty-four monomials before `field_simp`.
theorem rotLeftTeleparallel_eq (φ θ u v : ℝ) :
    rotLeftTeleparallel φ θ u v = -2 * u * v * Real.cosh φ := by
  simp only [rotLeftTeleparallel, rotLeftDown, rotLeftUp, rotLeftTrace,
    rotLeftTorsion_support]
  repeat rw [Fin.sum_univ_four]
  dsimp only [rotLeftTorsionVal, w31]
  field_simp
  ring

/-! ### What the order decides -/

theorem ordered_at_identity (u v : ℝ) :
    boostLeftTeleparallel 0 0 u v = -2 * u * v ∧
      rotLeftTeleparallel 0 0 u v = -2 * u * v := by
  rw [boostLeftTeleparallel_eq, rotLeftTeleparallel_eq, Real.cos_zero, Real.cosh_zero]
  constructor <;> ring

theorem cos_eq_cosh_iff (θ φ : ℝ) :
    Real.cos θ = Real.cosh φ ↔ φ = 0 ∧ Real.cos θ = 1 := by
  constructor
  · intro h
    have hcosh : Real.cosh φ = 1 :=
      le_antisymm (by rw [← h]; exact Real.cos_le_one θ) (Real.one_le_cosh φ)
    have hcos : Real.cos θ = 1 := by rw [h, hcosh]
    have hsq := Real.cosh_sq_sub_sinh_sq φ
    rw [hcosh] at hsq
    have hsinh2 : Real.sinh φ ^ 2 = 0 := by linarith
    have hsinh : Real.sinh φ = 0 := sq_eq_zero_iff.mp hsinh2
    exact ⟨(Real.sinh_eq_zero).mp hsinh, hcos⟩
  · rintro ⟨hφ, hθ⟩
    rw [hφ, hθ, Real.cosh_zero]

/-- For a nonzero product of derivatives, the two orders agree only at a
vanishing boost whose rotation has cosine one. -/
theorem ordered_agree_iff (φ θ u v : ℝ) (huv : u * v ≠ 0) :
    boostLeftTeleparallel φ θ u v = rotLeftTeleparallel φ θ u v ↔
      φ = 0 ∧ Real.cos θ = 1 := by
  rw [boostLeftTeleparallel_eq, rotLeftTeleparallel_eq]
  constructor
  · intro h
    have hmul : u * v * Real.cos θ = u * v * Real.cosh φ := by linarith
    have hcos : Real.cos θ = Real.cosh φ := mul_left_cancel₀ huv hmul
    exact (cos_eq_cosh_iff θ φ).mp hcos
  · rintro ⟨hφ, hθ⟩
    rw [hφ, hθ, Real.cosh_zero]

theorem rotLeft_has_vacuum_sign (φ θ u v : ℝ) (h : 0 < u * v) :
    rotLeftTeleparallel φ θ u v < 0 := by
  rw [rotLeftTeleparallel_eq]
  have hc : 0 < Real.cosh φ := Real.cosh_pos φ
  have h2 : 0 < 2 * (u * v) := mul_pos (by norm_num) h
  have hprod : 0 < 2 * (u * v) * Real.cosh φ := mul_pos h2 hc
  have hrewrite : 2 * u * v * Real.cosh φ = 2 * (u * v) * Real.cosh φ := by ring
  linarith

theorem boostLeft_has_vacuum_sign_iff (φ θ u v : ℝ) (h : 0 < u * v) :
    boostLeftTeleparallel φ θ u v < 0 ↔ 0 < Real.cos θ := by
  rw [boostLeftTeleparallel_eq]
  constructor
  · intro hT
    have hneg : -(2 * (u * v) * Real.cos θ) < 0 := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hT
    have hprod : 0 < 2 * (u * v) * Real.cos θ := by linarith
    have h2 : 0 < 2 * (u * v) := mul_pos (by norm_num) h
    exact (mul_pos_iff_of_pos_left h2).mp hprod
  · intro hc
    have h2 : 0 < 2 * (u * v) := mul_pos (by norm_num) h
    have : 0 < 2 * (u * v) * Real.cos θ := mul_pos h2 hc
    have hrewrite : 2 * u * v * Real.cos θ = 2 * (u * v) * Real.cos θ := by ring
    linarith

theorem ordered_opposite_at_pi (u v : ℝ) :
    boostLeftTeleparallel 0 Real.pi u v = 2 * u * v ∧
      rotLeftTeleparallel 0 Real.pi u v = -2 * u * v := by
  rw [boostLeftTeleparallel_eq, rotLeftTeleparallel_eq, Real.cos_pi, Real.cosh_zero]
  constructor <;> ring

theorem ordered_split_at_half_pi (u v : ℝ) :
    boostLeftTeleparallel 0 (Real.pi / 2) u v = 0 ∧
      rotLeftTeleparallel 0 (Real.pi / 2) u v = -2 * u * v := by
  rw [boostLeftTeleparallel_eq, rotLeftTeleparallel_eq, Real.cos_pi_div_two, Real.cosh_zero]
  constructor <;> ring

end Gravity

end DstDiophantine
