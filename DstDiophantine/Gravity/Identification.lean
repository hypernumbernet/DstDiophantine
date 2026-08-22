import DstDiophantine.Gravity.Weitzenbock
import DstDiophantine.Gravity.Sandwich
import DstDiophantine.Algebra.Invariant
import DstDiophantine.Algebra.Amplification
import DstDiophantine.Algebra.Motor
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Identification of `J` / `J⁵` with the teleparallel scalar

## Dictionary

| Symbol | Object | Role |
|--------|--------|------|
| `J(φ) = ½ φ²` | finite boost angle | parameter-space diagnostic |
| `J5 = J + ½ η_μν λ^μ λ^ν` | Lean / discrete-companion | torsion + translation diagnostic |
| `J_field = ½ (φ')²` | field seed from `∂_r φ` | same dimension class as `T` |
| `T` | Weitzenböck scalar | TEGR Lagrangian density |

Lean `J5` uses the discrete-companion `J = ½∑(α²−β²)`, **not** the paper's raw
`(1/16) B_Killing` (= `J/4` under the half-angle expansion).

## Proved / rejected

* `J(φ) = ½ φ²`, `T = -r⁻² formal∂_r(r² B^r)`, Minkowski `T = J_field = 0`.
* Boost leg: `∂_r √A = - φ' · √A`.
* **Rejected:** finite-angle `J = ½ T`; parametric `J5 = ½ T` on flat space;
  `J_field = ½ T` on Schwarzschild (concrete point).
* Corrected field dictionary for general motors remains open.
-/

namespace DstDiophantine

namespace Gravity

open Invariant Amplification Motor Real

/-- Convenience: exterior point used as the algebraic counterexample. -/
theorem isExterior_two_four : IsExterior (2 : ℝ) 4 :=
  ⟨by norm_num, by norm_num⟩

/-- Package of chart-level identification data at an exterior point. -/
structure SchwarzschildIdentification (rs r : ℝ) : Prop where
  exterior : IsExterior rs r
  /-- Parameter diagnostic (finite angle), not the field density. -/
  J_param :
    J (radialBoostParams rs r) = (1 / 2) * (schwarzschildRapidity rs r) ^ 2
  /-- Teleparallel scalar as a radial divergence. -/
  T_eq_div :
    schwarzschildTeleparallelT rs r =
      -(1 / r ^ 2) * formal_d_r2B_dr rs r
  /-- Field seed coefficient form. -/
  J_field_coef' :
    J_field rs r = rs ^ 2 / (8 * r ^ 4 * (schwarzschildA rs r) ^ 2)
  scales :
    let φ := schwarzschildRapidity rs r
    cosh φ - sinh φ = Real.sqrt (1 - rs / r) ∧
      cosh φ + sinh φ = (Real.sqrt (1 - rs / r))⁻¹

theorem schwarzschildIdentification_of_exterior {rs r : ℝ}
    (h : IsExterior rs r) : SchwarzschildIdentification rs r where
  exterior := h
  J_param := J_radialBoostParams
  T_eq_div := schwarzschild_T_eq_neg_r_inv_sq_formal_d_r2B h
  J_field_coef' := J_field_coef h
  scales := boost_eigenvalues_eq_schwarzschild_scales h.1 h.2

/-- On the diagonal gauge the translational sector vanishes, so `J⁵ = J`. -/
theorem J5_eq_J_of_radialBoost (rs r : ℝ) :
    J5 ⟨radialBoostParams rs r, ⟨fun _ => 0⟩⟩ = J (radialBoostParams rs r) := by
  simp [J5, minkowskiDot]

/-- Parameter diagnostic and field divergence, recorded separately. -/
theorem J5_and_T_on_schwarzschild_slice {rs r : ℝ} (h : IsExterior rs r) :
    J5 ⟨radialBoostParams rs r, ⟨fun _ => 0⟩⟩ =
        (1 / 2) * (schwarzschildRapidity rs r) ^ 2 ∧
      schwarzschildTeleparallelT rs r =
        -(1 / r ^ 2) * formal_d_r2B_dr rs r := by
  refine ⟨?_, schwarzschild_T_eq_neg_r_inv_sq_formal_d_r2B h⟩
  rw [J5_eq_J_of_radialBoost, J_radialBoostParams]

/-! ### Rejection of naive point identification -/

/-- Constant nonzero boost: parameter `J ≠ 0` while flat-chart `T = 0`. -/
theorem constant_boost_J_ne_zero_flat_T_zero (φ : ℝ) (hφ : φ ≠ 0) :
    J (Amplification.pureBoost φ) ≠ 0 ∧
      schwarzschildTeleparallelT 0 1 = 0 := by
  refine ⟨?_, (minkowski_T_and_J_field_zero (by norm_num : (0 : ℝ) < 1)).1⟩
  rw [Amplification.J_pureBoost]
  exact mul_ne_zero (by norm_num) (pow_ne_zero 2 hφ)

/-- Finite-angle `½ φ² = ½ T` fails (take `φ = 1`, flat `T = 0`). -/
theorem naive_finite_angle_eq_half_T_false :
    ∃ φ Tval : ℝ, φ ≠ 0 ∧ Tval = 0 ∧ (1 / 2 : ℝ) * φ ^ 2 ≠ (1 / 2) * Tval := by
  refine ⟨1, 0, one_ne_zero, rfl, ?_⟩
  norm_num

/-- Pure spatial translation: `J5 ≠ 0` with vanishing torsion. -/
theorem pure_spatial_translation_J5_ne_zero (L : ℝ) (hL : L ≠ 0) :
    J5 ⟨⟨fun _ => 0, fun _ => 0⟩, ⟨fun μ => if μ = 1 then L else 0⟩⟩ ≠ 0 := by
  have hJ : J ⟨fun _ => 0, fun _ => 0⟩ = 0 := by
    rw [J_coef]; simp
  have hdot :
      minkowskiDot (fun μ : Fin 4 => if μ = 1 then L else 0) = L ^ 2 := by
    simp [minkowskiDot, pow_two]
  simp only [J5, hJ, zero_add, hdot]
  exact mul_ne_zero (by norm_num) (pow_ne_zero 2 hL)

/-- Parametric `J5 ≠ ½ T` on Minkowski with a pure spatial translation. -/
theorem naive_parametric_J5_eq_half_flat_T_false :
    J5 ⟨⟨fun _ => 0, fun _ => 0⟩, ⟨fun μ => if μ = 1 then (1 : ℝ) else 0⟩⟩ ≠
      (1 / 2) * schwarzschildTeleparallelT 0 1 := by
  have hJ5 := pure_spatial_translation_J5_ne_zero 1 one_ne_zero
  have hT : schwarzschildTeleparallelT 0 1 = 0 :=
    (minkowski_T_and_J_field_zero (by norm_num : (0 : ℝ) < 1)).1
  simpa [hT] using hJ5

/-- Algebraic counterexample: `J_field ≠ ½ T` at `rₛ = 2`, `r = 4`. -/
theorem J_field_ne_half_T_schwarzschild_point :
    J_field 2 4 ≠ (1 / 2) * schwarzschildTeleparallelT 2 4 := by
  intro h
  have hA : schwarzschildA 2 4 = (1 : ℝ) / 2 := by
    simp only [schwarzschildA]; norm_num
  have hJf : J_field 2 4 = (1 : ℝ) / 128 := by
    rw [J_field_coef isExterior_two_four, hA]; norm_num
  set s := Real.sqrt ((1 : ℝ) / 2) with hs_def
  have hs2 : s ^ 2 = (1 : ℝ) / 2 := by
    rw [hs_def, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  have hs0 : s ≠ 0 := by
    rw [hs_def]
    exact (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 1 / 2)).ne'
  have hT : schwarzschildTeleparallelT 2 4 = (1 / 8) * (1 - s) ^ 2 / s := by
    simp only [schwarzschildTeleparallelT, hA, hs_def]
    norm_num
  rw [hJf, hT] at h
  have h1 : (1 : ℝ) / 8 = (1 - s) ^ 2 / s := by
    have h' : (1 : ℝ) / 128 = (1 / 16) * ((1 - s) ^ 2 / s) := by
      convert h using 1; ring
    have := congrArg (fun x : ℝ => 16 * x) h'
    field_simp [hs0] at this
    linarith
  have hEq : s = 8 * (1 - s) ^ 2 := by
    have := congrArg (fun x : ℝ => x * s) h1
    field_simp [hs0] at this
    linarith
  have hLin : s = (12 : ℝ) / 17 := by
    have : s = 8 * (1 - 2 * s + s ^ 2) := by
      convert hEq using 1; ring
    rw [hs2] at this
    linarith
  have : s ^ 2 = ((12 : ℝ) / 17) ^ 2 := by rw [hLin]
  rw [hs2] at this
  norm_num at this

/-! ### Rejected field-seed specialisation of the old conjecture -/

/-- Claim `J_field = ½ T` on a Schwarzschild exterior point (no arbitrary div). -/
def FieldSeedEqualsHalfT (rs r : ℝ) : Prop :=
  J_field rs r = (1 / 2) * schwarzschildTeleparallelT rs r

/-- Former vacuous stub, now the rejected reading `∀ exterior, J_field = ½ T`.
A corrected dictionary for general motor fields remains open. -/
def conjectured_J_field_eq_half_T_plus_div : Prop :=
  ∀ rs r : ℝ, IsExterior rs r → FieldSeedEqualsHalfT rs r

theorem conjectured_J_field_eq_half_T_plus_div_false :
    ¬ conjectured_J_field_eq_half_T_plus_div := by
  intro h
  exact J_field_ne_half_T_schwarzschild_point (h 2 4 isExterior_two_four)

/-- Legacy name of the rejected stub. -/
abbrev conjectured_J5_eq_half_T_plus_div : Prop :=
  conjectured_J_field_eq_half_T_plus_div

end Gravity

end DstDiophantine
