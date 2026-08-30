import DstDiophantine.Algebra.Motor
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Periodicity of cyclic versus hyperbolic rotor exponentials

Cyclic generators square to `-1`, so `exp(θ B⁻)` is `2π`-periodic in `θ`.
Hyperbolic generators square to `+1`, so `exp(θ B⁺)` is never `2π`-periodic.
Quantizing boosts onto a `2π`-torus is therefore a modelling choice, not a
consequence of the exponential map.
-/

namespace DstDiophantine

open CliffordAlgebra PGA Generators Motor NormedSpace Real

namespace Periodicity

theorem exp_cyclic_add_int_mul_two_pi (a : Fin 3) (θ : ℝ) (k : ℤ) :
    exp ((θ + 2 * π * k) • cyclic a) = exp (θ • cyclic a) := by
  rw [exp_of_sq_neg_one (cyclic_sq a), exp_of_sq_neg_one (cyclic_sq a)]
  have hc : cos (θ + 2 * π * k) = cos θ := by
    simpa [mul_comm, mul_assoc, mul_left_comm] using cos_add_int_mul_two_pi θ k
  have hs : sin (θ + 2 * π * k) = sin θ := by
    simpa [mul_comm, mul_assoc, mul_left_comm] using sin_add_int_mul_two_pi θ k
  rw [hc, hs]

theorem exp_cyclic_two_pi (a : Fin 3) :
    exp ((2 * π) • cyclic a) = 1 := by
  have h := exp_cyclic_add_int_mul_two_pi a 0 1
  simp only [Int.cast_one, mul_one, zero_add] at h
  rw [h, zero_smul, NormedSpace.exp_zero]

theorem hyperbolic_ne_zero (a : Fin 3) : hyperbolic a ≠ 0 := by
  intro h
  have : (1 : PGA) = 0 := by
    simpa [h] using hyperbolic_sq a
  exact one_ne_zero this

private theorem smul_one_eq_zero {c : ℝ} (h : c • (1 : PGA) = 0) (hc : c ≠ 0) :
    False := by
  have : (1 : PGA) = 0 := by
    calc (1 : PGA)
        = c⁻¹ • (c • (1 : PGA)) := (inv_smul_smul₀ hc (1 : PGA)).symm
      _ = c⁻¹ • 0 := by rw [h]
      _ = 0 := smul_zero _
  exact one_ne_zero this

private theorem smul_hyperbolic_eq_zero {c : ℝ} {a : Fin 3}
    (h : c • hyperbolic a = 0) (hc : c ≠ 0) : False := by
  have h1 : c • (1 : PGA) = 0 := by
    calc c • (1 : PGA)
        = c • (hyperbolic a * hyperbolic a) := by rw [hyperbolic_sq]
      _ = (c • hyperbolic a) * hyperbolic a := by rw [smul_mul_assoc]
      _ = 0 * hyperbolic a := by rw [h]
      _ = 0 := zero_mul _
  exact smul_one_eq_zero h1 hc

private theorem cosh_eq_iff_abs_eq {x y : ℝ} : cosh x = cosh y ↔ |x| = |y| := by
  constructor
  · intro h
    have : cosh |x| = cosh |y| := by rw [cosh_abs, cosh_abs, h]
    exact cosh_injOn (abs_nonneg x) (abs_nonneg y) this
  · intro h
    rw [← cosh_abs x, ← cosh_abs y, h]

/-- Hyperbolic rotor exponentials are nowhere `2π`-periodic. -/
theorem exp_hyperbolic_add_two_pi_ne (a : Fin 3) (θ : ℝ) :
    exp ((θ + 2 * π) • hyperbolic a) ≠ exp (θ • hyperbolic a) := by
  intro h
  rw [exp_of_sq_one (hyperbolic_sq a), exp_of_sq_one (hyperbolic_sq a)] at h
  set H := hyperbolic a
  set cΔ := cosh (θ + 2 * π) - cosh θ
  set sΔ := sinh (θ + 2 * π) - sinh θ
  have hsub : cΔ • (1 : PGA) + sΔ • H = 0 := by
    have := sub_eq_zero.mpr h
    convert this using 1
    simp only [cΔ, sΔ, sub_smul]
    abel
  have hrev : cΔ • (1 : PGA) + -(sΔ • H) = 0 := by
    have := congrArg reverse hsub
    simpa [map_add, map_smul, map_zero, reverse.map_one, hyperbolic_reverse, smul_neg, H]
      using this
  have h2 : (2 * cΔ) • (1 : PGA) = 0 := by
    have := congrArg₂ HAdd.hAdd hsub hrev
    simp only [add_zero] at this
    convert this using 1
    module
  have hc : cosh (θ + 2 * π) = cosh θ := by
    by_contra hne
    exact smul_one_eq_zero h2 (mul_ne_zero two_ne_zero (sub_ne_zero.mpr hne))
  have habs : |θ + 2 * π| = |θ| := (cosh_eq_iff_abs_eq).mp hc
  have hcases : θ + 2 * π = θ ∨ θ + 2 * π = -θ := abs_eq_abs.mp habs
  rcases hcases with hθ | hθ
  · have : (2 : ℝ) * π = 0 := by linarith
    exact (mul_ne_zero two_ne_zero pi_ne_zero) this
  · have hθπ : θ = -π := by linarith
    have hs : sΔ = 2 * sinh π := by
      simp only [sΔ, hθπ]
      have : -π + 2 * π = π := by ring
      rw [this, sinh_neg]
      ring
    have hH : sΔ • H = 0 := by
      have hc0 : cΔ = 0 := sub_eq_zero.mpr hc
      simpa [hc0, zero_smul, zero_add] using hsub
    have hsne : sΔ ≠ 0 := by
      rw [hs]
      exact mul_ne_zero two_ne_zero (sinh_pos_iff.mpr pi_pos).ne'
    exact smul_hyperbolic_eq_zero (a := a) hH hsne

theorem exp_hyperbolic_two_pi_ne_one (a : Fin 3) :
    exp ((2 * π) • hyperbolic a) ≠ 1 := by
  have h := exp_hyperbolic_add_two_pi_ne a 0
  simpa [zero_add, zero_smul, NormedSpace.exp_zero] using h

end Periodicity

end DstDiophantine
