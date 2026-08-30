import DstDiophantine.Gravity.ElectronShell
import DstDiophantine.Algebra.Invariant
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Closed-form structure of the equal-scale torsional layers

## Paper boundary (do **not** claim)

The characteristic length `ℓ` is **not** a theorem of the dual-rotor algebra,
and neither is the identification of the layered phase with the strong force.
What this module establishes is the *shape* of the layer sequence once the
equal-scale ansatz `α(r) = β(r) = ℓ/r` is granted.

No theorem asserts `dst_derives_lambda`, `dst_derives_alpha_s`, or
`dst_derives_Amax`.

## What is proved

Write `x = ℓ/(2r)` and `gammaSEqual x = cosh x * cos x - sinh x * sin x`
(the equal-scale specialisation of `gammaS`).

* Exact derivative `gammaSEqual' x = -2 cosh x sin x`. Hence the critical
  points are exactly the multiples of `π`.
* Exact extremal values `gammaSEqual (nπ) = (-1)^n cosh (nπ)`.
* `gammaSEqual` is strictly monotone on each `[nπ, (n+1)π]` (decreasing for
  even `n`, increasing for odd `n`), so each such interval carries **exactly
  one** node, and the sign of `gammaSEqual` strictly alternates.
* Sharpened branch localisation: a positive node in `(nπ, (n+1)π)` in fact
  lies in `(nπ + π/4, nπ + π/2)`, because a node forces `tan x = 1/tanh x > 1`.
  This is strictly stronger than the `(nπ, nπ + π/2)` branch of
  `ElectronShell.resonanceBranch`.
* Consequent radius window `ℓ/((2n+1)π) < r_n < 2ℓ/((4n+1)π)`.
* Amplitude growth `cosh π * cosh (nπ) ≤ cosh ((n+1)π)`, hence
  `(cosh π)^n ≤ cosh (nπ)` with `11 < cosh π`; and the one-sided ceiling
  `cosh (a+π) < e^π cosh a`.
* Inward screening: the mid-layer (plateau) force factor
  `4π²n²/cosh (nπ)` is strictly decreasing for `n ≥ 1`, so the layer
  amplitudes do **not** grow toward the centre. The paper's "ever-increasing
  amplitude toward the centre" is refuted for this force law.
* On the equal-scale locus the Killing-form scalar vanishes identically,
  `J = 0`, while the unsigned mass `M` is positive. The layer order parameter
  is therefore `gammaS`, not `J`.
-/

namespace DstDiophantine

namespace Gravity

open Real Set Operations Invariant

/-! ### Equal-scale interference factor -/

/-- Equal-scale specialisation of `gammaS` in the dimensionless variable
`x = ℓ/(2r)`. -/
noncomputable def gammaSEqual (x : ℝ) : ℝ :=
  cosh x * cos x - sinh x * sin x

theorem gammaSEqual_eq_gammaS (x : ℝ) : gammaSEqual x = gammaS (2 * x) (2 * x) := by
  unfold gammaSEqual gammaS
  rw [show (2 * x) / 2 = x by ring]

theorem gammaSEqual_zero : gammaSEqual 0 = 1 := by
  simp [gammaSEqual]

theorem continuous_gammaSEqual : Continuous gammaSEqual := by
  unfold gammaSEqual
  exact (continuous_cosh.mul continuous_cos).sub (continuous_sinh.mul continuous_sin)

/-! ### The exact derivative -/

/-- Exact derivative identity `γ_s'(x) = -2 cosh x sin x`. -/
theorem hasDerivAt_gammaSEqual (x : ℝ) :
    HasDerivAt gammaSEqual (-2 * cosh x * sin x) x := by
  have h1 : HasDerivAt (fun y : ℝ => cosh y * cos y)
      (sinh x * cos x + cosh x * (-sin x)) x :=
    (Real.hasDerivAt_cosh x).mul (Real.hasDerivAt_cos x)
  have h2 : HasDerivAt (fun y : ℝ => sinh y * sin y)
      (cosh x * sin x + sinh x * cos x) x :=
    (Real.hasDerivAt_sinh x).mul (Real.hasDerivAt_sin x)
  have h3 := h1.sub h2
  have heq : (-2 * cosh x * sin x) =
      (sinh x * cos x + cosh x * (-sin x)) - (cosh x * sin x + sinh x * cos x) := by
    ring
  unfold gammaSEqual
  rw [heq]
  exact h3

theorem deriv_gammaSEqual (x : ℝ) :
    deriv gammaSEqual x = -2 * cosh x * sin x :=
  (hasDerivAt_gammaSEqual x).deriv

/-- The critical points are exactly the zeros of `sin`. -/
theorem deriv_gammaSEqual_eq_zero_iff (x : ℝ) :
    deriv gammaSEqual x = 0 ↔ sin x = 0 := by
  rw [deriv_gammaSEqual]
  have hc : cosh x ≠ 0 := (cosh_pos x).ne'
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h | h
    · rcases mul_eq_zero.mp h with h | h
      · norm_num at h
      · exact absurd h hc
    · exact h
  · intro h
    rw [h]
    ring

/-! ### Exact extremal values -/

private theorem neg_one_pow_mul_self (n : ℕ) : ((-1 : ℝ) ^ n) * ((-1 : ℝ) ^ n) = 1 := by
  rw [← pow_add, ← two_mul, pow_mul]
  norm_num

/-- `γ_s(nπ) = (-1)^n cosh(nπ)`: the plateau amplitudes alternate in sign and
grow like `cosh`. -/
theorem gammaSEqual_nat_mul_pi (n : ℕ) :
    gammaSEqual ((n : ℝ) * π) = (-1) ^ n * cosh ((n : ℝ) * π) := by
  unfold gammaSEqual
  rw [sin_nat_mul_pi, cos_nat_mul_pi]
  ring

theorem abs_gammaSEqual_nat_mul_pi (n : ℕ) :
    |gammaSEqual ((n : ℝ) * π)| = cosh ((n : ℝ) * π) := by
  rw [gammaSEqual_nat_mul_pi, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_pos (cosh_pos _)]

theorem gammaSEqual_nat_mul_pi_ne_zero (n : ℕ) :
    gammaSEqual ((n : ℝ) * π) ≠ 0 := by
  intro h
  have := abs_gammaSEqual_nat_mul_pi n
  rw [h, abs_zero] at this
  exact absurd this.symm (cosh_pos _).ne'

/-! ### Sign of `sin` on a branch -/

private theorem sin_nat_mul_pi_add (n : ℕ) (t : ℝ) :
    sin ((n : ℝ) * π + t) = (-1) ^ n * sin t := by
  rw [sin_add, sin_nat_mul_pi, cos_nat_mul_pi]
  ring

private theorem cos_nat_mul_pi_add (n : ℕ) (t : ℝ) :
    cos ((n : ℝ) * π + t) = (-1) ^ n * cos t := by
  rw [cos_add, cos_nat_mul_pi, sin_nat_mul_pi]
  ring

/-- On the interior of the `n`-th `π`-interval the signed sine is positive. -/
theorem signed_sin_pos_on_branch (n : ℕ) {x : ℝ}
    (hx : x ∈ Ioo ((n : ℝ) * π) ((n : ℝ) * π + π)) :
    0 < (-1 : ℝ) ^ n * sin x := by
  obtain ⟨h1, h2⟩ := hx
  have hxt : x = (n : ℝ) * π + (x - (n : ℝ) * π) := by ring
  have ht0 : 0 < x - (n : ℝ) * π := by linarith
  have htπ : x - (n : ℝ) * π < π := by linarith
  have hsin : 0 < sin (x - (n : ℝ) * π) := sin_pos_of_pos_of_lt_pi ht0 htπ
  rw [hxt, sin_nat_mul_pi_add, ← mul_assoc, neg_one_pow_mul_self, one_mul]
  exact hsin

/-! ### Strict monotonicity on each branch -/

/-- Sign-corrected interference factor: strictly decreasing on the `n`-th
`π`-interval for every `n`. -/
noncomputable def gammaSSigned (n : ℕ) (x : ℝ) : ℝ := (-1 : ℝ) ^ n * gammaSEqual x

theorem gammaSSigned_eq_zero_iff (n : ℕ) (x : ℝ) :
    gammaSSigned n x = 0 ↔ gammaSEqual x = 0 := by
  unfold gammaSSigned
  have hne : ((-1 : ℝ) ^ n) ≠ 0 := by positivity
  simp [mul_eq_zero, hne]

theorem hasDerivAt_gammaSSigned (n : ℕ) (x : ℝ) :
    HasDerivAt (gammaSSigned n) ((-1 : ℝ) ^ n * (-2 * cosh x * sin x)) x :=
  (hasDerivAt_gammaSEqual x).const_mul _

theorem deriv_gammaSSigned (n : ℕ) (x : ℝ) :
    deriv (gammaSSigned n) x = (-1 : ℝ) ^ n * (-2 * cosh x * sin x) :=
  (hasDerivAt_gammaSSigned n x).deriv

theorem continuous_gammaSSigned (n : ℕ) : Continuous (gammaSSigned n) := by
  unfold gammaSSigned
  exact continuous_const.mul continuous_gammaSEqual

theorem strictAntiOn_gammaSSigned (n : ℕ) :
    StrictAntiOn (gammaSSigned n) (Icc ((n : ℝ) * π) ((n : ℝ) * π + π)) := by
  refine strictAntiOn_of_deriv_neg (convex_Icc _ _)
    (continuous_gammaSSigned n).continuousOn ?_
  intro x hx
  rw [interior_Icc] at hx
  have hs := signed_sin_pos_on_branch n hx
  have hc := cosh_pos x
  have hrw : ((-1 : ℝ) ^ n) * (-2 * cosh x * sin x)
      = -2 * cosh x * ((-1 : ℝ) ^ n * sin x) := by ring
  rw [deriv_gammaSSigned, hrw]
  nlinarith [hs, hc]

/-- `γ_s` is strictly decreasing on `[2kπ, (2k+1)π]`. -/
theorem strictAntiOn_gammaSEqual_even (k : ℕ) :
    StrictAntiOn gammaSEqual
      (Icc (((2 * k : ℕ) : ℝ) * π) (((2 * k : ℕ) : ℝ) * π + π)) := by
  have h := strictAntiOn_gammaSSigned (2 * k)
  intro a ha b hb hab
  have hlt := h ha hb hab
  unfold gammaSSigned at hlt
  rw [pow_mul] at hlt
  norm_num at hlt
  exact hlt

/-- `γ_s` is strictly increasing on `[(2k+1)π, (2k+2)π]`. -/
theorem strictMonoOn_gammaSEqual_odd (k : ℕ) :
    StrictMonoOn gammaSEqual
      (Icc (((2 * k + 1 : ℕ) : ℝ) * π) (((2 * k + 1 : ℕ) : ℝ) * π + π)) := by
  have h := strictAntiOn_gammaSSigned (2 * k + 1)
  intro a ha b hb hab
  have hlt := h ha hb hab
  unfold gammaSSigned at hlt
  rw [pow_succ, pow_mul] at hlt
  norm_num at hlt
  exact hlt

/-! ### Exactly one node per `π`-interval -/

private theorem gammaSSigned_left (n : ℕ) :
    gammaSSigned n ((n : ℝ) * π) = cosh ((n : ℝ) * π) := by
  unfold gammaSSigned
  rw [gammaSEqual_nat_mul_pi, ← mul_assoc, neg_one_pow_mul_self, one_mul]

private theorem gammaSSigned_right (n : ℕ) :
    gammaSSigned n ((n : ℝ) * π + π) = -cosh (((n : ℝ) + 1) * π) := by
  have hcast : ((n : ℝ) + 1) * π = ((n + 1 : ℕ) : ℝ) * π := by push_cast; ring
  have harg : (n : ℝ) * π + π = ((n + 1 : ℕ) : ℝ) * π := by push_cast; ring
  unfold gammaSSigned
  rw [harg, gammaSEqual_nat_mul_pi, hcast, ← mul_assoc, pow_succ]
  rw [show ((-1 : ℝ) ^ n * ((-1 : ℝ) ^ n * (-1))) = -(((-1 : ℝ) ^ n) * ((-1 : ℝ) ^ n)) by ring,
    neg_one_pow_mul_self]
  ring

/-- Each `π`-interval carries exactly one torsional node. -/
theorem exists_unique_node_branch (n : ℕ) :
    ∃! x : ℝ, x ∈ Ioo ((n : ℝ) * π) ((n : ℝ) * π + π) ∧ gammaSEqual x = 0 := by
  have hab : (n : ℝ) * π ≤ (n : ℝ) * π + π := by linarith [pi_pos]
  have hcont : ContinuousOn (gammaSSigned n)
      (Icc ((n : ℝ) * π) ((n : ℝ) * π + π)) :=
    (continuous_gammaSSigned n).continuousOn
  have hmem : (0 : ℝ) ∈ Ioo (gammaSSigned n ((n : ℝ) * π + π))
      (gammaSSigned n ((n : ℝ) * π)) := by
    rw [gammaSSigned_left, gammaSSigned_right]
    exact ⟨by linarith [cosh_pos (((n : ℝ) + 1) * π)], cosh_pos ((n : ℝ) * π)⟩
  obtain ⟨x, hxIoo, hxeq⟩ := intermediate_value_Ioo' hab hcont hmem
  refine ⟨x, ⟨hxIoo, (gammaSSigned_eq_zero_iff n x).mp hxeq⟩, ?_⟩
  rintro y ⟨hyIoo, hyeq⟩
  have hy : gammaSSigned n y = 0 := (gammaSSigned_eq_zero_iff n y).mpr hyeq
  have hxIcc : x ∈ Icc ((n : ℝ) * π) ((n : ℝ) * π + π) := Ioo_subset_Icc_self hxIoo
  have hyIcc : y ∈ Icc ((n : ℝ) * π) ((n : ℝ) * π + π) := Ioo_subset_Icc_self hyIoo
  rcases lt_trichotomy y x with h | h | h
  · have := strictAntiOn_gammaSSigned n hyIcc hxIcc h
    rw [hy, hxeq] at this
    exact absurd this (lt_irrefl 0)
  · exact h
  · have := strictAntiOn_gammaSSigned n hxIcc hyIcc h
    rw [hy, hxeq] at this
    exact absurd this (lt_irrefl 0)

/-! ### A node forces `tan x > 1` -/

theorem cos_ne_zero_of_gammaSEqual_eq_zero {x : ℝ} (hx : 0 < x)
    (h : gammaSEqual x = 0) : cos x ≠ 0 := by
  intro hc
  have hs : 0 < sinh x := sinh_pos_iff.mpr hx
  have hsin : sin x = 0 := by
    unfold gammaSEqual at h
    rw [hc, mul_zero, zero_sub, neg_eq_zero] at h
    rcases mul_eq_zero.mp h with h1 | h1
    · exact absurd h1 hs.ne'
    · exact h1
  have hpyth := sin_sq_add_cos_sq x
  rw [hsin, hc] at hpyth
  norm_num at hpyth

theorem tan_eq_of_gammaSEqual_eq_zero {x : ℝ} (hx : 0 < x)
    (h : gammaSEqual x = 0) : tan x = cosh x / sinh x := by
  have hs : 0 < sinh x := sinh_pos_iff.mpr hx
  have hc : cos x ≠ 0 := cos_ne_zero_of_gammaSEqual_eq_zero hx h
  have hbal : cosh x * cos x = sinh x * sin x := by
    unfold gammaSEqual at h; linarith
  rw [tan_eq_sin_div_cos, div_eq_div_iff hc hs.ne', mul_comm (sin x) (sinh x)]
  exact hbal.symm

/-- A node forces `tan x = 1/tanh x > 1`. -/
theorem one_lt_tan_of_gammaSEqual_eq_zero {x : ℝ} (hx : 0 < x)
    (h : gammaSEqual x = 0) : 1 < tan x := by
  have hs : 0 < sinh x := sinh_pos_iff.mpr hx
  rw [tan_eq_of_gammaSEqual_eq_zero hx h, lt_div_iff₀ hs]
  have hsub := cosh_sub_sinh x
  have hp := exp_pos (-x)
  linarith

/-! ### Sharpened branch localisation -/

private theorem mem_quarter_half_of_one_lt_tan {t : ℝ}
    (ht0 : 0 < t) (htπ : t < π) (hcos : cos t ≠ 0) (htan : 1 < tan t) :
    π / 4 < t ∧ t < π / 2 := by
  have hπ := pi_pos
  have hne : t ≠ π / 2 := by
    intro hEq
    rw [hEq, cos_pi_div_two] at hcos
    exact hcos rfl
  have hlt : t < π / 2 := by
    rcases lt_or_gt_of_ne hne with hcase | hcase
    · exact hcase
    · exfalso
      have hcosneg : cos t < 0 := by
        have hstep := strictAntiOn_cos
          (a := π / 2) (b := t) ⟨by linarith, by linarith⟩
          ⟨by linarith, le_of_lt htπ⟩ hcase
        rwa [cos_pi_div_two] at hstep
      have hsinpos : 0 < sin t := sin_pos_of_pos_of_lt_pi ht0 htπ
      have htneg : tan t < 0 := by
        rw [tan_eq_sin_div_cos]
        exact div_neg_of_pos_of_neg hsinpos hcosneg
      linarith
  refine ⟨?_, hlt⟩
  by_contra hcon
  have hcon' : t ≤ π / 4 := not_lt.mp hcon
  have hmem₁ : t ∈ Ioo (-(π / 2)) (π / 2) := ⟨by linarith, hlt⟩
  have hmem₂ : π / 4 ∈ Ioo (-(π / 2)) (π / 2) := ⟨by linarith, by linarith⟩
  rcases eq_or_lt_of_le hcon' with hEq | hlt2
  · rw [hEq, tan_pi_div_four] at htan
    linarith
  · have hstep := strictMonoOn_tan hmem₁ hmem₂ hlt2
    rw [tan_pi_div_four] at hstep
    linarith

/-- Sharpened localisation: a node of the `n`-th branch lies in
`(nπ + π/4, nπ + π/2)`, not merely in `(nπ, nπ + π/2)`. -/
theorem node_mem_sharp_branch (n : ℕ) {x : ℝ}
    (hx : x ∈ Ioo ((n : ℝ) * π) ((n : ℝ) * π + π)) (h : gammaSEqual x = 0) :
    x ∈ Ioo ((n : ℝ) * π + π / 4) ((n : ℝ) * π + π / 2) := by
  obtain ⟨h1, h2⟩ := hx
  have hπ := pi_pos
  have hn0 : (0 : ℝ) ≤ (n : ℝ) * π := by positivity
  have hxpos : 0 < x := lt_of_le_of_lt hn0 h1
  set t := x - (n : ℝ) * π with ht
  have ht0 : 0 < t := by simp only [ht]; linarith
  have htπ : t < π := by simp only [ht]; linarith
  have hxt : x = (n : ℝ) * π + t := by simp only [ht]; ring
  have hcos : cos t ≠ 0 := by
    have hcx := cos_ne_zero_of_gammaSEqual_eq_zero hxpos h
    intro hc0
    rw [hxt, cos_nat_mul_pi_add, hc0, mul_zero] at hcx
    exact hcx rfl
  have htan : 1 < tan t := by
    have hper : tan (t + (n : ℝ) * π) = tan t :=
      (tan_periodic.nat_mul n) t
    have hcx := one_lt_tan_of_gammaSEqual_eq_zero hxpos h
    rw [hxt, add_comm ((n : ℝ) * π) t, hper] at hcx
    exact hcx
  obtain ⟨hlo, hhi⟩ := mem_quarter_half_of_one_lt_tan ht0 htπ hcos htan
  constructor
  · simp only [ht] at hlo; linarith
  · simp only [ht] at hhi; linarith

/-! ### Bridge to the resonance product `tanh x · tan x` -/

theorem gammaSEqual_eq_zero_iff_resonanceProd {x : ℝ} (hc : cos x ≠ 0) :
    gammaSEqual x = 0 ↔ resonanceProd x = 1 := by
  have hhalf : (2 * x) / 2 = x := by ring
  have hc' : cos ((2 * x) / 2) ≠ 0 := by rwa [hhalf]
  rw [gammaSEqual_eq_gammaS, gammaS_eq_zero_iff (2 * x) (2 * x) hc', hhalf]
  rfl

theorem resonanceRoot1_gammaSEqual_zero : gammaSEqual resonanceRoot1 = 0 := by
  obtain ⟨hlo, hhi⟩ := resonanceRoot1_bounds
  have hπ := pi_pos
  have hcos : cos resonanceRoot1 ≠ 0 := by
    refine (cos_pos_of_mem_Ioo ⟨by linarith, ?_⟩).ne'
    linarith [pi_gt_d2]
  exact (gammaSEqual_eq_zero_iff_resonanceProd hcos).mpr resonanceRoot1_prod

/-- Sharpened bracket for the outermost root: `π/4 < x₁ < 1`. -/
theorem resonanceRoot1_sharp_bounds :
    π / 4 < resonanceRoot1 ∧ resonanceRoot1 < 1 := by
  obtain ⟨hlo, hhi⟩ := resonanceRoot1_bounds
  have hπ := pi_pos
  have hmem : resonanceRoot1 ∈ Ioo (((0 : ℕ) : ℝ) * π) (((0 : ℕ) : ℝ) * π + π) := by
    refine ⟨by simpa using by linarith, ?_⟩
    simp only [Nat.cast_zero, zero_mul, zero_add]
    linarith [pi_gt_d2]
  have hsharp := node_mem_sharp_branch 0 hmem resonanceRoot1_gammaSEqual_zero
  simp only [Nat.cast_zero, zero_mul, zero_add, mem_Ioo] at hsharp
  exact ⟨hsharp.1, hhi⟩

/-- The second node exists and lies in the sharpened second branch. -/
theorem exists_second_node_sharp :
    ∃ x₂ : ℝ, x₂ ∈ Ioo (π + π / 4) (π + π / 2) ∧ gammaSEqual x₂ = 0 := by
  obtain ⟨x, ⟨hxIoo, hxeq⟩, -⟩ := exists_unique_node_branch 1
  have hsharp := node_mem_sharp_branch 1 hxIoo hxeq
  simp only [Nat.cast_one, one_mul] at hsharp
  exact ⟨x, hsharp, hxeq⟩

/-! ### Layer radii -/

/-- Equal-scale layer radius `r = ℓ/(2x)`. -/
noncomputable def layerRadius (ℓ x : ℝ) : ℝ := ℓ / (2 * x)

/-- The sharpened branch window `(nπ + π/4, nπ + π/2)` converts into the radius
window `ℓ/((2n+1)π) < r < 2ℓ/((4n+1)π)`. -/
theorem layerRadius_window {ℓ x : ℝ} (hℓ : 0 < ℓ) (n : ℕ)
    (hx : x ∈ Ioo ((n : ℝ) * π + π / 4) ((n : ℝ) * π + π / 2)) :
    ℓ / ((2 * (n : ℝ) + 1) * π) < layerRadius ℓ x ∧
      layerRadius ℓ x < 2 * ℓ / ((4 * (n : ℝ) + 1) * π) := by
  obtain ⟨h1, h2⟩ := hx
  have hπ := pi_pos
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hxpos : 0 < x := by nlinarith
  have hden1 : 0 < (2 * (n : ℝ) + 1) * π := by positivity
  have hden2 : 0 < (4 * (n : ℝ) + 1) * π := by positivity
  unfold layerRadius
  constructor
  · rw [div_lt_div_iff₀ hden1 (by positivity)]
    nlinarith [h2]
  · rw [div_lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * x) hden2]
    nlinarith [h1]

/-- Outermost branch `n = 0`: `ℓ/π < r₁ < 2ℓ/π`. -/
theorem layerRadius_window_zero {ℓ x : ℝ} (hℓ : 0 < ℓ)
    (hx : x ∈ Ioo (π / 4) (π / 2)) :
    ℓ / π < layerRadius ℓ x ∧ layerRadius ℓ x < 2 * ℓ / π := by
  have hx' : x ∈ Ioo (((0 : ℕ) : ℝ) * π + π / 4) (((0 : ℕ) : ℝ) * π + π / 2) := by
    simpa using hx
  have h := layerRadius_window hℓ 0 hx'
  simpa using h

/-- Every node, on every branch, satisfies `r < 2ℓ/π`: the outermost node is
the largest layer radius. -/
theorem layerRadius_lt_two_ell_div_pi {ℓ x : ℝ} (hℓ : 0 < ℓ) (n : ℕ)
    (hx : x ∈ Ioo ((n : ℝ) * π + π / 4) ((n : ℝ) * π + π / 2)) :
    layerRadius ℓ x < 2 * ℓ / π := by
  have hπ := pi_pos
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hupper := (layerRadius_window hℓ n hx).2
  refine lt_of_lt_of_le hupper ?_
  rw [div_le_div_iff₀ (by positivity) hπ]
  nlinarith [mul_nonneg (mul_nonneg hℓ.le hπ.le) hn0]

/-! ### Amplitude growth of the plateau values -/

/-- `cosh π · cosh(nπ) ≤ cosh((n+1)π)`: each layer amplifies by at least
`cosh π`. -/
theorem cosh_pi_mul_cosh_le (a : ℝ) (ha : 0 ≤ a) :
    cosh π * cosh a ≤ cosh (a + π) := by
  rw [cosh_add]
  have hs : 0 ≤ sinh a := by
    rcases eq_or_lt_of_le ha with rfl | h
    · simp
    · exact (sinh_pos_iff.mpr h).le
  have hsπ : 0 < sinh π := sinh_pos_iff.mpr pi_pos
  nlinarith [hs, hsπ]

theorem cosh_pi_mul_growth (n : ℕ) :
    cosh π * cosh ((n : ℝ) * π) ≤ cosh (((n : ℝ) + 1) * π) := by
  have harg : ((n : ℝ) + 1) * π = (n : ℝ) * π + π := by ring
  rw [harg]
  exact cosh_pi_mul_cosh_le _ (by positivity)

/-- Exponential amplitude growth `(cosh π)^n ≤ cosh(nπ)`. -/
theorem cosh_pi_pow_le_cosh_nat_mul_pi (n : ℕ) :
    cosh π ^ n ≤ cosh ((n : ℝ) * π) := by
  induction n with
  | zero => simp
  | succ k ih =>
    have hgrow := cosh_pi_mul_growth k
    have hcast : ((k : ℝ) + 1) * π = ((k + 1 : ℕ) : ℝ) * π := by push_cast; ring
    have hpos : 0 < cosh π := cosh_pos π
    calc cosh π ^ (k + 1)
        = cosh π * cosh π ^ k := by ring
      _ ≤ cosh π * cosh ((k : ℝ) * π) :=
          mul_le_mul_of_nonneg_left ih hpos.le
      _ ≤ cosh (((k : ℝ) + 1) * π) := hgrow
      _ = cosh (((k + 1 : ℕ) : ℝ) * π) := by rw [hcast]

/-- Numeric floor `11 < cosh π`, so the per-layer amplification exceeds `11`. -/
theorem eleven_lt_cosh_pi : (11 : ℝ) < cosh π := by
  have he1 : (2.7182818283 : ℝ) < exp 1 := exp_one_gt_d9
  have he1pos : (0 : ℝ) < exp 1 := exp_pos 1
  have hexp3 : exp 1 * exp 1 * exp 1 = exp 3 := by
    rw [← exp_add, ← exp_add]
    norm_num
  have h3 : (20 : ℝ) < exp 3 := by
    rw [← hexp3]
    nlinarith [he1, he1pos]
  have hπ : (3.14 : ℝ) < π := pi_gt_d2
  have h2 : (1.14 : ℝ) < exp (π - 3) := by
    have hle := Real.add_one_le_exp (π - 3)
    linarith
  have hsplit : exp π = exp 3 * exp (π - 3) := by
    rw [← exp_add]
    ring_nf
  have hexpπ : (22 : ℝ) < exp π := by
    rw [hsplit]
    nlinarith [h3, h2, exp_pos (3 : ℝ), exp_pos (π - 3)]
  rw [cosh_eq]
  have := exp_pos (-π)
  linarith

theorem eleven_pow_le_cosh_nat_mul_pi (n : ℕ) :
    (11 : ℝ) ^ n ≤ cosh ((n : ℝ) * π) :=
  le_trans (pow_le_pow_left₀ (by norm_num) eleven_lt_cosh_pi.le n)
    (cosh_pi_pow_le_cosh_nat_mul_pi n)

/-- Exact shortfall below the `e^π` ceiling. -/
theorem exp_pi_mul_cosh_sub_cosh_add_pi (a : ℝ) :
    exp π * cosh a - cosh (a + π) = sinh π * exp (-a) := by
  have h1 : exp π = cosh π + sinh π := (cosh_add_sinh π).symm
  have h2 : cosh a - sinh a = exp (-a) := cosh_sub_sinh a
  rw [cosh_add, h1]
  have hrw : sinh π * exp (-a) = sinh π * (cosh a - sinh a) := by rw [h2]
  rw [hrw]
  ring

/-- One-sided ceiling: the per-layer amplification never reaches `e^π`. -/
theorem cosh_add_pi_lt_exp_pi_mul (a : ℝ) :
    cosh (a + π) < exp π * cosh a := by
  have hid := exp_pi_mul_cosh_sub_cosh_add_pi a
  have hpos : 0 < sinh π * exp (-a) :=
    mul_pos (sinh_pos_iff.mpr pi_pos) (exp_pos _)
  linarith

/-- The per-layer amplification ratio `cosh(a+π)/cosh a` is strictly increasing
in `a`, so it climbs strictly below the `e^π` ceiling. -/
theorem cosh_add_pi_ratio_strictMono {a b : ℝ} (hab : a < b) :
    cosh (a + π) * cosh b < cosh (b + π) * cosh a := by
  have hid : cosh (a + π) * cosh b - cosh (b + π) * cosh a
      = sinh π * sinh (a - b) := by
    rw [cosh_add, cosh_add, sinh_sub]
    ring
  have hneg : sinh π * sinh (a - b) < 0 :=
    mul_neg_of_pos_of_neg (sinh_pos_iff.mpr pi_pos)
      (sinh_neg_iff.mpr (by linarith))
  linarith

/-- `cosh` never exceeds `exp` on the non-negative reals, so plateau amplitudes
grow no faster than `e^{nπ}`. -/
theorem cosh_le_exp_of_nonneg {a : ℝ} (ha : 0 ≤ a) : cosh a ≤ exp a := by
  rw [cosh_eq]
  have hle : exp (-a) ≤ exp a := exp_le_exp.mpr (by linarith)
  linarith

theorem cosh_nat_mul_pi_le_exp (n : ℕ) :
    cosh ((n : ℝ) * π) ≤ exp ((n : ℝ) * π) :=
  cosh_le_exp_of_nonneg (by positivity)

/-! ### Inward screening of the mid-layer force -/

/-- Mid-layer (plateau) force factor: the force at the extremal radius
`r = ℓ/(2nπ)` is `k/(γ_s r²)`, i.e. `k/ℓ²` times this factor. -/
noncomputable def plateauForceFactor (n : ℕ) : ℝ :=
  4 * π ^ 2 * (n : ℝ) ^ 2 / cosh ((n : ℝ) * π)

theorem plateauForceFactor_nonneg (n : ℕ) : 0 ≤ plateauForceFactor n := by
  unfold plateauForceFactor
  positivity

/-- The plateau force factor strictly decreases inward: layer amplitudes are
exponentially screened, not amplified. -/
theorem plateauForceFactor_strictAnti (n : ℕ) (hn : 1 ≤ n) :
    plateauForceFactor (n + 1) < plateauForceFactor n := by
  have hπ := pi_pos
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hcn : 0 < cosh ((n : ℝ) * π) := cosh_pos _
  have hcast : (((n + 1 : ℕ)) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
  have hgrow : cosh π * cosh ((n : ℝ) * π) ≤ cosh ((((n + 1 : ℕ)) : ℝ) * π) := by
    rw [hcast]
    exact cosh_pi_mul_growth n
  have hcn1 : 0 < cosh ((((n + 1 : ℕ)) : ℝ) * π) := cosh_pos _
  have hsq : 4 * π ^ 2 * ((((n + 1 : ℕ)) : ℝ)) ^ 2
      ≤ 4 * (4 * π ^ 2 * (n : ℝ) ^ 2) := by
    rw [hcast]
    nlinarith [hn1, sq_nonneg ((n : ℝ) - 1), pi_pos, sq_nonneg π]
  have hcosh11 : (11 : ℝ) < cosh π := eleven_lt_cosh_pi
  have hnum : 0 < 4 * π ^ 2 * (n : ℝ) ^ 2 :=
    mul_pos (by positivity) (pow_pos (by linarith : (0 : ℝ) < (n : ℝ)) 2)
  unfold plateauForceFactor
  rw [div_lt_div_iff₀ hcn1 hcn]
  calc 4 * π ^ 2 * (((n + 1 : ℕ)) : ℝ) ^ 2 * cosh ((n : ℝ) * π)
      ≤ 4 * (4 * π ^ 2 * (n : ℝ) ^ 2) * cosh ((n : ℝ) * π) :=
        mul_le_mul_of_nonneg_right hsq hcn.le
    _ < (4 * π ^ 2 * (n : ℝ) ^ 2) * (cosh π * cosh ((n : ℝ) * π)) := by
        have hACn : 0 < (4 * π ^ 2 * (n : ℝ) ^ 2) * cosh ((n : ℝ) * π) :=
          mul_pos hnum hcn
        nlinarith [hACn, hcosh11]
    _ ≤ (4 * π ^ 2 * (n : ℝ) ^ 2) * cosh ((((n + 1 : ℕ)) : ℝ) * π) :=
        mul_le_mul_of_nonneg_left hgrow hnum.le

/-- Refutation of the "ever-increasing amplitude toward the centre" reading:
already at the first plateau pair the factor decreases. -/
theorem paper_amplitude_increase_inward_false :
    ¬ (∀ n : ℕ, 1 ≤ n → plateauForceFactor n < plateauForceFactor (n + 1)) := by
  intro h
  have h1 := h 1 le_rfl
  have h2 := plateauForceFactor_strictAnti 1 le_rfl
  linarith

/-! ### The equal-scale locus is the balanced locus `J = 0` -/

/-- Equal-scale torsion parameters `α = β`. -/
def equalScaleParams (α : Fin 3 → ℝ) : TorsionParams where
  alpha := α
  beta := α

/-- On the equal-scale locus the Killing-form scalar vanishes identically. -/
theorem J_equalScaleParams (α : Fin 3 → ℝ) : J (equalScaleParams α) = 0 := by
  rw [J_coef]
  simp [equalScaleParams]

theorem mass_equalScaleParams (α : Fin 3 → ℝ) :
    mass (equalScaleParams α) = ∑ a : Fin 3, (α a) ^ 2 := by
  rw [mass_coef]
  simp only [equalScaleParams, Fin.sum_univ_three]
  ring

/-- The equal-scale locus is massive: `J = 0` with `M > 0`. -/
theorem mass_equalScaleParams_pos {α : Fin 3 → ℝ} (h : ∃ a, α a ≠ 0) :
    0 < mass (equalScaleParams α) := by
  obtain ⟨a, ha⟩ := h
  rw [mass_equalScaleParams]
  refine Finset.sum_pos' (fun i _ => sq_nonneg (α i)) ⟨a, Finset.mem_univ a, ?_⟩
  exact pow_pos (abs_pos.mpr ha) 2 |>.trans_le (by rw [sq_abs])

/-- The layer order parameter is `gammaS`, not `J`: on the equal-scale locus
`J` vanishes while `gammaSEqual` changes sign. -/
theorem layer_order_parameter_is_gammaS :
    (∀ α : Fin 3 → ℝ, J (equalScaleParams α) = 0) ∧
      ∃ x y : ℝ, 0 < gammaSEqual x ∧ gammaSEqual y < 0 := by
  refine ⟨J_equalScaleParams, 0, π, ?_, ?_⟩
  · rw [gammaSEqual_zero]; norm_num
  · have h := gammaSEqual_nat_mul_pi 1
    norm_num at h
    rw [h]
    have := cosh_pos π
    linarith

end Gravity

end DstDiophantine
