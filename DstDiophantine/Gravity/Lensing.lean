import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-!
# Weak deflection by a thin signed shell

## What this is

The lens map of one thin spherical shell in the weak-deflection normalisation
already used for a point mass. Angles are measured in units of the shell's
angular radius, so the dimensionless radius `ξ = b / R` is the angular
coordinate, and `dᾱ/dθ` in those units is the physical radial derivative.
The parameter `c` is `(bₘ / R)²` when the shell is attractive. It is
negative, with `|c| = (bₘ / R)²`, when the shell is repulsive.

## What is proved

* The tangential ratio `ᾱ/θ` stays strictly below `c` on the open disk and
  the radial slope does not stay finite: for `c > 0` it exceeds every bound
  at some radius short of the limb.
* On an attractive shell there is a unique interior radial critical curve
  precisely when `c < 2`, i.e. `R > bₘ / √2`, and a unique interior
  tangential critical curve precisely when `1 < c < 2`, i.e.
  `bₘ / √2 < R < bₘ`. In that window the tangential curve lies outside the
  radial one. Outside the shell the map is the point mass of the shell:
  an Einstein ring when `R < bₘ`, and never a radial critical curve.
* On a repulsive shell both `ᾱ/θ` and the interior slope stay negative, so
  the disk contains neither critical curve.

## Not claimed

* A value for the shell mass, hence a prediction of which window is
  occupied, or of any magnification.
* The critical curves of a stack. An interior mass shifts the tangential
  ratio by a finite amount and does not cancel the radial divergence, but
  the windows above are the case of vanishing interior mass.
* A null integration through the frozen chart, or the identification of
  `F = k/(γₛ r²)` with a ray.
-/

namespace DstDiophantine

namespace Gravity

open Real

/-! ### Profiles -/

/-- `√(1 - ξ²)`, the cosine of the limb angle. -/
noncomputable def limbS (ξ : ℝ) : ℝ :=
  Real.sqrt (1 - ξ ^ 2)

/-- Fraction of the shell's mass enclosed by a cylinder of radius `ξ R`. -/
noncomputable def enclosedFraction (ξ : ℝ) : ℝ :=
  1 - limbS ξ

/-- Reduced deflection `ᾱ` inside the shell, in units of the shell's angular radius. -/
noncomputable def interiorDeflection (c ξ : ℝ) : ℝ :=
  c * ξ / (1 + limbS ξ)

/-- Tangential ratio `ᾱ/θ` inside the shell. -/
noncomputable def tangentialRatio (c ξ : ℝ) : ℝ :=
  c / (1 + limbS ξ)

/-- Radial slope `dᾱ/dθ` inside the shell. -/
noncomputable def radialSlope (c ξ : ℝ) : ℝ :=
  c / (limbS ξ * (1 + limbS ξ))

/-- Reduced deflection outside the shell. -/
noncomputable def exteriorDeflection (c ξ : ℝ) : ℝ :=
  c / ξ

/-- Nonnegative root of `s² + s = c`. -/
noncomputable def radialCriticalS (c : ℝ) : ℝ :=
  (-1 + Real.sqrt (1 + 4 * c)) / 2

/-- Value of `limbS` on an interior tangential critical curve. -/
noncomputable def tangentialCriticalS (c : ℝ) : ℝ :=
  c - 1

/-- Dimensionless radius with a prescribed `limbS`. -/
noncomputable def xiOfS (s : ℝ) : ℝ :=
  Real.sqrt (1 - s ^ 2)

/-! ### Algebra of the enclosed fraction -/

theorem limbS_sq {ξ : ℝ} (hξ : ξ ^ 2 ≤ 1) : limbS ξ ^ 2 = 1 - ξ ^ 2 := by
  unfold limbS
  exact Real.sq_sqrt (by linarith)

theorem limbS_nonneg (ξ : ℝ) : 0 ≤ limbS ξ :=
  Real.sqrt_nonneg _

theorem limbS_pos {ξ : ℝ} (hξ : ξ ^ 2 < 1) : 0 < limbS ξ := by
  have hpos : 0 < 1 - ξ ^ 2 := by linarith
  unfold limbS
  exact Real.sqrt_pos.mpr hpos

theorem limbS_le_one {ξ : ℝ} (hξ : 0 ≤ ξ ^ 2) : limbS ξ ≤ 1 := by
  have hle : 1 - ξ ^ 2 ≤ 1 := by linarith
  calc
    limbS ξ = Real.sqrt (1 - ξ ^ 2) := rfl
    _ ≤ Real.sqrt 1 := Real.sqrt_le_sqrt hle
    _ = 1 := Real.sqrt_one

theorem enclosedFraction_eq {ξ : ℝ} (hξ : ξ ^ 2 ≤ 1) :
    enclosedFraction ξ = ξ ^ 2 / (1 + limbS ξ) := by
  have hs : limbS ξ ^ 2 = 1 - ξ ^ 2 := limbS_sq hξ
  have hden : 1 + limbS ξ ≠ 0 := by linarith [limbS_nonneg ξ]
  unfold enclosedFraction
  apply (mul_right_inj' hden).mp
  field_simp [hden]
  nlinarith [hs]

theorem tangentialRatio_eq_enclosed {c ξ : ℝ} (hξ : ξ ^ 2 ≤ 1) (hξ0 : ξ ≠ 0) :
    tangentialRatio c ξ = c * enclosedFraction ξ / ξ ^ 2 := by
  have _ := hξ0
  rw [enclosedFraction_eq hξ]
  unfold tangentialRatio
  have hden : 1 + limbS ξ ≠ 0 := by linarith [limbS_nonneg ξ]
  field_simp [hden]

theorem tangentialRatio_mul_xi {c ξ : ℝ} :
    tangentialRatio c ξ * ξ = interiorDeflection c ξ := by
  unfold tangentialRatio interiorDeflection
  have hden : 1 + limbS ξ ≠ 0 := by linarith [limbS_nonneg ξ]
  field_simp [hden]

/-! ### The slope is the derivative of the deflection -/

theorem hasDerivAt_limbS {ξ : ℝ} (hξ : ξ ^ 2 < 1) :
    HasDerivAt limbS (-ξ / limbS ξ) ξ := by
  have hpos : 0 < 1 - ξ ^ 2 := by linarith
  have hne : (1 : ℝ) - ξ ^ 2 ≠ 0 := by linarith
  unfold limbS
  convert (HasDerivAt.sqrt ((hasDerivAt_const ξ (1 : ℝ)).sub (hasDerivAt_pow 2 ξ)) hne)
    using 1
  · funext y
    rfl
  · have hpoint :
        (((fun x : ℝ => (1 : ℝ)) - (fun x : ℝ => x ^ 2) : ℝ → ℝ) ξ) = 1 - ξ ^ 2 := rfl
    rw [hpoint]
    field_simp [Real.sqrt_ne_zero'.mpr hpos]
    ring

theorem hasDerivAt_interiorDeflection {c ξ : ℝ} (hξ : ξ ^ 2 < 1) :
    HasDerivAt (interiorDeflection c) (radialSlope c ξ) ξ := by
  have hs0 : limbS ξ ≠ 0 := (limbS_pos hξ).ne'
  have hden_ne : 1 + limbS ξ ≠ 0 := by linarith [limbS_nonneg ξ]
  have hs2 : limbS ξ ^ 2 = 1 - ξ ^ 2 := limbS_sq (le_of_lt hξ)
  have hnum : HasDerivAt (fun y : ℝ => c * y) (c * 1) ξ :=
    HasDerivAt.const_mul c (hasDerivAt_id ξ)
  have hden : HasDerivAt (fun y : ℝ => (fun _ : ℝ => (1 : ℝ)) y + limbS y)
      (0 + -ξ / limbS ξ) ξ :=
    (hasDerivAt_const ξ (1 : ℝ)).add (hasDerivAt_limbS hξ)
  have hdiv := hnum.fun_div hden hden_ne
  unfold interiorDeflection radialSlope
  convert hdiv using 1
  · rfl
  · rfl
  · have hone : ((fun x : ℝ => (1 : ℝ)) ξ) = 1 := rfl
    rw [hone, zero_add, mul_one]
    field_simp [hs0, hden_ne]
    rw [show ξ ^ 2 = 1 - limbS ξ ^ 2 by linarith [hs2]]
    ring

theorem hasDerivAt_exteriorDeflection {c ξ : ℝ} (hξ : ξ ≠ 0) :
    HasDerivAt (exteriorDeflection c) (-c / ξ ^ 2) ξ := by
  have hdiv := (hasDerivAt_const ξ c).fun_div (hasDerivAt_id ξ) hξ
  unfold exteriorDeflection
  convert hdiv using 1
  · rfl
  · rfl
  · funext y
    simp [id]
  · simp [id]

/-! ### Monotonicity -/

theorem limbS_anti {ξ₁ ξ₂ : ℝ} (h1 : 0 ≤ ξ₁) (hlt : ξ₁ < ξ₂) (h2 : ξ₂ ^ 2 < 1) :
    limbS ξ₂ < limbS ξ₁ := by
  have hξ2 : 0 ≤ ξ₂ := h1.trans hlt.le
  have hsq : ξ₁ * ξ₁ < ξ₂ * ξ₂ := (mul_self_lt_mul_self_iff h1 hξ2).mp hlt
  have hnn : 0 ≤ 1 - ξ₂ ^ 2 := by nlinarith [h2]
  have hlt' : 1 - ξ₂ ^ 2 < 1 - ξ₁ ^ 2 := by
    have h1sq : ξ₁ ^ 2 = ξ₁ * ξ₁ := by ring
    have h2sq : ξ₂ ^ 2 = ξ₂ * ξ₂ := by ring
    nlinarith [hsq, h1sq, h2sq]
  unfold limbS
  exact Real.sqrt_lt_sqrt hnn hlt'

theorem tangentialRatio_strictMono {c ξ₁ ξ₂ : ℝ} (hc : 0 < c)
    (h1 : 0 ≤ ξ₁) (hlt : ξ₁ < ξ₂) (h2 : ξ₂ ^ 2 < 1) :
    tangentialRatio c ξ₁ < tangentialRatio c ξ₂ := by
  have hs := limbS_anti h1 hlt h2
  have hden1 : 0 < 1 + limbS ξ₁ := by linarith [limbS_nonneg ξ₁]
  have hden2 : 0 < 1 + limbS ξ₂ := by linarith [limbS_nonneg ξ₂]
  have hden : 1 + limbS ξ₂ < 1 + limbS ξ₁ := by linarith
  unfold tangentialRatio
  exact (div_lt_div_iff_of_pos_left hc hden1 hden2).mpr hden

theorem radialSlope_strictMono {c ξ₁ ξ₂ : ℝ} (hc : 0 < c)
    (h1 : 0 ≤ ξ₁) (hlt : ξ₁ < ξ₂) (h2 : ξ₂ ^ 2 < 1) :
    radialSlope c ξ₁ < radialSlope c ξ₂ := by
  have hs := limbS_anti h1 hlt h2
  have hs1 : 0 < limbS ξ₁ := by
    have : ξ₁ ^ 2 < 1 := by
      have hξ2 : 0 ≤ ξ₂ := h1.trans hlt.le
      have hsq : ξ₁ * ξ₁ < ξ₂ * ξ₂ := (mul_self_lt_mul_self_iff h1 hξ2).mp hlt
      have h2sq : ξ₂ ^ 2 = ξ₂ * ξ₂ := by ring
      nlinarith [h2, hsq, h2sq]
    exact limbS_pos this
  have hs2 : 0 < limbS ξ₂ := limbS_pos h2
  have hden1 : 0 < limbS ξ₁ * (1 + limbS ξ₁) := by
    have : 0 < 1 + limbS ξ₁ := by linarith [limbS_nonneg ξ₁]
    exact mul_pos hs1 this
  have hden2 : 0 < limbS ξ₂ * (1 + limbS ξ₂) := by
    have : 0 < 1 + limbS ξ₂ := by linarith [limbS_nonneg ξ₂]
    exact mul_pos hs2 this
  have hden : limbS ξ₂ * (1 + limbS ξ₂) < limbS ξ₁ * (1 + limbS ξ₁) := by
    nlinarith [hs, limbS_nonneg ξ₁, limbS_nonneg ξ₂]
  unfold radialSlope
  exact (div_lt_div_iff_of_pos_left hc hden1 hden2).mpr hden

/-! ### Critical radii -/

theorem radialCriticalS_mul {c : ℝ} (hc : 0 ≤ c) :
    radialCriticalS c * (1 + radialCriticalS c) = c := by
  have hnn : (0 : ℝ) ≤ 1 + 4 * c := by linarith
  have hsq : Real.sqrt (1 + 4 * c) * Real.sqrt (1 + 4 * c) = 1 + 4 * c := by
    rw [← pow_two, Real.sq_sqrt hnn]
  unfold radialCriticalS
  have hsum : 1 + (-1 + Real.sqrt (1 + 4 * c)) / 2 =
      (1 + Real.sqrt (1 + 4 * c)) / 2 := by ring
  rw [hsum]
  field_simp
  nlinarith [hsq]

theorem radialCriticalS_nonneg {c : ℝ} (hc : 0 ≤ c) : 0 ≤ radialCriticalS c := by
  have hle : (1 : ℝ) ≤ 1 + 4 * c := by linarith
  have hsqrt : Real.sqrt 1 ≤ Real.sqrt (1 + 4 * c) := Real.sqrt_le_sqrt hle
  have hone : Real.sqrt 1 = 1 := Real.sqrt_one
  unfold radialCriticalS
  linarith [hsqrt, hone]

theorem radialCriticalS_lt_one {c : ℝ} (hc0 : 0 ≤ c) (hc : c < 2) :
    radialCriticalS c < 1 := by
  have hnn : (0 : ℝ) ≤ 1 + 4 * c := by linarith
  have h3 : (0 : ℝ) ≤ 3 := by norm_num
  have hlt : 1 + 4 * c < 3 ^ 2 := by nlinarith
  have hsqrt : Real.sqrt (1 + 4 * c) < Real.sqrt (3 ^ 2) := Real.sqrt_lt_sqrt hnn hlt
  have hsq : Real.sqrt (3 ^ 2) = 3 := Real.sqrt_sq h3
  unfold radialCriticalS
  linarith [hsqrt, hsq]

theorem radialCriticalS_pos {c : ℝ} (hc : 0 < c) : 0 < radialCriticalS c := by
  have hmul := radialCriticalS_mul hc.le
  have hnn := radialCriticalS_nonneg hc.le
  have hne : radialCriticalS c ≠ 0 := by
    intro h
    rw [h] at hmul
    linarith
  exact lt_of_le_of_ne hnn hne.symm

theorem xiOfS_limbS {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    limbS (xiOfS s) = s := by
  have hnn : 0 ≤ 1 - s ^ 2 := by nlinarith
  unfold limbS xiOfS
  rw [Real.sq_sqrt hnn]
  have : 1 - (1 - s ^ 2) = s ^ 2 := by ring
  rw [this, Real.sqrt_sq hs0]

theorem xiOfS_pos {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) : 0 < xiOfS s := by
  have hpos : 0 < 1 - s ^ 2 := by nlinarith
  unfold xiOfS
  exact Real.sqrt_pos.mpr hpos

theorem xiOfS_lt_one {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) : xiOfS s < 1 := by
  have hnn : 0 ≤ 1 - s ^ 2 := by nlinarith
  have hlt : 1 - s ^ 2 < 1 := by nlinarith
  calc
    xiOfS s = Real.sqrt (1 - s ^ 2) := rfl
    _ < Real.sqrt 1 := Real.sqrt_lt_sqrt hnn hlt
    _ = 1 := Real.sqrt_one

theorem xiOfS_anti {s₁ s₂ : ℝ} (h1 : 0 ≤ s₁) (hlt : s₁ < s₂) (h2 : s₂ ≤ 1) :
    xiOfS s₂ < xiOfS s₁ := by
  have hnn : 0 ≤ 1 - s₂ ^ 2 := by nlinarith
  have hlt' : 1 - s₂ ^ 2 < 1 - s₁ ^ 2 := by nlinarith
  unfold xiOfS
  exact Real.sqrt_lt_sqrt hnn hlt'

theorem tangentialRatio_axis {c : ℝ} : tangentialRatio c 0 = c / 2 := by
  have hlimb : limbS 0 = 1 := by
    unfold limbS
    simp [Real.sqrt_one]
  unfold tangentialRatio
  rw [hlimb]
  ring

theorem radialSlope_axis {c : ℝ} : radialSlope c 0 = c / 2 := by
  have hlimb : limbS 0 = 1 := by
    unfold limbS
    simp [Real.sqrt_one]
  unfold radialSlope
  rw [hlimb]
  ring

theorem tangentialRatio_at_witness {c : ℝ} (h1 : 1 < c) (h2 : c < 2) :
    tangentialRatio c (xiOfS (tangentialCriticalS c)) = 1 := by
  have hs0 : 0 ≤ tangentialCriticalS c := by unfold tangentialCriticalS; linarith
  have hs1 : tangentialCriticalS c ≤ 1 := by unfold tangentialCriticalS; linarith
  have hc : c ≠ 0 := by linarith
  unfold tangentialRatio
  rw [xiOfS_limbS hs0 hs1, tangentialCriticalS]
  have hsum : 1 + (c - 1) = c := by ring
  rw [hsum, div_self hc]

theorem radialSlope_at_witness {c : ℝ} (h0 : 0 < c) (h2 : c < 2) :
    radialSlope c (xiOfS (radialCriticalS c)) = 1 := by
  have hs0 := radialCriticalS_nonneg h0.le
  have hs1 := (radialCriticalS_lt_one h0.le h2).le
  have hmul := radialCriticalS_mul h0.le
  unfold radialSlope
  rw [xiOfS_limbS hs0 hs1]
  rw [show radialCriticalS c * (1 + radialCriticalS c) = c from hmul]
  field_simp [h0.ne']

theorem tangential_s_lt_radial_s {c : ℝ} (h1 : 1 < c) (h2 : c < 2) :
    tangentialCriticalS c < radialCriticalS c := by
  have hs0 : 0 ≤ radialCriticalS c := radialCriticalS_nonneg (by linarith)
  have hs1 : radialCriticalS c < 1 := radialCriticalS_lt_one (by linarith) h2
  have hmul : radialCriticalS c * (1 + radialCriticalS c) = c :=
    radialCriticalS_mul (by linarith)
  have hsq : radialCriticalS c * radialCriticalS c < 1 * 1 :=
    (mul_self_lt_mul_self_iff hs0 (by norm_num : (0 : ℝ) ≤ 1)).mp hs1
  unfold tangentialCriticalS
  nlinarith [hmul, hsq]

/-- In the window, the tangential critical curve lies outside the radial one. -/
theorem radial_caustic_lt_tangential {c : ℝ} (h1 : 1 < c) (h2 : c < 2) :
    xiOfS (radialCriticalS c) < xiOfS (tangentialCriticalS c) := by
  have hs0 : 0 < tangentialCriticalS c := by unfold tangentialCriticalS; linarith
  have hr0 : 0 ≤ radialCriticalS c := radialCriticalS_nonneg (by linarith)
  have hr1 : radialCriticalS c ≤ 1 := (radialCriticalS_lt_one (by linarith) h2).le
  have hlt := tangential_s_lt_radial_s h1 h2
  exact xiOfS_anti hs0.le hlt hr1

theorem existsUnique_interior_tangential {c : ℝ} (h1 : 1 < c) (h2 : c < 2) :
    ∃! ξ : ℝ, 0 < ξ ∧ ξ < 1 ∧ tangentialRatio c ξ = 1 := by
  let ξ₀ := xiOfS (tangentialCriticalS c)
  have hs0 : 0 < tangentialCriticalS c := by unfold tangentialCriticalS; linarith
  have hs1 : tangentialCriticalS c < 1 := by unfold tangentialCriticalS; linarith
  have hξ0 : 0 < ξ₀ := xiOfS_pos hs0.le hs1
  have hξ1 : ξ₀ < 1 := xiOfS_lt_one hs0 hs1.le
  have hval := tangentialRatio_at_witness h1 h2
  refine ⟨ξ₀, ⟨hξ0, hξ1, hval⟩, ?_⟩
  intro ξ hξ
  have hc : 0 < c := by linarith
  have hξsq : ξ ^ 2 < 1 := by nlinarith [hξ.1, hξ.2.1]
  have hξ0sq : ξ₀ ^ 2 < 1 := by nlinarith [hξ0, hξ1]
  rcases lt_trichotomy ξ ξ₀ with hlt | heq | hgt
  · have hmono := tangentialRatio_strictMono hc hξ.1.le hlt hξ0sq
    linarith [hξ.2.2, hval]
  · exact heq
  · have hmono := tangentialRatio_strictMono hc hξ0.le hgt hξsq
    linarith [hξ.2.2, hval]

theorem existsUnique_interior_radial {c : ℝ} (h0 : 0 < c) (h2 : c < 2) :
    ∃! ξ : ℝ, 0 < ξ ∧ ξ < 1 ∧ radialSlope c ξ = 1 := by
  let ξ₀ := xiOfS (radialCriticalS c)
  have hs0 := radialCriticalS_nonneg h0.le
  have hs1 := radialCriticalS_lt_one h0.le h2
  have hpos := radialCriticalS_pos h0
  have hξ0 : 0 < ξ₀ := xiOfS_pos hs0 hs1
  have hξ1 : ξ₀ < 1 := xiOfS_lt_one hpos hs1.le
  have hval := radialSlope_at_witness h0 h2
  refine ⟨ξ₀, ⟨hξ0, hξ1, hval⟩, ?_⟩
  intro ξ hξ
  have hξsq : ξ ^ 2 < 1 := by nlinarith [hξ.1, hξ.2.1]
  have hξ0sq : ξ₀ ^ 2 < 1 := by nlinarith [hξ0, hξ1]
  rcases lt_trichotomy ξ ξ₀ with hlt | heq | hgt
  · have hmono := radialSlope_strictMono h0 hξ.1.le hlt hξ0sq
    linarith [hξ.2.2, hval]
  · exact heq
  · have hmono := radialSlope_strictMono h0 hξ0.le hgt hξsq
    linarith [hξ.2.2, hval]

theorem no_interior_tangential_of_nonpos {c ξ : ℝ} (hc : c ≤ 0) (hξ : ξ ^ 2 < 1) :
    tangentialRatio c ξ ≠ 1 := by
  have _ : 0 < 1 - ξ ^ 2 := by linarith
  unfold tangentialRatio
  have hden : 0 < 1 + limbS ξ := by linarith [limbS_nonneg ξ]
  have hle : c / (1 + limbS ξ) ≤ 0 := div_nonpos_of_nonpos_of_nonneg hc hden.le
  linarith

theorem no_interior_radial_of_nonpos {c ξ : ℝ} (hc : c ≤ 0) (hξ : ξ ^ 2 < 1) :
    radialSlope c ξ ≠ 1 := by
  have _ : 0 < limbS ξ := limbS_pos hξ
  unfold radialSlope
  have hden : 0 < limbS ξ * (1 + limbS ξ) := by
    have hs := limbS_pos hξ
    have : 0 < 1 + limbS ξ := by linarith [limbS_nonneg ξ]
    exact mul_pos hs this
  have hle : c / (limbS ξ * (1 + limbS ξ)) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg hc hden.le
  linarith

theorem no_exterior_radial_of_pos {c ξ : ℝ} (hc : 0 < c) (hξ : 0 < ξ) :
    -c / ξ ^ 2 ≠ 1 := by
  have hden : 0 < ξ ^ 2 := by positivity
  have hlt : -c / ξ ^ 2 < 0 := div_neg_of_neg_of_pos (neg_neg_of_pos hc) hden
  linarith

theorem exterior_tangential_radius {c : ℝ} (hc : 1 < c) :
    exteriorDeflection c (Real.sqrt c) / Real.sqrt c = 1 ∧ 1 < Real.sqrt c := by
  have hpos : 0 < c := by linarith
  have hsqrt : 0 < Real.sqrt c := Real.sqrt_pos.mpr hpos
  have hsq : Real.sqrt c * Real.sqrt c = c := by
    rw [← pow_two, Real.sq_sqrt hpos.le]
  refine ⟨?_, ?_⟩
  · unfold exteriorDeflection
    field_simp [hsqrt.ne']
    nlinarith [hsq]
  · have hle : (1 : ℝ) < c := hc
    rw [← Real.sqrt_one]
    exact Real.sqrt_lt_sqrt (by norm_num) hle

theorem exterior_radial_of_neg {c : ℝ} (hc : c < -1) :
    -c / Real.sqrt (-c) ^ 2 = 1 ∧ 1 < Real.sqrt (-c) := by
  have hpos : 0 < -c := by linarith
  have hsq : Real.sqrt (-c) ^ 2 = -c := Real.sq_sqrt hpos.le
  refine ⟨?_, ?_⟩
  · rw [hsq, div_self hpos.ne']
  · rw [← Real.sqrt_one]
    exact Real.sqrt_lt_sqrt (by norm_num) (by linarith)

/-! ### The window in areal radii -/

/-- Attractive window `bₘ/√2 < R < bₘ` is exactly `1 < (bₘ/R)² < 2`. -/
theorem attractive_window_iff {bm R : ℝ} (hbm : 0 < bm) (hR : 0 < R) :
    bm / Real.sqrt 2 < R ∧ R < bm ↔ 1 < (bm / R) ^ 2 ∧ (bm / R) ^ 2 < 2 := by
  have h2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have h2sq : Real.sqrt 2 * Real.sqrt 2 = 2 := by
    rw [← pow_two, Real.sq_sqrt (by norm_num)]
  have hR0 : 0 ≤ R := hR.le
  have hbm0 : 0 ≤ bm := hbm.le
  constructor
  · rintro ⟨hlo, hhi⟩
    have hhalf0 : 0 ≤ bm / Real.sqrt 2 := (div_pos hbm h2).le
    have hsq_lo : (bm / Real.sqrt 2) * (bm / Real.sqrt 2) < R * R :=
      (mul_self_lt_mul_self_iff hhalf0 hR0).mp hlo
    have hleft : (bm / Real.sqrt 2) * (bm / Real.sqrt 2) = bm ^ 2 / 2 := by
      field_simp [h2.ne']
      nlinarith [h2sq]
    have hhi_c : (bm / R) ^ 2 < 2 := by
      have hR2 : 0 < R ^ 2 := by positivity
      rw [div_pow, div_lt_iff₀ hR2]
      nlinarith [hsq_lo, hleft]
    have hsq_hi : R * R < bm * bm := (mul_self_lt_mul_self_iff hR0 hbm0).mp hhi
    have hlo_c : 1 < (bm / R) ^ 2 := by
      have hR2 : 0 < R ^ 2 := by positivity
      rw [div_pow, one_lt_div hR2]
      nlinarith [hsq_hi]
    exact ⟨hlo_c, hhi_c⟩
  · rintro ⟨hlo, hhi⟩
    have hR2 : 0 < R ^ 2 := by positivity
    have hhalf0 : 0 ≤ bm / Real.sqrt 2 := (div_pos hbm h2).le
    have hleft : (bm / Real.sqrt 2) * (bm / Real.sqrt 2) = bm ^ 2 / 2 := by
      field_simp [h2.ne']
      nlinarith [h2sq]
    have hhiR : bm / Real.sqrt 2 < R := by
      have hbm2 : bm ^ 2 < 2 * R ^ 2 := by
        rw [div_pow, div_lt_iff₀ hR2] at hhi
        nlinarith
      have hsq : (bm / Real.sqrt 2) * (bm / Real.sqrt 2) < R * R := by
        nlinarith [hbm2, hleft]
      exact (mul_self_lt_mul_self_iff hhalf0 hR0).mpr hsq
    have hloR : R < bm := by
      have hsq : R * R < bm * bm := by
        rw [div_pow, one_lt_div hR2] at hlo
        nlinarith
      exact (mul_self_lt_mul_self_iff hR0 hbm0).mpr hsq
    exact ⟨hhiR, hloR⟩

/-- An interior radial curve exists precisely when `R > bₘ/√2`. -/
theorem radial_window_iff {bm R : ℝ} (hbm : 0 < bm) (hR : 0 < R) :
    bm / Real.sqrt 2 < R ↔ (bm / R) ^ 2 < 2 := by
  constructor
  · intro hlo
    have h2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    have h2sq : Real.sqrt 2 * Real.sqrt 2 = 2 := by
      rw [← pow_two, Real.sq_sqrt (by norm_num)]
    have hhalf0 : 0 ≤ bm / Real.sqrt 2 := (div_pos hbm h2).le
    have hsq : (bm / Real.sqrt 2) * (bm / Real.sqrt 2) < R * R :=
      (mul_self_lt_mul_self_iff hhalf0 hR.le).mp hlo
    have hleft : (bm / Real.sqrt 2) * (bm / Real.sqrt 2) = bm ^ 2 / 2 := by
      field_simp [h2.ne']
      nlinarith [h2sq]
    have hR2 : 0 < R ^ 2 := by positivity
    rw [div_pow, div_lt_iff₀ hR2]
    nlinarith [hsq, hleft]
  · intro hhi
    have h2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    have h2sq : Real.sqrt 2 * Real.sqrt 2 = 2 := by
      rw [← pow_two, Real.sq_sqrt (by norm_num)]
    have hR2 : 0 < R ^ 2 := by positivity
    have hbm2 : bm ^ 2 < 2 * R ^ 2 := by
      rw [div_pow, div_lt_iff₀ hR2] at hhi
      nlinarith
    have hhalf0 : 0 ≤ bm / Real.sqrt 2 := (div_pos hbm h2).le
    have hleft : (bm / Real.sqrt 2) * (bm / Real.sqrt 2) = bm ^ 2 / 2 := by
      field_simp [h2.ne']
      nlinarith [h2sq]
    have hsq : (bm / Real.sqrt 2) * (bm / Real.sqrt 2) < R * R := by
      nlinarith [hbm2, hleft]
    exact (mul_self_lt_mul_self_iff hhalf0 hR.le).mpr hsq

/-! ### The limb: finite tangential ratio, unbounded radial slope -/

theorem exists_radialSlope_gt {c K : ℝ} (hc : 0 < c) (hK : 0 < K) :
    ∃ ξ, 0 < ξ ∧ ξ < 1 ∧ K < radialSlope c ξ := by
  let s₀ : ℝ := min (1 / 2) (c / (4 * K))
  have hs0 : 0 < s₀ := lt_min (by norm_num) (div_pos hc (by positivity : (0 : ℝ) < 4 * K))
  have hs_half : s₀ ≤ 1 / 2 := min_le_left _ _
  have hs_c : s₀ ≤ c / (4 * K) := min_le_right _ _
  have hs1 : s₀ < 1 := by linarith
  refine ⟨xiOfS s₀, xiOfS_pos hs0.le hs1, xiOfS_lt_one hs0 hs1.le, ?_⟩
  have hlimb : limbS (xiOfS s₀) = s₀ := xiOfS_limbS hs0.le hs1.le
  unfold radialSlope
  rw [hlimb]
  have hden : 0 < s₀ * (1 + s₀) := by positivity
  rw [lt_div_iff₀ hden]
  have hstep1 : s₀ * (1 + s₀) ≤ s₀ * (3 / 2) := by
    apply mul_le_mul_of_nonneg_left _ hs0.le
    linarith
  have hstep2 : s₀ * (3 / 2) ≤ (c / (4 * K)) * (3 / 2) := by
    apply mul_le_mul_of_nonneg_right hs_c
    norm_num
  have hprod : K * ((3 / 2) * (c / (4 * K))) = (3 / 8) * c := by
    field_simp
    ring
  have hltc : (3 / 8) * c < c := by nlinarith [hc]
  have hle : K * (s₀ * (1 + s₀)) ≤ K * ((3 / 2) * (c / (4 * K))) := by
    have hmid : s₀ * (1 + s₀) ≤ (3 / 2) * (c / (4 * K)) := by
      have hcomm : (c / (4 * K)) * (3 / 2) = (3 / 2) * (c / (4 * K)) := by ring
      linarith [hstep1, hstep2, hcomm]
    exact mul_le_mul_of_nonneg_left hmid hK.le
  linarith [hle, hprod, hltc]

theorem tangentialRatio_lt_c {c ξ : ℝ} (hc : 0 < c) (hξ : ξ ^ 2 < 1) :
    tangentialRatio c ξ < c := by
  have hs : 0 < limbS ξ := limbS_pos hξ
  have hden : 0 < 1 + limbS ξ := by linarith
  unfold tangentialRatio
  rw [div_lt_iff₀ hden]
  nlinarith

end Gravity

end DstDiophantine
