import DstDiophantine.Gravity.BothChannels
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

set_option linter.style.native false

/-!
# The sign-reversal scale as an observational constant

## Paper boundary (do **not** claim)

The sign-reversal scale `r₁` is the separation at which a slow nucleon pair
changes from attraction to repulsion. Scattering potentials are repulsive
through `1/2` fm and attractive from `1` fm, so `1/2 < r₁ < 1`. That window
is an input. The channel length is the definition `ℓ = 2 x₁ r₁`. It is not a
Compton wavelength, and nothing here computes `r₁` from one.

## What is proved

* For every such `r₁`, `14/15 < ℓ < 19/10`.
* The first node of that length is `r₁` itself. The second node lies strictly
  below `1/2` fm, so the core scale lies in the inversion layer.
* The rapidity wall is `r₁` times a factor strictly between `224/189` and
  `190/157`. At `r₁ = 3/5` the wall lies inside `1` fm, and at `r₁ = 9/10` it
  lies outside. The window does not decide which.
* For every such `r₁` the wall lies strictly below each listed charge-radius
  lower edge and below the saturation spacing.
* `k e² / r₁ > 1439/1000` MeV, hence above `1294/1000` MeV.
  The deuteron binding is an external free-mass difference, strictly between
  `2224/1000` and `2225/1000` MeV, and is not derived. On the scattering
  window that Coulomb energy lies below the lower end when `r₁ ≥ 65/100`,
  and above the upper end when `r₁ ≤ 64/100`. Both sample radii lie in the
  window.
* At a separation above `52917` fm the mass term is a fraction of the charge
  term strictly between `440/10⁴²` and `442/10⁴²`, for every such length and
  for an electromagnetic length below `387` fm.
-/

namespace DstDiophantine

namespace Gravity

open Real Set SI

/-- Channel length defined by the sign-reversal scale: `ℓ = 2 x₁ r₁`. -/
noncomputable def lengthOfReversal (r₁ : ℝ) : ℝ :=
  2 * resonanceRoot1 * r₁

theorem lengthOfReversal_pos {r₁ : ℝ} (hr : 0 < r₁) : 0 < lengthOfReversal r₁ := by
  unfold lengthOfReversal
  have hx : (0 : ℝ) < resonanceRoot1 :=
    lt_trans (by norm_num) firstNode_num_window.1
  positivity

theorem lengthOfReversal_lt_nineteen_tenths {r₁ : ℝ} (hr0 : 0 < r₁) (hr1 : r₁ < 1) :
    lengthOfReversal r₁ < 19 / 10 := by
  have hx := firstNode_num_window.2
  unfold lengthOfReversal
  have hprod : 2 * resonanceRoot1 * r₁ < 2 * (19 / 20) * 1 :=
    mul_lt_mul (mul_lt_mul_of_pos_left hx (by norm_num)) hr1.le hr0 (by nlinarith [hx])
  linarith

theorem lengthOfReversal_bounds {r₁ : ℝ} (hr0 : 1 / 2 < r₁) (hr1 : r₁ < 1) :
    (14 / 15 : ℝ) < lengthOfReversal r₁ ∧ lengthOfReversal r₁ < 19 / 10 := by
  have hx := firstNode_num_window.1
  refine ⟨?_, lengthOfReversal_lt_nineteen_tenths (by linarith) hr1⟩
  unfold lengthOfReversal
  have hprod : (14 / 15 : ℝ) = 2 * (14 / 15) * (1 / 2) := by norm_num
  rw [hprod]
  exact mul_lt_mul (mul_lt_mul_of_pos_left hx (by norm_num)) hr0.le
    (by norm_num) (by nlinarith [hx])

/-- The first node of the defined length is the reversal scale. -/
theorem reversal_is_first_node {r₁ : ℝ} (hr : r₁ ≠ 0) :
    layerRadius (lengthOfReversal r₁) resonanceRoot1 = r₁ := by
  unfold lengthOfReversal layerRadius
  have hx : resonanceRoot1 ≠ 0 :=
    (lt_trans (by norm_num) firstNode_num_window.1).ne'
  field_simp

theorem wall_over_reversal {r₁ : ℝ} (hr : 0 < r₁) :
    (224 / 189 : ℝ) < (2 * lengthOfReversal r₁ / π) / r₁ ∧
      (2 * lengthOfReversal r₁ / π) / r₁ < 190 / 157 := by
  have hx := firstNode_num_window
  have hπlo : (3.14 : ℝ) < π := pi_gt_d2
  have hπhi : π < 3.15 := pi_lt_d2
  have hxpos : 0 < resonanceRoot1 := lt_trans (by norm_num) hx.1
  unfold lengthOfReversal
  have hrew : (2 * (2 * resonanceRoot1 * r₁) / π) / r₁ =
      4 * resonanceRoot1 / π := by
    field_simp [hr.ne']
    ring
  rw [hrew]
  constructor
  · have heq : (56 : ℝ) / (15 * 3.15) = 224 / 189 := by norm_num
    have hden : 56 / (15 * π) < 4 * resonanceRoot1 / π := by
      rw [div_lt_div_iff₀ (by positivity) (by positivity)]
      nlinarith [hx.1]
    have hπ : 56 / (15 * 3.15) < 56 / (15 * π) := by
      rw [div_lt_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    linarith
  · have heq : (19 : ℝ) / (5 * 3.14) = 190 / 157 := by norm_num
    have hden : 4 * resonanceRoot1 / π < 19 / (5 * π) := by
      rw [div_lt_div_iff₀ (by positivity) (by positivity)]
      nlinarith [hx.2]
    have hπ : 19 / (5 * π) < 19 / (5 * 3.14) := by
      rw [div_lt_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    linarith

/-- `r₁ = 3/5` places the wall inside `1` fm; `r₁ = 9/10` places it outside. -/
theorem window_does_not_fix_wall_against_one :
    2 * lengthOfReversal (3 / 5) / π < 1 ∧
      1 < 2 * lengthOfReversal (9 / 10) / π := by
  have hlo := (wall_over_reversal (r₁ := 3 / 5) (by norm_num)).2
  have hhi := (wall_over_reversal (r₁ := 9 / 10) (by norm_num)).1
  constructor
  · have hmul : (190 / 157 : ℝ) * (3 / 5) < 1 := by norm_num
    have : (2 * lengthOfReversal (3 / 5) / π) / (3 / 5) < 190 / 157 := hlo
    have hpos : (0 : ℝ) < 3 / 5 := by norm_num
    rw [div_lt_iff₀ hpos] at this
    nlinarith
  · have hmul : (1 : ℝ) < (224 / 189) * (9 / 10) := by norm_num
    have : (224 / 189 : ℝ) < (2 * lengthOfReversal (9 / 10) / π) / (9 / 10) := hhi
    have hpos : (0 : ℝ) < 9 / 10 := by norm_num
    rw [lt_div_iff₀ hpos] at this
    nlinarith

theorem second_node_below_core {r₁ : ℝ} (hr0 : 1 / 2 < r₁) (hr1 : r₁ < 1) :
    ∃ x₂ ∈ Ioo (π + π / 4) (π + π / 2), gammaSEqual x₂ = 0 ∧
      layerRadius (lengthOfReversal r₁) x₂ < (1 / 2 : ℝ) := by
  obtain ⟨x₂, hx₂, hzero, hratio⟩ := layer_ratio_first_second_sharp
  refine ⟨x₂, hx₂, hzero, ?_⟩
  have hπ : (3 : ℝ) < π := pi_gt_three
  have hratioLt : resonanceRoot1 / x₂ < 4 / (5 * π) := hratio.2
  have hfrac : 4 / (5 * π) < (4 / 15 : ℝ) := by
    rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hcore : (4 / 15 : ℝ) < 1 / 2 := by norm_num
  have hrad : layerRadius (lengthOfReversal r₁) x₂ =
      r₁ * (resonanceRoot1 / x₂) := by
    unfold lengthOfReversal layerRadius
    have hx : x₂ ≠ 0 := by
      have : (0 : ℝ) < π + π / 4 := by positivity
      linarith [hx₂.1]
    field_simp
  have hstep : r₁ * (resonanceRoot1 / x₂) < r₁ * (4 / (5 * π)) := by
    exact mul_lt_mul_of_pos_left hratioLt (by linarith)
  have hstep2 : r₁ * (4 / (5 * π)) < 4 / (5 * π) := by
    have hpos : (0 : ℝ) < 4 / (5 * π) := by positivity
    nlinarith
  linarith

theorem core_between_nodes {r₁ : ℝ} (hr0 : 1 / 2 < r₁) (hr1 : r₁ < 1) :
    ∃ x₂ ∈ Ioo (π + π / 4) (π + π / 2), gammaSEqual x₂ = 0 ∧
      layerRadius (lengthOfReversal r₁) x₂ < (1 / 2 : ℝ) ∧
      (1 / 2 : ℝ) < layerRadius (lengthOfReversal r₁) resonanceRoot1 := by
  obtain ⟨x₂, hx₂, hzero, hlt⟩ := second_node_below_core hr0 hr1
  refine ⟨x₂, hx₂, hzero, hlt, ?_⟩
  rw [reversal_is_first_node (ne_of_gt (by linarith : (0 : ℝ) < r₁))]
  exact hr0

private theorem oneNinety_lt_chargeLower :
    (190 / 157 : ℚ) < he4ChargeRadiusFmLower ∧
      (190 / 157 : ℚ) < deuteronChargeRadiusFmLower ∧
      (190 / 157 : ℚ) < oxygen16ChargeRadiusFmLower ∧
      (190 / 157 : ℚ) < calcium40ChargeRadiusFmLower ∧
      (190 / 157 : ℚ) < calcium48ChargeRadiusFmLower ∧
      (190 / 157 : ℚ) < lead208ChargeRadiusFmLower := by
  unfold he4ChargeRadiusFmLower deuteronChargeRadiusFmLower
    oxygen16ChargeRadiusFmLower calcium40ChargeRadiusFmLower
    calcium48ChargeRadiusFmLower lead208ChargeRadiusFmLower
  norm_num

theorem reversal_wall_below_chargeRadii {r₁ : ℝ} (hr0 : 0 < r₁) (hr1 : r₁ < 1) :
    2 * lengthOfReversal r₁ / π < (he4ChargeRadiusFmLower : ℝ) ∧
      2 * lengthOfReversal r₁ / π < (deuteronChargeRadiusFmLower : ℝ) ∧
      2 * lengthOfReversal r₁ / π < (oxygen16ChargeRadiusFmLower : ℝ) ∧
      2 * lengthOfReversal r₁ / π < (calcium40ChargeRadiusFmLower : ℝ) ∧
      2 * lengthOfReversal r₁ / π < (calcium48ChargeRadiusFmLower : ℝ) ∧
      2 * lengthOfReversal r₁ / π < (lead208ChargeRadiusFmLower : ℝ) := by
  have hwall := (wall_over_reversal hr0).2
  have hcmp := oneNinety_lt_chargeLower
  have hwall1 : 2 * lengthOfReversal r₁ / π < 190 / 157 := by
    have hpos : (0 : ℝ) < r₁ := hr0
    rw [div_lt_iff₀ hpos] at hwall
    have : (190 / 157 : ℝ) * r₁ < 190 / 157 := by nlinarith
    linarith
  have cast_bound {q : ℚ} (h : (190 / 157 : ℚ) < q) :
      (190 / 157 : ℝ) < (q : ℝ) := by
    rw [show (190 / 157 : ℝ) = ((190 / 157 : ℚ) : ℝ) by norm_num]
    exact Rat.cast_lt.mpr h
  constructor
  · exact hwall1.trans (cast_bound hcmp.1)
  constructor
  · exact hwall1.trans (cast_bound hcmp.2.1)
  constructor
  · exact hwall1.trans (cast_bound hcmp.2.2.1)
  constructor
  · exact hwall1.trans (cast_bound hcmp.2.2.2.1)
  constructor
  · exact hwall1.trans (cast_bound hcmp.2.2.2.2.1)
  · exact hwall1.trans (cast_bound hcmp.2.2.2.2.2)

theorem reversal_wall_below_spacing {r₁ s : ℝ}
    (hr0 : 0 < r₁) (hr1 : r₁ < 1) (hs : 0 < s)
    (hcube : s ^ 3 = (1 / saturationDensityFm3Approx : ℝ)) :
    2 * lengthOfReversal r₁ / π < s := by
  have hwall := (wall_over_reversal hr0).2
  have hspace := (saturation_spacing_window hs hcube).1
  have hwall1 : 2 * lengthOfReversal r₁ / π < 190 / 157 := by
    rw [div_lt_iff₀ hr0] at hwall
    have : (190 / 157 : ℝ) * r₁ < 190 / 157 := by nlinarith
    linarith
  have hcmp : (190 / 157 : ℝ) < 46 / 25 := by norm_num
  linarith

/-- At the reversal, `k e²/r₁` exceeds `1.439` MeV and hence `1.294` MeV. -/
theorem coulomb_at_reversal {r₁ : ℝ} (hr0 : 0 < r₁) (hr1 : r₁ < 1) :
    (1439 / 1000 : ℝ) < (coulombMeVFm : ℝ) / r₁ ∧
      (1294 / 1000 : ℝ) < (coulombMeVFm : ℝ) / r₁ := by
  have hke : (1439 / 1000 : ℚ) < coulombMeVFm :=
    (by norm_num : (1439 / 1000 : ℚ) < 1439964 / 10 ^ 6).trans coulombMeVFm_bounds.1
  have hgap : (1294 / 1000 : ℝ) < 1439 / 1000 := by norm_num
  have hdiv : (coulombMeVFm : ℝ) < (coulombMeVFm : ℝ) / r₁ := by
    have hke0 : (0 : ℝ) < coulombMeVFm := by
      rw [show (0 : ℝ) = ((0 : ℚ) : ℝ) by norm_num]
      exact Rat.cast_lt.mpr (lt_trans (by norm_num) hke)
    rw [lt_div_iff₀ hr0]
    nlinarith
  have h1439 : (1439 / 1000 : ℝ) < (coulombMeVFm : ℝ) := by
    rw [show (1439 / 1000 : ℝ) = ((1439 / 1000 : ℚ) : ℝ) by norm_num]
    exact Rat.cast_lt.mpr hke
  exact ⟨h1439.trans hdiv, hgap.trans (h1439.trans hdiv)⟩

/-- The Bohr comparison survives for every length in the observational window. -/
theorem reversal_bohr_mass_fraction {ℓE a r₁ : ℝ}
    (hE0 : 0 < ℓE) (hE : ℓE < 387)
    (hr0 : 0 < r₁) (hr1 : r₁ < 1)
    (ha : 52917 < a) :
    (440 : ℝ) / 10 ^ 42 <
        (electronProtonGravToCoulomb : ℝ) *
          gammaSEqual (ℓE / (2 * a)) /
            gammaSEqual (lengthOfReversal r₁ / (2 * a)) ∧
      (electronProtonGravToCoulomb : ℝ) *
          gammaSEqual (ℓE / (2 * a)) /
            gammaSEqual (lengthOfReversal r₁ / (2 * a)) <
        442 / 10 ^ 42 := by
  have hG0 := lengthOfReversal_pos hr0
  have hG : lengthOfReversal r₁ < 387 := by
    have hlen := lengthOfReversal_lt_nineteen_tenths hr0 hr1
    linarith
  have hEa := phase_le_one_fortieth hE0 hE ha
  have hGa := phase_le_one_fortieth hG0 hG ha
  have hEw := gammaWindow_of_le_one_fortieth hEa.1 hEa.2
  have hGw := gammaWindow_of_le_one_fortieth hGa.1 hGa.2
  set γE : ℝ := gammaSEqual (ℓE / (2 * a))
  set γG : ℝ := gammaSEqual (lengthOfReversal r₁ / (2 * a))
  have hEp : 0 < γE := lt_of_lt_of_le (by norm_num) hEw.1
  have hGp : 0 < γG := lt_of_lt_of_le (by norm_num) hGw.1
  set ρ : ℝ := (electronProtonGravToCoulomb : ℝ)
  have hρlo : (4407 / 10 ^ 43 : ℝ) < ρ := by
    refine lt_of_eq_of_lt ?_ (Rat.cast_lt.mpr electronProtonGravToCoulomb_bounds.1)
    norm_num
  have hρhi : ρ < (4408 / 10 ^ 43 : ℝ) := by
    refine lt_of_lt_of_eq (Rat.cast_lt.mpr electronProtonGravToCoulomb_bounds.2) ?_
    norm_num
  have hρpos : 0 < ρ := by
    have : (0 : ℝ) < 4407 / 10 ^ 43 := by norm_num
    linarith
  have hdiv_hi : γE / γG ≤ (16000 : ℝ) / 15987 := by
    rw [div_le_div_iff₀ hGp (by norm_num)]
    have hGscaled : (15987 : ℝ) ≤ γG * 16000 := by
      have := hGw.1
      rwa [div_le_iff₀ (by norm_num : (0 : ℝ) < 16000)] at this
    nlinarith [hEw.2]
  have hdiv_lo : (15987 : ℝ) / 16000 ≤ γE / γG := by
    rw [div_le_div_iff₀ (by norm_num) hGp]
    have hEscaled : (15987 : ℝ) ≤ γE * 16000 := by
      have := hEw.1
      rwa [div_le_iff₀ (by norm_num : (0 : ℝ) < 16000)] at this
    nlinarith [hGw.2]
  have hloR : (440 : ℝ) / 10 ^ 42 < (4407 / 10 ^ 43) * (15987 / 16000) := by
    norm_num
  have hhiR : (4408 / 10 ^ 43 : ℝ) * ((16000 : ℝ) / 15987) < 442 / 10 ^ 42 := by
    norm_num
  have hmpos : 0 < (15987 : ℝ) / 16000 := by norm_num
  have hMpos : 0 < (16000 : ℝ) / 15987 := by norm_num
  constructor
  · have h1 : (4407 / 10 ^ 43) * (15987 / 16000) < ρ * (15987 / 16000) :=
      mul_lt_mul_of_pos_right hρlo hmpos
    have h2 : ρ * (15987 / 16000) ≤ ρ * (γE / γG) :=
      mul_le_mul_of_nonneg_left hdiv_lo hρpos.le
    have hprod : ρ * (γE / γG) = ρ * γE / γG := by ring
    linarith
  · have h1 : ρ * (γE / γG) ≤ ρ * (16000 / 15987) :=
      mul_le_mul_of_nonneg_left hdiv_hi hρpos.le
    have h2 : ρ * ((16000 : ℝ) / 15987) < (4408 / 10 ^ 43) * (16000 / 15987) :=
      mul_lt_mul_of_pos_right hρhi hMpos
    have hprod : ρ * (γE / γG) = ρ * γE / γG := by ring
    linarith

/-- External window, in MeV, for the deuteron binding \(m_n+m_p-m_d\).
The CODATA value lies strictly inside. Not derived. -/
def deuteronBindingMeVLower : ℚ := 2224 / 1000

def deuteronBindingMeVUpper : ℚ := 2225 / 1000

/-- Both sample reversals lie in the open scattering window `(1/2, 1)`. -/
theorem reversal_splits_deuteronBinding :
    (1 / 2 : ℝ) < 64 / 100 ∧ (64 / 100 : ℝ) < 65 / 100 ∧ (65 / 100 : ℝ) < 1 := by
  norm_num

/-- At a reversal of at least `65/100` fm, and still below `1` fm,
`k e²/r₁` lies strictly below the deuteron binding. -/
theorem coulomb_lt_deuteronBinding_of_wide {r₁ : ℝ}
    (hr : (65 / 100 : ℝ) ≤ r₁) (hr1 : r₁ < 1) :
    (coulombMeVFm : ℝ) / r₁ < (deuteronBindingMeVLower : ℝ) := by
  have hke : (coulombMeVFm : ℝ) < ((1439965 / 10 ^ 6 : ℚ) : ℝ) :=
    Rat.cast_lt.mpr coulombMeVFm_bounds.2
  have hr0 : (0 : ℝ) < r₁ := by linarith
  have hdiv : (coulombMeVFm : ℝ) / r₁ < ((1439965 / 10 ^ 6 : ℚ) : ℝ) / r₁ :=
    div_lt_div_of_pos_right hke hr0
  have hmono : ((1439965 / 10 ^ 6 : ℚ) : ℝ) / r₁ ≤
      ((1439965 / 10 ^ 6 : ℚ) : ℝ) / (65 / 100 : ℝ) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hr
  have hnum : ((1439965 / 10 ^ 6 : ℚ) : ℝ) / (65 / 100 : ℝ) <
      (deuteronBindingMeVLower : ℝ) := by
    unfold deuteronBindingMeVLower
    norm_num
  exact (hdiv.trans_le hmono).trans hnum

/-- At a reversal above `1/2` fm and at most `64/100` fm,
`k e²/r₁` lies strictly above the deuteron binding. -/
theorem coulomb_gt_deuteronBinding_of_narrow {r₁ : ℝ}
    (hr0 : (1 / 2 : ℝ) < r₁) (hr : r₁ ≤ (64 / 100 : ℝ)) :
    (deuteronBindingMeVUpper : ℝ) < (coulombMeVFm : ℝ) / r₁ := by
  have hke : ((1439964 / 10 ^ 6 : ℚ) : ℝ) < (coulombMeVFm : ℝ) :=
    Rat.cast_lt.mpr coulombMeVFm_bounds.1
  have hpos : (0 : ℝ) < r₁ := lt_trans (by norm_num) hr0
  have hdiv : ((1439964 / 10 ^ 6 : ℚ) : ℝ) / r₁ < (coulombMeVFm : ℝ) / r₁ :=
    div_lt_div_of_pos_right hke hpos
  have hmono : ((1439964 / 10 ^ 6 : ℚ) : ℝ) / (64 / 100 : ℝ) ≤
      ((1439964 / 10 ^ 6 : ℚ) : ℝ) / r₁ :=
    div_le_div_of_nonneg_left (by norm_num) hpos hr
  have hnum : (deuteronBindingMeVUpper : ℝ) <
      ((1439964 / 10 ^ 6 : ℚ) : ℝ) / (64 / 100 : ℝ) := by
    unfold deuteronBindingMeVUpper
    norm_num
  exact (hnum.trans_le hmono).trans hdiv

end Gravity

end DstDiophantine
