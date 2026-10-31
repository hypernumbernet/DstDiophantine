import DstDiophantine.Gravity.SignReversal
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option linter.style.native false

/-!
# One interference factor, two lengths

## Paper boundary (do **not** claim)

`G`, the masses, `α`, `ℏ`, `c`, and the sign-reversal window
`1/2 < r₁ < 1` fm are external inputs. The channel length is the definition
`ℓ = 2 x₁ r₁`. It is not a Compton wavelength. Nothing here derives a
spectrum, a binding, or a radius at which the two factors vanish together.

## What is proved

* Where both interference factors are nonzero, the ratio of the mass term to
  the charge term is `(κ / coul) · (γ_E / γ_G)`, up to the sign written below.
* On the equal-scale ansatz, corresponding node radii stand in the ratio of
  the two lengths. The first node of the defined nuclear length is `r₁`.
* For every reversal in `(1/2, 1)` fm, the electron's electromagnetic length
  over that nuclear length lies strictly between `203` and `414`. The first
  node of the charge channel therefore stands that many times farther out
  than the nuclear sign-reversal.
-/

namespace DstDiophantine

namespace Gravity

open Real SI

/-- Ratio of the two signed inverse-square terms.
The mass term is `−κ/(γ_G r²)` and the charge term is `coul/(γ_E r²)`. -/
theorem channelTerm_ratio {κ coul γG γE r : ℝ}
    (hr : r ≠ 0) (hG : γG ≠ 0) (hE : γE ≠ 0) (hc : coul ≠ 0) :
    (-κ / (γG * r ^ 2)) / (coul / (γE * r ^ 2)) =
      (κ * γE) / (-coul * γG) := by
  have hr2 : r ^ 2 ≠ 0 := pow_ne_zero 2 hr
  field_simp

/-- Corresponding equal-scale nodes stand in the ratio of the lengths. -/
theorem layerRadius_ratio {ℓ₁ ℓ₂ x : ℝ} (hℓ : ℓ₂ ≠ 0) (hx : x ≠ 0) :
    layerRadius ℓ₁ x / layerRadius ℓ₂ x = ℓ₁ / ℓ₂ := by
  unfold layerRadius
  field_simp

/-- Electromagnetic length in femtometres, `ℏ/(m_e c)`. -/
def ellRepFm : ℚ := ellRep / femtometerApprox

theorem ellRepFm_eq :
    ellRepFm = ((ellRep_num : ℚ) * 10 ^ 15) / ellRep_den := by
  unfold ellRepFm femtometerApprox
  rw [ellRep_eq_num_div_den]
  field_simp

theorem ellRepFm_bounds :
    (3861 / 10 : ℚ) < ellRepFm ∧ ellRepFm < 3862 / 10 := by
  obtain ⟨hlo, hhi⟩ := ellRep_meter_window
  unfold ellRepFm femtometerApprox
  constructor
  · calc (3861 / 10 : ℚ)
        = (3861 / 10 ^ 16) * 10 ^ 15 := by norm_num
      _ < ellRep * 10 ^ 15 :=
          mul_lt_mul_of_pos_right hlo (by norm_num : (0 : ℚ) < 10 ^ 15)
      _ = ellRep / (1 / 10 ^ 15) := by field_simp
  · calc ellRep / (1 / 10 ^ 15)
        = ellRep * 10 ^ 15 := by field_simp
      _ < (3862 / 10 ^ 16) * 10 ^ 15 :=
          mul_lt_mul_of_pos_right hhi (by norm_num : (0 : ℚ) < 10 ^ 15)
      _ = 3862 / 10 := by norm_num

theorem ellRepFm_pos : (0 : ℚ) < ellRepFm :=
  lt_trans (by norm_num) ellRepFm_bounds.1

/-- For every scattering window, the two lengths differ by a factor in `(203, 414)`. -/
theorem charge_over_nuclear_length {r₁ : ℝ} (hr0 : 1 / 2 < r₁) (hr1 : r₁ < 1) :
    (203 : ℝ) < ((ellRepFm : ℚ) : ℝ) / lengthOfReversal r₁ ∧
      ((ellRepFm : ℚ) : ℝ) / lengthOfReversal r₁ < 414 := by
  obtain ⟨hℓlo, hℓhi⟩ := lengthOfReversal_bounds hr0 hr1
  have hℓpos : (0 : ℝ) < lengthOfReversal r₁ := lengthOfReversal_pos (by linarith)
  have hElo : (3861 / 10 : ℝ) < (ellRepFm : ℝ) := by
    simpa using (Rat.cast_lt (K := ℝ)).mpr ellRepFm_bounds.1
  have hEhi : (ellRepFm : ℝ) < 3862 / 10 := by
    simpa using (Rat.cast_lt (K := ℝ)).mpr ellRepFm_bounds.2
  have hnum : (0 : ℝ) < 3861 / 10 := by norm_num
  have hnumHi : (0 : ℝ) < 3862 / 10 := by norm_num
  have hmidLo : (3861 / 10 : ℝ) / (19 / 10) < (3861 / 10) / lengthOfReversal r₁ :=
    div_lt_div_of_pos_left hnum hℓpos hℓhi
  have hmid : (3861 / 10) / lengthOfReversal r₁ < (ellRepFm : ℝ) / lengthOfReversal r₁ :=
    div_lt_div_of_pos_right hElo hℓpos
  have hlo : (3861 / 10 : ℝ) / (19 / 10) < (ellRepFm : ℝ) / lengthOfReversal r₁ :=
    lt_trans hmidLo hmid
  have hmidHi : (ellRepFm : ℝ) / lengthOfReversal r₁ < (3862 / 10) / lengthOfReversal r₁ :=
    div_lt_div_of_pos_right hEhi hℓpos
  have htop : (3862 / 10) / lengthOfReversal r₁ < (3862 / 10) / (14 / 15) :=
    div_lt_div_of_pos_left hnumHi (by norm_num) hℓlo
  have hhi : (ellRepFm : ℝ) / lengthOfReversal r₁ < (3862 / 10) / (14 / 15) :=
    lt_trans hmidHi htop
  have hfloor : (203 : ℝ) < (3861 / 10) / (19 / 10) := by norm_num
  have hceil : (3862 / 10) / (14 / 15) < (414 : ℝ) := by norm_num
  exact ⟨lt_trans hfloor hlo, lt_trans hhi hceil⟩

/-- The same factor separates the first nodes. -/
theorem first_node_ratio {r₁ : ℝ} (hr0 : 1 / 2 < r₁) (hr1 : r₁ < 1) :
    (203 : ℝ) <
        layerRadius ((ellRepFm : ℚ) : ℝ) resonanceRoot1 / r₁ ∧
      layerRadius ((ellRepFm : ℚ) : ℝ) resonanceRoot1 / r₁ < 414 := by
  have hr : r₁ ≠ 0 := (lt_trans (by norm_num) hr0).ne'
  have hx : resonanceRoot1 ≠ 0 :=
    (lt_trans (by norm_num) firstNode_num_window.1).ne'
  have hℓ : lengthOfReversal r₁ ≠ 0 := (lengthOfReversal_pos (by linarith)).ne'
  have hnode : layerRadius (lengthOfReversal r₁) resonanceRoot1 = r₁ :=
    reversal_is_first_node hr
  have hratio := layerRadius_ratio (ℓ₁ := ((ellRepFm : ℚ) : ℝ))
    (ℓ₂ := lengthOfReversal r₁) (x := resonanceRoot1) hℓ hx
  rw [hnode] at hratio
  rw [hratio]
  exact charge_over_nuclear_length hr0 hr1

end Gravity

end DstDiophantine
