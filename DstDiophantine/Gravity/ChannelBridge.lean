import DstDiophantine.Gravity.SignReversal
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option linter.style.native false

/-!
# One interference factor, two lengths

Where both interference factors are nonzero, node radii stand in the ratio of
the two lengths. \(G\), the masses, \(\alpha\), \(\hbar\), \(c\), and the
sign-reversal window are inputs; the channel length is not a Compton
wavelength, and no joint zero is derived. The external electromagnetic length
over that window lies in `(203, 414)` and does not select `r₁`.
-/

namespace DstDiophantine

namespace Gravity

open Real SI

theorem channelTerm_ratio {κ coul γG γE r : ℝ}
    (hr : r ≠ 0) (hG : γG ≠ 0) (hE : γE ≠ 0) (hc : coul ≠ 0) :
    (-κ / (γG * r ^ 2)) / (coul / (γE * r ^ 2)) =
      (κ * γE) / (-coul * γG) := by
  have hr2 : r ^ 2 ≠ 0 := pow_ne_zero 2 hr
  field_simp

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

/-- `3/5` and `9/10` both lie in the external electromagnetic ratio, so that ratio does not
select `r₁`. No identification of `ℓ_E` with the nuclear channel length is assumed. -/
theorem charge_over_nuclear_length_not_unique :
    ¬ ∃! r₁ : ℝ, 1 / 2 < r₁ ∧ r₁ < 1 ∧
        (203 : ℝ) < ((ellRepFm : ℚ) : ℝ) / lengthOfReversal r₁ ∧
          ((ellRepFm : ℚ) : ℝ) / lengthOfReversal r₁ < 414 := by
  intro h
  obtain ⟨r, -, huniq⟩ := h
  have h35 := charge_over_nuclear_length (r₁ := 3 / 5) (by norm_num) (by norm_num)
  have h910 := charge_over_nuclear_length (r₁ := 9 / 10) (by norm_num) (by norm_num)
  have hleft := huniq (3 / 5) ⟨by norm_num, by norm_num, h35⟩
  have hright := huniq (9 / 10) ⟨by norm_num, by norm_num, h910⟩
  exact absurd (hleft.trans hright.symm) (by norm_num)

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
