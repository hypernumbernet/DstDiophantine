import DstDiophantine.Gravity.ElectronNumbers
import DstDiophantine.Gravity.ElectronOrbit
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option linter.style.native false

/-!
# Outer-well cap on the electromagnetic length

## Paper boundary (do **not** claim)

The electromagnetic length is the reduced Compton wavelength `ℏ/(m_e c)`.
The laboratory cap lies above it. The Bohr radius and `α` are external
inputs. The radius `a₀/Z` is not an input. Nothing here produces a Bohr
spectrum, a dissociation energy, or an identification of the square with a
laboratory bond.

## What is proved

* A radius in the outer well forces `ℓ < (19/10) r`, because `x₁ < 19/20`.
* Attraction at the Bohr radius forces `ℓ < lambdaHyp` and
  `ℓ < (19/10) a₀`. The rational cap lies strictly above `lambdaHyp`.
* On the SI stand-ins that cap lies in `(1005/10¹³, 1006/10¹³)` m.
* Placing the first node at `a₀` puts the phase of the radius `a₀/2` where
  `γ_s < 0`.
* The length `ℏ/(m_e c)` lies strictly below that cap, in
  `(3861/10¹⁶, 3862/10¹⁶)` m. Its first node lies in
  `(2032/10¹⁶, 2069/10¹⁶)` m.
-/

namespace DstDiophantine

namespace Gravity

open Real Set SI

/-! ### Phase cap -/

/-- An outer-well radius `r > ℓ/(2x₁)` forces `ℓ < (19/10) r`. -/
theorem outerWell_ell_lt_nineteen_tenths {ℓ r : ℝ} (hr : 0 < r)
    (hwell : ℓ / (2 * resonanceRoot1) < r) :
    ℓ < (19 / 10) * r := by
  have hx : resonanceRoot1 < 19 / 20 := firstNode_num_window.2
  have hxpos : (0 : ℝ) < resonanceRoot1 :=
    lt_trans (by norm_num : (0 : ℝ) < 14 / 15) firstNode_num_window.1
  have h2 : (0 : ℝ) < 2 * resonanceRoot1 := by positivity
  have hℓ : ℓ < r * (2 * resonanceRoot1) := (div_lt_iff₀ h2).mp hwell
  calc ℓ
      < r * (2 * resonanceRoot1) := hℓ
    _ = 2 * r * resonanceRoot1 := by ring
    _ < 2 * r * (19 / 20) := by nlinarith
    _ = (19 / 10) * r := by ring

/-- Attraction at the Bohr radius forces `ℓ` strictly below `lambdaHyp`. -/
theorem bohr_outer_well_lt_lambdaHyp {ℓ : ℝ}
    (hwell : ℓ / (2 * resonanceRoot1) < (bohrRadiusApprox : ℝ)) :
    ℓ < lambdaHyp := by
  have hxpos : (0 : ℝ) < resonanceRoot1 :=
    lt_trans (by norm_num : (0 : ℝ) < 14 / 15) firstNode_num_window.1
  have h2 : (0 : ℝ) < 2 * resonanceRoot1 := by positivity
  have hℓ : ℓ < (bohrRadiusApprox : ℝ) * (2 * resonanceRoot1) :=
    (div_lt_iff₀ h2).mp hwell
  unfold lambdaHyp
  linarith

/-- The rational cap sits strictly above the sharp cap `lambdaHyp`. -/
theorem lambdaHyp_lt_nineteen_tenths_bohr :
    lambdaHyp < (19 / 10) * (bohrRadiusApprox : ℝ) := by
  unfold lambdaHyp
  have hx : resonanceRoot1 < 19 / 20 := firstNode_num_window.2
  have ha0 : (0 : ℝ) < (bohrRadiusApprox : ℝ) := by exact_mod_cast bohrRadiusApprox_pos
  nlinarith

theorem bohr_outer_well_lt_nineteen_tenths {ℓ : ℝ}
    (hwell : ℓ / (2 * resonanceRoot1) < (bohrRadiusApprox : ℝ)) :
    ℓ < (19 / 10) * (bohrRadiusApprox : ℝ) :=
  outerWell_ell_lt_nineteen_tenths
    (by exact_mod_cast bohrRadiusApprox_pos) hwell

/-! ### The Bohr cap -/

/-- Rational cap `(19/10) a₀` in metres. Not a value of `ℓ`. -/
def bohrEllCap : ℚ := (19 / 10) * bohrRadiusApprox

/-! ### Cleared denominator of the Bohr stand-in -/

/-- Numerator of `a₀ = ℏ/(m_e c α)` after cancelling `10⁴³`. -/
def bohrRadius_num : ℕ := hbarMantissa * 10 ^ 11

/-- Denominator of `a₀ = ℏ/(m_e c α)` after cancelling `10⁴³`. -/
def bohrRadius_den : ℕ :=
  electronMassMantissa * speedOfLightNat * fineStructureMantissa

private theorem bohr_power_shift :
    (10 : ℚ) ^ electronMassScale * (10 : ℚ) ^ fineStructureScale =
      (10 : ℚ) ^ hbarScale * (10 : ℚ) ^ 11 := by
  unfold electronMassScale fineStructureScale hbarScale
  norm_num

theorem bohrRadiusApprox_eq_num_div_den :
    bohrRadiusApprox = (bohrRadius_num : ℚ) / bohrRadius_den := by
  unfold bohrRadiusApprox hbarApprox electronMassApprox fineStructureApprox
    speedOfLight bohrRadius_num bohrRadius_den
  have hpow := bohr_power_shift
  have hc : (speedOfLightNat : ℚ) ≠ 0 := by
    exact_mod_cast (by decide : speedOfLightNat ≠ 0)
  have hh : (10 : ℚ) ^ hbarScale ≠ 0 := pow_ne_zero _ (by norm_num)
  have he : (10 : ℚ) ^ electronMassScale ≠ 0 := pow_ne_zero _ (by norm_num)
  have hf : (10 : ℚ) ^ fineStructureScale ≠ 0 := pow_ne_zero _ (by norm_num)
  have hem : (electronMassMantissa : ℚ) ≠ 0 := by
    exact_mod_cast (by unfold electronMassMantissa; decide : electronMassMantissa ≠ 0)
  have hfm : (fineStructureMantissa : ℚ) ≠ 0 := by
    exact_mod_cast (by unfold fineStructureMantissa; decide : fineStructureMantissa ≠ 0)
  field_simp [hc, hh, he, hf, hem, hfm]
  have hdenCast :
      ((electronMassMantissa * speedOfLightNat * fineStructureMantissa : ℕ) : ℚ) =
        electronMassMantissa * speedOfLightNat * fineStructureMantissa := by
    simp [Nat.cast_mul]
  have hnumCast : ((hbarMantissa * 10 ^ 11 : ℕ) : ℚ) =
      hbarMantissa * (10 : ℚ) ^ 11 := by
    rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  rw [hdenCast, hnumCast]
  calc
      (hbarMantissa : ℚ) * (10 : ℚ) ^ electronMassScale *
          (10 : ℚ) ^ fineStructureScale *
          (electronMassMantissa * speedOfLightNat * fineStructureMantissa)
        = (hbarMantissa : ℚ) *
            ((10 : ℚ) ^ electronMassScale * (10 : ℚ) ^ fineStructureScale) *
            (electronMassMantissa * speedOfLightNat * fineStructureMantissa) := by ring
    _ = (hbarMantissa : ℚ) * ((10 : ℚ) ^ hbarScale * (10 : ℚ) ^ 11) *
          (electronMassMantissa * speedOfLightNat * fineStructureMantissa) := by rw [hpow]
    _ = (10 : ℚ) ^ hbarScale * electronMassMantissa * speedOfLightNat *
          fineStructureMantissa * (hbarMantissa * (10 : ℚ) ^ 11) := by ring

private theorem bohrRadius_den_pos : (0 : ℚ) < (bohrRadius_den : ℚ) := by
  unfold bohrRadius_den electronMassMantissa speedOfLightNat fineStructureMantissa
  norm_num

private theorem bohrEllCap_eq_cleared :
    bohrEllCap =
      (19 * bohrRadius_num : ℚ) / ((10 : ℕ) * bohrRadius_den) := by
  unfold bohrEllCap
  rw [bohrRadiusApprox_eq_num_div_den]
  have hden : (bohrRadius_den : ℚ) ≠ 0 := bohrRadius_den_pos.ne'
  have h10 : (10 : ℚ) ≠ 0 := by norm_num
  field_simp [hden, h10]
  ring

/-! ### Metre window on the SI stand-ins -/

private theorem bohrEllCap_window (loNum loDen hiNum hiDen : ℕ)
    (hlo : 0 < loDen) (hhi : 0 < hiDen)
    (hloNat : loNum * (10 * bohrRadius_den) < 19 * bohrRadius_num * loDen)
    (hhiNat : 19 * bohrRadius_num * hiDen < hiNum * (10 * bohrRadius_den)) :
    (loNum : ℚ) / loDen < bohrEllCap ∧ bohrEllCap < (hiNum : ℚ) / hiDen := by
  rw [bohrEllCap_eq_cleared]
  have hdenNat : 0 < bohrRadius_den := by
    unfold bohrRadius_den electronMassMantissa speedOfLightNat fineStructureMantissa
    decide
  have hden : (0 : ℚ) < ((10 : ℕ) : ℚ) * bohrRadius_den :=
    mul_pos (by norm_num) (Nat.cast_pos.mpr hdenNat)
  have hloDen : (0 : ℚ) < (loDen : ℚ) := Nat.cast_pos.mpr hlo
  have hhiDen : (0 : ℚ) < (hiDen : ℚ) := Nat.cast_pos.mpr hhi
  constructor
  · rw [div_lt_div_iff₀ hloDen hden]
    exact_mod_cast hloNat
  · rw [div_lt_div_iff₀ hden hhiDen]
    exact_mod_cast hhiNat

theorem bohrEllCap_meter_window :
    (1005 : ℚ) / 10 ^ 13 < bohrEllCap ∧ bohrEllCap < (1006 : ℚ) / 10 ^ 13 := by
  refine bohrEllCap_window 1005 (10 ^ 13) 1006 (10 ^ 13)
      (by norm_num) (by norm_num) ?_ ?_
  · unfold bohrRadius_den bohrRadius_num hbarMantissa electronMassMantissa
      speedOfLightNat fineStructureMantissa
    native_decide
  · unfold bohrRadius_den bohrRadius_num hbarMantissa electronMassMantissa
      speedOfLightNat fineStructureMantissa
    native_decide

/-! ### The node at `a₀` puts `a₀/2` where `γ_s < 0` -/

/-- If the first node sits at `a₀`, the phase of the radius `a₀/2` is `2x₁`,
where `γ_s < 0`. An unlike pair repels there. -/
theorem bohr_node_repels_half :
    gammaSEqual (lambdaHyp / (bohrRadiusApprox : ℝ)) < 0 := by
  have ha0 : (bohrRadiusApprox : ℝ) ≠ 0 :=
    (by exact_mod_cast bohrRadiusApprox_pos : (0 : ℝ) < (bohrRadiusApprox : ℝ)).ne'
  have hphase : lambdaHyp / (bohrRadiusApprox : ℝ) = 2 * resonanceRoot1 := by
    unfold lambdaHyp
    field_simp [ha0]
  have hx := resonanceRoot1_bounds
  have hmem : 2 * resonanceRoot1 ∈ Ioo resonanceRoot1 π := by
    refine ⟨?_, ?_⟩
    · nlinarith [hx.1]
    · have hπ : (2 : ℝ) < π := by linarith [pi_gt_three]
      nlinarith [hx.2, hπ]
  rw [hphase]
  exact gammaSEqual_neg_right_of_first_node hmem

/-! ### Representative input: the reduced Compton wavelength -/

/-- Representative input \(\hbar/(m_e c)\). Not a value derived from \(\gamma_s\). -/
def ellRep : ℚ := hbarApprox / (electronMassApprox * speedOfLight)

/-- Numerator of \(\hbar/(m_e c)\) after cancelling \(10^{41}\). -/
def ellRep_num : ℕ := hbarMantissa

/-- Denominator of \(\hbar/(m_e c)\) after cancelling \(10^{41}\). -/
def ellRep_den : ℕ := electronMassMantissa * speedOfLightNat * 100

theorem ellRep_pos : (0 : ℚ) < ellRep := by
  unfold ellRep
  exact div_pos hbarApprox_pos (mul_pos electronMassApprox_pos speedOfLight_pos)

private theorem ellRep_power_shift :
    (10 : ℚ) ^ hbarScale = (10 : ℚ) ^ electronMassScale * 100 := by
  unfold hbarScale electronMassScale
  norm_num

theorem ellRep_eq_num_div_den : ellRep = (ellRep_num : ℚ) / ellRep_den := by
  unfold ellRep ellRep_num ellRep_den hbarApprox electronMassApprox speedOfLight
  have hpow := ellRep_power_shift
  have hc : (speedOfLightNat : ℚ) ≠ 0 := by
    exact_mod_cast (by decide : speedOfLightNat ≠ 0)
  have hh : (10 : ℚ) ^ hbarScale ≠ 0 := pow_ne_zero _ (by norm_num)
  have he : (10 : ℚ) ^ electronMassScale ≠ 0 := pow_ne_zero _ (by norm_num)
  have hem : (electronMassMantissa : ℚ) ≠ 0 := by
    exact_mod_cast (by unfold electronMassMantissa; decide : electronMassMantissa ≠ 0)
  field_simp [hc, hh, he, hem]
  have hdenCast :
      ((electronMassMantissa * speedOfLightNat * 100 : ℕ) : ℚ) =
        electronMassMantissa * speedOfLightNat * 100 := by
    simp [Nat.cast_mul]
  rw [hdenCast, hpow]
  ring

theorem ellRep_eq_bohr_mul_alpha :
    ellRep = bohrRadiusApprox * fineStructureApprox := by
  unfold ellRep bohrRadiusApprox
  have hα : fineStructureApprox ≠ 0 := fineStructureApprox_pos.ne'
  have hm : electronMassApprox ≠ 0 := electronMassApprox_pos.ne'
  have hc : speedOfLight ≠ 0 := speedOfLight_pos.ne'
  field_simp [hα, hm, hc]

/-- The electron Compton wavelength lies strictly under the Bohr cap. -/
theorem ellRep_lt_bohrEllCap : ellRep < bohrEllCap := by
  rw [ellRep_eq_bohr_mul_alpha]
  unfold bohrEllCap
  have ha0 : (0 : ℚ) < bohrRadiusApprox := bohrRadiusApprox_pos
  have hα : fineStructureApprox < 19 / 10 := by
    unfold fineStructureApprox fineStructureMantissa fineStructureScale
    rw [div_lt_div_iff₀ (by norm_num) (by norm_num)]
    norm_cast
  rw [mul_comm (19 / 10) bohrRadiusApprox]
  exact mul_lt_mul_of_pos_left hα ha0

private theorem ellRep_mul_window (p q loNum loDen hiNum hiDen : ℕ)
    (hq : 0 < q) (hlo : 0 < loDen) (hhi : 0 < hiDen)
    (hloNat : loNum * (ellRep_den * q) < ellRep_num * p * loDen)
    (hhiNat : ellRep_num * p * hiDen < hiNum * (ellRep_den * q)) :
    (loNum : ℚ) / loDen < ellRep * ((p : ℚ) / q) ∧
      ellRep * ((p : ℚ) / q) < (hiNum : ℚ) / hiDen := by
  have hdenNat : 0 < ellRep_den := by
    unfold ellRep_den electronMassMantissa speedOfLightNat
    decide
  have hqQ : (0 : ℚ) < (q : ℚ) := Nat.cast_pos.mpr hq
  have hden : (0 : ℚ) < (ellRep_den : ℚ) * q :=
    mul_pos (Nat.cast_pos.mpr hdenNat) hqQ
  have hprod : ellRep * ((p : ℚ) / q) =
      ((ellRep_num * p : ℕ) : ℚ) / ((ellRep_den * q : ℕ) : ℚ) := by
    rw [ellRep_eq_num_div_den]
    have hden0 : (ellRep_den : ℚ) ≠ 0 := (Nat.cast_pos.mpr hdenNat).ne'
    have hq0 : (q : ℚ) ≠ 0 := hqQ.ne'
    field_simp [hden0, hq0]
    simp [Nat.cast_mul]
    ring
  rw [hprod]
  have hdenCast : (0 : ℚ) < ((ellRep_den * q : ℕ) : ℚ) := by
    exact_mod_cast mul_pos hdenNat hq
  have hloDen : (0 : ℚ) < (loDen : ℚ) := Nat.cast_pos.mpr hlo
  have hhiDen : (0 : ℚ) < (hiDen : ℚ) := Nat.cast_pos.mpr hhi
  constructor
  · rw [div_lt_div_iff₀ hloDen hdenCast]
    exact_mod_cast hloNat
  · rw [div_lt_div_iff₀ hdenCast hhiDen]
    exact_mod_cast hhiNat

private theorem rat_pow_ten_sixteen : (10 : ℚ) ^ 16 = ((10 : ℕ) ^ 16 : ℚ) := by
  norm_num

theorem ellRep_meter_window :
    (3861 : ℚ) / 10 ^ 16 < ellRep ∧ ellRep < (3862 : ℚ) / 10 ^ 16 := by
  have hlo : 3861 * (ellRep_den * 1) < ellRep_num * 1 * 10 ^ 16 := by
    unfold ellRep_den ellRep_num hbarMantissa electronMassMantissa speedOfLightNat
    native_decide
  have hhi : ellRep_num * 1 * 10 ^ 16 < 3862 * (ellRep_den * 1) := by
    unfold ellRep_den ellRep_num hbarMantissa electronMassMantissa speedOfLightNat
    native_decide
  have h := ellRep_mul_window 1 1 3861 (10 ^ 16) 3862 (10 ^ 16)
      (by decide) (by norm_num) (by norm_num) hlo hhi
  have hone : ellRep * (((1 : ℕ) : ℚ) / (1 : ℕ)) = ellRep := by ring
  rw [hone] at h
  rw [rat_pow_ten_sixteen]
  exact h

theorem ellRep_nodeLower_meter_window :
    (2032 : ℚ) / 10 ^ 16 < ellRep * (10 / 19) ∧
      ellRep * (10 / 19) < (2033 : ℚ) / 10 ^ 16 := by
  have hlo : 2032 * (ellRep_den * 19) < ellRep_num * 10 * 10 ^ 16 := by
    unfold ellRep_den ellRep_num hbarMantissa electronMassMantissa speedOfLightNat
    native_decide
  have hhi : ellRep_num * 10 * 10 ^ 16 < 2033 * (ellRep_den * 19) := by
    unfold ellRep_den ellRep_num hbarMantissa electronMassMantissa speedOfLightNat
    native_decide
  have h := ellRep_mul_window 10 19 2032 (10 ^ 16) 2033 (10 ^ 16)
      (by decide) (by norm_num) (by norm_num) hlo hhi
  rw [rat_pow_ten_sixteen]
  exact h

theorem ellRep_nodeUpper_meter_window :
    (2068 : ℚ) / 10 ^ 16 < ellRep * (15 / 28) ∧
      ellRep * (15 / 28) < (2069 : ℚ) / 10 ^ 16 := by
  have hlo : 2068 * (ellRep_den * 28) < ellRep_num * 15 * 10 ^ 16 := by
    unfold ellRep_den ellRep_num hbarMantissa electronMassMantissa speedOfLightNat
    native_decide
  have hhi : ellRep_num * 15 * 10 ^ 16 < 2069 * (ellRep_den * 28) := by
    unfold ellRep_den ellRep_num hbarMantissa electronMassMantissa speedOfLightNat
    native_decide
  have h := ellRep_mul_window 15 28 2068 (10 ^ 16) 2069 (10 ^ 16)
      (by decide) (by norm_num) (by norm_num) hlo hhi
  rw [rat_pow_ten_sixteen]
  exact h

/-- The first node of the electron Compton wavelength lies strictly between
`2032×10⁻¹⁶` m and `2069×10⁻¹⁶` m. -/
theorem ellRep_node_meter_window :
    (2032 : ℝ) / 10 ^ 16 < (ellRep : ℝ) / (2 * resonanceRoot1) ∧
      (ellRep : ℝ) / (2 * resonanceRoot1) < (2069 : ℝ) / 10 ^ 16 := by
  have hx := firstNode_num_window
  have hℓ : (0 : ℝ) < (ellRep : ℝ) := by exact_mod_cast ellRep_pos
  have hxpos : (0 : ℝ) < resonanceRoot1 := lt_trans (by norm_num) hx.1
  have h2 : (0 : ℝ) < 2 * resonanceRoot1 := by positivity
  have hlo : (ellRep : ℝ) * (10 / 19) < (ellRep : ℝ) / (2 * resonanceRoot1) := by
    rw [lt_div_iff₀ h2]
    nlinarith
  have hhi : (ellRep : ℝ) / (2 * resonanceRoot1) < (ellRep : ℝ) * (15 / 28) := by
    rw [div_lt_iff₀ h2]
    nlinarith
  have hloQ : (2032 : ℝ) / 10 ^ 16 < (ellRep : ℝ) * (10 / 19) := by
    have hQ : ((2032 : ℚ) / 10 ^ 16 : ℝ) < ((ellRep * (10 / 19) : ℚ) : ℝ) := by
      exact_mod_cast ellRep_nodeLower_meter_window.1
    simpa [Rat.cast_div, Rat.cast_pow, Rat.cast_mul, Nat.cast_ofNat] using hQ
  have hhiQ : (ellRep : ℝ) * (15 / 28) < (2069 : ℝ) / 10 ^ 16 := by
    have hQ : ((ellRep * (15 / 28) : ℚ) : ℝ) < ((2069 : ℚ) / 10 ^ 16 : ℝ) := by
      exact_mod_cast ellRep_nodeUpper_meter_window.2
    simpa [Rat.cast_div, Rat.cast_pow, Rat.cast_mul, Nat.cast_ofNat] using hQ
  exact ⟨lt_trans hloQ hlo, lt_trans hhi hhiQ⟩

end Gravity

end DstDiophantine
