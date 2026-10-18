import DstDiophantine.Gravity.ElectronLength
import DstDiophantine.Gravity.NuclearLayer
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option linter.style.nativeDecide false

/-!
# Laboratory caps on the nuclear length

## Paper boundary (do **not** claim)

The nuclear length is the charged-pion Compton wavelength `λ_π`. The
laboratory signs place it between `56/75` fm and `19/10` fm. The core radii
`2/5` fm and `1/2` fm, the attractive radius `1` fm, the saturation density,
and the charge-radius lower edges are external inputs. Nothing here produces
a binding energy, a scattering length, or an identification of a charge radius
with a pair separation. The identification is not a derivation of `ℓ`.

## What is proved

* A slow separation that repels lies inside the first node, so
  `ℓ > (28/15) r`. At the interior core radius `2/5` fm this is
  `ℓ > 56/75` fm.
* A slow separation that attracts lies in the outer well, so
  `ℓ < (19/10) r`. At `1` fm this is `ℓ < 19/10` fm.
* A widening by one fifth still leaves both `2/5` fm and `1/2` fm inside
  `1` fm.
* `56/75 < λ_π < 19/10`.
* Under `ℓ = λ_π` the first node lies in `(14/19, 213/280)` fm, hence
  strictly above `1/2` fm and strictly below `1` fm. The second node lies
  strictly below `1/2` fm, so the core scale lies in the inversion layer.
* The rapidity wall `2λ_π/π` lies in `(8/9, 142/157)` fm, hence strictly
  below `1` fm. The attractive radius, the saturation spacing, and each
  charge-radius lower edge lie outside that wall.
* The cap from the saturation spacing is weaker than the cap from `1` fm.
-/

namespace DstDiophantine

namespace Gravity

open Real Set SI

/-! ### Sign caps -/

/-- Repulsion at a slow separation `r` places `r` inside the first node, so
`ℓ > (28/15) r`. -/
theorem repulsive_separation_ell_gt {ℓ r : ℝ} (hr : 0 < r)
    (hrep : r < ℓ / (2 * resonanceRoot1)) :
    (28 / 15) * r < ℓ := by
  have hx : (14 / 15 : ℝ) < resonanceRoot1 := firstNode_num_window.1
  have hxpos : (0 : ℝ) < resonanceRoot1 := lt_trans (by norm_num) hx
  have h2 : (0 : ℝ) < 2 * resonanceRoot1 := by positivity
  have hℓ : r * (2 * resonanceRoot1) < ℓ := (lt_div_iff₀ h2).mp hrep
  have h28 : (28 / 15 : ℝ) < 2 * resonanceRoot1 := by nlinarith
  have hmul : (28 / 15) * r < r * (2 * resonanceRoot1) := by nlinarith
  linarith

/-- The interior core radius `2/5` fm forces `ℓ > 56/75` fm. -/
theorem core_interior_ell_floor {ℓ : ℝ}
    (hrep : (nnCoreInteriorFm : ℝ) < ℓ / (2 * resonanceRoot1)) :
    (56 / 75 : ℝ) < ℓ := by
  have h := repulsive_separation_ell_gt (by exact_mod_cast nnCoreInteriorFm_pos) hrep
  have hprod : (28 / 15 : ℝ) * (nnCoreInteriorFm : ℝ) = 56 / 75 := by
    unfold nnCoreInteriorFm
    norm_num
  linarith

/-- Attraction at `1` fm forces `ℓ < 19/10` fm. -/
theorem attraction_at_one_fm_ell_cap {ℓ : ℝ}
    (hatt : ℓ / (2 * resonanceRoot1) < (nnAttractionRadiusFm : ℝ)) :
    ℓ < (19 / 10 : ℝ) := by
  have h := outerWell_ell_lt_nineteen_tenths
    (by exact_mod_cast nnAttractionRadiusFm_pos) hatt
  simpa [nnAttractionRadiusFm] using h

/-- A one-fifth widening still leaves the core radii inside `1` fm. -/
theorem core_inside_attraction_after_fifth :
    nnCoreInteriorFm * (6 / 5) < nnAttractionRadiusFm ∧
      nnCoreScaleFm * (6 / 5) < nnAttractionRadiusFm := by
  unfold nnCoreInteriorFm nnCoreScaleFm nnAttractionRadiusFm
  norm_num

theorem core_interior_lt_scale : nnCoreInteriorFm < nnCoreScaleFm := by
  unfold nnCoreInteriorFm nnCoreScaleFm
  norm_num

/-! ### The charged-pion wavelength sits inside the caps -/

private theorem pion_real_gt : (7 / 5 : ℝ) < (pionComptonFm : ℝ) := by
  rw [show (7 / 5 : ℝ) = ((7 / 5 : ℚ) : ℝ) by norm_num]
  exact_mod_cast pionComptonFm_tight_bounds.1

private theorem pion_real_lt : (pionComptonFm : ℝ) < 71 / 50 := by
  rw [show (71 / 50 : ℝ) = ((71 / 50 : ℚ) : ℝ) by norm_num]
  exact_mod_cast pionComptonFm_tight_bounds.2

private theorem pion_real_pos : (0 : ℝ) < (pionComptonFm : ℝ) :=
  lt_trans (by norm_num : (0 : ℝ) < 7 / 5) pion_real_gt

/-- `56/75 < λ_π < 19/10`. -/
theorem pion_inside_sign_caps :
    (56 / 75 : ℚ) < pionComptonFm ∧ pionComptonFm < 19 / 10 := by
  have h := pionComptonFm_tight_bounds
  refine ⟨lt_trans ?_ h.1, lt_trans h.2 ?_⟩
  · norm_num
  · norm_num

/-! ### First node, second node, and the rapidity wall -/

theorem pion_first_node_fm_window :
    (14 / 19 : ℝ) < layerRadius (pionComptonFm : ℝ) resonanceRoot1 ∧
      layerRadius (pionComptonFm : ℝ) resonanceRoot1 < 213 / 280 := by
  have hrad := firstNode_radius_window
  have hxpos : (0 : ℝ) < 1 / (2 * resonanceRoot1) := by
    have hx : (0 : ℝ) < resonanceRoot1 :=
      lt_trans (by norm_num) firstNode_num_window.1
    positivity
  have hlo : (7 / 5 : ℝ) * (10 / 19) <
      (pionComptonFm : ℝ) * (1 / (2 * resonanceRoot1)) := by
    have h1 : (7 / 5 : ℝ) * (10 / 19) < (pionComptonFm : ℝ) * (10 / 19) :=
      mul_lt_mul_of_pos_right pion_real_gt (by norm_num)
    have h2 : (pionComptonFm : ℝ) * (10 / 19) <
        (pionComptonFm : ℝ) * (1 / (2 * resonanceRoot1)) :=
      mul_lt_mul_of_pos_left hrad.1 pion_real_pos
    linarith
  have hhi : (pionComptonFm : ℝ) * (1 / (2 * resonanceRoot1)) <
      (71 / 50 : ℝ) * (15 / 28) := by
    have h1 : (pionComptonFm : ℝ) * (1 / (2 * resonanceRoot1)) <
        (pionComptonFm : ℝ) * (15 / 28) :=
      mul_lt_mul_of_pos_left hrad.2 pion_real_pos
    have h2 : (pionComptonFm : ℝ) * (15 / 28) < (71 / 50) * (15 / 28) :=
      mul_lt_mul_of_pos_right pion_real_lt (by norm_num)
    linarith
  have heq : layerRadius (pionComptonFm : ℝ) resonanceRoot1 =
      (pionComptonFm : ℝ) * (1 / (2 * resonanceRoot1)) := by
    unfold layerRadius
    field_simp
  have hloQ : (7 / 5 : ℝ) * (10 / 19) = 14 / 19 := by norm_num
  have hhiQ : (71 / 50 : ℝ) * (15 / 28) = 213 / 280 := by norm_num
  constructor
  · linarith
  · linarith

theorem pion_first_node_between_core_and_attraction :
    (nnCoreScaleFm : ℝ) < layerRadius (pionComptonFm : ℝ) resonanceRoot1 ∧
      layerRadius (pionComptonFm : ℝ) resonanceRoot1 < (nnAttractionRadiusFm : ℝ) := by
  have h := pion_first_node_fm_window
  have hcore : (nnCoreScaleFm : ℝ) < 14 / 19 := by
    unfold nnCoreScaleFm
    norm_num
  have hatt : (213 / 280 : ℝ) < nnAttractionRadiusFm := by
    unfold nnAttractionRadiusFm
    norm_num
  constructor <;> linarith

/-- The second node lies strictly below the core scale `1/2` fm. -/
theorem pion_second_node_lt_core {x : ℝ}
    (hx : x ∈ Ioo (π + π / 4) (π + π / 2)) :
    layerRadius (pionComptonFm : ℝ) x < (nnCoreScaleFm : ℝ) := by
  have hx' : x ∈ Ioo (((1 : ℕ) : ℝ) * π + π / 4) (((1 : ℕ) : ℝ) * π + π / 2) := by
    simpa using hx
  have hupper := (layerRadius_window pion_real_pos 1 hx').2
  have hπ : (3.14 : ℝ) < π := pi_gt_d2
  have hfrac : 2 * (pionComptonFm : ℝ) / (5 * π) < 2 * (71 / 50) / (5 * 3.14) := by
    have hnum : 2 * (pionComptonFm : ℝ) / (5 * π) < 2 * (71 / 50) / (5 * π) :=
      div_lt_div_of_pos_right (by nlinarith [pion_real_lt]) (by positivity)
    have hden : 2 * (71 / 50) / (5 * π) < 2 * (71 / 50) / (5 * 3.14) :=
      div_lt_div_of_pos_left (by norm_num) (by positivity) (by nlinarith [hπ])
    linarith
  have hnum : 2 * (71 / 50 : ℝ) / (5 * 3.14) = 142 / 785 := by norm_num
  have hhalf : (142 / 785 : ℝ) < nnCoreScaleFm := by
    unfold nnCoreScaleFm
    norm_num
  have hrewrite : 2 * (pionComptonFm : ℝ) / ((4 * (1 : ℝ) + 1) * π) =
      2 * (pionComptonFm : ℝ) / (5 * π) := by ring
  linarith

/-- Under `ℓ = λ_π` the core scale lies between the second node and the first. -/
theorem pion_core_scale_in_inversion_layer {x : ℝ}
    (hx : x ∈ Ioo (π + π / 4) (π + π / 2)) :
    layerRadius (pionComptonFm : ℝ) x < (nnCoreScaleFm : ℝ) ∧
      (nnCoreScaleFm : ℝ) < layerRadius (pionComptonFm : ℝ) resonanceRoot1 :=
  ⟨pion_second_node_lt_core hx, pion_first_node_between_core_and_attraction.1⟩

theorem pion_rapidity_wall_window :
    (8 / 9 : ℝ) < 2 * (pionComptonFm : ℝ) / π ∧
      2 * (pionComptonFm : ℝ) / π < 142 / 157 := by
  have hπlo : (3.14 : ℝ) < π := pi_gt_d2
  have hπhi : π < 3.15 := pi_lt_d2
  constructor
  · have hnum : 2 * (7 / 5) / π < 2 * (pionComptonFm : ℝ) / π :=
      div_lt_div_of_pos_right (by nlinarith [pion_real_gt]) (by positivity)
    have hden : 2 * (7 / 5) / 3.15 < 2 * (7 / 5) / π :=
      div_lt_div_of_pos_left (by norm_num) pi_pos hπhi
    have hval : 2 * (7 / 5 : ℝ) / 3.15 = 8 / 9 := by norm_num
    linarith
  · have hnum : 2 * (pionComptonFm : ℝ) / π < 2 * (71 / 50) / π :=
      div_lt_div_of_pos_right (by nlinarith [pion_real_lt]) (by positivity)
    have hden : 2 * (71 / 50) / π < 2 * (71 / 50) / 3.14 :=
      div_lt_div_of_pos_left (by norm_num) (by positivity) hπlo
    have hval : 2 * (71 / 50 : ℝ) / 3.14 = 142 / 157 := by norm_num
    linarith

/-- The wall lies strictly below the attractive radius `1` fm. -/
theorem pion_attraction_outside_wall :
    2 * (pionComptonFm : ℝ) / π < (nnAttractionRadiusFm : ℝ) := by
  have h := pion_rapidity_wall_window.2
  have h1 : (142 / 157 : ℝ) < nnAttractionRadiusFm := by
    unfold nnAttractionRadiusFm
    norm_num
  linarith

theorem charge_lower_outside_wall {r : ℚ} (hr : (1 : ℚ) < r) :
    2 * (pionComptonFm : ℝ) / π < (r : ℝ) := by
  have hwall := pion_rapidity_wall_window.2
  have hr1 : (1 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have h157 : (142 / 157 : ℝ) < 1 := by norm_num
  linarith

theorem chargeRadii_outside_wall :
    2 * (pionComptonFm : ℝ) / π < (deuteronChargeRadiusFmLower : ℝ) ∧
      2 * (pionComptonFm : ℝ) / π < (he4ChargeRadiusFmLower : ℝ) ∧
      2 * (pionComptonFm : ℝ) / π < (oxygen16ChargeRadiusFmLower : ℝ) ∧
      2 * (pionComptonFm : ℝ) / π < (calcium40ChargeRadiusFmLower : ℝ) ∧
      2 * (pionComptonFm : ℝ) / π < (calcium48ChargeRadiusFmLower : ℝ) ∧
      2 * (pionComptonFm : ℝ) / π < (lead208ChargeRadiusFmLower : ℝ) := by
  have h := chargeRadiusLower_gt_one
  exact ⟨charge_lower_outside_wall h.1, charge_lower_outside_wall h.2.1,
    charge_lower_outside_wall h.2.2.1, charge_lower_outside_wall h.2.2.2.1,
    charge_lower_outside_wall h.2.2.2.2.1, charge_lower_outside_wall h.2.2.2.2.2⟩

/-! ### Saturation spacing -/

theorem saturation_volume_per_nucleon :
    1 / saturationDensityFm3Approx = 25 / 4 := by
  unfold saturationDensityFm3Approx saturationDensityFm3Mantissa
    saturationDensityFm3Scale
  norm_num

theorem saturation_volume_cube_window :
    (46 / 25 : ℚ) ^ 3 < 1 / saturationDensityFm3Approx ∧
      1 / saturationDensityFm3Approx < (37 / 20 : ℚ) ^ 3 := by
  rw [saturation_volume_per_nucleon]
  norm_num

/-- A positive cube root of the volume per nucleon lies in `(1.84, 1.85)` fm. -/
theorem saturation_spacing_window {s : ℝ} (hs : 0 < s)
    (hcube : s ^ 3 = (1 / saturationDensityFm3Approx : ℝ)) :
    (46 / 25 : ℝ) < s ∧ s < 37 / 20 := by
  have hvol : 1 / (saturationDensityFm3Approx : ℝ) = 25 / 4 := by
    unfold saturationDensityFm3Approx saturationDensityFm3Mantissa
      saturationDensityFm3Scale
    norm_num
  have hlo : (46 / 25 : ℝ) ^ 3 < s ^ 3 := by
    rw [hcube, hvol]
    norm_num
  have hhi : s ^ 3 < (37 / 20 : ℝ) ^ 3 := by
    rw [hcube, hvol]
    norm_num
  refine ⟨(pow_lt_pow_iff_left₀ (by norm_num : (0 : ℝ) ≤ 46 / 25) hs.le
      (by decide : (3 : ℕ) ≠ 0)).mp hlo,
    (pow_lt_pow_iff_left₀ hs.le (by norm_num : (0 : ℝ) ≤ 37 / 20)
      (by decide : (3 : ℕ) ≠ 0)).mp hhi⟩

theorem saturation_spacing_outside_wall {s : ℝ} (hs : 0 < s)
    (hcube : s ^ 3 = (1 / saturationDensityFm3Approx : ℝ)) :
    2 * (pionComptonFm : ℝ) / π < s := by
  have h := (saturation_spacing_window hs hcube).1
  have hwall := pion_rapidity_wall_window.2
  have h157 : (142 / 157 : ℝ) < 46 / 25 := by norm_num
  linarith

/-- The cap from the spacing is weaker than the cap from attraction at `1` fm. -/
theorem attraction_cap_lt_spacing_cap :
    (19 / 10 : ℚ) < (19 / 10) * (37 / 20) := by
  norm_num

end Gravity

end DstDiophantine
