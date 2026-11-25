import DstDiophantine.Gravity.ElectronOrbit
import DstDiophantine.Gravity.SI
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.Continuity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Repulsion against the hydrogen gross structure

The vacuum line ratios of hydrogen, in the gross structure, are the rational ratios of the Rydberg
gaps `1/n² - 1/m²`. A circular orbit in the central force `ke² f(x) / r²`, with phase
`x = ℓ/(2r)`
and potential normalised to vanish at infinity, has energy proportional to `x f(x) - 2 ∫₀ˣ f`.

The constant factor `f = 1` is Coulomb. Its circular energies on `r = n² a₀` are `-E_I / n²`,
and the wavelength ratios are the Balmer and Lyman ratios. That factor never changes sign.

The equal-scale factor `f = γ_s` has the same sign as `γ_s`. On the outer well it is strictly
below `1`, so it is a repulsive correction to Coulomb, and between the first node and `π` it points
outward. Its potential primitive `sinh x · cos x` stays finite at every node. The written factor
`1/γ_s` is strictly above `1` on the outer well and is unbounded at the first node, so it is an
attractive enhancement, not a repulsion.

Energies read from the nodes themselves, whether proportional to the phase or to its reciprocal, do
not reproduce the Lyman or Balmer gap. No fine structure is claimed, and `ℓ` is not derived.
-/

namespace DstDiophantine

namespace Gravity

open Real Set SI

/-! ### Rydberg gaps -/

/-- Gross-structure gap `1/n² - 1/m²`, in units of the ionisation energy. -/
def rydbergGap (n m : ℕ) : ℚ :=
  1 / (n : ℚ) ^ 2 - 1 / (m : ℚ) ^ 2

theorem lyman_two_over_three : rydbergGap 1 2 / rydbergGap 1 3 = 27 / 32 := by
  unfold rydbergGap
  norm_num

theorem second_over_first : rydbergGap 2 3 / rydbergGap 1 2 = 5 / 27 := by
  unfold rydbergGap
  norm_num

/-- Wavelength ratio of Hα (`3 → 2`) to Hβ (`4 → 2`). -/
theorem balmer_alpha_over_beta : rydbergGap 2 4 / rydbergGap 2 3 = 27 / 20 := by
  unfold rydbergGap
  norm_num

theorem hydrogenIonisation_eq_coulomb_over_bohr :
    hydrogenIonisationApprox = coulombScale / (2 * bohrRadiusApprox) := by
  unfold hydrogenIonisationApprox coulombScale bohrRadiusApprox hbarC
  field_simp [electronMassApprox_pos.ne', speedOfLight_pos.ne', fineStructureApprox_pos.ne',
    hbarApprox_pos.ne']

theorem coulomb_shell_energy {n : ℕ} (hn : 0 < n) :
    -coulombScale / (2 * (n : ℚ) ^ 2 * bohrRadiusApprox) =
      -hydrogenIonisationApprox / (n : ℚ) ^ 2 := by
  have hn0 : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  have ha : bohrRadiusApprox ≠ 0 := bohrRadiusApprox_pos.ne'
  calc -coulombScale / (2 * (n : ℚ) ^ 2 * bohrRadiusApprox)
      = -(coulombScale / (2 * bohrRadiusApprox)) / (n : ℚ) ^ 2 := by
        field_simp [hn0, ha]
      _ = -hydrogenIonisationApprox / (n : ℚ) ^ 2 := by
        rw [hydrogenIonisation_eq_coulomb_over_bohr]

/-- Hα is wider than Hβ by exactly `27/20` on the Coulomb ladder. -/
theorem balmer_wavelength_ratio :
    (hydrogenIonisationApprox * rydbergGap 2 4) /
        (hydrogenIonisationApprox * rydbergGap 2 3) = 27 / 20 := by
  have hI : hydrogenIonisationApprox ≠ 0 := hydrogenIonisationApprox_pos.ne'
  have h3 : rydbergGap 2 3 ≠ 0 := by unfold rydbergGap; norm_num
  calc (hydrogenIonisationApprox * rydbergGap 2 4) /
          (hydrogenIonisationApprox * rydbergGap 2 3)
      = rydbergGap 2 4 / rydbergGap 2 3 := by field_simp [hI, h3]
    _ = 27 / 20 := balmer_alpha_over_beta

/-! ### The two force factors -/

/-- Attraction-positive radial factor `4 x² f`, in units of `ke²/ℓ²`. -/
noncomputable def radialFactor (f x : ℝ) : ℝ := 4 * x ^ 2 * f

/-- Circular energy in units of `ke²/ℓ`, once `prim` is the running integral of the factor. -/
noncomputable def circularPhaseEnergy (f prim x : ℝ) : ℝ := x * f - 2 * prim

theorem coulomb_phaseEnergy (x : ℝ) : circularPhaseEnergy 1 x x = -x := by
  unfold circularPhaseEnergy
  ring

theorem coulomb_phase_at_radius {ℓ r : ℝ} :
    circularPhaseEnergy 1 (ℓ / (2 * r)) (ℓ / (2 * r)) = -ℓ / (2 * r) := by
  rw [coulomb_phaseEnergy]
  ring

/-- Potential primitive of the equal-scale factor. It is finite at every phase, including every
node. -/
noncomputable def gammaPrimitive (x : ℝ) : ℝ := sinh x * cos x

theorem hasDerivAt_gammaPrimitive (x : ℝ) :
    HasDerivAt gammaPrimitive (gammaSEqualLegacy x) x := by
  have h := (Real.hasDerivAt_sinh x).mul (hasDerivAt_cos x)
  refine h.congr_deriv ?_
  simp only [gammaPrimitive, gammaSEqualLegacy]
  ring

theorem gamma_phaseEnergy (x : ℝ) :
    circularPhaseEnergy (gammaSEqual x) (gammaPrimitive x) x =
      x * gammaSEqual x - 2 * sinh x * cos x := by
  unfold circularPhaseEnergy gammaPrimitive
  ring

/-! ### `γ_s` lies strictly below Coulomb before `π` -/

theorem gammaSEqualLegacy_lt_one {x : ℝ} (hx : x ∈ Ioo 0 π) : gammaSEqualLegacy x < 1 := by
  have hanti := legacy_strictAntiOn_gammaSEqual_even 0
  simp only [mul_zero, Nat.cast_zero, zero_mul, zero_add] at hanti
  have hlt := hanti ⟨le_rfl, pi_pos.le⟩ ⟨hx.1.le, hx.2.le⟩ hx.1
  simpa [gammaSEqualLegacy] using hlt

theorem gammaSEqual_lt_one {x : ℝ} (hx : x ∈ Ioo 0 π) : gammaSEqual x < 1 := by
  have hanti := strictAntiOn_gammaSEqual_even 0
  simp only [mul_zero, Nat.cast_zero, zero_mul, zero_add] at hanti
  have hlt := hanti ⟨le_rfl, pi_pos.le⟩ ⟨hx.1.le, hx.2.le⟩ hx.1
  simpa [gammaSEqual_zero] using hlt

private theorem hasDerivAt_phaseLag (x : ℝ) :
    HasDerivAt (fun y : ℝ => y - gammaPrimitive y) (1 - gammaSEqualLegacy x) x :=
  (hasDerivAt_id x).sub (hasDerivAt_gammaPrimitive x)

/-- A positive derivative on `(0, x)` with `f 0 = 0` makes `f x` positive. -/
private theorem pos_of_deriv_pos {f : ℝ → ℝ} {x : ℝ} (hx : 0 < x) (hf : Continuous f)
    (hderiv : ∀ t ∈ Ioo (0 : ℝ) x, 0 < deriv f t) (h0 : f 0 = 0) : 0 < f x := by
  have hmono : StrictMonoOn f (Icc 0 x) :=
    strictMonoOn_of_deriv_pos (convex_Icc 0 x) hf.continuousOn fun t ht => by
      rw [interior_Icc] at ht
      exact hderiv t ht
  simpa [h0] using hmono ⟨le_rfl, hx.le⟩ ⟨hx.le, le_rfl⟩ hx

theorem gammaPrimitive_lt_phase {x : ℝ} (hx0 : 0 < x) (hxπ : x ≤ π) :
    gammaPrimitive x < x := by
  let f : ℝ → ℝ := fun y => y - gammaPrimitive y
  have hfx : 0 < f x :=
    pos_of_deriv_pos hx0 (by unfold f gammaPrimitive; continuity)
      (fun t ht => by
        rw [(hasDerivAt_phaseLag t).deriv]
        have hγ : gammaSEqualLegacy t < 1 :=
          gammaSEqualLegacy_lt_one ⟨ht.1, lt_of_lt_of_le ht.2 hxπ⟩
        linarith)
      (by simp [f, gammaPrimitive])
  simpa [f, gammaPrimitive, sub_pos] using hfx

private theorem hasDerivAt_forceDefect (t : ℝ) :
    HasDerivAt (fun y : ℝ => y ^ 2 * cosh y - (1 - gammaSEqualLegacy y))
      (2 * t * cosh t + t ^ 2 * sinh t - 2 * cosh t * sin t) t := by
  have hsq : HasDerivAt (fun y : ℝ => y ^ 2) (2 * t) t := by
    simpa [pow_one] using hasDerivAt_pow 2 t
  have hprod := hsq.mul (Real.hasDerivAt_cosh t)
  have hγ : HasDerivAt (fun y : ℝ => 1 - gammaSEqualLegacy y) (2 * cosh t * sin t) t := by
    simpa using (hasDerivAt_gammaSEqualLegacy t).const_sub 1
  have h := hprod.sub hγ
  refine h.congr_deriv ?_
  ring

/-- Fractional reduction of the equal-scale factor: `1 - γ_s(x) < x² cosh x`. -/
theorem force_defect_lt_cosh_sq {x : ℝ} (hx : 0 < x) :
    1 - gammaSEqualLegacy x < x ^ 2 * cosh x := by
  let f : ℝ → ℝ := fun y => y ^ 2 * cosh y - (1 - gammaSEqualLegacy y)
  have hfx : 0 < f x :=
    pos_of_deriv_pos hx (by unfold f gammaSEqualLegacy; continuity)
      (fun t ht => by
        rw [(hasDerivAt_forceDefect t).deriv]
        have hsin : sin t < t := sin_lt ht.1
        have hfact : 2 * t * cosh t + t ^ 2 * sinh t - 2 * cosh t * sin t =
            2 * cosh t * (t - sin t) + t ^ 2 * sinh t := by ring
        rw [hfact]
        have h1 : 0 < 2 * cosh t * (t - sin t) := by
          have hts : 0 < t - sin t := by linarith
          positivity
        have h2 : 0 < t ^ 2 * sinh t := by
          have hs : 0 < sinh t := sinh_pos_iff.mpr ht.1
          exact mul_pos (pow_pos ht.1 2) hs
        linarith)
      (by unfold f; simp [gammaSEqualLegacy])
  linarith

/-! ### Outer well: `γ_s` corrects Coulomb downward, `1/γ_s` corrects it upward

On `(resonanceRoot1, π)` the factor is negative (`gammaSEqual_neg_right_of_first_node`), so it
points outward. -/

theorem outer_factor_order {x : ℝ} (hx : x ∈ Ioo 0 resonanceRoot1) :
    gammaSEqual x < 1 ∧ 1 < (gammaSEqual x)⁻¹ := by
  have hpos := gammaSEqual_pos_left_of_first_node hx
  have hxπ : x < π := lt_trans hx.2 resonanceRoot1_sharp_bounds.2
  have hlt := gammaSEqual_lt_one ⟨hx.1, hxπ⟩
  exact ⟨hlt, one_lt_inv_iff₀.mpr ⟨hpos, hlt⟩⟩

theorem outer_radial_order {x : ℝ} (hx : x ∈ Ioo 0 resonanceRoot1) :
    radialFactor (gammaSEqual x) x < radialFactor 1 x ∧
      radialFactor 1 x < radialFactor (gammaSEqual x)⁻¹ x := by
  have hord := outer_factor_order hx
  have hx4 : (0 : ℝ) < 4 * x ^ 2 := by nlinarith [hx.1]
  constructor
  · unfold radialFactor
    exact mul_lt_mul_of_pos_left hord.1 hx4
  · unfold radialFactor
    exact mul_lt_mul_of_pos_left hord.2 hx4

/-- The written factor exceeds every bound on the way into the first node. -/
theorem exists_writtenFactor_gt {M : ℝ} (hM : 0 ≤ M) :
    ∃ x, x ∈ Ioo 0 resonanceRoot1 ∧ M < (gammaSEqual x)⁻¹ := by
  set a : ℝ := resonanceRoot1 / 2
  have hr0 : (0 : ℝ) < resonanceRoot1 :=
    lt_trans (by linarith [pi_pos]) resonanceRoot1_bounds.1
  have ha0 : 0 < a := by unfold a; positivity
  have ha_lt : a < resonanceRoot1 := by unfold a; linarith
  have ha : a ∈ Ioo 0 resonanceRoot1 := ⟨ha0, ha_lt⟩
  have hga : 0 < gammaSEqual a := gammaSEqual_pos_left_of_first_node ha
  set ε : ℝ := min (gammaSEqual a) (1 / (M + 1))
  have hM1 : 0 < M + 1 := by linarith
  have hε : 0 < ε := by
    unfold ε
    exact lt_min hga (div_pos one_pos hM1)
  have hε_le_g : ε ≤ gammaSEqual a := min_le_left _ _
  have hε_le_inv : ε ≤ 1 / (M + 1) := min_le_right _ _
  have hroot : gammaSEqual resonanceRoot1 = 0 := resonanceRoot1_gammaSEqual_zero
  have hεmem : ε ∈ Icc (gammaSEqual resonanceRoot1) (gammaSEqual a) := by
    refine ⟨?_, hε_le_g⟩
    rw [hroot]
    exact hε.le
  have himg : ε ∈ gammaSEqual '' Icc a resonanceRoot1 :=
    intermediate_value_Icc' (le_of_lt ha_lt) continuous_gammaSEqual.continuousOn hεmem
  obtain ⟨x, hxI, hxγ⟩ := himg
  have hxlt : x < resonanceRoot1 := by
    rcases eq_or_lt_of_le hxI.2 with hEq | hlt
    · rw [hEq, hroot] at hxγ
      exact absurd hxγ.symm hε.ne'
    · exact hlt
  have hxmem : x ∈ Ioo 0 resonanceRoot1 := ⟨lt_of_lt_of_le ha0 hxI.1, hxlt⟩
  have hmul : ε * (M + 1) ≤ 1 := (le_div_iff₀ hM1).mp hε_le_inv
  have hinv : M + 1 ≤ ε⁻¹ := by
    rw [inv_eq_one_div, le_div_iff₀ hε]
    simpa [mul_comm] using hmul
  refine ⟨x, hxmem, ?_⟩
  rw [hxγ]
  exact lt_of_lt_of_le (by linarith) hinv

/-! ### Node ladders are not the gross structure -/

/-- Phases in the first three sharp node windows, read as energies proportional to `-x`. The gap
from the innermost of the three to the middle, over the gap down to the outermost, is strictly
below the Lyman ratio `27/32`. -/
theorem node_phase_gap_lt_lyman {x0 x1 x2 : ℝ}
    (h0 : x0 ∈ Ioo (π / 4) (π / 2))
    (h1 : x1 ∈ Ioo (π + π / 4) (π + π / 2))
    (h2 : x2 ∈ Ioo (2 * π + π / 4) (2 * π + π / 2)) :
    (x2 - x1) / (x2 - x0) < (27 : ℝ) / 32 := by
  have hnum : x2 - x1 < 5 * π / 4 := by linarith [h1.1, h2.2]
  have hden : 7 * π / 4 < x2 - x0 := by linarith [h0.2, h2.1]
  have hpos_bound : 0 < 7 * π / 4 := by positivity
  have hpos_den : 0 < x2 - x0 := by linarith [hden, hpos_bound]
  have hpos_num : 0 < 5 * π / 4 := by positivity
  have hstep₁ : (x2 - x1) / (x2 - x0) < (5 * π / 4) / (x2 - x0) :=
    div_lt_div_of_pos_right hnum hpos_den
  have hstep₂ : (5 * π / 4) / (x2 - x0) < (5 * π / 4) / (7 * π / 4) :=
    div_lt_div_of_pos_left hpos_num hpos_bound hden
  have hfrac : (5 * π / 4) / (7 * π / 4) = (5 : ℝ) / 7 := by
    field_simp
  have h57 : (5 * π / 4) / (7 * π / 4) < 27 / 32 := by
    rw [hfrac]
    norm_num
  exact lt_trans (lt_trans hstep₁ hstep₂) h57

theorem equalScale_nodes_miss_lyman {x0 x1 x2 : ℝ}
    (h0z : gammaSEqual x0 = 0) (h0 : x0 ∈ Ioo (0 : ℝ) π)
    (h1z : gammaSEqual x1 = 0) (h1 : x1 ∈ Ioo π (2 * π))
    (h2z : gammaSEqual x2 = 0) (h2 : x2 ∈ Ioo (2 * π) (3 * π)) :
    (x2 - x1) / (x2 - x0) < (27 : ℝ) / 32 := by
  have hx0 : x0 = branchNode 0 :=
    branchNode_eq_of_gamma_zero 0 (by simpa [Nat.cast_zero, zero_mul, zero_add] using h0) h0z
  have hmem1 : x1 ∈ Ioo (((1 : ℕ) : ℝ) * π) (((1 : ℕ) : ℝ) * π + π) := by
    convert h1 <;> simp [one_mul] <;> ring
  have hx1 : x1 = branchNode 1 := branchNode_eq_of_gamma_zero 1 hmem1 h1z
  have hmem2 : x2 ∈ Ioo (((2 : ℕ) : ℝ) * π) (((2 : ℕ) : ℝ) * π + π) := by
    convert h2 <;> simp [Nat.cast_two, two_mul]; ring
  have hx2 : x2 = branchNode 2 := branchNode_eq_of_gamma_zero 2 hmem2 h2z
  rw [hx0, hx1, hx2]
  unfold branchNode
  ring_nf
  norm_num

/-- Phases with the first one inside `(π/4, 1)`, read as energies proportional to `-1/x`.
The second gap over the first is strictly below the hydrogen ratio `5/27`. -/
theorem inv_node_gap_lt_hydrogen {x0 x1 x2 : ℝ}
    (h0 : x0 ∈ Ioo (π / 4) 1)
    (h1 : x1 ∈ Ioo (π + π / 4) (π + π / 2))
    (h2 : x2 ∈ Ioo (2 * π + π / 4) (2 * π + π / 2)) :
    (x1⁻¹ - x2⁻¹) / (x0⁻¹ - x1⁻¹) < (5 : ℝ) / 27 := by
  simp_rw [inv_eq_one_div]
  have hx0 : 0 < x0 := by linarith [h0.1, pi_pos]
  have hx1 : 0 < x1 := by linarith [h1.1, pi_pos]
  have hx2 : 0 < x2 := by linarith [h2.1, pi_pos]
  have hx1_lo : 5 * π / 4 < x1 := by linarith [h1.1]
  have hx2_hi : x2 < 5 * π / 2 := by linarith [h2.2]
  have h5π : (0 : ℝ) < 5 * π := by positivity
  have hinv1 : 1 / x1 < 4 / (5 * π) := by
    rw [div_lt_div_iff₀ hx1 h5π]
    linarith
  have hinv2 : 2 / (5 * π) < 1 / x2 := by
    rw [div_lt_div_iff₀ h5π hx2]
    linarith
  have hnum : 1 / x1 - 1 / x2 < 2 / (5 * π) := by
    have hdiff : 4 / (5 * π) - 2 / (5 * π) = 2 / (5 * π) := by ring
    linarith [hinv1, hinv2, hdiff]
  have hinv0 : (1 : ℝ) < 1 / x0 := by
    rw [lt_div_iff₀ hx0]
    linarith [h0.2]
  have hid : (1 : ℝ) - 4 / (5 * π) = (5 * π - 4) / (5 * π) := by field_simp
  have hden : (5 * π - 4) / (5 * π) < 1 / x0 - 1 / x1 := by
    have : 1 - 4 / (5 * π) < 1 / x0 - 1 / x1 := by linarith
    rwa [hid] at this
  have hden_pos : 0 < 1 / x0 - 1 / x1 := by
    have hpos_bound : 0 < (5 * π - 4) / (5 * π) := by
      have : (0 : ℝ) < 5 * π - 4 := by linarith [pi_gt_three]
      exact div_pos this h5π
    exact lt_trans hpos_bound hden
  have hstep₁ : (1 / x1 - 1 / x2) / (1 / x0 - 1 / x1) <
      (2 / (5 * π)) / (1 / x0 - 1 / x1) :=
    div_lt_div_of_pos_right hnum hden_pos
  have hpos_b : 0 < (5 * π - 4) / (5 * π) := by
    have : (0 : ℝ) < 5 * π - 4 := by linarith [pi_gt_three]
    exact div_pos this h5π
  have hpos_n : 0 < 2 / (5 * π) := by positivity
  have hstep₂ : (2 / (5 * π)) / (1 / x0 - 1 / x1) <
      (2 / (5 * π)) / ((5 * π - 4) / (5 * π)) :=
    div_lt_div_of_pos_left hpos_n hpos_b hden
  have hfrac : (2 / (5 * π)) / ((5 * π - 4) / (5 * π)) = 2 / (5 * π - 4) := by
    field_simp
  have hπ : (11 : ℝ) < 5 * π - 4 := by linarith [pi_gt_three]
  have h11 : 0 < 5 * π - 4 := by linarith
  have hrec : 2 / (5 * π - 4) < 2 / 11 := by
    rw [div_lt_div_iff₀ h11 (by norm_num : (0 : ℝ) < 11)]
    linarith
  have htarget : (2 : ℝ) / 11 < 5 / 27 := by norm_num
  have hchain : 2 / (5 * π - 4) < 5 / 27 := lt_trans hrec htarget
  have hfin : (2 / (5 * π)) / ((5 * π - 4) / (5 * π)) < 5 / 27 := by
    rw [hfrac]
    exact hchain
  exact lt_trans (lt_trans hstep₁ hstep₂) hfin

end Gravity

end DstDiophantine
