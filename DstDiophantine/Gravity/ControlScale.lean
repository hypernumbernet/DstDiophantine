import DstDiophantine.Gravity.HoldPrice
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# One scale for the control inequalities

The shield parabola, the two outer lobes, and the price of a hold are one
comparison once mass, mismatch, and lag are read in units of
\(k^2=(\pi/2)^2\).

With \(j=J/k^2\),
\[
M/k^2 \le 5/4 + \min\bigl(j^2,(j-1)^2,(j+1)^2\bigr),
\]
the square of the distance from \(j\) to the nearest of the centers
\(\{-1,0,1\}\). This is identical to `controlCeiling`. On that boundary
every axis lies on the wall, so the lag is the holding price of the same
distance,
\[
L/k^2 = 2 + 4\min\bigl(j^2,(j-1)^2,(j+1)^2\bigr).
\]
The three centers share the mass \(5k^2/4\) and the lag \(2k^2\). The
neutral lag ceiling is that shared lag, and the holding price vanishes at
the free-sitting mass \(3k^2/4\).

## Paper boundary (do **not** claim)

No electromagnetic coupling, no laboratory protocol, and no identification
of either channel force with a Faraday field.
-/

namespace DstDiophantine

namespace Gravity

open scoped Real
open Operations Invariant Admissible

/-! ### The cone scale -/

noncomputable def coneScale : ℝ := (Real.pi / 2) ^ 2

theorem coneScale_eq : coneScale = Real.pi ^ 2 / 4 := by
  unfold coneScale
  ring

theorem coneScale_pos : 0 < coneScale := by
  rw [coneScale_eq]
  positivity

theorem shield_mass_eq_scaled : 5 * Real.pi ^ 2 / 16 = 5 * coneScale / 4 := by
  rw [coneScale_eq]
  ring

theorem freeSit_mass_eq_scaled : 3 * Real.pi ^ 2 / 16 = 3 * coneScale / 4 := by
  rw [coneScale_eq]
  ring

theorem coneMass_eq_scaled : 3 * Real.pi ^ 2 / 8 = 3 * coneScale / 2 := by
  rw [coneScale_eq]
  ring

theorem neutral_lag_cap_eq_scaled : Real.pi ^ 2 / 2 = 2 * coneScale := by
  rw [coneScale_eq]
  ring

theorem half_wall : Real.pi / 4 = (Real.pi / 2) / 2 := by
  ring

theorem third_wall : Real.pi / 6 = (Real.pi / 2) / 3 := by
  ring

theorem ponderomotive_cap_eq_scaled : Real.pi ^ 2 / 32 = coneScale / 8 := by
  rw [coneScale_eq]
  ring

theorem isotropic_drop_eq_scaled : Real.pi ^ 2 / 72 = coneScale / 18 := by
  rw [coneScale_eq]
  ring

/-- Five sixths is the shield mass over the cone's own mass ceiling. -/
theorem shield_div_coneMass : (5 * coneScale / 4) / (3 * coneScale / 2) = 5 / 6 := by
  have hc : coneScale ≠ 0 := ne_of_gt coneScale_pos
  field_simp
  ring

/-- The holding price vanishes at the free-sitting mass and equals the
neutral lag ceiling at the shield mass. -/
theorem holdPrice_freeSit_and_shield :
    4 * (3 * coneScale / 4) - 3 * coneScale = 0 ∧
      4 * (5 * coneScale / 4) - 3 * coneScale = 2 * coneScale := by
  constructor <;> ring

/-! ### Distance to the three centers -/

noncomputable def lobeExcess (j : ℝ) : ℝ :=
  min (j ^ 2) (min ((j - 1) ^ 2) ((j + 1) ^ 2))

private theorem min_sq_of_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    min (a ^ 2) (b ^ 2) = (min a b) ^ 2 := by
  rcases le_total a b with h | h
  · have hsq : a ^ 2 ≤ b ^ 2 := by nlinarith
    rw [min_eq_left h, min_eq_left hsq]
  · have hsq : b ^ 2 ≤ a ^ 2 := by nlinarith
    rw [min_eq_right h, min_eq_right hsq]

/-- The excess is the squared distance to the nearest of \(-1\), \(0\), and \(1\). -/
theorem lobeExcess_eq_distSq (j : ℝ) :
    lobeExcess j = (min |j| (min |j - 1| |j + 1|)) ^ 2 := by
  unfold lobeExcess
  have h0 : 0 ≤ |j| := abs_nonneg j
  have h1 : 0 ≤ |j - 1| := abs_nonneg (j - 1)
  have h2 : 0 ≤ |j + 1| := abs_nonneg (j + 1)
  have h12 := min_sq_of_nonneg h1 h2
  rw [(sq_abs j).symm, (sq_abs (j - 1)).symm, (sq_abs (j + 1)).symm, h12]
  exact min_sq_of_nonneg h0 (le_min h1 h2)

theorem lobeExcess_center (j : ℝ) (h : j = -1 ∨ j = 0 ∨ j = 1) :
    lobeExcess j = 0 := by
  rcases h with rfl | rfl | rfl
  · unfold lobeExcess
    have hz : ((-1 : ℝ) + 1) ^ 2 = 0 := by ring
    have h4 : ((-1 : ℝ) - 1) ^ 2 = 4 := by norm_num
    have h1 : ((-1 : ℝ) ^ 2) = 1 := by norm_num
    rw [hz, h4, h1]
    norm_num
  · unfold lobeExcess
    norm_num
  · unfold lobeExcess
    norm_num

/-! ### The envelope in units of \(k^2\) -/

private theorem four_sq_scale (Jval : ℝ) :
    (4 / Real.pi ^ 4) * (4 * Jval ^ 2) = (Jval / coneScale) ^ 2 := by
  rw [coneScale_eq]
  field_simp

private theorem sub_sq_scale (Jval : ℝ) :
    (4 / Real.pi ^ 4) * (2 * Jval - Real.pi ^ 2 / 2) ^ 2 =
      (Jval / coneScale - 1) ^ 2 := by
  rw [coneScale_eq]
  field_simp
  ring

private theorem add_sq_scale (Jval : ℝ) :
    (4 / Real.pi ^ 4) * (2 * Jval + Real.pi ^ 2 / 2) ^ 2 =
      (Jval / coneScale + 1) ^ 2 := by
  rw [coneScale_eq]
  field_simp
  ring

private theorem envelopeNum_div_scale (Jval : ℝ) :
    (4 / Real.pi ^ 4) * controlEnvelopeNum Jval = lobeExcess (Jval / coneScale) := by
  have hpos : (0 : ℝ) ≤ 4 / Real.pi ^ 4 := by positivity
  have hmul : ∀ x y : ℝ,
      (4 / Real.pi ^ 4) * min x y =
        min ((4 / Real.pi ^ 4) * x) ((4 / Real.pi ^ 4) * y) :=
    fun x y => mul_min_of_nonneg x y hpos
  unfold controlEnvelopeNum lobeExcess
  rw [hmul, hmul, four_sq_scale, sub_sq_scale, add_sq_scale]

/-- `controlCeiling`, divided by \(k^2\), is the distance bound. -/
theorem controlCeiling_div_coneScale (Jval : ℝ) :
    controlCeiling Jval / coneScale = 5 / 4 + lobeExcess (Jval / coneScale) := by
  have hfloor : (5 * Real.pi ^ 2 / 16) / coneScale = 5 / 4 := by
    rw [coneScale_eq]
    field_simp
    ring
  have henv :
      controlEnvelopeNum Jval / Real.pi ^ 2 / coneScale =
        (4 / Real.pi ^ 4) * controlEnvelopeNum Jval := by
    rw [coneScale_eq]
    field_simp
  unfold controlCeiling
  rw [add_div, hfloor, henv, envelopeNum_div_scale]

theorem scaledMass_le_lobe {p : TorsionParams} (h : IsAdmissibleContinuous p) :
    mass p / coneScale ≤ 5 / 4 + lobeExcess (J p / coneScale) := by
  have hM := mass_le_control_ceiling p h
  have hdiv : mass p / coneScale ≤ controlCeiling (J p) / coneScale :=
    div_le_div_of_nonneg_right hM (le_of_lt coneScale_pos)
  rw [controlCeiling_div_coneScale] at hdiv
  exact hdiv

theorem scaledMass_eq_lobe_iff {p : TorsionParams} (h : IsAdmissibleContinuous p) :
    mass p / coneScale = 5 / 4 + lobeExcess (J p / coneScale) ↔
      OnWall p ∧ TwoCorners p := by
  have hc : coneScale ≠ 0 := ne_of_gt coneScale_pos
  have hid := controlCeiling_div_coneScale (J p)
  constructor
  · intro heq
    have hmass : mass p = controlCeiling (J p) := by
      have hdiv : mass p / coneScale = controlCeiling (J p) / coneScale := by
        rw [heq, hid]
      exact (div_left_inj' hc).mp hdiv
    exact (onEnvelope_iff h).mp hmass
  · intro hlock
    have hmass := (onEnvelope_iff h).mpr hlock
    rw [← hid, hmass]

/-! ### The hold on that boundary is the same distance -/

theorem lagSq_div_coneScale_of_onEnvelope {p : TorsionParams}
    (h : IsAdmissibleContinuous p) (hE : mass p = controlCeiling (J p)) :
    lagSq p / coneScale = 2 + 4 * lobeExcess (J p / coneScale) := by
  have hw := ((onEnvelope_iff h).mp hE).1
  have hlag := (lagSq_eq_mass_wall_iff h).mpr hw
  have hceil := controlCeiling_div_coneScale (J p)
  have hmass : mass p / coneScale = 5 / 4 + lobeExcess (J p / coneScale) := by
    rw [hE, hceil]
  have hlag' : lagSq p = 4 * mass p - 3 * coneScale := by
    rw [coneScale_eq] at *
    linarith
  have hdiv : lagSq p / coneScale = 4 * (mass p / coneScale) - 3 := by
    have hc : coneScale ≠ 0 := ne_of_gt coneScale_pos
    field_simp [hc]
    linarith
  rw [hdiv, hmass]
  ring

theorem stiffness_div_coneScale_of_onEnvelope {m : ℝ} {p : TorsionParams}
    (h : IsAdmissibleContinuous p) (hE : mass p = controlCeiling (J p)) :
    stiffnessPotential m p =
      m * coneScale * (1 + 2 * lobeExcess (J p / coneScale)) := by
  have hL := lagSq_div_coneScale_of_onEnvelope h hE
  have hc : coneScale ≠ 0 := ne_of_gt coneScale_pos
  have hlag : lagSq p = coneScale * (2 + 4 * lobeExcess (J p / coneScale)) := by
    field_simp [hc] at hL
    exact hL
  rw [stiffnessPotential_eq_lag, hlag]
  ring

/-! ### The three centers share one mass and one lag -/

private theorem lagSq_twoUsual_center :
    lagSq (twoUsualWitness (Real.pi / 4)) = 2 * coneScale := by
  rw [lagSq, coneScale]
  simp only [twoUsualWitness, Fin.sum_univ_three]
  norm_num
  ring

private theorem lagSq_dagger (p : TorsionParams) :
    lagSq (daggerParams p) = lagSq p := by
  rw [lagSq, lagSq]
  simp only [daggerParams, Fin.sum_univ_three]
  ring

theorem center_usual_mass_lag :
    J (twoUsualWitness (Real.pi / 4)) / coneScale = 1 ∧
      mass (twoUsualWitness (Real.pi / 4)) / coneScale = 5 / 4 ∧
        lagSq (twoUsualWitness (Real.pi / 4)) / coneScale = 2 ∧
          stiffnessPotential 1 (twoUsualWitness (Real.pi / 4)) = coneScale := by
  have hJ : J (twoUsualWitness (Real.pi / 4)) = coneScale := by
    rw [J_twoUsualWitness, coneScale_eq]
    ring
  have hM : mass (twoUsualWitness (Real.pi / 4)) = 5 * coneScale / 4 := by
    rw [mass_twoUsualWitness, shield_mass_eq_scaled]
    ring
  have hL := lagSq_twoUsual_center
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hJ]
    field_simp [ne_of_gt coneScale_pos]
  · rw [hM]
    field_simp [ne_of_gt coneScale_pos]
  · rw [hL]
    field_simp [ne_of_gt coneScale_pos]
  · rw [stiffnessPotential_eq_lag, hL]
    ring

theorem center_dual_mass_lag :
    J (twoDualWitness (Real.pi / 4)) / coneScale = -1 ∧
      mass (twoDualWitness (Real.pi / 4)) / coneScale = 5 / 4 ∧
        lagSq (twoDualWitness (Real.pi / 4)) / coneScale = 2 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [J_twoDualWitness, coneScale_eq]
    field_simp [ne_of_gt coneScale_pos]
    ring
  · rw [mass_twoDualWitness, mass_twoUsualWitness, shield_mass_eq_scaled]
    field_simp [ne_of_gt coneScale_pos]
    ring
  · unfold twoDualWitness
    rw [lagSq_dagger, lagSq_twoUsual_center]
    field_simp [ne_of_gt coneScale_pos]

theorem center_shield_mass_lag :
    J maximalShield / coneScale = 0 ∧
      mass maximalShield / coneScale = 5 / 4 ∧
        lagSq maximalShield / coneScale = 2 ∧
          stiffnessPotential 1 maximalShield = coneScale := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [J_maximalShield, zero_div]
  · rw [mass_maximalShield, shield_mass_eq_scaled]
    field_simp [ne_of_gt coneScale_pos]
  · rw [lagSq_maximalShield, neutral_lag_cap_eq_scaled]
    field_simp [ne_of_gt coneScale_pos]
  · rw [stiffness_maximalShield, coneScale_eq]
    ring

end Gravity

end DstDiophantine
