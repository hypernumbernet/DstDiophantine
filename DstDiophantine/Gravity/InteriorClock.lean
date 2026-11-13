import DstDiophantine.Gravity.SI
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option linter.style.native false

/-!
# Interior clock, apart from the potential

Two separate readings of a static spherical body.

DST time at a station is the enclosed compactness
`μ = G M(<r) / (c² r)`, the value at that station. At the centre the
enclosed mass vanishes and the rate equals the vacuum rate at infinity.
The advance of that centre clock against the surface factor is `centreAdvance`.

The potential is a different quantity. Its radial slope is the weight
`grav`, below the surface as well as above, and a carrier that tracks
`Φ` is shifted by `potentialSlope`. Outside, where `M` is constant, the
weak-field clock difference and the potential difference agree, and the
finite height shift is `GM/c² (1/r - 1/(r+h))` for both. The uniform
Newtonian centre, relative to the surface, is `-ε/2`.

## What is not claimed

No theorem says that a frequency beat of two clocks equals the wavelength
change of the carrier. The Earth figures are rounding bins for the external
`GM`, `R`, `G`, and `c` of the papers. They are not derived from the rotor algebra.
-/

namespace DstDiophantine

namespace Gravity

namespace InteriorClock

noncomputable section

open Real SI

/-- Enclosed compactness `G M / (c² r)`. The DST rate at one station. -/
def compactness (GM c2 r : ℝ) : ℝ :=
  GM / (c2 * r)

/-- Weak-field DST clock shift of the upper station against the lower, outside
the body. -/
def clockExterior (GM c2 r h : ℝ) : ℝ :=
  compactness GM c2 r - compactness GM c2 (r + h)

/-- Weak-field shift of a carrier that tracks the potential `Φ = -GM/r`. -/
def potentialExterior (GM c2 r h : ℝ) : ℝ :=
  ((-GM / (r + h)) - (-GM / r)) / c2

theorem clockExterior_eq {GM c2 r h : ℝ} (hr : r ≠ 0) (hrh : r + h ≠ 0) (hc : c2 ≠ 0) :
    clockExterior GM c2 r h = GM / c2 * (1 / r - 1 / (r + h)) := by
  unfold clockExterior compactness
  field_simp [hr, hrh, hc]

theorem potentialExterior_eq {GM c2 r h : ℝ} (hr : r ≠ 0) (hrh : r + h ≠ 0) (hc : c2 ≠ 0) :
    potentialExterior GM c2 r h = GM / c2 * (1 / r - 1 / (r + h)) := by
  unfold potentialExterior
  field_simp [hr, hrh, hc]
  ring

/-- Above the surface the weak-field clock and the potential agree. -/
theorem exterior_agreement {GM c2 r h : ℝ} (hr : r ≠ 0) (hrh : r + h ≠ 0) (hc : c2 ≠ 0) :
    clockExterior GM c2 r h = potentialExterior GM c2 r h := by
  rw [clockExterior_eq hr hrh hc, potentialExterior_eq hr hrh hc]

theorem newtonShift_eq_height {GM c2 r h : ℝ} (hr : r ≠ 0) (hrh : r + h ≠ 0) (hc : c2 ≠ 0) :
    GM / c2 * (1 / r - 1 / (r + h)) = (GM / r ^ 2) / c2 * h * (r / (r + h)) := by
  field_simp [hr, hrh, hc]
  ring

/-- Radial slope of `Φ/c²`, where `dΦ/dr = grav`. The weight, above or below the surface. -/
def potentialSlope (grav c2 : ℝ) : ℝ :=
  grav / c2

/-- Shift of light that climbs a height `h` against that weight. -/
def lightClimb (grav c2 h : ℝ) : ℝ :=
  potentialSlope grav c2 * h

theorem potentialSlope_eq {grav c2 : ℝ} : potentialSlope grav c2 = grav / c2 := by
  unfold potentialSlope
  rfl

theorem lightClimb_eq {grav c2 h : ℝ} : lightClimb grav c2 h = grav * h / c2 := by
  unfold lightClimb potentialSlope
  ring

/-- Centre advance of the enclosed-mass factor, `1/√(1-2ε) - 1`. -/
def centreAdvance (ε : ℝ) : ℝ :=
  1 / sqrt (1 - 2 * ε) - 1

/-- DST rate at the centre. Cancellation restores the vacuum value. -/
def centreFactor : ℝ :=
  1

/-- Surface factor `√(1-2ε)` of the enclosed compactness. -/
def surfaceFactor (ε : ℝ) : ℝ :=
  sqrt (1 - 2 * ε)

theorem centreAdvance_eq_ratio {ε : ℝ} :
    centreFactor / surfaceFactor ε - 1 = centreAdvance ε := by
  unfold centreFactor surfaceFactor centreAdvance
  rfl

/-- Uniform Newtonian centre relative to the surface, `-ε/2`. -/
def continuumCentre (ε : ℝ) : ℝ :=
  -ε / 2

theorem centreAdvance_eq {ε : ℝ} (hε : ε < 1 / 2) :
    centreAdvance ε = 2 * ε / (sqrt (1 - 2 * ε) * (1 + sqrt (1 - 2 * ε))) := by
  have hpos : 0 ≤ 1 - 2 * ε := by linarith
  set s : ℝ := sqrt (1 - 2 * ε)
  have hs0 : s ≠ 0 := by
    have : 0 < 1 - 2 * ε := by linarith
    exact (sqrt_pos.mpr this).ne'
  have hs1 : 1 + s ≠ 0 := by
    have : 0 ≤ s := sqrt_nonneg _
    linarith
  have hsq : s ^ 2 = 1 - 2 * ε := sq_sqrt hpos
  unfold centreAdvance
  suffices (1 / s - 1) * (s * (1 + s)) = 2 * ε by
    exact (eq_div_iff (mul_ne_zero hs0 hs1)).mpr this
  have hclear : (1 / s - 1) * (s * (1 + s)) = 1 - s ^ 2 := by
    field_simp [hs0]
    ring
  rw [hclear, hsq]
  ring

theorem centreAdvance_gt {ε : ℝ} (h0 : 0 < ε) (hε : ε < 1 / 2) : ε < centreAdvance ε := by
  have hε0 : 0 < ε := h0
  rw [centreAdvance_eq hε]
  have hpos : 0 ≤ 1 - 2 * ε := by linarith
  set s : ℝ := sqrt (1 - 2 * ε)
  have hs : 0 < s := sqrt_pos.mpr (by linarith)
  have hden : 0 < s * (1 + s) := by positivity
  rw [lt_div_iff₀ hden]
  have hsq : s ^ 2 = 1 - 2 * ε := sq_sqrt hpos
  have hcmp : s ^ 2 < (1 + 2 * ε) ^ 2 := by
    rw [hsq]
    nlinarith [hε0]
  have hsqrt : s < 1 + 2 * ε :=
    (sq_lt_sq₀ (sqrt_nonneg _) (by linarith : (0 : ℝ) ≤ 1 + 2 * ε)).mp hcmp
  nlinarith [hsq, hsqrt, hε0]

theorem centreAdvance_mono {ε₁ ε₂ : ℝ} (h0 : 0 ≤ ε₁) (hlt : ε₁ < ε₂) (h2 : ε₂ < 1 / 2) :
    centreAdvance ε₁ < centreAdvance ε₂ := by
  have hε1 : 0 ≤ ε₁ := h0
  unfold centreAdvance
  have hpos1 : 0 < 1 - 2 * ε₁ := by linarith [hε1]
  have hpos2 : 0 < 1 - 2 * ε₂ := by linarith
  have hs : sqrt (1 - 2 * ε₂) < sqrt (1 - 2 * ε₁) := sqrt_lt_sqrt hpos2.le (by linarith)
  have hs1 : 0 < sqrt (1 - 2 * ε₁) := sqrt_pos.mpr hpos1
  have hs2 : 0 < sqrt (1 - 2 * ε₂) := sqrt_pos.mpr hpos2
  have hinv : (sqrt (1 - 2 * ε₁))⁻¹ < (sqrt (1 - 2 * ε₂))⁻¹ := (inv_lt_inv₀ hs1 hs2).mpr hs
  simpa [one_div] using sub_lt_sub_right hinv 1

theorem uniform_centre_shift {GM R c2 : ℝ} (hR : R ≠ 0) (hc : c2 ≠ 0) :
    ((-3 * GM / (2 * R)) - (-GM / R)) / c2 = continuumCentre (GM / (R * c2)) := by
  unfold continuumCentre
  field_simp [hR, hc]
  ring

theorem centre_signs {ε : ℝ} (h0 : 0 < ε) (hε : ε < 1 / 2) :
    0 < centreAdvance ε ∧ continuumCentre ε < 0 := by
  refine ⟨lt_trans h0 (centreAdvance_gt h0 hε), ?_⟩
  unfold continuumCentre
  linarith

/-! ### Earth rounding bins

External inputs of the papers: `GM = 3.986004418 × 10¹⁴`, `R = 6.371 × 10⁶`,
with `G` and `c` from `SI`. A displayed figure means the exact value lies
in that figure's rounding bin. -/

def earthGM : ℕ := 3986004418 * 10 ^ 5

def earthRadius : ℕ := 6371000

private def compactnessDen : ℕ := earthRadius * speedOfLightNat ^ 2

private def weightDen : ℕ := earthRadius ^ 2 * speedOfLightNat ^ 2

def earthCompactnessQ : ℚ := (earthGM : ℚ) / compactnessDen

def earthWeightQ : ℚ := (earthGM : ℚ) / weightDen

def earthGravityQ : ℚ :=
  (earthGM : ℚ) / (earthRadius ^ 2 : ℚ)

private theorem nat_div_lt_pow {a c d e : ℕ} (hd : 0 < d) (h : a * d < c * 10 ^ e) :
    (a : ℚ) / 10 ^ e < (c : ℚ) / d := by
  have he : (0 : ℚ) < (10 : ℚ) ^ e := pow_pos (by norm_num) e
  have hd' : (0 : ℚ) < d := Nat.cast_pos.mpr hd
  refine (div_lt_div_iff₀ he hd').mpr ?_
  exact_mod_cast h

private theorem nat_div_gt_pow {a c d e : ℕ} (hd : 0 < d) (h : c * 10 ^ e < a * d) :
    (c : ℚ) / d < (a : ℚ) / 10 ^ e := by
  have he : (0 : ℚ) < (10 : ℚ) ^ e := pow_pos (by norm_num) e
  have hd' : (0 : ℚ) < d := Nat.cast_pos.mpr hd
  refine (div_lt_div_iff₀ hd' he).mpr ?_
  exact_mod_cast h

private theorem compactness_den_pos : 0 < earthRadius * speedOfLightNat ^ 2 := by
  unfold earthRadius speedOfLightNat
  norm_num

private theorem compactness_lo_witness :
    6961 * (earthRadius * speedOfLightNat ^ 2) < earthGM * 10 ^ 13 := by
  unfold earthRadius speedOfLightNat earthGM
  native_decide

private theorem compactness_hi_witness :
    earthGM * 10 ^ 13 < 6962 * (earthRadius * speedOfLightNat ^ 2) := by
  unfold earthRadius speedOfLightNat earthGM
  native_decide

theorem earthCompactnessQ_bounds :
    (6961 : ℚ) / 10 ^ 13 < earthCompactnessQ ∧ earthCompactnessQ < (6962 : ℚ) / 10 ^ 13 := by
  unfold earthCompactnessQ compactnessDen
  refine ⟨?_, ?_⟩
  · simpa only [Nat.cast_ofNat] using
      nat_div_lt_pow compactness_den_pos compactness_lo_witness
  · simpa only [Nat.cast_ofNat] using
      nat_div_gt_pow compactness_den_pos compactness_hi_witness

private theorem gravity_den_pos : 0 < earthRadius ^ 2 := by
  unfold earthRadius
  norm_num

private theorem gravity_lo_witness : 9815 * earthRadius ^ 2 < earthGM * 10 ^ 3 := by
  unfold earthRadius earthGM
  native_decide

private theorem gravity_hi_witness : earthGM * 10 ^ 3 < 9825 * earthRadius ^ 2 := by
  unfold earthRadius earthGM
  native_decide

theorem earthGravityQ_bounds :
    (9815 : ℚ) / 10 ^ 3 < earthGravityQ ∧ earthGravityQ < (9825 : ℚ) / 10 ^ 3 := by
  unfold earthGravityQ
  refine ⟨?_, ?_⟩
  · exact nat_div_lt_pow gravity_den_pos gravity_lo_witness
  · exact nat_div_gt_pow gravity_den_pos gravity_hi_witness

private theorem weight_den_pos : 0 < earthRadius ^ 2 * speedOfLightNat ^ 2 := by
  unfold earthRadius speedOfLightNat
  norm_num

private theorem weight_lo_witness :
    10925 * (earthRadius ^ 2 * speedOfLightNat ^ 2) < earthGM * 10 ^ 20 := by
  unfold earthRadius speedOfLightNat earthGM
  native_decide

private theorem weight_hi_witness :
    earthGM * 10 ^ 20 < 10935 * (earthRadius ^ 2 * speedOfLightNat ^ 2) := by
  unfold earthRadius speedOfLightNat earthGM
  native_decide

theorem earthWeightQ_bounds :
    (10925 : ℚ) / 10 ^ 20 < earthWeightQ ∧ earthWeightQ < (10935 : ℚ) / 10 ^ 20 := by
  unfold earthWeightQ weightDen
  refine ⟨?_, ?_⟩
  · simpa only [Nat.cast_ofNat] using nat_div_lt_pow weight_den_pos weight_lo_witness
  · simpa only [Nat.cast_ofNat] using nat_div_gt_pow weight_den_pos weight_hi_witness

def earthWeight : ℝ :=
  (earthGM : ℝ) / ((earthRadius : ℝ) ^ 2 * (speedOfLight : ℝ) ^ 2)

def earthGravity : ℝ :=
  (earthGM : ℝ) / (earthRadius : ℝ) ^ 2

private theorem earthWeight_cast : (earthWeightQ : ℝ) = earthWeight := by
  unfold earthWeightQ weightDen earthWeight speedOfLight
  push_cast
  rfl

private theorem earthGravity_cast : (earthGravityQ : ℝ) = earthGravity := by
  unfold earthGravityQ earthGravity
  push_cast
  rfl

private theorem lift_lt {a b : ℚ} (h : a < b) : (a : ℝ) < b :=
  (Rat.cast_lt (K := ℝ)).mpr h

/-- The shared potential gradient `g/c²` rounds to `1.093×10⁻¹⁶` per metre. -/
theorem earth_potential_gradient_bins :
    (10925 : ℝ) / 10 ^ 20 < earthWeight ∧ earthWeight < (10935 : ℝ) / 10 ^ 20 := by
  refine ⟨?_, ?_⟩
  · have h := lift_lt earthWeightQ_bounds.1
    simpa [earthWeight_cast] using h
  · have h := lift_lt earthWeightQ_bounds.2
    simpa [earthWeight_cast] using h

/-- Surface weight `g = GM/R²` rounds to `9.82`. -/
theorem earth_gravity_bins :
    (9815 : ℝ) / 10 ^ 3 < earthGravity ∧ earthGravity < (9825 : ℝ) / 10 ^ 3 := by
  refine ⟨?_, ?_⟩
  · have h := lift_lt earthGravityQ_bounds.1
    simpa [earthGravity_cast] using h
  · have h := lift_lt earthGravityQ_bounds.2
    simpa [earthGravity_cast] using h

private theorem centre_product_witness :
    (10 : ℕ) ^ 13 * (10 ^ 13 + 6965) ^ 2 >
      ((10 : ℕ) ^ 13) ^ 3 + 13924 * (10 ^ 13 + 6965) ^ 2 := by
  native_decide

private theorem centreAdvance_at_6962 :
    centreAdvance ((6962 : ℝ) / 10 ^ 13) < (6965 : ℝ) / 10 ^ 13 := by
  set ε : ℝ := (6962 : ℝ) / 10 ^ 13
  have hpos : 0 < 1 - 2 * ε := by norm_num
  have hcast : ((10 : ℝ) ^ 13) * ((10 : ℝ) ^ 13 + 6965) ^ 2 >
      ((10 : ℝ) ^ 13) ^ 3 + 13924 * ((10 : ℝ) ^ 13 + 6965) ^ 2 := by
    exact_mod_cast centre_product_witness
  have hmul : 1 < (1 - 2 * ε) * (1 + (6965 : ℝ) / 10 ^ 13) ^ 2 := by
    have he : (0 : ℝ) < (10 : ℝ) ^ 13 := by norm_num
    have hdiv := div_lt_div_of_pos_right hcast (pow_pos he 3)
    have hone : ((10 : ℝ) ^ 13) ^ 3 / ((10 : ℝ) ^ 13) ^ 3 = 1 := by field_simp
    -- (e * S) / e^3 > (e^3 + 13924 * S) / e^3
    -- S / e^2 > 1 + 13924 * S / e^3
    field_simp [he.ne'] at hdiv
    have : (1 - (13924 : ℝ) / 10 ^ 13) * (1 + (6965 : ℝ) / 10 ^ 13) ^ 2 > 1 := by
      field_simp [he.ne']
      linarith
    have hcoe : (13924 : ℝ) / 10 ^ 13 = 2 * ε := by
      unfold ε
      field_simp
      norm_num
    rw [hcoe] at this
    exact this
  have hsq : (1 : ℝ) ^ 2 < (sqrt (1 - 2 * ε) * (1 + (6965 : ℝ) / 10 ^ 13)) ^ 2 := by
    calc
      (1 : ℝ) ^ 2 = 1 := by ring
      _ < (1 - 2 * ε) * (1 + (6965 : ℝ) / 10 ^ 13) ^ 2 := hmul
      _ = sqrt (1 - 2 * ε) ^ 2 * (1 + (6965 : ℝ) / 10 ^ 13) ^ 2 := by rw [sq_sqrt hpos.le]
      _ = (sqrt (1 - 2 * ε) * (1 + (6965 : ℝ) / 10 ^ 13)) ^ 2 := by ring
  have hx : 0 ≤ sqrt (1 - 2 * ε) * (1 + (6965 : ℝ) / 10 ^ 13) := by positivity
  have hgt : (1 : ℝ) < sqrt (1 - 2 * ε) * (1 + (6965 : ℝ) / 10 ^ 13) :=
    (sq_lt_sq₀ (by norm_num) hx).mp hsq
  have hs : 0 < sqrt (1 - 2 * ε) := sqrt_pos.mpr hpos
  have ht : 0 < 1 + (6965 : ℝ) / 10 ^ 13 := by norm_num
  have hsmall : 0 < 1 / (1 + (6965 : ℝ) / 10 ^ 13) := by positivity
  have hsqrt : 1 / (1 + (6965 : ℝ) / 10 ^ 13) < sqrt (1 - 2 * ε) := by
    rw [div_lt_iff₀ ht]
    exact hgt
  have hrec : (sqrt (1 - 2 * ε))⁻¹ < 1 + (6965 : ℝ) / 10 ^ 13 := by
    have hinv := (inv_lt_inv₀ hs hsmall).mpr hsqrt
    have hright : (1 / (1 + (6965 : ℝ) / 10 ^ 13))⁻¹ = 1 + (6965 : ℝ) / 10 ^ 13 := by
      field_simp
    rwa [hright] at hinv
  unfold centreAdvance
  rw [one_div]
  linarith

/-- `GM/(Rc²)` and the centre advance both round to `6.96×10⁻¹⁰`. The uniform
Newtonian centre rounds to a retardation of `3.48×10⁻¹⁰`, and the gap of the
two centre clocks rounds to `1.04×10⁻⁹`. -/
theorem earth_centre_bins :
    (6955 : ℝ) / 10 ^ 13 < (earthCompactnessQ : ℝ) ∧
      (earthCompactnessQ : ℝ) < (6965 : ℝ) / 10 ^ 13 ∧
      (6955 : ℝ) / 10 ^ 13 < centreAdvance (earthCompactnessQ : ℝ) ∧
        centreAdvance (earthCompactnessQ : ℝ) < (6965 : ℝ) / 10 ^ 13 ∧
      (3475 : ℝ) / 10 ^ 13 < (earthCompactnessQ : ℝ) / 2 ∧
        (earthCompactnessQ : ℝ) / 2 < (3485 : ℝ) / 10 ^ 13 ∧
      (1035 : ℝ) / 10 ^ 12 < (3 / 2 : ℝ) * earthCompactnessQ ∧
        (3 / 2 : ℝ) * earthCompactnessQ < (1045 : ℝ) / 10 ^ 12 := by
  have h1 : (6961 : ℝ) / 10 ^ 13 < (earthCompactnessQ : ℝ) := by
    have hQ : ((6961 : ℚ) / 10 ^ 13 : ℝ) < (earthCompactnessQ : ℝ) := by
      exact_mod_cast earthCompactnessQ_bounds.1
    simpa only [Nat.cast_ofNat, Rat.cast_ofNat] using hQ
  have h2 : (earthCompactnessQ : ℝ) < (6962 : ℝ) / 10 ^ 13 := by
    have hQ : (earthCompactnessQ : ℝ) < ((6962 : ℚ) / 10 ^ 13 : ℝ) := by
      exact_mod_cast earthCompactnessQ_bounds.2
    simpa only [Nat.cast_ofNat, Rat.cast_ofNat] using hQ
  have hhalf : (6962 : ℝ) / 10 ^ 13 < 1 / 2 := by norm_num
  have hpos : 0 < (earthCompactnessQ : ℝ) := lt_trans (by norm_num) h1
  have hmono : centreAdvance (earthCompactnessQ : ℝ) < centreAdvance ((6962 : ℝ) / 10 ^ 13) :=
    centreAdvance_mono hpos.le h2 hhalf
  have hgt : (earthCompactnessQ : ℝ) < centreAdvance (earthCompactnessQ : ℝ) :=
    centreAdvance_gt hpos (lt_trans h2 hhalf)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · linarith
  · linarith
  · linarith
  · linarith [centreAdvance_at_6962, hmono]
  · have hdiv : (6961 : ℝ) / 10 ^ 13 / 2 < (earthCompactnessQ : ℝ) / 2 :=
      div_lt_div_of_pos_right h1 (by norm_num)
    have hbin : (3475 : ℝ) / 10 ^ 13 < (6961 : ℝ) / 10 ^ 13 / 2 := by norm_num
    linarith
  · have hdiv : (earthCompactnessQ : ℝ) / 2 < (6962 : ℝ) / 10 ^ 13 / 2 :=
      div_lt_div_of_pos_right h2 (by norm_num)
    have hbin : (6962 : ℝ) / 10 ^ 13 / 2 < (3485 : ℝ) / 10 ^ 13 := by norm_num
    linarith
  · have hmul : (3 / 2 : ℝ) * ((6961 : ℝ) / 10 ^ 13) < (3 / 2 : ℝ) * earthCompactnessQ :=
      mul_lt_mul_of_pos_left h1 (by norm_num)
    have hbin : (1035 : ℝ) / 10 ^ 12 < (3 / 2 : ℝ) * ((6961 : ℝ) / 10 ^ 13) := by norm_num
    linarith
  · have hmul : (3 / 2 : ℝ) * earthCompactnessQ < (3 / 2 : ℝ) * ((6962 : ℝ) / 10 ^ 13) :=
      mul_lt_mul_of_pos_left h2 (by norm_num)
    have hbin : (3 / 2 : ℝ) * ((6962 : ℝ) / 10 ^ 13) < (1045 : ℝ) / 10 ^ 12 := by norm_num
    linarith

end

end InteriorClock

end Gravity

end DstDiophantine
