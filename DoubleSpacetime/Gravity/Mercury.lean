import DoubleSpacetime.Gravity.Perihelion
import DoubleSpacetime.Gravity.SI
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option linter.style.native false

/-!
# Mercury perihelion advance from the exterior radial return

External orbital elements and SI stand-ins feed `Perihelion.radialReturn`. The excess over `2π`,
times Mercury's revolutions per Julian century, lies in `(42, 44)` arcseconds. No claim is made
about planetary perturbations, solar quadrupole, or an observational residual.
-/

namespace DoubleSpacetime

namespace Gravity

namespace Mercury

open Real SI Perihelion

/-! ### External elements -/

/-- External semi-major axis of Mercury, in metres. -/
def semiMajor : ℚ := 57909050000

/-- External eccentricity of Mercury. -/
def eccentricity : ℚ := 205630 / 1000000

/-- External sidereal period of Mercury, in days. -/
def periodDays : ℚ := 879691 / 10000

/-- Days in a Julian century. -/
def julianCenturyDays : ℚ := 36525

/-- Orbits of Mercury in one Julian century. -/
def revsPerCentury : ℚ := julianCenturyDays / periodDays

/-- Solar geometric mass `GM/c²`, in metres, from the SI stand-ins. -/
def solarGeometricMass : ℚ :=
  GApprox * solarMassApprox / speedOfLight ^ 2

/-- Semi-latus rectum `a(1-e²)`. -/
def semiLatus : ℚ := semiMajor * (1 - eccentricity ^ 2)

/-- Reciprocal aphelion radius. Smaller turning value of the radial return. -/
noncomputable def alpha : ℝ :=
  1 / ((semiMajor : ℝ) * (1 + (eccentricity : ℝ)))

/-- Reciprocal perihelion radius. Larger turning value of the radial return. -/
noncomputable def beta : ℝ :=
  1 / ((semiMajor : ℝ) * (1 - (eccentricity : ℝ)))

/-- Advance from `radialReturn`, in arcseconds per Julian century. -/
noncomputable def arcsecPerCentury : ℝ :=
  (radialReturn (solarGeometricMass : ℝ) alpha beta - 2 * Real.pi) *
    (revsPerCentury : ℝ) * (648000 / Real.pi)

/-! ### Explicit numerators -/

def solarGeometricMass_num : ℕ := 667430 * 198847 * 10 ^ 9

def oneMinusEsq_num : ℕ := 10 ^ 12 - 205630 ^ 2

def semiLatus_num : ℕ := 57909050000 * oneMinusEsq_num

def semiLatus_den : ℕ := 10 ^ 12

def revs_num : ℕ := 365250000

def revs_den : ℕ := 879691

theorem solarGeometricMass_eq_num_div_den :
    solarGeometricMass =
      (solarGeometricMass_num : ℚ) / (speedOfLightNat : ℚ) ^ 2 := by
  unfold solarGeometricMass GApprox solarMassApprox GMantissa GScale
    solarMassMantissa solarMassScale speedOfLight solarGeometricMass_num
  field_simp
  ring

theorem semiLatus_eq_num_div_den :
    semiLatus = (semiLatus_num : ℚ) / semiLatus_den := by
  unfold semiLatus semiMajor eccentricity semiLatus_num semiLatus_den oneMinusEsq_num
  field_simp
  ring

theorem revsPerCentury_eq_num_div_den :
    revsPerCentury = (revs_num : ℚ) / revs_den := by
  unfold revsPerCentury julianCenturyDays periodDays revs_num revs_den
  norm_num

theorem solarGeometricMass_pos : (0 : ℚ) < solarGeometricMass := by
  rw [solarGeometricMass_eq_num_div_den]
  unfold solarGeometricMass_num speedOfLightNat
  norm_num

theorem semiMajor_pos : (0 : ℚ) < semiMajor := by
  unfold semiMajor; norm_num

theorem eccentricity_bounds : (0 : ℚ) < eccentricity ∧ eccentricity < 1 := by
  unfold eccentricity; norm_num

theorem semiLatus_pos : (0 : ℚ) < semiLatus := by
  rw [semiLatus_eq_num_div_den]
  unfold semiLatus_num semiLatus_den oneMinusEsq_num
  norm_num

theorem revsPerCentury_pos : (0 : ℚ) < revsPerCentury := by
  rw [revsPerCentury_eq_num_div_den]
  unfold revs_num revs_den
  norm_num

private theorem semiLatus_coe :
    (semiLatus : ℝ) = (semiMajor : ℝ) * (1 - (eccentricity : ℝ) ^ 2) := by
  unfold semiLatus
  push_cast
  ring

theorem alpha_add_beta :
    alpha + beta = 2 / (semiLatus : ℝ) := by
  have ha : (0 : ℝ) < (semiMajor : ℝ) := by exact_mod_cast semiMajor_pos
  have he0 : (0 : ℝ) < (eccentricity : ℝ) := by exact_mod_cast eccentricity_bounds.1
  have he1 : (eccentricity : ℝ) < 1 := by exact_mod_cast eccentricity_bounds.2
  have hp : (0 : ℝ) < 1 + (eccentricity : ℝ) := by linarith
  have hm : (0 : ℝ) < 1 - (eccentricity : ℝ) := by linarith
  have hsq : (0 : ℝ) < 1 - (eccentricity : ℝ) ^ 2 := by nlinarith
  rw [semiLatus_coe]
  unfold alpha beta
  field_simp [ha.ne', hp.ne', hm.ne', hsq.ne']
  ring

private theorem alpha_nonneg : (0 : ℝ) ≤ alpha := by
  have ha : (0 : ℝ) < (semiMajor : ℝ) := by exact_mod_cast semiMajor_pos
  have he0 : (0 : ℝ) < (eccentricity : ℝ) := by exact_mod_cast eccentricity_bounds.1
  have hp : (0 : ℝ) < 1 + (eccentricity : ℝ) := by linarith
  unfold alpha
  positivity

private theorem alpha_lt_beta : alpha < beta := by
  have ha : (0 : ℝ) < (semiMajor : ℝ) := by exact_mod_cast semiMajor_pos
  have he0 : (0 : ℝ) < (eccentricity : ℝ) := by exact_mod_cast eccentricity_bounds.1
  have he1 : (eccentricity : ℝ) < 1 := by exact_mod_cast eccentricity_bounds.2
  have hp : (0 : ℝ) < 1 + (eccentricity : ℝ) := by linarith
  have hm : (0 : ℝ) < 1 - (eccentricity : ℝ) := by linarith
  unfold alpha beta
  refine (div_lt_div_iff₀ (mul_pos ha hp) (mul_pos ha hm)).mpr ?_
  nlinarith

/-! ### Hypotheses for `bound_return_bounds` -/

private theorem twelve_M_le_p :
    (12 : ℚ) * solarGeometricMass ≤ semiLatus := by
  rw [solarGeometricMass_eq_num_div_den, semiLatus_eq_num_div_den]
  have hdenM : (0 : ℚ) < (speedOfLightNat : ℚ) ^ 2 := by
    unfold speedOfLightNat; norm_num
  have hdenP : (0 : ℚ) < (semiLatus_den : ℚ) := by
    unfold semiLatus_den; norm_num
  have hmul :
      (12 : ℚ) * ((solarGeometricMass_num : ℚ) / (speedOfLightNat : ℚ) ^ 2) =
        (12 * solarGeometricMass_num : ℚ) / (speedOfLightNat : ℚ) ^ 2 := by
    ring
  rw [hmul, div_le_div_iff₀ hdenM hdenP]
  have hnat :
      (12 : ℕ) * solarGeometricMass_num * semiLatus_den ≤
        semiLatus_num * speedOfLightNat ^ 2 := by
    unfold solarGeometricMass_num semiLatus_num semiLatus_den oneMinusEsq_num
      speedOfLightNat
    native_decide
  exact_mod_cast hnat

theorem turning_half_le :
    (3 : ℝ) * (solarGeometricMass : ℝ) * (alpha + beta) ≤ 1 / 2 := by
  have hs : (0 : ℝ) < (semiLatus : ℝ) := by exact_mod_cast semiLatus_pos
  rw [alpha_add_beta]
  have hrat : (6 : ℚ) * solarGeometricMass / semiLatus ≤ 1 / 2 := by
    have h12 := twelve_M_le_p
    have h6 : (6 : ℚ) * solarGeometricMass ≤ semiLatus / 2 := by linarith
    exact (div_le_iff₀ semiLatus_pos).mpr (by linarith [h6])
  have hrew :
      (3 : ℝ) * (solarGeometricMass : ℝ) * (2 / (semiLatus : ℝ)) =
        (6 : ℝ) * (solarGeometricMass : ℝ) / (semiLatus : ℝ) := by
    field_simp [hs.ne']
    ring
  rw [hrew]
  have hratR :
      (6 : ℝ) * (solarGeometricMass : ℝ) / (semiLatus : ℝ) ≤ (1 / 2 : ℝ) := by
    have h : ((6 * solarGeometricMass / semiLatus : ℚ) : ℝ) ≤ ((1 / 2 : ℚ) : ℝ) :=
      Rat.cast_le.mpr hrat
    convert h using 1
    · push_cast; ring
    · norm_num
  exact hratR

/-- Third cubic root completing `α + β + γ = 1/(2M)`. -/
noncomputable def gamma : ℝ :=
  1 / (2 * (solarGeometricMass : ℝ)) - alpha - beta

private theorem two_M_three_e_lt_p :
    (2 : ℚ) * solarGeometricMass * (3 + eccentricity) < semiLatus := by
  rw [solarGeometricMass_eq_num_div_den, semiLatus_eq_num_div_den]
  unfold eccentricity
  have hdenM : (0 : ℚ) < (speedOfLightNat : ℚ) ^ 2 := by
    unfold speedOfLightNat; norm_num
  have hdenP : (0 : ℚ) < (semiLatus_den : ℚ) := by
    unfold semiLatus_den; norm_num
  have h6 : (0 : ℚ) < (10 : ℚ) ^ 6 := by norm_num
  have hnat :
      (2 : ℕ) * solarGeometricMass_num * (3 * 10 ^ 6 + 205630) * semiLatus_den <
        semiLatus_num * speedOfLightNat ^ 2 * 10 ^ 6 := by
    unfold solarGeometricMass_num semiLatus_num semiLatus_den oneMinusEsq_num
      speedOfLightNat
    native_decide
  have hcast :
      (2 : ℚ) * solarGeometricMass_num * (3 * 10 ^ 6 + 205630) * semiLatus_den <
        (semiLatus_num : ℚ) * (speedOfLightNat : ℚ) ^ 2 * 10 ^ 6 := by
    exact_mod_cast hnat
  have he :
      (3 : ℚ) + 205630 / 1000000 = (3 * 10 ^ 6 + 205630 : ℚ) / (10 : ℚ) ^ 6 := by
    norm_num
  rw [he]
  have hleft :
      (2 : ℚ) * ((solarGeometricMass_num : ℚ) / (speedOfLightNat : ℚ) ^ 2) *
          ((3 * 10 ^ 6 + 205630 : ℚ) / (10 : ℚ) ^ 6) =
        ((2 : ℚ) * solarGeometricMass_num * (3 * 10 ^ 6 + 205630)) /
          ((speedOfLightNat : ℚ) ^ 2 * (10 : ℚ) ^ 6) := by
    field_simp
  rw [hleft, div_lt_div_iff₀ (mul_pos hdenM h6) hdenP]
  simpa [mul_assoc, mul_left_comm, mul_comm] using hcast

private theorem beta_lt_gamma : beta < gamma := by
  unfold gamma
  have ha : (0 : ℝ) < (semiMajor : ℝ) := by exact_mod_cast semiMajor_pos
  have he0 : (0 : ℝ) < (eccentricity : ℝ) := by exact_mod_cast eccentricity_bounds.1
  have he1 : (eccentricity : ℝ) < 1 := by exact_mod_cast eccentricity_bounds.2
  have hp : (0 : ℝ) < 1 + (eccentricity : ℝ) := by linarith
  have hm : (0 : ℝ) < 1 - (eccentricity : ℝ) := by linarith
  have hform :
      alpha + 2 * beta =
        ((3 : ℝ) + (eccentricity : ℝ)) / (semiLatus : ℝ) := by
    unfold alpha beta
    calc
      1 / ((semiMajor : ℝ) * (1 + eccentricity)) +
            2 * (1 / (semiMajor * (1 - eccentricity))) =
          ((1 - eccentricity) + 2 * (1 + eccentricity)) /
            (semiMajor * (1 + eccentricity) * (1 - eccentricity)) := by
        field_simp [ha.ne', hp.ne', hm.ne']
      _ = (3 + eccentricity) / (semiMajor * (1 - eccentricity ^ 2)) := by
        ring
      _ = (3 + eccentricity) / (semiLatus : ℝ) := by
        rw [semiLatus_coe]
  have hgoal : alpha + 2 * beta < 1 / (2 * (solarGeometricMass : ℝ)) := by
    rw [hform]
    have hrat : ((3 : ℚ) + eccentricity) / semiLatus <
        1 / (2 * solarGeometricMass) := by
      have hMp : (0 : ℚ) < 2 * solarGeometricMass :=
        mul_pos (by norm_num) solarGeometricMass_pos
      rw [div_lt_div_iff₀ semiLatus_pos hMp]
      linarith [two_M_three_e_lt_p]
    exact_mod_cast hrat
  linarith

private theorem gamma_sum :
    alpha + beta + gamma = 1 / (2 * (solarGeometricMass : ℝ)) := by
  unfold gamma
  ring

/-! ### Arcsecond conversion -/

/-- Leading GR lower bound in arcseconds per century (`π` cancels). -/
noncomputable def leadingArcsec : ℝ :=
  (6 : ℝ) * (solarGeometricMass : ℝ) / (semiLatus : ℝ) *
    (revsPerCentury : ℝ) * 648000

/-- Envelope upper bound in arcseconds per century. -/
noncomputable def envelopeArcsec : ℝ :=
  leadingArcsec / (1 - 6 * (solarGeometricMass : ℝ) / (semiLatus : ℝ))

private theorem leading_eq_rad_times_factor :
    (6 * Real.pi * (solarGeometricMass : ℝ) / (semiLatus : ℝ)) *
        ((revsPerCentury : ℝ) * (648000 / Real.pi)) =
      leadingArcsec := by
  unfold leadingArcsec
  have hs : (semiLatus : ℝ) ≠ 0 := by exact_mod_cast semiLatus_pos.ne'
  field_simp [Real.pi_ne_zero, hs]

private theorem envelope_eq_rad_times_factor
    (hx : 6 * (solarGeometricMass : ℝ) / (semiLatus : ℝ) < 1) :
    ((6 * Real.pi * (solarGeometricMass : ℝ) / (semiLatus : ℝ)) /
          (1 - 6 * (solarGeometricMass : ℝ) / (semiLatus : ℝ))) *
        ((revsPerCentury : ℝ) * (648000 / Real.pi)) =
      envelopeArcsec := by
  unfold envelopeArcsec leadingArcsec
  have hs : (semiLatus : ℝ) ≠ 0 := by exact_mod_cast semiLatus_pos.ne'
  have h1x : 1 - 6 * (solarGeometricMass : ℝ) / (semiLatus : ℝ) ≠ 0 :=
    ne_of_gt (sub_pos.mpr hx)
  field_simp [Real.pi_ne_zero, hs, h1x]

private theorem factor_pos :
    (0 : ℝ) < (revsPerCentury : ℝ) * (648000 / Real.pi) := by
  have hr : (0 : ℝ) < (revsPerCentury : ℝ) := by exact_mod_cast revsPerCentury_pos
  positivity

private theorem six_M_over_p_lt_one :
    (6 : ℝ) * (solarGeometricMass : ℝ) / (semiLatus : ℝ) < 1 := by
  have hs : (0 : ℝ) < (semiLatus : ℝ) := by exact_mod_cast semiLatus_pos
  have h := turning_half_le
  have hrew :
      (3 : ℝ) * (solarGeometricMass : ℝ) * (alpha + beta) =
        6 * (solarGeometricMass : ℝ) / (semiLatus : ℝ) := by
    rw [alpha_add_beta]
    field_simp [hs.ne']
    ring
  have hle : 6 * (solarGeometricMass : ℝ) / (semiLatus : ℝ) ≤ 1 / 2 := by
    simpa [hrew] using h
  exact lt_of_le_of_lt hle (by norm_num)

private theorem forty_two_lt_leading_Q :
    (42 : ℚ) < 6 * solarGeometricMass / semiLatus * revsPerCentury * 648000 := by
  have hrew :
      (6 : ℚ) * solarGeometricMass / semiLatus * revsPerCentury * 648000 =
        (6 * solarGeometricMass * revsPerCentury * 648000) / semiLatus := by
    field_simp [semiLatus_pos.ne']
  rw [hrew, lt_div_iff₀ semiLatus_pos]
  -- 42 * p < 6 * M * revs * 648000  ↔  7 * p < M * revs * 648000
  have htarget : (42 : ℚ) * semiLatus <
      6 * solarGeometricMass * revsPerCentury * 648000 := by
    rw [solarGeometricMass_eq_num_div_den, semiLatus_eq_num_div_den,
      revsPerCentury_eq_num_div_den]
    have hdenM : (0 : ℚ) < (speedOfLightNat : ℚ) ^ 2 := by
      unfold speedOfLightNat; norm_num
    have hdenP : (0 : ℚ) < (semiLatus_den : ℚ) := by
      unfold semiLatus_den; norm_num
    have hdenR : (0 : ℚ) < (revs_den : ℚ) := by
      unfold revs_den; norm_num
    have hnat :
        (7 : ℕ) * semiLatus_num * speedOfLightNat ^ 2 * revs_den <
          solarGeometricMass_num * revs_num * 648000 * semiLatus_den := by
      unfold solarGeometricMass_num semiLatus_num semiLatus_den oneMinusEsq_num
        revs_num revs_den speedOfLightNat
      native_decide
    have hcast :
        (7 : ℚ) * semiLatus_num * (speedOfLightNat : ℚ) ^ 2 * revs_den <
          (solarGeometricMass_num : ℚ) * revs_num * 648000 * semiLatus_den := by
      exact_mod_cast hnat
    have hleft :
        (42 : ℚ) * ((semiLatus_num : ℚ) / semiLatus_den) =
          (42 * semiLatus_num : ℚ) / semiLatus_den := by
      ring
    have hright :
        (6 : ℚ) * ((solarGeometricMass_num : ℚ) / (speedOfLightNat : ℚ) ^ 2) *
            ((revs_num : ℚ) / revs_den) * 648000 =
          (6 * solarGeometricMass_num * revs_num * 648000 : ℚ) /
            ((speedOfLightNat : ℚ) ^ 2 * revs_den) := by
      field_simp
    rw [hleft, hright, div_lt_div_iff₀ hdenP (mul_pos hdenM hdenR)]
    -- goal: 42 * P_n * (c² * R_d) < 6 * M_n * R_n * 648000 * P_d
    have h6 := mul_lt_mul_of_pos_left hcast (by norm_num : (0 : ℚ) < 6)
    -- h6: 6*(7*P_n*c²*R_d) < 6*(M_n*R_n*648000*P_d)
    simpa [show (42 : ℚ) = 6 * 7 by norm_num, mul_assoc, mul_left_comm, mul_comm]
      using h6
  exact htarget

private theorem forty_two_lt_leading : (42 : ℝ) < leadingArcsec := by
  unfold leadingArcsec
  exact_mod_cast forty_two_lt_leading_Q

private theorem envelope_lt_forty_four_Q :
    (6 : ℚ) * solarGeometricMass / semiLatus * revsPerCentury * 648000 /
      (1 - 6 * solarGeometricMass / semiLatus) < 44 := by
  set Mq : ℚ := solarGeometricMass
  set pq : ℚ := semiLatus
  set rq : ℚ := revsPerCentury
  have hMpos : (0 : ℚ) < Mq := by simpa [Mq] using solarGeometricMass_pos
  have hppos : (0 : ℚ) < pq := by simpa [pq] using semiLatus_pos
  have hxQ : (6 : ℚ) * Mq / pq < 1 := by
    have h12 : (12 : ℚ) * Mq ≤ pq := by simpa [Mq, pq] using twelve_M_le_p
    have h6 : (6 : ℚ) * Mq ≤ pq / 2 := by linarith
    have hhalf : (6 : ℚ) * Mq / pq ≤ 1 / 2 := (div_le_iff₀ hppos).mpr (by linarith)
    exact lt_of_le_of_lt hhalf (by norm_num)
  have hdenpos : (0 : ℚ) < 1 - 6 * Mq / pq := sub_pos.mpr hxQ
  -- M * (3 * revs * 648000 + 132) < 22 * p
  have hcoeff : solarGeometricMass * (3 * revsPerCentury * 648000 + 132) <
      22 * semiLatus := by
    rw [solarGeometricMass_eq_num_div_den, semiLatus_eq_num_div_den,
      revsPerCentury_eq_num_div_den]
    have hdenM : (0 : ℚ) < (speedOfLightNat : ℚ) ^ 2 := by
      unfold speedOfLightNat; norm_num
    have hdenP : (0 : ℚ) < (semiLatus_den : ℚ) := by
      unfold semiLatus_den; norm_num
    have hdenR : (0 : ℚ) < (revs_den : ℚ) := by
      unfold revs_den; norm_num
    have hnat :
        solarGeometricMass_num * (3 * revs_num * 648000 + 132 * revs_den) *
            semiLatus_den <
          22 * semiLatus_num * speedOfLightNat ^ 2 * revs_den := by
      unfold solarGeometricMass_num semiLatus_num semiLatus_den oneMinusEsq_num
        revs_num revs_den speedOfLightNat
      native_decide
    have hcast :
        (solarGeometricMass_num : ℚ) *
            (3 * revs_num * 648000 + 132 * revs_den) * semiLatus_den <
          (22 : ℚ) * semiLatus_num * (speedOfLightNat : ℚ) ^ 2 * revs_den := by
      exact_mod_cast hnat
    have hleft :
        ((solarGeometricMass_num : ℚ) / (speedOfLightNat : ℚ) ^ 2) *
            (3 * ((revs_num : ℚ) / revs_den) * 648000 + 132) =
          (solarGeometricMass_num * (3 * revs_num * 648000 + 132 * revs_den) : ℚ) /
            ((speedOfLightNat : ℚ) ^ 2 * revs_den) := by
      field_simp
    have hright :
        (22 : ℚ) * ((semiLatus_num : ℚ) / semiLatus_den) =
          (22 * semiLatus_num : ℚ) / semiLatus_den := by
      ring
    rw [hleft, hright, div_lt_div_iff₀ (mul_pos hdenM hdenR) hdenP]
    simpa [mul_assoc, mul_left_comm, mul_comm] using hcast
  have hcoeff' : Mq * (3 * rq * 648000 + 132) < 22 * pq := by
    simpa [Mq, pq, rq] using hcoeff
  have hclear : (6 : ℚ) * Mq * rq * 648000 < 44 * (pq - 6 * Mq) := by
    have : (3 : ℚ) * Mq * rq * 648000 + 132 * Mq < 22 * pq := by
      simpa [mul_add, add_mul, mul_assoc, mul_left_comm, mul_comm] using hcoeff'
    linarith
  have hrew :
      (6 : ℚ) * Mq / pq * rq * 648000 / (1 - 6 * Mq / pq) =
        (6 * Mq * rq * 648000) / (pq - 6 * Mq) := by
    have hp6 : pq - 6 * Mq = pq * (1 - 6 * Mq / pq) := by
      field_simp [hppos.ne']
    rw [hp6]
    field_simp [hppos.ne', hdenpos.ne']
  rw [hrew]
  have hp6pos : (0 : ℚ) < pq - 6 * Mq := by
    have : (0 : ℚ) < pq * (1 - 6 * Mq / pq) := mul_pos hppos hdenpos
    have hp6 : pq - 6 * Mq = pq * (1 - 6 * Mq / pq) := by
      field_simp [hppos.ne']
    rwa [← hp6] at this
  exact (div_lt_iff₀ hp6pos).mpr hclear

private theorem envelope_lt_forty_four : envelopeArcsec < 44 := by
  unfold envelopeArcsec leadingArcsec
  exact_mod_cast envelope_lt_forty_four_Q

/-! ### Main bound -/

theorem return_excess_bounds :
    let M := (solarGeometricMass : ℝ)
    let p := 2 / (alpha + beta)
    6 * Real.pi * M / p < radialReturn M alpha beta - 2 * Real.pi ∧
      radialReturn M alpha beta - 2 * Real.pi <
        (6 * Real.pi * M / p) / (1 - 6 * M / p) := by
  have hM : (0 : ℝ) < (solarGeometricMass : ℝ) := by exact_mod_cast solarGeometricMass_pos
  exact bound_return_bounds hM alpha_nonneg alpha_lt_beta beta_lt_gamma gamma_sum
    turning_half_le

theorem perihelion_arcsec_bounds :
    42 < arcsecPerCentury ∧ arcsecPerCentury < 44 := by
  have hs : (0 : ℝ) < (semiLatus : ℝ) := by exact_mod_cast semiLatus_pos
  have hp : (2 : ℝ) / (alpha + beta) = (semiLatus : ℝ) := by
    rw [alpha_add_beta]
    field_simp [hs.ne']
  have hb := return_excess_bounds
  dsimp at hb
  rw [hp] at hb
  set M : ℝ := (solarGeometricMass : ℝ)
  set excess : ℝ := radialReturn M alpha beta - 2 * Real.pi
  set fac : ℝ := (revsPerCentury : ℝ) * (648000 / Real.pi)
  have hfac : (0 : ℝ) < fac := by simpa [fac] using factor_pos
  have hx1 := six_M_over_p_lt_one
  have hlo : leadingArcsec < excess * fac := by
    have hmul := mul_lt_mul_of_pos_right hb.1 hfac
    have hL :
        (6 * Real.pi * M / (semiLatus : ℝ)) * fac = leadingArcsec := by
      simpa [M, fac] using leading_eq_rad_times_factor
    rwa [hL] at hmul
  have hhi : excess * fac < envelopeArcsec := by
    have hmul := mul_lt_mul_of_pos_right hb.2 hfac
    have hU :
        ((6 * Real.pi * M / (semiLatus : ℝ)) /
            (1 - 6 * M / (semiLatus : ℝ))) * fac =
          envelopeArcsec := by
      simpa [M, fac] using envelope_eq_rad_times_factor hx1
    rwa [hU] at hmul
  have harc : arcsecPerCentury = excess * fac := by
    unfold arcsecPerCentury excess fac M
    ring
  rw [harc]
  exact ⟨lt_trans forty_two_lt_leading hlo, lt_trans hhi envelope_lt_forty_four⟩

end Mercury

end Gravity

end DoubleSpacetime
