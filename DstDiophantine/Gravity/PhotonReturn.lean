import DstDiophantine.Gravity.EventBoundary
import DstDiophantine.Gravity.Schwarzschild
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Return of rays that a horizon would capture

## What this is

On the Schwarzschild chart a ray with impact parameter below the photon
sphere has no turning point. The Killing time down to `rₛ` diverges, and for
`r < rₛ` the factor `A` has changed sign, so the radial direction is timelike
and the ray cannot turn around.

The saturated chart freezes `A` at a positive floor before that sign change.
Every such ray then has a periapsis inside the freeze, and the Killing time
of the visit is finite.

## What is proved

* `4u³ - 27u + 27 = (2u - 3)² (u + 3)` for the dimensionless radius, so
  `r²/A` on `r > rₛ` is minimised at the photon sphere with value `b_c²`.
  A ray with `b < b_c` therefore has no turning point on the classical
  exterior.
* For `0 < r < rₛ` one has `A < 0`, and a negative factor admits no turning
  point of positive impact parameter. The saturated factor stays positive.
* On either recorded ceiling the freeze lies inside the photon sphere, and
  the periapsis `r = b √A` of every `0 < b < b_c` lies inside the freeze.
* `d/dr (r + rₛ log(r - rₛ)) = 1/A`. The same antiderivative is unbounded
  as `r ↓ rₛ` and finite from the freeze out to the photon sphere.
* Numerical brackets, in units of `GM/c³`, for the photon half-orbit, the
  cavity from the photon sphere down to the freeze, and the Killing time
  spent inside the freeze.

## Not claimed

* A mass on any nodal shell, or a magnification.
* That `F = k/(γₛ r²)` is the force on a ray.
* A boundary condition for a gravitational wave.
* Which of the two ceilings is the physical one.
-/

namespace DstDiophantine

namespace Gravity

open Real

/-! ### The photon sphere and the critical impact parameter -/

/-- Schwarzschild photon sphere `r_ph = (3/2) rₛ`. -/
noncomputable def photonSphere (rs : ℝ) : ℝ :=
  (3 / 2) * rs

/-- Critical impact parameter `b_c = (3 √3 / 2) rₛ`. -/
noncomputable def criticalImpact (rs : ℝ) : ℝ :=
  (3 * Real.sqrt 3 / 2) * rs

/-- One-axis saturation `A = e^{-π}`. -/
noncomputable def AOne : ℝ :=
  Real.exp (-Real.pi)

/-- One-axis radius ratio `r_★ / rₛ = 1/(1 - e^{-π})`. -/
noncomputable def radiusRatioOne : ℝ :=
  (1 - AOne)⁻¹

/-- Coordinate half-orbit of the photon sphere, in units of `GM/c³`. -/
noncomputable def photonHalfOrbit : ℝ :=
  3 * Real.pi * Real.sqrt 3

/-- Antiderivative of `1/A` on the classical exterior. -/
noncomputable def killingAntideriv (rs r : ℝ) : ℝ :=
  r + rs * Real.log (r - rs)

/-- Dimensionless round trip from the freeze out to the photon sphere.
In units where `rₛ = 2GM/c²`, this is `Δt` in units of `GM/c³`. -/
noncomputable def cavityFactor (A : ℝ) : ℝ :=
  4 * (3 / 2 - 1 / (1 - A) + Real.log ((1 - A) / (2 * A)))

/-- Radial null round trip from the freeze to the centre, in the same units. -/
noncomputable def interiorRadialFactor (A : ℝ) : ℝ :=
  4 / (A * (1 - A))

/-- Shortest interior round trip of a ray that has passed the photon sphere. -/
noncomputable def shallowInteriorFactor (A : ℝ) : ℝ :=
  4 * (1 / (1 - A) - (3 * Real.sqrt 3 / 2) * Real.sqrt A) / A

theorem criticalImpact_sq {rs : ℝ} : criticalImpact rs ^ 2 = (27 / 4) * rs ^ 2 := by
  unfold criticalImpact
  have hsq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  calc (3 * Real.sqrt 3 / 2 * rs) ^ 2
      = (9 * (Real.sqrt 3) ^ 2 / 4) * rs ^ 2 := by ring
    _ = (27 / 4) * rs ^ 2 := by rw [hsq]; ring

theorem criticalImpact_pos {rs : ℝ} (hrs : 0 < rs) : 0 < criticalImpact rs := by
  unfold criticalImpact
  positivity

theorem schwarzschildA_eq_div {rs r : ℝ} (hr : r ≠ 0) :
    schwarzschildA rs r = (r - rs) / r := by
  unfold schwarzschildA
  field_simp [hr]

/-! ### No classical turning point below `b_c` -/

theorem impactRatio_poly (u : ℝ) :
    4 * u ^ 3 - 27 * u + 27 = (2 * u - 3) ^ 2 * (u + 3) := by
  ring

theorem impactRatio_ge {u : ℝ} (hu : 1 < u) :
    (27 : ℝ) / 4 ≤ u ^ 3 / (u - 1) ∧
      (u ^ 3 / (u - 1) = 27 / 4 ↔ u = 3 / 2) := by
  have hpos : 0 < u - 1 := by linarith
  have hpoly := impactRatio_poly u
  have hfac : 0 ≤ (2 * u - 3) ^ 2 * (u + 3) := by
    have hsq : 0 ≤ (2 * u - 3) ^ 2 := sq_nonneg _
    have hlin : 0 < u + 3 := by linarith
    positivity
  have hge : 27 * (u - 1) ≤ 4 * u ^ 3 := by linarith
  constructor
  · rw [le_div_iff₀ hpos]
    linarith
  · constructor
    · intro heq
      have hmul : 4 * u ^ 3 = 27 * (u - 1) := by
        rw [div_eq_iff hpos.ne'] at heq
        linarith
      have hzero : (2 * u - 3) ^ 2 * (u + 3) = 0 := by linarith
      have hsum : u + 3 ≠ 0 := by linarith
      have hsq : (2 * u - 3) ^ 2 = 0 := by
        exact (mul_eq_zero.mp hzero).resolve_right hsum
      have : 2 * u - 3 = 0 := by nlinarith
      linarith
    · intro hu'
      subst hu'
      norm_num

/-- A ray from infinity with `b < b_c` does not turn on `r > rₛ`. -/
theorem no_exterior_turning {rs r b : ℝ} (hrs : 0 < rs) (hr : rs < r)
    (hb : 0 ≤ b) (hlt : b < criticalImpact rs) :
    b ^ 2 * schwarzschildA rs r < r ^ 2 := by
  have hA : 0 < schwarzschildA rs r := schwarzschildA_pos ⟨hrs, hr⟩
  have hu : 1 < r / rs := (one_lt_div hrs).mpr hr
  have hge := (impactRatio_ge hu).1
  have hr0 : r ≠ 0 := (hrs.trans hr).ne'
  have hrs0 : rs ≠ 0 := hrs.ne'
  have hAeq := schwarzschildA_eq_div (rs := rs) hr0
  have hform :
      r ^ 2 / schwarzschildA rs r =
        rs ^ 2 * ((r / rs) ^ 3 / (r / rs - 1)) := by
    rw [hAeq]
    field_simp [hrs0, hr0, (sub_pos.mpr hr).ne']
  have hmin : (27 / 4) * rs ^ 2 ≤ r ^ 2 / schwarzschildA rs r := by
    rw [hform, mul_comm]
    exact mul_le_mul_of_nonneg_left hge (sq_nonneg rs)
  have hb_sq : b ^ 2 < criticalImpact rs ^ 2 := by
    simpa [pow_two] using
      (mul_self_lt_mul_self_iff hb (criticalImpact_pos hrs).le).mp hlt
  have hbc : b ^ 2 < (27 / 4) * rs ^ 2 := by
    rwa [criticalImpact_sq] at hb_sq
  have hlt_div : b ^ 2 < r ^ 2 / schwarzschildA rs r := hbc.trans_le hmin
  rwa [lt_div_iff₀ hA] at hlt_div

/-! ### The classical interior has changed sign -/

theorem schwarzschildA_neg_of_interior {rs r : ℝ}
    (_hrs : 0 < rs) (hr0 : 0 < r) (hr : r < rs) :
    schwarzschildA rs r < 0 := by
  unfold schwarzschildA
  have : rs / r > 1 := (one_lt_div hr0).mpr hr
  linarith

/-- A negative redshift admits no turning point of positive impact parameter. -/
theorem no_turning_of_neg_A {A b r : ℝ} (hA : A < 0) (hb : 0 < b) :
    b ^ 2 ≠ r ^ 2 / A := by
  intro h
  have hle : r ^ 2 / A ≤ 0 := div_nonpos_of_nonneg_of_nonpos (sq_nonneg r) hA.le
  have hpos : 0 < b ^ 2 := by positivity
  linarith

/-- Below `rₛ` the classical factor is negative, while the saturated chart
is still the positive floor. -/
theorem interior_sign_contrast {rs r : ℝ}
    (hrs : 0 < rs) (hr0 : 0 < r) (hr : r < rs) :
    schwarzschildA rs r < 0 ∧ 0 < saturatedA rs r := by
  refine ⟨schwarzschildA_neg_of_interior hrs hr0 hr, ?_⟩
  have hle : r ≤ eventBoundaryRadius rs :=
    le_of_lt (hr.trans (rs_lt_eventBoundaryRadius hrs))
  simpa [saturatedA_of_le hle] using AMin_pos

/-! ### Both ceilings lie inside the photon sphere, and the ray turns there -/

private theorem sqrt_three_lt_two : Real.sqrt 3 < 2 :=
  (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)

private theorem exp_series_three :
    (∑ m ∈ Finset.range 3, (1 : ℝ) ^ m / m.factorial) = 5 / 2 := by
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_zero]
  simp only [Nat.factorial_zero, Nat.factorial_succ, Nat.cast_one, pow_zero, pow_one,
    zero_add]
  norm_num

private theorem two_lt_exp_one : (2 : ℝ) < Real.exp 1 := by
  have hle := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1) 3
  linarith [exp_series_three]

private theorem exp_series_eight :
    (∑ m ∈ Finset.range 8, (1 : ℝ) ^ m / m.factorial) = 685 / 252 := by
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
  simp only [Nat.factorial_zero, Nat.factorial_succ, Nat.cast_one, pow_zero, pow_one,
    zero_add]
  norm_num

private theorem exp_one_gt_series : (685 : ℝ) / 252 < Real.exp 1 := by
  have hle := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1) 9
  have hsplit :
      (∑ m ∈ Finset.range 9, (1 : ℝ) ^ m / m.factorial) =
        685 / 252 + (1 : ℝ) ^ 8 / Nat.factorial 8 := by
    rw [Finset.sum_range_succ, exp_series_eight]
  have hpos : (0 : ℝ) < (1 : ℝ) ^ 8 / Nat.factorial 8 := by positivity
  linarith

private theorem exp_three_gt_twenty : (20 : ℝ) < Real.exp 3 := by
  have hpow : ((685 : ℝ) / 252) ^ 3 < Real.exp 1 ^ 3 :=
    pow_lt_pow_left₀ exp_one_gt_series (by positivity) (by decide : (3 : ℕ) ≠ 0)
  have hexp : Real.exp 1 ^ 3 = Real.exp 3 := by
    rw [← Real.exp_nat_mul]
    norm_num
  have hrat : (20 : ℝ) < ((685 : ℝ) / 252) ^ 3 := by norm_num
  linarith

theorem AOne_pos : (0 : ℝ) < AOne :=
  Real.exp_pos _

theorem AOne_lt_one : AOne < 1 := by
  unfold AOne
  rw [← Real.exp_zero]
  exact Real.exp_lt_exp.mpr (neg_neg_of_pos Real.pi_pos)

theorem AOne_lt_one_div_twenty : AOne < (1 : ℝ) / 20 := by
  have hπ : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hlt : AOne < Real.exp (-3) := by
    unfold AOne
    exact Real.exp_lt_exp.mpr (neg_lt_neg hπ)
  have h20 : Real.exp (-3) < (1 : ℝ) / 20 := by
    have h := exp_three_gt_twenty
    rw [Real.exp_neg]
    have hinv : (Real.exp 3)⁻¹ < (20 : ℝ)⁻¹ :=
      (inv_lt_inv₀ (Real.exp_pos _) (by norm_num)).mpr h
    simpa [one_div] using hinv
  exact hlt.trans h20

theorem radiusRatioOne_pos : (0 : ℝ) < radiusRatioOne := by
  unfold radiusRatioOne
  exact inv_pos.mpr (sub_pos.mpr AOne_lt_one)

theorem radiusRatioOne_lt_photon : radiusRatioOne < 3 / 2 := by
  have hA := AOne_lt_one_div_twenty
  have hden : (19 : ℝ) / 20 < 1 - AOne := by linarith
  have hinv : (1 - AOne)⁻¹ < ((19 : ℝ) / 20)⁻¹ :=
    (inv_lt_inv₀ (sub_pos.mpr AOne_lt_one) (by norm_num)).mpr hden
  have hsimp : ((19 : ℝ) / 20)⁻¹ = 20 / 19 := by norm_num
  have hlt : (20 : ℝ) / 19 < 3 / 2 := by norm_num
  unfold radiusRatioOne
  linarith

theorem threeAxis_freeze_below_photon {rs : ℝ} (hrs : 0 < rs) :
    eventBoundaryRadius rs < photonSphere rs := by
  unfold eventBoundaryRadius photonSphere
  have hratio : radiusRatio < 3 / 2 := by
    have h := radiusRatio_bounds.2
    linarith
  rw [mul_comm (3 / 2) rs]
  exact mul_lt_mul_of_pos_left hratio hrs

theorem oneAxis_freeze_below_photon {rs : ℝ} (hrs : 0 < rs) :
    rs * radiusRatioOne < photonSphere rs := by
  unfold photonSphere
  rw [mul_comm (3 / 2) rs]
  exact mul_lt_mul_of_pos_left radiusRatioOne_lt_photon hrs

theorem sqrt_AMin_lt_tenth : Real.sqrt AMin < (1 : ℝ) / 10 := by
  have hsqrt : Real.sqrt AMin < Real.sqrt ((1 : ℝ) / 100) :=
    Real.sqrt_lt_sqrt AMin_pos.le AMin_bounds.2
  have hten : Real.sqrt ((1 : ℝ) / 100) = 1 / 10 := by
    rw [one_div, Real.sqrt_inv,
      show (100 : ℝ) = 10 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    norm_num
  linarith

theorem sqrt_AOne_lt_quarter : Real.sqrt AOne < (1 : ℝ) / 4 := by
  have hA : AOne < ((1 : ℝ) / 4) ^ 2 := by
    have h := AOne_lt_one_div_twenty
    norm_num
    linarith
  exact (Real.sqrt_lt' (by norm_num)).mpr hA

/-- Marginal periapsis of the three-axis floor, strictly inside the freeze. -/
theorem threeAxis_cut_inside {rs : ℝ} (hrs : 0 < rs) :
    criticalImpact rs * Real.sqrt AMin < eventBoundaryRadius rs := by
  have hsqrt : Real.sqrt AMin < (1 : ℝ) / 10 := sqrt_AMin_lt_tenth
  have hk : 3 * Real.sqrt 3 / 2 < 3 := by
    have h3 := sqrt_three_lt_two
    linarith
  have hprod : (3 * Real.sqrt 3 / 2) * Real.sqrt AMin < (3 : ℝ) / 10 := by
    have hpos : 0 < 3 * Real.sqrt 3 / 2 := by positivity
    calc (3 * Real.sqrt 3 / 2) * Real.sqrt AMin
        < (3 * Real.sqrt 3 / 2) * (1 / 10) := by gcongr
      _ < 3 * (1 / 10) := by gcongr
      _ = 3 / 10 := by ring
  unfold criticalImpact eventBoundaryRadius
  have hrr : (1 : ℝ) < radiusRatio := one_lt_radiusRatio
  have hlt : (3 * Real.sqrt 3 / 2) * Real.sqrt AMin < radiusRatio := by
    have : (3 : ℝ) / 10 < 1 := by norm_num
    linarith
  have hcomm : (3 * Real.sqrt 3 / 2) * rs * Real.sqrt AMin =
      rs * ((3 * Real.sqrt 3 / 2) * Real.sqrt AMin) := by ring
  rw [hcomm]
  exact mul_lt_mul_of_pos_left hlt hrs

/-- Marginal periapsis of the one-axis floor, strictly inside the freeze. -/
theorem oneAxis_cut_inside {rs : ℝ} (hrs : 0 < rs) :
    criticalImpact rs * Real.sqrt AOne < rs * radiusRatioOne := by
  have hsqrt := sqrt_AOne_lt_quarter
  have hk : 3 * Real.sqrt 3 / 2 < 4 := by
    have h3 := sqrt_three_lt_two
    linarith
  have hprod : (3 * Real.sqrt 3 / 2) * Real.sqrt AOne < 1 := by
    calc (3 * Real.sqrt 3 / 2) * Real.sqrt AOne
        < (3 * Real.sqrt 3 / 2) * (1 / 4) := by gcongr
      _ < 4 * (1 / 4) := by gcongr
      _ = 1 := by norm_num
  have hrr : (1 : ℝ) < radiusRatioOne := by
    unfold radiusRatioOne
    rw [one_lt_inv_iff₀]
    exact ⟨sub_pos.mpr AOne_lt_one, sub_lt_self _ AOne_pos⟩
  have hlt : (3 * Real.sqrt 3 / 2) * Real.sqrt AOne < radiusRatioOne := by linarith
  have hassoc : criticalImpact rs * Real.sqrt AOne =
      rs * ((3 * Real.sqrt 3 / 2) * Real.sqrt AOne) := by
    unfold criticalImpact
    ring
  rw [hassoc]
  exact mul_lt_mul_of_pos_left hlt hrs

theorem periapsis_sq {b A : ℝ} (hA : 0 ≤ A) :
    (b * Real.sqrt A) ^ 2 = b ^ 2 * A := by
  rw [mul_pow, Real.sq_sqrt hA]

/-- Every subcritical ray turns inside the freeze, and nowhere on `r > rₛ`. -/
theorem penetrating_turns_inside {rs A b : ℝ}
    (hrs : 0 < rs) (hA : 0 < A) (hA1 : A < 1)
    (hstar : rs / (1 - A) < photonSphere rs)
    (hcut : criticalImpact rs * Real.sqrt A < rs / (1 - A))
    (hb0 : 0 < b) (hb : b < criticalImpact rs) :
    let rPeri := b * Real.sqrt A
    0 < rPeri ∧ rPeri < rs / (1 - A) ∧
      ∀ r, rs < r → b ^ 2 * schwarzschildA rs r < r ^ 2 := by
  intro rPeri
  have _ : 0 < 1 - A := sub_pos.mpr hA1
  have _ := hstar
  have hs : 0 < Real.sqrt A := Real.sqrt_pos.mpr hA
  refine ⟨mul_pos hb0 hs, ?_, ?_⟩
  · exact (mul_lt_mul_of_pos_right hb hs).trans hcut
  · intro r hr
    exact no_exterior_turning hrs hr hb0.le hb

theorem penetrating_turns_inside_threeAxis {rs b : ℝ}
    (hrs : 0 < rs) (hb0 : 0 < b) (hb : b < criticalImpact rs) :
    let rPeri := b * Real.sqrt AMin
    0 < rPeri ∧ rPeri < eventBoundaryRadius rs ∧
      ∀ r, rs < r → b ^ 2 * schwarzschildA rs r < r ^ 2 := by
  have hstar := threeAxis_freeze_below_photon hrs
  have hcut := threeAxis_cut_inside hrs
  have hA := AMin_pos
  have hA1 := AMin_lt_one
  have hradius : eventBoundaryRadius rs = rs / (1 - AMin) := by
    unfold eventBoundaryRadius radiusRatio
    rw [div_eq_mul_inv]
  have hturn := penetrating_turns_inside hrs hA hA1
    (by simpa [hradius] using hstar) (by simpa [hradius] using hcut) hb0 hb
  simpa [hradius] using hturn

theorem penetrating_turns_inside_oneAxis {rs b : ℝ}
    (hrs : 0 < rs) (hb0 : 0 < b) (hb : b < criticalImpact rs) :
    let rPeri := b * Real.sqrt AOne
    0 < rPeri ∧ rPeri < rs * radiusRatioOne ∧
      ∀ r, rs < r → b ^ 2 * schwarzschildA rs r < r ^ 2 := by
  have hradius : rs * radiusRatioOne = rs / (1 - AOne) := by
    unfold radiusRatioOne
    rw [div_eq_mul_inv]
  have hturn := penetrating_turns_inside hrs AOne_pos AOne_lt_one
    (by simpa [hradius] using oneAxis_freeze_below_photon hrs)
    (by simpa [hradius] using oneAxis_cut_inside hrs) hb0 hb
  simpa [hradius] using hturn

/-! ### Killing time -/

theorem hasDerivAt_killingAntideriv {rs r : ℝ} (hrs : 0 < rs) (hr : rs < r) :
    HasDerivAt (killingAntideriv rs) (1 / schwarzschildA rs r) r := by
  have hsub : HasDerivAt (fun x => x - rs) (1 : ℝ) r :=
    (hasDerivAt_id r).sub_const rs
  have hne : r - rs ≠ 0 := sub_ne_zero.mpr hr.ne'
  have hlog : HasDerivAt (fun x => Real.log (x - rs)) (1 / (r - rs)) r := by
    simpa using hsub.log hne
  have h := (hasDerivAt_id r).add (hlog.const_mul rs)
  have hr0 : r ≠ 0 := (hrs.trans hr).ne'
  refine h.congr_deriv ?_
  rw [schwarzschildA_eq_div hr0]
  field_simp [hr.ne', hr0]
  ring

theorem killing_gap_eq {rs r₁ r₂ : ℝ} (_hrs : 0 < rs) (h₁ : rs < r₁) (h₂ : rs < r₂) :
    killingAntideriv rs r₂ - killingAntideriv rs r₁ =
      (r₂ - r₁) + rs * Real.log ((r₂ - rs) / (r₁ - rs)) := by
  have h1 : 0 < r₁ - rs := by linarith
  have h2 : 0 < r₂ - rs := by linarith
  unfold killingAntideriv
  rw [Real.log_div h2.ne' h1.ne']
  ring

theorem cavityFactor_eq_killing {rs A : ℝ}
    (hrs : 0 < rs) (hA : 0 < A) (hA1 : A < 1)
    (hstar : rs < rs / (1 - A)) (hph : rs / (1 - A) < photonSphere rs) :
    4 / rs * (killingAntideriv rs (photonSphere rs) -
        killingAntideriv rs (rs / (1 - A))) =
      cavityFactor A := by
  have hrstar : rs < rs / (1 - A) := hstar
  have hrph : rs < photonSphere rs := hstar.trans hph
  have hgap := killing_gap_eq hrs hrstar hrph
  have hden : 1 - A ≠ 0 := (sub_pos.mpr hA1).ne'
  have hrph_sub : photonSphere rs - rs = rs / 2 := by
    unfold photonSphere
    ring
  have hrstar_sub : rs / (1 - A) - rs = rs * A / (1 - A) := by
    field_simp [hden, hrs.ne']
    ring
  have hlog_arg :
      (photonSphere rs - rs) / (rs / (1 - A) - rs) = (1 - A) / (2 * A) := by
    rw [hrph_sub, hrstar_sub]
    field_simp [hrs.ne', hA.ne', hden]
  have hdiff : photonSphere rs - rs / (1 - A) =
      rs * (3 / 2 - 1 / (1 - A)) := by
    unfold photonSphere
    field_simp [hden, hrs.ne']
  unfold cavityFactor
  rw [hgap, hdiff, hlog_arg]
  field_simp [hrs.ne']

/-- The classical antiderivative is unbounded as the horizon is approached,
so there is no finite Killing time in which a radial ray reaches `rₛ`. -/
theorem exists_classical_delay_gt {rs T : ℝ} (hrs : 0 < rs) :
    ∃ r, rs < r ∧ r < photonSphere rs ∧
      T < killingAntideriv rs (photonSphere rs) - killingAntideriv rs r := by
  have hlog2 : Real.log 2 < 1 := by
    have : Real.exp (Real.log 2) < Real.exp 1 := by
      rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      exact two_lt_exp_one
    exact Real.exp_lt_exp.mp this
  by_cases hT : T < 0
  · refine ⟨(5 / 4) * rs, ?_, ?_, ?_⟩
    · linarith
    · unfold photonSphere
      linarith
    · have hgap := killing_gap_eq hrs (by linarith : rs < (5 / 4) * rs)
        (by unfold photonSphere; linarith : rs < photonSphere rs)
      have hpos_span : 0 < photonSphere rs - (5 / 4) * rs := by
        unfold photonSphere
        linarith
      have hlogpos : 0 < Real.log ((photonSphere rs - rs) / ((5 / 4) * rs - rs)) := by
        have harg : (photonSphere rs - rs) / ((5 / 4) * rs - rs) = 2 := by
          have hph : photonSphere rs = (3 / 2) * rs := rfl
          rw [hph]
          have h1 : (3 / 2) * rs - rs = rs / 2 := by ring
          have h2 : (5 / 4) * rs - rs = rs / 4 := by ring
          rw [h1, h2]
          field_simp [hrs.ne']
          norm_num
        rw [harg]
        exact Real.log_pos (by norm_num)
      have : 0 < killingAntideriv rs (photonSphere rs) -
          killingAntideriv rs ((5 / 4) * rs) := by
        rw [hgap]
        positivity
      linarith
  · push Not at hT
    let δ : ℝ := rs * Real.exp (-(T / rs) - 1)
    have hδ : 0 < δ := by
      unfold δ
      positivity
    have hexp : Real.exp (-1) < 1 / 2 := by
      rw [Real.exp_neg]
      have hinv : (Real.exp 1)⁻¹ < (2 : ℝ)⁻¹ :=
        (inv_lt_inv₀ (Real.exp_pos _) (by norm_num)).mpr two_lt_exp_one
      simpa [one_div] using hinv
    have hδlt : δ < rs / 2 := by
      unfold δ
      have hle : Real.exp (-(T / rs) - 1) ≤ Real.exp (-1) := by
        refine Real.exp_le_exp.mpr ?_
        have : 0 ≤ T / rs := div_nonneg hT hrs.le
        linarith
      have hmul : rs * Real.exp (-(T / rs) - 1) ≤ rs * Real.exp (-1) :=
        mul_le_mul_of_nonneg_left hle hrs.le
      have hstrict : rs * Real.exp (-1) < rs * (1 / 2) :=
        mul_lt_mul_of_pos_left hexp hrs
      linarith
    refine ⟨rs + δ, by linarith, ?_, ?_⟩
    · unfold photonSphere
      linarith
    · have hr : rs < rs + δ := by linarith
      have hrph : rs < photonSphere rs := by
        unfold photonSphere
        linarith
      have hgap := killing_gap_eq hrs hr hrph
      have hratio : (photonSphere rs - rs) / δ = (1 / 2) * Real.exp (T / rs + 1) := by
        have hph : photonSphere rs - rs = rs / 2 := by
          unfold photonSphere
          ring
        have hδeq : δ = rs * Real.exp (-(T / rs + 1)) := by
          unfold δ
          rw [show -(T / rs) - 1 = -(T / rs + 1) by ring]
        rw [hph, hδeq, Real.exp_neg]
        field_simp [hrs.ne', (Real.exp_pos (T / rs + 1)).ne']
      have hlog : Real.log ((photonSphere rs - rs) / δ) =
          -Real.log 2 + T / rs + 1 := by
        rw [hratio, Real.log_mul (by norm_num) (by positivity), Real.log_exp,
          Real.log_div (by norm_num) (by norm_num), Real.log_one]
        ring
      have hrewrite : killingAntideriv rs (photonSphere rs) -
          killingAntideriv rs (rs + δ) =
          T + rs * (3 / 2 - Real.log 2) - δ := by
        have hsubr : (rs + δ) - rs = δ := by ring
        rw [hgap, hsubr, hlog]
        unfold photonSphere
        field_simp [hrs.ne']
        ring
      rw [hrewrite]
      have hhalf : (1 : ℝ) / 2 < 3 / 2 - Real.log 2 := by linarith
      have hmul : rs * (1 / 2) < rs * (3 / 2 - Real.log 2) :=
        mul_lt_mul_of_pos_left hhalf hrs
      have hδbig : δ < rs * (3 / 2 - Real.log 2) := by
        have : rs * (1 / 2) = rs / 2 := by ring
        linarith
      exact lt_of_lt_of_eq (lt_add_of_pos_right T (sub_pos.mpr hδbig))
        (by ring : T + (rs * (3 / 2 - Real.log 2) - δ) =
          T + rs * (3 / 2 - Real.log 2) - δ)

/-! ### Photon half-orbit -/

theorem photon_A {rs : ℝ} (hrs : 0 < rs) :
    schwarzschildA rs (photonSphere rs) = 1 / 3 := by
  unfold schwarzschildA photonSphere
  field_simp [hrs.ne']
  ring

theorem photon_omega {rs : ℝ} (hrs : 0 < rs) :
    schwarzschildA rs (photonSphere rs) * criticalImpact rs /
        (photonSphere rs) ^ 2 =
      2 / (3 * Real.sqrt 3 * rs) := by
  rw [photon_A hrs]
  unfold criticalImpact photonSphere
  have hsq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h3 : Real.sqrt 3 ≠ 0 := by positivity
  field_simp [hrs.ne', h3]
  nlinarith [hsq, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]

theorem photonHalfOrbit_eq {rs : ℝ} (hrs : 0 < rs) :
    Real.pi / (schwarzschildA rs (photonSphere rs) * criticalImpact rs /
        (photonSphere rs) ^ 2) =
      photonHalfOrbit * (rs / 2) := by
  rw [photon_omega hrs]
  unfold photonHalfOrbit
  have h3 : Real.sqrt 3 ≠ 0 := by positivity
  field_simp [hrs.ne', h3]

/-! ### The interior visit outlasts a photon half-orbit -/

private theorem pi_lt_315 : Real.pi < (315 : ℝ) / 100 := by
  have h := Real.pi_lt_d2
  norm_num at h ⊢
  exact h

private theorem pi_gt_314 : (314 : ℝ) / 100 < Real.pi := by
  have h := Real.pi_gt_d2
  norm_num at h ⊢
  exact h

private theorem sqrt_three_lt_174 : Real.sqrt 3 < (174 : ℝ) / 100 :=
  (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)

private theorem sqrt_three_gt_173 : (173 : ℝ) / 100 < Real.sqrt 3 :=
  Real.lt_sqrt_of_sq_lt (by norm_num)

theorem photonHalfOrbit_bounds : (16 : ℝ) < photonHalfOrbit ∧ photonHalfOrbit < 17 := by
  unfold photonHalfOrbit
  constructor
  · nlinarith [pi_gt_314, sqrt_three_gt_173]
  · have hmul : Real.pi * Real.sqrt 3 < (315 : ℝ) / 100 * (174 / 100) :=
      mul_lt_mul pi_lt_315 sqrt_three_lt_174.le
        (Real.sqrt_pos.mpr (by norm_num)) (by positivity)
    have h3 : 3 * (Real.pi * Real.sqrt 3) <
        3 * ((315 : ℝ) / 100 * (174 / 100)) :=
      mul_lt_mul_of_pos_left hmul (by norm_num)
    have hnum : 3 * ((315 : ℝ) / 100 * (174 / 100)) < 17 := by norm_num
    linarith

theorem interiorRadial_oneAxis_gt : (80 : ℝ) < interiorRadialFactor AOne := by
  have hprod : AOne * (1 - AOne) < (1 : ℝ) / 20 := by
    have hlt : AOne * (1 - AOne) < AOne := by
      nlinarith [AOne_pos, AOne_lt_one]
    exact hlt.trans AOne_lt_one_div_twenty
  unfold interiorRadialFactor
  have hden : 0 < AOne * (1 - AOne) := by
    nlinarith [AOne_pos, AOne_lt_one]
  rw [lt_div_iff₀ hden]
  nlinarith

theorem interiorRadial_threeAxis_gt : (400 : ℝ) < interiorRadialFactor AMin := by
  have hprod : AMin * (1 - AMin) < (1 : ℝ) / 100 := by
    have hlt : AMin * (1 - AMin) < AMin := by
      nlinarith [AMin_pos, AMin_lt_one]
    exact hlt.trans AMin_bounds.2
  unfold interiorRadialFactor
  have hden : 0 < AMin * (1 - AMin) := by
    nlinarith [AMin_pos, AMin_lt_one]
  rw [lt_div_iff₀ hden]
  nlinarith

theorem shallowInterior_oneAxis_gt : (20 : ℝ) < shallowInteriorFactor AOne := by
  have hinv : (1 : ℝ) < 1 / (1 - AOne) := by
    rw [one_lt_div (sub_pos.mpr AOne_lt_one)]
    linarith [AOne_pos]
  have hsub : (3 * Real.sqrt 3 / 2) * Real.sqrt AOne < (3 : ℝ) / 4 := by
    have hk : 3 * Real.sqrt 3 / 2 < 3 := by linarith [sqrt_three_lt_two]
    have hs : 0 < Real.sqrt AOne := Real.sqrt_pos.mpr AOne_pos
    have h1 : (3 * Real.sqrt 3 / 2) * Real.sqrt AOne < 3 * Real.sqrt AOne :=
      mul_lt_mul_of_pos_right hk hs
    have h2 : 3 * Real.sqrt AOne < 3 * (1 / 4) :=
      mul_lt_mul_of_pos_left sqrt_AOne_lt_quarter (by norm_num)
    linarith
  have hdiff : (1 : ℝ) / 4 <
      1 / (1 - AOne) - (3 * Real.sqrt 3 / 2) * Real.sqrt AOne := by
    linarith
  have hscale : (20 : ℝ) * AOne <
      4 * (1 / (1 - AOne) - (3 * Real.sqrt 3 / 2) * Real.sqrt AOne) := by
    nlinarith [AOne_lt_one_div_twenty, hdiff]
  unfold shallowInteriorFactor
  rw [lt_div_iff₀ AOne_pos]
  exact hscale

theorem shallowInterior_threeAxis_gt : (280 : ℝ) < shallowInteriorFactor AMin := by
  have hinv : (1 : ℝ) < 1 / (1 - AMin) := by
    rw [one_lt_div (sub_pos.mpr AMin_lt_one)]
    linarith [AMin_pos]
  have hsub : (3 * Real.sqrt 3 / 2) * Real.sqrt AMin < (3 : ℝ) / 10 := by
    have hk : 3 * Real.sqrt 3 / 2 < 3 := by linarith [sqrt_three_lt_two]
    have hs : 0 < Real.sqrt AMin := Real.sqrt_pos.mpr AMin_pos
    have h1 : (3 * Real.sqrt 3 / 2) * Real.sqrt AMin < 3 * Real.sqrt AMin :=
      mul_lt_mul_of_pos_right hk hs
    have h2 : 3 * Real.sqrt AMin < 3 * (1 / 10) :=
      mul_lt_mul_of_pos_left sqrt_AMin_lt_tenth (by norm_num)
    linarith
  have hdiff : (7 : ℝ) / 10 <
      1 / (1 - AMin) - (3 * Real.sqrt 3 / 2) * Real.sqrt AMin := by
    linarith
  have hscale : (280 : ℝ) * AMin <
      4 * (1 / (1 - AMin) - (3 * Real.sqrt 3 / 2) * Real.sqrt AMin) := by
    nlinarith [AMin_bounds.2, hdiff]
  unfold shallowInteriorFactor
  rw [lt_div_iff₀ AMin_pos]
  exact hscale

theorem interior_outlasts_half_orbit :
    photonHalfOrbit < shallowInteriorFactor AOne ∧
      photonHalfOrbit < shallowInteriorFactor AMin := by
  have hhalf := photonHalfOrbit_bounds.2
  refine ⟨?_, ?_⟩
  · linarith [shallowInterior_oneAxis_gt]
  · linarith [shallowInterior_threeAxis_gt]

end Gravity

end DstDiophantine
