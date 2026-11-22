import DstDiophantine.Gravity.Mercury
import DstDiophantine.Gravity.Schwarzschild
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option linter.style.native false

/-!
# Solar deflection on the exterior null orbit

A null ray that turns at radius `R` outside the photon sphere has azimuthal excess
`deflection M R` over `π`. The excess lies strictly above the classical term `4M/R` and strictly
below that term divided by `(1 - 3M/R)^{3/2}`.

For the nominal solar radius and the same SI stand-ins as Mercury, the excess lies in
`(17/10, 9/5)` arcseconds. No eclipse residual, solar quadrupole, or plasma delay is claimed.
`Lensing.interiorDeflection` is not this angle.
-/

namespace DstDiophantine

namespace Gravity

namespace SolarDeflection

open Real Set intervalIntegral MeasureTheory Mercury SI

/-! ### The null polynomial -/

/-- Schwarzschild null orbit polynomial at reciprocal turning value `u0`. `rs` is the
Schwarzschild radius. -/
noncomputable def nullSlope (rs u0 u : ℝ) : ℝ :=
  (u0 ^ 2 - u ^ 2) - rs * (u0 ^ 3 - u ^ 3)

/-- Null energy residual: the timelike `binetResidual` with the rest-mass `1` removed. -/
noncomputable def nullResidual (E rs L u : ℝ) : ℝ :=
  E ^ 2 - (1 - rs * u) * L ^ 2 * u ^ 2

theorem schwarzschildA_reciprocal {rs u : ℝ} (_hu : u ≠ 0) :
    schwarzschildA rs u⁻¹ = 1 - rs * u := by
  unfold schwarzschildA
  rw [div_eq_mul_inv, inv_inv]

theorem nullResidual_eq_slope {E rs L u0 u : ℝ}
    (hE : E ^ 2 = (1 - rs * u0) * L ^ 2 * u0 ^ 2) :
    nullResidual E rs L u = L ^ 2 * nullSlope rs u0 u := by
  unfold nullResidual nullSlope
  rw [hE]
  ring

/-- Turning radius outside the photon sphere `3M`, written on the exterior chart `rs = 2M`. -/
theorem turning_exterior {M R : ℝ} (hM : 0 < M) (hph : 3 * M < R) :
    IsExterior (2 * M) R :=
  ⟨by linarith, by linarith⟩

/-! ### Shape of the substituted radicand -/

/-- Weight `(1 + s + s²) / (1 + s)` left after cancelling the cosine zero at periapsis. -/
noncomputable def nullShape (s : ℝ) : ℝ :=
  (1 + s + s ^ 2) / (1 + s)

theorem nullShape_add {s : ℝ} (hs : s ≠ -1) : nullShape s = s + (1 + s)⁻¹ := by
  have hden : 1 + s ≠ 0 := by
    intro h
    exact hs (by linarith)
  unfold nullShape
  rw [div_eq_mul_inv]
  calc
    (1 + s + s ^ 2) * (1 + s)⁻¹ = (s * (1 + s) + 1) * (1 + s)⁻¹ := by ring
    _ = s * ((1 + s) * (1 + s)⁻¹) + (1 + s)⁻¹ := by ring
    _ = s * 1 + (1 + s)⁻¹ := by rw [mul_inv_cancel₀ hden]
    _ = s + (1 + s)⁻¹ := by ring

theorem nullShape_bounds {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    1 ≤ nullShape s ∧ nullShape s ≤ 3 / 2 := by
  have hden : (0 : ℝ) < 1 + s := by linarith
  constructor
  · unfold nullShape
    refine (le_div_iff₀ hden).mpr ?_
    nlinarith [sq_nonneg s]
  · unfold nullShape
    refine (div_le_iff₀ hden).mpr ?_
    nlinarith [sq_nonneg s]

theorem nullSlope_sin {rs u0 ψ : ℝ} (hs : Real.sin ψ ≠ -1) :
    nullSlope rs u0 (u0 * Real.sin ψ) =
      u0 ^ 2 * Real.cos ψ ^ 2 * (1 - rs * u0 * nullShape (Real.sin ψ)) := by
  have hpyth : Real.cos ψ ^ 2 = 1 - Real.sin ψ ^ 2 := by
    have h := Real.sin_sq_add_cos_sq ψ
    linarith
  unfold nullSlope nullShape
  rw [hpyth]
  have hden : 1 + Real.sin ψ ≠ 0 := by
    intro h
    apply hs
    linarith
  field_simp [hden]
  ring

theorem continuousOn_nullShape : ContinuousOn nullShape (Icc 0 1) := by
  unfold nullShape
  refine ContinuousOn.div ?_ ?_ ?_
  · exact ((continuous_const.add continuous_id).add (continuous_id.pow 2)).continuousOn
  · exact (continuous_const.add continuous_id).continuousOn
  · intro s hs
    exact (by linarith [hs.1] : (0 : ℝ) < 1 + s).ne'

theorem continuousOn_nullShape_sin :
    ContinuousOn (fun ψ => nullShape (Real.sin ψ)) (Icc 0 (Real.pi / 2)) := by
  refine continuousOn_nullShape.comp continuous_sin.continuousOn ?_
  intro ψ hψ
  exact ⟨sin_nonneg_of_mem_Icc ⟨hψ.1, hψ.2.trans (by linarith [Real.pi_pos])⟩,
    Real.sin_le_one ψ⟩

/-! ### The azimuthal excess -/

/-- Integrand of the azimuth after `u = u0 sin ψ`, with `ε = M/R`. -/
noncomputable def nullIntegrand (ε ψ : ℝ) : ℝ :=
  1 / Real.sqrt (1 - 2 * ε * nullShape (Real.sin ψ))

/-- Azimuth from one asymptote to the other. -/
noncomputable def nullAzimuth (M R : ℝ) : ℝ :=
  2 * ∫ ψ in (0 : ℝ)..Real.pi / 2, nullIntegrand (M / R) ψ

/-- Excess of that azimuth over the flat angle `π`. -/
noncomputable def deflection (M R : ℝ) : ℝ :=
  nullAzimuth M R - Real.pi

theorem nullIntegrand_zero (ψ : ℝ) : nullIntegrand 0 ψ = 1 := by
  unfold nullIntegrand
  simp [Real.sqrt_one]

theorem nullAzimuth_zero (R : ℝ) : nullAzimuth 0 R = Real.pi := by
  unfold nullAzimuth
  simp only [div_eq_mul_inv, zero_mul, nullIntegrand_zero]
  rw [intervalIntegral.integral_const, smul_eq_mul]
  ring

theorem continuousOn_nullIntegrand {ε : ℝ} (hε0 : 0 ≤ ε) (hε : 3 * ε < 1) :
    ContinuousOn (nullIntegrand ε) (Icc 0 (Real.pi / 2)) := by
  unfold nullIntegrand
  refine ContinuousOn.div continuousOn_const ?_ ?_
  · refine ContinuousOn.sqrt ?_
    refine ContinuousOn.sub continuousOn_const ?_
    refine ContinuousOn.mul continuousOn_const continuousOn_nullShape_sin
  · intro ψ hψ
    have hsin0 : 0 ≤ Real.sin ψ :=
      sin_nonneg_of_mem_Icc ⟨hψ.1, hψ.2.trans (by linarith [Real.pi_pos])⟩
    have hsin1 : Real.sin ψ ≤ 1 := Real.sin_le_one ψ
    have hshape := nullShape_bounds hsin0 hsin1
    have hle : 2 * ε * nullShape (Real.sin ψ) ≤ 3 * ε := by
      have hmul : 2 * ε * nullShape (Real.sin ψ) ≤ 2 * ε * (3 / 2) := by
        refine mul_le_mul_of_nonneg_left hshape.2 ?_
        positivity
      linarith
    have hrad : 0 < 1 - 2 * ε * nullShape (Real.sin ψ) := by linarith
    exact (Real.sqrt_pos.mpr hrad).ne'

/-! ### Square-root bounds -/

private theorem sqrt_turn {x : ℝ} (hx1 : x < 1) :
    0 < Real.sqrt (1 - x) ∧ Real.sqrt (1 - x) ^ 2 = 1 - x := by
  have h1x : 0 < 1 - x := by linarith
  exact ⟨Real.sqrt_pos.mpr h1x, Real.sq_sqrt h1x.le⟩

theorem inv_sqrt_lower {x : ℝ} (_hx0 : 0 ≤ x) (hx1 : x < 1) :
    1 + x / 2 ≤ 1 / Real.sqrt (1 - x) := by
  obtain ⟨hy0, hy2⟩ := sqrt_turn hx1
  set y : ℝ := Real.sqrt (1 - x)
  have hxeq : x = 1 - y ^ 2 := by linarith
  rw [hxeq]
  have hdiff :
      1 / y - (1 + (1 - y ^ 2) / 2) = (1 - y) ^ 2 * (2 + y) / (2 * y) := by
    field_simp [hy0.ne']
    ring
  have hnonneg : 0 ≤ (1 - y) ^ 2 * (2 + y) / (2 * y) := by positivity
  linarith

theorem inv_sqrt_lower_strict {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    1 + x / 2 < 1 / Real.sqrt (1 - x) := by
  obtain ⟨hy0, hy2⟩ := sqrt_turn hx1
  set y : ℝ := Real.sqrt (1 - x)
  have hy1 : y < 1 := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_lt_sqrt (by linarith) (by linarith)
  have hxeq : x = 1 - y ^ 2 := by linarith
  rw [hxeq]
  have hdiff :
      1 / y - (1 + (1 - y ^ 2) / 2) = (1 - y) ^ 2 * (2 + y) / (2 * y) := by
    field_simp [hy0.ne']
    ring
  have hpos : 0 < (1 - y) ^ 2 * (2 + y) / (2 * y) := by positivity
  linarith

theorem inv_sqrt_upper {x : ℝ} (_hx0 : 0 ≤ x) (hx1 : x < 1) :
    1 / Real.sqrt (1 - x) ≤ 1 + (x / 2) / Real.sqrt (1 - x) ^ 3 := by
  obtain ⟨hy0, hy2⟩ := sqrt_turn hx1
  set y : ℝ := Real.sqrt (1 - x)
  have hxeq : x = 1 - y ^ 2 := by linarith
  rw [hxeq]
  have hdiff :
      (1 + ((1 - y ^ 2) / 2) / y ^ 3) - 1 / y =
        (1 - y) ^ 2 * (1 + 2 * y) / (2 * y ^ 3) := by
    field_simp [hy0.ne']
    ring
  have hnonneg : 0 ≤ (1 - y) ^ 2 * (1 + 2 * y) / (2 * y ^ 3) := by positivity
  linarith

theorem inv_sqrt_upper_strict {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    1 / Real.sqrt (1 - x) < 1 + (x / 2) / Real.sqrt (1 - x) ^ 3 := by
  obtain ⟨hy0, hy2⟩ := sqrt_turn hx1
  set y : ℝ := Real.sqrt (1 - x)
  have hy1 : y < 1 := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_lt_sqrt (by linarith) (by linarith)
  have hxeq : x = 1 - y ^ 2 := by linarith
  rw [hxeq]
  have hdiff :
      (1 + ((1 - y ^ 2) / 2) / y ^ 3) - 1 / y =
        (1 - y) ^ 2 * (1 + 2 * y) / (2 * y ^ 3) := by
    field_simp [hy0.ne']
    ring
  have hpos : 0 < (1 - y) ^ 2 * (1 + 2 * y) / (2 * y ^ 3) := by positivity
  linarith

/-- `(1 - x)^{-3/2} < 1 + 2x` on `0 < x ≤ 1/10`. -/
theorem inv_sqrt_cube_lt {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1 / 10) :
    1 / Real.sqrt (1 - x) ^ 3 < 1 + 2 * x := by
  have hx1' : x < 1 := by linarith
  obtain ⟨hy0, hy2⟩ := sqrt_turn hx1'
  set y : ℝ := Real.sqrt (1 - x)
  have hy2_ge : 9 / 10 ≤ y ^ 2 := by
    rw [hy2]
    linarith
  have hy_ge : Real.sqrt (9 / 10) ≤ y := by
    rw [← Real.sqrt_sq hy0.le]
    exact Real.sqrt_le_sqrt hy2_ge
  have hy1 : y < 1 := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_lt_sqrt (by linarith) (by linarith)
  have hfactor :
      3 * y ^ 3 - 2 * y ^ 5 - 1 =
        (1 - y) * ((2 * y ^ 2 - 1) * (y ^ 2 + y) - 1) := by
    ring
  have hquad : 0 < (2 * y ^ 2 - 1) * (y ^ 2 + y) - 1 := by
    have hcoef : 4 / 5 ≤ 2 * y ^ 2 - 1 := by linarith
    have hsum : 9 / 10 + Real.sqrt (9 / 10) ≤ y ^ 2 + y := by linarith
    have hprod :
        (4 / 5) * (9 / 10 + Real.sqrt (9 / 10)) ≤ (2 * y ^ 2 - 1) * (y ^ 2 + y) := by
      refine mul_le_mul hcoef hsum ?_ ?_
      · positivity
      · positivity
    have hgt : (1 : ℝ) < (4 / 5) * (9 / 10 + Real.sqrt (9 / 10)) := by
      have hsqrt : 7 / 20 < Real.sqrt (9 / 10) :=
        Real.lt_sqrt_of_sq_lt (by norm_num)
      nlinarith
    linarith
  have hpoly : 0 < 3 * y ^ 3 - 2 * y ^ 5 - 1 := by
    rw [hfactor]
    have h1y : 0 < 1 - y := by linarith
    positivity
  have hrew : 3 * y ^ 3 - 2 * y ^ 5 = y ^ 3 * (1 + 2 * x) := by
    have hxeq : x = 1 - y ^ 2 := by linarith
    rw [hxeq]
    ring
  have hy3 : 0 < y ^ 3 := by positivity
  have hlt : 1 < y ^ 3 * (1 + 2 * x) := by linarith
  rw [div_lt_iff₀ hy3]
  simpa [mul_comm] using hlt

theorem three_halves_eq_sqrt_pow {y : ℝ} (hy : 0 ≤ y) :
    y ^ (3 / 2 : ℝ) = Real.sqrt y ^ 3 := by
  rw [Real.sqrt_eq_rpow]
  have hsplit : (3 / 2 : ℝ) = (1 / 2) * (3 : ℕ) := by norm_num
  rw [hsplit, Real.rpow_mul hy, Real.rpow_natCast]

/-! ### Integral of the shape -/

private theorem cos_quarter_sub_sq (ψ : ℝ) :
    Real.cos (Real.pi / 4 - ψ / 2) ^ 2 = (1 + Real.sin ψ) / 2 := by
  rw [Real.cos_sub, Real.cos_pi_div_four, Real.sin_pi_div_four]
  have hfac :
      Real.sqrt 2 / 2 * Real.cos (ψ / 2) + Real.sqrt 2 / 2 * Real.sin (ψ / 2) =
        Real.sqrt 2 / 2 * (Real.cos (ψ / 2) + Real.sin (ψ / 2)) := by
    ring
  rw [hfac, mul_pow]
  have hsqrt : (Real.sqrt 2 / 2) ^ 2 = 1 / 2 := by
    rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  rw [hsqrt]
  have hadd : (Real.cos (ψ / 2) + Real.sin (ψ / 2)) ^ 2 = 1 + Real.sin ψ := by
    have hdouble : Real.sin ψ = 2 * Real.sin (ψ / 2) * Real.cos (ψ / 2) := by
      rw [← Real.sin_two_mul]
      congr 1
      ring
    calc
      (Real.cos (ψ / 2) + Real.sin (ψ / 2)) ^ 2
          = Real.cos (ψ / 2) ^ 2 + Real.sin (ψ / 2) ^ 2 +
              2 * Real.cos (ψ / 2) * Real.sin (ψ / 2) := by ring
      _ = 1 + Real.sin ψ := by
          rw [Real.cos_sq_add_sin_sq]
          have hcomm : 2 * Real.cos (ψ / 2) * Real.sin (ψ / 2) = Real.sin ψ := by
            linarith [hdouble]
          rw [hcomm]
  rw [hadd]
  ring

private theorem hasDerivAt_inv_one_add_sin (ψ : ℝ) (h0 : 0 ≤ ψ) (h1 : ψ ≤ Real.pi / 2) :
    HasDerivAt (fun t => -Real.tan (Real.pi / 4 - t / 2)) ((1 + Real.sin ψ)⁻¹) ψ := by
  have hcos_pos : 0 < Real.cos (Real.pi / 4 - ψ / 2) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hlin : HasDerivAt (fun t => Real.pi / 4 - t / 2) (-(1 / 2 : ℝ)) ψ := by
    have hhalf : HasDerivAt (fun t => t / 2) ((1 : ℝ) / 2) ψ :=
      (hasDerivAt_id ψ).div_const 2
    simpa using hhalf.const_sub (Real.pi / 4)
  have htan := (Real.hasDerivAt_tan hcos_pos.ne').comp ψ hlin
  have hneg := htan.neg
  refine hneg.congr_deriv ?_
  rw [cos_quarter_sub_sq]
  field_simp [show (0 : ℝ) < 1 + Real.sin ψ by
    have hnn := sin_nonneg_of_mem_Icc ⟨h0, h1.trans (by linarith [Real.pi_pos])⟩
    linarith]

theorem integral_inv_one_add_sin :
    ∫ ψ in (0 : ℝ)..Real.pi / 2, (1 + Real.sin ψ)⁻¹ = 1 := by
  have hle : (0 : ℝ) ≤ Real.pi / 2 := by linarith [Real.pi_pos]
  have hderiv : ∀ x ∈ uIcc (0 : ℝ) (Real.pi / 2),
      HasDerivAt (fun t => -Real.tan (Real.pi / 4 - t / 2)) ((1 + Real.sin x)⁻¹) x := by
    intro x hx
    rw [uIcc_of_le hle] at hx
    exact hasDerivAt_inv_one_add_sin x hx.1 hx.2
  have hcont : ContinuousOn (fun ψ => (1 + Real.sin ψ)⁻¹) (Icc 0 (Real.pi / 2)) := by
    refine ContinuousOn.inv₀ (continuous_const.add continuous_sin).continuousOn ?_
    intro ψ hψ
    have hnn := sin_nonneg_of_mem_Icc ⟨hψ.1, hψ.2.trans (by linarith [Real.pi_pos])⟩
    linarith
  rw [integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable_of_Icc hle)]
  have htop : Real.pi / 4 - (Real.pi / 2) / 2 = 0 := by ring
  have hbot : Real.pi / 4 - (0 : ℝ) / 2 = Real.pi / 4 := by ring
  rw [htop, hbot, Real.tan_zero, Real.tan_pi_div_four]
  norm_num

theorem integral_nullShape_sin :
    ∫ ψ in (0 : ℝ)..Real.pi / 2, nullShape (Real.sin ψ) = 2 := by
  have hle : (0 : ℝ) ≤ Real.pi / 2 := by linarith [Real.pi_pos]
  have hcongr :
      ∫ ψ in (0 : ℝ)..Real.pi / 2, nullShape (Real.sin ψ) =
        ∫ ψ in (0 : ℝ)..Real.pi / 2, Real.sin ψ + (1 + Real.sin ψ)⁻¹ := by
    refine integral_congr ?_
    intro ψ hψ
    rw [uIcc_of_le hle] at hψ
    have hnn := sin_nonneg_of_mem_Icc ⟨hψ.1, hψ.2.trans (by linarith [Real.pi_pos])⟩
    exact nullShape_add (by linarith)
  rw [hcongr, integral_add (continuous_sin.intervalIntegrable _ _)
    ((by
      refine ContinuousOn.inv₀ (continuous_const.add continuous_sin).continuousOn ?_
      intro ψ hψ
      have hnn := sin_nonneg_of_mem_Icc ⟨hψ.1, hψ.2.trans (by linarith [Real.pi_pos])⟩
      linarith :
      ContinuousOn (fun ψ => (1 + Real.sin ψ)⁻¹) (Icc 0 (Real.pi / 2))).intervalIntegrable_of_Icc
      hle)]
  rw [integral_sin, integral_inv_one_add_sin, Real.cos_zero, Real.cos_pi_div_two]
  norm_num

/-! ### The classical window -/

theorem deflection_bounds {M R : ℝ} (hM : 0 < M) (hR : 0 < R) (hph : 3 * M < R) :
    4 * M / R < deflection M R ∧
      deflection M R < (4 * M / R) / (1 - 3 * M / R) ^ (3 / 2 : ℝ) := by
  have hpi : (0 : ℝ) < Real.pi / 2 := by linarith [Real.pi_pos]
  have hle : (0 : ℝ) ≤ Real.pi / 2 := hpi.le
  set ε : ℝ := M / R
  have hε : 0 < ε := div_pos hM hR
  have hε_lt : 3 * ε < 1 := by
    have hrew : 3 * ε = 3 * M / R := by
      dsimp [ε]
      ring
    rw [hrew]
    exact (div_lt_one hR).mpr hph
  have hcontI := continuousOn_nullIntegrand hε.le hε_lt
  have hcontS := continuousOn_nullShape_sin
  have hpoint_low : ∀ ψ ∈ Icc (0 : ℝ) (Real.pi / 2),
      1 + ε * nullShape (Real.sin ψ) < nullIntegrand ε ψ := by
    intro ψ hψ
    have hsin0 : 0 ≤ Real.sin ψ :=
      sin_nonneg_of_mem_Icc ⟨hψ.1, hψ.2.trans (by linarith [Real.pi_pos])⟩
    have hsin1 : Real.sin ψ ≤ 1 := Real.sin_le_one ψ
    have hshape := nullShape_bounds hsin0 hsin1
    set x : ℝ := 2 * ε * nullShape (Real.sin ψ)
    have hx0 : 0 < x := by
      have hone : (0 : ℝ) < nullShape (Real.sin ψ) := by linarith
      positivity
    have hx1 : x < 1 := by
      have hmul : x ≤ 2 * ε * (3 / 2) := by
        dsimp [x]
        exact mul_le_mul_of_nonneg_left hshape.2 (by positivity)
      have hthree : 2 * ε * (3 / 2) = 3 * ε := by ring
      linarith
    have hlow := inv_sqrt_lower_strict hx0 hx1
    have hxhalf : x / 2 = ε * nullShape (Real.sin ψ) := by
      dsimp [x]
      ring
    unfold nullIntegrand
    linarith
  have hint_low :
      ∫ ψ in (0 : ℝ)..Real.pi / 2, 1 + ε * nullShape (Real.sin ψ) <
        ∫ ψ in (0 : ℝ)..Real.pi / 2, nullIntegrand ε ψ := by
    refine integral_lt_integral_of_continuousOn_of_le_of_exists_lt hpi ?_ hcontI ?_ ?_
    · exact (continuousOn_const.add (continuousOn_const.mul hcontS))
    · intro ψ hψ
      exact (hpoint_low ψ ⟨hψ.1.le, hψ.2⟩).le
    · exact ⟨0, ⟨le_rfl, hle⟩, hpoint_low 0 ⟨le_rfl, hle⟩⟩
  have hshape_int :
      ∫ ψ in (0 : ℝ)..Real.pi / 2, nullShape (Real.sin ψ) = 2 :=
    integral_nullShape_sin
  have hlow_eval :
      ∫ ψ in (0 : ℝ)..Real.pi / 2, 1 + ε * nullShape (Real.sin ψ) =
        Real.pi / 2 + 2 * ε := by
    have hf : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume 0 (Real.pi / 2) :=
      continuous_const.intervalIntegrable 0 (Real.pi / 2)
    have hg : IntervalIntegrable (fun ψ => ε * nullShape (Real.sin ψ)) volume 0
        (Real.pi / 2) :=
      (continuousOn_const.mul hcontS).intervalIntegrable_of_Icc hle
    have hadd := integral_add hf hg
    have hcongr :
        ∫ ψ in (0 : ℝ)..Real.pi / 2, 1 + ε * nullShape (Real.sin ψ) =
          ∫ ψ in (0 : ℝ)..Real.pi / 2,
            (fun _ : ℝ => (1 : ℝ)) ψ + ε * nullShape (Real.sin ψ) := by
      rfl
    rw [hcongr, hadd, intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
      hshape_int, smul_eq_mul]
    ring
  have hdefl :
      deflection M R =
        2 * ((∫ ψ in (0 : ℝ)..Real.pi / 2, nullIntegrand ε ψ) - Real.pi / 2) := by
    unfold deflection nullAzimuth
    have hεeq : M / R = ε := rfl
    rw [hεeq]
    ring
  have hlow : 4 * M / R < deflection M R := by
    have hI : Real.pi / 2 + 2 * ε < ∫ ψ in (0 : ℝ)..Real.pi / 2, nullIntegrand ε ψ := by
      rwa [hlow_eval] at hint_low
    have h4 : 4 * ε = 4 * M / R := by
      dsimp [ε]
      ring
    rw [hdefl, ← h4]
    linarith
  set c : ℝ := ε / Real.sqrt (1 - 3 * ε) ^ 3
  have hsqrt_pos : 0 < Real.sqrt (1 - 3 * ε) := Real.sqrt_pos.mpr (by linarith)
  have hpoint_up : ∀ ψ ∈ Icc (0 : ℝ) (Real.pi / 2),
      nullIntegrand ε ψ < 1 + c * nullShape (Real.sin ψ) := by
    intro ψ hψ
    have hsin0 : 0 ≤ Real.sin ψ :=
      sin_nonneg_of_mem_Icc ⟨hψ.1, hψ.2.trans (by linarith [Real.pi_pos])⟩
    have hsin1 : Real.sin ψ ≤ 1 := Real.sin_le_one ψ
    have hshape := nullShape_bounds hsin0 hsin1
    set x : ℝ := 2 * ε * nullShape (Real.sin ψ)
    have hx0 : 0 < x := by
      have hone : (0 : ℝ) < nullShape (Real.sin ψ) := by linarith
      positivity
    have hx_le : x ≤ 3 * ε := by
      have hmul : x ≤ 2 * ε * (3 / 2) := by
        dsimp [x]
        exact mul_le_mul_of_nonneg_left hshape.2 (by positivity)
      have hthree : 2 * ε * (3 / 2) = 3 * ε := by ring
      linarith
    have hx1 : x < 1 := by linarith
    have hstrict := inv_sqrt_upper_strict hx0 hx1
    have hden : Real.sqrt (1 - 3 * ε) ≤ Real.sqrt (1 - x) :=
      Real.sqrt_le_sqrt (by linarith)
    have hpow : Real.sqrt (1 - 3 * ε) ^ 3 ≤ Real.sqrt (1 - x) ^ 3 :=
      pow_le_pow_left₀ hsqrt_pos.le hden 3
    have hdiv :
        (x / 2) / Real.sqrt (1 - x) ^ 3 ≤ (x / 2) / Real.sqrt (1 - 3 * ε) ^ 3 :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hpow
    have hxhalf : x / 2 = ε * nullShape (Real.sin ψ) := by
      dsimp [x]
      ring
    have hcshape : (x / 2) / Real.sqrt (1 - 3 * ε) ^ 3 = c * nullShape (Real.sin ψ) := by
      rw [hxhalf]
      dsimp [c]
      field_simp [hsqrt_pos.ne']
    unfold nullIntegrand
    linarith
  have hint_up :
      ∫ ψ in (0 : ℝ)..Real.pi / 2, nullIntegrand ε ψ <
        ∫ ψ in (0 : ℝ)..Real.pi / 2, 1 + c * nullShape (Real.sin ψ) := by
    refine integral_lt_integral_of_continuousOn_of_le_of_exists_lt hpi hcontI ?_ ?_ ?_
    · exact (continuousOn_const.add (continuousOn_const.mul hcontS))
    · intro ψ hψ
      exact (hpoint_up ψ ⟨hψ.1.le, hψ.2⟩).le
    · exact ⟨0, ⟨le_rfl, hle⟩, hpoint_up 0 ⟨le_rfl, hle⟩⟩
  have hup_eval :
      ∫ ψ in (0 : ℝ)..Real.pi / 2, 1 + c * nullShape (Real.sin ψ) =
        Real.pi / 2 + 2 * c := by
    have hf : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume 0 (Real.pi / 2) :=
      continuous_const.intervalIntegrable 0 (Real.pi / 2)
    have hg : IntervalIntegrable (fun ψ => c * nullShape (Real.sin ψ)) volume 0
        (Real.pi / 2) :=
      (continuousOn_const.mul hcontS).intervalIntegrable_of_Icc hle
    have hadd := integral_add hf hg
    have hcongr :
        ∫ ψ in (0 : ℝ)..Real.pi / 2, 1 + c * nullShape (Real.sin ψ) =
          ∫ ψ in (0 : ℝ)..Real.pi / 2,
            (fun _ : ℝ => (1 : ℝ)) ψ + c * nullShape (Real.sin ψ) := by
      rfl
    rw [hcongr, hadd, intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
      hshape_int, smul_eq_mul]
    ring
  have hup_sqrt : deflection M R < 4 * ε / Real.sqrt (1 - 3 * ε) ^ 3 := by
    have hI :
        ∫ ψ in (0 : ℝ)..Real.pi / 2, nullIntegrand ε ψ < Real.pi / 2 + 2 * c := by
      rwa [hup_eval] at hint_up
    rw [hdefl]
    have hc4 : 4 * c = 4 * ε / Real.sqrt (1 - 3 * ε) ^ 3 := by
      dsimp [c]
      ring
    linarith
  have hbase : 0 ≤ 1 - 3 * ε := by linarith
  have hpow_eq : (1 - 3 * ε) ^ (3 / 2 : ℝ) = Real.sqrt (1 - 3 * ε) ^ 3 :=
    three_halves_eq_sqrt_pow hbase
  have hup : deflection M R < (4 * M / R) / (1 - 3 * M / R) ^ (3 / 2 : ℝ) := by
    have h4 : 4 * ε = 4 * M / R := by
      dsimp [ε]
      ring
    have hsub : 1 - 3 * ε = 1 - 3 * M / R := by
      dsimp [ε]
      ring
    rw [← h4, ← hsub, hpow_eq]
    exact hup_sqrt
  exact ⟨hlow, hup⟩

/-! ### The Sun -/

/-- Nominal solar radius, in metres. An external stand-in, as Mercury's elements are. -/
def solarRadius : ℚ := 695700000

/-- Deflection of a ray that turns at the nominal solar radius, in arcseconds. -/
noncomputable def deflectionArcsec : ℝ :=
  deflection (solarGeometricMass : ℝ) (solarRadius : ℝ) * (648000 / Real.pi)

private theorem three_M_lt_tenth :
    (3 : ℚ) * solarGeometricMass / solarRadius < 1 / 10 := by
  rw [solarGeometricMass_eq_num_div_den]
  unfold solarRadius
  have hnat : (30 : ℕ) * solarGeometricMass_num < speedOfLightNat ^ 2 * 695700000 := by
    native_decide
  have hcast :
      (30 : ℚ) * solarGeometricMass_num < (speedOfLightNat : ℚ) ^ 2 * 695700000 := by
    exact_mod_cast hnat
  have hden : (0 : ℚ) < (speedOfLightNat : ℚ) ^ 2 * 695700000 := by
    unfold speedOfLightNat
    norm_num
  have hrew :
      (3 : ℚ) * ((solarGeometricMass_num : ℚ) / (speedOfLightNat : ℚ) ^ 2) / 695700000 =
        (3 * (solarGeometricMass_num : ℚ)) /
          ((speedOfLightNat : ℚ) ^ 2 * 695700000) := by
    field_simp
  rw [hrew, div_lt_iff₀ hden]
  have h10 : (0 : ℚ) < 10 := by norm_num
  have hdiv : (30 : ℚ) * solarGeometricMass_num / 10 <
      ((speedOfLightNat : ℚ) ^ 2 * 695700000) / 10 :=
    div_lt_div_of_pos_right hcast h10
  have hleft : (30 : ℚ) * solarGeometricMass_num / 10 = 3 * solarGeometricMass_num := by ring
  have hright :
      ((speedOfLightNat : ℚ) ^ 2 * 695700000) / 10 =
        (1 / 10) * ((speedOfLightNat : ℚ) ^ 2 * 695700000) := by ring
  linarith

private theorem leading_gt_seventeen_tenths :
    (17 / 10 : ℚ) <
      4 * solarGeometricMass / solarRadius * 648000 * (7 / 22) := by
  rw [solarGeometricMass_eq_num_div_den]
  unfold solarRadius
  have hnat :
      (17 : ℕ) * speedOfLightNat ^ 2 * 695700000 * 22 <
        4 * solarGeometricMass_num * 648000 * 7 * 10 := by
    native_decide
  have hcast :
      (17 : ℚ) * (speedOfLightNat : ℚ) ^ 2 * 695700000 * 22 <
        (4 : ℚ) * solarGeometricMass_num * 648000 * 7 * 10 := by
    exact_mod_cast hnat
  have hden : (0 : ℚ) < (speedOfLightNat : ℚ) ^ 2 * 695700000 * 22 := by
    unfold speedOfLightNat
    norm_num
  have hrew :
      4 * ((solarGeometricMass_num : ℚ) / (speedOfLightNat : ℚ) ^ 2) / 695700000 *
          648000 * (7 / 22) =
        ((4 : ℚ) * solarGeometricMass_num * 648000 * 7) /
          ((speedOfLightNat : ℚ) ^ 2 * 695700000 * 22) := by
    field_simp
  rw [hrew, lt_div_iff₀ hden]
  have h10 : (0 : ℚ) < 10 := by norm_num
  rw [show (17 / 10 : ℚ) * ((speedOfLightNat : ℚ) ^ 2 * 695700000 * 22) =
      ((17 : ℚ) * (speedOfLightNat : ℚ) ^ 2 * 695700000 * 22) / 10 by ring,
    div_lt_iff₀ h10]
  convert hcast using 1

private theorem envelope_lt_nine_fifths :
    4 * solarGeometricMass / solarRadius *
        (1 + 6 * solarGeometricMass / solarRadius) * 648000 * (100 / 314) <
      (9 / 5 : ℚ) := by
  rw [solarGeometricMass_eq_num_div_den]
  unfold solarRadius
  have hnat :
      4 * solarGeometricMass_num *
          (speedOfLightNat ^ 2 * 695700000 + 6 * solarGeometricMass_num) *
          648000 * 100 * 5 <
        9 * (speedOfLightNat ^ 2 * 695700000) ^ 2 * 314 := by
    native_decide
  have hcast :
      (4 : ℚ) * solarGeometricMass_num *
          ((speedOfLightNat : ℚ) ^ 2 * 695700000 + 6 * solarGeometricMass_num) *
          648000 * 100 * 5 <
        (9 : ℚ) * ((speedOfLightNat : ℚ) ^ 2 * 695700000) ^ 2 * 314 := by
    exact_mod_cast hnat
  have hden : (0 : ℚ) < ((speedOfLightNat : ℚ) ^ 2 * 695700000) ^ 2 * 314 := by
    unfold speedOfLightNat
    norm_num
  have hC : (speedOfLightNat : ℚ) ≠ 0 := by
    unfold speedOfLightNat
    norm_num
  have hrew :
      4 * ((solarGeometricMass_num : ℚ) / (speedOfLightNat : ℚ) ^ 2) / 695700000 *
          (1 + 6 * ((solarGeometricMass_num : ℚ) / (speedOfLightNat : ℚ) ^ 2) / 695700000) *
          648000 * (100 / 314) =
        ((4 : ℚ) * solarGeometricMass_num *
            ((speedOfLightNat : ℚ) ^ 2 * 695700000 + 6 * solarGeometricMass_num) *
            648000 * 100) /
          (((speedOfLightNat : ℚ) ^ 2 * 695700000) ^ 2 * 314) := by
    field_simp [hC]
  rw [hrew, div_lt_iff₀ hden]
  have h5 : (0 : ℚ) < 5 := by norm_num
  rw [show (9 / 5 : ℚ) * (((speedOfLightNat : ℚ) ^ 2 * 695700000) ^ 2 * 314) =
      ((9 : ℚ) * ((speedOfLightNat : ℚ) ^ 2 * 695700000) ^ 2 * 314) / 5 by ring,
    lt_div_iff₀ h5]
  convert hcast using 1

private theorem pi_lt_22_div_7 : Real.pi < 22 / 7 := by
  have h := Real.pi_lt_d4
  have h22 : (3.1416 : ℝ) < 22 / 7 := by norm_num
  exact h.trans h22

private theorem pi_gt_314 : (314 : ℝ) / 100 < Real.pi := by
  have h := Real.pi_gt_d2
  norm_num at h ⊢
  exact h

theorem solar_deflection_arcsec_bounds :
    17 / 10 < deflectionArcsec ∧ deflectionArcsec < 9 / 5 := by
  have hM : (0 : ℝ) < (solarGeometricMass : ℝ) := by exact_mod_cast solarGeometricMass_pos
  have hR : (0 : ℝ) < (solarRadius : ℝ) := by
    unfold solarRadius
    norm_num
  have hph : 3 * (solarGeometricMass : ℝ) < (solarRadius : ℝ) := by
    have hten : ((3 * solarGeometricMass / solarRadius : ℚ) : ℝ) < ((1 / 10 : ℚ) : ℝ) :=
      Rat.cast_lt.mpr three_M_lt_tenth
    have hform : (3 : ℝ) * (solarGeometricMass : ℝ) / (solarRadius : ℝ) =
        ((3 * solarGeometricMass / solarRadius : ℚ) : ℝ) := by
      push_cast
      ring
    rw [← hform] at hten
    have hmul : 3 * (solarGeometricMass : ℝ) < (solarRadius : ℝ) / 10 := by
      rw [div_lt_iff₀ hR] at hten
      linarith
    linarith
  have hb := deflection_bounds hM hR hph
  set δ : ℝ := deflection (solarGeometricMass : ℝ) (solarRadius : ℝ)
  set lead : ℝ := 4 * (solarGeometricMass : ℝ) / (solarRadius : ℝ)
  have hlead : 0 < lead := by
    dsimp [lead]
    positivity
  have hfac : 0 < (648000 : ℝ) / Real.pi := by positivity
  have hpi_hi := pi_lt_22_div_7
  have hinv : (7 : ℝ) / 22 < 1 / Real.pi := by
    have h7 : (7 : ℝ) / 22 = 1 / (22 / 7) := by norm_num
    rw [h7]
    exact (one_div_lt_one_div (by norm_num) Real.pi_pos).mpr hpi_hi
  have hlow_rat : (17 / 10 : ℝ) < lead * 648000 * (7 / 22) := by
    have hcast :
        ((17 / 10 : ℚ) : ℝ) <
          ((4 * solarGeometricMass / solarRadius * 648000 * (7 / 22) : ℚ) : ℝ) :=
      Rat.cast_lt.mpr leading_gt_seventeen_tenths
    have hform :
        4 * (solarGeometricMass : ℝ) / (solarRadius : ℝ) * 648000 * (7 / 22) =
          ((4 * solarGeometricMass / solarRadius * 648000 * (7 / 22) : ℚ) : ℝ) := by
      push_cast
      ring
    rw [← hform] at hcast
    simpa [lead] using hcast
  have hlow_pi : lead * 648000 * (7 / 22) < lead * 648000 / Real.pi := by
    have hmul := mul_lt_mul_of_pos_left hinv (mul_pos hlead (by norm_num : (0 : ℝ) < 648000))
    simpa [mul_assoc, div_eq_mul_inv] using hmul
  have hlow_δ : lead * 648000 / Real.pi < δ * 648000 / Real.pi := by
    have hmul := mul_lt_mul_of_pos_right hb.1 hfac
    simpa [lead, mul_assoc, div_eq_mul_inv] using hmul
  have hlow : 17 / 10 < deflectionArcsec := by
    have hchain := hlow_rat.trans (hlow_pi.trans hlow_δ)
    simpa [deflectionArcsec, δ, mul_assoc, div_eq_mul_inv] using hchain
  have hx0 : 0 < 3 * ((solarGeometricMass : ℝ) / (solarRadius : ℝ)) := by positivity
  have hx1 : 3 * ((solarGeometricMass : ℝ) / (solarRadius : ℝ)) ≤ 1 / 10 := by
    have hten : ((3 * solarGeometricMass / solarRadius : ℚ) : ℝ) < ((1 / 10 : ℚ) : ℝ) :=
      Rat.cast_lt.mpr three_M_lt_tenth
    have hform : 3 * ((solarGeometricMass : ℝ) / (solarRadius : ℝ)) =
        ((3 * solarGeometricMass / solarRadius : ℚ) : ℝ) := by
      push_cast
      ring
    linarith
  have hcube := inv_sqrt_cube_lt hx0 hx1
  have hbase : 0 ≤ 1 - 3 * (solarGeometricMass : ℝ) / (solarRadius : ℝ) := by
    have h3 : 3 * (solarGeometricMass : ℝ) / (solarRadius : ℝ) < 1 :=
      (div_lt_one hR).mpr hph
    linarith
  have hpow := three_halves_eq_sqrt_pow hbase
  have hwiden : lead / (1 - 3 * (solarGeometricMass : ℝ) / (solarRadius : ℝ)) ^ (3 / 2 : ℝ) <
      lead * (1 + 6 * (solarGeometricMass : ℝ) / (solarRadius : ℝ)) := by
    have hcube' :
        1 / Real.sqrt (1 - 3 * (solarGeometricMass : ℝ) / (solarRadius : ℝ)) ^ 3 <
          1 + 6 * (solarGeometricMass : ℝ) / (solarRadius : ℝ) := by
      have hsub : 1 - 3 * ((solarGeometricMass : ℝ) / (solarRadius : ℝ)) =
          1 - 3 * (solarGeometricMass : ℝ) / (solarRadius : ℝ) := by ring
      have htwo : 1 + 2 * (3 * ((solarGeometricMass : ℝ) / (solarRadius : ℝ))) =
          1 + 6 * (solarGeometricMass : ℝ) / (solarRadius : ℝ) := by ring
      simpa [hsub, htwo] using hcube
    rw [← hpow] at hcube'
    have hmul := mul_lt_mul_of_pos_left hcube' hlead
    simpa [div_eq_mul_inv] using hmul
  have hδ_env : δ < lead * (1 + 6 * (solarGeometricMass : ℝ) / (solarRadius : ℝ)) := by
    have h4 : lead = 4 * (solarGeometricMass : ℝ) / (solarRadius : ℝ) := rfl
    have hb2 := hb.2
    dsimp [δ, lead] at hb2 ⊢
    exact hb2.trans hwiden
  have hpi_lo := pi_gt_314
  have hinvpi : 1 / Real.pi < (100 : ℝ) / 314 := by
    have hrec : (1 : ℝ) / ((314 : ℝ) / 100) = 100 / 314 := by norm_num
    have hlt := (one_div_lt_one_div Real.pi_pos (by norm_num)).mpr hpi_lo
    simpa [hrec] using hlt
  have henv_pi :
      lead * (1 + 6 * (solarGeometricMass : ℝ) / (solarRadius : ℝ)) * 648000 / Real.pi <
        lead * (1 + 6 * (solarGeometricMass : ℝ) / (solarRadius : ℝ)) * 648000 * (100 / 314) := by
    have hpos : 0 < lead * (1 + 6 * (solarGeometricMass : ℝ) / (solarRadius : ℝ)) * 648000 := by
      positivity
    have hmul := mul_lt_mul_of_pos_left hinvpi hpos
    simpa [mul_assoc, div_eq_mul_inv] using hmul
  have henv_rat :
      lead * (1 + 6 * (solarGeometricMass : ℝ) / (solarRadius : ℝ)) * 648000 * (100 / 314) <
        9 / 5 := by
    have hcast :
        ((4 * solarGeometricMass / solarRadius *
            (1 + 6 * solarGeometricMass / solarRadius) * 648000 * (100 / 314) : ℚ) : ℝ) <
          ((9 / 5 : ℚ) : ℝ) :=
      Rat.cast_lt.mpr envelope_lt_nine_fifths
    have hform :
        4 * (solarGeometricMass : ℝ) / (solarRadius : ℝ) *
            (1 + 6 * (solarGeometricMass : ℝ) / (solarRadius : ℝ)) * 648000 * (100 / 314) =
          ((4 * solarGeometricMass / solarRadius *
            (1 + 6 * solarGeometricMass / solarRadius) * 648000 * (100 / 314) : ℚ) : ℝ) := by
      push_cast
      ring
    rw [← hform] at hcast
    simpa [lead] using hcast
  have hup_arc : δ * 648000 / Real.pi < 9 / 5 := by
    have hstep : δ * 648000 / Real.pi <
        lead * (1 + 6 * (solarGeometricMass : ℝ) / (solarRadius : ℝ)) * 648000 / Real.pi := by
      have hmul := mul_lt_mul_of_pos_right hδ_env hfac
      simpa [mul_assoc, div_eq_mul_inv] using hmul
    exact hstep.trans (henv_pi.trans henv_rat)
  have hup : deflectionArcsec < 9 / 5 := by
    simpa [deflectionArcsec, δ, mul_assoc, div_eq_mul_inv] using hup_arc
  exact ⟨hlow, hup⟩

end SolarDeflection

end Gravity

end DstDiophantine
