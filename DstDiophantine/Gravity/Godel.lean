import DstDiophantine.Gravity.Coframe
import DstDiophantine.Gravity.EventBoundary
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Artanh
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Gödel chart and the azimuthal time loop

The orthonormal coframe
`e⁰ = dt + √2 sinh²r dφ`, `e¹ = dr`, `e² = sinh r cosh r dφ`, `e³ = dz`
induces the Gödel metric. For `r > 0` the norm of `∂φ` has the sign of
`1 - sinh²r`. It vanishes at `r_c = log(1+√2)` and is negative beyond, so a
periodic identification of `φ` makes those circles closed and timelike. The
coframe legs stay finite there, and the `(t,φ)` block stays non-degenerate.
The norm of `∂t` stays `-1`.

The ratio of the orthonormal components of `∂φ` is the tilt `√2 tanh r`.
A real rapidity represents that ratio only as `tanh ψ`. Every such radius
lies strictly before `r_c`, where the azimuthal norm is still positive.
The three-axis ceiling `phiMax` and the one-axis bound `π/2` are two
instances. No real rapidity makes the circles timelike.

A pure boost in the `(t,φ)` plane of a diagonal cylindrical frame does not
produce the Gödel cross term. The rapidity bounded here is the component
ratio of `∂φ`, not the parameter of that boost.

## Not claimed

* The periodic identification of `φ`. The sign of the norm is proved; the
  closing of the circle is the classical chart.
* That the Gödel coframe is a pure boost, or that `J = ½ ψ²` is derived
  rather than read by the same working identification as the quasi-horizon.
* A teleparallel scalar for this coframe, dust, or a cosmological constant.
* That every closed timelike curve, in every spacetime, is excluded.
-/

namespace DstDiophantine

namespace Gravity

open Real Set

/-! ### Critical radius -/

/-- Radius `log(1+√2)` at which the azimuthal circles are null. -/
noncomputable def godelCriticalRadius : ℝ :=
  Real.log (1 + Real.sqrt 2)

theorem one_add_sqrt_two_pos : 0 < 1 + Real.sqrt 2 := by positivity

theorem one_add_sqrt_two_mul_conj : (1 + Real.sqrt 2) * (Real.sqrt 2 - 1) = 1 := by
  have hs : Real.sqrt 2 * Real.sqrt 2 = 2 := by
    rw [← pow_two, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  calc
    (1 + Real.sqrt 2) * (Real.sqrt 2 - 1)
        = Real.sqrt 2 - 1 + Real.sqrt 2 * Real.sqrt 2 - Real.sqrt 2 := by ring
    _ = 1 := by rw [hs]; ring

theorem inv_one_add_sqrt_two : (1 + Real.sqrt 2)⁻¹ = Real.sqrt 2 - 1 := by
  refine (mul_left_inj' one_add_sqrt_two_pos.ne').mp ?_
  rw [inv_mul_cancel₀ one_add_sqrt_two_pos.ne']
  rw [mul_comm (Real.sqrt 2 - 1)]
  exact one_add_sqrt_two_mul_conj.symm

theorem godelCriticalRadius_pos : 0 < godelCriticalRadius := by
  unfold godelCriticalRadius
  exact Real.log_pos (by linarith [Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)])

theorem sinh_godelCriticalRadius : Real.sinh godelCriticalRadius = 1 := by
  unfold godelCriticalRadius
  rw [Real.sinh_eq, Real.exp_log one_add_sqrt_two_pos, Real.exp_neg,
    Real.exp_log one_add_sqrt_two_pos, inv_one_add_sqrt_two]
  ring

theorem cosh_godelCriticalRadius : Real.cosh godelCriticalRadius = Real.sqrt 2 := by
  unfold godelCriticalRadius
  rw [Real.cosh_eq, Real.exp_log one_add_sqrt_two_pos, Real.exp_neg,
    Real.exp_log one_add_sqrt_two_pos, inv_one_add_sqrt_two]
  ring

theorem godelCriticalRadius_eq_arsinh : godelCriticalRadius = Real.arsinh 1 := by
  apply (Real.sinh_strictMono).injective
  rw [sinh_godelCriticalRadius, Real.sinh_arsinh]

/-! ### Coframe and metric -/

/-- Orthonormal Gödel coframe at radius `r`. Indices `(t,r,φ,z)`. -/
noncomputable def godelCoframe (r : ℝ) : Coframe :=
  fun a μ =>
    if a = 0 ∧ μ = 0 then 1
    else if a = 0 ∧ μ = 2 then Real.sqrt 2 * Real.sinh r ^ 2
    else if a = 1 ∧ μ = 1 then 1
    else if a = 2 ∧ μ = 2 then Real.sinh r * Real.cosh r
    else if a = 3 ∧ μ = 3 then 1
    else 0

/-- Azimuthal norm `g_φφ = sinh²r (1 - sinh²r)`. -/
noncomputable def godelGφφ (r : ℝ) : ℝ :=
  Real.sinh r ^ 2 * (1 - Real.sinh r ^ 2)

/-- Cross term `g_tφ = -√2 sinh²r`. -/
noncomputable def godelGtφ (r : ℝ) : ℝ :=
  -(Real.sqrt 2 * Real.sinh r ^ 2)

/-- Coordinate components of the Gödel metric. -/
noncomputable def godelMetric (r : ℝ) : Fin 4 → Fin 4 → ℝ
  | 0, 0 => -1
  | 1, 1 => 1
  | 2, 2 => godelGφφ r
  | 3, 3 => 1
  | 0, 2 => godelGtφ r
  | 2, 0 => godelGtφ r
  | _, _ => 0

theorem godel_azimuth_identity (r : ℝ) :
    -(Real.sqrt 2 * Real.sinh r ^ 2 * (Real.sqrt 2 * Real.sinh r ^ 2)) +
        Real.sinh r * Real.cosh r * (Real.sinh r * Real.cosh r) =
      godelGφφ r := by
  have hs : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  unfold godelGφφ
  calc
    -(Real.sqrt 2 * Real.sinh r ^ 2 * (Real.sqrt 2 * Real.sinh r ^ 2)) +
          Real.sinh r * Real.cosh r * (Real.sinh r * Real.cosh r)
        = -(Real.sqrt 2) ^ 2 * Real.sinh r ^ 4 +
            Real.sinh r ^ 2 * Real.cosh r ^ 2 := by ring
    _ = -2 * Real.sinh r ^ 4 +
          Real.sinh r ^ 2 * (1 + Real.sinh r ^ 2) := by rw [hs, Real.cosh_sq']
    _ = Real.sinh r ^ 2 * (1 - Real.sinh r ^ 2) := by ring

theorem induced_godel_tt (r : ℝ) :
    inducedMetric (godelCoframe r) 0 0 = -1 := by
  rw [inducedMetric_eq_weighted, Fin.sum_univ_four]
  simp [godelCoframe, w31]

theorem induced_godel_rr (r : ℝ) :
    inducedMetric (godelCoframe r) 1 1 = 1 := by
  rw [inducedMetric_eq_weighted, Fin.sum_univ_four]
  simp [godelCoframe, w31]

theorem induced_godel_zz (r : ℝ) :
    inducedMetric (godelCoframe r) 3 3 = 1 := by
  rw [inducedMetric_eq_weighted, Fin.sum_univ_four]
  simp [godelCoframe, w31]

theorem induced_godel_tφ (r : ℝ) :
    inducedMetric (godelCoframe r) 0 2 = godelGtφ r := by
  rw [inducedMetric_eq_weighted, Fin.sum_univ_four]
  simp [godelCoframe, w31, godelGtφ]

theorem induced_godel_φt (r : ℝ) :
    inducedMetric (godelCoframe r) 2 0 = godelGtφ r := by
  rw [inducedMetric_eq_weighted, Fin.sum_univ_four]
  simp [godelCoframe, w31, godelGtφ]

set_option linter.flexible false in
theorem induced_godel_φφ (r : ℝ) :
    inducedMetric (godelCoframe r) 2 2 = godelGφφ r := by
  rw [inducedMetric_eq_weighted, Fin.sum_univ_four]
  simp [godelCoframe, w31]
  exact godel_azimuth_identity r

/-- The coframe induces the Gödel metric. -/
theorem inducedMetric_godel (r : ℝ) (μ ν : Fin 4) :
    inducedMetric (godelCoframe r) μ ν = godelMetric r μ ν := by
  fin_cases μ <;> fin_cases ν <;> first
    | exact induced_godel_tt r
    | exact induced_godel_rr r
    | exact induced_godel_zz r
    | exact induced_godel_tφ r
    | exact induced_godel_φt r
    | exact induced_godel_φφ r
    | rw [inducedMetric_eq_weighted, Fin.sum_univ_four]; simp [godelCoframe, w31]; rfl

theorem godelCoframe_critical_tφ :
    godelCoframe godelCriticalRadius 0 2 = Real.sqrt 2 := by
  simp [godelCoframe, sinh_godelCriticalRadius]

theorem godelCoframe_critical_φ :
    godelCoframe godelCriticalRadius 2 2 = Real.sqrt 2 := by
  simp [godelCoframe, sinh_godelCriticalRadius, cosh_godelCriticalRadius]

theorem godel_timePhi_det (r : ℝ) :
    (-1) * godelGφφ r - godelGtφ r ^ 2 =
      -(Real.sinh r ^ 2 * (1 + Real.sinh r ^ 2)) := by
  unfold godelGφφ godelGtφ
  have hs : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  calc
    (-1) * (Real.sinh r ^ 2 * (1 - Real.sinh r ^ 2)) -
          (-(Real.sqrt 2 * Real.sinh r ^ 2)) ^ 2
        = -(Real.sinh r ^ 2 * (1 - Real.sinh r ^ 2)) -
            (Real.sqrt 2) ^ 2 * Real.sinh r ^ 4 := by ring
    _ = -(Real.sinh r ^ 2 - Real.sinh r ^ 4) - 2 * Real.sinh r ^ 4 := by rw [hs]; ring
    _ = -(Real.sinh r ^ 2 * (1 + Real.sinh r ^ 2)) := by ring

theorem godel_timePhi_det_critical :
    (-1) * godelGφφ godelCriticalRadius - godelGtφ godelCriticalRadius ^ 2 = -2 := by
  rw [godel_timePhi_det, sinh_godelCriticalRadius]
  ring

theorem godelGφφ_critical : godelGφφ godelCriticalRadius = 0 := by
  simp [godelGφφ, sinh_godelCriticalRadius]

/-! ### Sign of the azimuthal norm -/

theorem godelGφφ_pos_of_lt_critical {r : ℝ} (h0 : 0 < r) (hr : r < godelCriticalRadius) :
    0 < godelGφφ r := by
  have hs0 : 0 < Real.sinh r := by
    rw [← Real.sinh_zero]
    exact Real.sinh_strictMono h0
  have hs1 : Real.sinh r < 1 := by
    rw [← sinh_godelCriticalRadius]
    exact Real.sinh_strictMono hr
  have hsq : Real.sinh r ^ 2 < 1 := by nlinarith [hs0, hs1]
  have hpos : 0 < Real.sinh r ^ 2 := by nlinarith [hs0]
  have hrest : 0 < 1 - Real.sinh r ^ 2 := by linarith
  unfold godelGφφ
  exact mul_pos hpos hrest

theorem godelGφφ_neg_of_gt_critical {r : ℝ} (hr : godelCriticalRadius < r) :
    godelGφφ r < 0 := by
  have hs : 1 < Real.sinh r := by
    rw [← sinh_godelCriticalRadius]
    exact Real.sinh_strictMono hr
  have hsq : 0 < Real.sinh r ^ 2 := by nlinarith
  have hrest : 1 - Real.sinh r ^ 2 < 0 := by nlinarith
  unfold godelGφφ
  exact mul_neg_of_pos_of_neg hsq hrest

/-! ### Tilt and rapidity -/

/-- Component ratio of `∂φ` in the orthonormal frame, `√2 tanh r`. -/
noncomputable def godelTilt (r : ℝ) : ℝ :=
  Real.sqrt 2 * Real.tanh r

/-- Rapidity of the tilt. Real only while `godelTilt r` lies in `(-1, 1)`. -/
noncomputable def godelRapidity (r : ℝ) : ℝ :=
  Real.artanh (godelTilt r)

theorem godelTilt_zero : godelTilt 0 = 0 := by
  simp [godelTilt]

theorem godelTilt_critical : godelTilt godelCriticalRadius = 1 := by
  unfold godelTilt
  rw [Real.tanh_eq_sinh_div_cosh, sinh_godelCriticalRadius, cosh_godelCriticalRadius]
  have hs : Real.sqrt 2 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
  field_simp [hs]

theorem tanh_strictMono : StrictMono Real.tanh := by
  intro x y hxy
  rw [Real.tanh_eq_sinh_div_cosh, Real.tanh_eq_sinh_div_cosh]
  have hcx : 0 < Real.cosh x := Real.cosh_pos x
  have hcy : 0 < Real.cosh y := Real.cosh_pos y
  rw [div_lt_div_iff₀ hcx hcy]
  have hsub : Real.sinh (x - y) < 0 := by
    rw [Real.sinh_neg_iff]
    linarith
  rw [Real.sinh_sub] at hsub
  linarith

theorem continuous_godelTilt : Continuous godelTilt := by
  have hfun : godelTilt = fun r => Real.sqrt 2 * (Real.sinh r / Real.cosh r) := by
    ext r
    rw [godelTilt, Real.tanh_eq_sinh_div_cosh]
  rw [hfun]
  exact continuous_const.mul <|
    continuous_sinh.div continuous_cosh fun x => (Real.cosh_pos x).ne'

theorem godelTilt_strictMono : StrictMono godelTilt :=
  tanh_strictMono.const_mul (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2))

theorem godelTilt_lt_one_of_lt_critical {r : ℝ} (hr : r < godelCriticalRadius) :
    godelTilt r < 1 := by
  have h := godelTilt_strictMono hr
  simpa [godelTilt_critical] using h

theorem godelTilt_gt_one_of_gt_critical {r : ℝ} (hr : godelCriticalRadius < r) :
    1 < godelTilt r := by
  have h := godelTilt_strictMono hr
  simpa [godelTilt_critical] using h

/-- Past the null circle the tilt is not the hyperbolic tangent of any real rapidity. -/
theorem godelTilt_ne_tanh_of_gt_critical {ψ r : ℝ} (hr : godelCriticalRadius < r) :
    godelTilt r ≠ Real.tanh ψ := by
  intro h
  have h1 : 1 < godelTilt r := godelTilt_gt_one_of_gt_critical hr
  have ht : Real.tanh ψ < 1 := Real.tanh_lt_one ψ
  linarith

theorem godelTilt_nonneg_of_nonneg {r : ℝ} (hr : 0 ≤ r) : 0 ≤ godelTilt r := by
  unfold godelTilt
  rw [Real.tanh_eq_sinh_div_cosh]
  exact mul_nonneg (Real.sqrt_nonneg _)
    (div_nonneg (Real.sinh_nonneg_iff.mpr hr) (Real.cosh_pos r).le)

theorem exists_radius_of_tilt {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    ∃ r, 0 ≤ r ∧ r < godelCriticalRadius ∧ godelTilt r = u := by
  have hrc : 0 < godelCriticalRadius := godelCriticalRadius_pos
  have hsub := intermediate_value_Icc (le_of_lt hrc) continuous_godelTilt.continuousOn
  have huv : u ∈ Icc (godelTilt 0) (godelTilt godelCriticalRadius) := by
    rw [godelTilt_zero, godelTilt_critical]
    exact ⟨hu0, hu1.le⟩
  obtain ⟨r, hr, hru⟩ := hsub huv
  refine ⟨r, hr.1, lt_of_le_of_ne hr.2 ?_, hru⟩
  intro heq
  rw [heq, godelTilt_critical] at hru
  exact hu1.ne hru.symm

theorem tanh_godelRapidity_of_lt_critical {r : ℝ} (h0 : 0 ≤ r)
    (hr : r < godelCriticalRadius) :
    Real.tanh (godelRapidity r) = godelTilt r := by
  have hlt : godelTilt r < 1 := godelTilt_lt_one_of_lt_critical hr
  have hnn : 0 ≤ godelTilt r := godelTilt_nonneg_of_nonneg h0
  rw [godelRapidity]
  exact Real.tanh_artanh ⟨by linarith [hnn], hlt⟩

theorem godelRapidity_eq_of_tilt {ψ r : ℝ} (h0 : 0 ≤ r) (hr : r < godelCriticalRadius)
    (h : godelTilt r = Real.tanh ψ) :
    godelRapidity r = ψ := by
  apply tanh_strictMono.injective
  rw [tanh_godelRapidity_of_lt_critical h0 hr, h]

/-- A positive real rapidity is attained strictly before the null circle,
where the azimuthal norm is still positive. -/
theorem exists_godel_before_loop {ψ : ℝ} (hψ : 0 < ψ) :
    ∃ r, 0 < r ∧ r < godelCriticalRadius ∧ godelRapidity r = ψ ∧ 0 < godelGφφ r := by
  have hu0 : 0 < Real.tanh ψ := by
    rw [Real.tanh_eq_sinh_div_cosh]
    have hc : 0 < Real.cosh ψ := Real.cosh_pos ψ
    have hs : 0 < Real.sinh ψ := by
      rw [← Real.sinh_zero]
      exact Real.sinh_strictMono hψ
    exact div_pos hs hc
  have hu1 : Real.tanh ψ < 1 := Real.tanh_lt_one ψ
  obtain ⟨r, hr0, hrc, htilt⟩ := exists_radius_of_tilt hu0.le hu1
  have hrpos : 0 < r := by
    refine lt_of_le_of_ne hr0 ?_
    intro heq
    have : godelTilt r = 0 := by simpa [heq] using godelTilt_zero
    linarith
  refine ⟨r, hrpos, hrc, ?_, godelGφφ_pos_of_lt_critical hrpos hrc⟩
  exact godelRapidity_eq_of_tilt hr0 hrc htilt

theorem exists_phiMax_godel_before_loop :
    ∃ r, 0 < r ∧ r < godelCriticalRadius ∧ godelRapidity r = phiMax ∧
      0 < godelGφφ r := by
  have hψ : 0 < phiMax := by
    unfold phiMax
    positivity
  exact exists_godel_before_loop hψ

theorem exists_halfPi_godel_before_loop :
    ∃ r, 0 < r ∧ r < godelCriticalRadius ∧ godelRapidity r = Real.pi / 2 ∧
      0 < godelGφφ r :=
  exists_godel_before_loop (half_pos Real.pi_pos)

/-- The azimuthal norm of a tilt that equals `tanh ψ` cannot be negative. -/
theorem godelGφφ_not_neg_of_eq_tanh {ψ r : ℝ} (hr0 : 0 < r)
    (h : godelTilt r = Real.tanh ψ) :
    ¬ godelGφφ r < 0 := by
  intro hneg
  have hgt : godelCriticalRadius < r := by
    by_contra hle
    have hlt : r < godelCriticalRadius ∨ r = godelCriticalRadius :=
      lt_or_eq_of_le (not_lt.mp hle)
    cases hlt with
    | inl hlt =>
        exact (godelGφφ_pos_of_lt_critical hr0 hlt).not_gt hneg
    | inr heq =>
        rw [heq, godelGφφ_critical] at hneg
        exact lt_irrefl (0 : ℝ) hneg
  exact godelTilt_ne_tanh_of_gt_critical hgt h

/-! ### A pure boost does not write the cross term -/

/-- Diagonal cylindrical coframe, boosted by rapidity `ψ` in the `(t,φ)` plane.
`β` is the circumferential scale of the reference leg. -/
noncomputable def cylBoostCoframe (ψ β : ℝ) : Coframe :=
  fun a μ =>
    if a = 0 ∧ μ = 0 then Real.cosh ψ
    else if a = 0 ∧ μ = 2 then Real.sinh ψ * β
    else if a = 2 ∧ μ = 0 then Real.sinh ψ
    else if a = 2 ∧ μ = 2 then Real.cosh ψ * β
    else if a = 1 ∧ μ = 1 then 1
    else if a = 3 ∧ μ = 3 then 1
    else 0

theorem induced_cylBoost_tt (ψ β : ℝ) :
    inducedMetric (cylBoostCoframe ψ β) 0 0 = -1 := by
  rw [inducedMetric_eq_weighted, Fin.sum_univ_four]
  simp [cylBoostCoframe, w31]
  have h := Real.cosh_sq_sub_sinh_sq ψ
  ring_nf at h ⊢
  linarith

theorem induced_cylBoost_tφ (ψ β : ℝ) :
    inducedMetric (cylBoostCoframe ψ β) 0 2 = 0 := by
  rw [inducedMetric_eq_weighted, Fin.sum_univ_four]
  simp [cylBoostCoframe, w31]
  ring

theorem induced_cylBoost_φφ (ψ β : ℝ) :
    inducedMetric (cylBoostCoframe ψ β) 2 2 = β ^ 2 := by
  rw [inducedMetric_eq_weighted, Fin.sum_univ_four]
  simp [cylBoostCoframe, w31]
  have h := Real.cosh_sq_sub_sinh_sq ψ
  linear_combination β ^ 2 * h

theorem cylBoost_azimuth_pos {ψ β : ℝ} (hβ : β ≠ 0) :
    0 < inducedMetric (cylBoostCoframe ψ β) 2 2 := by
  rw [induced_cylBoost_φφ]
  exact sq_pos_of_ne_zero hβ

end Gravity

end DstDiophantine
