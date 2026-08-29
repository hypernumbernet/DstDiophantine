import DstDiophantine.Gravity.GaugeDictionary
import DstDiophantine.Gravity.JTDictionary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Exterior Schwarzschild as the classical special case

The closed dictionary of `Gravity.GaugeDictionary` holds for an arbitrary
static radial-boost gauge with time-leg \(A>0\). This file proves that the
exterior factor \(A=1-r_s/r\) is the classical specialisation of that gauge,
characterised uniquely by the vacuum condition \(\frac{d}{dr}(rA)=1\).

## Proved

* Gauge specialisation: every exterior Schwarzschild identity is the
  \(A=1-r_s/r\) instance of the corresponding abstract-gauge theorem.
* Vacuum characterisation: \(\frac{d}{dr}(rA)=1\) on an open ray forces
  \(A(r)=1-r_s/r\) for a unique \(r_s\).
* Newtonian sandwich \(\frac{r_s}{2r}\le\varphi\le\frac{r_s}{2rA}\) and
  \(r\varphi\to r_s/2\).
* Far-field coefficients \(r^4 T\to r_s^2/2\) and \(4r^2 J\to r_s^2/2\).
* Exterior layering: \(A\) strictly increasing, \(\varphi,J,T,r^2T\)
  strictly decreasing; \(A\to 0^+\) and \(\varphi\to\infty\) as \(r\to r_s^+\).
* Exact witness at \(r=\frac43 r_s\): \(A=\frac14\), \(\varphi=\log 2\),
  \(r^2 T=1\), \(4J=2\log^2 2<1\), \(r^2 J_{\mathrm{field}}=\frac98\).

## Not claimed

* A dictionary for a general tetrad field (off-axis or with translations).
* Identification of the proposed action \(\int J\) with the TEGR integral of \(T\).
-/

namespace DstDiophantine

namespace Gravity

open Invariant Amplification Real Set Filter
open scoped Topology

/-! ### Gauge arguments of the exterior chart -/

theorem gaugeArgs_of_exterior {rs r : ℝ} (h : IsExterior rs r) :
    0 < schwarzschildA rs r ∧ r ≠ 0 :=
  ⟨schwarzschildA_pos h, (lt_trans h.1 h.2).ne'⟩

theorem schwarzschildA_ne_one {rs r : ℝ} (h : IsExterior rs r) :
    schwarzschildA rs r ≠ 1 := by
  unfold schwarzschildA
  have : 0 < rs / r := div_pos h.1 (lt_trans h.1 h.2)
  linarith

/-! ### Specialisation: Schwarzschild theorems as gauge corollaries -/

theorem schwarzschild_T_eq_cosh_via_gauge {rs r : ℝ} (h : IsExterior rs r) :
    schwarzschildTeleparallelT rs r =
      (4 / r ^ 2) * (cosh (schwarzschildRapidity rs r) - 1) := by
  have ⟨hA, hr⟩ := gaugeArgs_of_exterior h
  rw [schwarzschildTeleparallelT_eq_teleparallelTofA,
    schwarzschildRapidity_eq_rapidityOfA]
  exact teleparallelTofA_eq_cosh hA hr

theorem schwarzschild_T_eq_sinh_half_via_gauge {rs r : ℝ}
    (h : IsExterior rs r) :
    schwarzschildTeleparallelT rs r =
      (8 / r ^ 2) * sinh (schwarzschildRapidity rs r / 2) ^ 2 := by
  have ⟨hA, hr⟩ := gaugeArgs_of_exterior h
  rw [schwarzschildTeleparallelT_eq_teleparallelTofA,
    schwarzschildRapidity_eq_rapidityOfA]
  exact teleparallelTofA_eq_sinh_half_sq hA hr

theorem four_J_le_r_sq_T_via_gauge {rs r : ℝ} (h : IsExterior rs r) :
    4 * J (radialBoostParams rs r) ≤
      r ^ 2 * schwarzschildTeleparallelT rs r := by
  have ⟨hA, hr⟩ := gaugeArgs_of_exterior h
  rw [radialBoostParams_eq_gauge, schwarzschildTeleparallelT_eq_teleparallelTofA]
  exact four_J_le_r_sq_T_ofA hA hr

theorem four_J_lt_r_sq_T_via_gauge {rs r : ℝ} (h : IsExterior rs r) :
    4 * J (radialBoostParams rs r) <
      r ^ 2 * schwarzschildTeleparallelT rs r := by
  have ⟨hA, hr⟩ := gaugeArgs_of_exterior h
  have hA1 := schwarzschildA_ne_one h
  rw [radialBoostParams_eq_gauge, schwarzschildTeleparallelT_eq_teleparallelTofA]
  exact four_J_lt_r_sq_T_ofA hA hA1 hr

theorem schwarzschild_T_nonneg_via_gauge {rs r : ℝ} (h : IsExterior rs r) :
    0 ≤ schwarzschildTeleparallelT rs r := by
  have ⟨hA, hr⟩ := gaugeArgs_of_exterior h
  rw [schwarzschildTeleparallelT_eq_teleparallelTofA]
  exact teleparallelTofA_nonneg hA hr

/-- The two derivations of the closed form agree. -/
example {rs r : ℝ} (h : IsExterior rs r) :
    schwarzschildTeleparallelT rs r =
      (4 / r ^ 2) * (cosh (schwarzschildRapidity rs r) - 1) :=
  schwarzschild_T_eq_cosh_via_gauge h

example {rs r : ℝ} (h : IsExterior rs r) :
    schwarzschildTeleparallelT rs r =
      (4 / r ^ 2) * (cosh (schwarzschildRapidity rs r) - 1) :=
  schwarzschild_T_eq_cosh_rapidity h

/-! ### Vacuum condition \(\frac{d}{dr}(rA)=1\) -/

theorem r_mul_schwarzschildA {rs r : ℝ} (hr : r ≠ 0) :
    r * schwarzschildA rs r = r - rs := by
  unfold schwarzschildA
  field_simp [hr]

theorem schwarzschildRadius_eq {rs r : ℝ} (hr : r ≠ 0) :
    r * (1 - schwarzschildA rs r) = rs := by
  rw [mul_sub, mul_one, r_mul_schwarzschildA hr]
  ring

theorem schwarzschildA_injective_rs {rs₁ rs₂ r : ℝ} (hr : 0 < r) :
    schwarzschildA rs₁ r = schwarzschildA rs₂ r → rs₁ = rs₂ := by
  intro h
  have h1 := schwarzschildRadius_eq (show r ≠ 0 from hr.ne') (rs := rs₁)
  have h2 := schwarzschildRadius_eq (show r ≠ 0 from hr.ne') (rs := rs₂)
  rw [h] at h1
  exact h1.symm.trans h2

theorem hasDerivAt_r_mul_schwarzschildA (rs r : ℝ) (hr : r ≠ 0) :
    HasDerivAt (fun x => x * schwarzschildA rs x) 1 r := by
  have hfun : (fun x => x * schwarzschildA rs x) =ᶠ[𝓝 r] (fun x => x - rs) := by
    filter_upwards [eventually_ne_nhds hr] with x hx
    exact r_mul_schwarzschildA hx
  exact ((hasDerivAt_id r).sub_const rs).congr_of_eventuallyEq hfun

private theorem eq_of_hasDerivAt_zero_on_Icc {f : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (h : ∀ x ∈ Icc a b, HasDerivAt f 0 x) : f a = f b := by
  have hcont : ContinuousOn f (Icc a b) := fun x hx =>
    (h x hx).continuousAt.continuousWithinAt
  obtain ⟨c, hc, hEq⟩ :=
    exists_hasDerivAt_eq_slope f (fun _ => (0 : ℝ)) hab hcont
      (fun x hx => h x (Ioo_subset_Icc_self hx))
  have hden : b - a ≠ 0 := sub_ne_zero.mpr hab.ne'
  have hdiff : f b - f a = 0 :=
    (div_eq_zero_iff.mp hEq.symm).resolve_right hden
  exact (sub_eq_zero.mp hdiff).symm

/-- On an open ray \(r>c\ge 0\), the vacuum condition \(\frac{d}{dr}(rA)=1\)
forces \(A\) to be a Schwarzschild factor. -/
theorem eq_schwarzschildA_of_vacuum {A : ℝ → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hA : ∀ r ∈ Ioi c, HasDerivAt (fun x => x * A x) 1 r) :
    ∃ rs, ∀ r ∈ Ioi c, A r = schwarzschildA rs r := by
  let r0 : ℝ := c + 1
  have hr0 : r0 ∈ Ioi c := mem_Ioi.mpr (lt_add_one c)
  let g : ℝ → ℝ := fun x => x * A x - x
  have hg : ∀ r ∈ Ioi c, HasDerivAt g 0 r := fun r hr => by
    have h := (hA r hr).sub (hasDerivAt_id r)
    have hfun : ((fun x => x * A x) - id) = g := by
      ext x; simp [g, Pi.sub_apply]
    simpa [hfun] using h
  let rs : ℝ := r0 - r0 * A r0
  have hg_eq : ∀ r ∈ Ioi c, g r = g r0 := by
    intro r hr
    rcases lt_trichotomy r r0 with hlt | heq | hgt
    · have hIcc : Icc r r0 ⊆ Ioi c := fun x hx =>
        lt_of_lt_of_le (mem_Ioi.mp hr) hx.1
      exact eq_of_hasDerivAt_zero_on_Icc hlt fun x hx => hg x (hIcc hx)
    · rw [heq]
    · have hIcc : Icc r0 r ⊆ Ioi c := fun x hx =>
        lt_of_lt_of_le (mem_Ioi.mp hr0) hx.1
      exact (eq_of_hasDerivAt_zero_on_Icc hgt fun x hx => hg x (hIcc hx)).symm
  refine ⟨rs, fun r hr => ?_⟩
  have hrpos : 0 < r := lt_of_le_of_lt hc (mem_Ioi.mp hr)
  have hgr : r * A r - r = -rs := by
    have := hg_eq r hr
    change r * A r - r = r0 * A r0 - r0 at this
    linarith
  have : r * A r = r - rs := by linarith
  unfold schwarzschildA
  field_simp [hrpos.ne']
  linarith

/-! ### Newtonian sandwich -/

theorem schwarzschildRapidity_sandwich {rs r : ℝ} (h : IsExterior rs r) :
    rs / (2 * r) ≤ schwarzschildRapidity rs r ∧
      schwarzschildRapidity rs r ≤
        rs / (2 * r * schwarzschildA rs r) := by
  have hA := schwarzschildA_pos h
  have hrpos : 0 < r := lt_trans h.1 h.2
  have hlogA : Real.log (schwarzschildA rs r) ≤ schwarzschildA rs r - 1 :=
    Real.log_le_sub_one_of_pos hA
  have hAinv : 0 < (schwarzschildA rs r)⁻¹ := inv_pos.mpr hA
  have hlogInv :
      Real.log (schwarzschildA rs r)⁻¹ ≤
        (schwarzschildA rs r)⁻¹ - 1 :=
    Real.log_le_sub_one_of_pos hAinv
  have hrsr : rs / r = 1 - schwarzschildA rs r := by
    have := schwarzschildRadius_eq (rs := rs) hrpos.ne'
    exact (div_eq_iff hrpos.ne').mpr (by linarith)
  have hφ : schwarzschildRapidity rs r =
      -(1 / 2) * Real.log (schwarzschildA rs r) := by
    simp [schwarzschildRapidity, schwarzschildA]
  refine ⟨?_, ?_⟩
  · have hnewt : -(1 / 2) * (schwarzschildA rs r - 1) = rs / (2 * r) := by
      have : -(1 / 2) * (schwarzschildA rs r - 1) =
          (1 - schwarzschildA rs r) / 2 := by ring
      rw [this, ← hrsr]
      field_simp [hrpos.ne']; try ring
    rw [hφ, ← hnewt]
    nlinarith
  · have hlog : -Real.log (schwarzschildA rs r) =
        Real.log (schwarzschildA rs r)⁻¹ := (Real.log_inv _).symm
    have hle : -(1 / 2) * Real.log (schwarzschildA rs r) ≤
        (1 / 2) * ((schwarzschildA rs r)⁻¹ - 1) := by
      nlinarith [hlogInv, hlog]
    have hnewt : (1 / 2) * ((schwarzschildA rs r)⁻¹ - 1) =
        rs / (2 * r * schwarzschildA rs r) := by
      have : (1 / 2) * ((schwarzschildA rs r)⁻¹ - 1) =
          (1 - schwarzschildA rs r) / (2 * schwarzschildA rs r) := by
        field_simp [hA.ne']; try ring
      rw [this, ← hrsr]
      field_simp [hrpos.ne', hA.ne']; try ring
    rw [hφ, ← hnewt]
    exact hle

theorem tendsto_schwarzschildA_atTop (rs : ℝ) :
    Tendsto (schwarzschildA rs) atTop (𝓝 1) := by
  have hinv : Tendsto (fun r : ℝ => r⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have hquot : Tendsto (fun r : ℝ => rs / r) atTop (𝓝 0) := by
    simp only [div_eq_mul_inv]
    simpa using (tendsto_const_nhds (x := rs)).mul hinv
  unfold schwarzschildA
  simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hquot

theorem tendsto_r_mul_rapidity_atTop {rs : ℝ} (hrs : 0 < rs) :
    Tendsto (fun r => r * schwarzschildRapidity rs r) atTop (𝓝 (rs / 2)) := by
  have hlo : Tendsto (fun _ : ℝ => rs / 2) atTop (𝓝 (rs / 2)) :=
    tendsto_const_nhds
  have hA := tendsto_schwarzschildA_atTop rs
  have h2A : Tendsto (fun r : ℝ => 2 * schwarzschildA rs r) atTop (𝓝 2) := by
    simpa using hA.const_mul (2 : ℝ)
  have hhi : Tendsto (fun r : ℝ => rs / (2 * schwarzschildA rs r))
      atTop (𝓝 (rs / 2)) :=
    (tendsto_const_nhds (x := rs)).div h2A (by norm_num)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi ?_ ?_
  · filter_upwards [eventually_gt_atTop rs] with r hr
    have hex : IsExterior rs r := ⟨hrs, hr⟩
    have hrpos : 0 < r := lt_trans hrs hr
    have hlo' := (schwarzschildRapidity_sandwich hex).1
    have hmul : r * (rs / (2 * r)) = rs / 2 := by
      field_simp [hrpos.ne']; try ring
    calc rs / 2 = r * (rs / (2 * r)) := hmul.symm
      _ ≤ r * schwarzschildRapidity rs r :=
        mul_le_mul_of_nonneg_left hlo' hrpos.le
  · filter_upwards [eventually_gt_atTop rs] with r hr
    have hex : IsExterior rs r := ⟨hrs, hr⟩
    have hrpos : 0 < r := lt_trans hrs hr
    have hApos := schwarzschildA_pos hex
    have hhi' := (schwarzschildRapidity_sandwich hex).2
    have hmul :
        r * (rs / (2 * r * schwarzschildA rs r)) =
          rs / (2 * schwarzschildA rs r) := by
      field_simp [hrpos.ne', hApos.ne']; try ring
    calc r * schwarzschildRapidity rs r
        ≤ r * (rs / (2 * r * schwarzschildA rs r)) :=
          mul_le_mul_of_nonneg_left hhi' hrpos.le
      _ = rs / (2 * schwarzschildA rs r) := hmul

theorem tendsto_rapidity_div_newtonian {rs : ℝ} (hrs : 0 < rs) :
    Tendsto (fun r =>
        schwarzschildRapidity rs r / (rs / (2 * r))) atTop (𝓝 1) := by
  have h := tendsto_r_mul_rapidity_atTop hrs
  have h2 : Tendsto (fun r => 2 * r * schwarzschildRapidity rs r)
      atTop (𝓝 rs) := by
    have := h.const_mul (2 : ℝ)
    convert this using 2
    · ring
    · ring
  have hdiv : Tendsto (fun r => 2 * r * schwarzschildRapidity rs r / rs)
      atTop (𝓝 1) := by
    have := h2.div_const rs
    rwa [div_self hrs.ne'] at this
  refine hdiv.congr' ?_
  filter_upwards [eventually_gt_atTop rs] with r hr
  have hrpos : 0 < r := lt_trans hrs hr
  field_simp [hrs.ne', hrpos.ne']; try ring

/-! ### Far-field coefficients -/

theorem r_pow_four_mul_T_eq {rs r : ℝ} (h : IsExterior rs r) :
    r ^ 4 * schwarzschildTeleparallelT rs r =
      2 * (r * schwarzschildRapidity rs r) ^ 2 *
        (sinh (schwarzschildRapidity rs r / 2) /
          (schwarzschildRapidity rs r / 2)) ^ 2 := by
  have hrpos : 0 < r := lt_trans h.1 h.2
  have hφ := schwarzschildRapidity_pos h
  have hhalf : schwarzschildRapidity rs r / 2 ≠ 0 :=
    (div_pos hφ (by norm_num)).ne'
  have hφne : schwarzschildRapidity rs r ≠ 0 := hφ.ne'
  rw [schwarzschild_T_eq_sinh_half_sq h]
  have hne : r ^ 2 ≠ 0 := (sq_pos_of_pos hrpos).ne'
  field_simp [hne, hhalf, hφne]; try ring

theorem four_r_sq_mul_J_eq (rs r : ℝ) :
    4 * r ^ 2 * J (radialBoostParams rs r) =
      2 * (r * schwarzschildRapidity rs r) ^ 2 := by
  rw [J_radialBoostParams]
  ring

theorem tendsto_four_r_sq_mul_J {rs : ℝ} (hrs : 0 < rs) :
    Tendsto (fun r => 4 * r ^ 2 * J (radialBoostParams rs r))
      atTop (𝓝 (rs ^ 2 / 2)) := by
  have h := tendsto_r_mul_rapidity_atTop hrs
  have hsq : Tendsto (fun r => (r * schwarzschildRapidity rs r) ^ 2)
      atTop (𝓝 ((rs / 2) ^ 2)) := by
    simpa using h.pow 2
  have h2 : Tendsto (fun r => 2 * (r * schwarzschildRapidity rs r) ^ 2)
      atTop (𝓝 (2 * (rs / 2) ^ 2)) := by
    simpa using hsq.const_mul (2 : ℝ)
  have hval : 2 * (rs / 2) ^ 2 = rs ^ 2 / 2 := by ring
  rw [← hval]
  refine h2.congr' ?_
  filter_upwards with r
  exact (four_r_sq_mul_J_eq rs r).symm

theorem tendsto_r_pow_four_mul_T {rs : ℝ} (hrs : 0 < rs) :
    Tendsto (fun r => r ^ 4 * schwarzschildTeleparallelT rs r)
      atTop (𝓝 (rs ^ 2 / 2)) := by
  have hφ := tendsto_schwarzschildRapidity_atTop hrs
  have hψ : Tendsto (fun r : ℝ => schwarzschildRapidity rs r / 2)
      atTop (𝓝[≠] 0) := by
    have hψ0 : Tendsto (fun r : ℝ => schwarzschildRapidity rs r / 2)
        atTop (𝓝 0) := by
      simpa using hφ.div_const (2 : ℝ)
    refine tendsto_nhdsWithin_iff.mpr ⟨hψ0, ?_⟩
    filter_upwards [eventually_gt_atTop rs] with r hr
    exact div_ne_zero (schwarzschildRapidity_pos ⟨hrs, hr⟩).ne' (by norm_num)
  have hsinh : Tendsto (fun r : ℝ =>
      sinh (schwarzschildRapidity rs r / 2) /
        (schwarzschildRapidity rs r / 2)) atTop (𝓝 1) :=
    tendsto_sinh_div_self.comp hψ
  have hsq : Tendsto (fun r : ℝ =>
      (sinh (schwarzschildRapidity rs r / 2) /
        (schwarzschildRapidity rs r / 2)) ^ 2) atTop (𝓝 1) := by
    simpa using hsinh.pow 2
  have hrφ := tendsto_r_mul_rapidity_atTop hrs
  have hrφsq : Tendsto (fun r => (r * schwarzschildRapidity rs r) ^ 2)
      atTop (𝓝 ((rs / 2) ^ 2)) := by
    simpa using hrφ.pow 2
  have hprod : Tendsto (fun r =>
      2 * (r * schwarzschildRapidity rs r) ^ 2 *
        (sinh (schwarzschildRapidity rs r / 2) /
          (schwarzschildRapidity rs r / 2)) ^ 2)
      atTop (𝓝 (2 * (rs / 2) ^ 2 * 1)) := by
    have h2 := hrφsq.const_mul (2 : ℝ)
    simpa using h2.mul hsq
  have hval : 2 * (rs / 2) ^ 2 * 1 = rs ^ 2 / 2 := by ring
  rw [← hval]
  refine hprod.congr' ?_
  filter_upwards [eventually_gt_atTop rs] with r hr
  exact (r_pow_four_mul_T_eq ⟨hrs, hr⟩).symm

/-! ### Exterior layering -/

theorem schwarzschildA_strictMonoOn {rs : ℝ} (hrs : 0 < rs) :
    StrictMonoOn (schwarzschildA rs) (Ioi rs) := by
  intro r1 hr1 r2 hr2 hlt
  simp only [mem_Ioi] at hr1 hr2
  unfold schwarzschildA
  have hr1pos : 0 < r1 := hrs.trans hr1
  have hr2pos : 0 < r2 := hrs.trans hr2
  have : rs / r2 < rs / r1 :=
    (div_lt_div_iff₀ hr2pos hr1pos).mpr (by nlinarith)
  linarith

theorem J_radialBoost_strictAntiOn {rs : ℝ} (hrs : 0 < rs) :
    StrictAntiOn (fun r => J (radialBoostParams rs r)) (Ioi rs) := by
  intro r1 hr1 r2 hr2 hlt
  simp only [mem_Ioi] at hr1 hr2
  change J (radialBoostParams rs r2) < J (radialBoostParams rs r1)
  rw [J_radialBoostParams, J_radialBoostParams]
  have hφ := (schwarzschildRapidity_strictAntiOn hrs)
    (mem_Ioi.mpr hr1) (mem_Ioi.mpr hr2) hlt
  have h2 : IsExterior rs r2 := ⟨hrs, hr2⟩
  have hpos2 := schwarzschildRapidity_pos h2
  have hpos1 : 0 < schwarzschildRapidity rs r1 := hpos2.trans hφ
  nlinarith [sq_nonneg (schwarzschildRapidity rs r1),
    sq_nonneg (schwarzschildRapidity rs r2)]

theorem r_sq_T_strictAntiOn {rs : ℝ} (hrs : 0 < rs) :
    StrictAntiOn (fun r => r ^ 2 * schwarzschildTeleparallelT rs r)
      (Ioi rs) := by
  intro r1 hr1 r2 hr2 hlt
  simp only [mem_Ioi] at hr1 hr2
  have h1 : IsExterior rs r1 := ⟨hrs, hr1⟩
  have h2 : IsExterior rs r2 := ⟨hrs, hr2⟩
  have hr1pos : 0 < r1 := hrs.trans hr1
  have hr2pos : 0 < r2 := hrs.trans hr2
  change r2 ^ 2 * schwarzschildTeleparallelT rs r2 <
    r1 ^ 2 * schwarzschildTeleparallelT rs r1
  rw [schwarzschild_T_eq_cosh_rapidity h1, schwarzschild_T_eq_cosh_rapidity h2]
  have hφ := (schwarzschildRapidity_strictAntiOn hrs)
    (mem_Ioi.mpr hr1) (mem_Ioi.mpr hr2) hlt
  have hφ2 := schwarzschildRapidity_pos h2
  have hφ1 : 0 < schwarzschildRapidity rs r1 := hφ2.trans hφ
  have hcosh :
      cosh (schwarzschildRapidity rs r2) <
        cosh (schwarzschildRapidity rs r1) := by
    refine cosh_lt_cosh.mpr ?_
    rw [abs_of_pos hφ2, abs_of_pos hφ1]
    exact hφ
  have hne1 : r1 ^ 2 ≠ 0 := (sq_pos_of_pos hr1pos).ne'
  have hne2 : r2 ^ 2 ≠ 0 := (sq_pos_of_pos hr2pos).ne'
  field_simp [hne1, hne2]
  linarith

theorem schwarzschild_T_strictAntiOn {rs : ℝ} (hrs : 0 < rs) :
    StrictAntiOn (schwarzschildTeleparallelT rs) (Ioi rs) := by
  intro r1 hr1 r2 hr2 hlt
  simp only [mem_Ioi] at hr1 hr2
  have h1 : IsExterior rs r1 := ⟨hrs, hr1⟩
  have h2 : IsExterior rs r2 := ⟨hrs, hr2⟩
  have hr1pos : 0 < r1 := hrs.trans hr1
  have hr2pos : 0 < r2 := hrs.trans hr2
  rw [schwarzschild_T_eq_cosh_rapidity h1, schwarzschild_T_eq_cosh_rapidity h2]
  have hφ := (schwarzschildRapidity_strictAntiOn hrs)
    (mem_Ioi.mpr hr1) (mem_Ioi.mpr hr2) hlt
  have hφ2 := schwarzschildRapidity_pos h2
  have hφ1 : 0 < schwarzschildRapidity rs r1 := hφ2.trans hφ
  have hcosh :
      cosh (schwarzschildRapidity rs r2) - 1 <
        cosh (schwarzschildRapidity rs r1) - 1 := by
    have :
        cosh (schwarzschildRapidity rs r2) <
          cosh (schwarzschildRapidity rs r1) := by
      refine cosh_lt_cosh.mpr ?_
      rw [abs_of_pos hφ2, abs_of_pos hφ1]
      exact hφ
    linarith
  have hinv : 1 / r2 ^ 2 < 1 / r1 ^ 2 := by
    rw [one_div, one_div, inv_lt_inv₀ (sq_pos_of_pos hr2pos)
      (sq_pos_of_pos hr1pos)]
    exact pow_lt_pow_left₀ hlt hr1pos.le (by norm_num)
  have hnum2 : 0 < cosh (schwarzschildRapidity rs r2) - 1 := by
    have : 1 < cosh (schwarzschildRapidity rs r2) :=
      one_lt_cosh.mpr hφ2.ne'
    linarith
  have hden1 : 0 < 4 / r1 ^ 2 := by positivity
  have hden2 : 0 < 4 / r2 ^ 2 := by positivity
  have hscale : 4 / r2 ^ 2 < 4 / r1 ^ 2 := by
    have : (4 : ℝ) / r2 ^ 2 = 4 * (1 / r2 ^ 2) := by ring
    have : (4 : ℝ) / r1 ^ 2 = 4 * (1 / r1 ^ 2) := by ring
    nlinarith
  nlinarith [mul_pos hden2 hnum2]

/-! ### Horizon-side limits -/

private theorem tendsto_inv_pos_atTop :
    Tendsto (fun x : ℝ => x⁻¹) (𝓝[>] 0) atTop := by
  refine tendsto_atTop.2 fun b => ?_
  let c : ℝ := max b 1
  have hc : 0 < c := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
    (le_max_right b 1)
  have hmem : Ioo 0 c⁻¹ ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT (inv_pos.mpr hc)
  filter_upwards [hmem] with x hx
  have hx0 : 0 < x := hx.1
  have hxc : x < c⁻¹ := hx.2
  have hmul : x * c < 1 := by
    have : x * c < c⁻¹ * c := mul_lt_mul_of_pos_right hxc hc
    rwa [inv_mul_cancel₀ hc.ne'] at this
  have : c < x⁻¹ := by
    have hc1 : c * x < 1 := by rwa [mul_comm] at hmul
    have : c < 1 / x := (lt_div_iff₀ hx0).mpr hc1
    rwa [one_div] at this
  exact (le_max_left b 1).trans this.le

private theorem tendsto_cosh_atTop :
    Tendsto (fun x : ℝ => cosh x) atTop atTop := by
  have h : Tendsto (fun x : ℝ => (1 / 2) * Real.exp x) atTop atTop :=
    (Real.tendsto_exp_atTop).const_mul_atTop (by norm_num)
  refine tendsto_atTop_mono (fun x => ?_) h
  have : (1 / 2) * Real.exp x ≤ cosh x := by
    rw [Real.cosh_eq]
    nlinarith [exp_pos (-x)]
  exact this

private theorem tendsto_atTop_sub_const {α : Type*} {l : Filter α}
    {f : α → ℝ} (c : ℝ) (hf : Tendsto f l atTop) :
    Tendsto (fun x => f x - c) l atTop := by
  refine tendsto_atTop.2 fun b => ?_
  filter_upwards [tendsto_atTop.1 hf (b + c)] with x hx
  linarith

theorem tendsto_schwarzschildA_nhdsWithin_gt {rs : ℝ} (hrs : 0 < rs) :
    Tendsto (schwarzschildA rs) (𝓝[>] rs) (𝓝 0) := by
  have hd : ContinuousAt (fun r : ℝ => rs / r) rs :=
    continuousAt_const.div continuousAt_id hrs.ne'
  have hcont : ContinuousAt (fun r : ℝ => (1 : ℝ) - rs / r) rs :=
    continuousAt_const.sub hd
  have h : Tendsto (fun r : ℝ => (1 : ℝ) - rs / r) (𝓝 rs)
      (𝓝 (1 - rs / rs)) := hcont.tendsto
  rw [div_self hrs.ne', sub_self] at h
  change Tendsto (fun r => (1 : ℝ) - rs / r) (𝓝[>] rs) (𝓝 0)
  exact h.mono_left nhdsWithin_le_nhds

theorem tendsto_schwarzschildRapidity_nhdsWithin_gt {rs : ℝ}
    (hrs : 0 < rs) :
    Tendsto (schwarzschildRapidity rs) (𝓝[>] rs) atTop := by
  have hA : Tendsto (schwarzschildA rs) (𝓝[>] rs) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr
      ⟨tendsto_schwarzschildA_nhdsWithin_gt hrs, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact schwarzschildA_pos ⟨hrs, hr⟩
  have hinv : Tendsto (fun r => (schwarzschildA rs r)⁻¹) (𝓝[>] rs) atTop :=
    tendsto_inv_pos_atTop.comp hA
  have hlog : Tendsto (fun r => Real.log (schwarzschildA rs r)⁻¹)
      (𝓝[>] rs) atTop :=
    Real.tendsto_log_atTop.comp hinv
  have hhalf :
      Tendsto (fun r => (1 / 2 : ℝ) * Real.log (schwarzschildA rs r)⁻¹)
        (𝓝[>] rs) atTop :=
    hlog.const_mul_atTop (by norm_num)
  refine Tendsto.congr (fun r => ?_) hhalf
  simp [schwarzschildRapidity, schwarzschildA, Real.log_inv]
  try ring

theorem tendsto_r_sq_T_nhdsWithin_gt {rs : ℝ} (hrs : 0 < rs) :
    Tendsto (fun r => r ^ 2 * schwarzschildTeleparallelT rs r)
      (𝓝[>] rs) atTop := by
  have hφ := tendsto_schwarzschildRapidity_nhdsWithin_gt hrs
  have hcosh : Tendsto (fun r => cosh (schwarzschildRapidity rs r))
      (𝓝[>] rs) atTop :=
    tendsto_cosh_atTop.comp hφ
  have hsub : Tendsto (fun r => cosh (schwarzschildRapidity rs r) - 1)
      (𝓝[>] rs) atTop :=
    tendsto_atTop_sub_const 1 hcosh
  have h4 := hsub.const_mul_atTop (by norm_num : (0 : ℝ) < 4)
  refine h4.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hex : IsExterior rs r := ⟨hrs, hr⟩
  have hrpos : 0 < r := hrs.trans hr
  rw [schwarzschild_T_eq_cosh_rapidity hex]
  field_simp [hrpos.ne']; try ring

theorem tendsto_T_nhdsWithin_gt {rs : ℝ} (hrs : 0 < rs) :
    Tendsto (schwarzschildTeleparallelT rs) (𝓝[>] rs) atTop := by
  have hnum := tendsto_r_sq_T_nhdsWithin_gt hrs
  have hc : 0 < ((2 * rs) ^ 2)⁻¹ := by positivity
  have hr_lt : ∀ᶠ r in 𝓝[>] rs, r < 2 * rs :=
    eventually_nhdsWithin_of_eventually_nhds
      (eventually_lt_nhds (by nlinarith : rs < 2 * rs))
  have hmul := hnum.const_mul_atTop hc
  refine tendsto_atTop_mono' (𝓝[>] rs) ?_ hmul
  filter_upwards [hr_lt, self_mem_nhdsWithin] with r hlt hr
  have hex : IsExterior rs r := ⟨hrs, hr⟩
  have hrpos : 0 < r := hrs.trans hr
  have hnonneg : 0 ≤ r ^ 2 * schwarzschildTeleparallelT rs r :=
    mul_nonneg (sq_nonneg r) (schwarzschild_T_pos hex).le
  have hinv : ((2 * rs) ^ 2)⁻¹ ≤ (r ^ 2)⁻¹ := by
    rw [inv_le_inv₀ (by positivity) (sq_pos_of_pos hrpos)]
    exact pow_le_pow_left₀ hrpos.le hlt.le 2
  calc ((2 * rs) ^ 2)⁻¹ * (r ^ 2 * schwarzschildTeleparallelT rs r)
      ≤ (r ^ 2)⁻¹ * (r ^ 2 * schwarzschildTeleparallelT rs r) :=
        mul_le_mul_of_nonneg_right hinv hnonneg
    _ = schwarzschildTeleparallelT rs r := by
        field_simp [hrpos.ne']; try ring

/-! ### Exact witness \(r=\frac43 r_s\) -/

noncomputable def referenceRadius (rs : ℝ) : ℝ :=
  (4 / 3) * rs

theorem referenceRadius_exterior {rs : ℝ} (hrs : 0 < rs) :
    IsExterior rs (referenceRadius rs) := by
  unfold referenceRadius
  refine ⟨hrs, ?_⟩
  nlinarith

theorem schwarzschildA_reference {rs : ℝ} (hrs : 0 < rs) :
    schwarzschildA rs (referenceRadius rs) = 1 / 4 := by
  unfold schwarzschildA referenceRadius
  field_simp [hrs.ne']
  ring

theorem sqrt_schwarzschildA_reference {rs : ℝ} (hrs : 0 < rs) :
    Real.sqrt (schwarzschildA rs (referenceRadius rs)) = 1 / 2 := by
  rw [schwarzschildA_reference hrs,
    show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num,
    Real.sqrt_sq (by norm_num)]

theorem schwarzschildRapidity_reference {rs : ℝ} (hrs : 0 < rs) :
    schwarzschildRapidity rs (referenceRadius rs) = Real.log 2 := by
  have hA := schwarzschildA_reference hrs
  unfold schwarzschildRapidity
  rw [show 1 - rs / referenceRadius rs =
      schwarzschildA rs (referenceRadius rs) from rfl, hA]
  have hlog : Real.log (1 / 4) = -Real.log 4 := by
    rw [one_div, Real.log_inv]
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    have : (4 : ℝ) = 2 ^ (2 : ℕ) := by norm_num
    rw [this, Real.log_pow]
    norm_cast
  rw [hlog, h4]
  ring

theorem cosh_log_two : cosh (Real.log 2) = 5 / 4 := by
  rw [Real.cosh_eq, Real.exp_log (by norm_num : (0 : ℝ) < 2), Real.exp_neg,
    Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  field_simp
  ring

theorem r_sq_T_reference {rs : ℝ} (hrs : 0 < rs) :
    referenceRadius rs ^ 2 *
      schwarzschildTeleparallelT rs (referenceRadius rs) = 1 := by
  have h := referenceRadius_exterior hrs
  rw [schwarzschild_T_eq_cosh_via_gauge h, schwarzschildRapidity_reference hrs,
    cosh_log_two]
  have hr : referenceRadius rs ≠ 0 := (mul_pos (by norm_num : (0 : ℝ) < 4 / 3)
    hrs).ne'
  field_simp [hr]
  ring

theorem four_J_reference {rs : ℝ} (hrs : 0 < rs) :
    4 * J (radialBoostParams rs (referenceRadius rs)) =
      2 * (Real.log 2) ^ 2 := by
  rw [J_radialBoostParams, schwarzschildRapidity_reference hrs]
  ring

theorem two_mul_log_two_sq_lt_one : 2 * (Real.log 2) ^ 2 < 1 := by
  have hlog := Real.log_two_lt_d9
  have hpos : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  have hsq : (Real.log 2) ^ 2 < (0.6931471808 : ℝ) ^ 2 :=
    pow_lt_pow_left₀ hlog hpos (by norm_num)
  have hbound : 2 * (0.6931471808 : ℝ) ^ 2 < 1 := by norm_num
  linarith

/-- Strict sandwich \(4J<r^2 T\) at the reference sphere. -/
theorem four_J_lt_r_sq_T_reference {rs : ℝ} (hrs : 0 < rs) :
    4 * J (radialBoostParams rs (referenceRadius rs)) <
      referenceRadius rs ^ 2 *
        schwarzschildTeleparallelT rs (referenceRadius rs) := by
  rw [four_J_reference hrs, r_sq_T_reference hrs]
  exact two_mul_log_two_sq_lt_one

theorem r_sq_J_field_reference {rs : ℝ} (hrs : 0 < rs) :
    referenceRadius rs ^ 2 * J_field rs (referenceRadius rs) = 9 / 8 := by
  have h := referenceRadius_exterior hrs
  rw [J_field_coef h, schwarzschildA_reference hrs]
  unfold referenceRadius
  field_simp [hrs.ne']
  ring

theorem J_field_div_T_reference {rs : ℝ} (hrs : 0 < rs) :
    J_field rs (referenceRadius rs) /
      schwarzschildTeleparallelT rs (referenceRadius rs) = 9 / 8 := by
  have h := referenceRadius_exterior hrs
  have hT := (schwarzschild_T_pos h).ne'
  have hr : referenceRadius rs ≠ 0 :=
    (mul_pos (by norm_num : (0 : ℝ) < 4 / 3) hrs).ne'
  have hnum := r_sq_J_field_reference hrs
  have hden := r_sq_T_reference hrs
  have : J_field rs (referenceRadius rs) /
      schwarzschildTeleparallelT rs (referenceRadius rs) =
      (referenceRadius rs ^ 2 * J_field rs (referenceRadius rs)) /
        (referenceRadius rs ^ 2 *
          schwarzschildTeleparallelT rs (referenceRadius rs)) := by
    have hr2 : referenceRadius rs ^ 2 ≠ 0 := pow_ne_zero 2 hr
    field_simp [hr2, hT]
  rw [this, hnum, hden]
  ring

theorem T_lt_four_J_field_reference {rs : ℝ} (hrs : 0 < rs) :
    schwarzschildTeleparallelT rs (referenceRadius rs) <
      4 * J_field rs (referenceRadius rs) := by
  have h := referenceRadius_exterior hrs
  have hT := schwarzschild_T_pos h
  have hratio := J_field_div_T_reference hrs
  have : (1 / 4 : ℝ) < J_field rs (referenceRadius rs) /
      schwarzschildTeleparallelT rs (referenceRadius rs) := by
    rw [hratio]
    norm_num
  rw [div_lt_div_iff₀ (by norm_num : (0 : ℝ) < (4 : ℝ)) hT] at this
  linarith

end Gravity

end DstDiophantine
