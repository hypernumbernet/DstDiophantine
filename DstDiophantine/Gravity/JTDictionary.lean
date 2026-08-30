import DstDiophantine.Gravity.Weitzenbock
import DstDiophantine.Gravity.Sandwich
import DstDiophantine.Gravity.EventBoundary
import DstDiophantine.Algebra.Invariant
import DstDiophantine.Algebra.Amplification
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Factorial.Basic

/-!
# Closed-form \(J\)–\(T\) dictionary on the radial pure-boost chart

On the exterior Schwarzschild coframe, \(\sqrt{A}=e^{-\varphi}\) converts the
Weitzenböck scalar into a function of the finite-angle parameter \(J=\tfrac12\varphi^2\):

\[
T=\frac{4}{r^2}(\cosh\varphi-1),\qquad
r^2 T=4\bigl(\cosh\sqrt{2J}-1\bigr).
\]

The naive identifications \(J=\tfrac12 T\) and \(J_{\mathrm{field}}=\tfrac12 T\)
fail for two independent reasons: a missing length scale \(r^2\), and a
leading coefficient \(4\) rather than \(\tfrac12\). The corrected dictionary
is proved below, together with the sandwich \(4J/r^2\le T\le 4J_{\mathrm{field}}\),
the exact field-seed ratio, the sign continuation, and the admissible ceiling
on \(r^2 T\).

## Proved

* Chart identities \(T=(4/r^2)(\cosh\varphi-1)=(8/r^2)\sinh^2(\varphi/2)\).
* \(r^2 T=4(\cosh\sqrt{2J}-1)\) on the radial boost slice.
* Sandwich \(4J\le r^2 T\) and \(T\le 4J_{\mathrm{field}}\), both strict on the
  exterior; weak-field limit \(r^2 T/(4J)\to 1\).
* \(J_{\mathrm{field}}/T=(1+\sqrt{A})^2/(16 A^{3/2})\), strictly increasing in
  \(\varphi\), with infimum \(\tfrac14\). Hence \(J_{\mathrm{field}}=\tfrac12 T\)
  holds on at most one sphere.
* Analytic continuation \(E(J)=\cosh\sqrt{2J}-1\) has \(\operatorname{sign}E=\operatorname{sign}J\)
  on the admissible cone \(|J|\le 3\pi^2/8\).
* Under \(\varphi\le\varphi_{\max}\), \(r^2 T\le 4(\cosh\varphi_{\max}-1)\) with
  numerical envelope \(26<\cdots<27\). Classical Schwarzschild has unbounded
  \(r^2 T\) as \(r\to r_s^+\).
* Two-sided window on the admissible cone:
  \(4(\cos\varphi_{\max}-1)\le r^2 T\le 4(\cosh\varphi_{\max}-1)\), with
  \(-7.7<4(\cos\varphi_{\max}-1)<-7.6\); both ends are attained at
  \(J=\mp J_{\max}\), so \(-8<r^2 T<27\) is sharp in that sense.
* \(E\) is strictly monotone on the cone, hence \(T\) at a fixed radius
  determines \(J\), and the dictionary inverts in closed form as
  \(J=\tfrac12(\operatorname{arcosh}(1+\tfrac14 r^2 T))^2\) on the hyperbolic
  branch and \(J=-\tfrac12(\arccos(1+\tfrac14 r^2 T))^2\) on the elliptic one.

## Not claimed

* A dictionary for a general motor field (off-axis or with translations).
* Identification of the proposed action \(\int J\) with the TEGR integral of \(T\).
-/

namespace DstDiophantine

namespace Gravity

open Invariant Amplification Real Set Filter
open scoped Topology

/-! ### Hyperbolic identities -/

theorem cosh_sub_one_eq_two_sinh_half_sq (φ : ℝ) :
    cosh φ - 1 = 2 * sinh (φ / 2) ^ 2 := by
  have h := cosh_two_mul (φ / 2)
  rw [show 2 * (φ / 2) = φ by ring] at h
  have hsq := cosh_sq_sub_sinh_sq (φ / 2)
  linarith

theorem sinh_le_self_mul_cosh {x : ℝ} (hx : 0 ≤ x) :
    sinh x ≤ x * cosh x := by
  rcases eq_or_lt_of_le hx with rfl | hx0
  · simp
  set f : ℝ → ℝ := fun y => y * cosh y - sinh y
  have hf0 : f 0 = 0 := by simp [f]
  have hderiv : ∀ t, HasDerivAt f (t * sinh t) t := fun t => by
    have hmul := (hasDerivAt_id t).mul (hasDerivAt_cosh t)
    have : HasDerivAt f (1 * cosh t + t * sinh t - cosh t) t :=
      hmul.sub (hasDerivAt_sinh t)
    convert this using 1
    ring
  have hcont : ContinuousOn f (Icc 0 x) := fun t _ =>
    (hderiv t).continuousAt.continuousWithinAt
  obtain ⟨c, hc, hEq⟩ :=
    exists_hasDerivAt_eq_slope f (fun t => t * sinh t) hx0 hcont fun t _ => hderiv t
  have hxne : (x : ℝ) ≠ 0 := hx0.ne'
  have hfx : f x = x * (c * sinh c) := by
    have : c * sinh c = (f x - f 0) / (x - 0) := hEq
    simp only [hf0, sub_zero] at this
    field_simp [hxne] at this
    linarith
  have hpos : 0 ≤ c * sinh c :=
    mul_nonneg hc.1.le (sinh_nonneg_iff.mpr hc.1.le)
  have : 0 ≤ f x := by
    rw [hfx]
    exact mul_nonneg hx0.le hpos
  simpa [f] using this

/-! ### Rapidity positivity and \(\sqrt{A}=e^{-\varphi}\) -/

theorem schwarzschildRapidity_pos {rs r : ℝ} (h : IsExterior rs r) :
    0 < schwarzschildRapidity rs r := by
  have hA : 0 < 1 - rs / r := A_pos_of_exterior h.1 h.2
  have hA_lt : 1 - rs / r < 1 := by
    have : 0 < rs / r := div_pos h.1 (lt_trans h.1 h.2)
    linarith
  have hlog : Real.log (1 - rs / r) < 0 := Real.log_neg hA hA_lt
  unfold schwarzschildRapidity
  linarith

theorem sqrt_schwarzschildA_eq_exp_neg {rs r : ℝ} (h : IsExterior rs r) :
    Real.sqrt (schwarzschildA rs r) =
      Real.exp (-schwarzschildRapidity rs r) := by
  simpa [schwarzschildA] using (exp_neg_schwarzschildRapidity h.1 h.2).symm

theorem schwarzschildA_eq_exp_neg_two {rs r : ℝ} (h : IsExterior rs r) :
    schwarzschildA rs r = Real.exp (-(2 * schwarzschildRapidity rs r)) := by
  have hs := sqrt_schwarzschildA_eq_exp_neg h
  have hA := schwarzschildA_pos h
  have : (Real.sqrt (schwarzschildA rs r)) ^ 2 = schwarzschildA rs r :=
    Real.sq_sqrt hA.le
  rw [← this, hs, sq, ← Real.exp_add]
  ring_nf

/-! ### Closed form \(T=(4/r^2)(\cosh\varphi-1)\) -/

theorem schwarzschild_T_eq_cosh_rapidity {rs r : ℝ} (h : IsExterior rs r) :
    schwarzschildTeleparallelT rs r =
      (4 / r ^ 2) * (cosh (schwarzschildRapidity rs r) - 1) := by
  set φ := schwarzschildRapidity rs r
  set s := Real.sqrt (schwarzschildA rs r)
  have hs : s = Real.exp (-φ) := sqrt_schwarzschildA_eq_exp_neg h
  have hspos : 0 < s := by
    rw [hs]
    exact Real.exp_pos _
  have hrpos : 0 < r := lt_trans h.1 h.2
  have hsne : s ≠ 0 := hspos.ne'
  have hfrac : (1 - s) ^ 2 / s = 2 * (cosh φ - 1) := by
    have hexp : Real.exp φ = s⁻¹ := by
      rw [hs, Real.exp_neg, inv_inv]
    calc (1 - s) ^ 2 / s
        = s⁻¹ - 2 + s := by field_simp [hsne]; ring
      _ = Real.exp φ - 2 + Real.exp (-φ) := by rw [hexp, hs]
      _ = 2 * (cosh φ - 1) := by rw [Real.cosh_eq φ]; ring
  calc schwarzschildTeleparallelT rs r
      = (2 / r ^ 2) * (1 - s) ^ 2 / s := by
          unfold schwarzschildTeleparallelT; simp [s]
    _ = (2 / r ^ 2) * ((1 - s) ^ 2 / s) := by field_simp [hsne]
    _ = (2 / r ^ 2) * (2 * (cosh φ - 1)) := by rw [hfrac]
    _ = (4 / r ^ 2) * (cosh φ - 1) := by ring

theorem schwarzschild_T_eq_sinh_half_sq {rs r : ℝ} (h : IsExterior rs r) :
    schwarzschildTeleparallelT rs r =
      (8 / r ^ 2) * sinh (schwarzschildRapidity rs r / 2) ^ 2 := by
  rw [schwarzschild_T_eq_cosh_rapidity h, cosh_sub_one_eq_two_sinh_half_sq]
  ring

theorem schwarzschild_T_pos {rs r : ℝ} (h : IsExterior rs r) :
    0 < schwarzschildTeleparallelT rs r := by
  have hφ := schwarzschildRapidity_pos h
  have hrpos : 0 < r := lt_trans h.1 h.2
  rw [schwarzschild_T_eq_cosh_rapidity h]
  have hcosh : 1 < cosh (schwarzschildRapidity rs r) :=
    one_lt_cosh.mpr hφ.ne'
  positivity

/-! ### Analytic continuation of the dictionary kernel -/

/-- Entire continuation of \(\cosh\sqrt{2J}-1\): trigonometric for \(J<0\). -/
noncomputable def coshDefect (J : ℝ) : ℝ :=
  if 0 ≤ J then cosh (Real.sqrt (2 * J)) - 1
  else cos (Real.sqrt (-(2 * J))) - 1

/-- Radial-boost reconstruction \(T_{\mathrm{of}\,J}(J,r)=(4/r^2)\,E(J)\). -/
noncomputable def teleparallelTofJ (Jval r : ℝ) : ℝ :=
  (4 / r ^ 2) * coshDefect Jval

theorem coshDefect_of_nonneg {J : ℝ} (h : 0 ≤ J) :
    coshDefect J = cosh (Real.sqrt (2 * J)) - 1 := by
  simp [coshDefect, h]

theorem coshDefect_of_neg {J : ℝ} (h : J < 0) :
    coshDefect J = cos (Real.sqrt (-(2 * J))) - 1 := by
  have : ¬ 0 ≤ J := not_le.mpr h
  simp [coshDefect, this]

theorem coshDefect_zero : coshDefect 0 = 0 := by
  simp [coshDefect]

theorem coshDefect_pos_of_pos {J : ℝ} (h : 0 < J) : 0 < coshDefect J := by
  rw [coshDefect_of_nonneg h.le]
  have hsq : 0 < Real.sqrt (2 * J) :=
    Real.sqrt_pos.mpr (mul_pos (by norm_num) h)
  have : 1 < cosh (Real.sqrt (2 * J)) := one_lt_cosh.mpr hsq.ne'
  linarith

/-! ### Main dictionary \(r^2 T=4(\cosh\sqrt{2J}-1)\) -/

theorem sqrt_two_J_eq_rapidity {rs r : ℝ} (h : IsExterior rs r) :
    Real.sqrt (2 * J (radialBoostParams rs r)) = schwarzschildRapidity rs r := by
  have hφ := schwarzschildRapidity_pos h
  rw [J_radialBoostParams]
  have : 2 * ((1 / 2) * schwarzschildRapidity rs r ^ 2) =
      schwarzschildRapidity rs r ^ 2 := by ring
  rw [this, Real.sqrt_sq hφ.le]

theorem schwarzschild_T_eq_teleparallelTofJ {rs r : ℝ} (h : IsExterior rs r) :
    schwarzschildTeleparallelT rs r =
      teleparallelTofJ (J (radialBoostParams rs r)) r := by
  have hJ : 0 ≤ J (radialBoostParams rs r) := by
    rw [J_radialBoostParams]
    positivity
  unfold teleparallelTofJ
  rw [coshDefect_of_nonneg hJ, sqrt_two_J_eq_rapidity h,
    schwarzschild_T_eq_cosh_rapidity h]

theorem r_sq_T_eq_four_coshDefect {rs r : ℝ} (h : IsExterior rs r) :
    r ^ 2 * schwarzschildTeleparallelT rs r =
      4 * coshDefect (J (radialBoostParams rs r)) := by
  have hrpos : 0 < r := lt_trans h.1 h.2
  rw [schwarzschild_T_eq_teleparallelTofJ h]
  unfold teleparallelTofJ
  field_simp [hrpos.ne']

theorem r_sq_T_eq_four_cosh_sqrt {rs r : ℝ} (h : IsExterior rs r) :
    r ^ 2 * schwarzschildTeleparallelT rs r =
      4 * (cosh (Real.sqrt (2 * J (radialBoostParams rs r))) - 1) := by
  have hJ : 0 ≤ J (radialBoostParams rs r) := by
    rw [J_radialBoostParams]
    positivity
  rw [r_sq_T_eq_four_coshDefect h, coshDefect_of_nonneg hJ]

/-! ### Sandwich \(4J\le r^2 T\) -/

theorem four_J_lt_r_sq_T {rs r : ℝ} (h : IsExterior rs r) :
    4 * J (radialBoostParams rs r) <
      r ^ 2 * schwarzschildTeleparallelT rs r := by
  have hrpos : 0 < r := lt_trans h.1 h.2
  have hhalf : 0 < schwarzschildRapidity rs r / 2 :=
    div_pos (schwarzschildRapidity_pos h) (by norm_num)
  rw [J_radialBoostParams, schwarzschild_T_eq_sinh_half_sq h]
  set φ := schwarzschildRapidity rs r
  have hsq : (φ / 2) ^ 2 < sinh (φ / 2) ^ 2 := by
    refine sq_lt_sq.mpr ?_
    rw [abs_of_pos hhalf, abs_of_pos (sinh_pos_iff.mpr hhalf)]
    exact self_lt_sinh_iff.mpr hhalf
  have hne : r ^ 2 ≠ 0 := (sq_pos_of_pos hrpos).ne'
  field_simp [hne]
  nlinarith [sq_nonneg (sinh (φ / 2)), sq_nonneg φ]

theorem four_J_le_r_sq_T {rs r : ℝ} (h : IsExterior rs r) :
    4 * J (radialBoostParams rs r) ≤
      r ^ 2 * schwarzschildTeleparallelT rs r :=
  (four_J_lt_r_sq_T h).le

theorem r_sq_T_le_four_J_cosh {rs r : ℝ} (h : IsExterior rs r) :
    r ^ 2 * schwarzschildTeleparallelT rs r ≤
      4 * J (radialBoostParams rs r) * cosh (schwarzschildRapidity rs r) := by
  have hhalf : 0 ≤ schwarzschildRapidity rs r / 2 :=
    (div_pos (schwarzschildRapidity_pos h) (by norm_num)).le
  have hsinh := sinh_le_self_mul_cosh hhalf
  rw [J_radialBoostParams, schwarzschild_T_eq_sinh_half_sq h]
  set φ := schwarzschildRapidity rs r
  have hrpos : 0 < r := lt_trans h.1 h.2
  have hne : r ^ 2 ≠ 0 := (sq_pos_of_pos hrpos).ne'
  have hch : cosh (φ / 2) ^ 2 ≤ cosh φ := by
    have h2 := cosh_two_mul (φ / 2)
    rw [show 2 * (φ / 2) = φ by ring] at h2
    nlinarith [one_le_cosh (φ / 2), sq_nonneg (cosh (φ / 2) - 1)]
  have hsq : sinh (φ / 2) ^ 2 ≤ ((φ / 2) * cosh (φ / 2)) ^ 2 := by
    refine sq_le_sq.mpr ?_
    have hs : 0 ≤ sinh (φ / 2) := sinh_nonneg_iff.mpr hhalf
    have hc : 0 ≤ (φ / 2) * cosh (φ / 2) := mul_nonneg hhalf (cosh_pos _).le
    simpa [abs_of_nonneg hs, abs_of_nonneg hc] using hsinh
  field_simp [hne]
  nlinarith [sq_nonneg φ, sq_nonneg (cosh (φ / 2)), one_le_cosh φ]

/-! ### Weak-field limit \(r^2 T/(4J)\to 1\) -/

theorem r_sq_T_div_four_J_eq {rs r : ℝ} (h : IsExterior rs r) :
    r ^ 2 * schwarzschildTeleparallelT rs r /
        (4 * J (radialBoostParams rs r)) =
      (sinh (schwarzschildRapidity rs r / 2) /
        (schwarzschildRapidity rs r / 2)) ^ 2 := by
  have hrpos : 0 < r := lt_trans h.1 h.2
  have hhalf : schwarzschildRapidity rs r / 2 ≠ 0 :=
    (div_pos (schwarzschildRapidity_pos h) (by norm_num)).ne'
  rw [J_radialBoostParams, schwarzschild_T_eq_sinh_half_sq h]
  set φ := schwarzschildRapidity rs r
  have hne : r ^ 2 ≠ 0 := (sq_pos_of_pos hrpos).ne'
  field_simp [hne, hhalf]
  ring

theorem tendsto_sinh_div_self :
    Tendsto (fun x : ℝ => sinh x / x) (𝓝[≠] 0) (𝓝 1) := by
  have h := (hasDerivAt_sinh (0 : ℝ)).tendsto_slope
  simp only [cosh_zero] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  simp [slope, sinh_zero, sub_zero, smul_eq_mul, inv_mul_eq_div]

theorem tendsto_schwarzschildRapidity_atTop {rs : ℝ} (_hrs : 0 < rs) :
    Tendsto (schwarzschildRapidity rs) atTop (𝓝 0) := by
  have hinv : Tendsto (fun r : ℝ => r⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have hquot : Tendsto (fun r : ℝ => rs / r) atTop (𝓝 0) := by
    simp only [div_eq_mul_inv]
    simpa using (tendsto_const_nhds (x := rs)).mul hinv
  have hA : Tendsto (fun r : ℝ => (1 : ℝ) - rs / r) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hquot
  have hlog : Tendsto Real.log (𝓝 1) (𝓝 0) := by
    simpa [Real.log_one] using
      (continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto
  have hlogA : Tendsto (fun r : ℝ => Real.log (1 - rs / r)) atTop (𝓝 0) :=
    hlog.comp hA
  unfold schwarzschildRapidity
  simpa using hlogA.const_mul (-(1 / 2 : ℝ))

theorem tendsto_r_sq_T_div_four_J {rs : ℝ} (hrs : 0 < rs) :
    Tendsto (fun r : ℝ =>
        r ^ 2 * schwarzschildTeleparallelT rs r /
          (4 * J (radialBoostParams rs r))) atTop (𝓝 1) := by
  have hφ := tendsto_schwarzschildRapidity_atTop hrs
  have hψ : Tendsto (fun r : ℝ => schwarzschildRapidity rs r / 2)
      atTop (𝓝[≠] 0) := by
    have hψ0 : Tendsto (fun r : ℝ => schwarzschildRapidity rs r / 2) atTop (𝓝 0) := by
      simpa using hφ.div_const (2 : ℝ)
    refine tendsto_nhdsWithin_iff.mpr ⟨hψ0, ?_⟩
    filter_upwards [eventually_gt_atTop rs] with r hr
    have hex : IsExterior rs r := ⟨hrs, hr⟩
    exact div_ne_zero (schwarzschildRapidity_pos hex).ne' (by norm_num)
  have hsinh : Tendsto (fun r : ℝ =>
      sinh (schwarzschildRapidity rs r / 2) /
        (schwarzschildRapidity rs r / 2)) atTop (𝓝 1) :=
    tendsto_sinh_div_self.comp hψ
  have hsq : Tendsto (fun r : ℝ =>
      (sinh (schwarzschildRapidity rs r / 2) /
        (schwarzschildRapidity rs r / 2)) ^ 2) atTop (𝓝 1) := by
    simpa using hsinh.pow 2
  refine hsq.congr' ?_
  filter_upwards [eventually_gt_atTop rs] with r hr
  exact (r_sq_T_div_four_J_eq ⟨hrs, hr⟩).symm

/-! ### Exact field-seed ratio -/

/-- Field-seed / torsion ratio as a function of rapidity. -/
noncomputable def jFieldRatio (φ : ℝ) : ℝ :=
  Real.exp (2 * φ) * (cosh (φ / 2)) ^ 2 / 4

theorem jFieldRatio_zero : jFieldRatio 0 = 1 / 4 := by
  simp [jFieldRatio]

theorem jFieldRatio_eq_A {rs r : ℝ} (h : IsExterior rs r) :
    jFieldRatio (schwarzschildRapidity rs r) =
      (1 + Real.sqrt (schwarzschildA rs r)) ^ 2 /
        (16 * schwarzschildA rs r * Real.sqrt (schwarzschildA rs r)) := by
  set φ := schwarzschildRapidity rs r
  set s := Real.sqrt (schwarzschildA rs r)
  have hs : s = Real.exp (-φ) := sqrt_schwarzschildA_eq_exp_neg h
  have hA : schwarzschildA rs r = s ^ 2 := (Real.sq_sqrt (schwarzschildA_pos h).le).symm
  have hcosh : cosh (φ / 2) = (Real.exp (φ / 2) + Real.exp (-(φ / 2))) / 2 :=
    Real.cosh_eq (φ / 2)
  have hspos : 0 < s := by
    rw [hs]; exact Real.exp_pos _
  unfold jFieldRatio
  have hexpφ : Real.exp φ = s⁻¹ := by
    rw [hs, Real.exp_neg, inv_inv]
  have hexp2 : Real.exp (2 * φ) = s⁻¹ ^ 2 := by
    rw [show 2 * φ = φ + φ by ring, Real.exp_add, hexpφ, sq]
  have hcosh2 : (cosh (φ / 2)) ^ 2 = (Real.exp φ + 2 + Real.exp (-φ)) / 4 := by
    have ha : Real.exp (φ / 2) ^ 2 = Real.exp φ := by
      rw [pow_two, ← Real.exp_add]; congr 1; ring
    have hb : Real.exp (-(φ / 2)) ^ 2 = Real.exp (-φ) := by
      rw [pow_two, ← Real.exp_add]; congr 1; ring
    have hc : Real.exp (φ / 2) * Real.exp (-(φ / 2)) = 1 := by
      simp [← Real.exp_add]
    have hsq : (Real.exp (φ / 2) + Real.exp (-(φ / 2))) ^ 2 =
        Real.exp φ + 2 + Real.exp (-φ) := by
      calc (Real.exp (φ / 2) + Real.exp (-(φ / 2))) ^ 2
          = Real.exp (φ / 2) ^ 2 +
              2 * Real.exp (φ / 2) * Real.exp (-(φ / 2)) +
              Real.exp (-(φ / 2)) ^ 2 := by ring
        _ = Real.exp φ + 2 * 1 + Real.exp (-φ) := by
            rw [ha, hb, mul_assoc, hc]
        _ = Real.exp φ + 2 + Real.exp (-φ) := by ring
    rw [hcosh, div_pow, hsq]
    ring
  rw [hA, hexp2, hcosh2, hexpφ, hs]
  have hsne : s ≠ 0 := hspos.ne'
  field_simp [hsne]
  ring

theorem J_field_eq_jFieldRatio_mul_T {rs r : ℝ} (h : IsExterior rs r) :
    J_field rs r =
      jFieldRatio (schwarzschildRapidity rs r) *
        schwarzschildTeleparallelT rs r := by
  have hA := schwarzschildA_pos h
  have hrpos : 0 < r := lt_trans h.1 h.2
  have hr0 : r ≠ 0 := hrpos.ne'
  have hrs0 : rs ≠ 0 := h.1.ne'
  -- Direct computation from the \(A\)-forms.
  have hrsA : rs / r = 1 - schwarzschildA rs r := by
    unfold schwarzschildA
    field_simp [hr0]
    ring
  rw [J_field_coef h, jFieldRatio_eq_A h]
  simp only [schwarzschildTeleparallelT]
  set A := schwarzschildA rs r
  set s := Real.sqrt A
  have hs : 0 < s := Real.sqrt_pos.mpr hA
  have hs2 : s ^ 2 = A := Real.sq_sqrt hA.le
  have hrsr : rs = r * (1 - A) := by
    have h' := hrsA
    field_simp [hr0] at h'
    linarith
  have h1A : 1 - A = (1 - s) * (1 + s) := by nlinarith [hs2]
  have hsm1 : 1 - s ≠ 0 := by
    intro hseq
    have hA1 : A = 1 := by rw [← hs2, show s = 1 by linarith, one_pow]
    exact hrs0 (by rw [hrsr, hA1]; ring)
  field_simp [hr0, hA.ne', hs.ne', hsm1]
  rw [hrsr, h1A, hs2]
  ring

theorem J_field_div_T_eq {rs r : ℝ} (h : IsExterior rs r) :
    J_field rs r / schwarzschildTeleparallelT rs r =
      (1 + Real.sqrt (schwarzschildA rs r)) ^ 2 /
        (16 * schwarzschildA rs r * Real.sqrt (schwarzschildA rs r)) := by
  have hT := (schwarzschild_T_pos h).ne'
  rw [J_field_eq_jFieldRatio_mul_T h, jFieldRatio_eq_A h]
  field_simp [hT]

/-! ### \(T\le 4 J_{\mathrm{field}}\) -/

theorem T_lt_four_J_field {rs r : ℝ} (h : IsExterior rs r) :
    schwarzschildTeleparallelT rs r < 4 * J_field rs r := by
  have hT := schwarzschild_T_pos h
  have hA := schwarzschildA_pos h
  have hs : 0 < Real.sqrt (schwarzschildA rs r) := Real.sqrt_pos.mpr hA
  have hratio := J_field_div_T_eq h
  set s := Real.sqrt (schwarzschildA rs r)
  have hs2 : s ^ 2 = schwarzschildA rs r := Real.sq_sqrt hA.le
  have hA_lt : schwarzschildA rs r < 1 := by
    unfold schwarzschildA
    have : 0 < rs / r := div_pos h.1 (lt_trans h.1 h.2)
    linarith
  have hs1 : s < 1 := (sq_lt_one_iff₀ hs.le).mp (hs2.trans_lt hA_lt)
  have hge : (1 / 4 : ℝ) < J_field rs r / schwarzschildTeleparallelT rs r := by
    rw [hratio]
    have hden : 0 < 16 * schwarzschildA rs r * s := by positivity
    rw [div_lt_div_iff₀ (by norm_num : (0 : ℝ) < 4) hden]
    rw [show schwarzschildA rs r = s ^ 2 from hs2.symm]
    have hfac : (1 + s) ^ 2 - 4 * s ^ 3 = (1 - s) * (4 * s ^ 2 + 3 * s + 1) := by
      ring
    have : 0 < (1 + s) ^ 2 - 4 * s ^ 3 := by
      rw [hfac]
      exact mul_pos (sub_pos.mpr hs1) (by positivity)
    nlinarith
  rw [div_lt_div_iff₀ (by norm_num : (0 : ℝ) < (4 : ℝ)) hT] at hge
  linarith

theorem T_le_four_J_field {rs r : ℝ} (h : IsExterior rs r) :
    schwarzschildTeleparallelT rs r ≤ 4 * J_field rs r :=
  (T_lt_four_J_field h).le

/-! ### Strict monotonicity of the ratio; at most one naive sphere -/

private theorem hasDerivAt_jFieldNum (x : ℝ) :
    HasDerivAt (fun y => Real.exp (2 * y) * (cosh (y / 2)) ^ 2)
      (Real.exp (2 * x) * 2 * (cosh (x / 2)) ^ 2 +
        Real.exp (2 * x) * (2 * cosh (x / 2) ^ 1 * (sinh (x / 2) * (1 / 2)))) x := by
  have hexp : HasDerivAt (fun y => Real.exp (2 * y)) (Real.exp (2 * x) * 2) x := by
    simpa [Function.comp_def] using
      (Real.hasDerivAt_exp (2 * x)).comp x ((hasDerivAt_id x).const_mul (2 : ℝ))
  have hhalf : HasDerivAt (fun y => y / 2) ((1 : ℝ) / 2) x :=
    (hasDerivAt_id x).div_const 2
  have hcosh : HasDerivAt (fun y => cosh (y / 2)) (sinh (x / 2) * (1 / 2)) x := by
    simpa [Function.comp_def] using (hasDerivAt_cosh (x / 2)).comp x hhalf
  have hsq : HasDerivAt (fun y => (cosh (y / 2)) ^ 2)
      (2 * cosh (x / 2) ^ 1 * (sinh (x / 2) * (1 / 2))) x := by
    simpa [Function.comp_def] using
      (hasDerivAt_pow 2 (cosh (x / 2))).comp x hcosh
  exact hexp.mul hsq

private theorem jFieldNum_deriv_pos (x : ℝ) :
    0 < Real.exp (2 * x) * 2 * (cosh (x / 2)) ^ 2 +
      Real.exp (2 * x) * (2 * cosh (x / 2) ^ 1 * (sinh (x / 2) * (1 / 2))) := by
  have hfact :
      Real.exp (2 * x) * 2 * (cosh (x / 2)) ^ 2 +
        Real.exp (2 * x) * (2 * cosh (x / 2) ^ 1 * (sinh (x / 2) * (1 / 2))) =
        Real.exp (2 * x) * cosh (x / 2) * (2 * cosh (x / 2) + sinh (x / 2)) := by
    ring
  have hform : 2 * cosh (x / 2) + sinh (x / 2) =
      (3 * Real.exp (x / 2) + Real.exp (-(x / 2))) / 2 := by
    rw [Real.cosh_eq, Real.sinh_eq]; ring
  rw [hfact, hform]
  positivity

theorem jFieldRatio_strictMono : StrictMono jFieldRatio := by
  have hnum :
      StrictMono (fun y => Real.exp (2 * y) * (cosh (y / 2)) ^ 2) := by
    refine strictMono_of_deriv_pos fun x => ?_
    rw [(hasDerivAt_jFieldNum x).deriv]
    exact jFieldNum_deriv_pos x
  intro a b hab
  unfold jFieldRatio
  linarith [hnum hab]

theorem schwarzschildRapidity_strictAntiOn {rs : ℝ} (hrs : 0 < rs) :
    StrictAntiOn (schwarzschildRapidity rs) (Ioi rs) := by
  intro r1 hr1 r2 hr2 hlt
  simp only [Set.mem_Ioi] at hr1 hr2
  unfold schwarzschildRapidity
  have hr1pos : 0 < r1 := hrs.trans hr1
  have hr2pos : 0 < r2 := hrs.trans hr2
  have hA1 : 0 < 1 - rs / r1 := A_pos_of_exterior hrs hr1
  have hA2 : 0 < 1 - rs / r2 := A_pos_of_exterior hrs hr2
  have hA : 1 - rs / r1 < 1 - rs / r2 := by
    have : rs / r2 < rs / r1 :=
      (div_lt_div_iff₀ hr2pos hr1pos).mpr (by nlinarith)
    linarith
  have hlog : Real.log (1 - rs / r1) < Real.log (1 - rs / r2) :=
    Real.log_lt_log hA1 hA
  linarith

theorem naive_half_ratio_at_most_one_sphere {rs r1 r2 : ℝ}
    (h1 : IsExterior rs r1) (h2 : IsExterior rs r2)
    (heq1 : J_field rs r1 = (1 / 2) * schwarzschildTeleparallelT rs r1)
    (heq2 : J_field rs r2 = (1 / 2) * schwarzschildTeleparallelT rs r2) :
    r1 = r2 := by
  have ratio_of {r : ℝ} (hr : IsExterior rs r)
      (heq : J_field rs r = (1 / 2) * schwarzschildTeleparallelT rs r) :
      jFieldRatio (schwarzschildRapidity rs r) = 1 / 2 := by
    have hT := (schwarzschild_T_pos hr).ne'
    have := J_field_eq_jFieldRatio_mul_T hr
    rw [heq] at this
    exact mul_right_cancel₀ hT this.symm
  have hφ :
      schwarzschildRapidity rs r1 = schwarzschildRapidity rs r2 :=
    jFieldRatio_strictMono.injective
      ((ratio_of h1 heq1).trans (ratio_of h2 heq2).symm)
  exact (schwarzschildRapidity_strictAntiOn h1.1).injOn
    (Set.mem_Ioi.mpr h1.2) (Set.mem_Ioi.mpr h2.2) hφ

/-! ### Sign continuation on the admissible cone -/

/-! Numeric envelopes for \(\pi\) and \(\sqrt3\), shared by the bounds below. -/

private theorem pi_gt_314 : (314 : ℝ) / 100 < Real.pi := by
  convert Real.pi_gt_d2 using 1
  norm_num

private theorem pi_lt_31416 : Real.pi < (31416 : ℝ) / 10000 := by
  convert Real.pi_lt_d4 using 1
  norm_num

private theorem sqrt_three_lt_two : Real.sqrt 3 < 2 :=
  (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)

private theorem sqrt_three_lt_1733 : Real.sqrt 3 < (1733 : ℝ) / 1000 :=
  (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)

private theorem sqrt_three_gt_1732 : (1732 : ℝ) / 1000 < Real.sqrt 3 :=
  Real.lt_sqrt_of_sq_lt (by norm_num)

theorem phiMax_lt_pi : phiMax < Real.pi := by
  unfold phiMax
  nlinarith [Real.pi_pos, sqrt_three_lt_two]

theorem JMax_pos : (0 : ℝ) < JMax := by
  unfold JMax
  positivity

/-- The admissible ceiling inverts to exactly the quasi-horizon rapidity. -/
theorem sqrt_two_JMax : Real.sqrt (2 * JMax) = phiMax := by
  unfold JMax phiMax
  have hsq : (Real.pi * Real.sqrt 3 / 2) ^ 2 = 2 * (3 * Real.pi ^ 2 / 8) := by
    field_simp
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    ring
  exact (Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)).mpr hsq.symm

/-- On the admissible cone the dictionary argument never leaves `[0, φ_max]`. -/
theorem sqrt_two_abs_le_phiMax {J : ℝ} (hbound : |J| ≤ JMax) :
    Real.sqrt (2 * |J|) ≤ phiMax := by
  rw [← sqrt_two_JMax]
  exact Real.sqrt_le_sqrt (by linarith)

theorem coshDefect_neg_of_admissible {J : ℝ}
    (hJ : J < 0) (hbound : |J| ≤ JMax) :
    coshDefect J < 0 := by
  rw [coshDefect_of_neg hJ]
  have habs : -(2 * J) = 2 * |J| := by
    rw [abs_of_neg hJ]; ring
  have hθ0 : 0 < Real.sqrt (-(2 * J)) :=
    Real.sqrt_pos.mpr (by linarith)
  have hθle : Real.sqrt (-(2 * J)) ≤ phiMax := by
    rw [habs]
    exact sqrt_two_abs_le_phiMax hbound
  have hθπ : Real.sqrt (-(2 * J)) ≤ Real.pi :=
    le_of_lt (lt_of_le_of_lt hθle phiMax_lt_pi)
  have hcos : cos (Real.sqrt (-(2 * J))) < cos 0 :=
    cos_lt_cos_of_nonneg_of_le_pi (le_refl (0 : ℝ)) hθπ hθ0
  simpa [cos_zero] using sub_lt_sub_right hcos 1

theorem sign_coshDefect_eq_sign_J {J : ℝ} (hbound : |J| ≤ JMax) :
    SignType.sign (coshDefect J) = SignType.sign J := by
  rcases lt_trichotomy J 0 with hJ | rfl | hJ
  · have hneg := coshDefect_neg_of_admissible hJ hbound
    rw [sign_neg hJ, sign_neg hneg]
  · simp [coshDefect_zero]
  · have hpos := coshDefect_pos_of_pos hJ
    rw [sign_pos hJ, sign_pos hpos]

theorem sign_T_eq_sign_J_on_cone {Jval r : ℝ} (hr : r ≠ 0)
    (hbound : |Jval| ≤ JMax) :
    SignType.sign (teleparallelTofJ Jval r) = SignType.sign Jval := by
  unfold teleparallelTofJ
  have hpos : 0 < 4 / r ^ 2 := by positivity
  rw [sign_mul, sign_pos hpos, one_mul]
  exact sign_coshDefect_eq_sign_J hbound

/-! ### Admissible ceiling on \(r^2 T\) -/

/-- A rapidity ceiling caps \(r^2 T\); both admissible envelopes specialise this. -/
theorem r_sq_T_le_of_rapidity_le {rs r c : ℝ} (h : IsExterior rs r)
    (hφ : schwarzschildRapidity rs r ≤ c) :
    r ^ 2 * schwarzschildTeleparallelT rs r ≤ 4 * (cosh c - 1) := by
  have hφ0 := (schwarzschildRapidity_pos h).le
  have hch : cosh (schwarzschildRapidity rs r) ≤ cosh c :=
    cosh_le_cosh.mpr (by rwa [abs_of_nonneg hφ0, abs_of_nonneg (hφ0.trans hφ)])
  have hrpos : 0 < r := lt_trans h.1 h.2
  rw [schwarzschild_T_eq_cosh_rapidity h]
  field_simp [hrpos.ne']
  linarith

theorem r_sq_T_le_ceiling {rs r : ℝ} (h : IsExterior rs r)
    (hφ : schwarzschildRapidity rs r ≤ phiMax) :
    r ^ 2 * schwarzschildTeleparallelT rs r ≤ 4 * (cosh phiMax - 1) :=
  r_sq_T_le_of_rapidity_le h hφ

theorem r_sq_T_le_one_axis_ceiling {rs r : ℝ} (h : IsExterior rs r)
    (hφ : schwarzschildRapidity rs r ≤ Real.pi / 2) :
    r ^ 2 * schwarzschildTeleparallelT rs r ≤
      4 * (cosh (Real.pi / 2) - 1) :=
  r_sq_T_le_of_rapidity_le h hφ

private theorem log_fifteen_lt_phiMax : Real.log 15 < phiMax := by
  have hlog : Real.log 15 < (27080502014 : ℝ) / 10000000000 := by
    rw [show (15 : ℝ) = 3 * 5 by norm_num,
      Real.log_mul (by norm_num) (by norm_num)]
    linarith [Real.log_three_lt_d9, Real.log_five_lt_d9]
  have hmul : (314 : ℝ) / 100 * (1732 / 1000) < Real.pi * Real.sqrt 3 :=
    mul_lt_mul pi_gt_314 sqrt_three_gt_1732.le (by positivity) Real.pi_pos.le
  have hφ : (314 : ℝ) / 100 * (1732 / 1000) / 2 < phiMax := by
    unfold phiMax
    exact (div_lt_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 2)).mpr hmul
  have hnum : (27080502014 : ℝ) / 10000000000 <
      (314 : ℝ) / 100 * (1732 / 1000) / 2 := by norm_num
  linarith

private theorem exp_phiMax_gt_fifteen : (15 : ℝ) < Real.exp phiMax := by
  have := Real.exp_lt_exp.mpr log_fifteen_lt_phiMax
  rwa [Real.exp_log (by norm_num : (0 : ℝ) < 15)] at this

private theorem phiMax_lt_2723_over_1000 : phiMax < (2723 : ℝ) / 1000 := by
  unfold phiMax
  have hmul : Real.pi * Real.sqrt 3 < (31416 / 10000) * (1733 / 1000) :=
    mul_lt_mul pi_lt_31416 sqrt_three_lt_1733.le (by positivity) (by positivity)
  have : (31416 / 10000 : ℝ) * (1733 / 1000) / 2 < 2723 / 1000 := by norm_num
  linarith

private theorem exp_le_taylor3 {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.exp x ≤ 1 + x + x ^ 2 / 2 + x ^ 3 * 4 / (6 * 3) := by
  have hbound := Real.exp_bound' hx0 hx1 (n := 3) (by norm_num)
  have hsum :
      (∑ m ∈ Finset.range 3, x ^ m / m.factorial) =
        1 + x + x ^ 2 / 2 := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_zero]
    simp only [pow_zero, pow_one, Nat.factorial_zero, Nat.factorial_succ, Nat.cast_succ,
      Nat.cast_zero, Nat.zero_add, mul_one]
    ring
  have hfac : (Nat.factorial 3 : ℝ) = 6 := by
    rw [Nat.factorial_succ, Nat.factorial_succ, Nat.factorial_succ, Nat.factorial_zero]
    norm_num
  have hrem : x ^ 3 * ((3 : ℝ) + 1) / ((Nat.factorial 3 : ℝ) * 3) =
      x ^ 3 * 4 / (6 * 3) := by
    rw [hfac]; ring
  calc Real.exp x
      ≤ (∑ m ∈ Finset.range 3, x ^ m / m.factorial) +
          x ^ 3 * ((3 : ℝ) + 1) / ((Nat.factorial 3 : ℝ) * 3) := hbound
    _ = 1 + x + x ^ 2 / 2 + x ^ 3 * 4 / (6 * 3) := by
        rw [hsum, hrem]

/-- Numeric wrapper: a `norm_num`-checkable third-order bound on `exp`. -/
private theorem exp_lt_of_taylor3 {x c : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hc : 1 + x + x ^ 2 / 2 + x ^ 3 * 4 / (6 * 3) < c) : Real.exp x < c :=
  (exp_le_taylor3 hx0 hx1).trans_lt hc

private theorem exp_723_over_1000_lt :
    Real.exp (723 / 1000) < (207 : ℝ) / 100 :=
  exp_lt_of_taylor3 (by norm_num) (by norm_num) (by norm_num)

private theorem exp_two_lt : Real.exp 2 < (739 : ℝ) / 100 := by
  have he2 : Real.exp 2 = Real.exp 1 ^ 2 := by
    rw [sq, ← Real.exp_add]; ring_nf
  rw [he2]
  have h1 := Real.exp_one_lt_d9
  have hpow : Real.exp 1 ^ 2 < (2.7182818286 : ℝ) ^ 2 :=
    pow_lt_pow_left₀ h1 (Real.exp_pos 1).le (by norm_num : (2 : ℕ) ≠ 0)
  have hbound : (2.7182818286 : ℝ) ^ 2 < (739 : ℝ) / 100 := by
    norm_num
  exact hpow.trans hbound

private theorem exp_phiMax_lt : Real.exp phiMax < (1543 : ℝ) / 100 := by
  have hexp : Real.exp phiMax < Real.exp (2723 / 1000) :=
    Real.exp_lt_exp.mpr phiMax_lt_2723_over_1000
  have hprod : Real.exp (2723 / 1000) = Real.exp 2 * Real.exp (723 / 1000) := by
    rw [show (2723 : ℝ) / 1000 = 2 + 723 / 1000 by norm_num, Real.exp_add]
  have : Real.exp 2 * Real.exp (723 / 1000) <
      (739 / 100) * (207 / 100) :=
    mul_lt_mul exp_two_lt exp_723_over_1000_lt.le (by positivity) (by positivity)
  have hnum : (739 / 100 : ℝ) * (207 / 100) < 1543 / 100 := by
    norm_num
  linarith

private theorem four_cosh_sub_one_eq (x : ℝ) :
    4 * (cosh x - 1) = 2 * (Real.exp x + Real.exp (-x) - 2) := by
  rw [Real.cosh_eq]; ring

theorem four_cosh_phiMax_sub_one_bounds :
    (26 : ℝ) < 4 * (cosh phiMax - 1) ∧ 4 * (cosh phiMax - 1) < 27 := by
  have hlo := exp_phiMax_gt_fifteen
  rw [four_cosh_sub_one_eq]
  refine ⟨by nlinarith [Real.exp_pos (-phiMax)], ?_⟩
  have hneg : Real.exp (-phiMax) < (1 / 15 : ℝ) := by
    rw [Real.exp_neg, one_div]
    exact (inv_lt_inv₀ (Real.exp_pos _) (by positivity)).mpr hlo
  linarith [exp_phiMax_lt]

private theorem exp_pi_div_two_split :
    Real.exp (Real.pi / 2) = Real.exp 1 * Real.exp (Real.pi / 2 - 1) := by
  rw [← Real.exp_add]; ring_nf

private theorem pi_div_two_sub_one_lt : Real.pi / 2 - 1 < (571 : ℝ) / 1000 := by
  linarith [pi_lt_31416]

private theorem exp_571_over_1000_lt :
    Real.exp (571 / 1000) < (1776 : ℝ) / 1000 :=
  exp_lt_of_taylor3 (by norm_num) (by norm_num) (by norm_num)

theorem four_cosh_half_pi_sub_one_lt :
    4 * (cosh (Real.pi / 2) - 1) < (61 : ℝ) / 10 := by
  have hexp : Real.exp (Real.pi / 2) < (483 : ℝ) / 100 := by
    have hlt : Real.exp (Real.pi / 2) < Real.exp 1 * Real.exp (571 / 1000) := by
      rw [exp_pi_div_two_split]
      exact mul_lt_mul_of_pos_left (Real.exp_lt_exp.mpr pi_div_two_sub_one_lt)
        (Real.exp_pos 1)
    have hprod : Real.exp 1 * Real.exp (571 / 1000) <
        (2.7182818286 : ℝ) * (1776 / 1000) :=
      mul_lt_mul Real.exp_one_lt_d9 exp_571_over_1000_lt.le (by positivity)
        (by positivity)
    have hnum : (2.7182818286 : ℝ) * (1776 / 1000) < 483 / 100 := by norm_num
    linarith
  have hneg : Real.exp (-(Real.pi / 2)) < (213 : ℝ) / 1000 := by
    have hlo : (1000 : ℝ) / 213 < Real.exp (Real.pi / 2) := by
      have harg : (57 : ℝ) / 100 < Real.pi / 2 - 1 := by linarith [pi_gt_314]
      have hprod : Real.exp 1 * Real.exp (57 / 100) ≤
          Real.exp 1 * Real.exp (Real.pi / 2 - 1) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr harg.le) (Real.exp_pos 1).le
      have hsplit := exp_pi_div_two_split
      have hnum : (1000 : ℝ) / 213 <
          (2.7182818283 : ℝ) * (1 + 57 / 100 + (57 / 100) ^ 2 / 2) := by
        norm_num
      have : (2.7182818283 : ℝ) * (1 + 57 / 100 + (57 / 100) ^ 2 / 2) ≤
          Real.exp 1 * Real.exp (57 / 100) :=
        mul_le_mul Real.exp_one_gt_d9.le
          (Real.quadratic_le_exp_of_nonneg (by norm_num)) (by positivity)
          (Real.exp_pos 1).le
      linarith
    rw [Real.exp_neg, show (213 / 1000 : ℝ) = (1000 / 213)⁻¹ by norm_num]
    exact (inv_lt_inv₀ (Real.exp_pos _) (by positivity)).mpr hlo
  rw [four_cosh_sub_one_eq]
  linarith

theorem classical_r_sq_T_unbounded {rs : ℝ} (hrs : 0 < rs) (M : ℝ) :
    ∃ r, IsExterior rs r ∧ M < r ^ 2 * schwarzschildTeleparallelT rs r := by
  let t : ℝ := |M| + 1
  let s : ℝ := 1 / (4 * t)
  have ht : 0 < t := by unfold t; positivity
  have hs_pos : 0 < s := by unfold s; positivity
  have hs_lt : s < (1 / 2 : ℝ) := by
    have ht1 : (1 : ℝ) ≤ t := by
      unfold t; nlinarith [abs_nonneg M]
    unfold s
    have hden : (2 : ℝ) < 4 * t := by nlinarith
    exact div_lt_div_of_pos_left (by norm_num) (by positivity) hden
  let A : ℝ := s ^ 2
  have hA_lt : A < 1 := by
    unfold A
    nlinarith [hs_lt]
  have h1A : 0 < 1 - A := sub_pos.mpr hA_lt
  let r : ℝ := rs / (1 - A)
  have hr : IsExterior rs r := by
    refine ⟨hrs, ?_⟩
    unfold r
    rw [lt_div_iff₀ h1A]
    nlinarith [mul_pos hrs (sq_pos_of_pos hs_pos)]
  have hr2T : r ^ 2 * schwarzschildTeleparallelT rs r =
      2 * (1 - Real.sqrt (schwarzschildA rs r)) ^ 2 /
        Real.sqrt (schwarzschildA rs r) := by
    simp only [schwarzschildTeleparallelT]
    have hrpos : 0 < r := lt_trans hr.1 hr.2
    field_simp [hrpos.ne']
  have hAeq : schwarzschildA rs r = A := by
    unfold schwarzschildA r A
    field_simp [hrs.ne', h1A.ne']
    ring
  have hsqrt : Real.sqrt (schwarzschildA rs r) = s := by
    rw [hAeq]; exact Real.sqrt_sq hs_pos.le
  have hval : r ^ 2 * schwarzschildTeleparallelT rs r = 2 * (1 - s) ^ 2 / s := by
    rw [hr2T, hsqrt]
  have hlower : 1 / (2 * s) ≤ 2 * (1 - s) ^ 2 / s := by
    have : (1 / 4 : ℝ) ≤ (1 - s) ^ 2 := by
      have : (1 / 2 : ℝ) ≤ 1 - s := by linarith [hs_lt.le]
      nlinarith
    have hs0 : 0 < s := hs_pos
    rw [div_le_div_iff₀ (mul_pos (by norm_num) hs0) hs0]
    nlinarith
  have hM : M < 1 / (2 * s) := by
    have hval2 : 1 / (2 * s) = 2 * (|M| + 1) := by
      change 1 / (2 * (1 / (4 * (|M| + 1)))) = 2 * (|M| + 1)
      field_simp
      ring
    rw [hval2]
    linarith [le_abs_self M, abs_nonneg M]
  exact ⟨r, hr, hval ▸ lt_of_lt_of_le hM hlower⟩

/-! ### Two-sided admissible window on \(r^2 T\)

The rapidity ceiling above caps \(r^2 T\) from one side only. On the admissible
cone the elliptic branch supplies the matching floor: `sqrt_two_abs_le_phiMax`
keeps the cosine argument inside `[0, φ_max]` with `φ_max < π`, where the cosine
is still strictly decreasing. Repulsion is therefore no deeper than
\(4(\cos\varphi_{\max}-1)\), and both ends are attained at \(J=\pm J_{\max}\).
-/

theorem coshDefect_le_cosh_phiMax {J : ℝ} (hbound : |J| ≤ JMax) :
    coshDefect J ≤ cosh phiMax - 1 := by
  rcases lt_or_ge J 0 with hJ | hJ
  · have hneg := coshDefect_neg_of_admissible hJ hbound
    linarith [one_le_cosh phiMax]
  · rw [coshDefect_of_nonneg hJ]
    have habs : (2 : ℝ) * J = 2 * |J| := by rw [abs_of_nonneg hJ]
    have hθ : Real.sqrt (2 * J) ≤ phiMax := by
      rw [habs]
      exact sqrt_two_abs_le_phiMax hbound
    have hθ0 : 0 ≤ Real.sqrt (2 * J) := Real.sqrt_nonneg _
    have hch : cosh (Real.sqrt (2 * J)) ≤ cosh phiMax :=
      cosh_le_cosh.mpr (by rwa [abs_of_nonneg hθ0, abs_of_nonneg (hθ0.trans hθ)])
    linarith

theorem coshDefect_ge_cos_phiMax {J : ℝ} (hbound : |J| ≤ JMax) :
    cos phiMax - 1 ≤ coshDefect J := by
  rcases lt_or_ge J 0 with hJ | hJ
  · rw [coshDefect_of_neg hJ]
    have habs : -(2 * J) = 2 * |J| := by
      rw [abs_of_neg hJ]; ring
    have hθ : Real.sqrt (-(2 * J)) ≤ phiMax := by
      rw [habs]
      exact sqrt_two_abs_le_phiMax hbound
    have hθ0 : 0 ≤ Real.sqrt (-(2 * J)) := Real.sqrt_nonneg _
    have hπ : phiMax ≤ Real.pi := phiMax_lt_pi.le
    have hcos : cos phiMax ≤ cos (Real.sqrt (-(2 * J))) :=
      Real.strictAntiOn_cos.antitoneOn ⟨hθ0, hθ.trans hπ⟩ ⟨hθ0.trans hθ, hπ⟩ hθ
    linarith
  · have hnn : 0 ≤ coshDefect J := by
      rcases eq_or_lt_of_le hJ with h | h
      · rw [← h, coshDefect_zero]
      · exact (coshDefect_pos_of_pos h).le
    linarith [cos_le_one phiMax]

/-! Both ends of the window are attained, so neither bound can be improved. -/

theorem coshDefect_JMax : coshDefect JMax = cosh phiMax - 1 := by
  rw [coshDefect_of_nonneg JMax_pos.le, sqrt_two_JMax]

theorem coshDefect_neg_JMax : coshDefect (-JMax) = cos phiMax - 1 := by
  rw [coshDefect_of_neg (neg_neg_of_pos JMax_pos)]
  rw [show -(2 * -JMax) = 2 * JMax by ring, sqrt_two_JMax]

/-! ### Numeric envelope for the repulsive floor -/

private theorem pi_sub_phiMax_lower : (418 : ℝ) / 1000 < Real.pi - phiMax := by
  unfold phiMax
  rw [show Real.pi - Real.pi * Real.sqrt 3 / 2
      = Real.pi * (2 - Real.sqrt 3) / 2 from by ring]
  have h1 : (267 : ℝ) / 1000 < 2 - Real.sqrt 3 := by linarith [sqrt_three_lt_1733]
  have hmul : (314 : ℝ) / 100 * (267 / 1000) < Real.pi * (2 - Real.sqrt 3) :=
    mul_lt_mul pi_gt_314 h1.le (by norm_num) Real.pi_pos.le
  linarith

private theorem pi_sub_phiMax_upper : Real.pi - phiMax < (422 : ℝ) / 1000 := by
  unfold phiMax
  rw [show Real.pi - Real.pi * Real.sqrt 3 / 2
      = Real.pi * (2 - Real.sqrt 3) / 2 from by ring]
  have h1 : 2 - Real.sqrt 3 < (268 : ℝ) / 1000 := by linarith [sqrt_three_gt_1732]
  have hpos : (0 : ℝ) < 2 - Real.sqrt 3 := by linarith [sqrt_three_lt_two]
  have hmul : Real.pi * (2 - Real.sqrt 3) < (31416 / 10000 : ℝ) * (268 / 1000) :=
    mul_lt_mul pi_lt_31416 h1.le hpos (by norm_num)
  linarith

theorem four_cos_phiMax_sub_one_bounds :
    -(77 : ℝ) / 10 < 4 * (cos phiMax - 1) ∧ 4 * (cos phiMax - 1) < -(76 : ℝ) / 10 := by
  have hxlo : (418 : ℝ) / 1000 < Real.pi - phiMax := pi_sub_phiMax_lower
  have hxhi : Real.pi - phiMax < (422 : ℝ) / 1000 := pi_sub_phiMax_upper
  set x := Real.pi - phiMax with hxdef
  have hxpos : (0 : ℝ) < x := by linarith
  have habs : |x| = x := abs_of_pos hxpos
  have hbound : |cos x - (1 - x ^ 2 / 2)| ≤ x ^ 4 * (5 / 96) := by
    simpa [habs] using Real.cos_bound (by rw [habs]; linarith : |x| ≤ 1)
  obtain ⟨hlo, hhi⟩ := abs_le.mp hbound
  have hcos : cos phiMax = -cos x := by
    have hps := Real.cos_pi_sub phiMax
    rw [← hxdef] at hps
    linarith
  have hx2hi : x ^ 2 < (178084 : ℝ) / 1000000 := by nlinarith
  have hx2lo : (174724 : ℝ) / 1000000 < x ^ 2 := by nlinarith
  have hx4hi : x ^ 4 < (31714 : ℝ) / 1000000 := by
    rw [show x ^ 4 = (x ^ 2) ^ 2 from by ring]
    nlinarith [sq_nonneg x]
  rw [hcos]
  exact ⟨by linarith, by linarith⟩

/-! ### The window itself -/

theorem r_sq_mul_teleparallelTofJ {Jval r : ℝ} (hr : r ≠ 0) :
    r ^ 2 * teleparallelTofJ Jval r = 4 * coshDefect Jval := by
  have hr2 : r ^ 2 ≠ 0 := pow_ne_zero 2 hr
  unfold teleparallelTofJ
  rw [show r ^ 2 * (4 / r ^ 2 * coshDefect Jval)
      = r ^ 2 / r ^ 2 * (4 * coshDefect Jval) from by ring,
    div_self hr2, one_mul]

theorem r_sq_teleparallelTofJ_window {Jval r : ℝ} (hr : r ≠ 0)
    (hbound : |Jval| ≤ JMax) :
    4 * (cos phiMax - 1) ≤ r ^ 2 * teleparallelTofJ Jval r ∧
      r ^ 2 * teleparallelTofJ Jval r ≤ 4 * (cosh phiMax - 1) := by
  rw [r_sq_mul_teleparallelTofJ hr]
  exact ⟨by linarith [coshDefect_ge_cos_phiMax hbound],
    by linarith [coshDefect_le_cosh_phiMax hbound]⟩

/-- Both window ends are realised, at `J = -JMax` and `J = JMax` respectively. -/
theorem r_sq_teleparallelTofJ_window_sharp {r : ℝ} (hr : r ≠ 0) :
    r ^ 2 * teleparallelTofJ (-JMax) r = 4 * (cos phiMax - 1) ∧
      r ^ 2 * teleparallelTofJ JMax r = 4 * (cosh phiMax - 1) := by
  rw [r_sq_mul_teleparallelTofJ hr, r_sq_mul_teleparallelTofJ hr,
    coshDefect_neg_JMax, coshDefect_JMax]
  exact ⟨rfl, rfl⟩

/-- Numeric form of the window: admissible torsion confines `r² T` to `(-8, 27)`. -/
theorem r_sq_teleparallelTofJ_bounds {Jval r : ℝ} (hr : r ≠ 0)
    (hbound : |Jval| ≤ JMax) :
    -8 < r ^ 2 * teleparallelTofJ Jval r ∧
      r ^ 2 * teleparallelTofJ Jval r < 27 := by
  obtain ⟨hwlo, hwhi⟩ := r_sq_teleparallelTofJ_window hr hbound
  obtain ⟨hflo, _⟩ := four_cos_phiMax_sub_one_bounds
  obtain ⟨_, hchi⟩ := four_cosh_phiMax_sub_one_bounds
  exact ⟨by linarith, by linarith⟩

/-! ### The dictionary is strictly monotone, hence \(T\) determines \(J\) -/

theorem coshDefect_strictMonoOn :
    StrictMonoOn coshDefect (Icc (-JMax) JMax) := by
  intro a ha b hb hab
  have habs_a : |a| ≤ JMax := abs_le.mpr ⟨ha.1, ha.2⟩
  rcases lt_or_ge a 0 with ha0 | ha0
  · rcases lt_or_ge b 0 with hb0 | hb0
    · rw [coshDefect_of_neg ha0, coshDefect_of_neg hb0]
      have hlt : Real.sqrt (-(2 * b)) < Real.sqrt (-(2 * a)) :=
        Real.sqrt_lt_sqrt (by linarith) (by linarith)
      have hπ : Real.sqrt (-(2 * a)) ≤ Real.pi := by
        have habs : -(2 * a) = 2 * |a| := by rw [abs_of_neg ha0]; ring
        rw [habs]
        exact (sqrt_two_abs_le_phiMax habs_a).trans phiMax_lt_pi.le
      have hcos := cos_lt_cos_of_nonneg_of_le_pi (Real.sqrt_nonneg _) hπ hlt
      linarith
    · have hlt := coshDefect_neg_of_admissible ha0 habs_a
      have hge : 0 ≤ coshDefect b := by
        rcases eq_or_lt_of_le hb0 with h | h
        · rw [← h, coshDefect_zero]
        · exact (coshDefect_pos_of_pos h).le
      linarith
  · have hb0 : 0 ≤ b := ha0.trans hab.le
    rw [coshDefect_of_nonneg ha0, coshDefect_of_nonneg hb0]
    have hlt : Real.sqrt (2 * a) < Real.sqrt (2 * b) :=
      Real.sqrt_lt_sqrt (by linarith) (by linarith)
    have hch : cosh (Real.sqrt (2 * a)) < cosh (Real.sqrt (2 * b)) :=
      cosh_lt_cosh.mpr <| by
        rwa [abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg (Real.sqrt_nonneg _)]
    linarith

theorem coshDefect_injOn : Set.InjOn coshDefect (Icc (-JMax) JMax) :=
  coshDefect_strictMonoOn.injOn

/-- At a fixed radius the teleparallel density determines the algebraic scalar. -/
theorem J_unique_of_teleparallelTofJ_eq {J₁ J₂ r : ℝ} (hr : r ≠ 0)
    (h₁ : |J₁| ≤ JMax) (h₂ : |J₂| ≤ JMax)
    (heq : teleparallelTofJ J₁ r = teleparallelTofJ J₂ r) : J₁ = J₂ := by
  have hr2 : (0 : ℝ) < r ^ 2 := lt_of_le_of_ne (sq_nonneg r) (pow_ne_zero 2 hr).symm
  have hcoef : (0 : ℝ) < 4 / r ^ 2 := div_pos (by norm_num) hr2
  have hcd : coshDefect J₁ = coshDefect J₂ := by
    unfold teleparallelTofJ at heq
    exact mul_left_cancel₀ hcoef.ne' heq
  exact coshDefect_injOn
    (mem_Icc.mpr ⟨neg_le_of_abs_le h₁, le_of_abs_le h₁⟩)
    (mem_Icc.mpr ⟨neg_le_of_abs_le h₂, le_of_abs_le h₂⟩) hcd

/-! ### Closed-form inversion of the dictionary -/

theorem arcosh_one_add_quarter_r_sq_T {Jval r : ℝ} (hr : r ≠ 0) (hJ : 0 ≤ Jval) :
    Real.arcosh (1 + r ^ 2 * teleparallelTofJ Jval r / 4) =
      Real.sqrt (2 * Jval) := by
  rw [r_sq_mul_teleparallelTofJ hr, coshDefect_of_nonneg hJ,
    show (1 : ℝ) + 4 * (cosh (Real.sqrt (2 * Jval)) - 1) / 4
      = cosh (Real.sqrt (2 * Jval)) from by ring]
  exact Real.arcosh_cosh (Real.sqrt_nonneg _)

/-- Hyperbolic branch: the algebraic scalar is recovered from `r² T` in closed form. -/
theorem J_eq_half_arcosh_sq {Jval r : ℝ} (hr : r ≠ 0) (hJ : 0 ≤ Jval) :
    (1 / 2) * Real.arcosh (1 + r ^ 2 * teleparallelTofJ Jval r / 4) ^ 2 = Jval := by
  rw [arcosh_one_add_quarter_r_sq_T hr hJ,
    Real.sq_sqrt (by linarith : (0 : ℝ) ≤ 2 * Jval)]
  ring

/-- Elliptic branch: the same inversion with the cosine reading of the kernel. -/
theorem J_eq_neg_half_arccos_sq {Jval r : ℝ} (hr : r ≠ 0) (hJ : Jval < 0)
    (hbound : |Jval| ≤ JMax) :
    -(1 / 2) * Real.arccos (1 + r ^ 2 * teleparallelTofJ Jval r / 4) ^ 2 = Jval := by
  have habs : -(2 * Jval) = 2 * |Jval| := by
    rw [abs_of_neg hJ]; ring
  have hπ : Real.sqrt (-(2 * Jval)) ≤ Real.pi := by
    rw [habs]
    exact (sqrt_two_abs_le_phiMax hbound).trans phiMax_lt_pi.le
  rw [r_sq_mul_teleparallelTofJ hr, coshDefect_of_neg hJ,
    show (1 : ℝ) + 4 * (cos (Real.sqrt (-(2 * Jval))) - 1) / 4
      = cos (Real.sqrt (-(2 * Jval))) from by ring,
    Real.arccos_cos (Real.sqrt_nonneg _) hπ,
    Real.sq_sqrt (by linarith : (0 : ℝ) ≤ -(2 * Jval))]
  ring

/-- Exterior Schwarzschild specialisation of the closed-form inversion. -/
theorem J_radialBoostParams_eq_half_arcosh_sq {rs r : ℝ} (h : IsExterior rs r) :
    (1 / 2) *
        Real.arcosh (1 + r ^ 2 * schwarzschildTeleparallelT rs r / 4) ^ 2 =
      J (radialBoostParams rs r) := by
  have hr : r ≠ 0 := (lt_trans h.1 h.2).ne'
  have hJ : 0 ≤ J (radialBoostParams rs r) := by
    rw [J_radialBoostParams]
    positivity
  rw [schwarzschild_T_eq_teleparallelTofJ h]
  exact J_eq_half_arcosh_sq hr hJ

end Gravity

end DstDiophantine
