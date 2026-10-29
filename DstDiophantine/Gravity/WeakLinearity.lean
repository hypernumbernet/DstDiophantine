import DstDiophantine.Gravity.ClassicalSchwarzschild
import DstDiophantine.Gravity.DualImage
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option linter.style.native false

/-!
# Where the weak field stays linear

Two readings of one source are compared.

On the exterior Schwarzschild chart the rapidity lies strictly above the
Newtonian value \(r_s/(2r)\), and the fractional excess is strictly less than
\(r_s/(r-r_s)\). On the SI stand-ins that fraction is below \(1/(4\times 10^7)\)
for a solar mass at one astronomical unit, and below \(10^{-6}\) for the
Milky-Way mass at the compactification radius fixed by the same mass and by
\(a_0\).

At a fixed compactification radius the dual-image acceleration is linear in
the mass, and the fractional excess over the inverse square depends only on
\(r/R\). It is positive and strictly less than \((r/R)^2/3\). A solar mass has
compactification radius between \(7020\) and \(7040\) astronomical units, so
at one astronomical unit the excess is below \(10^{-8}\).

The three-sphere enhancement is the reciprocal of the volume Jacobian. On
\((0,\pi)\) it lies strictly above the shared germ \(1+x^2/3\), while the dual
enhancement lies strictly below it.

Once the patch radius scales with the enclosed mass, `dualRAR` is strictly
subhomogeneous and strictly subadditive. \(a_0\), \(G\), and the astronomical
unit are external inputs. No theorem asserts `dst_derives_a0`.
-/

namespace DstDiophantine

namespace Gravity

open Real Set Filter SI
open scoped Topology

/-! ### Linearity in the mass at fixed radius -/

theorem dualAccel_add (G R r M₁ M₂ : ℝ) :
    dualAccel G (M₁ + M₂) R r = dualAccel G M₁ R r + dualAccel G M₂ R r := by
  unfold dualAccel
  ring

theorem dualAccel_smul (G R r c M : ℝ) :
    dualAccel G (c * M) R r = c * dualAccel G M R r := by
  unfold dualAccel
  ring

/-- The ratio to the inverse square depends only on \(r/R\). -/
theorem dualAccel_div_newton {G M R r : ℝ} (hr : r ≠ 0) (hR : R ≠ 0)
    (hGM : G * M ≠ 0) :
    dualAccel G M R r / (G * M / r ^ 2) = dualEnhancement (r / R) := by
  rw [dualAccel_eq_newton_mul hr hR]
  field_simp [hGM]
  exact mul_div_cancel_left₀ _ hGM

theorem dualFractionalExcess_bounds {x : ℝ} (hx : 0 < x) :
    0 < dualEnhancement x - 1 ∧ dualEnhancement x - 1 < x ^ 2 / 3 := by
  constructor
  · linarith [one_lt_dualEnhancement hx]
  · linarith [dualEnhancement_lt_one_add_sq_div_three hx]

theorem dualFractionalExcess_lt_of_sq {x ε : ℝ} (hx : 0 < x) (hε : x ^ 2 / 3 ≤ ε) :
    dualEnhancement x - 1 < ε :=
  (dualFractionalExcess_bounds hx).2.trans_le hε

/-! ### Mass-scaled patch: slower than Newton -/

theorem dualRAR_div_eq {a0 y : ℝ} (ha0 : 0 < a0) (hy : 0 < y) :
    dualRAR a0 y / y = dualEnhancement (sqrt (a0 / y)) := by
  unfold dualRAR dualEnhancement
  have hsqrt : sqrt (a0 * y) / y = sqrt (a0 / y) := by
    calc
      sqrt (a0 * y) / y = sqrt (a0 * y) / sqrt (y ^ 2) := by rw [sqrt_sq hy.le]
      _ = sqrt ((a0 * y) / y ^ 2) := by rw [sqrt_div (mul_nonneg ha0.le hy.le)]
      _ = sqrt (a0 / y) := by congr 1; field_simp
  calc
    sqrt (a0 * y) * (cosh (sqrt (a0 / y)) / sinh (sqrt (a0 / y))) / y
        = sqrt (a0 * y) / y * (cosh (sqrt (a0 / y)) / sinh (sqrt (a0 / y))) := by
          field_simp
    _ = sqrt (a0 / y) * (cosh (sqrt (a0 / y)) / sinh (sqrt (a0 / y))) := by
          rw [hsqrt]
    _ = sqrt (a0 / y) * cosh (sqrt (a0 / y)) / sinh (sqrt (a0 / y)) := by
          rw [mul_div_assoc]

theorem strictAntiOn_dualRAR_div {a0 : ℝ} (ha0 : 0 < a0) :
    StrictAntiOn (fun y => dualRAR a0 y / y) (Ioi 0) := by
  intro y1 hy1 y2 hy2 hlt
  change dualRAR a0 y2 / y2 < dualRAR a0 y1 / y1
  rw [dualRAR_div_eq ha0 hy2, dualRAR_div_eq ha0 hy1]
  have hs1 : 0 < sqrt (a0 / y1) := sqrt_pos.mpr (div_pos ha0 hy1)
  have hs2 : 0 < sqrt (a0 / y2) := sqrt_pos.mpr (div_pos ha0 hy2)
  have hdiv : a0 / y2 < a0 / y1 := div_lt_div_of_pos_left ha0 hy1 hlt
  have hsqrt : sqrt (a0 / y2) < sqrt (a0 / y1) :=
    sqrt_lt_sqrt (div_nonneg ha0.le hy2.le) hdiv
  exact strictMonoOn_dualEnhancement (mem_Ioi.mpr hs2) (mem_Ioi.mpr hs1) hsqrt

/-- For \(k>1\), scaling the Newtonian acceleration by \(k\) scales the dual
acceleration by a strictly smaller factor. -/
theorem dualRAR_strict_subhomogeneous {a0 gN k : ℝ}
    (ha0 : 0 < a0) (hgN : 0 < gN) (hk : 1 < k) :
    dualRAR a0 (k * gN) < k * dualRAR a0 gN := by
  have hk0 : 0 < k := lt_trans zero_lt_one hk
  have hkg : 0 < k * gN := mul_pos hk0 hgN
  have hdiv :
      dualRAR a0 (k * gN) / (k * gN) < dualRAR a0 gN / gN :=
    strictAntiOn_dualRAR_div ha0 (mem_Ioi.mpr hgN) (mem_Ioi.mpr hkg)
      (by simpa using (lt_mul_iff_one_lt_left hgN).mpr hk)
  have hmul := mul_lt_mul_of_pos_right hdiv hkg
  have hleft : dualRAR a0 (k * gN) / (k * gN) * (k * gN) = dualRAR a0 (k * gN) := by
    field_simp
  have hright : dualRAR a0 gN / gN * (k * gN) = k * dualRAR a0 gN := by
    field_simp
  linarith

theorem dualRAR_strict_subadditive {a0 g1 g2 : ℝ}
    (ha0 : 0 < a0) (hg1 : 0 < g1) (hg2 : 0 < g2) :
    dualRAR a0 (g1 + g2) < dualRAR a0 g1 + dualRAR a0 g2 := by
  have hanti := strictAntiOn_dualRAR_div ha0
  have hsum : 0 < g1 + g2 := add_pos hg1 hg2
  by_cases hle : g2 ≤ g1
  · have hlt := hanti (mem_Ioi.mpr hg1) (mem_Ioi.mpr hsum) (lt_add_of_pos_right g1 hg2)
    have hprod : dualRAR a0 (g1 + g2) * g1 < dualRAR a0 g1 * (g1 + g2) :=
      (div_lt_div_iff₀ hsum hg1).mp hlt
    have hmain : dualRAR a0 (g1 + g2) < dualRAR a0 g1 * (g1 + g2) / g1 :=
      (lt_div_iff₀ hg1).mpr hprod
    have hsplit : dualRAR a0 g1 * (g1 + g2) / g1 =
        dualRAR a0 g1 + dualRAR a0 g1 * g2 / g1 := by field_simp
    rcases lt_or_eq_of_le hle with hltg | heq
    · have hratio := hanti (mem_Ioi.mpr hg2) (mem_Ioi.mpr hg1) hltg
      have hcross : dualRAR a0 g1 * g2 < dualRAR a0 g2 * g1 :=
        (div_lt_div_iff₀ hg1 hg2).mp hratio
      have hshare : dualRAR a0 g1 * g2 / g1 < dualRAR a0 g2 :=
        (div_lt_iff₀ hg1).mpr hcross
      linarith
    · subst heq
      have hcancel : dualRAR a0 g2 * g2 / g2 = dualRAR a0 g2 := by field_simp
      linarith
  · push Not at hle
    have hlt := hanti (mem_Ioi.mpr hg2) (mem_Ioi.mpr hsum) (lt_add_of_pos_left g2 hg1)
    have hprod : dualRAR a0 (g1 + g2) * g2 < dualRAR a0 g2 * (g1 + g2) :=
      (div_lt_div_iff₀ hsum hg2).mp hlt
    have hmain : dualRAR a0 (g1 + g2) < dualRAR a0 g2 * (g1 + g2) / g2 :=
      (lt_div_iff₀ hg2).mpr hprod
    have hsplit : dualRAR a0 g2 * (g1 + g2) / g2 =
        dualRAR a0 g2 + dualRAR a0 g2 * g1 / g2 := by
      field_simp
      rw [add_comm g1 g2]
    have hratio := hanti (mem_Ioi.mpr hg1) (mem_Ioi.mpr hg2) hle
    have hcross : dualRAR a0 g2 * g1 < dualRAR a0 g1 * g2 :=
      (div_lt_div_iff₀ hg2 hg1).mp hratio
    have hshare : dualRAR a0 g2 * g1 / g2 < dualRAR a0 g1 :=
      (div_lt_iff₀ hg2).mpr hcross
    linarith

/-! ### Three-sphere enhancement above the shared germ -/

private theorem hasDerivAt_sin_sub_x_cos (x : ℝ) :
    HasDerivAt (fun y => sin y - y * cos y) (x * sin x) x := by
  have hmul : HasDerivAt (fun y => y * cos y) (1 * cos x + x * (-sin x)) x :=
    (hasDerivAt_id x).mul (hasDerivAt_cos x)
  have h := (hasDerivAt_sin x).sub hmul
  have heq : cos x - (1 * cos x + x * (-sin x)) = x * sin x := by ring
  rwa [heq] at h

private theorem sin_sub_x_cos_pos {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) π) :
    0 < sin x - x * cos x := by
  have hmono : StrictMonoOn (fun y => sin y - y * cos y) (Icc (0 : ℝ) π) := by
    refine strictMonoOn_of_deriv_pos (convex_Icc _ _) ?_ ?_
    · exact continuousOn_sin.sub (continuousOn_id.mul continuousOn_cos)
    · intro y hy
      have hyI : y ∈ Ioo (0 : ℝ) π := by simpa [interior_Icc] using hy
      rw [(hasDerivAt_sin_sub_x_cos y).deriv]
      exact mul_pos hyI.1 (sin_pos_of_mem_Ioo hyI)
  have h0 : (fun y => sin y - y * cos y) 0 = 0 := by simp
  have := hmono ⟨le_rfl, pi_pos.le⟩ ⟨hx.1.le, hx.2.le⟩ hx.1
  simpa [h0] using this

private theorem hasDerivAt_threeSin (y : ℝ) :
    HasDerivAt (fun t => 3 * (sin t - t * cos t) - t ^ 2 * sin t)
      (y * (sin y - y * cos y)) y := by
  have h1 := (hasDerivAt_sin_sub_x_cos y).const_mul 3
  have h2 := (hasDerivAt_pow 2 y).mul (hasDerivAt_sin y)
  have hsub := h1.sub h2
  have hder :
      3 * (y * sin y) - ((2 : ℝ) * y ^ (2 - 1) * sin y + y ^ 2 * cos y) =
        y * (sin y - y * cos y) := by
    simp [pow_one]
    ring
  have hsub' := hsub.congr_deriv hder
  refine hsub'.congr_of_eventuallyEq (EventuallyEq.of_eq ?_)
  funext t
  simp [Pi.sub_apply, Pi.mul_apply]

private theorem threeSin_pos {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) π) :
    0 < 3 * (sin y - y * cos y) - y ^ 2 * sin y := by
  have hmono : StrictMonoOn
      (fun t => 3 * (sin t - t * cos t) - t ^ 2 * sin t) (Icc (0 : ℝ) π) := by
    refine strictMonoOn_of_deriv_pos (convex_Icc _ _) ?_ ?_
    · exact ((continuousOn_sin.sub (continuousOn_id.mul continuousOn_cos)).const_mul 3).sub
        ((continuousOn_id.pow 2).mul continuousOn_sin)
    · intro t ht
      have htI : t ∈ Ioo (0 : ℝ) π := by simpa [interior_Icc] using ht
      rw [(hasDerivAt_threeSin t).deriv]
      exact mul_pos htI.1 (sin_sub_x_cos_pos htI)
  have h0 : (fun t => 3 * (sin t - t * cos t) - t ^ 2 * sin t) 0 = 0 := by simp
  have := hmono ⟨le_rfl, pi_pos.le⟩ ⟨hy.1.le, hy.2.le⟩ hy.1
  simpa [h0] using this

private theorem hasDerivAt_logExcess {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) π) :
    HasDerivAt (fun t => Real.log t - Real.log (sin t) - t ^ 2 / 6)
      ((3 * (sin y - y * cos y) - y ^ 2 * sin y) / (3 * y * sin y)) y := by
  have hsin : sin y ≠ 0 := (sin_pos_of_mem_Ioo hy).ne'
  have hl := Real.hasDerivAt_log hy.1.ne'
  have hs := (hasDerivAt_sin y).log hsin
  have hp := (hasDerivAt_pow 2 y).div_const 6
  have h := (hl.sub hs).sub hp
  have hden : (3 : ℝ) * y * sin y ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) hy.1.ne') hsin
  have hder : (y⁻¹ - cos y / sin y) - ((2 : ℝ) * y ^ (2 - 1)) / 6 =
      (3 * (sin y - y * cos y) - y ^ 2 * sin y) / (3 * y * sin y) := by
    field_simp [hden, hy.1.ne', hsin]
    ring
  have h' := h.congr_deriv hder
  refine h'.congr_of_eventuallyEq (EventuallyEq.of_eq ?_)
  funext t
  simp [Pi.sub_apply]

private theorem logExcess_pos {x : ℝ} (hx : 0 < x) (hxπ : x < π) :
    0 < Real.log x - Real.log (sin x) - x ^ 2 / 6 := by
  let f : ℝ → ℝ := fun t => Real.log t - Real.log (sin t) - t ^ 2 / 6
  have hmono : StrictMonoOn f (Ioo (0 : ℝ) π) := by
    refine strictMonoOn_of_deriv_pos (convex_Ioo _ _) ?_ ?_
    · have hlog : ContinuousOn Real.log (Ioo (0 : ℝ) π) :=
        continuousOn_log.mono fun t ht => ht.1.ne'
      have hlogs : ContinuousOn (fun t => Real.log (sin t)) (Ioo (0 : ℝ) π) :=
        ContinuousOn.log continuousOn_sin fun t ht => (sin_pos_of_mem_Ioo ht).ne'
      exact (hlog.sub hlogs).sub ((continuousOn_id.pow 2).div_const 6)
    · intro y hy
      rw [interior_Ioo] at hy
      rw [(hasDerivAt_logExcess hy).deriv]
      exact div_pos (threeSin_pos hy) (mul_pos (mul_pos (by norm_num) hy.1)
        (sin_pos_of_mem_Ioo hy))
  have hhalf : x / 2 ∈ Ioo (0 : ℝ) π :=
    ⟨div_pos hx (by norm_num), by linarith [hxπ, pi_pos]⟩
  have hfx : f (x / 2) < f x := hmono hhalf ⟨hx, hxπ⟩ (by linarith)
  by_contra hle
  push Not at hle
  have hle' : f x ≤ 0 := by simpa [f] using hle
  have hneg : f (x / 2) < 0 := hfx.trans_le hle'
  have htend : Tendsto f (𝓝[>] 0) (𝓝 0) := by
    have hsinc : Tendsto sinc (𝓝[>] (0 : ℝ)) (𝓝 1) := by
      simpa [sinc_zero] using
        (continuous_sinc.tendsto 0).mono_left (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
    have hlog := (hsinc.log one_ne_zero).neg
    have hsq : Tendsto (fun t : ℝ => t ^ 2 / 6) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      simpa using (((continuous_pow 2).div_const (6 : ℝ)).tendsto 0).mono_left
        (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
    have hsum := hlog.sub hsq
    have hopen : Ioo (0 : ℝ) π ∈ 𝓝[>] 0 := by
      rw [mem_nhdsWithin]
      refine ⟨Ioo (-1) π, isOpen_Ioo, ⟨by norm_num, pi_pos⟩, ?_⟩
      intro z hz
      simp only [mem_inter_iff, mem_Ioo, mem_Ioi] at hz
      exact ⟨hz.2, hz.1.2⟩
    have hlim : Tendsto (fun t => Real.log t - Real.log (sin t) - t ^ 2 / 6)
        (𝓝[>] 0) (𝓝 (-Real.log 1 - 0)) := by
      refine hsum.congr' ?_
      filter_upwards [hopen] with t ht
      rw [sinc_of_ne_zero ht.1.ne', Real.log_div (sin_pos_of_mem_Ioo ht).ne' ht.1.ne']
      ring
    simpa [f, Real.log_one] using hlim
  have hopen : Ioo (0 : ℝ) (x / 2) ∈ 𝓝[>] 0 := by
    rw [mem_nhdsWithin]
    refine ⟨Ioo (-1) (x / 2), isOpen_Ioo, ⟨by norm_num, div_pos hx (by norm_num)⟩, ?_⟩
    intro z hz
    simp only [mem_inter_iff, mem_Ioo, mem_Ioi] at hz
    exact ⟨hz.2, hz.1.2⟩
  have hev : ∀ᶠ t in 𝓝[>] 0, f (x / 2) < f t ∧ t ∈ Ioo (0 : ℝ) (x / 2) := by
    filter_upwards [htend.eventually (Ioi_mem_nhds hneg), hopen] with t ht1 ht2
    exact ⟨ht1, ht2⟩
  obtain ⟨t, ht1, ht2⟩ := hev.exists
  exact lt_asymm ht1 (hmono ⟨ht2.1, lt_trans ht2.2 hhalf.2⟩ hhalf ht2.2)

/-- On \((0,\pi)\) the three-sphere enhancement lies strictly above \(1+x^2/3\). -/
theorem enhancement_gt_curvatureGerm {x : ℝ} (hx : 0 < x) (hxπ : x < π) :
    1 + x ^ 2 / 3 < enhancement x := by
  have hs : 0 < sin x := sin_pos_of_mem_Ioo ⟨hx, hxπ⟩
  have hlog := logExcess_pos hx hxπ
  have htwo : x ^ 2 / 3 < 2 * (Real.log x - Real.log (sin x)) := by linarith
  have hexp : exp (x ^ 2 / 3) < exp (2 * (Real.log x - Real.log (sin x))) :=
    exp_lt_exp.mpr htwo
  have hpow : exp (2 * (Real.log x - Real.log (sin x))) = (x / sin x) ^ 2 := by
    rw [← Real.log_div hx.ne' hs.ne', two_mul, exp_add, exp_log (div_pos hx hs)]
    ring
  have hz3 : 0 < x ^ 2 / 3 := div_pos (sq_pos_of_pos hx) (by norm_num)
  have hgerm : 1 + x ^ 2 / 3 < exp (x ^ 2 / 3) := by
    simpa [add_comm] using add_one_lt_exp (ne_of_gt hz3)
  unfold enhancement
  rw [← hpow]
  exact hgerm.trans hexp

/-! ### Exterior rapidity above its Newtonian value -/

theorem schwarzschildRapidity_gt_newtonian {rs r : ℝ} (h : IsExterior rs r) :
    rs / (2 * r) < schwarzschildRapidity rs r := by
  have hA := schwarzschildA_pos h
  have hA1 := schwarzschildA_ne_one h
  have hrpos : 0 < r := lt_trans h.1 h.2
  have hlog := Real.log_lt_sub_one_of_pos hA hA1
  have hrsr : rs / r = 1 - schwarzschildA rs r := by
    have := schwarzschildRadius_eq (rs := rs) hrpos.ne'
    exact (div_eq_iff hrpos.ne').mpr (by linarith)
  have hnewt : -(1 / 2) * (schwarzschildA rs r - 1) = rs / (2 * r) := by
    have : -(1 / 2) * (schwarzschildA rs r - 1) =
        (1 - schwarzschildA rs r) / 2 := by ring
    rw [this, ← hrsr]
    field_simp [hrpos.ne']
  have hφ : schwarzschildRapidity rs r =
      -(1 / 2) * Real.log (schwarzschildA rs r) := by
    simp [schwarzschildRapidity, schwarzschildA]
  rw [hφ, ← hnewt]
  nlinarith

theorem schwarzschildRapidity_lt_scaled {rs r : ℝ} (h : IsExterior rs r) :
    schwarzschildRapidity rs r < rs / (2 * r * schwarzschildA rs r) := by
  have hA := schwarzschildA_pos h
  have hrpos : 0 < r := lt_trans h.1 h.2
  have hAinv : 0 < (schwarzschildA rs r)⁻¹ := inv_pos.mpr hA
  have hne : (schwarzschildA rs r)⁻¹ ≠ 1 := by
    intro h1
    exact schwarzschildA_ne_one h (inv_eq_one.mp h1)
  have hlogInv := Real.log_lt_sub_one_of_pos hAinv hne
  have hlog : -Real.log (schwarzschildA rs r) =
      Real.log (schwarzschildA rs r)⁻¹ := (Real.log_inv _).symm
  have hrsr : rs / r = 1 - schwarzschildA rs r := by
    have := schwarzschildRadius_eq (rs := rs) hrpos.ne'
    exact (div_eq_iff hrpos.ne').mpr (by linarith)
  have hφ : schwarzschildRapidity rs r =
      -(1 / 2) * Real.log (schwarzschildA rs r) := by
    simp [schwarzschildRapidity, schwarzschildA]
  have hle : -(1 / 2) * Real.log (schwarzschildA rs r) <
      (1 / 2) * ((schwarzschildA rs r)⁻¹ - 1) := by
    nlinarith [hlogInv, hlog]
  have hnewt : (1 / 2) * ((schwarzschildA rs r)⁻¹ - 1) =
      rs / (2 * r * schwarzschildA rs r) := by
    have : (1 / 2) * ((schwarzschildA rs r)⁻¹ - 1) =
        (1 - schwarzschildA rs r) / (2 * schwarzschildA rs r) := by
      field_simp [hA.ne']
    rw [this, ← hrsr]
    field_simp [hrpos.ne', hA.ne']
  rw [hφ, ← hnewt]
  exact hle

theorem schwarzschild_fractional_excess_lt {rs r : ℝ} (h : IsExterior rs r) :
    schwarzschildRapidity rs r / (rs / (2 * r)) - 1 < rs / (r - rs) := by
  have hrpos : 0 < r := lt_trans h.1 h.2
  have hA := schwarzschildA_pos h
  have hnewt : 0 < rs / (2 * r) := div_pos h.1 (mul_pos (by norm_num) hrpos)
  have hlt := schwarzschildRapidity_lt_scaled h
  have hdiv : schwarzschildRapidity rs r / (rs / (2 * r)) <
      (rs / (2 * r * schwarzschildA rs r)) / (rs / (2 * r)) :=
    div_lt_div_of_pos_right hlt hnewt
  have hAeq : schwarzschildA rs r = (r - rs) / r := by
    unfold schwarzschildA
    field_simp [hrpos.ne']
  have hrew : (rs / (2 * r * schwarzschildA rs r)) / (rs / (2 * r)) =
      r / (r - rs) := by
    rw [hAeq]
    field_simp [hrpos.ne', h.1.ne', (sub_pos.mpr h.2).ne']
  have hsub : r / (r - rs) - 1 = rs / (r - rs) := by
    field_simp [(sub_pos.mpr h.2).ne']
    ring
  linarith

theorem schwarzschild_fractional_excess_of_scale {rs r ε : ℝ}
    (h : IsExterior rs r) (hε : 0 < ε) (hscale : rs * (1 / ε + 1) < r) :
    schwarzschildRapidity rs r / (rs / (2 * r)) - 1 < ε := by
  have hfrac := schwarzschild_fractional_excess_lt h
  have hrs : 0 < r - rs := sub_pos.mpr h.2
  have hsum : rs / ε + rs < r := by
    have : rs * (1 / ε) + rs < r := by simpa [mul_add, mul_one] using hscale
    simpa [div_eq_mul_inv, mul_comm] using this
  have hgap : rs / ε < r - rs := by linarith
  have hquot : rs / (r - rs) < ε := by
    have : rs < (r - rs) * ε := (div_lt_iff₀ hε).mp hgap
    exact (div_lt_iff₀ hrs).mpr (by simpa [mul_comm] using this)
  exact hfrac.trans hquot

/-! ### Solar and Milky-Way windows on the SI stand-ins -/

/-- IAU astronomical unit, an external length in metres. -/
def astronomicalUnitNat : ℕ := 149597870700

def astronomicalUnit : ℚ := astronomicalUnitNat

def solarCompactRsq : ℚ := GApprox * solarMassApprox / mondAccelApprox

def solarCompactNum : ℕ :=
  GMantissa * solarMassMantissa * 10 ^ (30 + mondAccelScale)

def solarCompactDen : ℕ :=
  10 ^ GScale * 10 ^ solarMassScale * mondAccelMantissa

theorem solarCompactRsq_eq :
    solarCompactRsq = (solarCompactNum : ℚ) / (solarCompactDen : ℚ) := by
  unfold solarCompactRsq solarMassApprox GApprox mondAccelApprox
    solarCompactNum solarCompactDen
  unfold GMantissa GScale solarMassMantissa solarMassScale
    mondAccelMantissa mondAccelScale
  field_simp
  ring

private theorem solarCompactDen_pos : (0 : ℚ) < (solarCompactDen : ℚ) := by
  unfold solarCompactDen GScale solarMassScale mondAccelMantissa
  norm_num

theorem solarCompactRsq_bounds :
    ((7020 : ℚ) * astronomicalUnit) ^ 2 < solarCompactRsq ∧
      solarCompactRsq < ((7040 : ℚ) * astronomicalUnit) ^ 2 := by
  rw [solarCompactRsq_eq]
  have hden := solarCompactDen_pos
  constructor
  · have hnat : (7020 * astronomicalUnitNat) ^ 2 * solarCompactDen < solarCompactNum := by
      unfold solarCompactNum solarCompactDen astronomicalUnitNat
      unfold GMantissa GScale solarMassMantissa solarMassScale
        mondAccelMantissa mondAccelScale
      native_decide
    rw [lt_div_iff₀ hden]
    unfold astronomicalUnit
    exact_mod_cast hnat
  · have hnat : solarCompactNum < (7040 * astronomicalUnitNat) ^ 2 * solarCompactDen := by
      unfold solarCompactNum solarCompactDen astronomicalUnitNat
      unfold GMantissa GScale solarMassMantissa solarMassScale
        mondAccelMantissa mondAccelScale
      native_decide
    rw [div_lt_iff₀ hden]
    unfold astronomicalUnit
    exact_mod_cast hnat

noncomputable def solarCompactR : ℝ := sqrt (solarCompactRsq : ℝ)

theorem solarCompactR_bounds :
    (7020 : ℝ) * astronomicalUnit < solarCompactR ∧
      solarCompactR < (7040 : ℝ) * astronomicalUnit := by
  have ⟨hlo, hhi⟩ := solarCompactRsq_bounds
  have hlo' : (((7020 : ℚ) * astronomicalUnit) ^ 2 : ℝ) < (solarCompactRsq : ℝ) :=
    mod_cast hlo
  have hhi' : (solarCompactRsq : ℝ) < (((7040 : ℚ) * astronomicalUnit) ^ 2 : ℝ) :=
    mod_cast hhi
  have hpos : (0 : ℝ) < (7020 : ℝ) * astronomicalUnit := by
    unfold astronomicalUnit astronomicalUnitNat; norm_num
  have hhi0 : (0 : ℝ) < (7040 : ℝ) * astronomicalUnit := by
    unfold astronomicalUnit astronomicalUnitNat; norm_num
  unfold solarCompactR
  constructor
  · rw [lt_sqrt hpos.le]
    convert hlo' using 1
    norm_num
  · rw [sqrt_lt' hhi0]
    convert hhi' using 1
    norm_num

theorem solar_dualExcess_at_au :
    dualEnhancement ((astronomicalUnit : ℝ) / solarCompactR) - 1 < 1 / 10 ^ 8 := by
  have hR := solarCompactR_bounds.1
  have hAU : (0 : ℝ) < astronomicalUnit := by
    unfold astronomicalUnit astronomicalUnitNat; norm_num
  have hden : (0 : ℝ) < (7020 : ℝ) * astronomicalUnit := by
    unfold astronomicalUnit astronomicalUnitNat; norm_num
  have hRpos : 0 < solarCompactR := hden.trans hR
  have hx : 0 < (astronomicalUnit : ℝ) / solarCompactR := div_pos hAU hRpos
  have hlt : (astronomicalUnit : ℝ) / solarCompactR < 1 / 7020 := by
    calc
      (astronomicalUnit : ℝ) / solarCompactR
          < astronomicalUnit / ((7020 : ℝ) * astronomicalUnit) :=
            div_lt_div_of_pos_left hAU hden hR
      _ = 1 / 7020 := by field_simp
  have hsq0 : ((astronomicalUnit : ℝ) / solarCompactR) ^ 2 < (1 / 7020) ^ 2 := by
    have hone : (0 : ℝ) ≤ 1 / 7020 := by norm_num
    have hmul := mul_lt_mul hlt hlt.le hx hone
    simpa [sq] using hmul
  have hsq : ((astronomicalUnit : ℝ) / solarCompactR) ^ 2 / 3 < (1 / 7020) ^ 2 / 3 :=
    div_lt_div_of_pos_right hsq0 (by norm_num)
  have hnum : (1 / 7020 : ℝ) ^ 2 / 3 < 1 / 10 ^ 8 := by norm_num
  exact (dualFractionalExcess_bounds hx).2.trans (hsq.trans hnum)

noncomputable def solarRs : ℝ :=
  2 * (GApprox : ℝ) * (solarMassApprox : ℝ) / (speedOfLight : ℝ) ^ 2

private theorem solarRs_scale_rat :
    (2 * GApprox * solarMassApprox / speedOfLight ^ 2) *
        ((4 : ℚ) * 10 ^ 7 + 1) < astronomicalUnit := by
  unfold GApprox solarMassApprox speedOfLight astronomicalUnit
  unfold GMantissa GScale solarMassMantissa solarMassScale speedOfLightNat
    astronomicalUnitNat
  field_simp
  exact_mod_cast (by native_decide :
    2 * 667430 * 10 ^ 9 * 198847 * (10 ^ 7 * 4 + 1) <
      299792458 ^ 2 * 149597870700)

theorem solar_fractionalRapidity_at_au :
    schwarzschildRapidity solarRs (astronomicalUnit : ℝ) /
        (solarRs / (2 * (astronomicalUnit : ℝ))) - 1
      < 1 / (4 * 10 ^ 7) := by
  have hscale : solarRs * (1 / (1 / (4 * 10 ^ 7)) + 1) < (astronomicalUnit : ℝ) := by
    have hrat := solarRs_scale_rat
    have hcast : solarRs * ((4 : ℝ) * 10 ^ 7 + 1) < (astronomicalUnit : ℝ) := by
      unfold solarRs
      exact_mod_cast hrat
    have hε : (1 : ℝ) / (1 / (4 * 10 ^ 7)) = 4 * 10 ^ 7 := by norm_num
    simpa [hε] using hcast
  have hrs : 0 < solarRs := by
    unfold solarRs
    exact div_pos (mul_pos (mul_pos (by norm_num) (mod_cast GApprox_pos))
      (mod_cast solarMassApprox_pos)) (pow_pos (mod_cast speedOfLight_pos) 2)
  have hr : solarRs < (astronomicalUnit : ℝ) := by
    have hpos : (1 : ℝ) < 4 * 10 ^ 7 + 1 := by norm_num
    have : solarRs * 1 < solarRs * (4 * 10 ^ 7 + 1) :=
      mul_lt_mul_of_pos_left hpos hrs
    have h1 : solarRs * 1 = solarRs := by ring
    have hscale' : solarRs * ((4 : ℝ) * 10 ^ 7 + 1) < (astronomicalUnit : ℝ) := by
      simpa using hscale
    linarith
  have hex : IsExterior solarRs (astronomicalUnit : ℝ) := ⟨hrs, hr⟩
  exact schwarzschild_fractional_excess_of_scale hex (by norm_num) hscale

noncomputable def milkyWayCompactR : ℝ := sqrt (milkyWayRsqApprox : ℝ)

noncomputable def milkyWayRs : ℝ :=
  2 * (GApprox : ℝ) * (milkyWayMassApprox : ℝ) / (speedOfLight : ℝ) ^ 2

private theorem milkyWay_rs_scale_rat :
    (4 : ℚ) * GApprox * milkyWayMassApprox * ((10 : ℚ) ^ 6 + 1) ^ 2 *
        mondAccelApprox < speedOfLight ^ 4 := by
  unfold GApprox milkyWayMassApprox solarMassApprox mondAccelApprox speedOfLight
  unfold GMantissa GScale solarMassMantissa solarMassScale
    mondAccelMantissa mondAccelScale speedOfLightNat milkyWayMassCoeff
  field_simp
  exact_mod_cast (by native_decide :
    4 * 667430 * (6 * 10 ^ 10) * 198847 * (10 ^ 6 + 1) ^ 2 * 12 <
      10 ^ 2 * 299792458 ^ 4)

theorem milkyWay_fractionalRapidity_at_compactification :
    schwarzschildRapidity milkyWayRs milkyWayCompactR /
        (milkyWayRs / (2 * milkyWayCompactR)) - 1
      < 1 / 10 ^ 6 := by
  have hrat := milkyWay_rs_scale_rat
  have hcast : (4 : ℝ) * GApprox * milkyWayMassApprox * ((10 : ℝ) ^ 6 + 1) ^ 2 *
      mondAccelApprox < (speedOfLight : ℝ) ^ 4 := mod_cast hrat
  have hc : (0 : ℝ) < speedOfLight := mod_cast speedOfLight_pos
  have ha : (0 : ℝ) < mondAccelApprox := mod_cast mondAccelApprox_pos
  have hG : (0 : ℝ) < GApprox := mod_cast GApprox_pos
  have hM : (0 : ℝ) < milkyWayMassApprox := mod_cast milkyWayMassApprox_pos
  have hnn : 0 ≤ (milkyWayRsqApprox : ℝ) := by
    unfold milkyWayRsqApprox
    exact mod_cast (div_nonneg (mul_nonneg (le_of_lt GApprox_pos)
      (le_of_lt milkyWayMassApprox_pos)) (le_of_lt mondAccelApprox_pos))
  have hsq : (milkyWayRs * ((10 : ℝ) ^ 6 + 1)) ^ 2 < milkyWayCompactR ^ 2 := by
    unfold milkyWayRs milkyWayCompactR
    rw [sq_sqrt hnn]
    set G : ℝ := (GApprox : ℝ)
    set M : ℝ := (milkyWayMassApprox : ℝ)
    set c : ℝ := (speedOfLight : ℝ)
    set a : ℝ := (mondAccelApprox : ℝ)
    set K : ℝ := (10 : ℝ) ^ 6 + 1
    unfold milkyWayRsqApprox
    have hsplitR : ((GApprox * milkyWayMassApprox / mondAccelApprox : ℚ) : ℝ) =
        G * M / a := by
      unfold G M a
      push_cast
      rfl
    rw [hsplitR]
    have hxeq : (2 * G * M / c ^ 2 * K) ^ 2 = 4 * G ^ 2 * M ^ 2 * K ^ 2 / c ^ 4 := by
      field_simp [hc.ne']
      ring
    rw [hxeq, div_lt_div_iff₀ (pow_pos hc 4) ha]
    have hcast' : 4 * G * M * K ^ 2 * a < c ^ 4 := by
      simpa [G, M, c, a, K] using hcast
    convert mul_lt_mul_of_pos_right hcast' (mul_pos hG hM) using 1 <;> ring
  have hR : milkyWayRs * ((10 : ℝ) ^ 6 + 1) < milkyWayCompactR := by
    have hb : 0 ≤ milkyWayCompactR := by
      unfold milkyWayCompactR
      exact sqrt_nonneg _
    exact lt_of_abs_lt (abs_lt_of_sq_lt_sq hsq hb)
  have hrs0 : 0 < milkyWayRs := by
    unfold milkyWayRs
    exact div_pos (mul_pos (mul_pos (by norm_num) hG) hM) (pow_pos hc 2)
  have hr : milkyWayRs < milkyWayCompactR := by
    have hfac : (1 : ℝ) < (10 : ℝ) ^ 6 + 1 := by norm_num
    have : milkyWayRs * 1 < milkyWayRs * ((10 : ℝ) ^ 6 + 1) :=
      mul_lt_mul_of_pos_left hfac hrs0
    linarith
  have hex : IsExterior milkyWayRs milkyWayCompactR := ⟨hrs0, hr⟩
  have hscale : milkyWayRs * (1 / (1 / 10 ^ 6) + 1) < milkyWayCompactR := by
    have : (1 : ℝ) / (1 / 10 ^ 6) = 10 ^ 6 := by norm_num
    simpa [this] using hR
  exact schwarzschild_fractional_excess_of_scale hex (by norm_num) hscale

end Gravity

end DstDiophantine
