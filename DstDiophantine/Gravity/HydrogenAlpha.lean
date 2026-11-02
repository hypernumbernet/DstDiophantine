import DstDiophantine.Gravity.ElectronForce
import DstDiophantine.Gravity.ParticleStability
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The hydrogen Hα line on the outer plateau

## Paper boundary (do **not** claim)

The radius law \(r_n=n^2 a_0\) is an input. Nothing here derives it from
\(\gamma_s=0\), and nothing here is a fine-structure splitting or a
selection rule. The electromagnetic length is the reduced Compton
wavelength, likewise an input.

## What is proved

* The bookkeeping difference from shell \(3\) to shell \(2\) is exactly
  \(5/36\) of the ionisation energy.
* With that length, shell \(n\ge 1\) sits at phase \(\alpha/(2n^2)\).
  Every such phase lies in the outer well, below \(1/100\), on the
  restoring side of a circular path.
* For a fixed proton the vacuum wavelength of the difference lies strictly
  between \(656112\times 10^{-12}\,\mathrm{m}\) and
  \(656113\times 10^{-12}\,\mathrm{m}\). Shared inertia, with the mass
  ratio strictly between \(1836\) and \(1837\), places the wavelength
  strictly between \(656469\times 10^{-12}\,\mathrm{m}\) and
  \(656470\times 10^{-12}\,\mathrm{m}\).
* At every phase of a shell \(n\ge 2\), the signed circular energy departs
  from the Coulomb value by less than \(10^{-6}\) of the ionisation, and
  the difference of the shells \(3\) and \(2\) departs from \(5/36\) by
  less than one part in ten thousand of that fraction.
* The outer-well potential itself, the term an orbital equation would use,
  lies strictly below the Coulomb potential. Outside the Bohr radius the
  deepening is less than \(1/30000\) of the ionisation. At shell \(n\) the
  Coulomb value of that potential is \(-2/n^2\) of the ionisation, and the
  deepening is at most \((3/5)\alpha^2/n^6\), hence less than \(1/30000\).
  The potential keeps falling as the phase rises and is unbounded below
  only at the node, so these shells are not minima of the potential.
* The ground shell departs from \(-1\) by less than \(1/60000\). The
  bookkeeping steps \(2\to 1\), \(4\to 2\), \(5\to 2\), and \(4\to 3\) are
  \(3/4\), \(3/16\), \(21/100\), and \(7/144\) of the ionisation, and each
  circular-energy difference departs from that fraction by less than one
  part in ten thousand of it.
-/

namespace DstDiophantine

namespace Gravity

open Real Set SI intervalIntegral MeasureTheory

/-! ### Bookkeeping difference -/

theorem bohrEnergyDiff_hAlpha :
    bohrEnergyDiff 2 3 = (5 / 36) * (hydrogenIonisationApprox : ℝ) := by
  unfold bohrEnergyDiff
  norm_num
  ring

/-- Phase of the Bohr shell \(n\), once the electromagnetic length is the
reduced Compton wavelength: \(x_n=\alpha/(2n^2)\). -/
def bohrShellPhase (n : ℕ) : ℚ :=
  fineStructureApprox / (2 * (n : ℚ) ^ 2)

theorem bohrShellPhase_eq_compton (n : ℕ) (hn : n ≠ 0) :
    (hbarApprox / (electronMassApprox * speedOfLight)) /
        (2 * ((n : ℚ) ^ 2 * bohrRadiusApprox)) =
      bohrShellPhase n := by
  unfold bohrShellPhase bohrRadiusApprox
  have hm : electronMassApprox ≠ 0 := electronMassApprox_pos.ne'
  have hc : speedOfLight ≠ 0 := speedOfLight_pos.ne'
  have hα : fineStructureApprox ≠ 0 := fineStructureApprox_pos.ne'
  have hh : hbarApprox ≠ 0 := hbarApprox_pos.ne'
  have hn0 : (n : ℚ) ≠ 0 := by exact_mod_cast hn
  field_simp [hm, hc, hα, hh, hn0]

theorem bohrShellPhase_pos {n : ℕ} (hn : 0 < n) : (0 : ℚ) < bohrShellPhase n := by
  unfold bohrShellPhase
  exact div_pos fineStructureApprox_pos
    (mul_pos (by norm_num) (pow_pos (Nat.cast_pos.mpr hn) 2))

theorem bohrShellPhase_le_half_alpha {n : ℕ} (hn : 0 < n) :
    bohrShellPhase n ≤ fineStructureApprox / 2 := by
  unfold bohrShellPhase
  have hn1 : (1 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn
  have hsq : (1 : ℚ) ≤ (n : ℚ) ^ 2 := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℚ) ≤ 1) hn1 2
    simpa using this
  have hden : (0 : ℚ) < 2 * (n : ℚ) ^ 2 := by positivity
  rw [div_le_div_iff₀ hden (by norm_num)]
  have hα : (0 : ℚ) ≤ fineStructureApprox := fineStructureApprox_pos.le
  nlinarith

theorem fineStructureApprox_lt_one_fifty :
    (fineStructureApprox : ℝ) < 1 / 50 := by
  unfold fineStructureApprox fineStructureMantissa fineStructureScale
  norm_num

theorem bohrShellPhase_lt_hundredth {n : ℕ} (hn : 0 < n) :
    (bohrShellPhase n : ℝ) < 1 / 100 := by
  have hle := bohrShellPhase_le_half_alpha hn
  have hα : (fineStructureApprox : ℝ) / 2 < 1 / 100 := by
    have hα' := fineStructureApprox_lt_one_fifty
    linarith
  exact lt_of_le_of_lt (by exact_mod_cast hle) hα

/-! ### Both shells lie on the restoring side -/

theorem bohrShellPhase_mem_outer {n : ℕ} (hn : 0 < n) :
    (bohrShellPhase n : ℝ) ∈ Ioo (0 : ℝ) resonanceRoot1 := by
  refine ⟨by exact_mod_cast bohrShellPhase_pos hn, ?_⟩
  have h100 : (bohrShellPhase n : ℝ) < 1 / 100 := bohrShellPhase_lt_hundredth hn
  have hnode : (1 / 100 : ℝ) < resonanceRoot1 := by
    have hπ : (1 / 100 : ℝ) < π / 4 := by linarith [pi_gt_three]
    exact lt_trans hπ resonanceRoot1_sharp_bounds.1
  exact lt_trans h100 hnode

theorem bohrShell_restoring {n : ℕ} (hn : 0 < n) :
    0 < circStable (bohrShellPhase n) ∧
      (bohrShellPhase n : ℝ) * deriv pairAttraction (bohrShellPhase n) /
          pairAttraction (bohrShellPhase n) < 3 := by
  obtain ⟨y, hy, _⟩ := exists_unique_circStable
  have hx := bohrShellPhase_mem_outer hn
  have hlt : (bohrShellPhase n : ℝ) < y := by
    have h100 := bohrShellPhase_lt_hundredth hn
    linarith [hy.1.1]
  have hsign := circStable_outer_sign hx hy.1 hy.2
  have hpos : 0 < circStable (bohrShellPhase n) := hsign.1.mpr hlt
  exact ⟨hpos, (pairAttraction_logDeriv_lt_three_outer_iff hx).mpr hpos⟩

/-! ### Interference at the plateau -/

/-- On `[0, 1/50]` the exponential stays below `11/10`, by the chord of `exp`
from `0` to `log 2`. -/
private theorem exp_le_eleven_tenths {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 1 / 50) :
    exp t ≤ 11 / 10 := by
  have hlog : (1 / 2 : ℝ) < log 2 := by linarith [log_two_gt_d9]
  have htlog : t ≤ log 2 := by linarith [ht, hlog]
  set b : ℝ := t / log 2
  have hlogpos : 0 < log 2 := by linarith
  have hb0 : 0 ≤ b := div_nonneg ht0 hlogpos.le
  have hb1 : b ≤ 1 := by
    rw [div_le_one hlogpos]
    exact htlog
  have ha : 0 ≤ 1 - b := by linarith
  have hab : (1 - b) + b = 1 := by ring
  have hcomb := convexOn_exp.2 (x := (0 : ℝ)) (y := log 2)
    (mem_univ _) (mem_univ _) ha hb0 hab
  have hpoint : b * log 2 = t := by
    unfold b
    field_simp [hlogpos.ne']
  have hexp2 : exp (log 2) = 2 := exp_log (by norm_num)
  have hle : exp t ≤ (1 - b) * 1 + b * 2 := by
    have hrewrite : exp (b * log 2) ≤ (1 - b) * 1 + b * exp (log 2) := by
      simpa [smul_eq_mul, exp_zero, mul_zero, zero_add] using hcomb
    simpa [hpoint, hexp2] using hrewrite
  have hlin : exp t ≤ 1 + b := by linarith
  have hinv : (1 : ℝ) / log 2 ≤ 2 := by
    rw [div_le_iff₀ hlogpos]
    linarith
  have hb : b ≤ t * 2 := by
    unfold b
    calc t / log 2
        = t * (1 / log 2) := by ring
      _ ≤ t * 2 := mul_le_mul_of_nonneg_left hinv ht0
  have htwo : exp t ≤ 1 + 2 * t := by linarith
  have hcap : 1 + 2 * t ≤ 26 / 25 := by nlinarith [ht]
  have hcmp : (26 : ℝ) / 25 ≤ 11 / 10 := by norm_num
  linarith

private theorem cosh_le_exp_nonneg {t : ℝ} (ht : 0 ≤ t) : cosh t ≤ exp t := by
  rw [cosh_eq]
  have hle : exp (-t) ≤ exp t := (exp_le_exp).mpr (by linarith)
  linarith [exp_pos t, exp_pos (-t)]

private theorem gammaDepart_le {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 50) :
    1 - gammaSEqual x ≤ (11 / 10) * x ^ 2 := by
  have hx50 : x ≤ 1 / 50 := hx
  have hderiv : ∀ t ∈ uIcc (0 : ℝ) x, HasDerivAt gammaSEqual (-2 * cosh t * sin t) t :=
    fun t _ => hasDerivAt_gammaSEqual t
  have hint : IntervalIntegrable (fun t => -2 * cosh t * sin t) volume 0 x := by
    refine Continuous.intervalIntegrable ?_ 0 x
    fun_prop
  have hftc := integral_eq_sub_of_hasDerivAt hderiv hint
  rw [gammaSEqual_zero] at hftc
  have hflip : (1 : ℝ) - gammaSEqual x = ∫ t in (0 : ℝ)..x, 2 * cosh t * sin t := by
    have hneg : ∫ t in (0 : ℝ)..x, 2 * cosh t * sin t =
        -∫ t in (0 : ℝ)..x, -2 * cosh t * sin t := by
      simp [intervalIntegral.integral_neg]
    linarith [hneg]
  rw [hflip]
  have hbound : ∀ t ∈ Icc (0 : ℝ) x, 2 * cosh t * sin t ≤ (11 / 5) * t := by
    intro t ht
    have ht0 : 0 ≤ t := ht.1
    have ht50 : t ≤ 1 / 50 := le_trans ht.2 hx50
    have hsin : sin t ≤ t := by
      rcases eq_or_lt_of_le ht0 with rfl | hpos
      · simp
      · exact (sin_lt hpos).le
    have hcosh : cosh t ≤ 11 / 10 := by
      have hexp := exp_le_eleven_tenths ht0 ht50
      exact le_trans (cosh_le_exp_nonneg ht0) hexp
    have hsin0 : 0 ≤ sin t := by
      rcases eq_or_lt_of_le ht0 with rfl | hpos
      · simp
      · exact (sin_pos_of_pos_of_lt_pi hpos (by linarith [ht50, pi_gt_three])).le
    have hprod : cosh t * sin t ≤ (11 / 10) * t := by
      calc cosh t * sin t
          ≤ (11 / 10) * sin t := mul_le_mul_of_nonneg_right hcosh hsin0
        _ ≤ (11 / 10) * t := mul_le_mul_of_nonneg_left hsin (by norm_num)
    linarith
  have hintg : IntervalIntegrable (fun t => (11 / 5) * t) volume 0 x := by
    refine Continuous.intervalIntegrable ?_ 0 x
    fun_prop
  have hintf : IntervalIntegrable (fun t => 2 * cosh t * sin t) volume 0 x := by
    refine Continuous.intervalIntegrable ?_ 0 x
    fun_prop
  have hmono := integral_mono_on hx0 hintf hintg hbound
  have hquad : ∫ t in (0 : ℝ)..x, (11 / 5) * t = (11 / 10) * x ^ 2 := by
    have hder : ∀ t ∈ uIcc (0 : ℝ) x,
        HasDerivAt (fun s => (11 / 10) * s ^ 2) ((11 / 5) * t) t := by
      intro t _
      have hsq : HasDerivAt (fun s : ℝ => s ^ 2) (2 * t) t := by
        simpa [pow_one] using hasDerivAt_pow 2 t
      have hmul := hsq.const_mul ((11 : ℝ) / 10)
      convert hmul using 1
      ring
    have hq := integral_eq_sub_of_hasDerivAt hder hintg
    simp at hq
    linarith
  linarith

private theorem gammaLower_pos {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 100) :
    1 - (11 / 10) * x ^ 2 ≤ gammaSEqual x := by
  linarith [gammaDepart_le hx0 (le_trans hx (by norm_num : (1 / 100 : ℝ) ≤ 1 / 50))]

/-- Below phase `1/100` the outer-well integral exceeds the Coulomb phase by
at most `(6/5) x³`, and the excess is strict. -/
theorem layerAccum_coulomb_gap {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) (1 / 100)) :
    x < layerAccum x ∧ layerAccum x - x ≤ (6 / 5) * x ^ 3 := by
  have hx0 : 0 ≤ x := hx.1.le
  have hxle : x ≤ 1 / 100 := hx.2.le
  have hx1 : x < resonanceRoot1 :=
    lt_trans hx.2 <| lt_trans (by linarith [pi_gt_three] : (1 / 100 : ℝ) < π / 4)
      resonanceRoot1_sharp_bounds.1
  have hstrict := layerAccum_gt_phase ⟨hx.1, hx1⟩
  have hγx : 0 < gammaSEqual x := gammaSEqual_pos_left_of_first_node ⟨hx.1, hx1⟩
  have hanti : AntitoneOn gammaSEqual (Icc (0 : ℝ) π) := by
    simpa [Nat.cast_zero, zero_mul] using (strictAntiOn_gammaSEqual_even 0).antitoneOn
  have hxπ : x ≤ π := by linarith [hx.2, pi_gt_three]
  have hγmono : ∀ t ∈ Icc (0 : ℝ) x, gammaSEqual x ≤ gammaSEqual t := by
    intro t ht
    exact hanti ⟨ht.1, le_trans ht.2 hxπ⟩ ⟨hx0, hxπ⟩ ht.2
  have hγt : ∀ t ∈ Icc (0 : ℝ) x, 0 < gammaSEqual t :=
    fun t ht => gammaSEqual_pos_of_lt_firstNode ht.1 (lt_of_le_of_lt ht.2 hx1)
  have hcont : ContinuousOn (fun t => (gammaSEqual t)⁻¹) (Icc 0 x) := by
    refine continuous_gammaSEqual.continuousOn.inv₀ ?_
    intro t ht
    exact (hγt t ht).ne'
  have hint := hcont.intervalIntegrable_of_Icc (μ := volume) hx0
  have hconst : IntervalIntegrable (fun _ : ℝ => (gammaSEqual x)⁻¹) volume 0 x :=
    intervalIntegrable_const
  have hle : ∀ t ∈ Icc (0 : ℝ) x, (gammaSEqual t)⁻¹ ≤ (gammaSEqual x)⁻¹ := by
    intro t ht
    exact (inv_le_inv₀ (hγt t ht) hγx).mpr (hγmono t ht)
  have hupper := integral_mono_on hx0 hint hconst hle
  have hconst_int : ∫ t in (0 : ℝ)..x, (gammaSEqual x)⁻¹ = x * (gammaSEqual x)⁻¹ := by
    simp
  have haccum_le : layerAccum x ≤ x * (gammaSEqual x)⁻¹ := by
    unfold layerAccum
    linarith
  have hrel : (gammaSEqual x)⁻¹ - 1 ≤ (6 / 5) * x ^ 2 := by
    have hden_pos : 0 < 1 - (11 / 10) * x ^ 2 := by
      have hx2 : x ^ 2 ≤ (1 / 100) ^ 2 := pow_le_pow_left₀ hx0 hxle 2
      nlinarith
    have hγ := gammaLower_pos hx0 hxle
    have hdiv : (1 - gammaSEqual x) / gammaSEqual x ≤
        ((11 / 10) * x ^ 2) / (1 - (11 / 10) * x ^ 2) := by
      rw [div_le_div_iff₀ hγx hden_pos]
      have hnum := gammaDepart_le hx0
        (le_trans hxle (by norm_num : (1 / 100 : ℝ) ≤ 1 / 50))
      nlinarith
    have hcoeff : ((11 / 10) * x ^ 2) / (1 - (11 / 10) * x ^ 2) ≤
        (6 / 5) * x ^ 2 := by
      have hfloor : (99989 : ℝ) / 100000 ≤ 1 - (11 / 10) * x ^ 2 := by
        have hx2 : x ^ 2 ≤ (1 / 100) ^ 2 := pow_le_pow_left₀ hx0 hxle 2
        nlinarith
      have hconst : (11 : ℝ) / 10 / ((99989 : ℝ) / 100000) < 6 / 5 := by norm_num
      have hden_pos' : (0 : ℝ) < (99989 : ℝ) / 100000 := by norm_num
      have hquot : (11 / 10) / (1 - (11 / 10) * x ^ 2) ≤
          (11 / 10) / ((99989 : ℝ) / 100000) := by
        apply div_le_div_of_nonneg_left (by norm_num) hden_pos' hfloor
      have hquot_lt : (11 / 10) / (1 - (11 / 10) * x ^ 2) < 6 / 5 :=
        lt_of_le_of_lt hquot hconst
      have hx2_nonneg : 0 ≤ x ^ 2 := by positivity
      have hmul := mul_le_mul_of_nonneg_right hquot_lt.le hx2_nonneg
      have hform : ((11 / 10) * x ^ 2) / (1 - (11 / 10) * x ^ 2) =
          x ^ 2 * ((11 / 10) / (1 - (11 / 10) * x ^ 2)) := by ring
      linarith [hform, hmul]
    have hrewrite : (gammaSEqual x)⁻¹ - 1 = (1 - gammaSEqual x) / gammaSEqual x := by
      field_simp [hγx.ne']
    linarith
  refine ⟨hstrict, ?_⟩
  calc layerAccum x - x
      ≤ x * (gammaSEqual x)⁻¹ - x := by linarith
    _ = x * ((gammaSEqual x)⁻¹ - 1) := by ring
    _ ≤ x * ((6 / 5) * x ^ 2) := mul_le_mul_of_nonneg_left hrel hx0
    _ = (6 / 5) * x ^ 3 := by ring

private theorem circEnergy_coulomb_gap {x : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) (1 / 100)) :
    |circEnergy x + x| ≤ (6 / 5) * x ^ 3 := by
  have hx0 : 0 ≤ x := hx.1.le
  have hxle : x ≤ 1 / 100 := hx.2.le
  have hx1 : x < resonanceRoot1 :=
    lt_trans hx.2 <| lt_trans (by linarith [pi_gt_three] : (1 / 100 : ℝ) < π / 4)
      resonanceRoot1_sharp_bounds.1
  have hγx : 0 < gammaSEqual x := gammaSEqual_pos_left_of_first_node ⟨hx.1, hx1⟩
  have hanti : AntitoneOn gammaSEqual (Icc (0 : ℝ) π) := by
    simpa [Nat.cast_zero, zero_mul] using (strictAntiOn_gammaSEqual_even 0).antitoneOn
  have hxπ : x ≤ π := by linarith [hx.2, pi_gt_three]
  have hγmono : ∀ t ∈ Icc (0 : ℝ) x, gammaSEqual x ≤ gammaSEqual t := by
    intro t ht
    exact hanti ⟨ht.1, le_trans ht.2 hxπ⟩ ⟨hx0, hxπ⟩ ht.2
  have hγone : ∀ t ∈ Icc (0 : ℝ) x, gammaSEqual t ≤ 1 := by
    intro t ht
    have hle := hanti ⟨le_rfl, by linarith [pi_gt_three]⟩ ⟨ht.1, le_trans ht.2 hxπ⟩ ht.1
    rw [gammaSEqual_zero] at hle
    exact hle
  have hγt : ∀ t ∈ Icc (0 : ℝ) x, 0 < gammaSEqual t :=
    fun t ht => gammaSEqual_pos_of_lt_firstNode ht.1 (lt_of_le_of_lt ht.2 hx1)
  have hcont : ContinuousOn (fun t => (gammaSEqual t)⁻¹) (Icc 0 x) := by
    refine continuous_gammaSEqual.continuousOn.inv₀ ?_
    intro t ht
    exact (hγt t ht).ne'
  have hint := hcont.intervalIntegrable_of_Icc (μ := volume) hx0
  have hconst : IntervalIntegrable (fun _ : ℝ => (gammaSEqual x)⁻¹) volume 0 x :=
    intervalIntegrable_const
  have hone : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume 0 x :=
    intervalIntegrable_const
  have hle : ∀ t ∈ Icc (0 : ℝ) x, (gammaSEqual t)⁻¹ ≤ (gammaSEqual x)⁻¹ := by
    intro t ht
    exact (inv_le_inv₀ (hγt t ht) hγx).mpr (hγmono t ht)
  have hge : ∀ t ∈ Icc (0 : ℝ) x, (1 : ℝ) ≤ (gammaSEqual t)⁻¹ := by
    intro t ht
    have hmul := mul_le_mul_of_nonneg_right (hγone t ht) (inv_nonneg.mpr (hγt t ht).le)
    have hcancel : gammaSEqual t * (gammaSEqual t)⁻¹ = 1 :=
      mul_inv_cancel₀ (hγt t ht).ne'
    linarith
  have hupper := integral_mono_on hx0 hint hconst hle
  have hlower := integral_mono_on hx0 hone hint hge
  have hconst_int : ∫ t in (0 : ℝ)..x, (gammaSEqual x)⁻¹ = x * (gammaSEqual x)⁻¹ := by
    simp
  have hone_int : ∫ t in (0 : ℝ)..x, (1 : ℝ) = x := by simp
  have haccum_le : layerAccum x ≤ x * (gammaSEqual x)⁻¹ := by
    unfold layerAccum
    linarith
  have haccum_ge : x ≤ layerAccum x := by
    unfold layerAccum
    linarith
  have hup : circEnergy x + x ≤ x * ((gammaSEqual x)⁻¹ - 1) := by
    unfold circEnergy
    rw [div_eq_mul_inv]
    linarith
  have hlo : -(x * ((gammaSEqual x)⁻¹ - 1)) ≤ circEnergy x + x := by
    unfold circEnergy
    rw [div_eq_mul_inv]
    linarith
  have hgap_nonneg : 0 ≤ x * ((gammaSEqual x)⁻¹ - 1) := by
    have hone_le : (1 : ℝ) ≤ (gammaSEqual x)⁻¹ := hge x ⟨hx0, le_rfl⟩
    positivity
  have habs : |circEnergy x + x| ≤ x * ((gammaSEqual x)⁻¹ - 1) :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  have hrel : (gammaSEqual x)⁻¹ - 1 ≤ (6 / 5) * x ^ 2 := by
    have hden_pos : 0 < 1 - (11 / 10) * x ^ 2 := by
      have hx2 : x ^ 2 ≤ (1 / 100) ^ 2 := pow_le_pow_left₀ hx0 hxle 2
      nlinarith
    have hγ := gammaLower_pos hx0 hxle
    have hnum := gammaDepart_le hx0
      (le_trans hxle (by norm_num : (1 / 100 : ℝ) ≤ 1 / 50))
    have hdiv : (1 - gammaSEqual x) / gammaSEqual x ≤
        ((11 / 10) * x ^ 2) / (1 - (11 / 10) * x ^ 2) := by
      rw [div_le_div_iff₀ hγx hden_pos]
      nlinarith
    have hcoeff : ((11 / 10) * x ^ 2) / (1 - (11 / 10) * x ^ 2) ≤
        (6 / 5) * x ^ 2 := by
      have hfloor : (99989 : ℝ) / 100000 ≤ 1 - (11 / 10) * x ^ 2 := by
        have hx2 : x ^ 2 ≤ (1 / 100) ^ 2 := pow_le_pow_left₀ hx0 hxle 2
        nlinarith
      have hconst : (11 : ℝ) / 10 / ((99989 : ℝ) / 100000) < 6 / 5 := by norm_num
      have hden_pos' : (0 : ℝ) < (99989 : ℝ) / 100000 := by norm_num
      have hquot : (11 / 10) / (1 - (11 / 10) * x ^ 2) ≤
          (11 / 10) / ((99989 : ℝ) / 100000) := by
        apply div_le_div_of_nonneg_left (by norm_num) hden_pos' hfloor
      have hquot_lt : (11 / 10) / (1 - (11 / 10) * x ^ 2) < 6 / 5 :=
        lt_of_le_of_lt hquot hconst
      have hx2_nonneg : 0 ≤ x ^ 2 := by positivity
      have hmul := mul_le_mul_of_nonneg_right hquot_lt.le hx2_nonneg
      have hform : ((11 / 10) * x ^ 2) / (1 - (11 / 10) * x ^ 2) =
          x ^ 2 * ((11 / 10) / (1 - (11 / 10) * x ^ 2)) := by ring
      linarith [hform, hmul]
    have hrewrite : (gammaSEqual x)⁻¹ - 1 = (1 - gammaSEqual x) / gammaSEqual x := by
      field_simp [hγx.ne']
    linarith
  calc |circEnergy x + x|
      ≤ x * ((gammaSEqual x)⁻¹ - 1) := habs
    _ ≤ x * ((6 / 5) * x ^ 2) :=
        mul_le_mul_of_nonneg_left hrel hx0
    _ = (6 / 5) * x ^ 3 := by ring

/-- Signed circular energy at a Bohr phase, in units of the ionisation energy.
The Coulomb value is \(-1/n^2\). -/
noncomputable def signedShell (n : ℕ) : ℝ :=
  (2 / (fineStructureApprox : ℝ)) * circEnergy (bohrShellPhase n)

theorem signedShell_near_coulomb {n : ℕ} (hn : 2 ≤ n) :
    |signedShell n + 1 / (n : ℝ) ^ 2| < 1 / 1000000 := by
  have hn0 : 0 < n := by omega
  have hx_pos : (0 : ℝ) < (bohrShellPhase n : ℝ) := by
    exact_mod_cast bohrShellPhase_pos hn0
  have hx_le : (bohrShellPhase n : ℝ) ≤ (fineStructureApprox : ℝ) / 8 := by
    have hle : bohrShellPhase n ≤ fineStructureApprox / (2 * 4) := by
      unfold bohrShellPhase
      have hn2 : (4 : ℚ) ≤ (n : ℚ) ^ 2 := by
        have hn' : (2 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn
        have := pow_le_pow_left₀ (by norm_num : (0 : ℚ) ≤ 2) hn' 2
        simpa [show (2 : ℚ) ^ 2 = 4 by norm_num] using this
      have hden : (0 : ℚ) < 2 * (n : ℚ) ^ 2 := by positivity
      rw [div_le_div_iff₀ hden (by norm_num)]
      have hα : (0 : ℚ) ≤ fineStructureApprox := fineStructureApprox_pos.le
      nlinarith
    have hfour : (fineStructureApprox : ℚ) / (2 * 4) = fineStructureApprox / 8 := by ring
    have hcast : (bohrShellPhase n : ℝ) ≤ (fineStructureApprox : ℝ) / 8 := by
      have := hle
      rw [hfour] at this
      exact_mod_cast this
    exact hcast
  have hx_lt : (bohrShellPhase n : ℝ) < 1 / 100 := bohrShellPhase_lt_hundredth hn0
  have hgap := circEnergy_coulomb_gap ⟨hx_pos, hx_lt⟩
  have hα : (0 : ℝ) < (fineStructureApprox : ℝ) := by exact_mod_cast fineStructureApprox_pos
  have hident : signedShell n + 1 / (n : ℝ) ^ 2 =
      (2 / (fineStructureApprox : ℝ)) *
        (circEnergy (bohrShellPhase n) + (bohrShellPhase n : ℝ)) := by
    have hxphase : (bohrShellPhase n : ℝ) =
        (fineStructureApprox : ℝ) / (2 * (n : ℝ) ^ 2) := by
      unfold bohrShellPhase
      norm_cast
    unfold signedShell
    rw [hxphase]
    field_simp [hα.ne', (Nat.cast_pos.mpr hn0 : (0 : ℝ) < (n : ℝ)).ne']
  rw [hident]
  have habs : |(2 / (fineStructureApprox : ℝ)) *
      (circEnergy (bohrShellPhase n) + (bohrShellPhase n : ℝ))| =
      (2 / (fineStructureApprox : ℝ)) *
        |circEnergy (bohrShellPhase n) + (bohrShellPhase n : ℝ)| := by
    rw [abs_mul, abs_of_pos (div_pos (by norm_num) hα)]
  rw [habs]
  have hscale : (2 / (fineStructureApprox : ℝ)) *
      |circEnergy (bohrShellPhase n) + (bohrShellPhase n : ℝ)| ≤
      (2 / (fineStructureApprox : ℝ)) * ((6 / 5) * (bohrShellPhase n : ℝ) ^ 3) :=
    mul_le_mul_of_nonneg_left hgap (div_pos (by norm_num) hα).le
  have hx3 : (bohrShellPhase n : ℝ) ^ 3 ≤ ((fineStructureApprox : ℝ) / 8) ^ 3 := by
    have h0 : (0 : ℝ) ≤ (bohrShellPhase n : ℝ) := hx_pos.le
    exact pow_le_pow_left₀ h0 hx_le 3
  have hloose : (2 / (fineStructureApprox : ℝ)) * ((6 / 5) *
      (bohrShellPhase n : ℝ) ^ 3) ≤
      3 * (fineStructureApprox : ℝ) ^ 2 / 640 := by
    calc (2 / (fineStructureApprox : ℝ)) * ((6 / 5) * (bohrShellPhase n : ℝ) ^ 3)
        ≤ (2 / (fineStructureApprox : ℝ)) * ((6 / 5) * ((fineStructureApprox : ℝ) / 8) ^ 3) := by
          gcongr
      _ = 3 * (fineStructureApprox : ℝ) ^ 2 / 640 := by
          field_simp [hα.ne']
          norm_num
  have hα_lt : (fineStructureApprox : ℝ) < 73 / 10000 := by
    unfold fineStructureApprox fineStructureMantissa fineStructureScale
    norm_num
  have hfinal : 3 * (fineStructureApprox : ℝ) ^ 2 / 640 < 1 / 1000000 := by
    have hsq : (fineStructureApprox : ℝ) ^ 2 < (73 / 10000) ^ 2 := by
      have h0 : (0 : ℝ) ≤ (fineStructureApprox : ℝ) := hα.le
      exact pow_lt_pow_left₀ hα_lt h0 (by norm_num)
    have hnum : 3 * (fineStructureApprox : ℝ) ^ 2 / 640 <
        3 * ((73 : ℝ) / 10000) ^ 2 / 640 := by
      gcongr
    have hconst : 3 * ((73 : ℝ) / 10000) ^ 2 / 640 < 1 / 1000000 := by norm_num
    exact lt_trans hnum hconst
  linarith

/-- The Coulomb gap at shell `n ≥ 2` is at most `(3/10) α²/n⁶` of the ionisation. -/
theorem signedShell_coulomb_gap {n : ℕ} (hn : 2 ≤ n) :
    |signedShell n + 1 / (n : ℝ) ^ 2| ≤
      (3 / 10) * (fineStructureApprox : ℝ) ^ 2 / (n : ℝ) ^ 6 := by
  have hn0 : 0 < n := by omega
  have hx_pos : (0 : ℝ) < (bohrShellPhase n : ℝ) := by
    exact_mod_cast bohrShellPhase_pos hn0
  have hx_lt : (bohrShellPhase n : ℝ) < 1 / 100 := bohrShellPhase_lt_hundredth hn0
  have hgap := circEnergy_coulomb_gap ⟨hx_pos, hx_lt⟩
  have hα : (0 : ℝ) < (fineStructureApprox : ℝ) := by exact_mod_cast fineStructureApprox_pos
  have hxphase : (bohrShellPhase n : ℝ) =
      (fineStructureApprox : ℝ) / (2 * (n : ℝ) ^ 2) := by
    unfold bohrShellPhase
    norm_cast
  have hident : signedShell n + 1 / (n : ℝ) ^ 2 =
      (2 / (fineStructureApprox : ℝ)) *
        (circEnergy (bohrShellPhase n) + (bohrShellPhase n : ℝ)) := by
    unfold signedShell
    rw [hxphase]
    field_simp [hα.ne', (Nat.cast_pos.mpr hn0 : (0 : ℝ) < (n : ℝ)).ne']
  rw [hident]
  have habs : |(2 / (fineStructureApprox : ℝ)) *
      (circEnergy (bohrShellPhase n) + (bohrShellPhase n : ℝ))| =
      (2 / (fineStructureApprox : ℝ)) *
        |circEnergy (bohrShellPhase n) + (bohrShellPhase n : ℝ)| := by
    rw [abs_mul, abs_of_pos (div_pos (by norm_num) hα)]
  rw [habs]
  have hscale : (2 / (fineStructureApprox : ℝ)) *
      |circEnergy (bohrShellPhase n) + (bohrShellPhase n : ℝ)| ≤
      (2 / (fineStructureApprox : ℝ)) * ((6 / 5) * (bohrShellPhase n : ℝ) ^ 3) :=
    mul_le_mul_of_nonneg_left hgap (div_pos (by norm_num) hα).le
  refine le_trans hscale ?_
  rw [hxphase]
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn0.ne'
  have hpow : (2 / (fineStructureApprox : ℝ)) * ((6 / 5) *
      ((fineStructureApprox : ℝ) / (2 * (n : ℝ) ^ 2)) ^ 3) =
      (3 / 10) * (fineStructureApprox : ℝ) ^ 2 / (n : ℝ) ^ 6 := by
    field_simp [hα.ne', hn']
    ring
  exact le_of_eq hpow

/-- Outer-well potential at phase `x`, in units of the ionisation.
The Coulomb value is `-4x/α = -2 ke²/r` divided by the ionisation. -/
noncomputable def potentialDeepening (x : ℝ) : ℝ :=
  (4 / (fineStructureApprox : ℝ)) * (layerAccum x - x)

/-- Outside the Bohr radius, phase `x ≤ α/2`, the signed potential lies
strictly below the Coulomb potential, and the deepening is less than
`1/30000` of the ionisation. -/
theorem potentialDeepening_bohr_exterior {x : ℝ}
    (hx0 : 0 < x) (hx : x ≤ (fineStructureApprox : ℝ) / 2) :
    0 < potentialDeepening x ∧ potentialDeepening x < 1 / 30000 := by
  have hα : (0 : ℝ) < (fineStructureApprox : ℝ) := by exact_mod_cast fineStructureApprox_pos
  have hxlt : x < 1 / 100 := by
    have hα100 : (fineStructureApprox : ℝ) / 2 < 1 / 100 := by
      have hα' := fineStructureApprox_lt_one_fifty
      linarith
    exact lt_of_le_of_lt hx hα100
  have hgap := layerAccum_coulomb_gap ⟨hx0, hxlt⟩
  unfold potentialDeepening
  have hpos : 0 < (4 / (fineStructureApprox : ℝ)) * (layerAccum x - x) := by
    exact mul_pos (div_pos (by norm_num) hα) (sub_pos.mpr hgap.1)
  refine ⟨hpos, ?_⟩
  have hcubic : layerAccum x - x ≤ (6 / 5) * ((fineStructureApprox : ℝ) / 2) ^ 3 := by
    have hx3 : x ^ 3 ≤ ((fineStructureApprox : ℝ) / 2) ^ 3 := by
      exact pow_le_pow_left₀ hx0.le hx 3
    calc layerAccum x - x
        ≤ (6 / 5) * x ^ 3 := hgap.2
      _ ≤ (6 / 5) * ((fineStructureApprox : ℝ) / 2) ^ 3 := by gcongr
  have hscale : (4 / (fineStructureApprox : ℝ)) * (layerAccum x - x) ≤
      (3 / 5) * (fineStructureApprox : ℝ) ^ 2 := by
    calc (4 / (fineStructureApprox : ℝ)) * (layerAccum x - x)
        ≤ (4 / (fineStructureApprox : ℝ)) * ((6 / 5) * ((fineStructureApprox : ℝ) / 2) ^ 3) :=
          mul_le_mul_of_nonneg_left hcubic (div_pos (by norm_num) hα).le
      _ = (3 / 5) * (fineStructureApprox : ℝ) ^ 2 := by
          field_simp [hα.ne']
          ring
  have hα_lt : (fineStructureApprox : ℝ) < 73 / 10000 := by
    unfold fineStructureApprox fineStructureMantissa fineStructureScale
    norm_num
  have hconst : (3 / 5) * (fineStructureApprox : ℝ) ^ 2 < 1 / 30000 := by
    have hsq : (fineStructureApprox : ℝ) ^ 2 < (73 / 10000) ^ 2 := by
      exact pow_lt_pow_left₀ hα_lt hα.le (by norm_num)
    have hmul : (3 / 5) * (fineStructureApprox : ℝ) ^ 2 <
        (3 / 5) * ((73 : ℝ) / 10000) ^ 2 := by gcongr
    have hnum : (3 / 5) * ((73 : ℝ) / 10000) ^ 2 < 1 / 30000 := by norm_num
    exact lt_trans hmul hnum
  exact lt_of_le_of_lt hscale hconst

/-- Signed outer-well potential at a Bohr shell, in units of the ionisation.
The Coulomb value is `-2/n²`. -/
noncomputable def signedPotential (n : ℕ) : ℝ :=
  -((4 / (fineStructureApprox : ℝ)) * layerAccum (bohrShellPhase n))

theorem signedPotential_gap {n : ℕ} (hn : 0 < n) :
    0 < -(signedPotential n + 2 / (n : ℝ) ^ 2) ∧
      -(signedPotential n + 2 / (n : ℝ) ^ 2) ≤
        (3 / 5) * (fineStructureApprox : ℝ) ^ 2 / (n : ℝ) ^ 6 ∧
      -(signedPotential n + 2 / (n : ℝ) ^ 2) < 1 / 30000 := by
  have hx_pos : (0 : ℝ) < (bohrShellPhase n : ℝ) := by
    exact_mod_cast bohrShellPhase_pos hn
  have hx_lt : (bohrShellPhase n : ℝ) < 1 / 100 := bohrShellPhase_lt_hundredth hn
  have hgap := layerAccum_coulomb_gap ⟨hx_pos, hx_lt⟩
  have hα : (0 : ℝ) < (fineStructureApprox : ℝ) := by exact_mod_cast fineStructureApprox_pos
  have hxphase : (bohrShellPhase n : ℝ) =
      (fineStructureApprox : ℝ) / (2 * (n : ℝ) ^ 2) := by
    unfold bohrShellPhase
    norm_cast
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hident : -(signedPotential n + 2 / (n : ℝ) ^ 2) =
      (4 / (fineStructureApprox : ℝ)) *
        (layerAccum (bohrShellPhase n) - (bohrShellPhase n : ℝ)) := by
    unfold signedPotential
    rw [hxphase]
    field_simp [hα.ne', hn']
    ring
  rw [hident]
  have hpos : 0 < (4 / (fineStructureApprox : ℝ)) *
      (layerAccum (bohrShellPhase n) - (bohrShellPhase n : ℝ)) :=
    mul_pos (div_pos (by norm_num) hα) (sub_pos.mpr hgap.1)
  refine ⟨hpos, ?_, ?_⟩
  · calc (4 / (fineStructureApprox : ℝ)) *
          (layerAccum (bohrShellPhase n) - (bohrShellPhase n : ℝ))
        ≤ (4 / (fineStructureApprox : ℝ)) * ((6 / 5) * (bohrShellPhase n : ℝ) ^ 3) :=
          mul_le_mul_of_nonneg_left hgap.2 (div_pos (by norm_num) hα).le
      _ = (3 / 5) * (fineStructureApprox : ℝ) ^ 2 / (n : ℝ) ^ 6 := by
          rw [hxphase]
          field_simp [hα.ne', hn']
          ring
  · have hplateau := potentialDeepening_bohr_exterior hx_pos
      (by
        have hle := bohrShellPhase_le_half_alpha hn
        exact_mod_cast hle)
    simpa [potentialDeepening] using hplateau.2

theorem hAlpha_signed_shift :
    |signedShell 3 - signedShell 2 - (5 / 36)| < (1 / 10000) * (5 / 36) := by
  have h2 := signedShell_near_coulomb (n := 2) (by norm_num)
  have h3 := signedShell_near_coulomb (n := 3) (by norm_num)
  have hsplit : signedShell 3 - signedShell 2 - (5 / 36) =
      (signedShell 3 + 1 / (3 : ℝ) ^ 2) - (signedShell 2 + 1 / (2 : ℝ) ^ 2) := by
    have hnum : (1 : ℝ) / 3 ^ 2 - 1 / 2 ^ 2 = -(5 / 36) := by norm_num
    linarith
  obtain ⟨h3lo, h3hi⟩ := abs_lt.mp h3
  obtain ⟨h2lo, h2hi⟩ := abs_lt.mp h2
  rw [hsplit]
  have hpart : (2 : ℝ) / 1000000 < (1 / 10000) * (5 / 36) := by norm_num
  rw [abs_lt]
  constructor <;> linarith

/-! ### Vacuum wavelength -/

noncomputable def hAlphaWavelength : ℝ :=
  144 * π * (hbarApprox : ℝ) /
    (5 * (electronMassApprox : ℝ) * (speedOfLight : ℝ) * (fineStructureApprox : ℝ) ^ 2)

theorem hAlphaWavelength_eq_photon :
    hAlphaWavelength =
      2 * π * (hbarApprox : ℝ) * (speedOfLight : ℝ) / bohrEnergyDiff 2 3 := by
  rw [hAlphaWavelength, bohrEnergyDiff_hAlpha]
  simp only [hydrogenIonisationApprox]
  have hm : (electronMassApprox : ℝ) ≠ 0 := by exact_mod_cast electronMassApprox_pos.ne'
  have hc : (speedOfLight : ℝ) ≠ 0 := by exact_mod_cast speedOfLight_pos.ne'
  have hα : (fineStructureApprox : ℝ) ≠ 0 := by exact_mod_cast fineStructureApprox_pos.ne'
  push_cast
  field_simp [hm, hc, hα]
  ring

private theorem pi_gt_frac : (3141592 : ℝ) / 1000000 < π := by
  have heq : (3141592 : ℝ) / 1000000 = 3.141592 := by norm_num
  linarith [pi_gt_d6]

private theorem pi_lt_frac : π < (3141593 : ℝ) / 1000000 := by
  have heq : (3141593 : ℝ) / 1000000 = 3.141593 := by norm_num
  linarith [pi_lt_d6]

private theorem wavelength_factor_pos :
    (0 : ℝ) < 144 * (hbarApprox : ℝ) /
      (5 * (electronMassApprox : ℝ) * (speedOfLight : ℝ) * (fineStructureApprox : ℝ) ^ 2) := by
  have hnum : (0 : ℚ) < 144 * hbarApprox := mul_pos (by norm_num) hbarApprox_pos
  have hden : (0 : ℚ) < 5 * electronMassApprox * speedOfLight * fineStructureApprox ^ 2 :=
    mul_pos
      (mul_pos (mul_pos (by norm_num) electronMassApprox_pos) speedOfLight_pos)
      (pow_pos fineStructureApprox_pos 2)
  exact_mod_cast (div_pos hnum hden)

private theorem hAlpha_fixed_lo_rat :
    (656112 : ℚ) / 10 ^ 12 <
      144 * ((3141592 : ℚ) / 1000000) * hbarApprox /
        (5 * electronMassApprox * speedOfLight * fineStructureApprox ^ 2) := by
  unfold hbarApprox electronMassApprox fineStructureApprox speedOfLight
    hbarMantissa hbarScale electronMassMantissa electronMassScale
    fineStructureMantissa fineStructureScale speedOfLightNat
  field_simp
  norm_cast

private theorem hAlpha_fixed_hi_rat :
    144 * ((3141593 : ℚ) / 1000000) * hbarApprox /
        (5 * electronMassApprox * speedOfLight * fineStructureApprox ^ 2) <
      (656113 : ℚ) / 10 ^ 12 := by
  unfold hbarApprox electronMassApprox fineStructureApprox speedOfLight
    hbarMantissa hbarScale electronMassMantissa electronMassScale
    fineStructureMantissa fineStructureScale speedOfLightNat
  field_simp
  norm_cast

private theorem hAlpha_fixed_lo_real :
    (656112 : ℝ) / 10 ^ 12 <
      144 * ((3141592 : ℝ) / 1000000) * (hbarApprox : ℝ) /
        (5 * (electronMassApprox : ℝ) * (speedOfLight : ℝ) *
          (fineStructureApprox : ℝ) ^ 2) := by
  have hcast :
      ((656112 : ℚ) / 10 ^ 12 : ℝ) <
        ((144 * ((3141592 : ℚ) / 1000000) * hbarApprox /
          (5 * electronMassApprox * speedOfLight * fineStructureApprox ^ 2) : ℚ) : ℝ) := by
    exact_mod_cast hAlpha_fixed_lo_rat
  convert hcast using 1
  · push_cast
    rfl
  · push_cast
    ring

private theorem hAlpha_fixed_hi_real :
    144 * ((3141593 : ℝ) / 1000000) * (hbarApprox : ℝ) /
        (5 * (electronMassApprox : ℝ) * (speedOfLight : ℝ) *
          (fineStructureApprox : ℝ) ^ 2) <
      (656113 : ℝ) / 10 ^ 12 := by
  have hcast :
      ((144 * ((3141593 : ℚ) / 1000000) * hbarApprox /
        (5 * electronMassApprox * speedOfLight * fineStructureApprox ^ 2) : ℚ) : ℝ) <
        ((656113 : ℚ) / 10 ^ 12 : ℝ) := by
    exact_mod_cast hAlpha_fixed_hi_rat
  convert hcast using 1
  · push_cast
    ring
  · push_cast
    rfl

theorem hAlphaWavelength_bounds :
    (656112 : ℝ) / 10 ^ 12 < hAlphaWavelength ∧
      hAlphaWavelength < (656113 : ℝ) / 10 ^ 12 := by
  have hfac := wavelength_factor_pos
  unfold hAlphaWavelength
  constructor
  · refine lt_trans hAlpha_fixed_lo_real ?_
    calc 144 * ((3141592 : ℝ) / 1000000) * (hbarApprox : ℝ) /
          (5 * (electronMassApprox : ℝ) * (speedOfLight : ℝ) *
            (fineStructureApprox : ℝ) ^ 2)
        = (144 * (hbarApprox : ℝ) /
            (5 * (electronMassApprox : ℝ) * (speedOfLight : ℝ) *
              (fineStructureApprox : ℝ) ^ 2)) * ((3141592 : ℝ) / 1000000) := by ring
      _ < (144 * (hbarApprox : ℝ) /
            (5 * (electronMassApprox : ℝ) * (speedOfLight : ℝ) *
              (fineStructureApprox : ℝ) ^ 2)) * π :=
          mul_lt_mul_of_pos_left pi_gt_frac hfac
      _ = 144 * π * (hbarApprox : ℝ) /
            (5 * (electronMassApprox : ℝ) * (speedOfLight : ℝ) *
              (fineStructureApprox : ℝ) ^ 2) := by ring
  · refine lt_trans ?_ hAlpha_fixed_hi_real
    calc 144 * π * (hbarApprox : ℝ) /
          (5 * (electronMassApprox : ℝ) * (speedOfLight : ℝ) *
            (fineStructureApprox : ℝ) ^ 2)
        = (144 * (hbarApprox : ℝ) /
            (5 * (electronMassApprox : ℝ) * (speedOfLight : ℝ) *
              (fineStructureApprox : ℝ) ^ 2)) * π := by ring
      _ < (144 * (hbarApprox : ℝ) /
            (5 * (electronMassApprox : ℝ) * (speedOfLight : ℝ) *
              (fineStructureApprox : ℝ) ^ 2)) * ((3141593 : ℝ) / 1000000) :=
          mul_lt_mul_of_pos_left pi_lt_frac hfac
      _ = 144 * ((3141593 : ℝ) / 1000000) * (hbarApprox : ℝ) /
            (5 * (electronMassApprox : ℝ) * (speedOfLight : ℝ) *
              (fineStructureApprox : ℝ) ^ 2) := by ring

theorem massRatio_lengthens {ρ : ℝ} (hlo : (1836 : ℝ) < ρ) (hhi : ρ < 1837) :
    (1838 : ℝ) / 1837 < (ρ + 1) / ρ ∧ (ρ + 1) / ρ < (1837 : ℝ) / 1836 := by
  have hρ : 0 < ρ := by linarith
  constructor
  · rw [div_lt_div_iff₀ (by norm_num) hρ]
    linarith
  · rw [div_lt_div_iff₀ hρ (by norm_num)]
    linarith

private theorem hAlpha_shared_lo_rat :
    (656469 : ℚ) / 10 ^ 12 <
      144 * ((3141592 : ℚ) / 1000000) * hbarApprox /
        (5 * electronMassApprox * speedOfLight * fineStructureApprox ^ 2) *
        ((1838 : ℚ) / 1837) := by
  unfold hbarApprox electronMassApprox fineStructureApprox speedOfLight
    hbarMantissa hbarScale electronMassMantissa electronMassScale
    fineStructureMantissa fineStructureScale speedOfLightNat
  field_simp
  norm_cast

private theorem hAlpha_shared_hi_rat :
    144 * ((3141593 : ℚ) / 1000000) * hbarApprox /
        (5 * electronMassApprox * speedOfLight * fineStructureApprox ^ 2) *
        ((1837 : ℚ) / 1836) <
      (656470 : ℚ) / 10 ^ 12 := by
  unfold hbarApprox electronMassApprox fineStructureApprox speedOfLight
    hbarMantissa hbarScale electronMassMantissa electronMassScale
    fineStructureMantissa fineStructureScale speedOfLightNat
  field_simp
  norm_cast

private theorem hAlpha_shared_lo_real :
    (656469 : ℝ) / 10 ^ 12 <
      144 * ((3141592 : ℝ) / 1000000) * (hbarApprox : ℝ) /
        (5 * (electronMassApprox : ℝ) * (speedOfLight : ℝ) *
          (fineStructureApprox : ℝ) ^ 2) * ((1838 : ℝ) / 1837) := by
  have hcast :
      ((656469 : ℚ) / 10 ^ 12 : ℝ) <
        ((144 * ((3141592 : ℚ) / 1000000) * hbarApprox /
          (5 * electronMassApprox * speedOfLight * fineStructureApprox ^ 2) *
          ((1838 : ℚ) / 1837) : ℚ) : ℝ) := by
    exact_mod_cast hAlpha_shared_lo_rat
  convert hcast using 1
  · push_cast
    rfl
  · push_cast
    ring

private theorem hAlpha_shared_hi_real :
    144 * ((3141593 : ℝ) / 1000000) * (hbarApprox : ℝ) /
        (5 * (electronMassApprox : ℝ) * (speedOfLight : ℝ) *
          (fineStructureApprox : ℝ) ^ 2) * ((1837 : ℝ) / 1836) <
      (656470 : ℝ) / 10 ^ 12 := by
  have hcast :
      ((144 * ((3141593 : ℚ) / 1000000) * hbarApprox /
        (5 * electronMassApprox * speedOfLight * fineStructureApprox ^ 2) *
        ((1837 : ℚ) / 1836) : ℚ) : ℝ) <
        ((656470 : ℚ) / 10 ^ 12 : ℝ) := by
    exact_mod_cast hAlpha_shared_hi_rat
  convert hcast using 1
  · push_cast
    ring
  · push_cast
    rfl

theorem hAlpha_shared_wavelength {ρ : ℝ} (hlo : (1836 : ℝ) < ρ) (hhi : ρ < 1837) :
    (656469 : ℝ) / 10 ^ 12 < hAlphaWavelength * ((ρ + 1) / ρ) ∧
      hAlphaWavelength * ((ρ + 1) / ρ) < (656470 : ℝ) / 10 ^ 12 := by
  obtain ⟨hfacLo, hfacHi⟩ := massRatio_lengthens hlo hhi
  have hpos : 0 < hAlphaWavelength := by
    unfold hAlphaWavelength
    have hπ : (0 : ℝ) < π := Real.pi_pos
    have hrew : 144 * π * (hbarApprox : ℝ) /
        (5 * (electronMassApprox : ℝ) * (speedOfLight : ℝ) *
          (fineStructureApprox : ℝ) ^ 2) =
        (144 * (hbarApprox : ℝ) /
          (5 * (electronMassApprox : ℝ) * (speedOfLight : ℝ) *
            (fineStructureApprox : ℝ) ^ 2)) * π := by ring
    rw [hrew]
    exact mul_pos wavelength_factor_pos hπ
  constructor
  · have hendpoint : (656469 : ℝ) / 10 ^ 12 <
        hAlphaWavelength * ((1838 : ℝ) / 1837) := by
      refine lt_trans hAlpha_shared_lo_real ?_
      unfold hAlphaWavelength
      calc 144 * ((3141592 : ℝ) / 1000000) * (hbarApprox : ℝ) /
            (5 * (electronMassApprox : ℝ) * (speedOfLight : ℝ) *
              (fineStructureApprox : ℝ) ^ 2) * ((1838 : ℝ) / 1837)
          = (144 * (hbarApprox : ℝ) /
              (5 * (electronMassApprox : ℝ) * (speedOfLight : ℝ) *
                (fineStructureApprox : ℝ) ^ 2)) *
              ((3141592 : ℝ) / 1000000) * ((1838 : ℝ) / 1837) := by ring
        _ < (144 * (hbarApprox : ℝ) /
              (5 * (electronMassApprox : ℝ) * (speedOfLight : ℝ) *
                (fineStructureApprox : ℝ) ^ 2)) * π * ((1838 : ℝ) / 1837) := by
            have hpos := wavelength_factor_pos
            have hmul := mul_lt_mul_of_pos_left pi_gt_frac hpos
            have hscale := mul_lt_mul_of_pos_right hmul (by norm_num : (0 : ℝ) < 1838 / 1837)
            simpa [mul_assoc, mul_left_comm, mul_comm] using hscale
        _ = 144 * π * (hbarApprox : ℝ) /
              (5 * (electronMassApprox : ℝ) * (speedOfLight : ℝ) *
                (fineStructureApprox : ℝ) ^ 2) * ((1838 : ℝ) / 1837) := by ring
    exact lt_of_lt_of_le hendpoint
      (mul_le_mul_of_nonneg_left hfacLo.le hpos.le)
  · have hendpoint : hAlphaWavelength * ((1837 : ℝ) / 1836) <
        (656470 : ℝ) / 10 ^ 12 := by
      refine lt_trans ?_ hAlpha_shared_hi_real
      unfold hAlphaWavelength
      calc 144 * π * (hbarApprox : ℝ) /
            (5 * (electronMassApprox : ℝ) * (speedOfLight : ℝ) *
              (fineStructureApprox : ℝ) ^ 2) * ((1837 : ℝ) / 1836)
          = (144 * (hbarApprox : ℝ) /
              (5 * (electronMassApprox : ℝ) * (speedOfLight : ℝ) *
                (fineStructureApprox : ℝ) ^ 2)) * π * ((1837 : ℝ) / 1836) := by ring
        _ < (144 * (hbarApprox : ℝ) /
              (5 * (electronMassApprox : ℝ) * (speedOfLight : ℝ) *
                (fineStructureApprox : ℝ) ^ 2)) *
              ((3141593 : ℝ) / 1000000) * ((1837 : ℝ) / 1836) := by
            have hpos := wavelength_factor_pos
            have hmul := mul_lt_mul_of_pos_left pi_lt_frac hpos
            have hscale := mul_lt_mul_of_pos_right hmul (by norm_num : (0 : ℝ) < 1837 / 1836)
            simpa [mul_assoc, mul_left_comm, mul_comm] using hscale
        _ = 144 * ((3141593 : ℝ) / 1000000) * (hbarApprox : ℝ) /
              (5 * (electronMassApprox : ℝ) * (speedOfLight : ℝ) *
                (fineStructureApprox : ℝ) ^ 2) * ((1837 : ℝ) / 1836) := by ring
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hfacHi.le hpos.le) hendpoint

theorem hAlpha_proton_share :
    (656469 : ℝ) / 10 ^ 12 <
      hAlphaWavelength *
        (((protonElectronMassRatio : ℝ) + 1) / (protonElectronMassRatio : ℝ)) ∧
      hAlphaWavelength *
        (((protonElectronMassRatio : ℝ) + 1) / (protonElectronMassRatio : ℝ)) <
        (656470 : ℝ) / 10 ^ 12 := by
  have h := protonElectronMassRatio_bounds
  exact hAlpha_shared_wavelength (by exact_mod_cast h.1) (by exact_mod_cast h.2)

/-! ### Further bookkeeping fractions -/

theorem bohrEnergyDiff_lymanAlpha :
    bohrEnergyDiff 1 2 = (3 / 4) * (hydrogenIonisationApprox : ℝ) := by
  unfold bohrEnergyDiff
  norm_num
  ring

theorem bohrEnergyDiff_hBeta :
    bohrEnergyDiff 2 4 = (3 / 16) * (hydrogenIonisationApprox : ℝ) := by
  unfold bohrEnergyDiff
  norm_num
  ring

theorem bohrEnergyDiff_hGamma :
    bohrEnergyDiff 2 5 = (21 / 100) * (hydrogenIonisationApprox : ℝ) := by
  unfold bohrEnergyDiff
  norm_num
  ring

theorem bohrEnergyDiff_paschenAlpha :
    bohrEnergyDiff 3 4 = (7 / 144) * (hydrogenIonisationApprox : ℝ) := by
  unfold bohrEnergyDiff
  norm_num
  ring

theorem fineStructureApprox_lt_hundredth :
    (fineStructureApprox : ℝ) < 1 / 100 := by
  unfold fineStructureApprox fineStructureMantissa fineStructureScale
  norm_num

/-! ### Ground shell, and the other hydrogen differences -/

theorem signedShell_ground :
    |signedShell 1 + 1| < 1 / 60000 := by
  have hn0 : 0 < (1 : ℕ) := by norm_num
  have hx_pos : (0 : ℝ) < (bohrShellPhase 1 : ℝ) := by
    exact_mod_cast bohrShellPhase_pos hn0
  have hx_eq : (bohrShellPhase 1 : ℝ) = (fineStructureApprox : ℝ) / 2 := by
    unfold bohrShellPhase
    norm_num
  have hx_lt : (bohrShellPhase 1 : ℝ) < 1 / 100 := bohrShellPhase_lt_hundredth hn0
  have hgap := circEnergy_coulomb_gap ⟨hx_pos, hx_lt⟩
  have hα : (0 : ℝ) < (fineStructureApprox : ℝ) := by exact_mod_cast fineStructureApprox_pos
  have hident : signedShell 1 + 1 =
      (2 / (fineStructureApprox : ℝ)) *
        (circEnergy (bohrShellPhase 1) + (bohrShellPhase 1 : ℝ)) := by
    unfold signedShell
    rw [hx_eq]
    field_simp [hα.ne']
  rw [hident]
  have habs : |(2 / (fineStructureApprox : ℝ)) *
      (circEnergy (bohrShellPhase 1) + (bohrShellPhase 1 : ℝ))| =
      (2 / (fineStructureApprox : ℝ)) *
        |circEnergy (bohrShellPhase 1) + (bohrShellPhase 1 : ℝ)| := by
    rw [abs_mul, abs_of_pos (div_pos (by norm_num) hα)]
  rw [habs]
  have hscale : (2 / (fineStructureApprox : ℝ)) *
      |circEnergy (bohrShellPhase 1) + (bohrShellPhase 1 : ℝ)| ≤
      (2 / (fineStructureApprox : ℝ)) * ((6 / 5) * (bohrShellPhase 1 : ℝ) ^ 3) :=
    mul_le_mul_of_nonneg_left hgap (div_pos (by norm_num) hα).le
  have hloose : (2 / (fineStructureApprox : ℝ)) * ((6 / 5) *
      (bohrShellPhase 1 : ℝ) ^ 3) = (3 / 10) * (fineStructureApprox : ℝ) ^ 2 := by
    rw [hx_eq]
    field_simp [hα.ne']
    ring
  have hα_lt : (fineStructureApprox : ℝ) < 73 / 10000 := by
    unfold fineStructureApprox fineStructureMantissa fineStructureScale
    norm_num
  have hfinal : (3 / 10) * (fineStructureApprox : ℝ) ^ 2 < 1 / 60000 := by
    have hsq : (fineStructureApprox : ℝ) ^ 2 < (73 / 10000) ^ 2 := by
      exact pow_lt_pow_left₀ hα_lt hα.le (by norm_num)
    have hnum : (3 / 10) * (fineStructureApprox : ℝ) ^ 2 <
        (3 / 10) * ((73 : ℝ) / 10000) ^ 2 := by gcongr
    have hconst : (3 / 10) * ((73 : ℝ) / 10000) ^ 2 < 1 / 60000 := by norm_num
    exact lt_trans hnum hconst
  linarith

theorem lyman_signed_shift :
    |signedShell 2 - signedShell 1 - (3 / 4)| < (1 / 10000) * (3 / 4) := by
  have h2 := signedShell_near_coulomb (n := 2) (by norm_num)
  have h1 := signedShell_ground
  have hsplit : signedShell 2 - signedShell 1 - (3 / 4) =
      (signedShell 2 + 1 / (2 : ℝ) ^ 2) - (signedShell 1 + 1) := by
    have hnum : (1 : ℝ) / 2 ^ 2 - 1 = -(3 / 4) := by norm_num
    linarith
  obtain ⟨h2lo, h2hi⟩ := abs_lt.mp h2
  obtain ⟨h1lo, h1hi⟩ := abs_lt.mp h1
  rw [hsplit]
  have hpart : (1 : ℝ) / 1000000 + 1 / 60000 < (1 / 10000) * (3 / 4) := by norm_num
  rw [abs_lt]
  constructor <;> linarith

theorem hBeta_signed_shift :
    |signedShell 4 - signedShell 2 - (3 / 16)| < (1 / 10000) * (3 / 16) := by
  have h2 := signedShell_near_coulomb (n := 2) (by norm_num)
  have h4 := signedShell_near_coulomb (n := 4) (by norm_num)
  have hsplit : signedShell 4 - signedShell 2 - (3 / 16) =
      (signedShell 4 + 1 / (4 : ℝ) ^ 2) - (signedShell 2 + 1 / (2 : ℝ) ^ 2) := by
    have hnum : (1 : ℝ) / 4 ^ 2 - 1 / 2 ^ 2 = -(3 / 16) := by norm_num
    linarith
  obtain ⟨h4lo, h4hi⟩ := abs_lt.mp h4
  obtain ⟨h2lo, h2hi⟩ := abs_lt.mp h2
  rw [hsplit]
  have hpart : (2 : ℝ) / 1000000 < (1 / 10000) * (3 / 16) := by norm_num
  rw [abs_lt]
  constructor <;> linarith

theorem hGamma_signed_shift :
    |signedShell 5 - signedShell 2 - (21 / 100)| < (1 / 10000) * (21 / 100) := by
  have h2 := signedShell_near_coulomb (n := 2) (by norm_num)
  have h5 := signedShell_near_coulomb (n := 5) (by norm_num)
  have hsplit : signedShell 5 - signedShell 2 - (21 / 100) =
      (signedShell 5 + 1 / (5 : ℝ) ^ 2) - (signedShell 2 + 1 / (2 : ℝ) ^ 2) := by
    have hnum : (1 : ℝ) / 5 ^ 2 - 1 / 2 ^ 2 = -(21 / 100) := by norm_num
    linarith
  obtain ⟨h5lo, h5hi⟩ := abs_lt.mp h5
  obtain ⟨h2lo, h2hi⟩ := abs_lt.mp h2
  rw [hsplit]
  have hpart : (2 : ℝ) / 1000000 < (1 / 10000) * (21 / 100) := by norm_num
  rw [abs_lt]
  constructor <;> linarith

theorem paschen_signed_shift :
    |signedShell 4 - signedShell 3 - (7 / 144)| < (1 / 10000) * (7 / 144) := by
  have h3 := signedShell_near_coulomb (n := 3) (by norm_num)
  have h4 := signedShell_near_coulomb (n := 4) (by norm_num)
  have hsplit : signedShell 4 - signedShell 3 - (7 / 144) =
      (signedShell 4 + 1 / (4 : ℝ) ^ 2) - (signedShell 3 + 1 / (3 : ℝ) ^ 2) := by
    have hnum : (1 : ℝ) / 4 ^ 2 - 1 / 3 ^ 2 = -(7 / 144) := by norm_num
    linarith
  obtain ⟨h4lo, h4hi⟩ := abs_lt.mp h4
  obtain ⟨h3lo, h3hi⟩ := abs_lt.mp h3
  rw [hsplit]
  have hpart : (2 : ℝ) / 1000000 < (1 / 10000) * (7 / 144) := by norm_num
  rw [abs_lt]
  constructor <;> linarith

end Gravity

end DstDiophantine
