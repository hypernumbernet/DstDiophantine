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
* The ground shell departs from \(-1\) by less than \(1/60000\). The
  bookkeeping steps \(2\to 1\), \(4\to 2\), \(5\to 2\), and \(4\to 3\) are
  \(3/4\), \(3/16\), \(21/100\), and \(7/144\) of the ionisation, and each
  circular-energy difference departs from that fraction by less than one
  part in ten thousand of it.
* With nuclear charge two the hydrogenic phases \(Z\alpha/(2n^2)\) stay
  below \(1/100\), in the outer well, on the restoring side. The steps
  \(2\to 1\) and \(4\to 3\) are three ionisations and \(7/36\) of one, and
  each departs from that fraction by less than one part in ten thousand.
  The even shells repeat hydrogen fractions: \(4\to 2\), \(6\to 4\),
  \(8\to 4\), and \(10\to 4\) are \(3/4\), \(5/36\), \(3/16\), and
  \(21/100\), each within one part in ten thousand. With nuclear charge
  three the hydrogenic phases stay below \(1/90\), in the outer well, on
  the restoring side. The steps \(2\to 1\) and \(4\to 3\) are \(27/4\)
  ionisations and \(7/16\) of one, each within one part in ten thousand.
  Shells scaled by three, \(6\to 3\), \(9\to 6\), \(12\to 6\), and
  \(15\to 6\), repeat \(3/4\), \(5/36\), \(3/16\), and \(21/100\), each
  within one part in ten thousand. A nucleus of charge three together
  with the two electrons of the first shell leaves one electron on the
  second shell, feeling charge one. The monopole and the dipole of that
  shell share its phase, so both the bookkeeping step and the
  circular-energy step vanish. With nuclear charge
  eleven the hydrogenic phases stay below \(1/20\), in the outer well, on
  the restoring side. The bookkeeping steps \(2\to 1\) and \(4\to 3\) are
  \(363/4\) ionisations and \(847/144\) of one; the second departs from
  that fraction by less than one part in ten thousand. Shells scaled by
  eleven, \(22\to 11\), \(33\to 22\), \(44\to 22\), and \(55\to 22\),
  repeat \(3/4\), \(5/36\), \(3/16\), and \(21/100\), each within one part
  in ten thousand. A nucleus of charge eleven together with the ten
  electrons of the first two shells leaves one electron on the third
  shell, feeling charge one. The monopole and the dipole of that shell
  share its phase, so both the bookkeeping step and the circular-energy
  step vanish. The radius law, including the charge, remains an input.
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

/-! ### Charge two: the one-electron ion -/

/-- Hydrogenic phase \(Z\alpha/(2n^2)\), the Bohr shell of charge \(Z\) once
the electromagnetic length is the reduced Compton wavelength. -/
def hydrogenicPhase (Z n : ℕ) : ℚ :=
  (Z : ℚ) * fineStructureApprox / (2 * (n : ℚ) ^ 2)

/-- Signed circular energy in units of the hydrogen ionisation. The Coulomb
value is \(-Z^2/n^2\). -/
noncomputable def signedCharge (Z n : ℕ) : ℝ :=
  (2 * (Z : ℝ) / (fineStructureApprox : ℝ)) * circEnergy (hydrogenicPhase Z n)

theorem hydrogenicPhase_two_pos {n : ℕ} (hn : 0 < n) :
    (0 : ℚ) < hydrogenicPhase 2 n := by
  unfold hydrogenicPhase
  exact div_pos (mul_pos (by norm_num) fineStructureApprox_pos)
    (mul_pos (by norm_num) (pow_pos (Nat.cast_pos.mpr hn) 2))

theorem hydrogenicPhase_two_le_alpha {n : ℕ} (hn : 0 < n) :
    hydrogenicPhase 2 n ≤ fineStructureApprox := by
  unfold hydrogenicPhase
  have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  have hn1 : (1 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn
  have hsq : (1 : ℚ) ≤ (n : ℚ) ^ 2 := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℚ) ≤ 1) hn1 2
    simpa using this
  have hα : (0 : ℚ) ≤ fineStructureApprox := fineStructureApprox_pos.le
  calc (2 : ℚ) * fineStructureApprox / (2 * (n : ℚ) ^ 2)
      = fineStructureApprox / (n : ℚ) ^ 2 := by field_simp [hn']
    _ ≤ fineStructureApprox / 1 :=
        div_le_div_of_nonneg_left hα (by norm_num) hsq
    _ = fineStructureApprox := by ring

theorem hydrogenicPhase_two_le_quarter {n : ℕ} (hn : 2 ≤ n) :
    hydrogenicPhase 2 n ≤ fineStructureApprox / 4 := by
  unfold hydrogenicPhase
  have hn' : (n : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le (by norm_num : 0 < 2) hn))
  have hn2 : (4 : ℚ) ≤ (n : ℚ) ^ 2 := by
    have hn'' : (2 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn
    have := pow_le_pow_left₀ (by norm_num : (0 : ℚ) ≤ 2) hn'' 2
    simpa [show (2 : ℚ) ^ 2 = 4 by norm_num] using this
  have hα : (0 : ℚ) ≤ fineStructureApprox := fineStructureApprox_pos.le
  calc (2 : ℚ) * fineStructureApprox / (2 * (n : ℚ) ^ 2)
      = fineStructureApprox / (n : ℚ) ^ 2 := by field_simp [hn']
    _ ≤ fineStructureApprox / 4 :=
        div_le_div_of_nonneg_left hα (by norm_num) hn2

theorem hydrogenicPhase_two_lt_hundredth {n : ℕ} (hn : 0 < n) :
    (hydrogenicPhase 2 n : ℝ) < 1 / 100 := by
  have hle := hydrogenicPhase_two_le_alpha hn
  exact lt_of_le_of_lt (by exact_mod_cast hle) fineStructureApprox_lt_hundredth

theorem hydrogenicPhase_two_mem_outer {n : ℕ} (hn : 0 < n) :
    (hydrogenicPhase 2 n : ℝ) ∈ Ioo (0 : ℝ) resonanceRoot1 := by
  refine ⟨by exact_mod_cast hydrogenicPhase_two_pos hn, ?_⟩
  have h100 := hydrogenicPhase_two_lt_hundredth hn
  have hnode : (1 / 100 : ℝ) < resonanceRoot1 := by
    have hπ : (1 / 100 : ℝ) < π / 4 := by linarith [pi_gt_three]
    exact lt_trans hπ resonanceRoot1_sharp_bounds.1
  exact lt_trans h100 hnode

theorem hydrogenicTwo_restoring {n : ℕ} (hn : 0 < n) :
    0 < circStable (hydrogenicPhase 2 n) ∧
      (hydrogenicPhase 2 n : ℝ) * deriv pairAttraction (hydrogenicPhase 2 n) /
          pairAttraction (hydrogenicPhase 2 n) < 3 := by
  obtain ⟨y, hy, _⟩ := exists_unique_circStable
  have hx := hydrogenicPhase_two_mem_outer hn
  have hlt : (hydrogenicPhase 2 n : ℝ) < y := by
    have h100 := hydrogenicPhase_two_lt_hundredth hn
    linarith [hy.1.1]
  have hsign := circStable_outer_sign hx hy.1 hy.2
  have hpos : 0 < circStable (hydrogenicPhase 2 n) := hsign.1.mpr hlt
  exact ⟨hpos, (pairAttraction_logDeriv_lt_three_outer_iff hx).mpr hpos⟩

theorem hydrogenicPhase_two_ground :
    hydrogenicPhase 2 1 = fineStructureApprox := by
  unfold hydrogenicPhase
  norm_num

theorem signedCharge_two_ground :
    |signedCharge 2 1 + 4| < 1 / 3900 := by
  have hx_pos : (0 : ℝ) < (hydrogenicPhase 2 1 : ℝ) := by
    exact_mod_cast hydrogenicPhase_two_pos (by norm_num : 0 < (1 : ℕ))
  have hx_eq : (hydrogenicPhase 2 1 : ℝ) = (fineStructureApprox : ℝ) := by
    exact_mod_cast hydrogenicPhase_two_ground
  have hx_lt : (hydrogenicPhase 2 1 : ℝ) < 1 / 100 :=
    hydrogenicPhase_two_lt_hundredth (by norm_num)
  have hgap := circEnergy_coulomb_gap ⟨hx_pos, hx_lt⟩
  have hα : (0 : ℝ) < (fineStructureApprox : ℝ) := by exact_mod_cast fineStructureApprox_pos
  have hident : signedCharge 2 1 + 4 =
      (4 / (fineStructureApprox : ℝ)) *
        (circEnergy (hydrogenicPhase 2 1) + (hydrogenicPhase 2 1 : ℝ)) := by
    unfold signedCharge
    rw [hx_eq]
    field_simp [hα.ne']
    ring
  rw [hident]
  have habs : |(4 / (fineStructureApprox : ℝ)) *
      (circEnergy (hydrogenicPhase 2 1) + (hydrogenicPhase 2 1 : ℝ))| =
      (4 / (fineStructureApprox : ℝ)) *
        |circEnergy (hydrogenicPhase 2 1) + (hydrogenicPhase 2 1 : ℝ)| := by
    rw [abs_mul, abs_of_pos (div_pos (by norm_num) hα)]
  rw [habs]
  have hscale : (4 / (fineStructureApprox : ℝ)) *
      |circEnergy (hydrogenicPhase 2 1) + (hydrogenicPhase 2 1 : ℝ)| ≤
      (4 / (fineStructureApprox : ℝ)) *
        ((6 / 5) * (hydrogenicPhase 2 1 : ℝ) ^ 3) :=
    mul_le_mul_of_nonneg_left hgap (div_pos (by norm_num) hα).le
  have hloose : (4 / (fineStructureApprox : ℝ)) *
      ((6 / 5) * (hydrogenicPhase 2 1 : ℝ) ^ 3) =
      (24 / 5) * (fineStructureApprox : ℝ) ^ 2 := by
    rw [hx_eq]
    field_simp [hα.ne']
    ring
  have hα_lt : (fineStructureApprox : ℝ) < 73 / 10000 := by
    unfold fineStructureApprox fineStructureMantissa fineStructureScale
    norm_num
  have hfinal : (24 / 5) * (fineStructureApprox : ℝ) ^ 2 < 1 / 3900 := by
    have hsq : (fineStructureApprox : ℝ) ^ 2 < (73 / 10000) ^ 2 := by
      exact pow_lt_pow_left₀ hα_lt hα.le (by norm_num)
    have hnum : (24 / 5) * (fineStructureApprox : ℝ) ^ 2 <
        (24 / 5) * ((73 : ℝ) / 10000) ^ 2 := by gcongr
    have hconst : (24 / 5) * ((73 : ℝ) / 10000) ^ 2 < 1 / 3900 := by norm_num
    exact lt_trans hnum hconst
  linarith

theorem signedCharge_two_excited {n : ℕ} (hn : 2 ≤ n) :
    |signedCharge 2 n + 4 / (n : ℝ) ^ 2| < 1 / 250000 := by
  have hn0 : 0 < n := by omega
  have hx_pos : (0 : ℝ) < (hydrogenicPhase 2 n : ℝ) := by
    exact_mod_cast hydrogenicPhase_two_pos hn0
  have hx_le : (hydrogenicPhase 2 n : ℝ) ≤ (fineStructureApprox : ℝ) / 4 := by
    exact_mod_cast hydrogenicPhase_two_le_quarter hn
  have hx_lt : (hydrogenicPhase 2 n : ℝ) < 1 / 100 :=
    hydrogenicPhase_two_lt_hundredth hn0
  have hgap := circEnergy_coulomb_gap ⟨hx_pos, hx_lt⟩
  have hα : (0 : ℝ) < (fineStructureApprox : ℝ) := by exact_mod_cast fineStructureApprox_pos
  have hident : signedCharge 2 n + 4 / (n : ℝ) ^ 2 =
      (4 / (fineStructureApprox : ℝ)) *
        (circEnergy (hydrogenicPhase 2 n) + (hydrogenicPhase 2 n : ℝ)) := by
    have hxQ : hydrogenicPhase 2 n = fineStructureApprox / (n : ℚ) ^ 2 := by
      unfold hydrogenicPhase
      have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn0.ne'
      field_simp [hn']
      ring
    have hxphase : (hydrogenicPhase 2 n : ℝ) =
        (fineStructureApprox : ℝ) / (n : ℝ) ^ 2 := by
      exact_mod_cast hxQ
    unfold signedCharge
    rw [hxphase]
    field_simp [hα.ne', (Nat.cast_pos.mpr hn0 : (0 : ℝ) < (n : ℝ)).ne']
    ring
  rw [hident]
  have habs : |(4 / (fineStructureApprox : ℝ)) *
      (circEnergy (hydrogenicPhase 2 n) + (hydrogenicPhase 2 n : ℝ))| =
      (4 / (fineStructureApprox : ℝ)) *
        |circEnergy (hydrogenicPhase 2 n) + (hydrogenicPhase 2 n : ℝ)| := by
    rw [abs_mul, abs_of_pos (div_pos (by norm_num) hα)]
  rw [habs]
  have hscale : (4 / (fineStructureApprox : ℝ)) *
      |circEnergy (hydrogenicPhase 2 n) + (hydrogenicPhase 2 n : ℝ)| ≤
      (4 / (fineStructureApprox : ℝ)) * ((6 / 5) * (hydrogenicPhase 2 n : ℝ) ^ 3) :=
    mul_le_mul_of_nonneg_left hgap (div_pos (by norm_num) hα).le
  have hloose : (4 / (fineStructureApprox : ℝ)) * ((6 / 5) *
      (hydrogenicPhase 2 n : ℝ) ^ 3) ≤ (3 / 40) * (fineStructureApprox : ℝ) ^ 2 := by
    calc (4 / (fineStructureApprox : ℝ)) * ((6 / 5) * (hydrogenicPhase 2 n : ℝ) ^ 3)
        ≤ (4 / (fineStructureApprox : ℝ)) * ((6 / 5) *
            ((fineStructureApprox : ℝ) / 4) ^ 3) := by gcongr
      _ = (24 / 320) * (fineStructureApprox : ℝ) ^ 2 := by
          field_simp [hα.ne']
          ring
      _ = (3 / 40) * (fineStructureApprox : ℝ) ^ 2 := by norm_num
  have hα_lt : (fineStructureApprox : ℝ) < 73 / 10000 := by
    unfold fineStructureApprox fineStructureMantissa fineStructureScale
    norm_num
  have hfinal : (3 / 40) * (fineStructureApprox : ℝ) ^ 2 < 1 / 250000 := by
    have hsq : (fineStructureApprox : ℝ) ^ 2 < (73 / 10000) ^ 2 := by
      exact pow_lt_pow_left₀ hα_lt hα.le (by norm_num)
    have hnum : (3 / 40) * (fineStructureApprox : ℝ) ^ 2 <
        (3 / 40) * ((73 : ℝ) / 10000) ^ 2 := by gcongr
    have hconst : (3 / 40) * ((73 : ℝ) / 10000) ^ 2 < 1 / 250000 := by norm_num
    exact lt_trans hnum hconst
  linarith

theorem heLyman_signed_shift :
    |signedCharge 2 2 - signedCharge 2 1 - 3| < (1 / 10000) * 3 := by
  have h2 := signedCharge_two_excited (n := 2) (by norm_num)
  have h1 := signedCharge_two_ground
  have hsplit : signedCharge 2 2 - signedCharge 2 1 - 3 =
      (signedCharge 2 2 + 4 / (2 : ℝ) ^ 2) - (signedCharge 2 1 + 4) := by
    have hnum : (4 : ℝ) / 2 ^ 2 - 4 = -3 := by norm_num
    linarith
  obtain ⟨h2lo, h2hi⟩ := abs_lt.mp h2
  obtain ⟨h1lo, h1hi⟩ := abs_lt.mp h1
  rw [hsplit]
  have hpart : (1 : ℝ) / 250000 + 1 / 3900 < (1 / 10000) * 3 := by norm_num
  rw [abs_lt]
  constructor <;> linarith

theorem heVisible_signed_shift :
    |signedCharge 2 4 - signedCharge 2 3 - (7 / 36)| < (1 / 10000) * (7 / 36) := by
  have h4 := signedCharge_two_excited (n := 4) (by norm_num)
  have h3 := signedCharge_two_excited (n := 3) (by norm_num)
  have hsplit : signedCharge 2 4 - signedCharge 2 3 - (7 / 36) =
      (signedCharge 2 4 + 4 / (4 : ℝ) ^ 2) - (signedCharge 2 3 + 4 / (3 : ℝ) ^ 2) := by
    have hnum : (4 : ℝ) / 3 ^ 2 - 4 / 4 ^ 2 = 7 / 36 := by norm_num
    linarith
  obtain ⟨h4lo, h4hi⟩ := abs_lt.mp h4
  obtain ⟨h3lo, h3hi⟩ := abs_lt.mp h3
  rw [hsplit]
  have hpart : (2 : ℝ) / 250000 < (1 / 10000) * (7 / 36) := by norm_num
  rw [abs_lt]
  constructor <;> linarith

/-- Both shells excited: the two Coulomb gaps of `signedCharge_two_excited`
add, and the photon step is the difference of the Coulomb values. -/
private theorem signedCharge_two_step {n m : ℕ} {frac : ℝ}
    (hn : 2 ≤ n) (hm : 2 ≤ m)
    (hfrac : (4 : ℝ) / (n : ℝ) ^ 2 - 4 / (m : ℝ) ^ 2 = frac)
    (hroom : (2 : ℝ) / 250000 < (1 / 10000) * frac) :
    |signedCharge 2 m - signedCharge 2 n - frac| < (1 / 10000) * frac := by
  have hn' := signedCharge_two_excited hn
  have hm' := signedCharge_two_excited hm
  have hsplit : signedCharge 2 m - signedCharge 2 n - frac =
      (signedCharge 2 m + 4 / (m : ℝ) ^ 2) -
        (signedCharge 2 n + 4 / (n : ℝ) ^ 2) := by
    linarith
  obtain ⟨hmlo, hmhi⟩ := abs_lt.mp hm'
  obtain ⟨hnlo, hnhi⟩ := abs_lt.mp hn'
  rw [hsplit, abs_lt]
  constructor <;> linarith

theorem heMatchLyman_signed_shift :
    |signedCharge 2 4 - signedCharge 2 2 - (3 / 4)| < (1 / 10000) * (3 / 4) :=
  signedCharge_two_step (n := 2) (m := 4) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem heMatchAlpha_signed_shift :
    |signedCharge 2 6 - signedCharge 2 4 - (5 / 36)| < (1 / 10000) * (5 / 36) :=
  signedCharge_two_step (n := 4) (m := 6) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem heMatchBeta_signed_shift :
    |signedCharge 2 8 - signedCharge 2 4 - (3 / 16)| < (1 / 10000) * (3 / 16) :=
  signedCharge_two_step (n := 4) (m := 8) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem heMatchGamma_signed_shift :
    |signedCharge 2 10 - signedCharge 2 4 - (21 / 100)| <
      (1 / 10000) * (21 / 100) :=
  signedCharge_two_step (n := 4) (m := 10) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

/-! ### Charge one after the first two shells

The first two principal shells hold ten electrons. Charge eleven minus
those ten leaves one, and the remaining electron sits on the third shell.
The monopole and the dipole of one shell index share one phase, so the
yellow doublet — that step — has circular energy zero. There is no
fine-structure splitting. The bare charge \(Z=11\) is a separate ladder.
-/

theorem hydrogenicPhase_one {n : ℕ} (hn : 0 < n) :
    hydrogenicPhase 1 n = bohrShellPhase n := by
  unfold hydrogenicPhase bohrShellPhase
  have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp [hn']
  ring

theorem sodiumCore_electrons :
    2 * 1 ^ 2 + 2 * 2 ^ 2 = 10 ∧ 11 - (2 * 1 ^ 2 + 2 * 2 ^ 2) = 1 := by
  constructor <;> norm_num

theorem sodiumValence_restoring :
    0 < circStable (hydrogenicPhase 1 3) ∧
      (hydrogenicPhase 1 3 : ℝ) * deriv pairAttraction (hydrogenicPhase 1 3) /
          pairAttraction (hydrogenicPhase 1 3) < 3 := by
  rw [hydrogenicPhase_one (by norm_num : 0 < (3 : ℕ))]
  exact bohrShell_restoring (by norm_num)

theorem sodiumValence_book :
    ((11 - (2 * 1 ^ 2 + 2 * 2 ^ 2) : ℕ) : ℝ) ^ 2 * bohrEnergyDiff 3 3 = 0 := by
  have hcore : (11 - (2 * 1 ^ 2 + 2 * 2 ^ 2) : ℕ) = 1 := sodiumCore_electrons.2
  rw [hcore]
  unfold bohrEnergyDiff
  norm_num

theorem sodiumValence_circ :
    signedCharge (11 - (2 * 1 ^ 2 + 2 * 2 ^ 2)) 3 -
        signedCharge (11 - (2 * 1 ^ 2 + 2 * 2 ^ 2)) 3 = 0 := by
  ring

theorem hydrogenicPhase_eleven_pos {n : ℕ} (hn : 0 < n) :
    (0 : ℚ) < hydrogenicPhase 11 n := by
  unfold hydrogenicPhase
  exact div_pos (mul_pos (by norm_num) fineStructureApprox_pos)
    (mul_pos (by norm_num) (pow_pos (Nat.cast_pos.mpr hn) 2))

theorem hydrogenicPhase_eleven_le_ground {n : ℕ} (hn : 0 < n) :
    hydrogenicPhase 11 n ≤ 11 * fineStructureApprox / 2 := by
  unfold hydrogenicPhase
  have hn1 : (1 : ℚ) ≤ (n : ℚ) ^ 2 := by
    have hn' : (1 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn
    have := pow_le_pow_left₀ (by norm_num : (0 : ℚ) ≤ 1) hn' 2
    simpa using this
  have hnum : (0 : ℚ) ≤ 11 * fineStructureApprox :=
    mul_nonneg (by norm_num) fineStructureApprox_pos.le
  exact div_le_div_of_nonneg_left hnum (by norm_num)
    (by nlinarith [hn1])

theorem hydrogenicPhase_eleven_lt_twentieth {n : ℕ} (hn : 0 < n) :
    (hydrogenicPhase 11 n : ℝ) < 1 / 20 := by
  have hle := hydrogenicPhase_eleven_le_ground hn
  have hα : (fineStructureApprox : ℝ) < 73 / 10000 := by
    unfold fineStructureApprox fineStructureMantissa fineStructureScale
    norm_num
  have hground : (11 : ℝ) * (fineStructureApprox : ℝ) / 2 < 1 / 20 := by
    have hmul : (11 : ℝ) * (fineStructureApprox : ℝ) <
        (11 : ℝ) * (73 / 10000) :=
      mul_lt_mul_of_pos_left hα (by norm_num)
    have hdiv : (11 : ℝ) * (fineStructureApprox : ℝ) / 2 <
        (11 : ℝ) * (73 / 10000) / 2 := by
      exact div_lt_div_of_pos_right hmul (by norm_num)
    have hconst : (11 : ℝ) * (73 / 10000) / 2 < 1 / 20 := by norm_num
    linarith
  exact lt_of_le_of_lt (by exact_mod_cast hle) hground

theorem hydrogenicPhase_eleven_mem_outer {n : ℕ} (hn : 0 < n) :
    (hydrogenicPhase 11 n : ℝ) ∈ Ioo (0 : ℝ) resonanceRoot1 := by
  refine ⟨by exact_mod_cast hydrogenicPhase_eleven_pos hn, ?_⟩
  have h20 := hydrogenicPhase_eleven_lt_twentieth hn
  have hnode : (1 / 20 : ℝ) < resonanceRoot1 := by
    have hπ : (1 / 20 : ℝ) < π / 4 := by linarith [pi_gt_three]
    exact lt_trans hπ resonanceRoot1_sharp_bounds.1
  exact lt_trans h20 hnode

theorem hydrogenicEleven_restoring {n : ℕ} (hn : 0 < n) :
    0 < circStable (hydrogenicPhase 11 n) ∧
      (hydrogenicPhase 11 n : ℝ) * deriv pairAttraction (hydrogenicPhase 11 n) /
          pairAttraction (hydrogenicPhase 11 n) < 3 := by
  obtain ⟨y, hy, _⟩ := exists_unique_circStable
  have hx := hydrogenicPhase_eleven_mem_outer hn
  have hlt : (hydrogenicPhase 11 n : ℝ) < y := by
    have h20 := hydrogenicPhase_eleven_lt_twentieth hn
    have hhalf : (1 / 20 : ℝ) < 1 / 2 := by norm_num
    linarith [hy.1.1, hhalf]
  have hsign := circStable_outer_sign hx hy.1 hy.2
  have hpos : 0 < circStable (hydrogenicPhase 11 n) := hsign.1.mpr hlt
  exact ⟨hpos, (pairAttraction_logDeriv_lt_three_outer_iff hx).mpr hpos⟩

theorem hydrogenicPhase_eleven_le_div22 {n : ℕ} (hn : 11 ≤ n) :
    hydrogenicPhase 11 n ≤ fineStructureApprox / 22 := by
  unfold hydrogenicPhase
  have hn11 : (11 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn
  have hn2 : (121 : ℚ) ≤ (n : ℚ) ^ 2 := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℚ) ≤ 11) hn11 2
    simpa [show (11 : ℚ) ^ 2 = 121 by norm_num] using this
  have hnum : (0 : ℚ) ≤ 11 * fineStructureApprox :=
    mul_nonneg (by norm_num) fineStructureApprox_pos.le
  have hden : (2 : ℚ) * 121 ≤ 2 * (n : ℚ) ^ 2 := by nlinarith
  calc (11 : ℚ) * fineStructureApprox / (2 * (n : ℚ) ^ 2)
      ≤ 11 * fineStructureApprox / (2 * 121) :=
        div_le_div_of_nonneg_left hnum (by norm_num) hden
    _ = fineStructureApprox / 22 := by ring

theorem naLyman_book :
    (11 : ℝ) ^ 2 * bohrEnergyDiff 1 2 =
      (363 / 4) * (hydrogenIonisationApprox : ℝ) := by
  rw [bohrEnergyDiff_lymanAlpha]
  norm_num
  ring

theorem naFourThree_book :
    (11 : ℝ) ^ 2 * bohrEnergyDiff 3 4 =
      (847 / 144) * (hydrogenIonisationApprox : ℝ) := by
  rw [bohrEnergyDiff_paschenAlpha]
  norm_num
  ring

private theorem signedCharge_eleven_close {n : ℕ} {bound target : ℝ}
    (hn : 0 < n)
    (hxle : (hydrogenicPhase 11 n : ℝ) ≤ bound * (fineStructureApprox : ℝ))
    (hbound : 0 < bound)
    (hsmall : bound * (73 / 10000) < 1 / 100)
    (hcoeff : (22 : ℝ) * (6 / 5) * bound ^ 3 * ((73 : ℝ) / 10000) ^ 2 < target) :
    |signedCharge 11 n + 121 / (n : ℝ) ^ 2| < target := by
  have hx_pos : (0 : ℝ) < (hydrogenicPhase 11 n : ℝ) := by
    exact_mod_cast hydrogenicPhase_eleven_pos hn
  have hα : (0 : ℝ) < (fineStructureApprox : ℝ) := by exact_mod_cast fineStructureApprox_pos
  have hα_lt : (fineStructureApprox : ℝ) < 73 / 10000 := by
    unfold fineStructureApprox fineStructureMantissa fineStructureScale
    norm_num
  have hxphase : (hydrogenicPhase 11 n : ℝ) =
      (11 : ℝ) * (fineStructureApprox : ℝ) / (2 * (n : ℝ) ^ 2) := by
    unfold hydrogenicPhase
    push_cast
    ring
  have hx_lt : (hydrogenicPhase 11 n : ℝ) < 1 / 100 := by
    have hmul : bound * (fineStructureApprox : ℝ) < bound * (73 / 10000) :=
      mul_lt_mul_of_pos_left hα_lt hbound
    linarith [hxle, hsmall]
  have hgap := circEnergy_coulomb_gap ⟨hx_pos, hx_lt⟩
  have hident : signedCharge 11 n + 121 / (n : ℝ) ^ 2 =
      (22 / (fineStructureApprox : ℝ)) *
        (circEnergy (hydrogenicPhase 11 n) + (hydrogenicPhase 11 n : ℝ)) := by
    unfold signedCharge
    rw [hxphase]
    field_simp [hα.ne', (Nat.cast_pos.mpr hn : (0 : ℝ) < (n : ℝ)).ne']
    ring
  rw [hident]
  have habs : |(22 / (fineStructureApprox : ℝ)) *
      (circEnergy (hydrogenicPhase 11 n) + (hydrogenicPhase 11 n : ℝ))| =
      (22 / (fineStructureApprox : ℝ)) *
        |circEnergy (hydrogenicPhase 11 n) + (hydrogenicPhase 11 n : ℝ)| := by
    rw [abs_mul, abs_of_pos (div_pos (by norm_num) hα)]
  rw [habs]
  have hscale : (22 / (fineStructureApprox : ℝ)) *
      |circEnergy (hydrogenicPhase 11 n) + (hydrogenicPhase 11 n : ℝ)| ≤
      (22 / (fineStructureApprox : ℝ)) *
        ((6 / 5) * (hydrogenicPhase 11 n : ℝ) ^ 3) :=
    mul_le_mul_of_nonneg_left hgap (div_pos (by norm_num) hα).le
  have hcubic : (hydrogenicPhase 11 n : ℝ) ^ 3 ≤
      (bound * (fineStructureApprox : ℝ)) ^ 3 := by
    have h0 : (0 : ℝ) ≤ (hydrogenicPhase 11 n : ℝ) := hx_pos.le
    exact pow_le_pow_left₀ h0 hxle 3
  have hloose : (22 / (fineStructureApprox : ℝ)) *
      ((6 / 5) * (hydrogenicPhase 11 n : ℝ) ^ 3) ≤
      (22 * (6 / 5) * bound ^ 3) * (fineStructureApprox : ℝ) ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hcubic (by norm_num : (0 : ℝ) ≤ 6 / 5))
      (div_pos (by norm_num : (0 : ℝ) < 22) hα).le
    calc (22 / (fineStructureApprox : ℝ)) *
          ((6 / 5) * (hydrogenicPhase 11 n : ℝ) ^ 3)
        ≤ (22 / (fineStructureApprox : ℝ)) *
            ((6 / 5) * (bound * (fineStructureApprox : ℝ)) ^ 3) := hmul
      _ = (22 * (6 / 5) * bound ^ 3) * (fineStructureApprox : ℝ) ^ 2 := by
          field_simp [hα.ne']
  have hsq : (fineStructureApprox : ℝ) ^ 2 < (73 / 10000) ^ 2 :=
    pow_lt_pow_left₀ hα_lt hα.le (by norm_num)
  have hnum : (22 * (6 / 5) * bound ^ 3) * (fineStructureApprox : ℝ) ^ 2 <
      (22 * (6 / 5) * bound ^ 3) * ((73 : ℝ) / 10000) ^ 2 :=
    mul_lt_mul_of_pos_left hsq
      (mul_pos (mul_pos (by norm_num) (by norm_num)) (pow_pos hbound 3))
  linarith

theorem signedCharge_eleven_three :
    |signedCharge 11 3 + 121 / (3 : ℝ) ^ 2| < 1 / 3000 := by
  have hx_eq : (hydrogenicPhase 11 3 : ℝ) =
      (11 / 18) * (fineStructureApprox : ℝ) := by
    unfold hydrogenicPhase
    push_cast
    ring
  refine signedCharge_eleven_close (n := 3) (bound := 11 / 18) (target := 1 / 3000)
      (by norm_num) (hx_eq.le) (by norm_num) (by norm_num) ?_
  norm_num

theorem signedCharge_eleven_four :
    |signedCharge 11 4 + 121 / (4 : ℝ) ^ 2| < 1 / 10000 := by
  have hx_eq : (hydrogenicPhase 11 4 : ℝ) =
      (11 / 32) * (fineStructureApprox : ℝ) := by
    unfold hydrogenicPhase
    push_cast
    ring
  refine signedCharge_eleven_close (n := 4) (bound := 11 / 32) (target := 1 / 10000)
      (by norm_num) (hx_eq.le) (by norm_num) (by norm_num) ?_
  norm_num

theorem naFourThree_signed_shift :
    |signedCharge 11 4 - signedCharge 11 3 - (847 / 144)| <
      (1 / 10000) * (847 / 144) := by
  have h4 := signedCharge_eleven_four
  have h3 := signedCharge_eleven_three
  have hsplit : signedCharge 11 4 - signedCharge 11 3 - (847 / 144) =
      (signedCharge 11 4 + 121 / (4 : ℝ) ^ 2) -
        (signedCharge 11 3 + 121 / (3 : ℝ) ^ 2) := by
    have hnum : (121 : ℝ) / 3 ^ 2 - 121 / 4 ^ 2 = 847 / 144 := by norm_num
    linarith
  obtain ⟨h4lo, h4hi⟩ := abs_lt.mp h4
  obtain ⟨h3lo, h3hi⟩ := abs_lt.mp h3
  rw [hsplit, abs_lt]
  have hpart : (1 : ℝ) / 3000 + 1 / 10000 < (1 / 10000) * (847 / 144) := by norm_num
  constructor <;> linarith

theorem signedCharge_eleven_high {n : ℕ} (hn : 11 ≤ n) :
    |signedCharge 11 n + 121 / (n : ℝ) ^ 2| < 1 / 1000000 := by
  have hxle : (hydrogenicPhase 11 n : ℝ) ≤
      (1 / 22) * (fineStructureApprox : ℝ) := by
    have hcast : (hydrogenicPhase 11 n : ℝ) ≤ (fineStructureApprox : ℝ) / 22 := by
      exact_mod_cast hydrogenicPhase_eleven_le_div22 hn
    linarith [hcast]
  refine signedCharge_eleven_close (n := n) (bound := 1 / 22) (target := 1 / 1000000)
      (by omega) hxle (by norm_num) (by norm_num) ?_
  norm_num

private theorem signedCharge_eleven_step {n m : ℕ} {frac : ℝ}
    (hn : 11 ≤ n) (hm : 11 ≤ m)
    (hfrac : (121 : ℝ) / (n : ℝ) ^ 2 - 121 / (m : ℝ) ^ 2 = frac)
    (hroom : (2 : ℝ) / 1000000 < (1 / 10000) * frac) :
    |signedCharge 11 m - signedCharge 11 n - frac| < (1 / 10000) * frac := by
  have hn' := signedCharge_eleven_high hn
  have hm' := signedCharge_eleven_high hm
  have hsplit : signedCharge 11 m - signedCharge 11 n - frac =
      (signedCharge 11 m + 121 / (m : ℝ) ^ 2) -
        (signedCharge 11 n + 121 / (n : ℝ) ^ 2) := by
    linarith
  obtain ⟨hmlo, hmhi⟩ := abs_lt.mp hm'
  obtain ⟨hnlo, hnhi⟩ := abs_lt.mp hn'
  rw [hsplit, abs_lt]
  constructor <;> linarith

theorem naMatchLyman_signed_shift :
    |signedCharge 11 22 - signedCharge 11 11 - (3 / 4)| <
      (1 / 10000) * (3 / 4) :=
  signedCharge_eleven_step (n := 11) (m := 22) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem naMatchAlpha_signed_shift :
    |signedCharge 11 33 - signedCharge 11 22 - (5 / 36)| <
      (1 / 10000) * (5 / 36) :=
  signedCharge_eleven_step (n := 22) (m := 33) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem naMatchBeta_signed_shift :
    |signedCharge 11 44 - signedCharge 11 22 - (3 / 16)| <
      (1 / 10000) * (3 / 16) :=
  signedCharge_eleven_step (n := 22) (m := 44) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem naMatchGamma_signed_shift :
    |signedCharge 11 55 - signedCharge 11 22 - (21 / 100)| <
      (1 / 10000) * (21 / 100) :=
  signedCharge_eleven_step (n := 22) (m := 55) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

/-! ### Charge three: the one-electron ion

The ground phase \(3\alpha/2\) lies above \(1/100\), so the plateau gap of
width \(6/5\) is too coarse for the step \(2\to 1\). On `(0, 1/90)` the
same departure is at most half a cube, and that is enough.
-/

private theorem one_sub_gammaSEqual_integral {x : ℝ} (_hx : 0 ≤ x) :
    1 - gammaSEqual x = ∫ t in (0 : ℝ)..x, 2 * cosh t * sin t := by
  have hderiv : ∀ t ∈ uIcc (0 : ℝ) x, HasDerivAt gammaSEqual (-2 * cosh t * sin t) t :=
    fun t _ => hasDerivAt_gammaSEqual t
  have hint : IntervalIntegrable (fun t => -2 * cosh t * sin t) volume 0 x := by
    refine Continuous.intervalIntegrable ?_ 0 x
    fun_prop
  have hftc := integral_eq_sub_of_hasDerivAt hderiv hint
  rw [gammaSEqual_zero] at hftc
  have hneg : ∫ t in (0 : ℝ)..x, 2 * cosh t * sin t =
      -∫ t in (0 : ℝ)..x, -2 * cosh t * sin t := by
    simp [intervalIntegral.integral_neg]
  linarith [hneg]

private theorem gammaDepart_cubic {x : ℝ} (hx : 0 ≤ x) (hx90 : x ≤ 1 / 90) :
    x ^ 2 - x ^ 4 / 12 ≤ 1 - gammaSEqual x := by
  rw [one_sub_gammaSEqual_integral hx]
  have hbound : ∀ t ∈ Icc (0 : ℝ) x, 2 * t - t ^ 3 / 3 ≤ 2 * cosh t * sin t := by
    intro t ht
    have ht0 : 0 ≤ t := ht.1
    have hsin_cubic : t - t ^ 3 / 6 ≤ sin t := by
      rcases eq_or_lt_of_le ht0 with rfl | hpos
      · simp
      · exact (sin_gt_sub_cube hpos).le
    have hsin0 : 0 ≤ sin t :=
      sin_nonneg_of_nonneg_of_le_pi ht0 (by linarith [ht.2, hx90, pi_gt_three])
    have hcosh : sin t ≤ cosh t * sin t := by
      simpa [one_mul] using mul_le_mul_of_nonneg_right (one_le_cosh t) hsin0
    have hge : t - t ^ 3 / 6 ≤ cosh t * sin t := le_trans hsin_cubic hcosh
    have htwo : 2 * (t - t ^ 3 / 6) ≤ 2 * (cosh t * sin t) :=
      mul_le_mul_of_nonneg_left hge (by norm_num)
    have hrew : 2 * (t - t ^ 3 / 6) = 2 * t - t ^ 3 / 3 := by ring
    linarith
  have hintf : IntervalIntegrable (fun t => 2 * cosh t * sin t) volume 0 x := by
    refine Continuous.intervalIntegrable ?_ 0 x
    fun_prop
  have hintg : IntervalIntegrable (fun t => 2 * t - t ^ 3 / 3) volume 0 x := by
    refine Continuous.intervalIntegrable ?_ 0 x
    fun_prop
  have hmono := integral_mono_on hx hintg hintf hbound
  have hquad : ∫ t in (0 : ℝ)..x, 2 * t - t ^ 3 / 3 = x ^ 2 - x ^ 4 / 12 := by
    have hder : ∀ t ∈ uIcc (0 : ℝ) x,
        HasDerivAt (fun s => s ^ 2 - s ^ 4 / 12) (2 * t - t ^ 3 / 3) t := by
      intro t _
      have h2 : HasDerivAt (fun s : ℝ => s ^ 2) (2 * t) t := by
        simpa [pow_one] using hasDerivAt_pow 2 t
      have h4 : HasDerivAt (fun s : ℝ => s ^ 4) (4 * t ^ 3) t := by
        simpa [pow_succ, pow_one] using hasDerivAt_pow 4 t
      have hsub := h2.sub (h4.div_const 12)
      convert hsub using 1
      ring
    have hq := integral_eq_sub_of_hasDerivAt hder hintg
    simp at hq
    linarith
  linarith

private theorem circEnergy_half_cubic {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) (1 / 90)) :
    0 < circEnergy x + x ∧ circEnergy x + x < (1 / 2) * x ^ 3 := by
  have hx0 : 0 ≤ x := hx.1.le
  have hxle : x ≤ 1 / 90 := hx.2.le
  have hx50 : x ≤ 1 / 50 := by linarith
  have hx1 : x < resonanceRoot1 := by
    have hπ : (1 / 90 : ℝ) < π / 4 := by linarith [pi_gt_three]
    exact lt_trans hx.2 (lt_trans hπ resonanceRoot1_sharp_bounds.1)
  have hxπ : x ≤ π := by linarith [hx.2, pi_gt_three]
  have hxsq : x ^ 2 < 1 / 8100 := by
    have hlt : |x| < |(1 / 90 : ℝ)| := by
      rw [abs_of_nonneg hx0, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 90)]
      exact hx.2
    have hsq : x ^ 2 < (1 / 90) ^ 2 := (sq_lt_sq).mpr hlt
    have heq : (1 / 90) ^ 2 = (1 : ℝ) / 8100 := by norm_num
    linarith
  set den : ℝ := 1 - (11 / 10) * x ^ 2
  have hden_gt : (80989 : ℝ) / 81000 < den := by
    have hmul : (11 / 10) * x ^ 2 < (11 / 10) * (1 / 8100) :=
      mul_lt_mul_of_pos_left hxsq (by norm_num)
    have hconst : (11 / 10) * (1 / 8100) = (11 : ℝ) / 81000 := by ring
    dsimp [den]
    linarith
  have hden_pos : 0 < den := by
    have hfloor : (0 : ℝ) < (80989 : ℝ) / 81000 := by norm_num
    linarith
  set kap : ℝ := 89100 / 80989
  have hkap : (11 / 10) / den < kap := by
    have hfloor : (0 : ℝ) < (80989 : ℝ) / 81000 := by norm_num
    have hdiv : (11 / 10) / den < (11 / 10) / ((80989 : ℝ) / 81000) :=
      div_lt_div_of_pos_left (by norm_num) hfloor hden_gt
    have heq : (11 / 10) / ((80989 : ℝ) / 81000) = kap := by
      dsimp [kap]
      ring
    linarith
  have hγx : 0 < gammaSEqual x := gammaSEqual_pos_left_of_first_node ⟨hx.1, hx1⟩
  have hanti : AntitoneOn gammaSEqual (Icc (0 : ℝ) π) := by
    simpa [Nat.cast_zero, zero_mul] using (strictAntiOn_gammaSEqual_even 0).antitoneOn
  have hδ : 1 - gammaSEqual x ≤ (11 / 10) * x ^ 2 := gammaDepart_le hx0 hx50
  have hγden : den ≤ gammaSEqual x := by
    dsimp [den]
    linarith
  have hcont : ContinuousOn (fun t => (gammaSEqual t)⁻¹) (Icc 0 x) := by
    refine continuous_gammaSEqual.continuousOn.inv₀ ?_
    intro t ht
    exact (gammaSEqual_pos_of_lt_firstNode ht.1 (lt_of_le_of_lt ht.2 hx1)).ne'
  have hintInv := hcont.intervalIntegrable_of_Icc (μ := volume) hx0
  have hone : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume 0 x :=
    intervalIntegrable_const
  have hintDiff : IntervalIntegrable (fun t => (gammaSEqual t)⁻¹ - 1) volume 0 x :=
    hintInv.sub hone
  have haccum : ∫ t in (0 : ℝ)..x, (gammaSEqual t)⁻¹ = layerAccum x := by
    unfold layerAccum
    rfl
  have hone_int : ∫ t in (0 : ℝ)..x, (1 : ℝ) = x := by simp
  have hsplit : ∫ t in (0 : ℝ)..x, ((gammaSEqual t)⁻¹ - 1) = layerAccum x - x := by
    rw [intervalIntegral.integral_sub hintInv hone, haccum, hone_int]
  have hident : circEnergy x + x =
      x * ((gammaSEqual x)⁻¹ - 1) -
        2 * ∫ t in (0 : ℝ)..x, ((gammaSEqual t)⁻¹ - 1) := by
    unfold circEnergy
    rw [div_eq_mul_inv, hsplit]
    ring
  have hAx : x * ((gammaSEqual x)⁻¹ - 1) ≤ (11 / 10) * x ^ 3 / den := by
    have hrewrite : (gammaSEqual x)⁻¹ - 1 = (1 - gammaSEqual x) / gammaSEqual x := by
      field_simp [hγx.ne']
    rw [hrewrite]
    have hle : (1 - gammaSEqual x) / gammaSEqual x ≤
        ((11 / 10) * x ^ 2) / den := by
      rw [div_le_div_iff₀ hγx hden_pos]
      have hleft := mul_le_mul_of_nonneg_left hδ hden_pos.le
      have hright : (11 / 10) * x ^ 2 * den ≤ (11 / 10) * x ^ 2 * gammaSEqual x :=
        mul_le_mul_of_nonneg_left hγden (by positivity)
      nlinarith
    have hmul := mul_le_mul_of_nonneg_left hle hx0
    calc x * ((1 - gammaSEqual x) / gammaSEqual x)
        ≤ x * (((11 / 10) * x ^ 2) / den) := hmul
      _ = (11 / 10) * x ^ 3 / den := by ring
  have hcubic_int : ∫ t in (0 : ℝ)..x, t ^ 2 - t ^ 4 / 12 = x ^ 3 / 3 - x ^ 5 / 60 := by
    have hintp : IntervalIntegrable (fun t => t ^ 2 - t ^ 4 / 12) volume 0 x := by
      refine Continuous.intervalIntegrable ?_ 0 x
      fun_prop
    have hder : ∀ t ∈ uIcc (0 : ℝ) x,
        HasDerivAt (fun s => s ^ 3 / 3 - s ^ 5 / 60) (t ^ 2 - t ^ 4 / 12) t := by
      intro t _
      have h3 : HasDerivAt (fun s : ℝ => s ^ 3) (3 * t ^ 2) t := by
        simpa [pow_succ, pow_one] using hasDerivAt_pow 3 t
      have h5 : HasDerivAt (fun s : ℝ => s ^ 5) (5 * t ^ 4) t := by
        simpa [pow_succ, pow_one] using hasDerivAt_pow 5 t
      have hsub := (h3.div_const 3).sub (h5.div_const 60)
      convert hsub using 1
      ring
    have hq := integral_eq_sub_of_hasDerivAt hder hintp
    have hzero : (0 : ℝ) ^ 3 / 3 - (0 : ℝ) ^ 5 / 60 = 0 := by norm_num
    rw [hq, hzero, sub_zero]
  have hIge : x ^ 3 / 3 - x ^ 5 / 60 ≤
      ∫ t in (0 : ℝ)..x, ((gammaSEqual t)⁻¹ - 1) := by
    have hpoint : ∀ t ∈ Icc (0 : ℝ) x,
        t ^ 2 - t ^ 4 / 12 ≤ (gammaSEqual t)⁻¹ - 1 := by
      intro t ht
      have ht0 : 0 ≤ t := ht.1
      have ht90 : t ≤ 1 / 90 := le_trans ht.2 hxle
      have hγt : 0 < gammaSEqual t :=
        gammaSEqual_pos_of_lt_firstNode ht0 (lt_of_le_of_lt ht.2 hx1)
      have hcub := gammaDepart_cubic ht0 ht90
      have hge_δ : 1 - gammaSEqual t ≤ (gammaSEqual t)⁻¹ - 1 := by
        have hrewrite : (gammaSEqual t)⁻¹ - 1 - (1 - gammaSEqual t) =
            (1 - gammaSEqual t) ^ 2 / gammaSEqual t := by
          field_simp [hγt.ne']
        have hsq : 0 ≤ (1 - gammaSEqual t) ^ 2 / gammaSEqual t := by positivity
        linarith
      linarith
    have hintp : IntervalIntegrable (fun t => t ^ 2 - t ^ 4 / 12) volume 0 x := by
      refine Continuous.intervalIntegrable ?_ 0 x
      fun_prop
    have hmono := integral_mono_on hx0 hintp hintDiff hpoint
    linarith [hcubic_int, hmono]
  have hIlt : ∫ t in (0 : ℝ)..x, ((gammaSEqual t)⁻¹ - 1) < kap * x ^ 3 / 3 := by
    have hpoint : ∀ t ∈ Icc (0 : ℝ) x,
        (gammaSEqual t)⁻¹ - 1 ≤ ((11 / 10) / den) * t ^ 2 := by
      intro t ht
      have ht0 : 0 ≤ t := ht.1
      have ht50 : t ≤ 1 / 50 := by linarith [ht.2, hxle]
      have hγt : 0 < gammaSEqual t :=
        gammaSEqual_pos_of_lt_firstNode ht0 (lt_of_le_of_lt ht.2 hx1)
      have hδt : 1 - gammaSEqual t ≤ (11 / 10) * t ^ 2 := gammaDepart_le ht0 ht50
      have htsq : t ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ ht0 ht.2 2
      have hden_t : den ≤ 1 - (11 / 10) * t ^ 2 := by
        dsimp [den]
        have hmul := mul_le_mul_of_nonneg_left htsq (by norm_num : (0 : ℝ) ≤ 11 / 10)
        linarith
      have hγden_t : den ≤ gammaSEqual t := by
        have hlow := gammaDepart_le ht0 ht50
        linarith
      have hrewrite : (gammaSEqual t)⁻¹ - 1 = (1 - gammaSEqual t) / gammaSEqual t := by
        field_simp [hγt.ne']
      rw [hrewrite]
      have hle : (1 - gammaSEqual t) / gammaSEqual t ≤ ((11 / 10) * t ^ 2) / den := by
        rw [div_le_div_iff₀ hγt hden_pos]
        have hleft := mul_le_mul_of_nonneg_left hδt hden_pos.le
        have hright : (11 / 10) * t ^ 2 * den ≤ (11 / 10) * t ^ 2 * gammaSEqual t :=
          mul_le_mul_of_nonneg_left hγden_t (mul_nonneg (by norm_num) (sq_nonneg t))
        nlinarith
      have hform : ((11 / 10) * t ^ 2) / den = ((11 / 10) / den) * t ^ 2 := by ring
      linarith
    have hintp : IntervalIntegrable (fun t => ((11 / 10) / den) * t ^ 2) volume 0 x := by
      refine Continuous.intervalIntegrable ?_ 0 x
      fun_prop
    have hmono := integral_mono_on hx0 hintDiff hintp hpoint
    have hintq : IntervalIntegrable (fun t => t ^ 2) volume 0 x := by
      refine Continuous.intervalIntegrable ?_ 0 x
      fun_prop
    have hq : ∫ t in (0 : ℝ)..x, t ^ 2 = x ^ 3 / 3 := by
      have hder : ∀ t ∈ uIcc (0 : ℝ) x,
          HasDerivAt (fun s => s ^ 3 / 3) (t ^ 2) t := by
        intro t _
        have h3 : HasDerivAt (fun s : ℝ => s ^ 3) (3 * t ^ 2) t := by
          simpa [pow_succ, pow_one] using hasDerivAt_pow 3 t
        have hdiv := h3.div_const 3
        convert hdiv using 1
        ring
      have hqi := integral_eq_sub_of_hasDerivAt hder hintq
      have hzero : (0 : ℝ) ^ 3 / 3 = 0 := by norm_num
      rw [hqi, hzero, sub_zero]
    have hscale : ∫ t in (0 : ℝ)..x, ((11 / 10) / den) * t ^ 2 =
        ((11 / 10) / den) * (x ^ 3 / 3) := by
      rw [intervalIntegral.integral_const_mul, hq]
    have hcmp : ((11 / 10) / den) * (x ^ 3 / 3) < kap * x ^ 3 / 3 := by
      have hx3 : 0 < x ^ 3 := pow_pos hx.1 3
      have hmul := mul_lt_mul_of_pos_right hkap (div_pos hx3 (by norm_num : (0 : ℝ) < 3))
      linarith
    linarith
  have hx3 : 0 < x ^ 3 := pow_pos hx.1 3
  have hx5 : x ^ 5 / 30 < x ^ 3 / 243000 := by
    have hdiv : x ^ 2 / 30 < (1 / 8100) / 30 := by
      exact div_lt_div_of_pos_right hxsq (by norm_num)
    have hconst : (1 / 8100) / 30 = (1 : ℝ) / 243000 := by ring
    have hmul := mul_lt_mul_of_pos_left (lt_of_lt_of_eq hdiv hconst) hx3
    have hleft : x ^ 3 * (x ^ 2 / 30) = x ^ 5 / 30 := by ring
    have hright : x ^ 3 * (1 / 243000) = x ^ 3 / 243000 := by ring
    linarith
  have hcoeff : kap - 2 / 3 + 1 / 243000 < 1 / 2 := by
    dsimp [kap]
    norm_num
  have hlow : (0 : ℝ) < 1 - 1 / 97200 - 2 * kap / 3 := by
    dsimp [kap]
    norm_num
  have hx5lo : x ^ 5 / 12 < x ^ 3 / 97200 := by
    have hdiv : x ^ 2 / 12 < (1 / 8100) / 12 :=
      div_lt_div_of_pos_right hxsq (by norm_num)
    have hconst : (1 / 8100) / 12 = (1 : ℝ) / 97200 := by ring
    have hmul := mul_lt_mul_of_pos_left (lt_of_lt_of_eq hdiv hconst) hx3
    have hleft : x ^ 3 * (x ^ 2 / 12) = x ^ 5 / 12 := by ring
    have hright : x ^ 3 * (1 / 97200) = x ^ 3 / 97200 := by ring
    linarith
  constructor
  · have hA : x ^ 3 - x ^ 5 / 12 ≤ x * ((gammaSEqual x)⁻¹ - 1) := by
      have hcub := gammaDepart_cubic hx0 hxle
      have hrewrite : (gammaSEqual x)⁻¹ - 1 = (1 - gammaSEqual x) / gammaSEqual x := by
        field_simp [hγx.ne']
      have hge : 1 - gammaSEqual x ≤ (gammaSEqual x)⁻¹ - 1 := by
        rw [hrewrite]
        have hform : (1 - gammaSEqual x) / gammaSEqual x - (1 - gammaSEqual x) =
            (1 - gammaSEqual x) ^ 2 / gammaSEqual x := by
          field_simp [hγx.ne']
        have hsq : 0 ≤ (1 - gammaSEqual x) ^ 2 / gammaSEqual x := by positivity
        linarith
      have hmul := mul_le_mul_of_nonneg_left (le_trans hcub hge) hx0
      have hleft : x * (x ^ 2 - x ^ 4 / 12) = x ^ 3 - x ^ 5 / 12 := by ring
      linarith
    rw [hident]
    set A : ℝ := x * ((gammaSEqual x)⁻¹ - 1)
    set Iint : ℝ := ∫ t in (0 : ℝ)..x, ((gammaSEqual t)⁻¹ - 1)
    have hI : Iint < kap * x ^ 3 / 3 := by
      simpa [Iint] using hIlt
    have hfloor : x ^ 3 - x ^ 3 / 97200 - 2 * (kap * x ^ 3 / 3) < A - 2 * Iint := by
      have hstep : x ^ 3 - x ^ 5 / 12 - 2 * (kap * x ^ 3 / 3) < A - 2 * Iint := by
        linarith [hA, hI]
      linarith [hstep, hx5lo]
    have hform : x ^ 3 - x ^ 3 / 97200 - 2 * (kap * x ^ 3 / 3) =
        x ^ 3 * (1 - 1 / 97200 - 2 * kap / 3) := by ring
    have hpos : 0 < x ^ 3 * (1 - 1 / 97200 - 2 * kap / 3) := mul_pos hx3 hlow
    linarith
  · rw [hident]
    set A : ℝ := x * ((gammaSEqual x)⁻¹ - 1)
    set Iint : ℝ := ∫ t in (0 : ℝ)..x, ((gammaSEqual t)⁻¹ - 1)
    have hA : A ≤ (11 / 10) * x ^ 3 / den := by
      simpa [A] using hAx
    have hI : x ^ 3 / 3 - x ^ 5 / 60 ≤ Iint := by
      simpa [Iint] using hIge
    have hA' : A < kap * x ^ 3 := by
      have hrew : (11 / 10) * x ^ 3 / den = ((11 / 10) / den) * x ^ 3 := by ring
      rw [hrew] at hA
      exact lt_of_le_of_lt hA (mul_lt_mul_of_pos_right hkap hx3)
    have htail : -(2 * Iint) < -(2 / 3) * x ^ 3 + x ^ 3 / 243000 := by
      have htwo : 2 * (x ^ 3 / 3 - x ^ 5 / 60) = (2 / 3) * x ^ 3 - x ^ 5 / 30 := by ring
      linarith [hI, htwo, hx5]
    have hbundle : kap * x ^ 3 - (2 / 3) * x ^ 3 + x ^ 3 / 243000 < (1 / 2) * x ^ 3 := by
      have hrew : kap * x ^ 3 - (2 / 3) * x ^ 3 + x ^ 3 / 243000 =
          x ^ 3 * (kap - 2 / 3 + 1 / 243000) := by ring
      rw [hrew]
      exact lt_of_lt_of_eq (mul_lt_mul_of_pos_left hcoeff hx3)
        (by ring : x ^ 3 * (1 / 2) = (1 / 2) * x ^ 3)
    calc A - 2 * Iint
        = A + -(2 * Iint) := by ring
      _ < kap * x ^ 3 + (-(2 / 3) * x ^ 3 + x ^ 3 / 243000) := add_lt_add hA' htail
      _ = kap * x ^ 3 - (2 / 3) * x ^ 3 + x ^ 3 / 243000 := by ring
      _ < (1 / 2) * x ^ 3 := hbundle

theorem hydrogenicPhase_three_pos {n : ℕ} (hn : 0 < n) :
    (0 : ℚ) < hydrogenicPhase 3 n := by
  unfold hydrogenicPhase
  exact div_pos (mul_pos (by norm_num) fineStructureApprox_pos)
    (mul_pos (by norm_num) (pow_pos (Nat.cast_pos.mpr hn) 2))

theorem hydrogenicPhase_three_le_ground {n : ℕ} (hn : 0 < n) :
    hydrogenicPhase 3 n ≤ 3 * fineStructureApprox / 2 := by
  unfold hydrogenicPhase
  have hn1 : (1 : ℚ) ≤ (n : ℚ) ^ 2 := by
    have hn' : (1 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn
    have := pow_le_pow_left₀ (by norm_num : (0 : ℚ) ≤ 1) hn' 2
    simpa using this
  have hnum : (0 : ℚ) ≤ 3 * fineStructureApprox :=
    mul_nonneg (by norm_num) fineStructureApprox_pos.le
  exact div_le_div_of_nonneg_left hnum (by norm_num) (by nlinarith [hn1])

theorem hydrogenicPhase_three_ground :
    hydrogenicPhase 3 1 = 3 * fineStructureApprox / 2 := by
  unfold hydrogenicPhase
  norm_num

theorem hydrogenicPhase_three_lt_ninety {n : ℕ} (hn : 0 < n) :
    (hydrogenicPhase 3 n : ℝ) < 1 / 90 := by
  have hle := hydrogenicPhase_three_le_ground hn
  have hα : (fineStructureApprox : ℝ) < 73 / 10000 := by
    unfold fineStructureApprox fineStructureMantissa fineStructureScale
    norm_num
  have hground : (3 : ℝ) * (fineStructureApprox : ℝ) / 2 < 1 / 90 := by
    have hmul : (3 : ℝ) * (fineStructureApprox : ℝ) < (3 : ℝ) * (73 / 10000) :=
      mul_lt_mul_of_pos_left hα (by norm_num)
    have hdiv : (3 : ℝ) * (fineStructureApprox : ℝ) / 2 <
        (3 : ℝ) * (73 / 10000) / 2 :=
      div_lt_div_of_pos_right hmul (by norm_num)
    have hconst : (3 : ℝ) * (73 / 10000) / 2 < 1 / 90 := by norm_num
    linarith
  exact lt_of_le_of_lt (by exact_mod_cast hle) hground

theorem hydrogenicPhase_three_mem_outer {n : ℕ} (hn : 0 < n) :
    (hydrogenicPhase 3 n : ℝ) ∈ Ioo (0 : ℝ) resonanceRoot1 := by
  refine ⟨by exact_mod_cast hydrogenicPhase_three_pos hn, ?_⟩
  have h90 := hydrogenicPhase_three_lt_ninety hn
  have hnode : (1 / 90 : ℝ) < resonanceRoot1 := by
    have hπ : (1 / 90 : ℝ) < π / 4 := by linarith [pi_gt_three]
    exact lt_trans hπ resonanceRoot1_sharp_bounds.1
  exact lt_trans h90 hnode

theorem hydrogenicThree_restoring {n : ℕ} (hn : 0 < n) :
    0 < circStable (hydrogenicPhase 3 n) ∧
      (hydrogenicPhase 3 n : ℝ) * deriv pairAttraction (hydrogenicPhase 3 n) /
          pairAttraction (hydrogenicPhase 3 n) < 3 := by
  obtain ⟨y, hy, _⟩ := exists_unique_circStable
  have hx := hydrogenicPhase_three_mem_outer hn
  have hlt : (hydrogenicPhase 3 n : ℝ) < y := by
    have h90 := hydrogenicPhase_three_lt_ninety hn
    have hhalf : (1 / 90 : ℝ) < 1 / 2 := by norm_num
    linarith [hy.1.1, hhalf]
  have hsign := circStable_outer_sign hx hy.1 hy.2
  have hpos : 0 < circStable (hydrogenicPhase 3 n) := hsign.1.mpr hlt
  exact ⟨hpos, (pairAttraction_logDeriv_lt_three_outer_iff hx).mpr hpos⟩

theorem hydrogenicPhase_three_le_sixth {n : ℕ} (hn : 3 ≤ n) :
    hydrogenicPhase 3 n ≤ fineStructureApprox / 6 := by
  unfold hydrogenicPhase
  have hn3 : (3 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn
  have hn2 : (9 : ℚ) ≤ (n : ℚ) ^ 2 := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℚ) ≤ 3) hn3 2
    simpa [show (3 : ℚ) ^ 2 = 9 by norm_num] using this
  have hnum : (0 : ℚ) ≤ 3 * fineStructureApprox :=
    mul_nonneg (by norm_num) fineStructureApprox_pos.le
  calc (3 : ℚ) * fineStructureApprox / (2 * (n : ℚ) ^ 2)
      ≤ 3 * fineStructureApprox / (2 * 9) :=
        div_le_div_of_nonneg_left hnum (by norm_num) (by nlinarith)
    _ = fineStructureApprox / 6 := by ring

theorem liLyman_book :
    (3 : ℝ) ^ 2 * bohrEnergyDiff 1 2 =
      (27 / 4) * (hydrogenIonisationApprox : ℝ) := by
  rw [bohrEnergyDiff_lymanAlpha]
  norm_num
  ring

theorem liFourThree_book :
    (3 : ℝ) ^ 2 * bohrEnergyDiff 3 4 =
      (7 / 16) * (hydrogenIonisationApprox : ℝ) := by
  rw [bohrEnergyDiff_paschenAlpha]
  norm_num
  ring

theorem signedCharge_three_ground :
    |signedCharge 3 1 + 9| < 54 / 100000 := by
  have hx_pos : (0 : ℝ) < (hydrogenicPhase 3 1 : ℝ) := by
    exact_mod_cast hydrogenicPhase_three_pos (by norm_num : 0 < (1 : ℕ))
  have hx_eq : (hydrogenicPhase 3 1 : ℝ) = 3 * (fineStructureApprox : ℝ) / 2 := by
    exact_mod_cast hydrogenicPhase_three_ground
  have hx_lt : (hydrogenicPhase 3 1 : ℝ) < 1 / 90 :=
    hydrogenicPhase_three_lt_ninety (by norm_num)
  have hgap := circEnergy_half_cubic ⟨hx_pos, hx_lt⟩
  have hα : (0 : ℝ) < (fineStructureApprox : ℝ) := by exact_mod_cast fineStructureApprox_pos
  have hident : signedCharge 3 1 + 9 =
      (6 / (fineStructureApprox : ℝ)) *
        (circEnergy (hydrogenicPhase 3 1) + (hydrogenicPhase 3 1 : ℝ)) := by
    unfold signedCharge
    rw [hx_eq]
    field_simp [hα.ne']
    ring
  rw [hident]
  have hnonneg : 0 ≤ circEnergy (hydrogenicPhase 3 1) + (hydrogenicPhase 3 1 : ℝ) :=
    hgap.1.le
  have habs : |(6 / (fineStructureApprox : ℝ)) *
      (circEnergy (hydrogenicPhase 3 1) + (hydrogenicPhase 3 1 : ℝ))| =
      (6 / (fineStructureApprox : ℝ)) *
        |circEnergy (hydrogenicPhase 3 1) + (hydrogenicPhase 3 1 : ℝ)| := by
    rw [abs_mul, abs_of_pos (div_pos (by norm_num) hα)]
  rw [habs, abs_of_nonneg hnonneg]
  have hscale : (6 / (fineStructureApprox : ℝ)) *
      (circEnergy (hydrogenicPhase 3 1) + (hydrogenicPhase 3 1 : ℝ)) <
      (6 / (fineStructureApprox : ℝ)) * ((1 / 2) * (hydrogenicPhase 3 1 : ℝ) ^ 3) :=
    mul_lt_mul_of_pos_left hgap.2 (div_pos (by norm_num) hα)
  have hloose : (6 / (fineStructureApprox : ℝ)) *
      ((1 / 2) * (hydrogenicPhase 3 1 : ℝ) ^ 3) =
      (81 / 8) * (fineStructureApprox : ℝ) ^ 2 := by
    rw [hx_eq]
    field_simp [hα.ne']
    ring
  have hα_lt : (fineStructureApprox : ℝ) < 73 / 10000 := by
    unfold fineStructureApprox fineStructureMantissa fineStructureScale
    norm_num
  have hsq : (fineStructureApprox : ℝ) ^ 2 < (73 / 10000) ^ 2 :=
    pow_lt_pow_left₀ hα_lt hα.le (by norm_num)
  have hnum : (81 / 8) * (fineStructureApprox : ℝ) ^ 2 <
      (81 / 8) * ((73 : ℝ) / 10000) ^ 2 :=
    mul_lt_mul_of_pos_left hsq (by norm_num)
  have hconst : (81 / 8) * ((73 : ℝ) / 10000) ^ 2 < 54 / 100000 := by norm_num
  linarith

theorem signedCharge_three_two :
    |signedCharge 3 2 + 9 / (2 : ℝ) ^ 2| < 1 / 40000 := by
  have hx_pos : (0 : ℝ) < (hydrogenicPhase 3 2 : ℝ) := by
    exact_mod_cast hydrogenicPhase_three_pos (by norm_num)
  have hx_eq : (hydrogenicPhase 3 2 : ℝ) = (3 / 8) * (fineStructureApprox : ℝ) := by
    unfold hydrogenicPhase
    push_cast
    ring
  have hx_lt : (hydrogenicPhase 3 2 : ℝ) < 1 / 100 := by
    have hα := fineStructureApprox_lt_hundredth
    linarith [hx_eq]
  have hgap := circEnergy_coulomb_gap ⟨hx_pos, hx_lt⟩
  have hα : (0 : ℝ) < (fineStructureApprox : ℝ) := by exact_mod_cast fineStructureApprox_pos
  have hident : signedCharge 3 2 + 9 / (2 : ℝ) ^ 2 =
      (6 / (fineStructureApprox : ℝ)) *
        (circEnergy (hydrogenicPhase 3 2) + (hydrogenicPhase 3 2 : ℝ)) := by
    unfold signedCharge
    rw [hx_eq]
    field_simp [hα.ne']
    ring
  rw [hident]
  have habs : |(6 / (fineStructureApprox : ℝ)) *
      (circEnergy (hydrogenicPhase 3 2) + (hydrogenicPhase 3 2 : ℝ))| =
      (6 / (fineStructureApprox : ℝ)) *
        |circEnergy (hydrogenicPhase 3 2) + (hydrogenicPhase 3 2 : ℝ)| := by
    rw [abs_mul, abs_of_pos (div_pos (by norm_num) hα)]
  rw [habs]
  have hscale : (6 / (fineStructureApprox : ℝ)) *
      |circEnergy (hydrogenicPhase 3 2) + (hydrogenicPhase 3 2 : ℝ)| ≤
      (6 / (fineStructureApprox : ℝ)) * ((6 / 5) * (hydrogenicPhase 3 2 : ℝ) ^ 3) :=
    mul_le_mul_of_nonneg_left hgap (div_pos (by norm_num) hα).le
  have hloose : (6 / (fineStructureApprox : ℝ)) *
      ((6 / 5) * (hydrogenicPhase 3 2 : ℝ) ^ 3) =
      (243 / 640) * (fineStructureApprox : ℝ) ^ 2 := by
    rw [hx_eq]
    field_simp [hα.ne']
    ring
  have hα_lt : (fineStructureApprox : ℝ) < 73 / 10000 := by
    unfold fineStructureApprox fineStructureMantissa fineStructureScale
    norm_num
  have hsq : (fineStructureApprox : ℝ) ^ 2 < (73 / 10000) ^ 2 :=
    pow_lt_pow_left₀ hα_lt hα.le (by norm_num)
  have hnum : (243 / 640) * (fineStructureApprox : ℝ) ^ 2 <
      (243 / 640) * ((73 : ℝ) / 10000) ^ 2 :=
    mul_lt_mul_of_pos_left hsq (by norm_num)
  have hconst : (243 / 640) * ((73 : ℝ) / 10000) ^ 2 < 1 / 40000 := by norm_num
  linarith

theorem liLyman_signed_shift :
    |signedCharge 3 2 - signedCharge 3 1 - (27 / 4)| < (1 / 10000) * (27 / 4) := by
  have h2 := signedCharge_three_two
  have h1 := signedCharge_three_ground
  have hsplit : signedCharge 3 2 - signedCharge 3 1 - (27 / 4) =
      (signedCharge 3 2 + 9 / (2 : ℝ) ^ 2) - (signedCharge 3 1 + 9) := by
    have hnum : (9 : ℝ) - 9 / 2 ^ 2 = 27 / 4 := by norm_num
    linarith
  obtain ⟨h2lo, h2hi⟩ := abs_lt.mp h2
  obtain ⟨h1lo, h1hi⟩ := abs_lt.mp h1
  rw [hsplit, abs_lt]
  have hpart : (1 : ℝ) / 40000 + 54 / 100000 < (1 / 10000) * (27 / 4) := by norm_num
  constructor <;> linarith

private theorem signedCharge_three_close {n : ℕ} (hn : 3 ≤ n) :
    |signedCharge 3 n + 9 / (n : ℝ) ^ 2| < 1 / 200000 := by
  have hn0 : 0 < n := by omega
  have hx_pos : (0 : ℝ) < (hydrogenicPhase 3 n : ℝ) := by
    exact_mod_cast hydrogenicPhase_three_pos hn0
  have hx_le : (hydrogenicPhase 3 n : ℝ) ≤ (fineStructureApprox : ℝ) / 6 := by
    exact_mod_cast hydrogenicPhase_three_le_sixth hn
  have hx_lt : (hydrogenicPhase 3 n : ℝ) < 1 / 100 := by
    have hα := fineStructureApprox_lt_hundredth
    linarith
  have hgap := circEnergy_coulomb_gap ⟨hx_pos, hx_lt⟩
  have hα : (0 : ℝ) < (fineStructureApprox : ℝ) := by exact_mod_cast fineStructureApprox_pos
  have hxphase : (hydrogenicPhase 3 n : ℝ) =
      (3 : ℝ) * (fineStructureApprox : ℝ) / (2 * (n : ℝ) ^ 2) := by
    unfold hydrogenicPhase
    push_cast
    ring
  have hident : signedCharge 3 n + 9 / (n : ℝ) ^ 2 =
      (6 / (fineStructureApprox : ℝ)) *
        (circEnergy (hydrogenicPhase 3 n) + (hydrogenicPhase 3 n : ℝ)) := by
    unfold signedCharge
    rw [hxphase]
    field_simp [hα.ne', (Nat.cast_pos.mpr hn0 : (0 : ℝ) < (n : ℝ)).ne']
    ring
  rw [hident]
  have habs : |(6 / (fineStructureApprox : ℝ)) *
      (circEnergy (hydrogenicPhase 3 n) + (hydrogenicPhase 3 n : ℝ))| =
      (6 / (fineStructureApprox : ℝ)) *
        |circEnergy (hydrogenicPhase 3 n) + (hydrogenicPhase 3 n : ℝ)| := by
    rw [abs_mul, abs_of_pos (div_pos (by norm_num) hα)]
  rw [habs]
  have hscale : (6 / (fineStructureApprox : ℝ)) *
      |circEnergy (hydrogenicPhase 3 n) + (hydrogenicPhase 3 n : ℝ)| ≤
      (6 / (fineStructureApprox : ℝ)) * ((6 / 5) * (hydrogenicPhase 3 n : ℝ) ^ 3) :=
    mul_le_mul_of_nonneg_left hgap (div_pos (by norm_num) hα).le
  have hcubic : (hydrogenicPhase 3 n : ℝ) ^ 3 ≤
      ((fineStructureApprox : ℝ) / 6) ^ 3 := by
    exact pow_le_pow_left₀ hx_pos.le hx_le 3
  have hloose : (6 / (fineStructureApprox : ℝ)) *
      ((6 / 5) * (hydrogenicPhase 3 n : ℝ) ^ 3) ≤
      (1 / 30) * (fineStructureApprox : ℝ) ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hcubic (by norm_num : (0 : ℝ) ≤ 6 / 5))
      (div_pos (by norm_num : (0 : ℝ) < 6) hα).le
    calc (6 / (fineStructureApprox : ℝ)) *
          ((6 / 5) * (hydrogenicPhase 3 n : ℝ) ^ 3)
        ≤ (6 / (fineStructureApprox : ℝ)) *
            ((6 / 5) * ((fineStructureApprox : ℝ) / 6) ^ 3) := hmul
      _ = (1 / 30) * (fineStructureApprox : ℝ) ^ 2 := by
          field_simp [hα.ne']
          ring
  have hα_lt : (fineStructureApprox : ℝ) < 73 / 10000 := by
    unfold fineStructureApprox fineStructureMantissa fineStructureScale
    norm_num
  have hsq : (fineStructureApprox : ℝ) ^ 2 < (73 / 10000) ^ 2 :=
    pow_lt_pow_left₀ hα_lt hα.le (by norm_num)
  have hnum : (1 / 30) * (fineStructureApprox : ℝ) ^ 2 <
      (1 / 30) * ((73 : ℝ) / 10000) ^ 2 :=
    mul_lt_mul_of_pos_left hsq (by norm_num)
  have hconst : (1 / 30) * ((73 : ℝ) / 10000) ^ 2 < 1 / 200000 := by norm_num
  linarith

theorem liFourThree_signed_shift :
    |signedCharge 3 4 - signedCharge 3 3 - (7 / 16)| < (1 / 10000) * (7 / 16) := by
  have h4 := signedCharge_three_close (by norm_num : 3 ≤ (4 : ℕ))
  have h3 := signedCharge_three_close (by norm_num : 3 ≤ (3 : ℕ))
  have hsplit : signedCharge 3 4 - signedCharge 3 3 - (7 / 16) =
      (signedCharge 3 4 + 9 / (4 : ℝ) ^ 2) -
        (signedCharge 3 3 + 9 / (3 : ℝ) ^ 2) := by
    have hnum : (9 : ℝ) / 3 ^ 2 - 9 / 4 ^ 2 = 7 / 16 := by norm_num
    linarith
  obtain ⟨h4lo, h4hi⟩ := abs_lt.mp h4
  obtain ⟨h3lo, h3hi⟩ := abs_lt.mp h3
  rw [hsplit, abs_lt]
  have hpart : (2 : ℝ) / 200000 < (1 / 10000) * (7 / 16) := by norm_num
  constructor <;> linarith

private theorem signedCharge_three_step {n m : ℕ} {frac : ℝ}
    (hn : 3 ≤ n) (hm : 3 ≤ m)
    (hfrac : (9 : ℝ) / (n : ℝ) ^ 2 - 9 / (m : ℝ) ^ 2 = frac)
    (hroom : (2 : ℝ) / 200000 < (1 / 10000) * frac) :
    |signedCharge 3 m - signedCharge 3 n - frac| < (1 / 10000) * frac := by
  have hn' := signedCharge_three_close hn
  have hm' := signedCharge_three_close hm
  have hsplit : signedCharge 3 m - signedCharge 3 n - frac =
      (signedCharge 3 m + 9 / (m : ℝ) ^ 2) -
        (signedCharge 3 n + 9 / (n : ℝ) ^ 2) := by
    linarith
  obtain ⟨hmlo, hmhi⟩ := abs_lt.mp hm'
  obtain ⟨hnlo, hnhi⟩ := abs_lt.mp hn'
  rw [hsplit, abs_lt]
  constructor <;> linarith

theorem liMatchLyman_signed_shift :
    |signedCharge 3 6 - signedCharge 3 3 - (3 / 4)| < (1 / 10000) * (3 / 4) :=
  signedCharge_three_step (n := 3) (m := 6) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem liMatchAlpha_signed_shift :
    |signedCharge 3 9 - signedCharge 3 6 - (5 / 36)| < (1 / 10000) * (5 / 36) :=
  signedCharge_three_step (n := 6) (m := 9) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem liMatchBeta_signed_shift :
    |signedCharge 3 12 - signedCharge 3 6 - (3 / 16)| < (1 / 10000) * (3 / 16) :=
  signedCharge_three_step (n := 6) (m := 12) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem liMatchGamma_signed_shift :
    |signedCharge 3 15 - signedCharge 3 6 - (21 / 100)| <
      (1 / 10000) * (21 / 100) :=
  signedCharge_three_step (n := 6) (m := 15) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

/-! ### Charge one after the first shell

The first principal shell holds two electrons. Charge three minus those
two leaves one, and the remaining electron sits on the second shell.
The monopole and the dipole of one shell index share one phase, so the
red doublet — that step — has circular energy zero. There is no
fine-structure splitting.
-/

theorem lithiumCore_electrons :
    2 * 1 ^ 2 = 2 ∧ 3 - (2 * 1 ^ 2) = 1 := by
  constructor <;> norm_num

theorem lithiumValence_restoring :
    0 < circStable (hydrogenicPhase 1 2) ∧
      (hydrogenicPhase 1 2 : ℝ) * deriv pairAttraction (hydrogenicPhase 1 2) /
          pairAttraction (hydrogenicPhase 1 2) < 3 := by
  rw [hydrogenicPhase_one (by norm_num : 0 < (2 : ℕ))]
  exact bohrShell_restoring (by norm_num)

theorem lithiumValence_book :
    ((3 - (2 * 1 ^ 2) : ℕ) : ℝ) ^ 2 * bohrEnergyDiff 2 2 = 0 := by
  have hcore : (3 - (2 * 1 ^ 2) : ℕ) = 1 := lithiumCore_electrons.2
  rw [hcore]
  unfold bohrEnergyDiff
  norm_num

theorem lithiumValence_circ :
    signedCharge (3 - (2 * 1 ^ 2)) 2 - signedCharge (3 - (2 * 1 ^ 2)) 2 = 0 := by
  ring

end Gravity

end DstDiophantine
