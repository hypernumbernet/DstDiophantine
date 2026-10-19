import DstDiophantine.Gravity.NuclearLength
import DstDiophantine.Gravity.TorsionalLayer
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Alpha–gold scattering in the outer region of the nuclear length

## Paper boundary (do **not** claim)

The Coulomb constant `k e² = 1.439964` MeV fm, the alpha energy `7.69` MeV,
the charges `2` and `79`, and the mass numbers `4` and `197` are external
inputs. The length is chosen by the particles: charges of electrons or protons
take the electromagnetic length, and mass-bearing particles, mainly nucleons,
take the gravitational length. Between two nuclei the length is `λ_π`, and the
Coulomb term is read with the equal-scale factor at that length: the protons
of a nucleus sit in the sign cell of the chaotic proton force and are not
isolated charges. The head-on distance is the laboratory-frame Coulomb value
`2 Z k e² / E`. No cross section or half-life is computed here. The coherent
sum `A₁ A₂ κ` of the nuclear prefactor over nucleon pairs is an option, not a
statement of the papers.

## What is proved

* The head-on distance lies in `(29, 30)` fm, outside the first node of `λ_π`.
* For `0 ≤ x ≤ 1/40`, `0 ≤ 1/γ_s(x) - 1 ≤ 13/15987`.
* At every separation `r ≥ 29` fm the phase `λ_π/(2r)` lies in `[0, 1/40]`,
  so the signed Coulomb factor differs from one by at most `13/15987`.
* If the nuclear prefactor adds coherently over the `4 · 197` nucleon pairs
  and its far-field share is at most `1/200` of the charge term `2 · 79 k e²`,
  then `κ < k e²/997`.
-/

namespace DstDiophantine

namespace Gravity

open Real Set

/-- `γ_s(x) ≥ 1 - x² cosh x` for `x ≥ 0`. -/
private lemma rf_gamma_ge {x : ℝ} (hx : 0 ≤ x) :
    1 - x ^ 2 * cosh x ≤ gammaSEqual x := by
  let f : ℝ → ℝ := fun y => gammaSEqual y - 1 + y ^ 2 * cosh y
  have hderiv : ∀ y ∈ Ioo 0 (x + 1),
      HasDerivAt f (2 * cosh y * (y - sin y) + y ^ 2 * sinh y) y := by
    intro y _
    have hg := hasDerivAt_gammaSEqual y
    have hpow : HasDerivAt (fun z : ℝ => z ^ 2) (2 * y) y := by
      simpa using (hasDerivAt_pow 2 y)
    have hprod := hpow.mul (Real.hasDerivAt_cosh y)
    have hf := (hg.sub (hasDerivAt_const y (1 : ℝ))).add hprod
    refine hf.congr_deriv ?_
    ring
  have hcont : ContinuousOn f (Icc 0 (x + 1)) := by
    unfold f
    exact (continuous_gammaSEqual.continuousOn.sub continuousOn_const).add
      ((continuous_id.pow 2).continuousOn.mul continuous_cosh.continuousOn)
  have hdiff : DifferentiableOn ℝ f (interior (Icc 0 (x + 1))) := by
    intro y hy
    rw [interior_Icc] at hy
    exact (hderiv y hy).differentiableAt.differentiableWithinAt
  have hnonneg : ∀ y ∈ interior (Icc 0 (x + 1)), 0 ≤ deriv f y := by
    intro y hy
    rw [interior_Icc] at hy
    rw [(hderiv y hy).deriv]
    have hsin : sin y ≤ y := sin_le hy.1.le
    have hgap : 0 ≤ y - sin y := sub_nonneg.mpr hsin
    have hc : 0 ≤ cosh y := (cosh_pos y).le
    have hs : 0 ≤ sinh y := sinh_nonneg_iff.mpr hy.1.le
    have h1 : 0 ≤ 2 * cosh y * (y - sin y) := by positivity
    have h2 : 0 ≤ y ^ 2 * sinh y := by positivity
    linarith
  have hmono := monotoneOn_of_deriv_nonneg (convex_Icc 0 (x + 1)) hcont hdiff hnonneg
  have hle := hmono ⟨le_rfl, by linarith⟩ ⟨hx, by linarith⟩ hx
  have h0 : f 0 = 0 := by
    unfold f
    rw [gammaSEqual_zero, cosh_zero]
    norm_num
  linarith

/-- Up to phase `1`, `γ_s(x) ≤ 2 cos x - 1`. -/
private lemma rf_gamma_le {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    gammaSEqual x ≤ 2 * cos x - 1 := by
  let f : ℝ → ℝ := fun y => 2 * cos y - 1 - gammaSEqual y
  have hderiv : ∀ y ∈ Ioo 0 1, HasDerivAt f (2 * sin y * (cosh y - 1)) y := by
    intro y _
    have hg := hasDerivAt_gammaSEqual y
    have hc := (Real.hasDerivAt_cos y).const_mul 2
    have hf := (hc.sub (hasDerivAt_const y (1 : ℝ))).sub hg
    refine hf.congr_deriv ?_
    ring
  have hcont : ContinuousOn f (Icc 0 1) := by
    unfold f
    exact ((continuous_cos.continuousOn.const_mul 2).sub continuousOn_const).sub
      continuous_gammaSEqual.continuousOn
  have hdiff : DifferentiableOn ℝ f (interior (Icc (0 : ℝ) 1)) := by
    intro y hy
    rw [interior_Icc] at hy
    exact (hderiv y hy).differentiableAt.differentiableWithinAt
  have hnonneg : ∀ y ∈ interior (Icc (0 : ℝ) 1), 0 ≤ deriv f y := by
    intro y hy
    rw [interior_Icc] at hy
    rw [(hderiv y hy).deriv]
    have hyπ : y < π := lt_trans hy.2 (by linarith [pi_gt_three])
    have hs : 0 ≤ sin y := (sin_pos_of_pos_of_lt_pi hy.1 hyπ).le
    have hc : 0 ≤ cosh y - 1 := sub_nonneg.mpr (one_le_cosh y)
    positivity
  have hmono := monotoneOn_of_deriv_nonneg (convex_Icc 0 1) hcont hdiff hnonneg
  have hle := hmono ⟨le_rfl, by norm_num⟩ ⟨hx0, hx1⟩ hx0
  have h0 : f 0 = 0 := by
    unfold f
    rw [cos_zero, gammaSEqual_zero]
    norm_num
  linarith

private lemma rf_exp_sixth : exp (1 / 6 : ℝ) ≤ 6 / 5 := by
  have h := exp_bound' (x := 1 / 6) (by norm_num) (by norm_num) (n := 4) (by decide)
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h
  exact h.trans (by norm_num)

private lemma rf_exp_quarter : exp (1 / 4 : ℝ) ≤ 13 / 10 := by
  have h := exp_bound' (x := 1 / 4) (by norm_num) (by norm_num) (n := 5) (by decide)
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h
  exact h.trans (by norm_num)

/-- `k e²` in MeV fm (external stand-in). -/
def coulombMeVFm : ℚ := 1439964 / 1000000

/-- Alpha kinetic energy of the Geiger–Marsden source, `7.69` MeV (external). -/
def alphaGoldEnergyMeV : ℚ := 769 / 100

/-- Gold nuclear charge (external). -/
def goldCharge : ℚ := 79

/-- Laboratory-frame Coulomb head-on distance `2 Z k e² / E`, in fm. -/
def alphaGoldClosestFm : ℚ := 2 * goldCharge * coulombMeVFm / alphaGoldEnergyMeV

theorem alphaGoldClosest_window :
    (29 : ℚ) < alphaGoldClosestFm ∧ alphaGoldClosestFm < 30 := by
  unfold alphaGoldClosestFm goldCharge coulombMeVFm alphaGoldEnergyMeV
  constructor <;> norm_num

private theorem rf_pion_lt : (pionComptonFm : ℝ) < 71 / 50 := by
  rw [show (71 / 50 : ℝ) = ((71 / 50 : ℚ) : ℝ) by norm_num]
  exact_mod_cast pionComptonFm_tight_bounds.2

private theorem rf_pion_pos : (0 : ℝ) < (pionComptonFm : ℝ) := by
  have h : (7 / 5 : ℝ) < (pionComptonFm : ℝ) := by
    rw [show (7 / 5 : ℝ) = ((7 / 5 : ℚ) : ℝ) by norm_num]
    exact_mod_cast pionComptonFm_tight_bounds.1
  linarith

/-- The head-on distance lies outside the first node of `λ_π`. -/
theorem alphaGold_outside_pion_node :
    (pionComptonFm : ℝ) / (2 * resonanceRoot1) < (alphaGoldClosestFm : ℝ) := by
  have hx := firstNode_num_window
  have hxpos : (0 : ℝ) < resonanceRoot1 := lt_trans (by norm_num) hx.1
  have hd : (29 : ℝ) < (alphaGoldClosestFm : ℝ) := by
    exact_mod_cast alphaGoldClosest_window.1
  have hp := rf_pion_lt
  rw [div_lt_iff₀ (by positivity)]
  nlinarith

/-- For `0 ≤ x ≤ 1/40` the signed factor departs from one by at most `13/15987`. -/
theorem invGamma_dev_le {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 40) :
    0 ≤ 1 / gammaSEqual x - 1 ∧ 1 / gammaSEqual x - 1 ≤ 13 / 15987 := by
  have hup : gammaSEqual x ≤ 1 := by
    have h := rf_gamma_le hx0 (by linarith)
    have hc := cos_le_one x
    linarith
  have hcosh : cosh x ≤ 13 / 10 := by
    have h1 := cosh_le_exp_of_nonneg hx0
    have h2 : exp x ≤ exp (1 / 4 : ℝ) := exp_le_exp.mpr (by linarith)
    linarith [rf_exp_quarter]
  have hsq : x ^ 2 ≤ (1 / 40 : ℝ) ^ 2 := pow_le_pow_left₀ hx0 hx1 2
  have hprod : x ^ 2 * cosh x ≤ (1 / 40 : ℝ) ^ 2 * (13 / 10) :=
    mul_le_mul hsq hcosh (cosh_pos x).le (by norm_num)
  have hlow : (15987 / 16000 : ℝ) ≤ gammaSEqual x := by
    have h := rf_gamma_ge hx0
    norm_num at hprod
    linarith
  have hpos : 0 < gammaSEqual x := lt_of_lt_of_le (by norm_num) hlow
  have hne : gammaSEqual x ≠ 0 := hpos.ne'
  rw [div_sub_one hne]
  constructor
  · exact div_nonneg (by linarith) hpos.le
  · rw [div_le_iff₀ hpos]
    linarith

/-- At every separation `r ≥ 29` fm the phase of `λ_π` lies in `[0, 1/40]`. -/
theorem pion_phase_le_of_ge {r : ℝ} (hr : 29 ≤ r) :
    0 ≤ (pionComptonFm : ℝ) / (2 * r) ∧ (pionComptonFm : ℝ) / (2 * r) ≤ 1 / 40 := by
  have hp := rf_pion_lt
  have hp0 := rf_pion_pos
  have hr0 : (0 : ℝ) < 2 * r := by linarith
  refine ⟨div_nonneg hp0.le hr0.le, ?_⟩
  rw [div_le_iff₀ hr0]
  linarith

/-- At `r ≥ 29` fm the signed Coulomb factor at `λ_π` departs from one by at most
`13/15987`. -/
theorem nuclear_dev_of_ge {r : ℝ} (hr : 29 ≤ r) :
    0 ≤ 1 / gammaSEqual ((pionComptonFm : ℝ) / (2 * r)) - 1 ∧
      1 / gammaSEqual ((pionComptonFm : ℝ) / (2 * r)) - 1 ≤ 13 / 15987 :=
  invGamma_dev_le (pion_phase_le_of_ge hr).1 (pion_phase_le_of_ge hr).2

/-- At the alpha–gold head-on distance the departure is at most `13/15987`. -/
theorem alphaGold_dev :
    0 ≤ 1 / gammaSEqual ((pionComptonFm : ℝ) / (2 * (alphaGoldClosestFm : ℝ))) - 1 ∧
      1 / gammaSEqual ((pionComptonFm : ℝ) / (2 * (alphaGoldClosestFm : ℝ))) - 1 ≤
        13 / 15987 := by
  have hd : (29 : ℝ) ≤ (alphaGoldClosestFm : ℝ) := by
    have h : (29 : ℚ) ≤ alphaGoldClosestFm := alphaGoldClosest_window.1.le
    exact_mod_cast h
  exact nuclear_dev_of_ge hd

/-! ### Mass numbers -/

/-- Nucleon pairs over charge pairs for alpha on gold: `4·197 / (2·79)`. -/
theorem alphaGold_pair_ratio :
    (498 / 100 : ℚ) < (4 * 197) / (2 * 79) ∧ (4 * 197 : ℚ) / (2 * 79) < 499 / 100 := by
  constructor <;> norm_num

/-- A coherent nuclear prefactor whose far-field share is at most `1/200` of the
charge term forces `κ < k e²/997`. -/
theorem coherent_kappa_cap {κ k : ℝ} (hk : 0 < k)
    (h : 4 * 197 * κ ≤ (1 / 200) * (2 * 79 * k)) : κ < k / 997 := by
  linarith

/-! ### Chadwick's three charges -/

/-- The alpha coefficient `2A/Z` for copper, silver, and platinum (external
mass numbers `63.55`, `107.87`, `195.08`). -/
theorem chadwick_coeff_windows :
    ((438 : ℚ) / 100 < 2 * (6355 / 100) / 29 ∧ 2 * (6355 / 100 : ℚ) / 29 < 439 / 100) ∧
    ((459 : ℚ) / 100 < 2 * (10787 / 100) / 47 ∧ 2 * (10787 / 100 : ℚ) / 47 < 460 / 100) ∧
    ((500 : ℚ) / 100 < 2 * (19508 / 100) / 78 ∧ 2 * (19508 / 100 : ℚ) / 78 < 501 / 100) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> norm_num

/-- A coherent nuclear share of at most `1/50` of the platinum charge forces
`κ < k e²/250`. -/
theorem platinum_kappa_cap {κ k : ℝ} (hk : 0 < k)
    (h : 2 * (19508 / 100) / 78 * κ ≤ (1 / 50) * k) : κ < k / 250 := by
  have hk' := hk
  nlinarith

end Gravity

end DstDiophantine
