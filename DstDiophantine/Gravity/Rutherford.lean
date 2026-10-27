import DstDiophantine.Gravity.NuclearLength
import DstDiophantine.Gravity.TorsionalLayer
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option linter.style.native false

/-!
# Alpha–gold scattering in the outer region of the nuclear length

## Paper boundary (do **not** claim)

The electromagnetic scale is the observational product `k e² = α ℏ c`
(`SI.coulombMeVFm`), which lies strictly between `1.439964` and `1.439965`
MeV fm. The alpha energy `7.69` MeV, the charges `2` and `79`, and the mass
numbers `4` and `197` are external inputs. Every particle carries both
channels at once. The gravitational
channel is governed by `λ_π`; the electric channel by `ℓ_E` for isolated
charges and by the common length for protons in proton chaos. Between two
nuclei the length is `λ_π`, and the Coulomb term is read with the
equal-scale factor at that length: the protons of a nucleus sit in the sign
cell of the chaotic proton force and are not isolated charges. The head-on
distance is the laboratory-frame Coulomb value
`2 Z k e² / E`. No cross section or half-life is computed here. The coherent
sum `A₁ A₂ κ` of the nuclear prefactor over nucleon pairs is an option, not a
statement of the papers.

## What is proved

* The head-on distance lies in `(29, 30)` fm, outside the first node of `λ_π`,
  and strictly beyond `20 λ_π`.
* For `0 ≤ x ≤ 1/40`, `0 ≤ 1/γ_s(x) - 1 ≤ 13/15987`.
* At every separation `r ≥ 29` fm the phase `λ_π/(2r)` lies in `[0, 1/40]`,
  and the signed Coulomb factor exceeds one by less than `6/10000`.
* In the centre-of-mass frame the head-on distance lies in `(30.18, 30.19)` fm
  and the departure lies strictly between `548/1000000` and `55/100000`.
* At `10` fm the departure lies strictly between `5/1000` and `51/10000`.
* If the nuclear prefactor adds coherently over the `4 · 197` nucleon pairs
  and its far-field share is at most `1/200` of the charge term `2 · 79 k e²`,
  then `κ < k e²/997`.
* Chadwick's three charges, weighted by one percent, give a coherent ratio
  `κ/(k e²)` strictly between `94/100000` and `95/100000`, with standard
  deviation strictly between `123/100000` and `124/100000`.
-/

namespace DstDiophantine

namespace Gravity

open Real Set SI

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

/-- Alpha kinetic energy of the Geiger–Marsden source, `7.69` MeV (external). -/
def alphaGoldEnergyMeV : ℚ := 769 / 100

/-- Gold nuclear charge (external). -/
def goldCharge : ℚ := 79

/-- Laboratory-frame Coulomb head-on distance `2 Z k e² / E`, in fm. -/
def alphaGoldClosestFm : ℚ := 2 * goldCharge * coulombMeVFm / alphaGoldEnergyMeV

theorem alphaGoldClosest_window :
    (29 : ℚ) < alphaGoldClosestFm ∧ alphaGoldClosestFm < 30 := by
  have hden : (0 : ℚ) < (coulombMeVFm_den : ℚ) := by
    unfold coulombMeVFm_den elementaryChargeMantissa
    norm_num
  have hform : alphaGoldClosestFm =
      (15800 : ℚ) * coulombMeVFm_num / ((769 : ℚ) * coulombMeVFm_den) := by
    unfold alphaGoldClosestFm goldCharge alphaGoldEnergyMeV
    rw [coulombMeVFm_eq_num_div_den]
    field_simp
    ring
  rw [hform]
  have hden' : (0 : ℚ) < (769 : ℚ) * coulombMeVFm_den :=
    mul_pos (by norm_num) hden
  constructor
  · rw [lt_div_iff₀ hden']
    have hnat : 29 * 769 * coulombMeVFm_den < 15800 * coulombMeVFm_num := by
      unfold coulombMeVFm_num coulombMeVFm_den fineStructureMantissa
        hbarMantissa speedOfLightNat elementaryChargeMantissa
      native_decide
    exact_mod_cast hnat
  · rw [div_lt_iff₀ hden']
    have hnat : 15800 * coulombMeVFm_num < 30 * 769 * coulombMeVFm_den := by
      unfold coulombMeVFm_num coulombMeVFm_den fineStructureMantissa
        hbarMantissa speedOfLightNat elementaryChargeMantissa
      native_decide
    exact_mod_cast hnat

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

/-! ### Thermal neutrons -/

/-- A thermal neutron of `0.0253` eV has `2T/(m c²)` below `6×10⁻¹¹`, with the
neutron rest energy `939.565` MeV (external), so `(v/c)²` and the rapidity
squared are of that order. -/
theorem thermalNeutron_speedSq_lt :
    2 * ((253 : ℚ) / 10 ^ 10) / (939565 / 1000) < 6 / 10 ^ 11 := by
  norm_num

/-! ### Departure from one, sharpened -/

private noncomputable def c0 (y : ℝ) : ℝ := 1 + y ^ 2 / 2 + y ^ 4 / 12 - cosh y

private noncomputable def c1 (y : ℝ) : ℝ := y + y ^ 3 / 3 - sinh y

private noncomputable def c2 (y : ℝ) : ℝ := 1 + y ^ 2 - cosh y

private noncomputable def c3 (y : ℝ) : ℝ := 2 * y - sinh y

private noncomputable def c4 (y : ℝ) : ℝ := 2 - cosh y

private lemma hasDerivAt_c0 (y : ℝ) : HasDerivAt c0 (c1 y) y := by
  have h2 : HasDerivAt (fun z : ℝ => z ^ 2) (2 * y) y := by simpa using hasDerivAt_pow 2 y
  have h4 : HasDerivAt (fun z : ℝ => z ^ 4) (4 * y ^ 3) y := by simpa using hasDerivAt_pow 4 y
  have h := (((hasDerivAt_const y (1 : ℝ)).add (h2.div_const 2)).add
    (h4.div_const 12)).sub (Real.hasDerivAt_cosh y)
  unfold c0 c1
  refine h.congr_deriv ?_
  ring

private lemma hasDerivAt_c1 (y : ℝ) : HasDerivAt c1 (c2 y) y := by
  have h3 : HasDerivAt (fun z : ℝ => z ^ 3) (3 * y ^ 2) y := by simpa using hasDerivAt_pow 3 y
  have h := ((hasDerivAt_id y).add (h3.div_const 3)).sub (Real.hasDerivAt_sinh y)
  unfold c1 c2
  refine h.congr_deriv ?_
  ring

private lemma hasDerivAt_c2 (y : ℝ) : HasDerivAt c2 (c3 y) y := by
  have h2 : HasDerivAt (fun z : ℝ => z ^ 2) (2 * y) y := by simpa using hasDerivAt_pow 2 y
  have h := ((hasDerivAt_const y (1 : ℝ)).add h2).sub (Real.hasDerivAt_cosh y)
  unfold c2 c3
  refine h.congr_deriv ?_
  ring

private lemma hasDerivAt_c3 (y : ℝ) : HasDerivAt c3 (c4 y) y := by
  have h := (hasDerivAt_id y).const_mul 2 |>.sub (Real.hasDerivAt_sinh y)
  unfold c3 c4
  refine h.congr_deriv ?_
  ring

private lemma nonneg_up_to {f df : ℝ → ℝ} {B : ℝ}
    (hf0 : f 0 = 0) (hcont : Continuous f)
    (hder : ∀ y, HasDerivAt f (df y) y)
    (hnn : ∀ y ∈ Ioo 0 B, 0 ≤ df y) :
    ∀ y ∈ Icc 0 B, 0 ≤ f y := by
  intro y hy
  rcases eq_or_lt_of_le hy.1 with rfl | hypos
  · exact hf0.symm.le
  · obtain ⟨c, hc, hslope⟩ :=
      exists_hasDerivAt_eq_slope f df hypos hcont.continuousOn (fun z _ => hder z)
    rw [hf0, sub_zero, sub_zero] at hslope
    have hfc : 0 ≤ df c := hnn c ⟨hc.1, lt_of_lt_of_le hc.2 hy.2⟩
    have hquot : 0 ≤ f y / y := by
      rw [← hslope]
      exact hfc
    have : 0 ≤ f y / y * y := mul_nonneg hquot hypos.le
    rwa [div_mul_cancel₀ _ hypos.ne'] at this

private lemma c0_nonneg {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1 / 10) : 0 ≤ c0 y := by
  have hB : (0 : ℝ) < 1 / 10 := by norm_num
  have hnn4 : ∀ t ∈ Ioo (0 : ℝ) (1 / 10), 0 ≤ c4 t := by
    intro t ht
    have hexp : exp t ≤ exp (1 / 6 : ℝ) :=
      exp_le_exp.mpr (le_of_lt (lt_trans ht.2 (by norm_num : (1 / 10 : ℝ) < 1 / 6)))
    have hcosh : cosh t ≤ 6 / 5 := by
      have h1 := cosh_le_exp_of_nonneg ht.1.le
      linarith [rf_exp_sixth, hexp]
    unfold c4
    linarith
  have hc3_0 : c3 0 = 0 := by unfold c3; simp
  have hc2_0 : c2 0 = 0 := by unfold c2; simp [cosh_zero]
  have hc1_0 : c1 0 = 0 := by unfold c1; simp
  have hc0_0 : c0 0 = 0 := by unfold c0; simp [cosh_zero]
  have hc3 := nonneg_up_to hc3_0 (by unfold c3; continuity) hasDerivAt_c3 hnn4
  have hnn3 : ∀ t ∈ Ioo (0 : ℝ) (1 / 10), 0 ≤ c3 t := by
    intro t ht
    exact hc3 t ⟨ht.1.le, ht.2.le⟩
  have hc2 := nonneg_up_to hc2_0 (by unfold c2; continuity) hasDerivAt_c2 hnn3
  have hnn2 : ∀ t ∈ Ioo (0 : ℝ) (1 / 10), 0 ≤ c2 t := by
    intro t ht
    exact hc2 t ⟨ht.1.le, ht.2.le⟩
  have hc1 := nonneg_up_to hc1_0 (by unfold c1; continuity) hasDerivAt_c1 hnn2
  have hnn1 : ∀ t ∈ Ioo (0 : ℝ) (1 / 10), 0 ≤ c1 t := by
    intro t ht
    exact hc1 t ⟨ht.1.le, ht.2.le⟩
  have hc0 := nonneg_up_to hc0_0 (by unfold c0; continuity) hasDerivAt_c0 hnn1
  exact hc0 y ⟨hy0, hy1⟩

/-- `cosh x ≤ 1 + x²/2 + x⁴/12` up to phase `1/10`. -/
private lemma cosh_le_poly {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 10) :
    cosh x ≤ 1 + x ^ 2 / 2 + x ^ 4 / 12 := by
  have h := c0_nonneg hx0 hx1
  unfold c0 at h
  linarith

private noncomputable def k0 (y : ℝ) : ℝ := 1 - y ^ 2 / 2 + y ^ 4 / 24 - cos y

private noncomputable def k1 (y : ℝ) : ℝ := -y + y ^ 3 / 6 + sin y

private noncomputable def k2 (y : ℝ) : ℝ := -1 + y ^ 2 / 2 + cos y

private noncomputable def k3 (y : ℝ) : ℝ := y - sin y

private noncomputable def k4 (y : ℝ) : ℝ := 1 - cos y

private lemma hasDerivAt_k0 (y : ℝ) : HasDerivAt k0 (k1 y) y := by
  have h2 : HasDerivAt (fun z : ℝ => z ^ 2) (2 * y) y := by simpa using hasDerivAt_pow 2 y
  have h4 : HasDerivAt (fun z : ℝ => z ^ 4) (4 * y ^ 3) y := by simpa using hasDerivAt_pow 4 y
  have h := ((((hasDerivAt_const y (1 : ℝ)).sub (h2.div_const 2)).add
    (h4.div_const 24)).sub (Real.hasDerivAt_cos y))
  unfold k0 k1
  refine h.congr_deriv ?_
  ring

private lemma hasDerivAt_k1 (y : ℝ) : HasDerivAt k1 (k2 y) y := by
  have h3 : HasDerivAt (fun z : ℝ => z ^ 3) (3 * y ^ 2) y := by simpa using hasDerivAt_pow 3 y
  have h := (((hasDerivAt_id y).neg.add (h3.div_const 6)).add (Real.hasDerivAt_sin y))
  unfold k1 k2
  refine h.congr_deriv ?_
  ring

private lemma hasDerivAt_k2 (y : ℝ) : HasDerivAt k2 (k3 y) y := by
  have h2 : HasDerivAt (fun z : ℝ => z ^ 2) (2 * y) y := by simpa using hasDerivAt_pow 2 y
  have h := (((hasDerivAt_const y (1 : ℝ)).neg.add (h2.div_const 2)).add
    (Real.hasDerivAt_cos y))
  unfold k2 k3
  refine h.congr_deriv ?_
  ring

private lemma hasDerivAt_k3 (y : ℝ) : HasDerivAt k3 (k4 y) y := by
  have h := (hasDerivAt_id y).sub (Real.hasDerivAt_sin y)
  unfold k3 k4
  refine h.congr_deriv ?_
  ring

private lemma k0_nonneg {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1) : 0 ≤ k0 y := by
  have hB : (0 : ℝ) < 1 := by norm_num
  have hnn4 : ∀ t ∈ Ioo (0 : ℝ) 1, 0 ≤ k4 t := by
    intro t ht
    have hπ : t < π := lt_trans ht.2 (by linarith [pi_gt_three])
    have hcos : cos t ≤ 1 := cos_le_one t
    unfold k4
    linarith
  have hk3_0 : k3 0 = 0 := by unfold k3; simp
  have hk2_0 : k2 0 = 0 := by unfold k2; simp
  have hk1_0 : k1 0 = 0 := by unfold k1; simp
  have hk0_0 : k0 0 = 0 := by unfold k0; simp
  have hk3 := nonneg_up_to hk3_0 (by unfold k3; continuity) hasDerivAt_k3 hnn4
  have hnn3 : ∀ t ∈ Ioo (0 : ℝ) 1, 0 ≤ k3 t := by
    intro t ht
    exact hk3 t ⟨ht.1.le, ht.2.le⟩
  have hk2 := nonneg_up_to hk2_0 (by unfold k2; continuity) hasDerivAt_k2 hnn3
  have hnn2 : ∀ t ∈ Ioo (0 : ℝ) 1, 0 ≤ k2 t := by
    intro t ht
    exact hk2 t ⟨ht.1.le, ht.2.le⟩
  have hk1 := nonneg_up_to hk1_0 (by unfold k1; continuity) hasDerivAt_k1 hnn2
  have hnn1 : ∀ t ∈ Ioo (0 : ℝ) 1, 0 ≤ k1 t := by
    intro t ht
    exact hk1 t ⟨ht.1.le, ht.2.le⟩
  have hk0 := nonneg_up_to hk0_0 (by unfold k0; continuity) hasDerivAt_k0 hnn1
  exact hk0 y ⟨hy0, hy1⟩

/-- `cos x ≤ 1 - x²/2 + x⁴/24` on `[0, 1]`. -/
private lemma cos_le_poly {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    cos x ≤ 1 - x ^ 2 / 2 + x ^ 4 / 24 := by
  have h := k0_nonneg hx0 hx1
  unfold k0 at h
  linarith

private lemma gamma_le_poly {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    gammaSEqual x ≤ 1 - x ^ 2 + x ^ 4 / 12 := by
  have hγ := rf_gamma_le hx0 hx1
  have hcos := cos_le_poly hx0 hx1
  linarith

private lemma gamma_ge_coshPoly {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 10) :
    1 - x ^ 2 * (1 + x ^ 2 / 2 + x ^ 4 / 12) ≤ gammaSEqual x := by
  have hγ := rf_gamma_ge hx0
  have hcosh := cosh_le_poly hx0 hx1
  have hx2 : 0 ≤ x ^ 2 := by positivity
  have hmul : x ^ 2 * cosh x ≤ x ^ 2 * (1 + x ^ 2 / 2 + x ^ 4 / 12) :=
    mul_le_mul_of_nonneg_left hcosh hx2
  linarith

set_option linter.style.native false in
private theorem rf_pion_scattering_bounds :
    (14138 / 10000 : ℝ) < (pionComptonFm : ℝ) ∧
      (pionComptonFm : ℝ) < 14139 / 10000 := by
  have hden : (0 : ℚ) < (pionComptonFm_den : ℚ) := by
    unfold pionComptonFm_den hbarC_MeVfm_den SI.elementaryChargeMantissa
      SI.pionMassMeVMantissa
    norm_num
  have hlo : (14138 / 10000 : ℚ) < pionComptonFm := by
    rw [pionComptonFm_eq_num_div_den]
    have hnat : 14138 * pionComptonFm_den < 10000 * pionComptonFm_num := by
      unfold pionComptonFm_num pionComptonFm_den hbarC_MeVfm_num hbarC_MeVfm_den
        SI.hbarMantissa SI.speedOfLightNat SI.elementaryChargeMantissa
        SI.pionMassMeVMantissa SI.pionMassMeVScale
      native_decide
    rw [div_lt_div_iff₀ (by norm_num) hden]
    exact_mod_cast hnat
  have hhi : pionComptonFm < (14139 / 10000 : ℚ) := by
    rw [pionComptonFm_eq_num_div_den]
    have hnat : 10000 * pionComptonFm_num < 14139 * pionComptonFm_den := by
      unfold pionComptonFm_num pionComptonFm_den hbarC_MeVfm_num hbarC_MeVfm_den
        SI.hbarMantissa SI.speedOfLightNat SI.elementaryChargeMantissa
        SI.pionMassMeVMantissa SI.pionMassMeVScale
      native_decide
    rw [div_lt_div_iff₀ hden (by norm_num)]
    exact_mod_cast hnat
  constructor
  · rw [show (14138 / 10000 : ℝ) = ((14138 / 10000 : ℚ) : ℝ) by norm_num]
    exact_mod_cast hlo
  · rw [show (14139 / 10000 : ℝ) = ((14139 / 10000 : ℚ) : ℝ) by norm_num]
    exact_mod_cast hhi

/-- The laboratory head-on distance lies beyond twenty pion wavelengths. -/
theorem alphaGold_beyond_twenty_pion :
    20 * (pionComptonFm : ℝ) < (alphaGoldClosestFm : ℝ) := by
  have hpion := rf_pion_scattering_bounds.2
  have hd : (29 : ℝ) < (alphaGoldClosestFm : ℝ) := by
    exact_mod_cast alphaGoldClosest_window.1
  nlinarith

private lemma dev_upper_of_delta {x δ : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 10)
    (hδ : x ^ 2 * (1 + x ^ 2 / 2 + x ^ 4 / 12) ≤ δ) (hδ1 : δ < 1) :
    1 / gammaSEqual x - 1 ≤ δ / (1 - δ) := by
  have hlow := gamma_ge_coshPoly hx0 hx1
  have hγ : 1 - δ ≤ gammaSEqual x := by linarith
  have hup : gammaSEqual x ≤ 1 := by
    have h := rf_gamma_le hx0 (by linarith)
    have hc := cos_le_one x
    linarith
  have hpos : 0 < gammaSEqual x := by linarith
  have hne : gammaSEqual x ≠ 0 := hpos.ne'
  rw [div_sub_one hne]
  have hnum : 1 - gammaSEqual x ≤ δ := by linarith
  rw [div_le_div_iff₀ hpos (by linarith : (0 : ℝ) < 1 - δ)]
  have hleft : (1 - gammaSEqual x) * (1 - δ) ≤ δ * (1 - δ) :=
    mul_le_mul_of_nonneg_right hnum (by linarith)
  have hright : δ * (1 - δ) ≤ δ * gammaSEqual x := by
    have : 1 - δ ≤ gammaSEqual x := hγ
    exact mul_le_mul_of_nonneg_left this (by linarith)
  linarith

/-- At every separation `r ≥ 29` fm the signed factor exceeds one by less than
six parts in ten thousand. -/
theorem nuclear_dev_six {r : ℝ} (hr : 29 ≤ r) :
    0 ≤ 1 / gammaSEqual ((pionComptonFm : ℝ) / (2 * r)) - 1 ∧
      1 / gammaSEqual ((pionComptonFm : ℝ) / (2 * r)) - 1 < 6 / 10000 := by
  have hphase := pion_phase_le_of_ge hr
  set x : ℝ := (pionComptonFm : ℝ) / (2 * r)
  have hx10 : x ≤ 1 / 10 := by linarith [hphase.2]
  have hxUp : x < (14139 / 10000 : ℝ) / (2 * 29) := by
    have hpion := rf_pion_scattering_bounds.2
    have hnonneg : 0 ≤ (pionComptonFm : ℝ) :=
      le_of_lt (lt_trans (by norm_num) rf_pion_scattering_bounds.1)
    have hden : (0 : ℝ) < 2 * 29 := by norm_num
    have hfrac : (pionComptonFm : ℝ) / (2 * r) ≤ (pionComptonFm : ℝ) / (2 * 29) := by
      refine div_le_div_of_nonneg_left hnonneg hden ?_
      linarith
    have hstrict : (pionComptonFm : ℝ) / (2 * 29) < (14139 / 10000) / (2 * 29) := by
      exact div_lt_div_of_pos_right hpion hden
    exact lt_of_le_of_lt hfrac hstrict
  have hxU : x < (2438 / 100000 : ℝ) := by
    have hcmp : (14139 / 10000 : ℝ) / (2 * 29) < 2438 / 100000 := by norm_num
    exact lt_trans hxUp hcmp
  have hδ : x ^ 2 * (1 + x ^ 2 / 2 + x ^ 4 / 12) ≤
      (2438 / 100000 : ℝ) ^ 2 * (1 + (2438 / 100000 : ℝ) ^ 2 / 2 +
        (2438 / 100000 : ℝ) ^ 4 / 12) := by
    have hx0 := hphase.1
    have hmon : x ≤ 2438 / 100000 := hxU.le
    have hsq : x ^ 2 ≤ (2438 / 100000 : ℝ) ^ 2 := pow_le_pow_left₀ hx0 hmon 2
    have h4 : x ^ 4 ≤ (2438 / 100000 : ℝ) ^ 4 := pow_le_pow_left₀ hx0 hmon 4
    have hpoly : 1 + x ^ 2 / 2 + x ^ 4 / 12 ≤
        1 + (2438 / 100000 : ℝ) ^ 2 / 2 + (2438 / 100000 : ℝ) ^ 4 / 12 := by
      gcongr
    exact mul_le_mul hsq hpoly (by positivity) (by positivity)
  have hcap : x ^ 2 * (1 + x ^ 2 / 2 + x ^ 4 / 12) < (599 / 1000000 : ℝ) := by
    have hnum : (2438 / 100000 : ℝ) ^ 2 * (1 + (2438 / 100000 : ℝ) ^ 2 / 2 +
        (2438 / 100000 : ℝ) ^ 4 / 12) < 599 / 1000000 := by norm_num
    exact lt_of_le_of_lt hδ hnum
  have hle' := dev_upper_of_delta hphase.1 hx10 hcap.le (by norm_num)
  have hfin : (599 / 1000000 : ℝ) / (1 - 599 / 1000000) < 6 / 10000 := by norm_num
  refine ⟨?_, lt_of_le_of_lt hle' hfin⟩
  · have hup : gammaSEqual x ≤ 1 := by
      have h := rf_gamma_le hphase.1 (by linarith)
      linarith [cos_le_one x]
    have hpos : 0 < gammaSEqual x := by
      have hlow := gamma_ge_coshPoly hphase.1 hx10
      linarith [hcap]
    rw [div_sub_one hpos.ne']
    exact div_nonneg (by linarith) hpos.le

/-! ### Centre-of-mass head-on distance -/

/-- Gold mass number used for the recoil of an alpha particle (external). -/
def goldMassNumber : ℚ := 197

/-- Centre-of-mass head-on distance, laboratory distance times `(A+4)/A`. -/
def alphaGoldClosestCmFm : ℚ :=
  alphaGoldClosestFm * (goldMassNumber + 4) / goldMassNumber

theorem alphaGoldClosestCm_window :
    (3018 / 100 : ℚ) < alphaGoldClosestCmFm ∧ alphaGoldClosestCmFm < 3019 / 100 := by
  have hden : (0 : ℚ) < (coulombMeVFm_den : ℚ) := by
    unfold coulombMeVFm_den elementaryChargeMantissa
    norm_num
  have hform : alphaGoldClosestCmFm =
      (15800 : ℚ) * coulombMeVFm_num * 201 /
        ((769 : ℚ) * coulombMeVFm_den * 197) := by
    unfold alphaGoldClosestCmFm alphaGoldClosestFm goldMassNumber goldCharge
      alphaGoldEnergyMeV
    rw [coulombMeVFm_eq_num_div_den]
    field_simp
    ring
  rw [hform]
  have hden' : (0 : ℚ) < (769 : ℚ) * coulombMeVFm_den * 197 :=
    mul_pos (mul_pos (by norm_num) hden) (by norm_num)
  constructor
  · rw [lt_div_iff₀ hden']
    have hclear : (3018 / 100 : ℚ) * ((769 : ℚ) * coulombMeVFm_den * 197) =
        (3018 : ℚ) * (769 * coulombMeVFm_den * 197) / 100 := by ring
    rw [hclear, div_lt_iff₀ (by norm_num)]
    have hnat : 3018 * 769 * coulombMeVFm_den * 197 <
        15800 * coulombMeVFm_num * 201 * 100 := by
      unfold coulombMeVFm_num coulombMeVFm_den fineStructureMantissa
        hbarMantissa speedOfLightNat elementaryChargeMantissa
      native_decide
    exact_mod_cast hnat
  · rw [div_lt_iff₀ hden']
    have hclear : (3019 / 100 : ℚ) * ((769 : ℚ) * coulombMeVFm_den * 197) =
        (3019 : ℚ) * (769 * coulombMeVFm_den * 197) / 100 := by ring
    rw [hclear, lt_div_iff₀ (by norm_num)]
    have hnat : 15800 * coulombMeVFm_num * 201 * 100 <
        3019 * 769 * coulombMeVFm_den * 197 := by
      unfold coulombMeVFm_num coulombMeVFm_den fineStructureMantissa
        hbarMantissa speedOfLightNat elementaryChargeMantissa
      native_decide
    exact_mod_cast hnat

private lemma dev_lower_of_phase {x xL : ℝ} (hx0 : 0 ≤ xL) (hx : xL ≤ x) (hx1 : x ≤ 1 / 10)
    (hpoly : 0 < 1 - xL ^ 2 + xL ^ 4 / 12) :
    (xL ^ 2 - xL ^ 4 / 12) / (1 - xL ^ 2 + xL ^ 4 / 12) ≤
      1 / gammaSEqual x - 1 := by
  have hγx := gamma_le_poly (hx0.trans hx) (by linarith)
  have hdec : 1 - x ^ 2 + x ^ 4 / 12 ≤ 1 - xL ^ 2 + xL ^ 4 / 12 := by
    have hdiff : (1 - x ^ 2 + x ^ 4 / 12) - (1 - xL ^ 2 + xL ^ 4 / 12) =
        (xL - x) * (xL + x) * (1 - (x ^ 2 + xL ^ 2) / 12) := by ring
    have hfac : 0 ≤ (x - xL) * (xL + x) * (1 - (x ^ 2 + xL ^ 2) / 12) := by
      have hsum : 0 ≤ xL + x := by linarith
      have hquad : x ^ 2 + xL ^ 2 ≤ 2 := by nlinarith
      have hbrk : 0 ≤ 1 - (x ^ 2 + xL ^ 2) / 12 := by linarith
      have hgap : 0 ≤ x - xL := by linarith
      exact mul_nonneg (mul_nonneg hgap hsum) hbrk
    linarith
  have hγ : gammaSEqual x ≤ 1 - xL ^ 2 + xL ^ 4 / 12 := le_trans hγx hdec
  have hpos : 0 < gammaSEqual x := by
    have hlow := gamma_ge_coshPoly (hx0.trans hx) hx1
    have hsmall : x ^ 2 * (1 + x ^ 2 / 2 + x ^ 4 / 12) < 1 := by
      have hx10 : x ≤ 1 / 10 := by linarith
      have hx2 : x ^ 2 ≤ (1 / 10 : ℝ) ^ 2 := pow_le_pow_left₀ (hx0.trans hx) hx10 2
      have hx4 : x ^ 4 ≤ (1 / 10 : ℝ) ^ 4 := pow_le_pow_left₀ (hx0.trans hx) hx10 4
      have hpoly' : 1 + x ^ 2 / 2 + x ^ 4 / 12 ≤
          1 + (1 / 10 : ℝ) ^ 2 / 2 + (1 / 10 : ℝ) ^ 4 / 12 := by gcongr
      have hprod : x ^ 2 * (1 + x ^ 2 / 2 + x ^ 4 / 12) ≤
          (1 / 10 : ℝ) ^ 2 * (1 + (1 / 10 : ℝ) ^ 2 / 2 + (1 / 10 : ℝ) ^ 4 / 12) :=
        mul_le_mul hx2 hpoly' (by positivity) (by positivity)
      have hlt : (1 / 10 : ℝ) ^ 2 * (1 + (1 / 10 : ℝ) ^ 2 / 2 + (1 / 10 : ℝ) ^ 4 / 12) < 1 := by
        norm_num
      exact lt_of_le_of_lt hprod hlt
    linarith
  rw [div_sub_one hpos.ne']
  rw [div_le_div_iff₀ hpoly hpos]
  have hnum : xL ^ 2 - xL ^ 4 / 12 ≤ 1 - gammaSEqual x := by linarith
  have : (xL ^ 2 - xL ^ 4 / 12) * gammaSEqual x ≤
      (1 - gammaSEqual x) * (1 - xL ^ 2 + xL ^ 4 / 12) := by
    have h1 : (xL ^ 2 - xL ^ 4 / 12) * gammaSEqual x ≤
        (xL ^ 2 - xL ^ 4 / 12) * (1 - xL ^ 2 + xL ^ 4 / 12) := by
      have hnum0 : 0 ≤ xL ^ 2 - xL ^ 4 / 12 := by
        have hxsq : xL ^ 2 ≤ 1 := by nlinarith
        have hnn : 0 ≤ xL ^ 2 := by nlinarith
        have hmul : xL ^ 4 ≤ xL ^ 2 := by
          calc
            xL ^ 4 = xL ^ 2 * xL ^ 2 := by ring
            _ ≤ xL ^ 2 * 1 := mul_le_mul_of_nonneg_left hxsq hnn
            _ = xL ^ 2 := by ring
        have hdiv : xL ^ 4 / 12 ≤ xL ^ 2 / 12 :=
          div_le_div_of_nonneg_right hmul (by norm_num)
        have hshrink : xL ^ 2 / 12 ≤ xL ^ 2 := by
          rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 12)]
          nlinarith
        linarith
      exact mul_le_mul_of_nonneg_left hγ hnum0
    have h2 : (xL ^ 2 - xL ^ 4 / 12) * (1 - xL ^ 2 + xL ^ 4 / 12) ≤
        (1 - gammaSEqual x) * (1 - xL ^ 2 + xL ^ 4 / 12) :=
      mul_le_mul_of_nonneg_right hnum hpoly.le
    linarith
  linarith

/-- At the centre-of-mass head-on distance the departure lies strictly between
`5.48×10⁻⁴` and `5.50×10⁻⁴`. -/
theorem alphaGoldCm_dev :
    (548 / 1000000 : ℝ) <
        1 / gammaSEqual ((pionComptonFm : ℝ) / (2 * (alphaGoldClosestCmFm : ℝ))) - 1 ∧
      1 / gammaSEqual ((pionComptonFm : ℝ) / (2 * (alphaGoldClosestCmFm : ℝ))) - 1 <
        55 / 100000 := by
  set d : ℝ := (alphaGoldClosestCmFm : ℝ)
  have hdlo : (3018 / 100 : ℝ) < d := by
    have hcast : ((3018 / 100 : ℚ) : ℝ) < (alphaGoldClosestCmFm : ℝ) := by
      exact_mod_cast alphaGoldClosestCm_window.1
    have heq : ((3018 / 100 : ℚ) : ℝ) = (3018 / 100 : ℝ) := by norm_num
    simpa [d, heq] using hcast
  have hdhi : d < (3019 / 100 : ℝ) := by
    have hcast : (alphaGoldClosestCmFm : ℝ) < ((3019 / 100 : ℚ) : ℝ) := by
      exact_mod_cast alphaGoldClosestCm_window.2
    have heq : ((3019 / 100 : ℚ) : ℝ) = (3019 / 100 : ℝ) := by norm_num
    simpa [d, heq] using hcast
  set x : ℝ := (pionComptonFm : ℝ) / (2 * d)
  have hpion := rf_pion_scattering_bounds
  have hxpos : 0 < x := by
    have hpion0 : (0 : ℝ) < (pionComptonFm : ℝ) := lt_trans (by norm_num) hpion.1
    have hd0 : (0 : ℝ) < 2 * d := by linarith
    exact div_pos hpion0 hd0
  have hxU : x < (14139 / 10000 : ℝ) / (2 * (3018 / 100)) := by
    have hden : (0 : ℝ) < 2 * (3018 / 100 : ℝ) := by norm_num
    have hdpos : (0 : ℝ) < d := by linarith [hdlo]
    have hleft : x < (14139 / 10000) / (2 * d) := by
      rw [div_lt_div_iff₀ (by linarith : (0 : ℝ) < 2 * d) (by linarith : (0 : ℝ) < 2 * d)]
      nlinarith [hpion.2, hdpos]
    have hright : (14139 / 10000 : ℝ) / (2 * d) < (14139 / 10000) / (2 * (3018 / 100)) := by
      refine div_lt_div_of_pos_left (by norm_num) (by norm_num) ?_
      linarith [hdlo]
    exact lt_trans hleft hright
  have hxL : (14138 / 10000 : ℝ) / (2 * (3019 / 100)) < x := by
    have hleft : (14138 / 10000 : ℝ) / (2 * (3019 / 100)) < (14138 / 10000) / (2 * d) := by
      refine div_lt_div_of_pos_left (by norm_num) (by linarith [hdlo]) ?_
      linarith [hdhi]
    have hright : (14138 / 10000 : ℝ) / (2 * d) < x := by
      rw [div_lt_div_iff₀ (by linarith [hdlo] : (0 : ℝ) < 2 * d)
        (by linarith [hdlo] : (0 : ℝ) < 2 * d)]
      nlinarith [hpion.1, hdlo]
    exact lt_trans hleft hright
  have hx10 : x ≤ 1 / 10 := by
    have hcmp : (14139 / 10000 : ℝ) / (2 * (3018 / 100)) < 1 / 10 := by norm_num
    linarith
  have hδ : x ^ 2 * (1 + x ^ 2 / 2 + x ^ 4 / 12) ≤
      ((14139 / 10000 : ℝ) / (2 * (3018 / 100))) ^ 2 *
        (1 + ((14139 / 10000 : ℝ) / (2 * (3018 / 100))) ^ 2 / 2 +
          ((14139 / 10000 : ℝ) / (2 * (3018 / 100))) ^ 4 / 12) := by
    have hx0 : 0 ≤ x := hxpos.le
    have hmon : x ≤ (14139 / 10000 : ℝ) / (2 * (3018 / 100)) := hxU.le
    have hsq : x ^ 2 ≤ ((14139 / 10000 : ℝ) / (2 * (3018 / 100))) ^ 2 :=
      pow_le_pow_left₀ hx0 hmon 2
    have h4 : x ^ 4 ≤ ((14139 / 10000 : ℝ) / (2 * (3018 / 100))) ^ 4 :=
      pow_le_pow_left₀ hx0 hmon 4
    have hpoly : 1 + x ^ 2 / 2 + x ^ 4 / 12 ≤
        1 + ((14139 / 10000 : ℝ) / (2 * (3018 / 100))) ^ 2 / 2 +
          ((14139 / 10000 : ℝ) / (2 * (3018 / 100))) ^ 4 / 12 := by gcongr
    exact mul_le_mul hsq hpoly (by positivity) (by positivity)
  have hδlt : ((14139 / 10000 : ℝ) / (2 * (3018 / 100))) ^ 2 *
      (1 + ((14139 / 10000 : ℝ) / (2 * (3018 / 100))) ^ 2 / 2 +
        ((14139 / 10000 : ℝ) / (2 * (3018 / 100))) ^ 4 / 12) < 5495 / 10000000 := by
    norm_num
  have hδ1 : x ^ 2 * (1 + x ^ 2 / 2 + x ^ 4 / 12) < 1 := by
    have : (5495 / 10000000 : ℝ) < 1 := by norm_num
    linarith
  have hup := dev_upper_of_delta hxpos.le hx10 (le_trans hδ hδlt.le)
    (by norm_num : (5495 / 10000000 : ℝ) < 1)
  have hupfin : (5495 / 10000000 : ℝ) / (1 - 5495 / 10000000) < 55 / 100000 := by norm_num
  have hxL0 : 0 ≤ (14138 / 10000 : ℝ) / (2 * (3019 / 100)) := by positivity
  have hpolypos : 0 < 1 - ((14138 / 10000 : ℝ) / (2 * (3019 / 100))) ^ 2 +
      ((14138 / 10000 : ℝ) / (2 * (3019 / 100))) ^ 4 / 12 := by norm_num
  have hlow := dev_lower_of_phase hxL0 hxL.le hx10 hpolypos
  have hlowfin : (548 / 1000000 : ℝ) <
      (((14138 / 10000 : ℝ) / (2 * (3019 / 100))) ^ 2 -
        ((14138 / 10000 : ℝ) / (2 * (3019 / 100))) ^ 4 / 12) /
      (1 - ((14138 / 10000 : ℝ) / (2 * (3019 / 100))) ^ 2 +
        ((14138 / 10000 : ℝ) / (2 * (3019 / 100))) ^ 4 / 12) := by norm_num
  exact ⟨lt_of_lt_of_le hlowfin hlow, lt_of_le_of_lt hup hupfin⟩

/-- At `10` fm the signed factor departs from one by just over five parts in a
thousand, and by less than `5.1` parts. -/
theorem dev_at_ten_fm :
    (5 / 1000 : ℝ) < 1 / gammaSEqual ((pionComptonFm : ℝ) / 20) - 1 ∧
      1 / gammaSEqual ((pionComptonFm : ℝ) / 20) - 1 < 51 / 10000 := by
  set x : ℝ := (pionComptonFm : ℝ) / 20
  have hpion := rf_pion_scattering_bounds
  have hxpos : 0 < x := by
    have : (0 : ℝ) < (pionComptonFm : ℝ) := lt_trans (by norm_num) hpion.1
    exact div_pos this (by norm_num)
  have hxU : x < (14139 / 10000 : ℝ) / 20 := by
    exact div_lt_div_of_pos_right hpion.2 (by norm_num)
  have hxL : (14138 / 10000 : ℝ) / 20 < x := by
    exact div_lt_div_of_pos_right hpion.1 (by norm_num)
  have hx10 : x ≤ 1 / 10 := by
    have : (14139 / 10000 : ℝ) / 20 < 1 / 10 := by norm_num
    linarith
  have hδ : x ^ 2 * (1 + x ^ 2 / 2 + x ^ 4 / 12) ≤
      ((14139 / 10000 : ℝ) / 20) ^ 2 *
        (1 + ((14139 / 10000 : ℝ) / 20) ^ 2 / 2 + ((14139 / 10000 : ℝ) / 20) ^ 4 / 12) := by
    have hmon : x ≤ (14139 / 10000 : ℝ) / 20 := hxU.le
    have hsq := pow_le_pow_left₀ hxpos.le hmon 2
    have h4 := pow_le_pow_left₀ hxpos.le hmon 4
    have hpoly : 1 + x ^ 2 / 2 + x ^ 4 / 12 ≤
        1 + ((14139 / 10000 : ℝ) / 20) ^ 2 / 2 + ((14139 / 10000 : ℝ) / 20) ^ 4 / 12 := by
      gcongr
    exact mul_le_mul hsq hpoly (by positivity) (by positivity)
  have hδlt : ((14139 / 10000 : ℝ) / 20) ^ 2 *
      (1 + ((14139 / 10000 : ℝ) / 20) ^ 2 / 2 + ((14139 / 10000 : ℝ) / 20) ^ 4 / 12) <
      (5036 / 1000000 : ℝ) := by norm_num
  have hδ1 : x ^ 2 * (1 + x ^ 2 / 2 + x ^ 4 / 12) < 1 := by
    have : (5036 / 1000000 : ℝ) < 1 := by norm_num
    linarith
  have hup := dev_upper_of_delta hxpos.le hx10 (le_trans hδ hδlt.le)
    (by norm_num : (5036 / 1000000 : ℝ) < 1)
  have hupfin : (5036 / 1000000 : ℝ) / (1 - 5036 / 1000000) < 51 / 10000 := by norm_num
  have hxL0 : 0 ≤ (14138 / 10000 : ℝ) / 20 := by positivity
  have hpolypos : 0 < 1 - ((14138 / 10000 : ℝ) / 20) ^ 2 +
      ((14138 / 10000 : ℝ) / 20) ^ 4 / 12 := by norm_num
  have hlow := dev_lower_of_phase hxL0 hxL.le hx10 hpolypos
  have hlowfin : (5 / 1000 : ℝ) <
      (((14138 / 10000 : ℝ) / 20) ^ 2 - ((14138 / 10000 : ℝ) / 20) ^ 4 / 12) /
        (1 - ((14138 / 10000 : ℝ) / 20) ^ 2 + ((14138 / 10000 : ℝ) / 20) ^ 4 / 12) := by
    norm_num
  exact ⟨lt_of_lt_of_le hlowfin hlow, lt_of_le_of_lt hup hupfin⟩

/-! ### Chadwick's least squares -/

/-- Inverse-variance weight for a one-percent error on a charge `Z`. -/
def chadwickWeight (Z : ℚ) : ℚ := 1 / (Z / 100) ^ 2

/-- Coherent ratio `κ/(k e²)` from copper, silver, and platinum, weighted by
one percent on each measured charge. The charges and mass numbers are external. -/
def chadwickBeta : ℚ :=
  let wCu := chadwickWeight 29
  let wAg := chadwickWeight 47
  let wPt := chadwickWeight 78
  let aCu := 2 * (6355 / 100)
  let aAg := 2 * (10787 / 100)
  let aPt := 2 * (19508 / 100)
  let num := wCu * aCu * (29 - 293 / 10) + wAg * aAg * (47 - 463 / 10) +
    wPt * aPt * (78 - 774 / 10)
  let den := wCu * aCu ^ 2 + wAg * aAg ^ 2 + wPt * aPt ^ 2
  num / den

/-- Variance of that weighted fit. -/
def chadwickVariance : ℚ :=
  let wCu := chadwickWeight 29
  let wAg := chadwickWeight 47
  let wPt := chadwickWeight 78
  let aCu := 2 * (6355 / 100)
  let aAg := 2 * (10787 / 100)
  let aPt := 2 * (19508 / 100)
  1 / (wCu * aCu ^ 2 + wAg * aAg ^ 2 + wPt * aPt ^ 2)

theorem chadwickBeta_window :
    (94 / 100000 : ℚ) < chadwickBeta ∧ chadwickBeta < 95 / 100000 := by
  unfold chadwickBeta chadwickWeight
  norm_num

theorem chadwickVariance_window :
    ((123 / 100000 : ℚ) ^ 2) < chadwickVariance ∧
      chadwickVariance < ((124 / 100000) ^ 2) := by
  unfold chadwickVariance chadwickWeight
  norm_num

theorem chadwickSigma_window :
    (123 / 100000 : ℝ) < Real.sqrt (chadwickVariance : ℝ) ∧
      Real.sqrt (chadwickVariance : ℝ) < 124 / 100000 := by
  have hvar := chadwickVariance_window
  have hlo : ((123 / 100000 : ℚ) ^ 2 : ℝ) < (chadwickVariance : ℝ) := by
    exact_mod_cast hvar.1
  have hhi : (chadwickVariance : ℝ) < ((124 / 100000 : ℚ) ^ 2 : ℝ) := by
    exact_mod_cast hvar.2
  have hposv : (0 : ℝ) ≤ (chadwickVariance : ℝ) :=
    le_of_lt (lt_trans (by norm_num : (0 : ℝ) < ((123 / 100000 : ℚ) ^ 2 : ℝ)) hlo)
  constructor
  · rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 123 / 100000)]
    have hsq : ((123 / 100000 : ℝ) ^ 2) = ((123 / 100000 : ℚ) ^ 2 : ℝ) := by norm_num
    rw [hsq]
    exact Real.sqrt_lt_sqrt (sq_nonneg _) hlo
  · rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 124 / 100000)]
    have hsq : ((124 / 100000 : ℝ) ^ 2) = ((124 / 100000 : ℚ) ^ 2 : ℝ) := by norm_num
    rw [hsq]
    exact Real.sqrt_lt_sqrt hposv hhi

end Gravity

end DstDiophantine
