import DstDiophantine.Gravity.StrongChannel
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Neutron scattering outside the rapidity wall

## Paper boundary (do **not** claim)

The prefactor `κ`, a scattering amplitude inside the wall, and the sign of a
measured scattering length are **not** derived. The neutron rest energy
`939.565` MeV is an external input. The rapidity is the nonnegative parameter
of the pair.

## What is proved

At vanishing phase the interference factor equals `cosh(φ/2)`, so the pair
force is the inverse-square law of strength `κ/cosh(φ/2)`. That coefficient
is `κ/√(1 + T/(2mc²))`. At `1` MeV the square root lies in
`(1.000266, 1.000267)`; at `14` MeV, in `(1.003718, 1.003719)`. From the
first energy to the second the coefficient falls by a fraction strictly less
than `4/1000`.

On `0 < x < π/4`, at every nonnegative rapidity, the force stays inward and
exceeds that inverse-square law by a fraction strictly smaller than
`e^{-x}/(cos x - sin x) - 1`. For `x ≤ 7/100` the fraction is strictly less
than `6/1000`.

If the nucleons lie in a ball and the neutron lies outside the concentric
ball enlarged by the rapidity wall, every pair is outside its wall and the
net force has a negative radial component.
-/

namespace DstDiophantine

namespace Gravity

open Real Set

/-! ### Far field of one pair -/

private theorem sigmaEqual_zero : sigmaEqual 0 = 0 := by
  simp [sigmaEqual]

theorem gammaRapidity_zero_phase (δ : ℝ) : gammaRapidity 0 δ = cosh δ := by
  simp [gammaRapidity, gammaSEqual_zero, sigmaEqual_zero]

theorem cosh_half_sq (φ : ℝ) : cosh (φ / 2) ^ 2 = (cosh φ + 1) / 2 := by
  have h := cosh_two_mul (φ / 2)
  rw [show (2 : ℝ) * (φ / 2) = φ by ring] at h
  have hsq := cosh_sq_sub_sinh_sq (φ / 2)
  linarith

theorem hasDerivAt_sigmaEqual (x : ℝ) :
    HasDerivAt sigmaEqual (2 * sinh x * sin x) x := by
  have h1 : HasDerivAt (fun y => cosh y * sin y) (sinh x * sin x + cosh x * cos x) x :=
    (hasDerivAt_cosh x).mul (hasDerivAt_sin x)
  have h2 : HasDerivAt (fun y => sinh y * cos y) (cosh x * cos x + sinh x * -sin x) x :=
    (hasDerivAt_sinh x).mul (hasDerivAt_cos x)
  have hsub := h1.sub h2
  have heq : (sinh x * sin x + cosh x * cos x) - (cosh x * cos x + sinh x * -sin x) =
      2 * sinh x * sin x := by ring
  unfold sigmaEqual
  rw [heq] at hsub
  exact hsub

private theorem continuous_sigmaEqual : Continuous sigmaEqual := by
  unfold sigmaEqual
  exact (continuous_cosh.mul continuous_sin).sub (continuous_sinh.mul continuous_cos)

theorem sigmaEqual_pos {x : ℝ} (hx : 0 < x) (hxπ : x < π) : 0 < sigmaEqual x := by
  have hmono : StrictMonoOn sigmaEqual (Icc 0 π) := by
    refine strictMonoOn_of_deriv_pos (convex_Icc _ _) continuous_sigmaEqual.continuousOn ?_
    intro y hy
    rw [interior_Icc] at hy
    rw [(hasDerivAt_sigmaEqual y).deriv]
    have hsin : 0 < sin y := sin_pos_of_pos_of_lt_pi hy.1 hy.2
    have hsinh : 0 < sinh y := sinh_pos_iff.mpr hy.1
    positivity
  have hlt := hmono ⟨le_rfl, pi_pos.le⟩ ⟨hx.le, hxπ.le⟩ hx
  simpa [sigmaEqual_zero] using hlt

private theorem gammaSEqual_lt_one_of_pos {x : ℝ} (hx : 0 < x) (hxπ : x < π) :
    gammaSEqual x < 1 := by
  have hanti := strictAntiOn_gammaSEqual_even 0
  have h0 : ((2 * 0 : ℕ) : ℝ) * π ∈
      Icc (((2 * 0 : ℕ) : ℝ) * π) (((2 * 0 : ℕ) : ℝ) * π + π) :=
    ⟨le_rfl, le_add_of_nonneg_right pi_pos.le⟩
  have hxI : x ∈ Icc (((2 * 0 : ℕ) : ℝ) * π) (((2 * 0 : ℕ) : ℝ) * π + π) := by
    refine ⟨?_, ?_⟩
    · have hzero : ((2 * 0 : ℕ) : ℝ) * π = 0 := by simp
      linarith
    · have htop : ((2 * 0 : ℕ) : ℝ) * π + π = π := by simp
      linarith
  have hx0' : ((2 * 0 : ℕ) : ℝ) * π < x := by simpa using hx
  have hlt := hanti h0 hxI hx0'
  simpa [gammaSEqual_zero] using hlt

private theorem gamma_sub_sigma (x : ℝ) :
    gammaSEqual x - sigmaEqual x = exp x * (cos x - sin x) := by
  have h := sigmaEqual_sub_gammaSEqual x
  linarith

private theorem cos_sub_sin_pos {x : ℝ} (hx0 : 0 ≤ x) (hx : x < π / 4) :
    0 < cos x - sin x := by
  have hcos : 0 < cos x :=
    cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], by linarith [pi_pos]⟩
  rcases eq_or_lt_of_le hx0 with rfl | hxpos
  · simp
  · have hmem₁ : x ∈ Ioo (-(π / 2)) (π / 2) := ⟨by linarith [pi_pos], by linarith [pi_pos]⟩
    have hmem₂ : (π / 4) ∈ Ioo (-(π / 2)) (π / 2) :=
      ⟨by linarith [pi_pos], by linarith [pi_pos]⟩
    have htan : tan x < 1 := by
      have hstep := strictMonoOn_tan hmem₁ hmem₂ hx
      rwa [tan_pi_div_four] at hstep
    rw [tan_eq_sin_div_cos, div_lt_one hcos] at htan
    linarith

private theorem tanh_lt_one (δ : ℝ) : tanh δ < 1 := by
  have hcosh : 0 < cosh δ := cosh_pos δ
  rw [tanh_eq_sinh_div_cosh, div_lt_one hcosh]
  have hsub : cosh δ - sinh δ = exp (-δ) := by
    rw [cosh_eq, sinh_eq]
    ring
  linarith [exp_pos (-δ)]

theorem gammaRapidity_ratio {x δ : ℝ} :
    gammaRapidity x δ / cosh δ = gammaSEqual x - tanh δ * sigmaEqual x := by
  unfold gammaRapidity
  rw [tanh_eq_sinh_div_cosh]
  field_simp [(cosh_pos δ).ne']

/-- Outside the wall the pair force exceeds the inverse-square law of strength
`κ/cosh(φ/2)`. The fractional excess is strictly smaller than
`e^{-x}/(cos x - sin x) - 1`. -/
theorem farField_excess {x δ : ℝ} (hx0 : 0 < x) (hx : x < π / 4) (hδ : 0 ≤ δ) :
    gammaRapidity x δ < cosh δ ∧
      cosh δ / gammaRapidity x δ - 1 < exp (-x) / (cos x - sin x) - 1 := by
  have hπ : x < π := lt_trans hx (by linarith [pi_gt_three])
  have hσ : 0 < sigmaEqual x := sigmaEqual_pos hx0 hπ
  have hγs : gammaSEqual x < 1 := gammaSEqual_lt_one_of_pos hx0 hπ
  have hcosh : 0 < cosh δ := cosh_pos δ
  have hratio := gammaRapidity_ratio (x := x) (δ := δ)
  have htanh0 : 0 ≤ tanh δ := by
    rw [tanh_eq_sinh_div_cosh]
    exact div_nonneg (sinh_nonneg_iff.mpr hδ) hcosh.le
  have hle : gammaRapidity x δ / cosh δ ≤ gammaSEqual x := by
    rw [hratio]
    have hsub : 0 ≤ tanh δ * sigmaEqual x := mul_nonneg htanh0 hσ.le
    linarith
  have hγlt : gammaRapidity x δ < cosh δ := by
    have hdiv : gammaRapidity x δ / cosh δ < 1 := lt_of_le_of_lt hle hγs
    rwa [div_lt_one hcosh] at hdiv
  have hdiff : cos x - sin x > 0 := cos_sub_sin_pos hx0.le hx
  have hfloor : gammaSEqual x - sigmaEqual x = exp x * (cos x - sin x) := gamma_sub_sigma x
  have hstrict : gammaSEqual x - sigmaEqual x < gammaRapidity x δ / cosh δ := by
    rw [hratio]
    have hgap : sigmaEqual x * (1 - tanh δ) =
        (gammaSEqual x - tanh δ * sigmaEqual x) - (gammaSEqual x - sigmaEqual x) := by ring
    have hpos : 0 < sigmaEqual x * (1 - tanh δ) := by
      have ht : tanh δ < 1 := tanh_lt_one δ
      positivity
    linarith
  have hfloor_pos : 0 < gammaSEqual x - sigmaEqual x := by
    rw [hfloor]
    positivity
  have hγpos : 0 < gammaRapidity x δ := by
    have hquot : 0 < gammaRapidity x δ / cosh δ := lt_trans hfloor_pos hstrict
    have hmul : 0 < gammaRapidity x δ / cosh δ * cosh δ := mul_pos hquot hcosh
    rwa [div_mul_cancel₀ _ hcosh.ne'] at hmul
  refine ⟨hγlt, ?_⟩
  have hbound : cosh δ / gammaRapidity x δ <
      1 / (gammaSEqual x - sigmaEqual x) := by
    rw [div_lt_div_iff₀ hγpos hfloor_pos]
    have hleft : cosh δ * (gammaSEqual x - sigmaEqual x) <
        cosh δ * (gammaRapidity x δ / cosh δ) :=
      mul_lt_mul_of_pos_left hstrict hcosh
    have hrew : cosh δ * (gammaRapidity x δ / cosh δ) = gammaRapidity x δ := by
      field_simp [hcosh.ne']
    linarith
  have hinv : 1 / (gammaSEqual x - sigmaEqual x) = exp (-x) / (cos x - sin x) := by
    rw [hfloor]
    field_simp [hdiff.ne', (exp_pos x).ne']
    rw [← exp_add]
    simp
  linarith

/-! ### A concrete phase -/

private lemma cos_quadratic_lower {x : ℝ} (hx : 0 ≤ x) : 1 - x ^ 2 / 2 ≤ cos x := by
  rcases eq_or_lt_of_le hx with rfl | hxpos
  · simp
  · let f : ℝ → ℝ := fun y => cos y - 1 + y ^ 2 / 2
    let df : ℝ → ℝ := fun y => y - sin y
    have hder : ∀ y, HasDerivAt f (df y) y := by
      intro y
      have hpow : HasDerivAt (fun z : ℝ => z ^ 2) (2 * y) y := by
        simpa using hasDerivAt_pow 2 y
      have h := ((Real.hasDerivAt_cos y).sub (hasDerivAt_const y (1 : ℝ))).add
        (hpow.div_const 2)
      refine h.congr_deriv ?_
      unfold df
      ring
    have hcont : Continuous f := by
      unfold f
      exact (continuous_cos.sub continuous_const).add ((continuous_id.pow 2).div_const 2)
    obtain ⟨c, hc, hslope⟩ :=
      exists_hasDerivAt_eq_slope f df hxpos hcont.continuousOn (fun z _ => hder z)
    have hf0 : f 0 = 0 := by unfold f; simp
    rw [hf0, sub_zero, sub_zero] at hslope
    have hdf : 0 ≤ df c := by
      unfold df
      have hsin : sin c ≤ c := sin_le hc.1.le
      linarith
    have hquot : 0 ≤ f x / x := by
      rw [← hslope]
      exact hdf
    have hmul : 0 ≤ f x / x * x := mul_nonneg hquot hxpos.le
    rw [div_mul_cancel₀ _ hxpos.ne'] at hmul
    unfold f at hmul
    linarith

private lemma exp_neg_quadratic {x : ℝ} (hx : 0 ≤ x) :
    exp (-x) ≤ 1 - x + x ^ 2 / 2 := by
  rcases eq_or_lt_of_le hx with rfl | hxpos
  · simp
  · let f : ℝ → ℝ := fun y => 1 - y + y ^ 2 / 2 - (exp ∘ Neg.neg) y
    let df : ℝ → ℝ := fun y => -1 + y - exp (-y) * -1
    have hder : ∀ y, HasDerivAt f (df y) y := by
      intro y
      have hpow : HasDerivAt (fun z : ℝ => z ^ 2) (2 * y) y := by
        simpa using hasDerivAt_pow 2 y
      have hexp := (Real.hasDerivAt_exp (-y)).comp y (hasDerivAt_neg y)
      have h := (((hasDerivAt_const y (1 : ℝ)).sub (hasDerivAt_id y)).add
        (hpow.div_const 2)).sub hexp
      refine h.congr_deriv ?_
      unfold df
      ring
    have hcont : Continuous f := by
      unfold f
      exact ((continuous_const.sub continuous_id).add ((continuous_id.pow 2).div_const 2)).sub
        (continuous_exp.comp continuous_neg)
    obtain ⟨c, hc, hslope⟩ :=
      exists_hasDerivAt_eq_slope f df hxpos hcont.continuousOn (fun z _ => hder z)
    have hf0 : f 0 = 0 := by unfold f; simp
    rw [hf0, sub_zero, sub_zero] at hslope
    have hdf : 0 ≤ df c := by
      unfold df
      have hexp := add_one_le_exp (-c)
      linarith
    have hquot : 0 ≤ f x / x := by
      rw [← hslope]
      exact hdf
    have hmul : 0 ≤ f x / x * x := mul_nonneg hquot hxpos.le
    rw [div_mul_cancel₀ _ hxpos.ne'] at hmul
    unfold f at hmul
    simp only [Function.comp_apply] at hmul
    linarith

private theorem phase_excess_bound {x : ℝ} (hx0 : 0 < x) (hx : x ≤ 7 / 100) :
    exp (-x) / (cos x - sin x) - 1 < 6 / 1000 := by
  have hxπ : x < π / 4 := by
    linarith [pi_gt_three, hx]
  have hdiff : 0 < cos x - sin x := cos_sub_sin_pos hx0.le hxπ
  have hcos := cos_quadratic_lower hx0.le
  have hsin : sin x ≤ x := sin_le hx0.le
  have hden_le : 1 - x - x ^ 2 / 2 ≤ cos x - sin x := by linarith
  have hden_pos : 0 < 1 - x - x ^ 2 / 2 := by
    have hx2 : x ^ 2 ≤ (7 / 100) ^ 2 := (sq_le_sq₀ hx0.le (by norm_num)).2 hx
    have hsq : (7 / 100) ^ 2 = (49 : ℝ) / 10000 := by norm_num
    nlinarith [hx, hx2, hsq]
  have hnum := exp_neg_quadratic hx0.le
  have hnum_pos : 0 ≤ 1 - x + x ^ 2 / 2 := by
    have : 0 ≤ x ^ 2 / 2 := by positivity
    linarith
  have hfrac : exp (-x) / (cos x - sin x) ≤
      (1 - x + x ^ 2 / 2) / (1 - x - x ^ 2 / 2) := by
    rw [div_le_div_iff₀ hdiff hden_pos]
    have hleft : exp (-x) * (1 - x - x ^ 2 / 2) ≤
        (1 - x + x ^ 2 / 2) * (1 - x - x ^ 2 / 2) :=
      mul_le_mul_of_nonneg_right hnum hden_pos.le
    have hright : (1 - x + x ^ 2 / 2) * (1 - x - x ^ 2 / 2) ≤
        (1 - x + x ^ 2 / 2) * (cos x - sin x) :=
      mul_le_mul_of_nonneg_left hden_le hnum_pos
    linarith
  have hpoly : (1 - x + x ^ 2 / 2) / (1 - x - x ^ 2 / 2) - 1 =
      x ^ 2 / (1 - x - x ^ 2 / 2) := by
    rw [div_sub_one hden_pos.ne']
    congr 1
    ring
  have hxsq : x ^ 2 ≤ (7 / 100) ^ 2 := (sq_le_sq₀ hx0.le (by norm_num)).2 hx
  have hden_ge : (18551 : ℝ) / 20000 ≤ 1 - x - x ^ 2 / 2 := by
    have hx2 : x ^ 2 / 2 ≤ (49 : ℝ) / 20000 := by
      have hsq : x ^ 2 ≤ (49 : ℝ) / 10000 := by
        have : (7 / 100) ^ 2 = (49 : ℝ) / 10000 := by norm_num
        linarith
      linarith
    have hxle : x ≤ 7 / 100 := hx
    linarith
  have hquot : x ^ 2 / (1 - x - x ^ 2 / 2) ≤
      ((49 : ℝ) / 10000) / ((18551 : ℝ) / 20000) := by
    have hx2 : x ^ 2 ≤ (49 : ℝ) / 10000 := by
      have : (7 / 100) ^ 2 = (49 : ℝ) / 10000 := by norm_num
      linarith
    rw [div_le_div_iff₀ hden_pos (by norm_num)]
    have hleft : x ^ 2 * ((18551 : ℝ) / 20000) ≤ ((49 : ℝ) / 10000) * ((18551 : ℝ) / 20000) :=
      mul_le_mul_of_nonneg_right hx2 (by norm_num)
    have hright : ((49 : ℝ) / 10000) * ((18551 : ℝ) / 20000) ≤
        ((49 : ℝ) / 10000) * (1 - x - x ^ 2 / 2) :=
      mul_le_mul_of_nonneg_left hden_ge (by norm_num)
    linarith
  have hsmall : ((49 : ℝ) / 10000) / ((18551 : ℝ) / 20000) < 6 / 1000 := by
    norm_num
  have hchain : exp (-x) / (cos x - sin x) - 1 ≤
      x ^ 2 / (1 - x - x ^ 2 / 2) := by
    rw [← hpoly]
    linarith
  have : x ^ 2 / (1 - x - x ^ 2 / 2) < 6 / 1000 := lt_of_le_of_lt hquot hsmall
  linarith

theorem farField_excess_small {x δ : ℝ} (hx0 : 0 < x) (hx : x ≤ 7 / 100) (hδ : 0 ≤ δ) :
    cosh δ / gammaRapidity x δ - 1 < 6 / 1000 := by
  have hxπ : x < π / 4 := by
    linarith [pi_gt_three, hx]
  have hfrac := (farField_excess hx0 hxπ hδ).2
  have hbound := phase_excess_bound hx0 hx
  linarith

/-! ### Laboratory energies -/

theorem oneMeV_halfAngle {φ : ℝ}
    (h : cosh φ = 1 + (1 : ℝ) / (939565 / 1000)) :
    1000266 / 1000000 < cosh (φ / 2) ∧ cosh (φ / 2) < 1000267 / 1000000 := by
  have hsq : cosh (φ / 2) ^ 2 = (940065 : ℝ) / 939565 := by
    rw [cosh_half_sq, h]
    norm_num
  have hpos : 0 < cosh (φ / 2) := cosh_pos _
  constructor
  · rw [← sq_lt_sq₀ (by norm_num) hpos.le, hsq]
    norm_num
  · rw [← sq_lt_sq₀ hpos.le (by norm_num), hsq]
    norm_num

theorem fourteenMeV_halfAngle {φ : ℝ}
    (h : cosh φ = 1 + (14 : ℝ) / (939565 / 1000)) :
    1003718 / 1000000 < cosh (φ / 2) ∧ cosh (φ / 2) < 1003719 / 1000000 := by
  have hsq : cosh (φ / 2) ^ 2 = (946565 : ℝ) / 939565 := by
    rw [cosh_half_sq, h]
    norm_num
  have hpos : 0 < cosh (φ / 2) := cosh_pos _
  constructor
  · rw [← sq_lt_sq₀ (by norm_num) hpos.le, hsq]
    norm_num
  · rw [← sq_lt_sq₀ hpos.le (by norm_num), hsq]
    norm_num

/-- From `1` MeV to `14` MeV the far-field coefficient `1/cosh(φ/2)` falls by
a fraction strictly less than `4/1000`. -/
theorem farField_strength_drop {c₁ c₁₄ : ℝ}
    (h₁ : (1000266 : ℝ) / 1000000 < c₁)
    (h₁₄lo : (1003718 : ℝ) / 1000000 < c₁₄)
    (h₁₄ : c₁₄ < (1003719 : ℝ) / 1000000) :
    (c₁₄ - c₁) / c₁₄ < 4 / 1000 := by
  have hpos : 0 < c₁₄ := lt_trans (by norm_num) h₁₄lo
  have hcmp : (996 / 1000) * c₁₄ < c₁ := by
    have hstep : (996 / 1000) * c₁₄ < (996 / 1000) * ((1003719 : ℝ) / 1000000) :=
      mul_lt_mul_of_pos_left h₁₄ (by norm_num)
    have hnum : (996 / 1000) * ((1003719 : ℝ) / 1000000) < 1000266 / 1000000 := by
      norm_num
    linarith
  have hsub : c₁₄ - c₁ < (4 / 1000) * c₁₄ := by linarith
  rwa [div_lt_iff₀ hpos]

/-! ### A nucleus outside the wall pulls inward -/

private lemma sum_lt_zero {ι : Type*} {s : Finset ι} {f : ι → ℝ}
    (hne : s.Nonempty) (hf : ∀ i ∈ s, f i < 0) : ∑ i ∈ s, f i < 0 := by
  classical
  obtain ⟨i, hi⟩ := hne
  have hsplit := Finset.add_sum_erase s f hi
  have hrest : ∑ j ∈ s.erase i, f j ≤ ∑ j ∈ s.erase i, (0 : ℝ) :=
    Finset.sum_le_sum fun j hj => (hf j (Finset.mem_of_mem_erase hj)).le
  simp only [Finset.sum_const_zero] at hrest
  linarith [hf i hi, hsplit]

private theorem separation_outside_wall
    {E : Type*} [NormedAddCommGroup E] {n p C : E} {R w : ℝ}
    (hR : ‖p - C‖ ≤ R) (hn : R + w ≤ ‖n - C‖) :
    w ≤ ‖n - p‖ := by
  have heq : (n - p) + (p - C) = n - C := sub_add_sub_cancel n p C
  have htri : ‖n - C‖ ≤ ‖n - p‖ + ‖p - C‖ := by
    simpa [heq] using norm_add_le (n - p) (p - C)
  linarith

private theorem radial_gap_pos
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {n p C : E} {R : ℝ}
    (hR : ‖p - C‖ ≤ R) (hr : R < ‖n - C‖) :
    0 < ‖n - C‖ ^ 2 - inner ℝ (p - C) (n - C) := by
  have hdot : inner ℝ (p - C) (n - C) ≤ ‖p - C‖ * ‖n - C‖ := real_inner_le_norm _ _
  have hle : inner ℝ (p - C) (n - C) ≤ R * ‖n - C‖ := by
    have hmul : ‖p - C‖ * ‖n - C‖ ≤ R * ‖n - C‖ :=
      mul_le_mul_of_nonneg_right hR (norm_nonneg _)
    linarith
  have hpos : 0 < ‖n - C‖ * (‖n - C‖ - R) := by
    have hR0 : 0 ≤ R := le_trans (norm_nonneg (p - C)) hR
    have hnorm : 0 < ‖n - C‖ := by linarith
    positivity
  have hrew : ‖n - C‖ * (‖n - C‖ - R) = ‖n - C‖ ^ 2 - R * ‖n - C‖ := by ring
  linarith

/-- The force on the neutron from one nucleon, along the separation. A positive
coefficient is an attraction. -/
noncomputable def neutronPairForce
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (κ ℓ δ : ℝ) (n p : E) : E :=
  - (κ / (gammaRapidity (ℓ / (2 * ‖n - p‖)) δ * ‖n - p‖ ^ 3)) • (n - p)

theorem neutron_force_inward
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {ι : Type*} {s : Finset ι} {n C : E} {p : ι → E} {κ ℓ δ R : ℝ}
    (hκ : 0 < κ) (hℓ : 0 < ℓ) (_hδ : 0 ≤ δ)
    (hball : ∀ i ∈ s, ‖p i - C‖ ≤ R)
    (hn : R + 2 * ℓ / π ≤ ‖n - C‖)
    (hne : s.Nonempty) :
    inner ℝ (∑ i ∈ s, neutronPairForce κ ℓ δ n (p i)) (n - C) < 0 := by
  have hπ : 0 < π := pi_pos
  have hwall : 0 < 2 * ℓ / π := by positivity
  have hr : R < ‖n - C‖ := by linarith
  rw [sum_inner]
  refine sum_lt_zero hne ?_
  intro i hi
  have hsep : 2 * ℓ / π ≤ ‖n - p i‖ :=
    separation_outside_wall (hball i hi) hn
  have hspos : 0 < ‖n - p i‖ := lt_of_lt_of_le hwall hsep
  have hphase : ℓ / (2 * ‖n - p i‖) ≤ π / 4 := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * ‖n - p i‖)]
    have hmul : (π / 4) * (2 * ‖n - p i‖) = π * ‖n - p i‖ / 2 := by ring
    rw [hmul]
    have hclear : ℓ * 2 ≤ π * ‖n - p i‖ := by
      have hstep : (2 * ℓ / π) * π ≤ ‖n - p i‖ * π :=
        mul_le_mul_of_nonneg_right hsep hπ.le
      have hrew : (2 * ℓ / π) * π = 2 * ℓ := by field_simp
      linarith
    linarith
  have hphase0 : 0 ≤ ℓ / (2 * ‖n - p i‖) := by positivity
  have hγ : 0 < gammaRapidity (ℓ / (2 * ‖n - p i‖)) δ :=
    gammaRapidity_pos_of_le_quarter hphase0 hphase
  have hc : 0 < κ / (gammaRapidity (ℓ / (2 * ‖n - p i‖)) δ * ‖n - p i‖ ^ 3) := by
    refine div_pos hκ ?_
    exact mul_pos hγ (pow_pos hspos 3)
  have hgap := radial_gap_pos (hball i hi) hr
  have hdot : 0 < inner ℝ (n - p i) (n - C) := by
    have hsplit : (n - C) - (p i - C) = n - p i := sub_sub_sub_cancel_right n (p i) C
    rw [← hsplit, inner_sub_left]
    simpa using hgap
  unfold neutronPairForce
  rw [real_inner_smul_left]
  have hneg : -(κ / (gammaRapidity (ℓ / (2 * ‖n - p i‖)) δ * ‖n - p i‖ ^ 3)) *
      inner ℝ (n - p i) (n - C) < 0 := by
    nlinarith [hc, hdot]
  simpa using hneg

end Gravity

end DstDiophantine
