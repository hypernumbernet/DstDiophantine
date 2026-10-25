import DstDiophantine.Gravity.StrongChannel
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Neutron scattering outside the rapidity wall

## Paper boundary (do **not** claim)

The prefactor `κ`, a scattering amplitude inside the wall, and the value in
femtometres of a measured scattering length are **not** derived. The neutron
rest energy `939.565` MeV is an external input. The rapidity is the
nonnegative parameter of the pair. Abundances and tabulated lengths are
external inputs.

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

If the nucleons lie in a ball of radius `R` and the neutron lies at a
distance `D > R` from the centre, and if the phase at distance `D - R` is
at most `7/100`, the net force differs from the point field of strength
`A κ / cosh(φ/2)` by a fraction of that field strictly less than
`6/1000 + (1 + 6/1000) · 2(R/D)/(1 - R/D)³`. When `D ≥ 50 R` the fraction
is strictly less than `1/20`.

The fixed-angle cross section of an inverse-square field of that strength
scales as `1/(T² (1 + T/(2mc²)))`. The angular law is the classical
Rutherford law and is not re-derived. From `1` MeV to `14` MeV the ratio of
those prefactors lies strictly between `197` and `198`. With the evaluated
gold totals `5.755` b and `5.295` b, the later total is strictly above nine
tenths of the earlier one.

At vanishing phase the interference factor with rapidity `δ` and relative
dual phase `ε` is `cosh δ · cos ε − sinh δ · sin ε`. It reduces to the
rapidity factor at `ε = 0` and to the dual-excitation factor at `δ = 0`.
For `δ ≥ 0` that factor is at least `1` when `ε = 0`. It is negative when
`ε` lies past the right angle. It stays positive when `ε` lies short of the
right angle and `δ` does not exceed the gap. At zero rapidity it can lie
strictly between `0` and `1/M` for every `M > 0`, and likewise just below
zero. The mean-square fluctuation of a weighted sample is nonnegative and
vanishes exactly when every nucleus that occurs has the same coefficient.
Opposite signs put the mean strictly between the two coefficients, and
strictly below the larger magnitude. The tabulated hydrogen and vanadium
incoherent cross sections exceed their coherent ones by more than `45` and
`200`. The abundance-weighted mean of the five stable titanium lengths lies
strictly between `-3.44` and `-3.43` fm.
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

/-! ### The point field -/

/-- Inverse-square field `x / ‖x‖³`. -/
noncomputable def coulombField {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x : E) : E :=
  (‖x‖ ^ 3)⁻¹ • x

/-- Point-nucleus force of strength `α` for `A` nucleons at `C`. -/
noncomputable def pointNeutronForce
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (α A : ℝ) (n C : E) : E :=
  - (A * α) • coulombField (n - C)

private theorem sq_rpow_inv_three {r : ℝ} (hr : 0 < r) :
    (r ^ 2) ^ (-3 / 2 : ℝ) = (r ^ 3)⁻¹ := by
  have hr0 : 0 ≤ r := hr.le
  calc (r ^ 2) ^ (-3 / 2 : ℝ)
      = (r ^ ((2 : ℕ) : ℝ)) ^ (-3 / 2 : ℝ) := by rw [← Real.rpow_natCast]
    _ = r ^ (((2 : ℕ) : ℝ) * (-3 / 2)) := (Real.rpow_mul hr0 _ _).symm
    _ = r ^ (-3 : ℝ) := by
      congr 1
      norm_num
    _ = (r ^ (3 : ℝ))⁻¹ := Real.rpow_neg hr0 _
    _ = (r ^ 3)⁻¹ := congrArg Inv.inv (Real.rpow_natCast r 3)

private theorem sq_rpow_inv_five {r : ℝ} (hr : 0 < r) :
    (r ^ 2) ^ (-5 / 2 : ℝ) = (r ^ 5)⁻¹ := by
  have hr0 : 0 ≤ r := hr.le
  calc (r ^ 2) ^ (-5 / 2 : ℝ)
      = (r ^ ((2 : ℕ) : ℝ)) ^ (-5 / 2 : ℝ) := by rw [← Real.rpow_natCast]
    _ = r ^ (((2 : ℕ) : ℝ) * (-5 / 2)) := (Real.rpow_mul hr0 _ _).symm
    _ = r ^ (-5 : ℝ) := by
      congr 1
      norm_num
    _ = (r ^ (5 : ℝ))⁻¹ := Real.rpow_neg hr0 _
    _ = (r ^ 5)⁻¹ := congrArg Inv.inv (Real.rpow_natCast r 5)

private theorem coulomb_velocity_bound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x h : E) (hx : x ≠ 0) :
    ‖(-(‖x‖ ^ 3)⁻¹) • h + ((3 * inner ℝ x h) * (‖x‖ ^ 5)⁻¹) • x‖
      ≤ 2 * ‖h‖ / ‖x‖ ^ 3 := by
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  set r : ℝ := ‖x‖
  set a : ℝ := inner ℝ x h
  set c1 : ℝ := -(r ^ 3)⁻¹
  set c2 : ℝ := 3 * a * (r ^ 5)⁻¹
  set w : E := c1 • h + c2 • x
  have hinner : inner ℝ w w =
      c1 ^ 2 * ‖h‖ ^ 2 + 2 * c1 * c2 * a + c2 ^ 2 * r ^ 2 := by
    simp only [w, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right]
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
    rw [show inner ℝ h x = inner ℝ x h from (real_inner_comm x h)]
    simp [a, r]
    ring_nf
  have hnorm : ‖w‖ ^ 2 = ‖h‖ ^ 2 / r ^ 6 + 3 * a ^ 2 / r ^ 8 := by
    rw [← real_inner_self_eq_norm_sq, hinner]
    simp only [c1, c2]
    field_simp [hr.ne']
    ring
  have ha : a ^ 2 ≤ r ^ 2 * ‖h‖ ^ 2 := by
    have habs : |a| ≤ r * ‖h‖ := by
      simpa [a, r] using abs_real_inner_le_norm x h
    have hnonneg : 0 ≤ r * ‖h‖ := by positivity
    have hsq : |a| ^ 2 ≤ (r * ‖h‖) ^ 2 := (sq_le_sq₀ (abs_nonneg a) hnonneg).mpr habs
    rw [sq_abs] at hsq
    have hexp : (r * ‖h‖) ^ 2 = r ^ 2 * ‖h‖ ^ 2 := by ring
    linarith
  have hfour : ‖w‖ ^ 2 ≤ 4 * ‖h‖ ^ 2 / r ^ 6 := by
    rw [hnorm]
    have hden8 : 0 < r ^ 8 := by positivity
    have h3 : 3 * a ^ 2 / r ^ 8 ≤ 3 * (r ^ 2 * ‖h‖ ^ 2) / r ^ 8 :=
      div_le_div_of_nonneg_right (by nlinarith : 3 * a ^ 2 ≤ 3 * (r ^ 2 * ‖h‖ ^ 2)) hden8.le
    have hrew : 3 * (r ^ 2 * ‖h‖ ^ 2) / r ^ 8 = 3 * ‖h‖ ^ 2 / r ^ 6 := by
      field_simp [hr.ne']
    have h3' : 3 * a ^ 2 / r ^ 8 ≤ 3 * ‖h‖ ^ 2 / r ^ 6 := h3.trans (le_of_eq hrew)
    have hsum : ‖h‖ ^ 2 / r ^ 6 + 3 * a ^ 2 / r ^ 8 ≤
        ‖h‖ ^ 2 / r ^ 6 + 3 * ‖h‖ ^ 2 / r ^ 6 := by linarith
    have hadd : ‖h‖ ^ 2 / r ^ 6 + 3 * ‖h‖ ^ 2 / r ^ 6 = 4 * ‖h‖ ^ 2 / r ^ 6 := by ring
    linarith
  have htarget : (2 * ‖h‖ / r ^ 3) ^ 2 = 4 * ‖h‖ ^ 2 / r ^ 6 := by
    field_simp [hr.ne']
    ring
  have hsqle : ‖w‖ ^ 2 ≤ (2 * ‖h‖ / r ^ 3) ^ 2 := by linarith
  have hw0 : 0 ≤ ‖w‖ := norm_nonneg _
  have hb0 : 0 ≤ 2 * ‖h‖ / r ^ 3 := by positivity
  simpa [w, c1, c2, a, r] using (sq_le_sq₀ hw0 hb0).mp hsqle

private theorem path_outside_ball
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {u v : E} {R t : ℝ} (hv : ‖v‖ ≤ R) (_hD : R < ‖u‖) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ‖u‖ - R ≤ ‖u - t • v‖ := by
  have htri : ‖u‖ ≤ ‖u - t • v‖ + ‖t • v‖ := by
    have heq : (u - t • v) + t • v = u := by simp
    simpa [heq] using norm_add_le (u - t • v) (t • v)
  have hsmul : ‖t • v‖ = t * ‖v‖ := by
    rw [norm_smul, Real.norm_of_nonneg ht0]
  have hle : t * ‖v‖ ≤ R := by
    have hv0 : 0 ≤ ‖v‖ := norm_nonneg _
    nlinarith
  linarith

private theorem hasDerivAt_coulomb_path
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {u v : E} {t : ℝ} (hpos : 0 < ‖u - t • v‖) :
    HasDerivAt (fun s => coulombField (u - s • v))
      ((-(‖u - t • v‖ ^ 3)⁻¹) • v +
        ((3 * inner ℝ (u - t • v) v) * (‖u - t • v‖ ^ 5)⁻¹) • (u - t • v)) t := by
  set x : E := u - t • v
  have hpath : HasDerivAt (fun s : ℝ => u - s • v) (-v) t := by
    have hlin : HasDerivAt (fun s : ℝ => s • v) v t := by
      simpa using (hasDerivAt_id t).smul_const v
    convert (hasDerivAt_const t u).sub hlin using 1
    simp
  have hsq := hpath.norm_sq
  have hbase : (‖x‖ ^ 2) ≠ 0 := by
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr (norm_pos_iff.mp hpos))
  have hrpow := hsq.rpow_const (p := (-3 / 2 : ℝ)) (Or.inl hbase)
  have hscalar : HasDerivAt (fun s => (‖u - s • v‖ ^ 2) ^ (-3 / 2 : ℝ))
      (3 * inner ℝ x v * (‖x‖ ^ 2) ^ (-5 / 2 : ℝ)) t := by
    refine hrpow.congr_deriv ?_
    have hinner : inner ℝ x (-v) = - inner ℝ x v := by simp
    rw [hinner]
    ring_nf
    simp [x]
  have hprod := hscalar.smul hpath
  have hagree : (fun s => (‖u - s • v‖ ^ 2) ^ (-3 / 2 : ℝ) • (u - s • v)) =ᶠ[nhds t]
      fun s => coulombField (u - s • v) := by
    have hcont : ContinuousAt (fun s : ℝ => ‖u - s • v‖) t :=
      (continuous_const.sub (continuous_id.smul continuous_const)).continuousAt.norm
    filter_upwards [hcont.eventually (eventually_gt_nhds hpos)] with s hs
    have h3s := sq_rpow_inv_three hs
    simp [coulombField, h3s]
  have hshifted := hprod.congr_of_eventuallyEq hagree.symm
  refine hshifted.congr_deriv ?_
  have h3 := sq_rpow_inv_three hpos
  have h5 := sq_rpow_inv_five hpos
  simp only [x] at h3 h5 ⊢
  rw [h3, h5]
  simp [smul_neg, neg_smul]

private theorem coulombField_distortion
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {u v : E} {R : ℝ} (hv : ‖v‖ ≤ R) (hD : R < ‖u‖) :
    ‖coulombField (u - v) - coulombField u‖ ≤ 2 * R / (‖u‖ - R) ^ 3 := by
  let f : ℝ → E := fun t => coulombField (u - t • v)
  let f' : ℝ → E := fun t =>
    (-(‖u - t • v‖ ^ 3)⁻¹) • v +
      ((3 * inner ℝ (u - t • v) v) * (‖u - t • v‖ ^ 5)⁻¹) • (u - t • v)
  have hpos : ∀ t ∈ Icc (0 : ℝ) 1, 0 < ‖u - t • v‖ := by
    intro t ht
    have hge := path_outside_ball hv hD ht.1 ht.2
    linarith
  have hf : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt f (f' t) (Icc (0 : ℝ) 1) t := by
    intro t ht
    exact (hasDerivAt_coulomb_path (hpos t ht)).hasDerivWithinAt
  set C : ℝ := 2 * R / (‖u‖ - R) ^ 3
  have hbound : ∀ t ∈ Ico (0 : ℝ) 1, ‖f' t‖ ≤ C := by
    intro t ht
    have htI : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1, ht.2.le⟩
    have hvel := coulomb_velocity_bound (u - t • v) v (norm_pos_iff.mp (hpos t htI))
    have hge := path_outside_ball hv hD ht.1 ht.2.le
    have hrpos : 0 < ‖u - t • v‖ := hpos t htI
    have hden : 0 < ‖u‖ - R := by linarith
    have hstep : 2 * ‖v‖ / ‖u - t • v‖ ^ 3 ≤ 2 * R / (‖u‖ - R) ^ 3 := by
      have hvR : 2 * ‖v‖ ≤ 2 * R := by linarith
      have hpow : (‖u‖ - R) ^ 3 ≤ ‖u - t • v‖ ^ 3 := by
        have hmono := pow_le_pow_left₀ hden.le hge 3
        exact hmono
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have hleft : 2 * ‖v‖ * (‖u‖ - R) ^ 3 ≤ 2 * R * (‖u‖ - R) ^ 3 := by
        have hnn : 0 ≤ (‖u‖ - R) ^ 3 := by positivity
        nlinarith
      have hright : 2 * R * (‖u‖ - R) ^ 3 ≤ 2 * R * ‖u - t • v‖ ^ 3 := by
        have hnn : 0 ≤ 2 * R := by
          have : 0 ≤ ‖v‖ := norm_nonneg _
          linarith
        nlinarith
      linarith
    simpa [f', C] using hvel.trans hstep
  have hmv := norm_image_sub_le_of_norm_deriv_le_segment_01' hf hbound
  simpa [f, C] using hmv

theorem norm_coulombField {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {x : E} (hx : x ≠ 0) : ‖coulombField x‖ = 1 / ‖x‖ ^ 2 := by
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  unfold coulombField
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (by positivity : (0 : ℝ) ≤ ‖x‖ ^ 3))]
  field_simp [hr.ne']

private theorem halfAngle_ratio_bounds {x δ : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 7 / 100) (hδ : 0 ≤ δ) :
    0 < gammaRapidity x δ ∧
      1 ≤ cosh δ / gammaRapidity x δ ∧
        cosh δ / gammaRapidity x δ < 1 + 6 / 1000 := by
  have hπ : x ≤ π / 4 := by linarith [pi_gt_three, hx]
  have hγ : 0 < gammaRapidity x δ := gammaRapidity_pos_of_le_quarter hx0 hπ
  suffices hpair : 1 ≤ cosh δ / gammaRapidity x δ ∧
      cosh δ / gammaRapidity x δ < 1 + 6 / 1000 by
    exact ⟨hγ, hpair.1, hpair.2⟩
  rcases eq_or_lt_of_le hx0 with rfl | hxpos
  · have h0 : gammaRapidity 0 δ = cosh δ := gammaRapidity_zero_phase δ
    have hc : 0 < cosh δ := cosh_pos δ
    refine ⟨?_, ?_⟩
    · rw [h0, div_self hc.ne']
    · rw [h0, div_self hc.ne']
      norm_num
  · have hxπ : x < π / 4 := by linarith [pi_gt_three, hx]
    have hlt : gammaRapidity x δ < cosh δ := (farField_excess hxpos hxπ hδ).1
    have hfrac : cosh δ / gammaRapidity x δ - 1 < 6 / 1000 :=
      farField_excess_small hxpos hx hδ
    exact ⟨(one_le_div hγ).mpr hlt.le, by linarith⟩

private theorem phase_le_of_ball
    {E : Type*} [NormedAddCommGroup E] {n p C : E} {ℓ R : ℝ}
    (hℓ : 0 < ℓ) (hball : ‖p - C‖ ≤ R) (hD : R < ‖n - C‖)
    (hphase : ℓ / (2 * (‖n - C‖ - R)) ≤ 7 / 100) :
    0 ≤ ℓ / (2 * ‖n - p‖) ∧ ℓ / (2 * ‖n - p‖) ≤ 7 / 100 := by
  have hsep : ‖n - C‖ - R ≤ ‖n - p‖ :=
    separation_outside_wall hball (by linarith : R + (‖n - C‖ - R) ≤ ‖n - C‖)
  have hspos : 0 < ‖n - p‖ := by
    have hgap : 0 < ‖n - C‖ - R := by linarith
    linarith
  have hden : 0 < 2 * (‖n - C‖ - R) := by linarith
  have hle : ℓ / (2 * ‖n - p‖) ≤ ℓ / (2 * (‖n - C‖ - R)) := by
    refine div_le_div_of_nonneg_left hℓ.le hden ?_
    linarith
  exact ⟨by positivity, hle.trans hphase⟩

/-- At phase at most `7/100`, the net force differs from the point field of
strength `A κ / cosh δ` by a fraction of that field strictly less than
`6/1000 + (1 + 6/1000) · 2(R/D)/(1 - R/D)³`. -/
theorem neutron_force_near_point
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {ι : Type*} {s : Finset ι} {n C : E} {p : ι → E} {κ ℓ δ R : ℝ}
    (hκ : 0 < κ) (hℓ : 0 < ℓ) (hδ : 0 ≤ δ) (hR : 0 ≤ R)
    (hball : ∀ i ∈ s, ‖p i - C‖ ≤ R) (hD : R < ‖n - C‖)
    (hphase : ℓ / (2 * (‖n - C‖ - R)) ≤ 7 / 100) (hne : s.Nonempty) :
    ‖(∑ i ∈ s, neutronPairForce κ ℓ δ n (p i)) -
        pointNeutronForce (κ / cosh δ) (s.card : ℝ) n C‖ <
      ‖pointNeutronForce (κ / cosh δ) (s.card : ℝ) n C‖ *
        (6 / 1000 + (1 + 6 / 1000) *
          (2 * (R / ‖n - C‖) / (1 - R / ‖n - C‖) ^ 3)) := by
  classical
  set D : ℝ := ‖n - C‖
  set α : ℝ := κ / cosh δ
  set A : ℝ := (s.card : ℝ)
  set ε : ℝ := 6 / 1000
  have hA : 0 < A := by
    have : 0 < s.card := Finset.card_pos.mpr hne
    exact Nat.cast_pos.mpr this
  have hcosh : 0 < cosh δ := cosh_pos δ
  have hα : 0 < α := div_pos hκ hcosh
  have hDpos : 0 < D := by linarith
  have hgap : 0 < D - R := by linarith
  have hCne : n - C ≠ 0 := by
    intro h0
    have : ‖n - C‖ = 0 := by simpa using congrArg norm h0
    linarith
  let β : ι → ℝ := fun i => cosh δ / gammaRapidity (ℓ / (2 * ‖n - p i‖)) δ
  let g : ι → E := fun i => coulombField (n - p i)
  let g0 : E := coulombField (n - C)
  have hβ : ∀ i ∈ s, 1 ≤ β i ∧ β i < 1 + ε := by
    intro i hi
    have hph := phase_le_of_ball hℓ (hball i hi) hD hphase
    have hb := halfAngle_ratio_bounds hph.1 hph.2 hδ
    exact ⟨hb.2.1, hb.2.2⟩
  have hpair : ∀ i ∈ s, neutronPairForce κ ℓ δ n (p i) = - (α * β i) • g i := by
    intro i hi
    have hph := phase_le_of_ball hℓ (hball i hi) hD hphase
    have hγ : 0 < gammaRapidity (ℓ / (2 * ‖n - p i‖)) δ :=
      (halfAngle_ratio_bounds hph.1 hph.2 hδ).1
    have hspos : 0 < ‖n - p i‖ := by
      have hsep := separation_outside_wall (hball i hi)
        (by linarith : R + (D - R) ≤ D)
      linarith
    simp only [neutronPairForce, g, coulombField, β, α]
    have hcoe : κ / (gammaRapidity (ℓ / (2 * ‖n - p i‖)) δ * ‖n - p i‖ ^ 3) =
        (κ / cosh δ) * (cosh δ / gammaRapidity (ℓ / (2 * ‖n - p i‖)) δ) *
          (‖n - p i‖ ^ 3)⁻¹ := by
      field_simp [hγ.ne', hcosh.ne', hspos.ne']
    rw [hcoe]
    simp [smul_smul, mul_comm]
  have hF : ∑ i ∈ s, neutronPairForce κ ℓ δ n (p i) = -α • ∑ i ∈ s, β i • g i := by
    have hrewrite : ∑ i ∈ s, neutronPairForce κ ℓ δ n (p i) =
        ∑ i ∈ s, (-α) • (β i • g i) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      rw [hpair i hi]
      simp [neg_smul, smul_smul]
    refine hrewrite.trans ?_
    simp [Finset.smul_sum]
  have hsplit : ∑ i ∈ s, β i • g i - A • g0 =
      ∑ i ∈ s, β i • (g i - g0) + (∑ i ∈ s, β i - A) • g0 := by
    have hterm : ∀ i ∈ s, β i • g i = β i • (g i - g0) + β i • g0 := by
      intro i _
      simp [smul_sub]
    have hsum : ∑ i ∈ s, β i • g i =
        ∑ i ∈ s, β i • (g i - g0) + ∑ i ∈ s, β i • g0 := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl hterm
    have hconst : ∑ i ∈ s, β i • g0 = (∑ i ∈ s, β i) • g0 :=
      (Finset.sum_smul (s := s) (f := β) (x := g0)).symm
    rw [hsum, hconst, sub_eq_add_neg, sub_eq_add_neg]
    simp [add_smul, neg_smul]
    abel
  set G : ℝ := 2 * R / (D - R) ^ 3
  have hG0 : 0 ≤ G := by
    unfold G
    positivity
  have hdiff : ∀ i ∈ s, ‖g i - g0‖ ≤ G := by
    intro i hi
    have hv : ‖p i - C‖ ≤ R := hball i hi
    have hdist := coulombField_distortion (u := n - C) (v := p i - C) hv hD
    simpa [g, g0, G, D, sub_sub_sub_cancel_right] using hdist
  have hsumβ_lt : ∑ i ∈ s, β i < A * (1 + ε) := by
    have hlt : ∑ i ∈ s, β i < ∑ _ ∈ s, (1 + ε) := by
      refine Finset.sum_lt_sum ?_ ?_
      · intro i hi
        exact (hβ i hi).2.le
      · obtain ⟨i, hi⟩ := hne
        exact ⟨i, hi, (hβ i hi).2⟩
    have hconst : ∑ _ ∈ s, (1 + ε) = A * (1 + ε) := by
      simp [Finset.sum_const, nsmul_eq_mul, A]
      ring
    exact hlt.trans_eq hconst
  have hsumβ_ge : A ≤ ∑ i ∈ s, β i := by
    have hle : ∑ _ ∈ s, (1 : ℝ) ≤ ∑ i ∈ s, β i := by
      refine Finset.sum_le_sum ?_
      intro i hi
      exact (hβ i hi).1
    simpa [Finset.sum_const, nsmul_eq_mul, A] using hle
  have hgeom : ‖∑ i ∈ s, β i • (g i - g0)‖ ≤ G * ∑ i ∈ s, β i := by
    refine (norm_sum_le _ _).trans ?_
    have hle : ∑ i ∈ s, ‖β i • (g i - g0)‖ ≤ ∑ i ∈ s, β i * G := by
      refine Finset.sum_le_sum ?_
      intro i hi
      rw [norm_smul, Real.norm_of_nonneg (by linarith [(hβ i hi).1] : 0 ≤ β i)]
      exact mul_le_mul_of_nonneg_left (hdiff i hi) (by linarith [(hβ i hi).1])
    have hconst : ∑ i ∈ s, β i * G = G * ∑ i ∈ s, β i := by
      simp [Finset.mul_sum, mul_comm]
    linarith
  have hscale : ‖(∑ i ∈ s, β i - A) • g0‖ < A * ε * ‖g0‖ := by
    have hg0 : 0 < ‖g0‖ := by
      have : ‖g0‖ = 1 / D ^ 2 := by simpa [g0, D] using norm_coulombField hCne
      rw [this]
      positivity
    rw [norm_smul, Real.norm_of_nonneg (sub_nonneg.mpr hsumβ_ge)]
    exact mul_lt_mul_of_pos_right (by linarith : ∑ i ∈ s, β i - A < A * ε) hg0
  have hstar : ‖pointNeutronForce α A n C‖ = A * α / D ^ 2 := by
    unfold pointNeutronForce
    have hnorm := norm_coulombField hCne
    rw [show ‖n - C‖ = D from rfl] at hnorm
    rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos (by positivity : 0 < A * α), hnorm]
    field_simp [hDpos.ne']
  have hgeom_abs : ‖∑ i ∈ s, β i • (g i - g0)‖ < A * (1 + ε) * G ∨ R = 0 := by
    rcases eq_or_lt_of_le hR with rfl | hRpos
    · exact Or.inr rfl
    · left
      have hGpos : 0 < G := by
        unfold G
        positivity
      have hstrict : G * ∑ i ∈ s, β i < A * (1 + ε) * G := by
        simpa [mul_comm, mul_left_comm, mul_assoc] using
          mul_lt_mul_of_pos_left hsumβ_lt hGpos
      exact lt_of_le_of_lt hgeom hstrict
  have hvec : ‖∑ i ∈ s, β i • g i - A • g0‖ < A * (ε / D ^ 2 + (1 + ε) * G) := by
    rw [hsplit]
    refine lt_of_le_of_lt (norm_add_le _ _) ?_
    have hg0norm : ‖g0‖ = 1 / D ^ 2 := by
      simpa [g0, D] using norm_coulombField hCne
    have hscale' : ‖(∑ i ∈ s, β i - A) • g0‖ < A * ε / D ^ 2 := by
      rw [hg0norm] at hscale
      have : A * ε * (1 / D ^ 2) = A * ε / D ^ 2 := by ring
      linarith
    rcases hgeom_abs with hlt | hR0
    · have hsumlt : ‖∑ i ∈ s, β i • (g i - g0)‖ + ‖(∑ i ∈ s, β i - A) • g0‖ <
          A * (1 + ε) * G + A * ε / D ^ 2 := add_lt_add hlt hscale'
      have heq : A * (1 + ε) * G + A * ε / D ^ 2 = A * (ε / D ^ 2 + (1 + ε) * G) := by ring
      exact hsumlt.trans_eq heq
    · have hGzero : G = 0 := by
        unfold G
        simp [hR0]
      have hzero : ‖∑ i ∈ s, β i • (g i - g0)‖ = 0 := by
        have hle0 : ‖∑ i ∈ s, β i • (g i - g0)‖ ≤ 0 := by
          simpa [hGzero] using hgeom
        exact le_antisymm hle0 (norm_nonneg _)
      rw [hzero, zero_add, hGzero]
      exact hscale'.trans_eq (by ring)
  have hforce : ‖(∑ i ∈ s, neutronPairForce κ ℓ δ n (p i)) - pointNeutronForce α A n C‖ =
      α * ‖∑ i ∈ s, β i • g i - A • g0‖ := by
    rw [hF]
    unfold pointNeutronForce
    have hsub : -α • ∑ i ∈ s, β i • g i - -(A * α) • g0 =
        (-α) • (∑ i ∈ s, β i • g i - A • g0) := by
      simp [smul_sub, smul_smul, mul_comm A α]
    rw [hsub, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos hα]
  have habs : ‖(∑ i ∈ s, neutronPairForce κ ℓ δ n (p i)) - pointNeutronForce α A n C‖ <
      α * A * (ε / D ^ 2 + (1 + ε) * G) := by
    rw [hforce]
    exact (mul_lt_mul_of_pos_left hvec hα).trans_eq (by ring)
  have htheta : G * D ^ 2 = 2 * (R / D) / (1 - R / D) ^ 3 := by
    unfold G
    have hfac : 1 - R / D = (D - R) / D := by
      field_simp [hDpos.ne']
    rw [hfac]
    field_simp [hDpos.ne', hgap.ne']
  have hmatch : α * A * (ε / D ^ 2 + (1 + ε) * G) =
      ‖pointNeutronForce α A n C‖ *
        (ε + (1 + ε) * (2 * (R / D) / (1 - R / D) ^ 3)) := by
    rw [hstar]
    calc α * A * (ε / D ^ 2 + (1 + ε) * G)
        = (A * α / D ^ 2) * (ε + (1 + ε) * (G * D ^ 2)) := by
          field_simp [hDpos.ne']
      _ = (A * α / D ^ 2) * (ε + (1 + ε) * (2 * (R / D) / (1 - R / D) ^ 3)) := by
          rw [htheta]
  have : ‖(∑ i ∈ s, neutronPairForce κ ℓ δ n (p i)) -
      pointNeutronForce (κ / cosh δ) (s.card : ℝ) n C‖ <
      ‖pointNeutronForce (κ / cosh δ) (s.card : ℝ) n C‖ *
        (ε + (1 + ε) * (2 * (R / D) / (1 - R / D) ^ 3)) := by
    simpa [α, A, D, ε] using habs.trans_eq hmatch
  simpa [D, ε] using this

/-- When the neutron is at least fifty radii out, the fraction is strictly
less than `1/20`. -/
theorem neutron_force_near_point_fifty
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {ι : Type*} {s : Finset ι} {n C : E} {p : ι → E} {κ ℓ δ R : ℝ}
    (hκ : 0 < κ) (hℓ : 0 < ℓ) (hδ : 0 ≤ δ) (hR : 0 ≤ R)
    (hball : ∀ i ∈ s, ‖p i - C‖ ≤ R) (hfar : 50 * R ≤ ‖n - C‖) (hD : R < ‖n - C‖)
    (hphase : ℓ / (2 * (‖n - C‖ - R)) ≤ 7 / 100) (hne : s.Nonempty) :
    ‖(∑ i ∈ s, neutronPairForce κ ℓ δ n (p i)) -
        pointNeutronForce (κ / cosh δ) (s.card : ℝ) n C‖ <
      ‖pointNeutronForce (κ / cosh δ) (s.card : ℝ) n C‖ / 20 := by
  have hnear := neutron_force_near_point hκ hℓ hδ hR hball hD hphase hne
  set D : ℝ := ‖n - C‖
  have hDpos : 0 < D := by linarith
  have hρ : R / D ≤ 1 / 50 := by
    rw [div_le_div_iff₀ hDpos (by norm_num : (0 : ℝ) < 50)]
    linarith
  have hdenpos : 0 < 1 - R / D := by
    have : R / D < 1 := by
      rw [div_lt_one hDpos]
      linarith
    linarith
  have htheta : 2 * (R / D) / (1 - R / D) ^ 3 ≤ (5000 : ℝ) / 117649 := by
    have hden : (49 : ℝ) / 50 ≤ 1 - R / D := by linarith
    have hcube : ((49 : ℝ) / 50) ^ 3 ≤ (1 - R / D) ^ 3 :=
      pow_le_pow_left₀ (by norm_num) hden 3
    have hnum : 2 * (R / D) ≤ 2 / 50 := by linarith
    have hG : (5000 : ℝ) / 117649 = (2 / 50) / ((49 : ℝ) / 50) ^ 3 := by norm_num
    rw [hG, div_le_div_iff₀ (by positivity) (by positivity)]
    have hleft : 2 * (R / D) * ((49 : ℝ) / 50) ^ 3 ≤ (2 / 50) * ((49 : ℝ) / 50) ^ 3 := by
      have hnn : 0 ≤ ((49 : ℝ) / 50) ^ 3 := by positivity
      nlinarith
    have hright : (2 / 50) * ((49 : ℝ) / 50) ^ 3 ≤ (2 / 50) * (1 - R / D) ^ 3 := by
      have hnn : (0 : ℝ) ≤ 2 / 50 := by norm_num
      nlinarith
    linarith
  have hcap : (6 : ℝ) / 1000 + (1 + 6 / 1000) * ((5000 : ℝ) / 117649) < 1 / 20 := by
    norm_num
  have hfrac : 6 / 1000 + (1 + 6 / 1000) * (2 * (R / D) / (1 - R / D) ^ 3) < 1 / 20 := by
    have hmul : (1 + 6 / 1000) * (2 * (R / D) / (1 - R / D) ^ 3) ≤
        (1 + 6 / 1000) * ((5000 : ℝ) / 117649) :=
      mul_le_mul_of_nonneg_left htheta (by norm_num)
    linarith
  have hpos : 0 < ‖pointNeutronForce (κ / cosh δ) (s.card : ℝ) n C‖ := by
    have hA : 0 < (s.card : ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr hne)
    have hCne : n - C ≠ 0 := by
      intro h0
      have : ‖n - C‖ = 0 := by simpa using congrArg norm h0
      linarith
    unfold pointNeutronForce
    rw [norm_smul, Real.norm_eq_abs, abs_neg,
      abs_of_pos (by positivity : 0 < (s.card : ℝ) * (κ / cosh δ)),
      norm_coulombField hCne]
    positivity
  have hscaled := mul_lt_mul_of_pos_left hfrac hpos
  have hnear' : ‖(∑ i ∈ s, neutronPairForce κ ℓ δ n (p i)) -
      pointNeutronForce (κ / cosh δ) (s.card : ℝ) n C‖ <
      ‖pointNeutronForce (κ / cosh δ) (s.card : ℝ) n C‖ *
        (6 / 1000 + (1 + 6 / 1000) * (2 * (R / D) / (1 - R / D) ^ 3)) := by
    simpa [D] using hnear
  have hlt := lt_trans hnear' hscaled
  simpa [div_eq_mul_inv] using hlt

/-- From `1` MeV to `14` MeV, `T² (1 + T/(2mc²))` grows by a factor strictly
between `197` and `198`. For the inverse-square point field this is the factor
by which the fixed-angle Rutherford cross section falls. The angular law is
classical and is not re-derived. The rest energy `939.565` MeV is external. -/
theorem pointField_cross_section_ratio :
    (197 : ℝ) < 14 ^ 2 * (1 + 14 / (2 * ((939565 : ℝ) / 1000))) /
        (1 + 1 / (2 * ((939565 : ℝ) / 1000))) ∧
      14 ^ 2 * (1 + 14 / (2 * ((939565 : ℝ) / 1000))) /
        (1 + 1 / (2 * ((939565 : ℝ) / 1000))) < 198 := by
  constructor <;> norm_num

/-- The evaluated gold totals `5.295` b and `5.755` b (external) leave the
later total strictly above nine tenths of the earlier one. -/
theorem goldTotal_above_nine_tenths :
    (9 : ℝ) / 10 < ((5295 : ℝ) / 1000) / (5755 / 1000) := by
  norm_num

/-! ### Relative dual phase -/

/-- Interference factor at phase `x`, rapidity half-angle `δ`, and relative
dual half-angle `ε`. At equal scale both angles sit on top of `x`. -/
noncomputable def gammaChannel (x δ ε : ℝ) : ℝ :=
  cosh (x + δ) * cos (x + ε) - sinh (x + δ) * sin (x + ε)

theorem gammaChannel_zero_phase (δ ε : ℝ) :
    gammaChannel 0 δ ε = cosh δ * cos ε - sinh δ * sin ε := by
  simp [gammaChannel]

theorem gammaChannel_eq_rapidity (x δ : ℝ) :
    gammaChannel x δ 0 = gammaRapidity x δ := by
  unfold gammaChannel gammaRapidity gammaSEqual sigmaEqual
  rw [show x + (0 : ℝ) = x by ring, cosh_add x δ, sinh_add x δ]
  ring

theorem gammaChannel_eq_dual (x ε : ℝ) :
    gammaChannel x 0 ε = cos ε * gammaSEqual x - sin ε * tauEqual x := by
  unfold gammaChannel gammaSEqual tauEqual
  rw [show x + (0 : ℝ) = x by ring, cos_add x ε, sin_add x ε]
  ring

/-- A pure rapidity weakens the far field and does not reverse it. -/
theorem rapidity_farField_attractive_bounded {δ : ℝ} (_hδ : 0 ≤ δ) :
    0 < gammaChannel 0 δ 0 ∧ 1 ≤ gammaChannel 0 δ 0 := by
  have hcosh : gammaChannel 0 δ 0 = cosh δ := by
    simp [gammaChannel]
  rw [hcosh]
  exact ⟨cosh_pos δ, one_le_cosh δ⟩

theorem farField_right_angle {δ : ℝ} :
    gammaChannel 0 δ (π / 2) = -sinh δ := by
  simp [gammaChannel, cos_pi_div_two, sin_pi_div_two]

/-- Past the right angle the far field repels at every nonnegative rapidity. -/
theorem farField_repulsive {δ ε : ℝ} (hδ : 0 ≤ δ) (hε : π / 2 < ε) (hεπ : ε ≤ π) :
    gammaChannel 0 δ ε < 0 := by
  rw [gammaChannel_zero_phase]
  have hcosh : 0 < cosh δ := cosh_pos δ
  have hcos : cos ε < 0 := by
    have hstep := strictAntiOn_cos (a := π / 2) (b := ε)
      ⟨by linarith [pi_pos], by linarith [pi_pos]⟩ ⟨by linarith [pi_pos], hεπ⟩ hε
    rwa [cos_pi_div_two] at hstep
  have hsin : 0 ≤ sin ε := sin_nonneg_of_mem_Icc ⟨by linarith [pi_pos], hεπ⟩
  have hleft : cosh δ * cos ε < 0 := mul_neg_of_pos_of_neg hcosh hcos
  have hright : -(sinh δ * sin ε) ≤ 0 := by
    have hsinh : 0 ≤ sinh δ := sinh_nonneg_iff.mpr hδ
    have hprod : 0 ≤ sinh δ * sin ε := mul_nonneg hsinh hsin
    linarith
  linarith

private theorem tanh_lt_self {x : ℝ} (hx : 0 < x) : tanh x < x := by
  let f : ℝ → ℝ := fun y => y - tanh y
  let df : ℝ → ℝ := fun y => tanh y ^ 2
  have hder : ∀ y, HasDerivAt f (df y) y := by
    intro y
    have hdiv := (hasDerivAt_sinh y).div (hasDerivAt_cosh y) (cosh_pos y).ne'
    have hdiv' : HasDerivAt tanh (1 / cosh y ^ 2) y := by
      have hfun : tanh = fun z => sinh z / cosh z := by
        ext z
        rw [tanh_eq_sinh_div_cosh]
      rw [hfun]
      refine hdiv.congr_deriv ?_
      have hnum : cosh y * cosh y - sinh y * sinh y = 1 := by
        rw [← pow_two, ← pow_two]
        simpa [pow_two] using cosh_sq_sub_sinh_sq y
      rw [hnum]
    have hsub := (hasDerivAt_id y).sub hdiv'
    refine hsub.congr_deriv ?_
    have hcosh : cosh y ≠ 0 := (cosh_pos y).ne'
    have hsq : cosh y ^ 2 - sinh y ^ 2 = 1 := by
      simpa [pow_two] using cosh_sq_sub_sinh_sq y
    unfold df
    rw [tanh_eq_sinh_div_cosh]
    field_simp [hcosh]
    linarith [hsq]
  have hcont : Continuous f := by
    unfold f
    have hfun : tanh = fun y => sinh y / cosh y := by
      ext y
      rw [tanh_eq_sinh_div_cosh]
    rw [hfun]
    exact continuous_id.sub
      (continuous_sinh.div continuous_cosh fun y => (cosh_pos y).ne')
  obtain ⟨c, hc, hslope⟩ :=
    exists_hasDerivAt_eq_slope f df hx hcont.continuousOn (fun z _ => hder z)
  have hf0 : f 0 = 0 := by unfold f; simp
  rw [hf0, sub_zero, sub_zero] at hslope
  have hdf : 0 < df c := by
    unfold df
    have hc0 : 0 < c := hc.1
    have hsinh : 0 < sinh c := sinh_pos_iff.mpr hc0
    have htanh : 0 < tanh c := by
      rw [tanh_eq_sinh_div_cosh]
      exact div_pos hsinh (cosh_pos c)
    exact pow_pos htanh 2
  have hquot : 0 < f x / x := by
    rw [← hslope]
    exact hdf
  have hmul : 0 < f x / x * x := mul_pos hquot hx
  rw [div_mul_cancel₀ _ hx.ne'] at hmul
  unfold f at hmul
  linarith

/-- Short of the right angle, a half-rapidity no larger than the angular gap
leaves the far field attractive. -/
theorem farField_attractive_of_gap {δ ε : ℝ}
    (hδ : 0 ≤ δ) (hε : 0 ≤ ε) (hεlt : ε < π / 2) (hgap : δ + ε ≤ π / 2) :
    0 < gammaChannel 0 δ ε := by
  rcases eq_or_lt_of_le hε with rfl | hεpos
  · have hcosh : gammaChannel 0 δ 0 = cosh δ := by simp [gammaChannel]
    rw [hcosh]
    exact cosh_pos δ
  · have hθ0 : 0 < π / 2 - ε := by linarith
    have hθpi : π / 2 - ε < π / 2 := by linarith
    have hδθ : δ ≤ π / 2 - ε := by linarith
    have hsin : 0 < sin ε := sin_pos_of_pos_of_lt_pi hεpos (by linarith [pi_pos])
    have hcosh : 0 < cosh δ := cosh_pos δ
    have htanθ : tan (π / 2 - ε) = cos ε / sin ε := by
      rw [tan_eq_sin_div_cos, sin_pi_div_two_sub, cos_pi_div_two_sub]
    have hcot : tanh δ < cos ε / sin ε := by
      rw [← htanθ]
      rcases eq_or_lt_of_le hδ with rfl | hδpos
      · rw [tanh_zero]
        exact lt_trans hθ0 (lt_tan hθ0 hθpi)
      · have htanh : tanh δ < δ := tanh_lt_self hδpos
        have htan : π / 2 - ε < tan (π / 2 - ε) := lt_tan hθ0 hθpi
        linarith
    rw [gammaChannel_zero_phase]
    rw [tanh_eq_sinh_div_cosh] at hcot
    rw [div_lt_div_iff₀ hcosh hsin] at hcot
    linarith

/-- At zero rapidity the far-field factor can lie strictly between `0` and
`1/M`, so the strength exceeds every bound. -/
theorem dualPhase_factor_arbitrarily_small {M : ℝ} (hM : 0 < M) :
    ∃ ε : ℝ, 0 < ε ∧ ε < π / 2 ∧ 0 < gammaChannel 0 0 ε ∧
      gammaChannel 0 0 ε < 1 / M := by
  set η : ℝ := min 1 (1 / (2 * M))
  have hηhalf : 0 < 1 / (2 * M) := by positivity
  have hη0 : 0 < η := lt_min (by norm_num) hηhalf
  have hηle : η ≤ 1 := min_le_left _ _
  have hηM : η ≤ 1 / (2 * M) := min_le_right _ _
  have hηpi : η < π / 2 := lt_of_le_of_lt hηle (by linarith [pi_gt_three])
  refine ⟨π / 2 - η, by linarith, by linarith, ?_, ?_⟩
  · have hsin : 0 < sin η := sin_pos_of_pos_of_lt_pi hη0 (by linarith [pi_pos])
    simpa [gammaChannel, cos_pi_div_two_sub] using hsin
  · have hsinle : sin η ≤ η := sin_le hη0.le
    have hhalf : 1 / (2 * M) < 1 / M := by
      rw [div_lt_div_iff₀ (by positivity) hM]
      linarith
    have hsmall : sin η < 1 / M := lt_of_le_of_lt hsinle (lt_of_le_of_lt hηM hhalf)
    simpa [gammaChannel, cos_pi_div_two_sub] using hsmall

theorem dualPhase_factor_arbitrarily_small_neg {M : ℝ} (hM : 0 < M) :
    ∃ ε : ℝ, π / 2 < ε ∧ ε < π ∧ gammaChannel 0 0 ε < 0 ∧
      -(1 / M) < gammaChannel 0 0 ε := by
  obtain ⟨ε, hε0, hεπ, hpos, hsmall⟩ := dualPhase_factor_arbitrarily_small hM
  refine ⟨π - ε, by linarith, by linarith, ?_, ?_⟩
  · have hcos : gammaChannel 0 0 (π - ε) = -gammaChannel 0 0 ε := by
      simp [gammaChannel, cos_pi_sub, sin_pi_sub]
    linarith
  · have hcos : gammaChannel 0 0 (π - ε) = -gammaChannel 0 0 ε := by
      simp [gammaChannel, cos_pi_sub, sin_pi_sub]
    linarith

/-! ### A sample of nuclei -/

theorem sample_fluctuation {ι : Type*} (s : Finset ι) (p b : ι → ℝ)
    (hp : ∀ i ∈ s, 0 ≤ p i) (hsum : ∑ i ∈ s, p i = 1) :
    ∑ i ∈ s, p i * b i ^ 2 - (∑ i ∈ s, p i * b i) ^ 2 =
      ∑ i ∈ s, p i * (b i - ∑ j ∈ s, p j * b j) ^ 2 ∧
      0 ≤ ∑ i ∈ s, p i * b i ^ 2 - (∑ i ∈ s, p i * b i) ^ 2 := by
  set μ : ℝ := ∑ j ∈ s, p j * b j
  have hterm : ∀ i, p i * (b i - μ) ^ 2 =
      p i * b i ^ 2 - 2 * μ * (p i * b i) + μ ^ 2 * p i := by
    intro i
    ring
  have hexpand : ∑ i ∈ s, p i * (b i - μ) ^ 2 =
      ∑ i ∈ s, p i * b i ^ 2 - 2 * μ * μ + μ ^ 2 := by
    have hrewrite : ∑ i ∈ s, p i * (b i - μ) ^ 2 =
        ∑ i ∈ s, (p i * b i ^ 2 - 2 * μ * (p i * b i) + μ ^ 2 * p i) := by
      refine Finset.sum_congr rfl ?_
      intro i _
      exact hterm i
    rw [hrewrite]
    have hsplit : ∑ i ∈ s, (p i * b i ^ 2 - 2 * μ * (p i * b i) + μ ^ 2 * p i) =
        (∑ i ∈ s, p i * b i ^ 2 - ∑ i ∈ s, 2 * μ * (p i * b i)) +
          ∑ i ∈ s, μ ^ 2 * p i := by
      have hrewrite2 : ∑ i ∈ s, (p i * b i ^ 2 - 2 * μ * (p i * b i) + μ ^ 2 * p i) =
          ∑ i ∈ s, ((p i * b i ^ 2 - 2 * μ * (p i * b i)) + μ ^ 2 * p i) := by
        refine Finset.sum_congr rfl ?_
        intro i _
        ring
      rw [hrewrite2, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [hsplit]
    have hlin : ∑ i ∈ s, 2 * μ * (p i * b i) = 2 * μ * μ := by
      have hsame : ∑ i ∈ s, 2 * μ * (p i * b i) =
          ∑ i ∈ s, (2 * μ) * (p i * b i) := by
        refine Finset.sum_congr rfl ?_
        intro i _
        ring
      rw [hsame, ← Finset.mul_sum]
    have hweight : ∑ i ∈ s, μ ^ 2 * p i = μ ^ 2 := by
      have hsame : ∑ i ∈ s, μ ^ 2 * p i = ∑ i ∈ s, (μ ^ 2) * p i := by
        refine Finset.sum_congr rfl ?_
        intro i _
        ring
      rw [hsame, ← Finset.mul_sum, hsum, mul_one]
    rw [hlin, hweight]
  have hnn : 0 ≤ ∑ i ∈ s, p i * (b i - μ) ^ 2 := by
    refine Finset.sum_nonneg ?_
    intro i hi
    exact mul_nonneg (hp i hi) (sq_nonneg _)
  have hmain : ∑ i ∈ s, p i * b i ^ 2 - μ ^ 2 =
      ∑ i ∈ s, p i * (b i - μ) ^ 2 := by
    linarith [hexpand]
  constructor
  · simpa [μ] using hmain
  · have hμsq : (∑ i ∈ s, p i * b i) ^ 2 = μ ^ 2 := by simp [μ]
    linarith [hmain, hnn, hμsq]

theorem sample_fluctuation_vanishes_iff {ι : Type*} (s : Finset ι) (p b : ι → ℝ)
    (hp : ∀ i ∈ s, 0 ≤ p i) (hsum : ∑ i ∈ s, p i = 1) :
    ∑ i ∈ s, p i * b i ^ 2 - (∑ i ∈ s, p i * b i) ^ 2 = 0 ↔
      ∀ i ∈ s, p i = 0 ∨ b i = ∑ j ∈ s, p j * b j := by
  set μ : ℝ := ∑ j ∈ s, p j * b j
  have hpair := sample_fluctuation s p b hp hsum
  have hid : ∑ i ∈ s, p i * b i ^ 2 - (∑ i ∈ s, p i * b i) ^ 2 =
      ∑ i ∈ s, p i * (b i - μ) ^ 2 := by
    simpa [μ] using hpair.1
  constructor
  · intro h0
    have hsum0 : ∑ i ∈ s, p i * (b i - μ) ^ 2 = 0 := by linarith
    have hnn : ∀ i ∈ s, 0 ≤ p i * (b i - μ) ^ 2 := by
      intro i hi
      exact mul_nonneg (hp i hi) (sq_nonneg _)
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum0
    intro i hi
    have hzero : p i * (b i - μ) ^ 2 = 0 := hterm i hi
    rcases mul_eq_zero.mp hzero with hp0 | hsq
    · exact Or.inl hp0
    · exact Or.inr (sub_eq_zero.mp (sq_eq_zero_iff.mp hsq))
  · intro hall
    have hzero : ∑ i ∈ s, p i * (b i - μ) ^ 2 = 0 := by
      refine Finset.sum_eq_zero ?_
      intro i hi
      rcases hall i hi with hp0 | hb
      · simp [hp0]
      · simp [hb, μ]
    linarith

theorem two_channel_fluctuation (p b₁ b₂ : ℝ) :
    p * b₁ ^ 2 + (1 - p) * b₂ ^ 2 - (p * b₁ + (1 - p) * b₂) ^ 2 =
      p * (1 - p) * (b₁ - b₂) ^ 2 := by
  ring

theorem channel_mean_strictly_between {p b₁ b₂ : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (h : b₁ < b₂) :
    b₁ < p * b₁ + (1 - p) * b₂ ∧ p * b₁ + (1 - p) * b₂ < b₂ := by
  constructor
  · have hpos : 0 < (1 - p) * (b₂ - b₁) := mul_pos (by linarith) (sub_pos.mpr h)
    have : p * b₁ + (1 - p) * b₂ - b₁ = (1 - p) * (b₂ - b₁) := by ring
    linarith
  · have hpos : 0 < p * (b₂ - b₁) := mul_pos hp (sub_pos.mpr h)
    have : b₂ - (p * b₁ + (1 - p) * b₂) = p * (b₂ - b₁) := by ring
    linarith

/-- Opposite signs put the coherent coefficient strictly between the two
channels and strictly below the larger magnitude. -/
theorem opposite_channel_mean_smaller {p b₁ b₂ : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (h₁ : b₁ < 0) (h₂ : 0 < b₂) :
    |p * b₁ + (1 - p) * b₂| < max (-b₁) b₂ := by
  have hbetween := channel_mean_strictly_between hp hp1 (show b₁ < b₂ by linarith)
  set μ : ℝ := p * b₁ + (1 - p) * b₂
  rcases lt_or_ge μ 0 with hμ | hμ
  · rw [abs_of_neg hμ]
    have : -μ < -b₁ := by linarith [hbetween.1]
    exact lt_of_lt_of_le this (le_max_left _ _)
  · rw [abs_of_nonneg hμ]
    exact lt_of_lt_of_le hbetween.2 (le_max_right _ _)

/-- External Sears values. The incoherent cross section of natural hydrogen
exceeds the coherent one by more than `45`. -/
theorem hydrogen_incoherent_dominates :
    (45 : ℝ) < ((8026 : ℝ) / 100) / (17568 / 10000) := by
  norm_num

/-- External Sears values. The incoherent cross section of natural vanadium
exceeds the coherent one by more than `200`. -/
theorem vanadium_incoherent_dominates :
    (200 : ℝ) < ((508 : ℝ) / 100) / (184 / 10000) := by
  norm_num

/-- External Sears abundances and bound coherent lengths of the five stable
titanium isotopes. `46` and `48` have opposite signs, and the weighted mean
lies strictly between `-3.44` and `-3.43` fm. -/
theorem titanium_sample_mean :
    ((82 : ℝ) / 1000) * (493 / 100) + (74 / 1000) * (363 / 100) +
        (738 / 1000) * (-608 / 100) + (54 / 1000) * (104 / 100) +
        (52 / 1000) * (618 / 100) ∈ Ioo (-344 / 100) (-343 / 100) ∧
      (-608 / 100 : ℝ) < 0 ∧ 0 < (493 / 100 : ℝ) ∧
      (82 : ℝ) / 1000 + 74 / 1000 + 738 / 1000 + 54 / 1000 + 52 / 1000 = 1 := by
  refine ⟨?_, by norm_num, by norm_num, by norm_num⟩
  rw [Set.mem_Ioo]
  constructor <;> norm_num

end Gravity

end DstDiophantine
