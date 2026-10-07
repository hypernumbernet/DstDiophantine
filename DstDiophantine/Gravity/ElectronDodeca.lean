import DstDiophantine.Gravity.ElectronBoundary
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The dodecahedral shell in the outer well

For every nuclear charge `Z ≥ 8` the radial response of twenty vertices of a
regular dodecahedron meets `Z` exactly once before the nearest chord reaches
the first node. The root lies at a radius strictly between `7ℓ/10` and
`10ℓ/7`, and the outward force restores it.
-/

namespace DstDiophantine

namespace Gravity

open Real Set Finset

noncomputable def chordAmp (t : ℝ) : ℝ :=
  cosh t * sin t

theorem strictMonoOn_chordAmp : StrictMonoOn chordAmp (Icc (0 : ℝ) (π / 2)) := by
  refine strictMonoOn_of_deriv_pos (convex_Icc 0 (π / 2))
    (continuous_cosh.mul continuous_sin).continuousOn ?_
  intro y hy
  rw [interior_Icc] at hy
  have hder : HasDerivAt chordAmp (sinh y * sin y + cosh y * cos y) y :=
    (hasDerivAt_cosh y).mul (hasDerivAt_sin y)
  rw [hder.deriv]
  have hsin : 0 < sin y :=
    sin_pos_of_pos_of_lt_pi hy.1 (lt_trans hy.2 (half_lt_self pi_pos))
  have hcos : 0 < cos y :=
    cos_pos_of_mem_Ioo ⟨by linarith [pi_pos, hy.1], hy.2⟩
  have h1 : 0 < sinh y * sin y := mul_pos (sinh_pos_iff.mpr hy.1) hsin
  have h2 : 0 < cosh y * cos y := mul_pos (cosh_pos y) hcos
  linarith

/-! ### Polynomial bounds for sine and cosine -/

private theorem segment_strictMono {f f' : ℝ → ℝ} {b : ℝ} (_hb : 0 < b)
    (hcont : ContinuousOn f (Icc 0 b))
    (hderiv : ∀ y ∈ Ioo (0 : ℝ) b, HasDerivAt f (f' y) y)
    (hpos : ∀ y ∈ Ioo (0 : ℝ) b, 0 < f' y) :
    StrictMonoOn f (Icc 0 b) := by
  refine strictMonoOn_of_deriv_pos (convex_Icc 0 b) hcont ?_
  intro y hy
  rw [interior_Icc] at hy
  rw [(hderiv y hy).deriv]
  exact hpos y hy

private theorem segment_pos {f f' : ℝ → ℝ} {b : ℝ} (hb : 0 < b) (h0 : f 0 = 0)
    (hcont : ContinuousOn f (Icc 0 b))
    (hderiv : ∀ y ∈ Ioo (0 : ℝ) b, HasDerivAt f (f' y) y)
    (hpos : ∀ y ∈ Ioo (0 : ℝ) b, 0 < f' y) :
    0 < f b := by
  have hmono := segment_strictMono hb hcont hderiv hpos
  have hlt := hmono (by simp [hb.le]) (right_mem_Icc.mpr hb.le) hb
  simpa [h0] using hlt

private noncomputable def gap3 (x : ℝ) : ℝ :=
  1 - x ^ 2 / 2 + x ^ 4 / 24 - cos x

private noncomputable def gap2 (x : ℝ) : ℝ :=
  x - x ^ 3 / 6 + x ^ 5 / 120 - sin x

private noncomputable def gap1 (x : ℝ) : ℝ :=
  cos x - (1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720)

private noncomputable def gap0 (x : ℝ) : ℝ :=
  sin x - (x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040)

private theorem hasDerivAt_gap3 (x : ℝ) :
    HasDerivAt gap3 (sin x - x + x ^ 3 / 6) x := by
  have h2 : HasDerivAt (fun t : ℝ => t ^ 2 / 2) ((2 * x) / 2) x := by
    simpa using (hasDerivAt_pow 2 x).div_const 2
  have h4 : HasDerivAt (fun t : ℝ => t ^ 4 / 24) ((4 * x ^ 3) / 24) x := by
    simpa using (hasDerivAt_pow 4 x).div_const 24
  have h := ((((hasDerivAt_const x (1 : ℝ)).sub h2).add h4).sub (hasDerivAt_cos x))
  unfold gap3
  refine h.congr_deriv ?_
  ring

private theorem hasDerivAt_gap2 (x : ℝ) : HasDerivAt gap2 (gap3 x) x := by
  have h3 : HasDerivAt (fun t : ℝ => t ^ 3 / 6) ((3 * x ^ 2) / 6) x := by
    simpa using (hasDerivAt_pow 3 x).div_const 6
  have h5 : HasDerivAt (fun t : ℝ => t ^ 5 / 120) ((5 * x ^ 4) / 120) x := by
    simpa using (hasDerivAt_pow 5 x).div_const 120
  have h := (((hasDerivAt_id' x).sub h3).add h5).sub (hasDerivAt_sin x)
  unfold gap2
  refine h.congr_deriv ?_
  unfold gap3
  ring

private theorem hasDerivAt_gap1 (x : ℝ) : HasDerivAt gap1 (gap2 x) x := by
  have h2 : HasDerivAt (fun t : ℝ => t ^ 2 / 2) ((2 * x) / 2) x := by
    simpa using (hasDerivAt_pow 2 x).div_const 2
  have h4 : HasDerivAt (fun t : ℝ => t ^ 4 / 24) ((4 * x ^ 3) / 24) x := by
    simpa using (hasDerivAt_pow 4 x).div_const 24
  have h6 : HasDerivAt (fun t : ℝ => t ^ 6 / 720) ((6 * x ^ 5) / 720) x := by
    simpa using (hasDerivAt_pow 6 x).div_const 720
  have hpoly := (((hasDerivAt_const x (1 : ℝ)).sub h2).add h4).sub h6
  have h := (hasDerivAt_cos x).sub hpoly
  unfold gap1
  refine h.congr_deriv ?_
  unfold gap2
  ring

private theorem hasDerivAt_gap0 (x : ℝ) : HasDerivAt gap0 (gap1 x) x := by
  have h3 : HasDerivAt (fun t : ℝ => t ^ 3 / 6) ((3 * x ^ 2) / 6) x := by
    simpa using (hasDerivAt_pow 3 x).div_const 6
  have h5 : HasDerivAt (fun t : ℝ => t ^ 5 / 120) ((5 * x ^ 4) / 120) x := by
    simpa using (hasDerivAt_pow 5 x).div_const 120
  have h7 : HasDerivAt (fun t : ℝ => t ^ 7 / 5040) ((7 * x ^ 6) / 5040) x := by
    simpa using (hasDerivAt_pow 7 x).div_const 5040
  have hpoly := (((hasDerivAt_id' x).sub h3).add h5).sub h7
  have h := (hasDerivAt_sin x).sub hpoly
  unfold gap0
  refine h.congr_deriv ?_
  unfold gap1
  ring

theorem trigPoly_bounds {x : ℝ} (hx : 0 < x) :
    x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040 < sin x ∧
      sin x < x - x ^ 3 / 6 + x ^ 5 / 120 ∧
        1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 < cos x ∧
          cos x < 1 - x ^ 2 / 2 + x ^ 4 / 24 := by
  have h4pos : ∀ t ∈ Ioo (0 : ℝ) x, 0 < sin t - t + t ^ 3 / 6 := by
    intro t ht
    have h := sin_gt_sub_cube ht.1
    linarith
  have hcont3 : ContinuousOn gap3 (Icc 0 x) := by
    unfold gap3
    exact (by continuity : Continuous fun t : ℝ =>
      1 - t ^ 2 / 2 + t ^ 4 / 24 - cos t).continuousOn
  have h3 := segment_pos hx (by unfold gap3; simp) hcont3
    (fun t _ => hasDerivAt_gap3 t) h4pos
  have h3pos : ∀ t ∈ Ioo (0 : ℝ) x, 0 < gap3 t := by
    intro t ht
    have hmono := segment_strictMono hx hcont3 (fun s _ => hasDerivAt_gap3 s) h4pos
    have hlt := hmono (by simp [hx.le]) ⟨ht.1.le, ht.2.le⟩ ht.1
    simpa [gap3] using hlt
  have hcont2 : ContinuousOn gap2 (Icc 0 x) := by
    unfold gap2
    exact (by continuity : Continuous fun t : ℝ =>
      t - t ^ 3 / 6 + t ^ 5 / 120 - sin t).continuousOn
  have h2 := segment_pos hx (by unfold gap2; simp) hcont2
    (fun t _ => hasDerivAt_gap2 t) h3pos
  have h2pos : ∀ t ∈ Ioo (0 : ℝ) x, 0 < gap2 t := by
    intro t ht
    have hmono := segment_strictMono hx hcont2 (fun s _ => hasDerivAt_gap2 s) h3pos
    have hlt := hmono (by simp [hx.le]) ⟨ht.1.le, ht.2.le⟩ ht.1
    simpa [gap2] using hlt
  have hcont1 : ContinuousOn gap1 (Icc 0 x) := by
    unfold gap1
    exact (by continuity : Continuous fun t : ℝ =>
      cos t - (1 - t ^ 2 / 2 + t ^ 4 / 24 - t ^ 6 / 720)).continuousOn
  have h1 := segment_pos hx (by unfold gap1; simp) hcont1
    (fun t _ => hasDerivAt_gap1 t) h2pos
  have h1pos : ∀ t ∈ Ioo (0 : ℝ) x, 0 < gap1 t := by
    intro t ht
    have hmono := segment_strictMono hx hcont1 (fun s _ => hasDerivAt_gap1 s) h2pos
    have hlt := hmono (by simp [hx.le]) ⟨ht.1.le, ht.2.le⟩ ht.1
    simpa [gap1] using hlt
  have hcont0 : ContinuousOn gap0 (Icc 0 x) := by
    unfold gap0
    exact (by continuity : Continuous fun t : ℝ =>
      sin t - (t - t ^ 3 / 6 + t ^ 5 / 120 - t ^ 7 / 5040)).continuousOn
  have h0 := segment_pos hx (by unfold gap0; simp) hcont0
    (fun t _ => hasDerivAt_gap0 t) h1pos
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [gap0] using h0
  · simpa [gap2] using h2
  · simpa [gap1] using h1
  · simpa [gap3] using h3

/-! ### Hyperbolic and interference bounds from the polynomials -/

private theorem phase_bounds {t sLo sHi cLo cHi eLo eHi ALo AHi GLo GHi : ℝ}
    (ht0 : 0 < t) (_ht1 : t ≤ 1)
    (hsLo : sLo < sin t) (hsHi : sin t < sHi)
    (hcLo : cLo < cos t) (hcHi : cos t < cHi)
    (heLo : eLo < exp t) (heHi : exp t < eHi)
    (hspos : 0 < sLo) (hcpos : 0 < cLo) (hepos : 0 < eLo) (hehi : 0 < eHi)
    (he1 : 1 < eLo)
    (hALo : ALo < (eLo + eHi⁻¹) / 2 * sLo)
    (hAHi : (eHi + eLo⁻¹) / 2 * sHi < AHi)
    (hGLo : GLo < (eLo + eHi⁻¹) / 2 * cLo - (eHi - eHi⁻¹) / 2 * sHi)
    (hGHi : (eHi + eLo⁻¹) / 2 * cHi - (eLo - eLo⁻¹) / 2 * sLo < GHi) :
    ALo < chordAmp t ∧ chordAmp t < AHi ∧
      GLo < gammaSEqual t ∧ gammaSEqual t < GHi := by
  have hneg_lo : exp (-t) < eLo⁻¹ := by
    rw [exp_neg]
    exact (inv_lt_inv₀ (exp_pos t) hepos).mpr heLo
  have hneg_hi : eHi⁻¹ < exp (-t) := by
    rw [exp_neg]
    exact (inv_lt_inv₀ hehi (exp_pos t)).mpr heHi
  have hch_lo : (eLo + eHi⁻¹) / 2 < cosh t := by
    rw [cosh_eq]
    linarith
  have hch_hi : cosh t < (eHi + eLo⁻¹) / 2 := by
    rw [cosh_eq]
    linarith
  have hsh_lo : (eLo - eLo⁻¹) / 2 < sinh t := by
    rw [sinh_eq]
    linarith
  have hsh_hi : sinh t < (eHi - eHi⁻¹) / 2 := by
    rw [sinh_eq]
    linarith
  have hch_pos : 0 < (eLo + eHi⁻¹) / 2 := by positivity
  have hsin_pos : 0 < sin t := lt_trans hspos hsLo
  have hcos_pos : 0 < cos t := lt_trans hcpos hcLo
  have hAmp_lo : (eLo + eHi⁻¹) / 2 * sLo < chordAmp t := by
    unfold chordAmp
    exact mul_lt_mul hch_lo hsLo.le hspos (cosh_pos t).le
  have hch_hi_pos : 0 ≤ (eHi + eLo⁻¹) / 2 := le_of_lt (lt_trans (cosh_pos t) hch_hi)
  have hAmp_hi : chordAmp t < (eHi + eLo⁻¹) / 2 * sHi := by
    unfold chordAmp
    exact mul_lt_mul hch_hi hsHi.le hsin_pos hch_hi_pos
  have hcos_lo : (eLo + eHi⁻¹) / 2 * cLo < cosh t * cos t :=
    mul_lt_mul hch_lo hcLo.le hcpos (cosh_pos t).le
  have hsh_hi_pos : 0 ≤ (eHi - eHi⁻¹) / 2 :=
    le_of_lt (lt_trans (sinh_pos_iff.mpr ht0) hsh_hi)
  have hsin_hi : sinh t * sin t < (eHi - eHi⁻¹) / 2 * sHi :=
    mul_lt_mul hsh_hi hsHi.le hsin_pos hsh_hi_pos
  have hcos_hi : cosh t * cos t < (eHi + eLo⁻¹) / 2 * cHi :=
    mul_lt_mul hch_hi hcHi.le hcos_pos hch_hi_pos
  have hsh_lo_pos : 0 < (eLo - eLo⁻¹) / 2 := by
    have hinv_lt : eLo⁻¹ < eLo := by
      rw [← mul_lt_mul_iff_of_pos_left hepos]
      field_simp [hepos.ne']
      nlinarith [he1]
    linarith
  have hsin_lo : (eLo - eLo⁻¹) / 2 * sLo < sinh t * sin t :=
    mul_lt_mul hsh_lo hsLo.le hspos (sinh_pos_iff.mpr ht0).le
  have hγ_lo : (eLo + eHi⁻¹) / 2 * cLo - (eHi - eHi⁻¹) / 2 * sHi < gammaSEqual t := by
    unfold gammaSEqual
    linarith
  have hγ_hi : gammaSEqual t < (eHi + eLo⁻¹) / 2 * cHi - (eLo - eLo⁻¹) / 2 * sLo := by
    unfold gammaSEqual
    linarith
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

/-! ### The wall and the response below charge 8 -/

theorem dodecaWall_lt_five_sevenths : dodecaWall < 5 / 7 := by
  have hnear : (7 / 5 : ℝ) < dodecaNear := dodecaNear_gt_seven_fifths
  have hx1 : resonanceRoot1 < 1 := resonanceRoot1_sharp_bounds.2
  have hpos : 0 < dodecaNear := by linarith
  unfold dodecaWall
  have h1 : resonanceRoot1 / dodecaNear < 1 / dodecaNear :=
    div_lt_div_of_pos_right hx1 hpos
  have h2 : (1 : ℝ) / dodecaNear < 5 / 7 := by
    rw [div_lt_iff₀ hpos]
    nlinarith
  exact h1.trans h2

theorem seven_twentieths_lt_dodecaWall : (7 / 20 : ℝ) < dodecaWall := by
  have hnear : dodecaNear < 701 / 500 := dodecaNear_lt_sevenHundredOne_fiveHundred
  have hpos : 0 < dodecaNear := by linarith [dodecaNear_gt_one]
  have hden : (0 : ℝ) < 701 / 500 := by norm_num
  have hpi : (0 : ℝ) < π / 4 := by positivity
  have h1 : (3 / 4 : ℝ) / (701 / 500) < (π / 4) / (701 / 500) := by
    refine div_lt_div_of_pos_right ?_ hden
    linarith [pi_gt_three]
  have h2 : (π / 4) / (701 / 500) < (π / 4) / dodecaNear := by
    rw [div_lt_div_iff₀ hden hpos]
    nlinarith [hnear, pi_gt_three]
  have h3 : (π / 4) / dodecaNear < resonanceRoot1 / dodecaNear :=
    div_lt_div_of_pos_right resonanceRoot1_sharp_bounds.1 hpos
  have h4 : (7 / 20 : ℝ) < (3 / 4) / (701 / 500) := by norm_num
  unfold dodecaWall
  linarith

private lemma sqrt_six_lt_fortyNine_twentieths : sqrt 6 < 49 / 20 := by
  rw [← sqrt_sq (by norm_num : (0 : ℝ) ≤ 49 / 20)]
  exact (sqrt_lt_sqrt_iff (by positivity)).mpr (by norm_num)

private lemma dodecaFarScale_lt_twentySeven_fiftieths : dodecaFarScale < 27 / 50 := by
  have h5 : (1389 / 625 : ℝ) < sqrt 5 := by
    rw [← sqrt_sq (by norm_num : (0 : ℝ) ≤ 1389 / 625)]
    exact (sqrt_lt_sqrt_iff (by positivity)).mpr (by norm_num)
  have h5lt : sqrt 5 < 3 := by
    rw [← sqrt_sq (by norm_num : (0 : ℝ) ≤ 3), sqrt_lt_sqrt_iff (by positivity)]
    norm_num
  have hsq : dodecaFarScale ^ 2 = 3 * (3 - sqrt 5) / 8 := by
    unfold dodecaFarScale
    exact sq_sqrt (by nlinarith [h5lt])
  have hstep : 3 * (3 - sqrt 5) < ((27 : ℝ) / 50) ^ 2 * 8 := by
    have h8 : ((27 : ℝ) / 50) ^ 2 * 8 = 1458 / 625 := by norm_num
    rw [h8]
    nlinarith [h5]
  have hlt : dodecaFarScale ^ 2 < ((27 : ℝ) / 50) ^ 2 := by
    rw [hsq]
    exact (div_lt_iff₀ (by norm_num)).mpr hstep
  have hnn : 0 ≤ dodecaFarScale := by
    unfold dodecaFarScale
    exact sqrt_nonneg _
  rw [← abs_of_nonneg hnn, ← abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 27 / 50)]
  exact (sq_lt_sq).mp hlt

private lemma lowerPoly_anti {u v : ℝ} (hu : 0 ≤ u) (huv : u < v) :
    1 - v ^ 2 - v ^ 4 / 6 < 1 - u ^ 2 - u ^ 4 / 6 := by
  have h2 : u ^ 2 < v ^ 2 := by nlinarith
  have h4 : u ^ 4 < v ^ 4 := by
    have hdiff : v ^ 4 - u ^ 4 = (v ^ 2 - u ^ 2) * (v ^ 2 + u ^ 2) := by ring
    have hpos : 0 < (v ^ 2 - u ^ 2) * (v ^ 2 + u ^ 2) :=
      mul_pos (by linarith) (by nlinarith [huv])
    linarith
  linarith

private lemma early_budget :
    ((3 : ℝ) / 2) * (701 / 500) * (1 - (7 / 20) ^ 2) /
        (1 - (701 / 500 * (7 / 20)) ^ 2 - (701 / 500 * (7 / 20)) ^ 4 / 6) +
      (13 / 5 + 147 / 80 + 81 / 100 + 1 / 4) < 8 := by
  norm_num

theorem dodecaResponse_lt_eight_early {x : ℝ} (hx : x ∈ Ioc (0 : ℝ) (7 / 20)) :
    dodecaResponse x < 8 := by
  have hwall : (7 / 20 : ℝ) < dodecaWall := seven_twentieths_lt_dodecaWall
  have hxπ : x < π / 4 := by
    have h7 : (7 / 20 : ℝ) < 3 / 4 := by norm_num
    have hπ : (3 / 4 : ℝ) < π / 4 := by linarith [pi_gt_three]
    exact lt_trans (lt_of_le_of_lt hx.2 h7) hπ
  have hx1 : x < resonanceRoot1 := lt_trans hxπ resonanceRoot1_sharp_bounds.1
  have hxmem : x ∈ Ioo (0 : ℝ) dodecaWall := ⟨hx.1, lt_of_le_of_lt hx.2 hwall⟩
  rw [dodecaResponse_eq_terms]
  have hcut : (7 / 20 : ℝ) ∈ Ioo (0 : ℝ) dodecaWall := ⟨by norm_num, hwall⟩
  have hnear_le : dodecaNearTerm x ≤ dodecaNearTerm (7 / 20) := by
    rcases lt_or_eq_of_le hx.2 with hlt | rfl
    · exact (dodecaNearTerm_strictMono hxmem hcut hlt).le
    · exact le_rfl
  have hphase : (701 / 500) * (7 / 20) < π / 4 := by
    have hcmp : (701 / 500) * ((7 : ℝ) / 20) < 3 / 4 := by norm_num
    linarith [pi_gt_three]
  have h7pos : (0 : ℝ) < 7 / 20 := by norm_num
  have hnear_pos : 0 < dodecaNear := by linarith [dodecaNear_gt_one]
  have hcx1 : dodecaNear * (7 / 20) < resonanceRoot1 := by
    have hlt : dodecaNear * (7 / 20) < (701 / 500) * (7 / 20) :=
      mul_lt_mul_of_pos_right dodecaNear_lt_sevenHundredOne_fiveHundred h7pos
    exact lt_trans (lt_trans hlt hphase) resonanceRoot1_sharp_bounds.1
  have h7π : (7 / 20 : ℝ) < π / 4 := by
    have hcmp : (7 / 20 : ℝ) < 3 / 4 := by norm_num
    linarith [pi_gt_three]
  have hγx : gammaSEqual (7 / 20) < 1 - (7 / 20 : ℝ) ^ 2 :=
    gammaSEqual_lt_sub_sq h7pos (lt_trans h7π resonanceRoot1_sharp_bounds.1)
  have hγc : 1 - (dodecaNear * (7 / 20)) ^ 2 - (dodecaNear * (7 / 20)) ^ 4 / 6 <
      gammaSEqual (dodecaNear * (7 / 20)) :=
    gammaSEqual_gt_lowerPoly (mul_pos hnear_pos h7pos) hcx1
  have hanti := lowerPoly_anti (u := dodecaNear * (7 / 20)) (v := (701 / 500) * (7 / 20))
    (mul_nonneg hnear_pos.le h7pos.le)
    (mul_lt_mul_of_pos_right dodecaNear_lt_sevenHundredOne_fiveHundred h7pos)
  set fHi : ℝ := 1 - ((701 : ℝ) / 500 * (7 / 20)) ^ 2 -
    ((701 : ℝ) / 500 * (7 / 20)) ^ 4 / 6
  have hfpos : 0 < fHi := by
    unfold fHi
    norm_num
  have hγpos : 0 < gammaSEqual (dodecaNear * (7 / 20)) :=
    gammaSEqual_pos_of_lt_firstNode (mul_pos hnear_pos h7pos).le hcx1
  have h1pos : (0 : ℝ) < 1 - (7 / 20 : ℝ) ^ 2 := by norm_num
  have hchain : fHi < gammaSEqual (dodecaNear * (7 / 20)) := hanti.trans hγc
  have hratio : scaledRatio dodecaNear (7 / 20) < (1 - (7 / 20) ^ 2) / fHi := by
    unfold scaledRatio
    rw [div_lt_div_iff₀ hγpos hfpos]
    have hleft : gammaSEqual (7 / 20) * fHi < (1 - (7 / 20) ^ 2) * fHi :=
      mul_lt_mul_of_pos_right hγx hfpos
    have hright : (1 - (7 / 20) ^ 2) * fHi <
        (1 - (7 / 20) ^ 2) * gammaSEqual (dodecaNear * (7 / 20)) :=
      mul_lt_mul_of_pos_left hchain h1pos
    linarith
  have hkn : 3 / 2 * dodecaNear < 3 / 2 * (701 / 500) := by
    nlinarith [dodecaNear_lt_sevenHundredOne_fiveHundred]
  have hratio_pos : 0 < scaledRatio dodecaNear (7 / 20) := by
    unfold scaledRatio
    exact div_pos (gammaSEqual_pos_of_lt_firstNode h7pos.le
      (lt_trans h7π resonanceRoot1_sharp_bounds.1)) hγpos
  have hnear_at : dodecaNearTerm (7 / 20) <
      (3 / 2) * (701 / 500) * ((1 - (7 / 20 : ℝ) ^ 2) / fHi) := by
    unfold dodecaNearTerm
    exact mul_lt_mul hkn hratio.le hratio_pos (by norm_num)
  have h3c : sqrt 3 / 2 < 1 := by
    rw [div_lt_one (by norm_num)]
    exact lt_trans sqrt_three_lt_twentySix_fifteenths (by norm_num)
  have h6c : sqrt 6 / 4 < 1 := by
    rw [div_lt_one (by norm_num)]
    exact lt_trans sqrt_six_lt_five_halves (by norm_num)
  have h3r := scaledRatio_lt_one
    (div_pos (sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3)) (by norm_num)) h3c hx.1 hx1
  have h6r := scaledRatio_lt_one
    (div_pos (sqrt_pos.mpr (by norm_num : (0 : ℝ) < 6)) (by norm_num)) h6c hx.1 hx1
  have hfr := scaledRatio_lt_one (by
      have h5lt : sqrt 5 < 3 := by
        rw [← sqrt_sq (by norm_num : (0 : ℝ) ≤ 3), sqrt_lt_sqrt_iff (by positivity)]
        norm_num
      unfold dodecaFarScale
      exact sqrt_pos.mpr (by nlinarith [h5lt]))
    dodecaFarScale_lt_one hx.1 hx1
  have hhr := scaledRatio_lt_one (c := (1 / 2 : ℝ)) (by norm_num) (by norm_num) hx.1 hx1
  have h3k : 3 * sqrt 3 / 2 < 13 / 5 := by
    nlinarith [sqrt_three_lt_twentySix_fifteenths]
  have h6k : 3 * sqrt 6 / 4 < 147 / 80 := by
    nlinarith [sqrt_six_lt_fortyNine_twentieths]
  have hfk : 3 / 2 * dodecaFarScale < 81 / 100 := by
    nlinarith [dodecaFarScale_lt_twentySeven_fiftieths]
  have hfar : dodecaFarTerm x < 13 / 5 + 147 / 80 + 81 / 100 + 1 / 4 := by
    unfold dodecaFarTerm
    have h3t : 3 * sqrt 3 / 2 * scaledRatio (sqrt 3 / 2) x < 13 / 5 := by
      have hpos : 0 < 3 * sqrt 3 / 2 := by positivity
      linarith [mul_lt_mul_of_pos_left h3r hpos, h3k]
    have h6t : 3 * sqrt 6 / 4 * scaledRatio (sqrt 6 / 4) x < 147 / 80 := by
      have hpos : 0 < 3 * sqrt 6 / 4 := by positivity
      linarith [mul_lt_mul_of_pos_left h6r hpos, h6k]
    have hft : 3 / 2 * dodecaFarScale * scaledRatio dodecaFarScale x < 81 / 100 := by
      have hpos : 0 < 3 / 2 * dodecaFarScale := by
        have h5lt : sqrt 5 < 3 := by
          rw [← sqrt_sq (by norm_num : (0 : ℝ) ≤ 3), sqrt_lt_sqrt_iff (by positivity)]
          norm_num
        have hpos' : 0 < dodecaFarScale := by
          unfold dodecaFarScale
          exact sqrt_pos.mpr (by nlinarith [h5lt])
        nlinarith
      linarith [mul_lt_mul_of_pos_left hfr hpos, hfk]
    have hht : (1 / 4) * scaledRatio (1 / 2) x < 1 / 4 := by
      nlinarith [mul_lt_mul_of_pos_left hhr (by norm_num : (0 : ℝ) < 1 / 4)]
    linarith
  have hbudget := early_budget
  have hnear : dodecaNearTerm x <
      (3 / 2) * (701 / 500) * ((1 - (7 / 20) ^ 2) / fHi) := by
    exact lt_of_le_of_lt hnear_le hnear_at
  unfold fHi at hnear hbudget
  linarith

/-! ### Six-digit enclosures of the chord scales -/

private lemma lt_of_sq_lt {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hsq : a ^ 2 < b ^ 2) :
    a < b := by
  rw [← abs_of_nonneg ha, ← abs_of_nonneg hb]
  exact (sq_lt_sq).mp hsq

private theorem dodecaNear_gt_700629_500000 : (700629 : ℝ) / 500000 < dodecaNear := by
  have hsq : dodecaNear ^ 2 = 3 * (3 + sqrt 5) / 8 := by
    unfold dodecaNear
    exact sq_sqrt (by nlinarith [sqrt_nonneg (5 : ℝ)])
  have hNpos : (0 : ℝ) < 8 * 700629 ^ 2 - 9 * 500000 ^ 2 := by norm_num
  have hNsq : (8 * (700629 : ℝ) ^ 2 - 9 * (500000 : ℝ) ^ 2) ^ 2 <
      45 * (500000 : ℝ) ^ 4 := by norm_num
  have hden3 : (0 : ℝ) < 3 * (500000 : ℝ) ^ 2 := by norm_num
  have h5lt : (8 * (700629 : ℝ) ^ 2 - 9 * 500000 ^ 2) / (3 * 500000 ^ 2) < sqrt 5 := by
    rw [div_lt_iff₀ hden3]
    refine lt_of_sq_lt hNpos.le (by positivity) ?_
    have hright : (sqrt 5 * (3 * (500000 : ℝ) ^ 2)) ^ 2 = 45 * (500000 : ℝ) ^ 4 := by
      rw [mul_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)]
      ring
    linarith [hNsq, hright]
  have hmul : 8 * (700629 : ℝ) ^ 2 - 9 * 500000 ^ 2 < sqrt 5 * (3 * 500000 ^ 2) := by
    rwa [div_lt_iff₀ hden3] at h5lt
  have h8 : 8 * ((700629 : ℝ) / 500000) ^ 2 < 3 * (3 + sqrt 5) := by
    have hpow : ((700629 : ℝ) / 500000) ^ 2 = (700629 : ℝ) ^ 2 / (500000 : ℝ) ^ 2 := by ring
    rw [hpow, ← mul_div_assoc]
    rw [div_lt_iff₀ (by norm_num : (0 : ℝ) < (500000 : ℝ) ^ 2)]
    linarith [hmul]
  have hlt : ((700629 : ℝ) / 500000) ^ 2 < dodecaNear ^ 2 := by
    rw [hsq]
    exact (lt_div_iff₀ (by norm_num : (0 : ℝ) < 8)).mpr (by
      simpa [mul_comm] using h8)
  exact lt_of_sq_lt (by norm_num) (by unfold dodecaNear; exact sqrt_nonneg _) hlt

private theorem sqrt_three_div_two_gt_34641 : (34641 : ℝ) / 40000 < sqrt 3 / 2 := by
  have hsq : ((34641 : ℝ) / 40000) ^ 2 < (sqrt 3 / 2) ^ 2 := by
    rw [div_pow, div_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num
  exact lt_of_sq_lt (by norm_num) (div_nonneg (sqrt_nonneg _) (by norm_num)) hsq

private theorem sqrt_three_div_two_lt_433013 : sqrt 3 / 2 < (433013 : ℝ) / 500000 := by
  have hsq : (sqrt 3 / 2) ^ 2 < ((433013 : ℝ) / 500000) ^ 2 := by
    rw [div_pow, div_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num
  exact lt_of_sq_lt (div_nonneg (sqrt_nonneg _) (by norm_num)) (by norm_num) hsq

private theorem sqrt_six_div_four_gt_153093 : (153093 : ℝ) / 250000 < sqrt 6 / 4 := by
  have hsq : ((153093 : ℝ) / 250000) ^ 2 < (sqrt 6 / 4) ^ 2 := by
    rw [div_pow, div_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 6)]
    norm_num
  exact lt_of_sq_lt (by norm_num) (div_nonneg (sqrt_nonneg _) (by norm_num)) hsq

private theorem sqrt_six_div_four_lt_612373 : sqrt 6 / 4 < (612373 : ℝ) / 1000000 := by
  have hsq : (sqrt 6 / 4) ^ 2 < ((612373 : ℝ) / 1000000) ^ 2 := by
    rw [div_pow, div_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 6)]
    norm_num
  exact lt_of_sq_lt (div_nonneg (sqrt_nonneg _) (by norm_num)) (by norm_num) hsq

private theorem dodecaFarScale_gt_535233 : (535233 : ℝ) / 1000000 < dodecaFarScale := by
  have h5lt : sqrt 5 < 3 := by
    rw [← sqrt_sq (by norm_num : (0 : ℝ) ≤ 3), sqrt_lt_sqrt_iff (by positivity)]
    norm_num
  have hsq : dodecaFarScale ^ 2 = 3 * (3 - sqrt 5) / 8 := by
    unfold dodecaFarScale
    exact sq_sqrt (by nlinarith [h5lt])
  have hrhs : (0 : ℝ) < 9 * (1000000 : ℝ) ^ 2 - 8 * 535233 ^ 2 := by norm_num
  have hcmp : 45 * (1000000 : ℝ) ^ 4 < (9 * (1000000 : ℝ) ^ 2 - 8 * 535233 ^ 2) ^ 2 := by
    norm_num
  have hden : (0 : ℝ) < 3 * (1000000 : ℝ) ^ 2 := by norm_num
  have hsqrt : sqrt 5 < (9 * (1000000 : ℝ) ^ 2 - 8 * 535233 ^ 2) / (3 * 1000000 ^ 2) := by
    refine lt_of_sq_lt (sqrt_nonneg _) (div_nonneg hrhs.le (by norm_num)) ?_
    rw [sq_sqrt (by norm_num : (0 : ℝ) ≤ 5), div_pow]
    rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < (3 * (1000000 : ℝ) ^ 2) ^ 2)]
    have hpow : (3 * (1000000 : ℝ) ^ 2) ^ 2 = 9 * (1000000 : ℝ) ^ 4 := by ring
    linarith [hcmp, hpow]
  have hmul : sqrt 5 * (3 * (1000000 : ℝ) ^ 2) < 9 * 1000000 ^ 2 - 8 * 535233 ^ 2 := by
    rwa [lt_div_iff₀ hden] at hsqrt
  have h8 : 8 * ((535233 : ℝ) / 1000000) ^ 2 < 3 * (3 - sqrt 5) := by
    have hpow : ((535233 : ℝ) / 1000000) ^ 2 =
        (535233 : ℝ) ^ 2 / (1000000 : ℝ) ^ 2 := by ring
    rw [hpow, ← mul_div_assoc]
    rw [div_lt_iff₀ (by norm_num : (0 : ℝ) < (1000000 : ℝ) ^ 2)]
    linarith [hmul]
  have hlt : ((535233 : ℝ) / 1000000) ^ 2 < dodecaFarScale ^ 2 := by
    rw [hsq]
    exact (lt_div_iff₀ (by norm_num : (0 : ℝ) < 8)).mpr (by simpa [mul_comm] using h8)
  exact lt_of_sq_lt (by norm_num) (by unfold dodecaFarScale; exact sqrt_nonneg _) hlt

private theorem dodecaFarScale_lt_267617 : dodecaFarScale < (267617 : ℝ) / 500000 := by
  have h5lt : sqrt 5 < 3 := by
    rw [← sqrt_sq (by norm_num : (0 : ℝ) ≤ 3), sqrt_lt_sqrt_iff (by positivity)]
    norm_num
  have hsq : dodecaFarScale ^ 2 = 3 * (3 - sqrt 5) / 8 := by
    unfold dodecaFarScale
    exact sq_sqrt (by nlinarith [h5lt])
  have hrhs : (0 : ℝ) < 9 * (500000 : ℝ) ^ 2 - 8 * 267617 ^ 2 := by norm_num
  have hcmp : (9 * (500000 : ℝ) ^ 2 - 8 * 267617 ^ 2) ^ 2 < 45 * (500000 : ℝ) ^ 4 := by
    norm_num
  have hden : (0 : ℝ) < 3 * (500000 : ℝ) ^ 2 := by norm_num
  have hsqrt : (9 * (500000 : ℝ) ^ 2 - 8 * 267617 ^ 2) / (3 * (500000 : ℝ) ^ 2) < sqrt 5 := by
    refine lt_of_sq_lt (div_nonneg hrhs.le (by norm_num)) (sqrt_nonneg _) ?_
    rw [div_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)]
    rw [div_lt_iff₀ (by norm_num : (0 : ℝ) < (3 * (500000 : ℝ) ^ 2) ^ 2)]
    have hfive : (5 : ℝ) * (3 * (500000 : ℝ) ^ 2) ^ 2 = 45 * (500000 : ℝ) ^ 4 := by ring
    linarith [hcmp, hfive]
  have hmul : 9 * (500000 : ℝ) ^ 2 - 8 * 267617 ^ 2 <
      sqrt 5 * (3 * (500000 : ℝ) ^ 2) := by
    rwa [div_lt_iff₀ hden] at hsqrt
  have hstep : 3 * (3 - sqrt 5) < 8 * ((267617 : ℝ) / 500000) ^ 2 := by
    have hpow : ((267617 : ℝ) / 500000) ^ 2 = (267617 : ℝ) ^ 2 / (500000 : ℝ) ^ 2 := by ring
    rw [hpow, ← mul_div_assoc]
    rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < (500000 : ℝ) ^ 2)]
    linarith [hmul]
  have hlt : dodecaFarScale ^ 2 < ((267617 : ℝ) / 500000) ^ 2 := by
    rw [hsq]
    exact (div_lt_iff₀ (by norm_num : (0 : ℝ) < 8)).mpr (by simpa [mul_comm] using hstep)
  exact lt_of_sq_lt (by unfold dodecaFarScale; exact sqrt_nonneg _) (by norm_num) hlt

/-! ### Comparing a chord derivative with rational bounds -/

private lemma mul_le_lt_of_pos {a b c d : ℝ} (hab : a ≤ b) (hcd : c < d)
    (hc : 0 < c) (hb : 0 < b) : a * c < b * d := by
  rcases lt_or_eq_of_le hab with hlt | rfl
  · exact mul_lt_mul hlt hcd.le hc hb.le
  · exact mul_lt_mul_of_pos_left hcd hb

private lemma mul4_lt {a b c d A B C D : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hA : a < A) (hB : b < B) (hC : c < C) (hD : d < D) :
    a * b * c * d < A * B * C * D := by
  have h1 : a * b < A * B :=
    mul_lt_mul hA hB.le hb (le_of_lt (lt_trans ha hA))
  have h1pos : 0 < a * b := mul_pos ha hb
  have hAB : 0 < A * B := lt_trans h1pos h1
  have h2 : a * b * c < A * B * C := mul_lt_mul h1 hC.le hc hAB.le
  have h2pos : 0 < a * b * c := mul_pos h1pos hc
  have hABC : 0 < A * B * C := lt_trans h2pos h2
  exact mul_lt_mul h2 hD.le hd hABC.le

private lemma mul4_le_lt {a b c d A B C D : ℝ}
    (ha0 : 0 < a) (hb0 : 0 < b) (hc0 : 0 < c) (hd0 : 0 < d) (hA0 : 0 < A)
    (ha : a ≤ A) (hb : b < B) (hc : c < C) (hd : d < D) :
    a * b * c * d < A * B * C * D := by
  have h1 : a * b < A * B := mul_le_lt_of_pos ha hb hb0 hA0
  have h1pos : 0 < a * b := mul_pos ha0 hb0
  have hAB : 0 < A * B := lt_trans h1pos h1
  have h2 : a * b * c < A * B * C := mul_lt_mul h1 hc.le hc0 hAB.le
  have h2pos : 0 < a * b * c := mul_pos h1pos hc0
  have hABC : 0 < A * B * C := lt_trans h2pos h2
  exact mul_lt_mul h2 hd.le hd0 hABC.le

private lemma div_lt_div_num_den {n N d D : ℝ}
    (hn : 0 < n) (hd : 0 < d) (hN : n < N) (hD : d < D) : n / D < N / d := by
  have hD0 : 0 < D := lt_trans hd hD
  rw [div_lt_div_iff₀ hD0 hd]
  exact lt_trans (mul_lt_mul_of_pos_right hN hd)
    (mul_lt_mul_of_pos_left hD (lt_trans hn hN))

private lemma sq_lt_of_lt_pos {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) : a ^ 2 < b ^ 2 := by
  nlinarith

private lemma one_lt_pi_div_two : (1 : ℝ) < π / 2 := by
  rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
  linarith [pi_gt_three]

private lemma chordAmp_strictMono_unit {a b : ℝ} (ha : 0 < a) (hb : b ≤ 1) (hab : a < b) :
    chordAmp a < chordAmp b := by
  have hbpi : b ≤ π / 2 := le_trans hb (le_of_lt one_lt_pi_div_two)
  exact strictMonoOn_chordAmp ⟨ha.le, le_trans (le_of_lt hab) hbpi⟩
    ⟨le_of_lt (lt_trans ha hab), hbpi⟩ hab

private lemma gamma_strictAnti_unit {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) (hab : a < b) :
    gammaSEqual b < gammaSEqual a := by
  have hπ : (1 : ℝ) < π := by linarith [pi_gt_three]
  have hbπ : b ≤ π := le_trans hb (le_of_lt hπ)
  have haI : a ∈ Icc (((2 * 0 : ℕ) : ℝ) * π) (((2 * 0 : ℕ) : ℝ) * π + π) := by
    simpa using ⟨ha, le_trans (le_of_lt hab) hbπ⟩
  have hbI : b ∈ Icc (((2 * 0 : ℕ) : ℝ) * π) (((2 * 0 : ℕ) : ℝ) * π + π) := by
    simpa using ⟨le_trans ha (le_of_lt hab), hbπ⟩
  exact strictAntiOn_gammaSEqual_even 0 haI hbI hab

private lemma slope_strictAnti_phase {a b : ℝ} (ha : 0 < a) (hb : b < resonanceRoot1)
    (hab : a < b) : chordSlope b < chordSlope a :=
  strictAntiOn_chordSlope ⟨ha, lt_trans hab hb⟩ ⟨lt_trans ha hab, hb⟩ hab

private lemma slope_gt_quot {t AHi GLo : ℝ}
    (hAHi : chordAmp t < AHi) (hGLo : GLo < gammaSEqual t)
    (hA0 : 0 < chordAmp t) (hG0 : 0 < GLo) : GLo / AHi < chordSlope t := by
  have hG : 0 < gammaSEqual t := lt_trans hG0 hGLo
  have hAHi0 : 0 < AHi := lt_trans hA0 hAHi
  have hAmp : 0 < cosh t * sin t := by simpa [chordAmp] using hA0
  have hlt : cosh t * sin t < AHi := by simpa [chordAmp] using hAHi
  rw [chordSlope, div_lt_div_iff₀ hAHi0 hAmp]
  exact lt_trans (mul_lt_mul_of_pos_right hGLo hAmp) (mul_lt_mul_of_pos_left hlt hG)

private lemma slope_lt_quot {t ALo GHi : ℝ}
    (hALo : ALo < chordAmp t) (hGHi : gammaSEqual t < GHi)
    (hA0 : 0 < ALo) (hG0 : 0 < gammaSEqual t) : chordSlope t < GHi / ALo := by
  have hAmp : 0 < cosh t * sin t := by simpa [chordAmp] using lt_trans hA0 hALo
  have hlt : ALo < cosh t * sin t := by simpa [chordAmp] using hALo
  rw [chordSlope, div_lt_div_iff₀ hAmp hA0]
  exact lt_trans (mul_lt_mul_of_pos_left hlt hG0) (mul_lt_mul_of_pos_right hGHi hAmp)

private theorem deriv_scaledRatio_eq {c x : ℝ}
    (hx0 : 0 < x) (hcx0 : 0 < c * x) (hπx : x < π) (hπc : c * x < π)
    (hgc : gammaSEqual (c * x) ≠ 0) :
    deriv (scaledRatio c) x =
      2 * chordAmp x * chordAmp (c * x) *
        (c * chordSlope x - chordSlope (c * x)) / gammaSEqual (c * x) ^ 2 := by
  rw [(hasDerivAt_scaledRatio hgc).deriv, scaledRatio_numer_eq hx0 hcx0 hπx hπc]
  unfold chordAmp
  rfl

private lemma contrib_eq {k c x : ℝ}
    (hx0 : 0 < x) (hcx0 : 0 < c * x) (hπx : x < π) (hπc : c * x < π)
    (hgc : gammaSEqual (c * x) ≠ 0) :
    k * deriv (scaledRatio c) x =
      (k * 2 * chordAmp x * chordAmp (c * x) *
        (c * chordSlope x - chordSlope (c * x))) / gammaSEqual (c * x) ^ 2 := by
  have hden : gammaSEqual (c * x) ^ 2 ≠ 0 := pow_ne_zero 2 hgc
  rw [deriv_scaledRatio_eq hx0 hcx0 hπx hπc hgc]
  field_simp [hden]

private theorem hasDerivAt_dodecaResponse {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) dodecaWall) :
    HasDerivAt dodecaResponse
      ((3 / 2 * dodecaNear) * deriv (scaledRatio dodecaNear) x +
        (3 * sqrt 3 / 2) * deriv (scaledRatio (sqrt 3 / 2)) x +
        (3 * sqrt 6 / 4) * deriv (scaledRatio (sqrt 6 / 4)) x +
        (3 / 2 * dodecaFarScale) * deriv (scaledRatio dodecaFarScale) x +
        (1 / 4) * deriv (scaledRatio (1 / 2)) x) x := by
  have hsc := dodeca_scales_lt_near
  have hnear := (gamma_pos_dodeca_phase (by linarith [dodecaNear_gt_one]) le_rfl hx).ne'
  have h3 := (gamma_pos_dodeca_phase
    (div_pos (sqrt_pos.mpr (by norm_num)) (by norm_num)) hsc.1.le hx).ne'
  have h6 := (gamma_pos_dodeca_phase
    (div_pos (sqrt_pos.mpr (by norm_num)) (by norm_num)) hsc.2.1.le hx).ne'
  have hfar : gammaSEqual (dodecaFarScale * x) ≠ 0 := by
    simpa only [dodecaFarScale] using
      (gamma_pos_dodeca_phase (sqrt_pos.mpr
        (by nlinarith [sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)])) hsc.2.2.1.le hx).ne'
  have hhalf := (gamma_pos_dodeca_phase (by norm_num) hsc.2.2.2.le hx).ne'
  have dNear : HasDerivAt (fun y => (3 / 2 * dodecaNear) * scaledRatio dodecaNear y)
      ((3 / 2 * dodecaNear) * deriv (scaledRatio dodecaNear) x) x := by
    refine ((hasDerivAt_scaledRatio hnear).const_mul (3 / 2 * dodecaNear)).congr_deriv ?_
    rw [← (hasDerivAt_scaledRatio hnear).deriv]
  have d3 : HasDerivAt (fun y => (3 * sqrt 3 / 2) * scaledRatio (sqrt 3 / 2) y)
      ((3 * sqrt 3 / 2) * deriv (scaledRatio (sqrt 3 / 2)) x) x := by
    refine ((hasDerivAt_scaledRatio h3).const_mul (3 * sqrt 3 / 2)).congr_deriv ?_
    rw [← (hasDerivAt_scaledRatio h3).deriv]
  have d6 : HasDerivAt (fun y => (3 * sqrt 6 / 4) * scaledRatio (sqrt 6 / 4) y)
      ((3 * sqrt 6 / 4) * deriv (scaledRatio (sqrt 6 / 4)) x) x := by
    refine ((hasDerivAt_scaledRatio h6).const_mul (3 * sqrt 6 / 4)).congr_deriv ?_
    rw [← (hasDerivAt_scaledRatio h6).deriv]
  have dFar : HasDerivAt (fun y => (3 / 2 * dodecaFarScale) * scaledRatio dodecaFarScale y)
      ((3 / 2 * dodecaFarScale) * deriv (scaledRatio dodecaFarScale) x) x := by
    refine ((hasDerivAt_scaledRatio hfar).const_mul (3 / 2 * dodecaFarScale)).congr_deriv ?_
    rw [← (hasDerivAt_scaledRatio hfar).deriv]
  have dHalf : HasDerivAt (fun y => (1 / 4) * scaledRatio (1 / 2) y)
      ((1 / 4) * deriv (scaledRatio (1 / 2)) x) x := by
    refine ((hasDerivAt_scaledRatio hhalf).const_mul (1 / 4)).congr_deriv ?_
    rw [← (hasDerivAt_scaledRatio hhalf).deriv]
  unfold dodecaResponse
  exact (((dNear.add d3).add d6).add dFar).add dHalf

private lemma near_contrib_gt
    {x a pNa : ℝ} {aALo nALo nGHi bGLo bAHi : ℝ}
    (ha0 : 0 < a) (_hx0 : 0 < x) (hax : a < x) (hx1 : x ≤ 1)
    (hp0 : 0 < pNa) (_hp1 : pNa ≤ 1)
    (hpLe : pNa ≤ (700629 : ℝ) / 500000 * a)
    (hAa : aALo < chordAmp a) (hAa0 : 0 < aALo)
    (hAn : nALo < chordAmp pNa) (hAn0 : 0 < nALo)
    (hGn : gammaSEqual pNa < nGHi) (hGn0 : 0 < gammaSEqual pNa)
    (hbG0 : 0 < bGLo) (hbA0 : 0 < bAHi)
    (hSlo : bGLo / bAHi < chordSlope x)
    (hbr0 : 0 < (700629 : ℝ) / 500000 * (bGLo / bAHi) - nGHi / nALo)
    (hnx : dodecaNear * x < resonanceRoot1) (hγnx : 0 < gammaSEqual (dodecaNear * x)) :
    (((3 : ℝ) / 2) * ((700629 : ℝ) / 500000) * 2 * aALo * nALo *
        ((700629 : ℝ) / 500000 * (bGLo / bAHi) - nGHi / nALo)) / nGHi ^ 2 <
      ((3 / 2 * dodecaNear) * 2 * chordAmp x * chordAmp (dodecaNear * x) *
        (dodecaNear * chordSlope x - chordSlope (dodecaNear * x))) /
          gammaSEqual (dodecaNear * x) ^ 2 := by
  set nLo : ℝ := (700629 : ℝ) / 500000
  set brLo : ℝ := nLo * (bGLo / bAHi) - nGHi / nALo
  set br : ℝ := dodecaNear * chordSlope x - chordSlope (dodecaNear * x)
  have hnLo : nLo < dodecaNear := by
    simpa [nLo] using dodecaNear_gt_700629_500000
  have hnear0 : 0 < dodecaNear := by linarith [dodecaNear_gt_one]
  have h1 : nLo * a < dodecaNear * a := mul_lt_mul_of_pos_right hnLo ha0
  have h2 : dodecaNear * a < dodecaNear * x := mul_lt_mul_of_pos_left hax hnear0
  have hpnx : pNa < dodecaNear * x := lt_of_le_of_lt (by simpa [nLo] using hpLe) (lt_trans h1 h2)
  have hAx : aALo < chordAmp x := lt_trans hAa (chordAmp_strictMono_unit ha0 hx1 hax)
  have hnx1 : dodecaNear * x ≤ 1 := le_of_lt (lt_trans hnx resonanceRoot1_sharp_bounds.2)
  have hAnx : nALo < chordAmp (dodecaNear * x) :=
    lt_trans hAn (chordAmp_strictMono_unit hp0 hnx1 hpnx)
  have hSn : chordSlope (dodecaNear * x) < chordSlope pNa :=
    slope_strictAnti_phase hp0 hnx hpnx
  have hSq : chordSlope pNa < nGHi / nALo := slope_lt_quot hAn hGn hAn0 hGn0
  have hSnx : chordSlope (dodecaNear * x) < nGHi / nALo := lt_trans hSn hSq
  have hprod : nLo * (bGLo / bAHi) < dodecaNear * chordSlope x :=
    mul_lt_mul hnLo hSlo.le (div_pos hbG0 hbA0) hnear0.le
  have hbr : brLo < br := by
    simpa [brLo, br] using (by linarith [hprod, hSnx] : nLo * (bGLo / bAHi) - nGHi / nALo <
      dodecaNear * chordSlope x - chordSlope (dodecaNear * x))
  have hk0 : 0 < (3 : ℝ) / 2 * nLo := by unfold nLo; norm_num
  have hk : (3 : ℝ) / 2 * nLo < 3 / 2 * dodecaNear :=
    mul_lt_mul_of_pos_left hnLo (by norm_num)
  have h4 : (3 : ℝ) / 2 * nLo * aALo * nALo * brLo <
      (3 / 2 * dodecaNear) * chordAmp x * chordAmp (dodecaNear * x) * br :=
    mul4_lt hk0 hAa0 hAn0 (by simpa [brLo] using hbr0) hk hAx hAnx hbr
  have htwo : (0 : ℝ) < 2 := by norm_num
  have h4t : (3 : ℝ) / 2 * nLo * aALo * nALo * brLo * 2 <
      (3 / 2 * dodecaNear) * chordAmp x * chordAmp (dodecaNear * x) * br * 2 :=
    mul_lt_mul_of_pos_right h4 htwo
  have hnumL : (3 : ℝ) / 2 * nLo * 2 * aALo * nALo * brLo =
      (3 : ℝ) / 2 * nLo * aALo * nALo * brLo * 2 := by ring
  have hnumR : (3 / 2 * dodecaNear) * 2 * chordAmp x * chordAmp (dodecaNear * x) * br =
      (3 / 2 * dodecaNear) * chordAmp x * chordAmp (dodecaNear * x) * br * 2 := by ring
  have hnum : (3 : ℝ) / 2 * nLo * 2 * aALo * nALo * brLo <
      (3 / 2 * dodecaNear) * 2 * chordAmp x * chordAmp (dodecaNear * x) * br := by
    linarith [h4t, hnumL, hnumR]
  have hγp : gammaSEqual (dodecaNear * x) < gammaSEqual pNa :=
    gamma_strictAnti_unit hp0.le hnx1 hpnx
  have hγlt : gammaSEqual (dodecaNear * x) < nGHi := lt_trans hγp hGn
  have hden : gammaSEqual (dodecaNear * x) ^ 2 < nGHi ^ 2 := sq_lt_of_lt_pos hγnx.le hγlt
  have hnpos : 0 < (3 : ℝ) / 2 * nLo * 2 * aALo * nALo * brLo :=
    mul_pos (mul_pos (mul_pos (mul_pos hk0 htwo) hAa0) hAn0) (by simpa [brLo] using hbr0)
  simpa [nLo, brLo, br] using div_lt_div_num_den hnpos (sq_pos_of_pos hγnx) hnum hden

private lemma far_contrib_lt
    {x a b p q c cLo cHi k kHi : ℝ} {bAHi bGLo pALo pGHi qAHi qGLo : ℝ}
    (ha0 : 0 < a) (hx0 : 0 < x) (hax : a < x) (hxb : x ≤ b) (hb1 : b ≤ 1)
    (hxR : x < resonanceRoot1) (hp0 : 0 < p) (hq1 : q ≤ 1)
    (hc0 : 0 < c) (hc1 : c < 1) (hcLo : cLo ≤ c) (hcHi : c ≤ cHi)
    (hk0 : 0 < k) (hkHi : 0 < kHi) (hk : k ≤ kHi)
    (hpLe : p ≤ cLo * a) (hqGe : cHi * b ≤ q)
    (hbA : chordAmp b < bAHi) (hpA : pALo < chordAmp p) (hpA0 : 0 < pALo)
    (hpG : gammaSEqual p < pGHi) (hpG0 : 0 < gammaSEqual p)
    (hqA : chordAmp q < qAHi) (hqG : qGLo < gammaSEqual q) (hqG0 : 0 < qGLo)
    (hbG0 : 0 < bGLo) (hbAHi0 : 0 < bAHi) (hSlo : bGLo / bAHi < chordSlope x)
    (_hbr0 : 0 < pGHi / pALo - cLo * (bGLo / bAHi))
    (hcx1 : c * x < resonanceRoot1) (_hγcx : 0 < gammaSEqual (c * x)) :
    (k * 2 * chordAmp x * chordAmp (c * x) *
        (chordSlope (c * x) - c * chordSlope x)) / gammaSEqual (c * x) ^ 2 <
      (kHi * 2 * bAHi * qAHi * (pGHi / pALo - cLo * (bGLo / bAHi))) / qGLo ^ 2 := by
  have hb0 : 0 < b := lt_of_lt_of_le hx0 hxb
  have hpx : p < c * x := by
    have hpa : p ≤ c * a := le_trans hpLe (mul_le_mul_of_nonneg_right hcLo ha0.le)
    exact lt_of_le_of_lt hpa (mul_lt_mul_of_pos_left hax hc0)
  have hcxq : c * x ≤ q := by
    have hxbc : c * x ≤ c * b := mul_le_mul_of_nonneg_left hxb hc0.le
    have hcb : c * b ≤ cHi * b := mul_le_mul_of_nonneg_right hcHi hb0.le
    exact le_trans (le_trans hxbc hcb) hqGe
  have hAxb : chordAmp x ≤ chordAmp b := by
    rcases lt_or_eq_of_le hxb with hlt | rfl
    · exact (chordAmp_strictMono_unit hx0 hb1 hlt).le
    · rfl
  have hAx : chordAmp x < bAHi := lt_of_le_of_lt hAxb hbA
  have hcx0 : 0 < c * x := mul_pos hc0 hx0
  have hAcx : chordAmp (c * x) < qAHi := by
    rcases lt_or_eq_of_le hcxq with hlt | rfl
    · exact lt_trans (chordAmp_strictMono_unit hcx0 hq1 hlt) hqA
    · exact hqA
  have hSp : chordSlope (c * x) < chordSlope p := slope_strictAnti_phase hp0 hcx1 hpx
  have hScx : chordSlope (c * x) < pGHi / pALo :=
    lt_trans hSp (slope_lt_quot hpA hpG hpA0 hpG0)
  have hcs : cLo * (bGLo / bAHi) < c * chordSlope x :=
    mul_le_lt_of_pos hcLo hSlo (div_pos hbG0 hbAHi0) hc0
  set br : ℝ := chordSlope (c * x) - c * chordSlope x
  set brHi : ℝ := pGHi / pALo - cLo * (bGLo / bAHi)
  have hbr : br < brHi := by
    simpa [br, brHi] using (by linarith [hScx, hcs] :
      chordSlope (c * x) - c * chordSlope x < pGHi / pALo - cLo * (bGLo / bAHi))
  have hSpos : 0 < chordSlope x := chordSlope_pos hx0 hxR
  have hbrPos : 0 < br := by
    have hSgt : chordSlope x < chordSlope (c * x) :=
      slope_strictAnti_phase hcx0 hxR (by nlinarith [hc1, hx0])
    have hcmul : c * chordSlope x < chordSlope x := by nlinarith [hc1, hSpos]
    unfold br
    linarith
  have hx1 : x ≤ 1 := le_trans hxb hb1
  have hπ : x < π := lt_of_le_of_lt hx1 (by linarith [pi_gt_three])
  have hπc : c * x < π :=
    lt_trans hcx1 (lt_trans resonanceRoot1_sharp_bounds.2 (by linarith [pi_gt_three]))
  have hAx0 : 0 < chordAmp x := by
    unfold chordAmp
    exact mul_pos (cosh_pos x) (sin_pos_of_pos_of_lt_pi hx0 hπ)
  have hAcx0 : 0 < chordAmp (c * x) := by
    unfold chordAmp
    exact mul_pos (cosh_pos _) (sin_pos_of_pos_of_lt_pi hcx0 hπc)
  have h4 : k * chordAmp x * chordAmp (c * x) * br < kHi * bAHi * qAHi * brHi :=
    mul4_le_lt hk0 hAx0 hAcx0 hbrPos hkHi hk hAx hAcx hbr
  have htwo : (0 : ℝ) < 2 := by norm_num
  have h4t : k * chordAmp x * chordAmp (c * x) * br * 2 <
      kHi * bAHi * qAHi * brHi * 2 := mul_lt_mul_of_pos_right h4 htwo
  have hnumL : k * 2 * chordAmp x * chordAmp (c * x) * br =
      k * chordAmp x * chordAmp (c * x) * br * 2 := by ring
  have hnumR : kHi * 2 * bAHi * qAHi * brHi = kHi * bAHi * qAHi * brHi * 2 := by ring
  have hnum : k * 2 * chordAmp x * chordAmp (c * x) * br <
      kHi * 2 * bAHi * qAHi * brHi := by linarith [h4t, hnumL, hnumR]
  have hγ : qGLo < gammaSEqual (c * x) := by
    rcases lt_or_eq_of_le hcxq with hlt | rfl
    · exact lt_trans hqG (gamma_strictAnti_unit hcx0.le hq1 hlt)
    · exact hqG
  have hden : qGLo ^ 2 < gammaSEqual (c * x) ^ 2 := sq_lt_of_lt_pos hqG0.le hγ
  have hnpos : 0 < k * 2 * chordAmp x * chordAmp (c * x) * br :=
    mul_pos (mul_pos (mul_pos (mul_pos hk0 htwo) hAx0) hAcx0) (by simpa [br] using hbrPos)
  simpa [br, brHi] using
    div_lt_div_num_den hnpos (sq_pos_of_pos hqG0) hnum hden

/-! ### The response derivative on the outer side of the nearest chord -/

private noncomputable def nearContrib (x : ℝ) : ℝ :=
  ((3 / 2 * dodecaNear) * 2 * chordAmp x * chordAmp (dodecaNear * x) *
    (dodecaNear * chordSlope x - chordSlope (dodecaNear * x))) /
      gammaSEqual (dodecaNear * x) ^ 2

private noncomputable def farContrib (k c x : ℝ) : ℝ :=
  (k * 2 * chordAmp x * chordAmp (c * x) *
    (chordSlope (c * x) - c * chordSlope x)) / gammaSEqual (c * x) ^ 2

private lemma scaledPhase_lt_firstNode {s x : ℝ} (hs : s ≤ dodecaNear)
    (hx : x ∈ Ioo (0 : ℝ) dodecaWall) : s * x < resonanceRoot1 := by
  have hpos : 0 < dodecaNear := by linarith [dodecaNear_gt_one]
  have hx2 : x < resonanceRoot1 / dodecaNear := by simpa [dodecaWall] using hx.2
  have hwall : dodecaNear * x < resonanceRoot1 := by
    rw [lt_div_iff₀ hpos] at hx2
    simpa [mul_comm] using hx2
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hs hx.1.le) hwall

private lemma phase_lt_pi {t : ℝ} (ht : t < resonanceRoot1) : t < π :=
  lt_trans ht (lt_trans resonanceRoot1_sharp_bounds.2 (by linarith [pi_gt_three]))

private lemma near_term_eq {x : ℝ}
    (hx0 : 0 < x) (hn0 : 0 < dodecaNear * x) (hπx : x < π) (hπn : dodecaNear * x < π)
    (hgc : gammaSEqual (dodecaNear * x) ≠ 0) :
    (3 / 2 * dodecaNear) * deriv (scaledRatio dodecaNear) x = nearContrib x := by
  unfold nearContrib
  exact contrib_eq hx0 hn0 hπx hπn hgc

private lemma signed_far_eq {k c x : ℝ}
    (hx0 : 0 < x) (hcx0 : 0 < c * x) (hπx : x < π) (hπc : c * x < π)
    (hgc : gammaSEqual (c * x) ≠ 0) :
    k * deriv (scaledRatio c) x = -farContrib k c x := by
  unfold farContrib
  rw [contrib_eq hx0 hcx0 hπx hπc hgc]
  have hden : gammaSEqual (c * x) ^ 2 ≠ 0 := pow_ne_zero 2 hgc
  field_simp [hden]
  ring

private lemma deriv_dodecaResponse_split {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) dodecaWall) :
    deriv dodecaResponse x =
      nearContrib x
        - farContrib (3 * sqrt 3 / 2) (sqrt 3 / 2) x
        - farContrib (3 * sqrt 6 / 4) (sqrt 6 / 4) x
        - farContrib (3 / 2 * dodecaFarScale) dodecaFarScale x
        - farContrib (1 / 4) (1 / 2) x := by
  have hsc := dodeca_scales_lt_near
  have hx0 := hx.1
  have hπx : x < π := by
    have h1 : (1 : ℝ) ≤ dodecaNear := le_of_lt dodecaNear_gt_one
    exact phase_lt_pi (by simpa [one_mul] using scaledPhase_lt_firstNode h1 hx)
  have hπn : dodecaNear * x < π := phase_lt_pi (scaledPhase_lt_firstNode le_rfl hx)
  have hπ3 : (sqrt 3 / 2) * x < π := phase_lt_pi (scaledPhase_lt_firstNode hsc.1.le hx)
  have hπ6 : (sqrt 6 / 4) * x < π := phase_lt_pi (scaledPhase_lt_firstNode hsc.2.1.le hx)
  have hπf : dodecaFarScale * x < π :=
    phase_lt_pi (scaledPhase_lt_firstNode hsc.2.2.1.le hx)
  have hπh : (1 / 2) * x < π := phase_lt_pi (scaledPhase_lt_firstNode hsc.2.2.2.le hx)
  have hn0 : 0 < dodecaNear * x := mul_pos (by linarith [dodecaNear_gt_one]) hx0
  have h30 : 0 < (sqrt 3 / 2) * x :=
    mul_pos (lt_trans (by norm_num) sqrt_three_div_two_gt_34641) hx0
  have h60 : 0 < (sqrt 6 / 4) * x :=
    mul_pos (lt_trans (by norm_num) sqrt_six_div_four_gt_153093) hx0
  have hf0 : 0 < dodecaFarScale * x :=
    mul_pos (lt_trans (by norm_num) dodecaFarScale_gt_535233) hx0
  have hh0 : 0 < (1 / 2) * x := mul_pos (by norm_num) hx0
  have hnear := (gamma_pos_dodeca_phase (by linarith [dodecaNear_gt_one]) le_rfl hx).ne'
  have h3 := (gamma_pos_dodeca_phase
    (div_pos (sqrt_pos.mpr (by norm_num)) (by norm_num)) hsc.1.le hx).ne'
  have h6 := (gamma_pos_dodeca_phase
    (div_pos (sqrt_pos.mpr (by norm_num)) (by norm_num)) hsc.2.1.le hx).ne'
  have hfar : gammaSEqual (dodecaFarScale * x) ≠ 0 := by
    simpa only [dodecaFarScale] using
      (gamma_pos_dodeca_phase (sqrt_pos.mpr
        (by nlinarith [sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)])) hsc.2.2.1.le hx).ne'
  have hhalf := (gamma_pos_dodeca_phase (by norm_num) hsc.2.2.2.le hx).ne'
  have hN := near_term_eq hx0 hn0 hπx hπn hnear
  have hS3 := signed_far_eq (k := 3 * sqrt 3 / 2) hx0 h30 hπx hπ3 h3
  have hS6 := signed_far_eq (k := 3 * sqrt 6 / 4) hx0 h60 hπx hπ6 h6
  have hSF := signed_far_eq (k := 3 / 2 * dodecaFarScale) hx0 hf0 hπx hπf hfar
  have hSH := signed_far_eq (k := 1 / 4) hx0 hh0 hπx hπh hhalf
  rw [(hasDerivAt_dodecaResponse hx).deriv, hN, hS3, hS6, hSF, hSH]
  ring

private lemma deriv_pos_of_gap {x L R3 R6 Rf Rh : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) dodecaWall)
    (hN : L < nearContrib x)
    (h3 : farContrib (3 * sqrt 3 / 2) (sqrt 3 / 2) x < R3)
    (h6 : farContrib (3 * sqrt 6 / 4) (sqrt 6 / 4) x < R6)
    (hf : farContrib (3 / 2 * dodecaFarScale) dodecaFarScale x < Rf)
    (hh : farContrib (1 / 4) (1 / 2) x < Rh)
    (hgap : R3 + R6 + Rf + Rh < L) :
    0 < deriv dodecaResponse x := by
  have hs := deriv_dodecaResponse_split hx
  linarith

private lemma dodecaWall_lt_firstNode : dodecaWall < resonanceRoot1 := by
  have hx1pos : 0 < resonanceRoot1 := lt_trans (by positivity) resonanceRoot1_sharp_bounds.1
  have hnear : (0 : ℝ) < dodecaNear := by linarith [dodecaNear_gt_one]
  unfold dodecaWall
  rw [div_lt_iff₀ hnear]
  nlinarith [dodecaNear_gt_one, hx1pos]

private lemma slope_below_end {x b GLo AHi : ℝ}
    (hx0 : 0 < x) (hxb : x ≤ b) (hbR : b < resonanceRoot1)
    (hA : chordAmp b < AHi) (hG : GLo < gammaSEqual b)
    (hA0 : 0 < chordAmp b) (hG0 : 0 < GLo) :
    GLo / AHi < chordSlope x := by
  have hSb : GLo / AHi < chordSlope b := slope_gt_quot hA hG hA0 hG0
  rcases lt_or_eq_of_le hxb with hlt | rfl
  · exact lt_trans hSb (slope_strictAnti_phase hx0 hbR hlt)
  · exact hSb

private lemma s3_weight_le : 3 * sqrt 3 / 2 ≤ 3 * ((433013 : ℝ) / 500000) := by
  have hlt : 3 * (sqrt 3 / 2) < 3 * ((433013 : ℝ) / 500000) :=
    mul_lt_mul_of_pos_left sqrt_three_div_two_lt_433013 (by norm_num : (0 : ℝ) < 3)
  linarith [show 3 * sqrt 3 / 2 = 3 * (sqrt 3 / 2) by ring]

private lemma s6_weight_le : 3 * sqrt 6 / 4 ≤ 3 * ((612373 : ℝ) / 1000000) := by
  have hlt : 3 * (sqrt 6 / 4) < 3 * ((612373 : ℝ) / 1000000) :=
    mul_lt_mul_of_pos_left sqrt_six_div_four_lt_612373 (by norm_num : (0 : ℝ) < 3)
  linarith [show 3 * sqrt 6 / 4 = 3 * (sqrt 6 / 4) by ring]

private lemma far_weight_le :
    3 / 2 * dodecaFarScale ≤ 3 / 2 * ((267617 : ℝ) / 500000) :=
  (mul_lt_mul_of_pos_left dodecaFarScale_lt_267617 (by norm_num : (0 : ℝ) < 3 / 2)).le

private lemma sqrt_three_div_two_lt_one : sqrt 3 / 2 < 1 :=
  lt_trans sqrt_three_div_two_lt_433013 (by norm_num)

private lemma sqrt_six_div_four_lt_one : sqrt 6 / 4 < 1 :=
  lt_trans sqrt_six_div_four_lt_612373 (by norm_num)

private lemma near_lower
    {x a b pNa : ℝ} {aALo nALo nGHi bGLo bAHi : ℝ}
    (ha0 : 0 < a) (hx0 : 0 < x) (hax : a < x) (hx1 : x ≤ 1)
    (hxb : x ≤ b) (hbR : b < resonanceRoot1)
    (hp0 : 0 < pNa) (hp1 : pNa ≤ 1)
    (hpLe : pNa ≤ (700629 : ℝ) / 500000 * a)
    (hAa : aALo < chordAmp a) (hAa0 : 0 < aALo)
    (hAn : nALo < chordAmp pNa) (hAn0 : 0 < nALo)
    (hGn : gammaSEqual pNa < nGHi) (hGn0 : 0 < gammaSEqual pNa)
    (hAb : chordAmp b < bAHi) (hAb0 : 0 < chordAmp b)
    (hGb : bGLo < gammaSEqual b)
    (hbG0 : 0 < bGLo) (hbA0 : 0 < bAHi)
    (hbr0 : 0 < (700629 : ℝ) / 500000 * (bGLo / bAHi) - nGHi / nALo)
    (hxI : x ∈ Ioo (0 : ℝ) dodecaWall) :
    (((3 : ℝ) / 2) * ((700629 : ℝ) / 500000) * 2 * aALo * nALo *
        ((700629 : ℝ) / 500000 * (bGLo / bAHi) - nGHi / nALo)) / nGHi ^ 2 <
      nearContrib x := by
  have hSlo := slope_below_end hx0 hxb hbR hAb hGb hAb0 hbG0
  have hnx := scaledPhase_lt_firstNode (le_rfl : dodecaNear ≤ dodecaNear) hxI
  have hγ := gamma_pos_dodeca_phase (by linarith [dodecaNear_gt_one]) le_rfl hxI
  simpa [nearContrib] using
    near_contrib_gt ha0 hx0 hax hx1 hp0 hp1 hpLe hAa hAa0 hAn hAn0 hGn hGn0
      hbG0 hbA0 hSlo hbr0 hnx hγ

private lemma far_upper
    {x a b p q c cLo cHi k kHi : ℝ}
    {bAHi bGLo pALo pGHi qAHi qGLo : ℝ}
    (ha0 : 0 < a) (hx0 : 0 < x) (hax : a < x) (hxb : x ≤ b) (hb1 : b ≤ 1)
    (hbR : b < resonanceRoot1) (hp0 : 0 < p) (hq1 : q ≤ 1)
    (hc0 : 0 < c) (hc1 : c < 1) (hcLo : cLo ≤ c) (hcHi : c ≤ cHi)
    (hk0 : 0 < k) (hkHi : 0 < kHi) (hk : k ≤ kHi)
    (hpLe : p ≤ cLo * a) (hqGe : cHi * b ≤ q)
    (hAb : chordAmp b < bAHi) (hAb0 : 0 < chordAmp b)
    (hGb : bGLo < gammaSEqual b)
    (hpA : pALo < chordAmp p) (hpA0 : 0 < pALo)
    (hpG : gammaSEqual p < pGHi) (hpG0 : 0 < gammaSEqual p)
    (hqA : chordAmp q < qAHi) (hqG : qGLo < gammaSEqual q) (hqG0 : 0 < qGLo)
    (hbG0 : 0 < bGLo) (hbA0 : 0 < bAHi)
    (hbr0 : 0 < pGHi / pALo - cLo * (bGLo / bAHi))
    (hsNear : c ≤ dodecaNear) (hxI : x ∈ Ioo (0 : ℝ) dodecaWall) :
    farContrib k c x <
      (kHi * 2 * bAHi * qAHi * (pGHi / pALo - cLo * (bGLo / bAHi))) / qGLo ^ 2 := by
  have hSlo := slope_below_end hx0 hxb hbR hAb hGb hAb0 hbG0
  have hxR : x < resonanceRoot1 := lt_of_le_of_lt hxb hbR
  have hcx1 := scaledPhase_lt_firstNode hsNear hxI
  have hγ := gamma_pos_dodeca_phase hc0 hsNear hxI
  simpa [farContrib] using
    far_contrib_lt ha0 hx0 hax hxb hb1 hxR hp0 hq1
      hc0 hc1 hcLo hcHi hk0 hkHi hk hpLe hqGe
      hAb hpA hpA0 hpG hpG0 hqA hqG hqG0
      hbG0 hbA0 hSlo hbr0 hcx1 hγ

/-! ### One sample phase, used to check the rational bounds -/

private lemma phase_350 :
    (364115573 / 1000000000 : ℝ) < chordAmp ((350 : ℝ) / 1000) ∧
      chordAmp ((350 : ℝ) / 1000) < 364115713 / 1000000000 ∧
        (437509707 / 500000000 : ℝ) < gammaSEqual ((350 : ℝ) / 1000) ∧
          gammaSEqual ((350 : ℝ) / 1000) < 437511093 / 500000000 := by
  have ht0 : (0 : ℝ) < 350 / 1000 := by norm_num
  have ht1 : (350 : ℝ) / 1000 ≤ 1 := by norm_num
  obtain ⟨hs7, hs5, hc6, hc4⟩ := trigPoly_bounds ht0
  have hsLo : (342897807 / 1000000000 : ℝ) < sin ((350 : ℝ) / 1000) := by
    have hnum : (342897807 / 1000000000 : ℝ) <
        (350 : ℝ) / 1000 - ((350 : ℝ) / 1000) ^ 3 / 6 + ((350 : ℝ) / 1000) ^ 5 / 120 -
          ((350 : ℝ) / 1000) ^ 7 / 5040 := by norm_num
    linarith
  have hsHi : sin ((350 : ℝ) / 1000) < 68579587 / 200000000 := by
    have hnum : (350 : ℝ) / 1000 - ((350 : ℝ) / 1000) ^ 3 / 6 + ((350 : ℝ) / 1000) ^ 5 / 120 <
        (68579587 : ℝ) / 200000000 := by norm_num
    linarith
  have hcLo : (939372707 / 1000000000 : ℝ) < cos ((350 : ℝ) / 1000) := by
    have hnum : (939372707 / 1000000000 : ℝ) <
        1 - ((350 : ℝ) / 1000) ^ 2 / 2 + ((350 : ℝ) / 1000) ^ 4 / 24 -
          ((350 : ℝ) / 1000) ^ 6 / 720 := by norm_num
    linarith
  have hcHi : cos ((350 : ℝ) / 1000) < 939375261 / 1000000000 := by
    have hnum : 1 - ((350 : ℝ) / 1000) ^ 2 / 2 + ((350 : ℝ) / 1000) ^ 4 / 24 <
        (939375261 : ℝ) / 1000000000 := by norm_num
    linarith
  have hexp := exp_between (x := (350 : ℝ) / 1000) (n := 8)
    (lo := 88691721 / 62500000) (hi := 28381351 / 20000000)
    ht0.le ht1 (by decide)
    (by norm_num [sum_range_succ, Nat.factorial])
    (by norm_num [sum_range_succ, Nat.factorial])
  exact phase_bounds ht0 ht1 hsLo hsHi hcLo hcHi hexp.1 hexp.2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-! ### Rational phases on the thousandth grid, through the chord wall. -/

private def phaseHolds (t ALo AHi GLo GHi : ℝ) : Prop :=
  0 < t ∧ t ≤ 1 ∧ t < (93 : ℝ) / 100 ∧
    0 < ALo ∧ ALo < chordAmp t ∧ chordAmp t < AHi ∧
      0 < GLo ∧ GLo < gammaSEqual t ∧ gammaSEqual t < GHi


private lemma phaseAt_175 :
    phaseHolds (((175 : ℝ) / 1000)) ((88390489 : ℝ) / 500000000) ((176780981 : ℝ) / 1000000000) ((484609501 : ℝ) / 500000000) ((484609523 : ℝ) / 500000000) := by
  have ht0 : (0 : ℝ) < ((175 : ℝ) / 1000) := by norm_num
  have ht1 : ((175 : ℝ) / 1000) ≤ 1 := by norm_num
  obtain ⟨hs7, hs5, hc6, hc4⟩ := trigPoly_bounds ht0
  have hsLo : ((174108137 : ℝ) / 1000000000) < sin (((175 : ℝ) / 1000)) := by
    have hnum : ((174108137 : ℝ) / 1000000000) <
        ((175 : ℝ) / 1000) - (((175 : ℝ) / 1000)) ^ 3 / 6 + (((175 : ℝ) / 1000)) ^ 5 / 120 - (((175 : ℝ) / 1000)) ^ 7 / 5040 := by norm_num
    linarith
  have hsHi : sin (((175 : ℝ) / 1000)) < ((174108139 : ℝ) / 1000000000) := by
    have hnum : ((175 : ℝ) / 1000) - (((175 : ℝ) / 1000)) ^ 3 / 6 + (((175 : ℝ) / 1000)) ^ 5 / 120 < ((174108139 : ℝ) / 1000000000) := by norm_num
    linarith
  have hcLo : ((492363269 : ℝ) / 500000000) < cos (((175 : ℝ) / 1000)) := by
    have hnum : ((492363269 : ℝ) / 500000000) <
        1 - (((175 : ℝ) / 1000)) ^ 2 / 2 + (((175 : ℝ) / 1000)) ^ 4 / 24 - (((175 : ℝ) / 1000)) ^ 6 / 720 := by norm_num
    linarith
  have hcHi : cos (((175 : ℝ) / 1000)) < ((984726579 : ℝ) / 1000000000) := by
    have hnum : 1 - (((175 : ℝ) / 1000)) ^ 2 / 2 + (((175 : ℝ) / 1000)) ^ 4 / 24 < ((984726579 : ℝ) / 1000000000) := by norm_num
    linarith
  have hexp := exp_between (x := ((175 : ℝ) / 1000)) (n := 8) (lo := ((148905777 : ℝ) / 125000000)) (hi := ((1191246217 : ℝ) / 1000000000))
    ht0.le ht1 (by decide)
    (by norm_num [sum_range_succ, Nat.factorial])
    (by norm_num [sum_range_succ, Nat.factorial])
  have hph : ((88390489 : ℝ) / 500000000) < chordAmp (((175 : ℝ) / 1000)) ∧ chordAmp (((175 : ℝ) / 1000)) < ((176780981 : ℝ) / 1000000000) ∧
      ((484609501 : ℝ) / 500000000) < gammaSEqual (((175 : ℝ) / 1000)) ∧ gammaSEqual (((175 : ℝ) / 1000)) < ((484609523 : ℝ) / 500000000) := by
    exact phase_bounds ht0 ht1 hsLo hsHi hcLo hcHi hexp.1 hexp.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨ht0, ht1, by norm_num, by norm_num, hph.1, hph.2.1, by norm_num, hph.2.2.1, hph.2.2.2⟩


private lemma phaseAt_180 :
    phaseHolds (((180 : ℝ) / 1000)) ((181937691 : ℝ) / 1000000000) ((90968847 : ℝ) / 500000000) ((120928177 : ℝ) / 125000000) ((241856367 : ℝ) / 250000000) := by
  have ht0 : (0 : ℝ) < ((180 : ℝ) / 1000) := by norm_num
  have ht1 : ((180 : ℝ) / 1000) ≤ 1 := by norm_num
  obtain ⟨hs7, hs5, hc6, hc4⟩ := trigPoly_bounds ht0
  have hsLo : ((179029573 : ℝ) / 1000000000) < sin (((180 : ℝ) / 1000)) := by
    have hnum : ((179029573 : ℝ) / 1000000000) <
        ((180 : ℝ) / 1000) - (((180 : ℝ) / 1000)) ^ 3 / 6 + (((180 : ℝ) / 1000)) ^ 5 / 120 - (((180 : ℝ) / 1000)) ^ 7 / 5040 := by norm_num
    linarith
  have hsHi : sin (((180 : ℝ) / 1000)) < ((7161183 : ℝ) / 40000000) := by
    have hnum : ((180 : ℝ) / 1000) - (((180 : ℝ) / 1000)) ^ 3 / 6 + (((180 : ℝ) / 1000)) ^ 5 / 120 < ((7161183 : ℝ) / 40000000) := by norm_num
    linarith
  have hcLo : ((245960923 : ℝ) / 250000000) < cos (((180 : ℝ) / 1000)) := by
    have hnum : ((245960923 : ℝ) / 250000000) <
        1 - (((180 : ℝ) / 1000)) ^ 2 / 2 + (((180 : ℝ) / 1000)) ^ 4 / 24 - (((180 : ℝ) / 1000)) ^ 6 / 720 := by norm_num
    linarith
  have hcHi : cos (((180 : ℝ) / 1000)) < ((983843741 : ℝ) / 1000000000) := by
    have hnum : 1 - (((180 : ℝ) / 1000)) ^ 2 / 2 + (((180 : ℝ) / 1000)) ^ 4 / 24 < ((983843741 : ℝ) / 1000000000) := by norm_num
    linarith
  have hexp := exp_between (x := ((180 : ℝ) / 1000)) (n := 8) (lo := ((1197217363 : ℝ) / 1000000000)) (hi := ((299304341 : ℝ) / 250000000))
    ht0.le ht1 (by decide)
    (by norm_num [sum_range_succ, Nat.factorial])
    (by norm_num [sum_range_succ, Nat.factorial])
  have hph : ((181937691 : ℝ) / 1000000000) < chordAmp (((180 : ℝ) / 1000)) ∧ chordAmp (((180 : ℝ) / 1000)) < ((90968847 : ℝ) / 500000000) ∧
      ((120928177 : ℝ) / 125000000) < gammaSEqual (((180 : ℝ) / 1000)) ∧ gammaSEqual (((180 : ℝ) / 1000)) < ((241856367 : ℝ) / 250000000) := by
    exact phase_bounds ht0 ht1 hsLo hsHi hcLo hcHi hexp.1 hexp.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨ht0, ht1, by norm_num, by norm_num, hph.1, hph.2.1, by norm_num, hph.2.2.1, hph.2.2.2⟩


private lemma phaseAt_187 :
    phaseHolds (((187 : ℝ) / 1000)) ((94586049 : ℝ) / 500000000) ((94586051 : ℝ) / 500000000) ((241206917 : ℝ) / 250000000) ((964827733 : ℝ) / 1000000000) := by
  have ht0 : (0 : ℝ) < ((187 : ℝ) / 1000) := by norm_num
  have ht1 : ((187 : ℝ) / 1000) ≤ 1 := by norm_num
  obtain ⟨hs7, hs5, hc6, hc4⟩ := trigPoly_bounds ht0
  have hsLo : ((46478009 : ℝ) / 250000000) < sin (((187 : ℝ) / 1000)) := by
    have hnum : ((46478009 : ℝ) / 250000000) <
        ((187 : ℝ) / 1000) - (((187 : ℝ) / 1000)) ^ 3 / 6 + (((187 : ℝ) / 1000)) ^ 5 / 120 - (((187 : ℝ) / 1000)) ^ 7 / 5040 := by norm_num
    linarith
  have hsHi : sin (((187 : ℝ) / 1000)) < ((185912039 : ℝ) / 1000000000) := by
    have hnum : ((187 : ℝ) / 1000) - (((187 : ℝ) / 1000)) ^ 3 / 6 + (((187 : ℝ) / 1000)) ^ 5 / 120 < ((185912039 : ℝ) / 1000000000) := by norm_num
    linarith
  have hcLo : ((982566391 : ℝ) / 1000000000) < cos (((187 : ℝ) / 1000)) := by
    have hnum : ((982566391 : ℝ) / 1000000000) <
        1 - (((187 : ℝ) / 1000)) ^ 2 / 2 + (((187 : ℝ) / 1000)) ^ 4 / 24 - (((187 : ℝ) / 1000)) ^ 6 / 720 := by norm_num
    linarith
  have hcHi : cos (((187 : ℝ) / 1000)) < ((245641613 : ℝ) / 250000000) := by
    have hnum : 1 - (((187 : ℝ) / 1000)) ^ 2 / 2 + (((187 : ℝ) / 1000)) ^ 4 / 24 < ((245641613 : ℝ) / 250000000) := by norm_num
    linarith
  have hexp := exp_between (x := ((187 : ℝ) / 1000)) (n := 8) (lo := ((301406821 : ℝ) / 250000000)) (hi := ((602813643 : ℝ) / 500000000))
    ht0.le ht1 (by decide)
    (by norm_num [sum_range_succ, Nat.factorial])
    (by norm_num [sum_range_succ, Nat.factorial])
  have hph : ((94586049 : ℝ) / 500000000) < chordAmp (((187 : ℝ) / 1000)) ∧ chordAmp (((187 : ℝ) / 1000)) < ((94586051 : ℝ) / 500000000) ∧
      ((241206917 : ℝ) / 250000000) < gammaSEqual (((187 : ℝ) / 1000)) ∧ gammaSEqual (((187 : ℝ) / 1000)) < ((964827733 : ℝ) / 1000000000) := by
    exact phase_bounds ht0 ht1 hsLo hsHi hcLo hcHi hexp.1 hexp.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨ht0, ht1, by norm_num, by norm_num, hph.1, hph.2.1, by norm_num, hph.2.2.1, hph.2.2.2⟩


private lemma phaseAt_188 :
    phaseHolds (((188 : ℝ) / 1000)) ((190207049 : ℝ) / 1000000000) ((47551763 : ℝ) / 250000000) ((964448289 : ℝ) / 1000000000) ((192889671 : ℝ) / 200000000) := by
  have ht0 : (0 : ℝ) < ((188 : ℝ) / 1000) := by norm_num
  have ht1 : ((188 : ℝ) / 1000) ≤ 1 := by norm_num
  obtain ⟨hs7, hs5, hc6, hc4⟩ := trigPoly_bounds ht0
  have hsLo : ((18689451 : ℝ) / 100000000) < sin (((188 : ℝ) / 1000)) := by
    have hnum : ((18689451 : ℝ) / 100000000) <
        ((188 : ℝ) / 1000) - (((188 : ℝ) / 1000)) ^ 3 / 6 + (((188 : ℝ) / 1000)) ^ 5 / 120 - (((188 : ℝ) / 1000)) ^ 7 / 5040 := by norm_num
    linarith
  have hsHi : sin (((188 : ℝ) / 1000)) < ((11680907 : ℝ) / 62500000) := by
    have hnum : ((188 : ℝ) / 1000) - (((188 : ℝ) / 1000)) ^ 3 / 6 + (((188 : ℝ) / 1000)) ^ 5 / 120 < ((11680907 : ℝ) / 62500000) := by norm_num
    linarith
  have hcLo : ((245594997 : ℝ) / 250000000) < cos (((188 : ℝ) / 1000)) := by
    have hnum : ((245594997 : ℝ) / 250000000) <
        1 - (((188 : ℝ) / 1000)) ^ 2 / 2 + (((188 : ℝ) / 1000)) ^ 4 / 24 - (((188 : ℝ) / 1000)) ^ 6 / 720 := by norm_num
    linarith
  have hcHi : cos (((188 : ℝ) / 1000)) < ((19647601 : ℝ) / 20000000) := by
    have hnum : 1 - (((188 : ℝ) / 1000)) ^ 2 / 2 + (((188 : ℝ) / 1000)) ^ 4 / 24 < ((19647601 : ℝ) / 20000000) := by norm_num
    linarith
  have hexp := exp_between (x := ((188 : ℝ) / 1000)) (n := 8) (lo := ((241366703 : ℝ) / 200000000)) (hi := ((301708379 : ℝ) / 250000000))
    ht0.le ht1 (by decide)
    (by norm_num [sum_range_succ, Nat.factorial])
    (by norm_num [sum_range_succ, Nat.factorial])
  have hph : ((190207049 : ℝ) / 1000000000) < chordAmp (((188 : ℝ) / 1000)) ∧ chordAmp (((188 : ℝ) / 1000)) < ((47551763 : ℝ) / 250000000) ∧
      ((964448289 : ℝ) / 1000000000) < gammaSEqual (((188 : ℝ) / 1000)) ∧ gammaSEqual (((188 : ℝ) / 1000)) < ((192889671 : ℝ) / 200000000) := by
    exact phase_bounds ht0 ht1 hsLo hsHi hcLo hcHi hexp.1 hexp.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨ht0, ht1, by norm_num, by norm_num, hph.1, hph.2.1, by norm_num, hph.2.2.1, hph.2.2.2⟩


private lemma phaseAt_192 :
    phaseHolds (((192 : ℝ) / 1000)) ((97175291 : ℝ) / 500000000) ((194350587 : ℝ) / 1000000000) ((962910063 : ℝ) / 1000000000) ((481455069 : ℝ) / 500000000) := by
  have ht0 : (0 : ℝ) < ((192 : ℝ) / 1000) := by norm_num
  have ht1 : ((192 : ℝ) / 1000) ≤ 1 := by norm_num
  obtain ⟨hs7, hs5, hc6, hc4⟩ := trigPoly_bounds ht0
  have hsLo : ((47705631 : ℝ) / 250000000) < sin (((192 : ℝ) / 1000)) := by
    have hnum : ((47705631 : ℝ) / 250000000) <
        ((192 : ℝ) / 1000) - (((192 : ℝ) / 1000)) ^ 3 / 6 + (((192 : ℝ) / 1000)) ^ 5 / 120 - (((192 : ℝ) / 1000)) ^ 7 / 5040 := by norm_num
    linarith
  have hsHi : sin (((192 : ℝ) / 1000)) < ((190822527 : ℝ) / 1000000000) := by
    have hnum : ((192 : ℝ) / 1000) - (((192 : ℝ) / 1000)) ^ 3 / 6 + (((192 : ℝ) / 1000)) ^ 5 / 120 < ((190822527 : ℝ) / 1000000000) := by norm_num
    linarith
  have hcLo : ((981624553 : ℝ) / 1000000000) < cos (((192 : ℝ) / 1000)) := by
    have hnum : ((981624553 : ℝ) / 1000000000) <
        1 - (((192 : ℝ) / 1000)) ^ 2 / 2 + (((192 : ℝ) / 1000)) ^ 4 / 24 - (((192 : ℝ) / 1000)) ^ 6 / 720 := by norm_num
    linarith
  have hcHi : cos (((192 : ℝ) / 1000)) < ((61351539 : ℝ) / 62500000) := by
    have hnum : 1 - (((192 : ℝ) / 1000)) ^ 2 / 2 + (((192 : ℝ) / 1000)) ^ 4 / 24 < ((61351539 : ℝ) / 62500000) := by norm_num
    linarith
  have hexp := exp_between (x := ((192 : ℝ) / 1000)) (n := 8) (lo := ((302917629 : ℝ) / 250000000)) (hi := ((1211670517 : ℝ) / 1000000000))
    ht0.le ht1 (by decide)
    (by norm_num [sum_range_succ, Nat.factorial])
    (by norm_num [sum_range_succ, Nat.factorial])
  have hph : ((97175291 : ℝ) / 500000000) < chordAmp (((192 : ℝ) / 1000)) ∧ chordAmp (((192 : ℝ) / 1000)) < ((194350587 : ℝ) / 1000000000) ∧
      ((962910063 : ℝ) / 1000000000) < gammaSEqual (((192 : ℝ) / 1000)) ∧ gammaSEqual (((192 : ℝ) / 1000)) < ((481455069 : ℝ) / 500000000) := by
    exact phase_bounds ht0 ht1 hsLo hsHi hcLo hcHi hexp.1 hexp.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨ht0, ht1, by norm_num, by norm_num, hph.1, hph.2.1, by norm_num, hph.2.2.1, hph.2.2.2⟩


private lemma phaseAt_193 :
    phaseHolds (((193 : ℝ) / 1000)) ((195387409 : ℝ) / 1000000000) ((97693707 : ℝ) / 500000000) ((38500813 : ℝ) / 40000000) ((481260201 : ℝ) / 500000000) := by
  have ht0 : (0 : ℝ) < ((193 : ℝ) / 1000) := by norm_num
  have ht1 : ((193 : ℝ) / 1000) ≤ 1 := by norm_num
  obtain ⟨hs7, hs5, hc6, hc4⟩ := trigPoly_bounds ht0
  have hsLo : ((191804053 : ℝ) / 1000000000) < sin (((193 : ℝ) / 1000)) := by
    have hnum : ((191804053 : ℝ) / 1000000000) <
        ((193 : ℝ) / 1000) - (((193 : ℝ) / 1000)) ^ 3 / 6 + (((193 : ℝ) / 1000)) ^ 5 / 120 - (((193 : ℝ) / 1000)) ^ 7 / 5040 := by norm_num
    linarith
  have hsHi : sin (((193 : ℝ) / 1000)) < ((23975507 : ℝ) / 125000000) := by
    have hnum : ((193 : ℝ) / 1000) - (((193 : ℝ) / 1000)) ^ 3 / 6 + (((193 : ℝ) / 1000)) ^ 5 / 120 < ((23975507 : ℝ) / 125000000) := by norm_num
    linarith
  have hcLo : ((24535831 : ℝ) / 25000000) < cos (((193 : ℝ) / 1000)) := by
    have hnum : ((24535831 : ℝ) / 25000000) <
        1 - (((193 : ℝ) / 1000)) ^ 2 / 2 + (((193 : ℝ) / 1000)) ^ 4 / 24 - (((193 : ℝ) / 1000)) ^ 6 / 720 := by norm_num
    linarith
  have hcHi : cos (((193 : ℝ) / 1000)) < ((981433313 : ℝ) / 1000000000) := by
    have hnum : 1 - (((193 : ℝ) / 1000)) ^ 2 / 2 + (((193 : ℝ) / 1000)) ^ 4 / 24 < ((981433313 : ℝ) / 1000000000) := by norm_num
    linarith
  have hexp := exp_between (x := ((193 : ℝ) / 1000)) (n := 8) (lo := ((1212882793 : ℝ) / 1000000000)) (hi := ((606441397 : ℝ) / 500000000))
    ht0.le ht1 (by decide)
    (by norm_num [sum_range_succ, Nat.factorial])
    (by norm_num [sum_range_succ, Nat.factorial])
  have hph : ((195387409 : ℝ) / 1000000000) < chordAmp (((193 : ℝ) / 1000)) ∧ chordAmp (((193 : ℝ) / 1000)) < ((97693707 : ℝ) / 500000000) ∧
      ((38500813 : ℝ) / 40000000) < gammaSEqual (((193 : ℝ) / 1000)) ∧ gammaSEqual (((193 : ℝ) / 1000)) < ((481260201 : ℝ) / 500000000) := by
    exact phase_bounds ht0 ht1 hsLo hsHi hcLo hcHi hexp.1 hexp.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨ht0, ht1, by norm_num, by norm_num, hph.1, hph.2.1, by norm_num, hph.2.2.1, hph.2.2.2⟩


private lemma phaseAt_197 :
    phaseHolds (((197 : ℝ) / 1000)) ((49884637 : ℝ) / 250000000) ((24942319 : ℝ) / 125000000) ((307501 : ℝ) / 320000) ((960940711 : ℝ) / 1000000000) := by
  have ht0 : (0 : ℝ) < ((197 : ℝ) / 1000) := by norm_num
  have ht1 : ((197 : ℝ) / 1000) ≤ 1 := by norm_num
  obtain ⟨hs7, hs5, hc6, hc4⟩ := trigPoly_bounds ht0
  have hsLo : ((195728241 : ℝ) / 1000000000) < sin (((197 : ℝ) / 1000)) := by
    have hnum : ((195728241 : ℝ) / 1000000000) <
        ((197 : ℝ) / 1000) - (((197 : ℝ) / 1000)) ^ 3 / 6 + (((197 : ℝ) / 1000)) ^ 5 / 120 - (((197 : ℝ) / 1000)) ^ 7 / 5040 := by norm_num
    linarith
  have hsHi : sin (((197 : ℝ) / 1000)) < ((48932061 : ℝ) / 250000000) := by
    have hnum : ((197 : ℝ) / 1000) - (((197 : ℝ) / 1000)) ^ 3 / 6 + (((197 : ℝ) / 1000)) ^ 5 / 120 < ((48932061 : ℝ) / 250000000) := by norm_num
    linarith
  have hcLo : ((490329087 : ℝ) / 500000000) < cos (((197 : ℝ) / 1000)) := by
    have hnum : ((490329087 : ℝ) / 500000000) <
        1 - (((197 : ℝ) / 1000)) ^ 2 / 2 + (((197 : ℝ) / 1000)) ^ 4 / 24 - (((197 : ℝ) / 1000)) ^ 6 / 720 := by norm_num
    linarith
  have hcHi : cos (((197 : ℝ) / 1000)) < ((61291141 : ℝ) / 62500000) := by
    have hnum : 1 - (((197 : ℝ) / 1000)) ^ 2 / 2 + (((197 : ℝ) / 1000)) ^ 4 / 24 < ((61291141 : ℝ) / 62500000) := by norm_num
    linarith
  have hexp := exp_between (x := ((197 : ℝ) / 1000)) (n := 8) (lo := ((30443601 : ℝ) / 25000000)) (hi := ((1217744041 : ℝ) / 1000000000))
    ht0.le ht1 (by decide)
    (by norm_num [sum_range_succ, Nat.factorial])
    (by norm_num [sum_range_succ, Nat.factorial])
  have hph : ((49884637 : ℝ) / 250000000) < chordAmp (((197 : ℝ) / 1000)) ∧ chordAmp (((197 : ℝ) / 1000)) < ((24942319 : ℝ) / 125000000) ∧
      ((307501 : ℝ) / 320000) < gammaSEqual (((197 : ℝ) / 1000)) ∧ gammaSEqual (((197 : ℝ) / 1000)) < ((960940711 : ℝ) / 1000000000) := by
    exact phase_bounds ht0 ht1 hsLo hsHi hcLo hcHi hexp.1 hexp.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨ht0, ht1, by norm_num, by norm_num, hph.1, hph.2.1, by norm_num, hph.2.2.1, hph.2.2.2⟩


private lemma phaseAt_198 :
    phaseHolds (((198 : ℝ) / 1000)) ((2005773 : ℝ) / 10000000) ((25072163 : ℝ) / 125000000) ((96054051 : ℝ) / 100000000) ((480270299 : ℝ) / 500000000) := by
  have ht0 : (0 : ℝ) < ((198 : ℝ) / 1000) := by norm_num
  have ht1 : ((198 : ℝ) / 1000) ≤ 1 := by norm_num
  obtain ⟨hs7, hs5, hc6, hc4⟩ := trigPoly_bounds ht0
  have hsLo : ((196708801 : ℝ) / 1000000000) < sin (((198 : ℝ) / 1000)) := by
    have hnum : ((196708801 : ℝ) / 1000000000) <
        ((198 : ℝ) / 1000) - (((198 : ℝ) / 1000)) ^ 3 / 6 + (((198 : ℝ) / 1000)) ^ 5 / 120 - (((198 : ℝ) / 1000)) ^ 7 / 5040 := by norm_num
    linarith
  have hsHi : sin (((198 : ℝ) / 1000)) < ((49177201 : ℝ) / 250000000) := by
    have hnum : ((198 : ℝ) / 1000) - (((198 : ℝ) / 1000)) ^ 3 / 6 + (((198 : ℝ) / 1000)) ^ 5 / 120 < ((49177201 : ℝ) / 250000000) := by norm_num
    linarith
  have hcLo : ((245115489 : ℝ) / 250000000) < cos (((198 : ℝ) / 1000)) := by
    have hnum : ((245115489 : ℝ) / 250000000) <
        1 - (((198 : ℝ) / 1000)) ^ 2 / 2 + (((198 : ℝ) / 1000)) ^ 4 / 24 - (((198 : ℝ) / 1000)) ^ 6 / 720 := by norm_num
    linarith
  have hcHi : cos (((198 : ℝ) / 1000)) < ((24511551 : ℝ) / 25000000) := by
    have hnum : 1 - (((198 : ℝ) / 1000)) ^ 2 / 2 + (((198 : ℝ) / 1000)) ^ 4 / 24 < ((24511551 : ℝ) / 25000000) := by norm_num
    linarith
  have hexp := exp_between (x := ((198 : ℝ) / 1000)) (n := 8) (lo := ((1218962393 : ℝ) / 1000000000)) (hi := ((609481197 : ℝ) / 500000000))
    ht0.le ht1 (by decide)
    (by norm_num [sum_range_succ, Nat.factorial])
    (by norm_num [sum_range_succ, Nat.factorial])
  have hph : ((2005773 : ℝ) / 10000000) < chordAmp (((198 : ℝ) / 1000)) ∧ chordAmp (((198 : ℝ) / 1000)) < ((25072163 : ℝ) / 125000000) ∧
      ((96054051 : ℝ) / 100000000) < gammaSEqual (((198 : ℝ) / 1000)) ∧ gammaSEqual (((198 : ℝ) / 1000)) < ((480270299 : ℝ) / 500000000) := by
    exact phase_bounds ht0 ht1 hsLo hsHi hcLo hcHi hexp.1 hexp.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨ht0, ht1, by norm_num, by norm_num, hph.1, hph.2.1, by norm_num, hph.2.2.1, hph.2.2.2⟩


private lemma phaseAt_200 :
    phaseHolds (((200 : ℝ) / 1000)) ((101327989 : ℝ) / 500000000) ((12665999 : ℝ) / 62500000) ((959734043 : ℝ) / 1000000000) ((479867069 : ℝ) / 500000000) := by
  have ht0 : (0 : ℝ) < ((200 : ℝ) / 1000) := by norm_num
  have ht1 : ((200 : ℝ) / 1000) ≤ 1 := by norm_num
  obtain ⟨hs7, hs5, hc6, hc4⟩ := trigPoly_bounds ht0
  have hsLo : ((19866933 : ℝ) / 100000000) < sin (((200 : ℝ) / 1000)) := by
    have hnum : ((19866933 : ℝ) / 100000000) <
        ((200 : ℝ) / 1000) - (((200 : ℝ) / 1000)) ^ 3 / 6 + (((200 : ℝ) / 1000)) ^ 5 / 120 - (((200 : ℝ) / 1000)) ^ 7 / 5040 := by norm_num
    linarith
  have hsHi : sin (((200 : ℝ) / 1000)) < ((99334667 : ℝ) / 500000000) := by
    have hnum : ((200 : ℝ) / 1000) - (((200 : ℝ) / 1000)) ^ 3 / 6 + (((200 : ℝ) / 1000)) ^ 5 / 120 < ((99334667 : ℝ) / 500000000) := by norm_num
    linarith
  have hcLo : ((980066577 : ℝ) / 1000000000) < cos (((200 : ℝ) / 1000)) := by
    have hnum : ((980066577 : ℝ) / 1000000000) <
        1 - (((200 : ℝ) / 1000)) ^ 2 / 2 + (((200 : ℝ) / 1000)) ^ 4 / 24 - (((200 : ℝ) / 1000)) ^ 6 / 720 := by norm_num
    linarith
  have hcHi : cos (((200 : ℝ) / 1000)) < ((980066667 : ℝ) / 1000000000) := by
    have hnum : 1 - (((200 : ℝ) / 1000)) ^ 2 / 2 + (((200 : ℝ) / 1000)) ^ 4 / 24 < ((980066667 : ℝ) / 1000000000) := by norm_num
    linarith
  have hexp := exp_between (x := ((200 : ℝ) / 1000)) (n := 8) (lo := ((610701379 : ℝ) / 500000000)) (hi := ((1221402759 : ℝ) / 1000000000))
    ht0.le ht1 (by decide)
    (by norm_num [sum_range_succ, Nat.factorial])
    (by norm_num [sum_range_succ, Nat.factorial])
  have hph : ((101327989 : ℝ) / 500000000) < chordAmp (((200 : ℝ) / 1000)) ∧ chordAmp (((200 : ℝ) / 1000)) < ((12665999 : ℝ) / 62500000) ∧
      ((959734043 : ℝ) / 1000000000) < gammaSEqual (((200 : ℝ) / 1000)) ∧ gammaSEqual (((200 : ℝ) / 1000)) < ((479867069 : ℝ) / 500000000) := by
    exact phase_bounds ht0 ht1 hsLo hsHi hcLo hcHi hexp.1 hexp.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨ht0, ht1, by norm_num, by norm_num, hph.1, hph.2.1, by norm_num, hph.2.2.1, hph.2.2.2⟩


private lemma phaseAt_201 :
    phaseHolds (((201 : ℝ) / 1000)) ((50923977 : ℝ) / 250000000) ((101847957 : ℝ) / 500000000) ((959327691 : ℝ) / 1000000000) ((959327789 : ℝ) / 1000000000) := by
  have ht0 : (0 : ℝ) < ((201 : ℝ) / 1000) := by norm_num
  have ht1 : ((201 : ℝ) / 1000) ≤ 1 := by norm_num
  obtain ⟨hs7, hs5, hc6, hc4⟩ := trigPoly_bounds ht0
  have hsLo : ((199649297 : ℝ) / 1000000000) < sin (((201 : ℝ) / 1000)) := by
    have hnum : ((199649297 : ℝ) / 1000000000) <
        ((201 : ℝ) / 1000) - (((201 : ℝ) / 1000)) ^ 3 / 6 + (((201 : ℝ) / 1000)) ^ 5 / 120 - (((201 : ℝ) / 1000)) ^ 7 / 5040 := by norm_num
    linarith
  have hsHi : sin (((201 : ℝ) / 1000)) < ((199649301 : ℝ) / 1000000000) := by
    have hnum : ((201 : ℝ) / 1000) - (((201 : ℝ) / 1000)) ^ 3 / 6 + (((201 : ℝ) / 1000)) ^ 5 / 120 < ((199649301 : ℝ) / 1000000000) := by norm_num
    linarith
  have hcLo : ((489933709 : ℝ) / 500000000) < cos (((201 : ℝ) / 1000)) := by
    have hnum : ((489933709 : ℝ) / 500000000) <
        1 - (((201 : ℝ) / 1000)) ^ 2 / 2 + (((201 : ℝ) / 1000)) ^ 4 / 24 - (((201 : ℝ) / 1000)) ^ 6 / 720 := by norm_num
    linarith
  have hcHi : cos (((201 : ℝ) / 1000)) < ((979867511 : ℝ) / 1000000000) := by
    have hnum : 1 - (((201 : ℝ) / 1000)) ^ 2 / 2 + (((201 : ℝ) / 1000)) ^ 4 / 24 < ((979867511 : ℝ) / 1000000000) := by norm_num
    linarith
  have hexp := exp_between (x := ((201 : ℝ) / 1000)) (n := 8) (lo := ((1222624771 : ℝ) / 1000000000)) (hi := ((305656193 : ℝ) / 250000000))
    ht0.le ht1 (by decide)
    (by norm_num [sum_range_succ, Nat.factorial])
    (by norm_num [sum_range_succ, Nat.factorial])
  have hph : ((50923977 : ℝ) / 250000000) < chordAmp (((201 : ℝ) / 1000)) ∧ chordAmp (((201 : ℝ) / 1000)) < ((101847957 : ℝ) / 500000000) ∧
      ((959327691 : ℝ) / 1000000000) < gammaSEqual (((201 : ℝ) / 1000)) ∧ gammaSEqual (((201 : ℝ) / 1000)) < ((959327789 : ℝ) / 1000000000) := by
    exact phase_bounds ht0 ht1 hsLo hsHi hcLo hcHi hexp.1 hexp.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨ht0, ht1, by norm_num, by norm_num, hph.1, hph.2.1, by norm_num, hph.2.2.1, hph.2.2.2⟩


private lemma phaseAt_207 :
    phaseHolds (((207 : ℝ) / 1000)) ((41988777 : ℝ) / 200000000) ((209943891 : ℝ) / 1000000000) ((956845867 : ℝ) / 1000000000) ((478422991 : ℝ) / 500000000) := by
  have ht0 : (0 : ℝ) < ((207 : ℝ) / 1000) := by norm_num
  have ht1 : ((207 : ℝ) / 1000) ≤ 1 := by norm_num
  obtain ⟨hs7, hs5, hc6, hc4⟩ := trigPoly_bounds ht0
  have hsLo : ((205524873 : ℝ) / 1000000000) < sin (((207 : ℝ) / 1000)) := by
    have hnum : ((205524873 : ℝ) / 1000000000) <
        ((207 : ℝ) / 1000) - (((207 : ℝ) / 1000)) ^ 3 / 6 + (((207 : ℝ) / 1000)) ^ 5 / 120 - (((207 : ℝ) / 1000)) ^ 7 / 5040 := by norm_num
    linarith
  have hsHi : sin (((207 : ℝ) / 1000)) < ((205524877 : ℝ) / 1000000000) := by
    have hnum : ((207 : ℝ) / 1000) - (((207 : ℝ) / 1000)) ^ 3 / 6 + (((207 : ℝ) / 1000)) ^ 5 / 120 < ((205524877 : ℝ) / 1000000000) := by norm_num
    linarith
  have hcLo : ((244662973 : ℝ) / 250000000) < cos (((207 : ℝ) / 1000)) := by
    have hnum : ((244662973 : ℝ) / 250000000) <
        1 - (((207 : ℝ) / 1000)) ^ 2 / 2 + (((207 : ℝ) / 1000)) ^ 4 / 24 - (((207 : ℝ) / 1000)) ^ 6 / 720 := by norm_num
    linarith
  have hcHi : cos (((207 : ℝ) / 1000)) < ((489326001 : ℝ) / 500000000) := by
    have hnum : 1 - (((207 : ℝ) / 1000)) ^ 2 / 2 + (((207 : ℝ) / 1000)) ^ 4 / 24 < ((489326001 : ℝ) / 500000000) := by norm_num
    linarith
  have hexp := exp_between (x := ((207 : ℝ) / 1000)) (n := 8) (lo := ((1229982571 : ℝ) / 1000000000)) (hi := ((307495643 : ℝ) / 250000000))
    ht0.le ht1 (by decide)
    (by norm_num [sum_range_succ, Nat.factorial])
    (by norm_num [sum_range_succ, Nat.factorial])
  have hph : ((41988777 : ℝ) / 200000000) < chordAmp (((207 : ℝ) / 1000)) ∧ chordAmp (((207 : ℝ) / 1000)) < ((209943891 : ℝ) / 1000000000) ∧
      ((956845867 : ℝ) / 1000000000) < gammaSEqual (((207 : ℝ) / 1000)) ∧ gammaSEqual (((207 : ℝ) / 1000)) < ((478422991 : ℝ) / 500000000) := by
    exact phase_bounds ht0 ht1 hsLo hsHi hcLo hcHi hexp.1 hexp.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨ht0, ht1, by norm_num, by norm_num, hph.1, hph.2.1, by norm_num, hph.2.2.1, hph.2.2.2⟩


private lemma phaseAt_208 :
    phaseHolds (((208 : ℝ) / 1000)) ((26373329 : ℝ) / 125000000) ((210986637 : ℝ) / 1000000000) ((956424937 : ℝ) / 1000000000) ((191285011 : ℝ) / 200000000) := by
  have ht0 : (0 : ℝ) < ((208 : ℝ) / 1000) := by norm_num
  have ht1 : ((208 : ℝ) / 1000) ≤ 1 := by norm_num
  obtain ⟨hs7, hs5, hc6, hc4⟩ := trigPoly_bounds ht0
  have hsLo : ((103251711 : ℝ) / 500000000) < sin (((208 : ℝ) / 1000)) := by
    have hnum : ((103251711 : ℝ) / 500000000) <
        ((208 : ℝ) / 1000) - (((208 : ℝ) / 1000)) ^ 3 / 6 + (((208 : ℝ) / 1000)) ^ 5 / 120 - (((208 : ℝ) / 1000)) ^ 7 / 5040 := by norm_num
    linarith
  have hsHi : sin (((208 : ℝ) / 1000)) < ((103251713 : ℝ) / 500000000) := by
    have hnum : ((208 : ℝ) / 1000) - (((208 : ℝ) / 1000)) ^ 3 / 6 + (((208 : ℝ) / 1000)) ^ 5 / 120 < ((103251713 : ℝ) / 500000000) := by norm_num
    linarith
  have hcLo : ((489222939 : ℝ) / 500000000) < cos (((208 : ℝ) / 1000)) := by
    have hnum : ((489222939 : ℝ) / 500000000) <
        1 - (((208 : ℝ) / 1000)) ^ 2 / 2 + (((208 : ℝ) / 1000)) ^ 4 / 24 - (((208 : ℝ) / 1000)) ^ 6 / 720 := by norm_num
    linarith
  have hcHi : cos (((208 : ℝ) / 1000)) < ((978445991 : ℝ) / 1000000000) := by
    have hnum : 1 - (((208 : ℝ) / 1000)) ^ 2 / 2 + (((208 : ℝ) / 1000)) ^ 4 / 24 < ((978445991 : ℝ) / 1000000000) := by norm_num
    linarith
  have hexp := exp_between (x := ((208 : ℝ) / 1000)) (n := 8) (lo := ((1231213169 : ℝ) / 1000000000)) (hi := ((123121317 : ℝ) / 100000000))
    ht0.le ht1 (by decide)
    (by norm_num [sum_range_succ, Nat.factorial])
    (by norm_num [sum_range_succ, Nat.factorial])
  have hph : ((26373329 : ℝ) / 125000000) < chordAmp (((208 : ℝ) / 1000)) ∧ chordAmp (((208 : ℝ) / 1000)) < ((210986637 : ℝ) / 1000000000) ∧
      ((956424937 : ℝ) / 1000000000) < gammaSEqual (((208 : ℝ) / 1000)) ∧ gammaSEqual (((208 : ℝ) / 1000)) < ((191285011 : ℝ) / 200000000) := by
    exact phase_bounds ht0 ht1 hsLo hsHi hcLo hcHi hexp.1 hexp.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨ht0, ht1, by norm_num, by norm_num, hph.1, hph.2.1, by norm_num, hph.2.2.1, hph.2.2.2⟩


private lemma phaseAt_211 :
    phaseHolds (((211 : ℝ) / 1000)) ((214117339 : ℝ) / 1000000000) ((42823469 : ℝ) / 200000000) ((7641197 : ℝ) / 8000000) ((238787439 : ℝ) / 250000000) := by
  have ht0 : (0 : ℝ) < ((211 : ℝ) / 1000) := by norm_num
  have ht1 : ((211 : ℝ) / 1000) ≤ 1 := by norm_num
  obtain ⟨hs7, hs5, hc6, hc4⟩ := trigPoly_bounds ht0
  have hsLo : ((104718913 : ℝ) / 500000000) < sin (((211 : ℝ) / 1000)) := by
    have hnum : ((104718913 : ℝ) / 500000000) <
        ((211 : ℝ) / 1000) - (((211 : ℝ) / 1000)) ^ 3 / 6 + (((211 : ℝ) / 1000)) ^ 5 / 120 - (((211 : ℝ) / 1000)) ^ 7 / 5040 := by norm_num
    linarith
  have hsHi : sin (((211 : ℝ) / 1000)) < ((209437831 : ℝ) / 1000000000) := by
    have hnum : ((211 : ℝ) / 1000) - (((211 : ℝ) / 1000)) ^ 3 / 6 + (((211 : ℝ) / 1000)) ^ 5 / 120 < ((209437831 : ℝ) / 1000000000) := by norm_num
    linarith
  have hcLo : ((195564393 : ℝ) / 200000000) < cos (((211 : ℝ) / 1000)) := by
    have hnum : ((195564393 : ℝ) / 200000000) <
        1 - (((211 : ℝ) / 1000)) ^ 2 / 2 + (((211 : ℝ) / 1000)) ^ 4 / 24 - (((211 : ℝ) / 1000)) ^ 6 / 720 := by norm_num
    linarith
  have hcHi : cos (((211 : ℝ) / 1000)) < ((977822089 : ℝ) / 1000000000) := by
    have hnum : 1 - (((211 : ℝ) / 1000)) ^ 2 / 2 + (((211 : ℝ) / 1000)) ^ 4 / 24 < ((977822089 : ℝ) / 1000000000) := by norm_num
    linarith
  have hexp := exp_between (x := ((211 : ℝ) / 1000)) (n := 8) (lo := ((617456177 : ℝ) / 500000000)) (hi := ((308728089 : ℝ) / 250000000))
    ht0.le ht1 (by decide)
    (by norm_num [sum_range_succ, Nat.factorial])
    (by norm_num [sum_range_succ, Nat.factorial])
  have hph : ((214117339 : ℝ) / 1000000000) < chordAmp (((211 : ℝ) / 1000)) ∧ chordAmp (((211 : ℝ) / 1000)) < ((42823469 : ℝ) / 200000000) ∧
      ((7641197 : ℝ) / 8000000) < gammaSEqual (((211 : ℝ) / 1000)) ∧ gammaSEqual (((211 : ℝ) / 1000)) < ((238787439 : ℝ) / 250000000) := by
    exact phase_bounds ht0 ht1 hsLo hsHi hcLo hcHi hexp.1 hexp.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨ht0, ht1, by norm_num, by norm_num, hph.1, hph.2.1, by norm_num, hph.2.2.1, hph.2.2.2⟩


private lemma phaseAt_212 :
    phaseHolds (((212 : ℝ) / 1000)) ((215161737 : ℝ) / 1000000000) ((215161743 : ℝ) / 1000000000) ((954720347 : ℝ) / 1000000000) ((954720481 : ℝ) / 1000000000) := by
  have ht0 : (0 : ℝ) < ((212 : ℝ) / 1000) := by norm_num
  have ht1 : ((212 : ℝ) / 1000) ≤ 1 := by norm_num
  obtain ⟨hs7, hs5, hc6, hc4⟩ := trigPoly_bounds ht0
  have hsLo : ((210415543 : ℝ) / 1000000000) < sin (((212 : ℝ) / 1000)) := by
    have hnum : ((210415543 : ℝ) / 1000000000) <
        ((212 : ℝ) / 1000) - (((212 : ℝ) / 1000)) ^ 3 / 6 + (((212 : ℝ) / 1000)) ^ 5 / 120 - (((212 : ℝ) / 1000)) ^ 7 / 5040 := by norm_num
    linarith
  have hsHi : sin (((212 : ℝ) / 1000)) < ((52603887 : ℝ) / 250000000) := by
    have hnum : ((212 : ℝ) / 1000) - (((212 : ℝ) / 1000)) ^ 3 / 6 + (((212 : ℝ) / 1000)) ^ 5 / 120 < ((52603887 : ℝ) / 250000000) := by norm_num
    linarith
  have hcLo : ((977612039 : ℝ) / 1000000000) < cos (((212 : ℝ) / 1000)) := by
    have hnum : ((977612039 : ℝ) / 1000000000) <
        1 - (((212 : ℝ) / 1000)) ^ 2 / 2 + (((212 : ℝ) / 1000)) ^ 4 / 24 - (((212 : ℝ) / 1000)) ^ 6 / 720 := by norm_num
    linarith
  have hcHi : cos (((212 : ℝ) / 1000)) < ((488806083 : ℝ) / 500000000) := by
    have hnum : 1 - (((212 : ℝ) / 1000)) ^ 2 / 2 + (((212 : ℝ) / 1000)) ^ 4 / 24 < ((488806083 : ℝ) / 500000000) := by norm_num
    linarith
  have hexp := exp_between (x := ((212 : ℝ) / 1000)) (n := 8) (lo := ((309036971 : ℝ) / 250000000)) (hi := ((618073943 : ℝ) / 500000000))
    ht0.le ht1 (by decide)
    (by norm_num [sum_range_succ, Nat.factorial])
    (by norm_num [sum_range_succ, Nat.factorial])
  have hph : ((215161737 : ℝ) / 1000000000) < chordAmp (((212 : ℝ) / 1000)) ∧ chordAmp (((212 : ℝ) / 1000)) < ((215161743 : ℝ) / 1000000000) ∧
      ((954720347 : ℝ) / 1000000000) < gammaSEqual (((212 : ℝ) / 1000)) ∧ gammaSEqual (((212 : ℝ) / 1000)) < ((954720481 : ℝ) / 1000000000) := by
    exact phase_bounds ht0 ht1 hsLo hsHi hcLo hcHi hexp.1 hexp.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨ht0, ht1, by norm_num, by norm_num, hph.1, hph.2.1, by norm_num, hph.2.2.1, hph.2.2.2⟩


private lemma phaseAt_214 :
    phaseHolds (((214 : ℝ) / 1000)) ((217251787 : ℝ) / 1000000000) ((217251793 : ℝ) / 1000000000) ((953855521 : ℝ) / 1000000000) ((953855661 : ℝ) / 1000000000) := by
  have ht0 : (0 : ℝ) < ((214 : ℝ) / 1000) := by norm_num
  have ht1 : ((214 : ℝ) / 1000) ≤ 1 := by norm_num
  obtain ⟨hs7, hs5, hc6, hc4⟩ := trigPoly_bounds ht0
  have hsLo : ((42474069 : ℝ) / 200000000) < sin (((214 : ℝ) / 1000)) := by
    have hnum : ((42474069 : ℝ) / 200000000) <
        ((214 : ℝ) / 1000) - (((214 : ℝ) / 1000)) ^ 3 / 6 + (((214 : ℝ) / 1000)) ^ 5 / 120 - (((214 : ℝ) / 1000)) ^ 7 / 5040 := by norm_num
    linarith
  have hsHi : sin (((214 : ℝ) / 1000)) < ((4247407 : ℝ) / 20000000) := by
    have hnum : ((214 : ℝ) / 1000) - (((214 : ℝ) / 1000)) ^ 3 / 6 + (((214 : ℝ) / 1000)) ^ 5 / 120 < ((4247407 : ℝ) / 20000000) := by norm_num
    linarith
  have hcLo : ((977189253 : ℝ) / 1000000000) < cos (((214 : ℝ) / 1000)) := by
    have hnum : ((977189253 : ℝ) / 1000000000) <
        1 - (((214 : ℝ) / 1000)) ^ 2 / 2 + (((214 : ℝ) / 1000)) ^ 4 / 24 - (((214 : ℝ) / 1000)) ^ 6 / 720 := by norm_num
    linarith
  have hcHi : cos (((214 : ℝ) / 1000)) < ((977189387 : ℝ) / 1000000000) := by
    have hnum : 1 - (((214 : ℝ) / 1000)) ^ 2 / 2 + (((214 : ℝ) / 1000)) ^ 4 / 24 < ((977189387 : ℝ) / 1000000000) := by norm_num
    linarith
  have hexp := exp_between (x := ((214 : ℝ) / 1000)) (n := 8) (lo := ((619311327 : ℝ) / 500000000)) (hi := ((247724531 : ℝ) / 200000000))
    ht0.le ht1 (by decide)
    (by norm_num [sum_range_succ, Nat.factorial])
    (by norm_num [sum_range_succ, Nat.factorial])
  have hph : ((217251787 : ℝ) / 1000000000) < chordAmp (((214 : ℝ) / 1000)) ∧ chordAmp (((214 : ℝ) / 1000)) < ((217251793 : ℝ) / 1000000000) ∧
      ((953855521 : ℝ) / 1000000000) < gammaSEqual (((214 : ℝ) / 1000)) ∧ gammaSEqual (((214 : ℝ) / 1000)) < ((953855661 : ℝ) / 1000000000) := by
    exact phase_bounds ht0 ht1 hsLo hsHi hcLo hcHi hexp.1 hexp.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨ht0, ht1, by norm_num, by norm_num, hph.1, hph.2.1, by norm_num, hph.2.2.1, hph.2.2.2⟩


private lemma phaseAt_220 :
    phaseHolds (((220 : ℝ) / 1000)) ((111766057 : ℝ) / 500000000) ((111766061 : ℝ) / 500000000) ((951210833 : ℝ) / 1000000000) ((475605499 : ℝ) / 500000000) := by
  have ht0 : (0 : ℝ) < ((220 : ℝ) / 1000) := by norm_num
  have ht1 : ((220 : ℝ) / 1000) ≤ 1 := by norm_num
  obtain ⟨hs7, hs5, hc6, hc4⟩ := trigPoly_bounds ht0
  have hsLo : ((218229623 : ℝ) / 1000000000) < sin (((220 : ℝ) / 1000)) := by
    have hnum : ((218229623 : ℝ) / 1000000000) <
        ((220 : ℝ) / 1000) - (((220 : ℝ) / 1000)) ^ 3 / 6 + (((220 : ℝ) / 1000)) ^ 5 / 120 - (((220 : ℝ) / 1000)) ^ 7 / 5040 := by norm_num
    linarith
  have hsHi : sin (((220 : ℝ) / 1000)) < ((218229629 : ℝ) / 1000000000) := by
    have hnum : ((220 : ℝ) / 1000) - (((220 : ℝ) / 1000)) ^ 3 / 6 + (((220 : ℝ) / 1000)) ^ 5 / 120 < ((218229629 : ℝ) / 1000000000) := by norm_num
    linarith
  have hcLo : ((975897449 : ℝ) / 1000000000) < cos (((220 : ℝ) / 1000)) := by
    have hnum : ((975897449 : ℝ) / 1000000000) <
        1 - (((220 : ℝ) / 1000)) ^ 2 / 2 + (((220 : ℝ) / 1000)) ^ 4 / 24 - (((220 : ℝ) / 1000)) ^ 6 / 720 := by norm_num
    linarith
  have hcHi : cos (((220 : ℝ) / 1000)) < ((975897607 : ℝ) / 1000000000) := by
    have hnum : 1 - (((220 : ℝ) / 1000)) ^ 2 / 2 + (((220 : ℝ) / 1000)) ^ 4 / 24 < ((975897607 : ℝ) / 1000000000) := by norm_num
    linarith
  have hexp := exp_between (x := ((220 : ℝ) / 1000)) (n := 8) (lo := ((124607673 : ℝ) / 100000000)) (hi := ((1246076731 : ℝ) / 1000000000))
    ht0.le ht1 (by decide)
    (by norm_num [sum_range_succ, Nat.factorial])
    (by norm_num [sum_range_succ, Nat.factorial])
  have hph : ((111766057 : ℝ) / 500000000) < chordAmp (((220 : ℝ) / 1000)) ∧ chordAmp (((220 : ℝ) / 1000)) < ((111766061 : ℝ) / 500000000) ∧
      ((951210833 : ℝ) / 1000000000) < gammaSEqual (((220 : ℝ) / 1000)) ∧ gammaSEqual (((220 : ℝ) / 1000)) < ((475605499 : ℝ) / 500000000) := by
    exact phase_bounds ht0 ht1 hsLo hsHi hcLo hcHi hexp.1 hexp.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨ht0, ht1, by norm_num, by norm_num, hph.1, hph.2.1, by norm_num, hph.2.2.1, hph.2.2.2⟩


private lemma phaseAt_221 :
    phaseHolds (((221 : ℝ) / 1000)) ((224580339 : ℝ) / 1000000000) ((224580347 : ℝ) / 1000000000) ((5942267 : ℝ) / 6250000) ((95076289 : ℝ) / 100000000) := by
  have ht0 : (0 : ℝ) < ((221 : ℝ) / 1000) := by norm_num
  have ht1 : ((221 : ℝ) / 1000) ≤ 1 := by norm_num
  obtain ⟨hs7, hs5, hc6, hc4⟩ := trigPoly_bounds ht0
  have hsLo : ((219205411 : ℝ) / 1000000000) < sin (((221 : ℝ) / 1000)) := by
    have hnum : ((219205411 : ℝ) / 1000000000) <
        ((221 : ℝ) / 1000) - (((221 : ℝ) / 1000)) ^ 3 / 6 + (((221 : ℝ) / 1000)) ^ 5 / 120 - (((221 : ℝ) / 1000)) ^ 7 / 5040 := by norm_num
    linarith
  have hsHi : sin (((221 : ℝ) / 1000)) < ((219205417 : ℝ) / 1000000000) := by
    have hnum : ((221 : ℝ) / 1000) - (((221 : ℝ) / 1000)) ^ 3 / 6 + (((221 : ℝ) / 1000)) ^ 5 / 120 < ((219205417 : ℝ) / 1000000000) := by norm_num
    linarith
  have hcLo : ((975678731 : ℝ) / 1000000000) < cos (((221 : ℝ) / 1000)) := by
    have hnum : ((975678731 : ℝ) / 1000000000) <
        1 - (((221 : ℝ) / 1000)) ^ 2 / 2 + (((221 : ℝ) / 1000)) ^ 4 / 24 - (((221 : ℝ) / 1000)) ^ 6 / 720 := by norm_num
    linarith
  have hcHi : cos (((221 : ℝ) / 1000)) < ((487839447 : ℝ) / 500000000) := by
    have hnum : 1 - (((221 : ℝ) / 1000)) ^ 2 / 2 + (((221 : ℝ) / 1000)) ^ 4 / 24 < ((487839447 : ℝ) / 500000000) := by norm_num
    linarith
  have hexp := exp_between (x := ((221 : ℝ) / 1000)) (n := 8) (lo := ((124732343 : ℝ) / 100000000)) (hi := ((1247323431 : ℝ) / 1000000000))
    ht0.le ht1 (by decide)
    (by norm_num [sum_range_succ, Nat.factorial])
    (by norm_num [sum_range_succ, Nat.factorial])
  have hph : ((224580339 : ℝ) / 1000000000) < chordAmp (((221 : ℝ) / 1000)) ∧ chordAmp (((221 : ℝ) / 1000)) < ((224580347 : ℝ) / 1000000000) ∧
      ((5942267 : ℝ) / 6250000) < gammaSEqual (((221 : ℝ) / 1000)) ∧ gammaSEqual (((221 : ℝ) / 1000)) < ((95076289 : ℝ) / 100000000) := by
    exact phase_bounds ht0 ht1 hsLo hsHi hcLo hcHi hexp.1 hexp.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨ht0, ht1, by norm_num, by norm_num, hph.1, hph.2.1, by norm_num, hph.2.2.1, hph.2.2.2⟩


private lemma phaseAt_222 :
    phaseHolds (((222 : ℝ) / 1000)) ((225628999 : ℝ) / 1000000000) ((112814503 : ℝ) / 500000000) ((950312511 : ℝ) / 1000000000) ((190062537 : ℝ) / 200000000) := by
  have ht0 : (0 : ℝ) < ((222 : ℝ) / 1000) := by norm_num
  have ht1 : ((222 : ℝ) / 1000) ≤ 1 := by norm_num
  obtain ⟨hs7, hs5, hc6, hc4⟩ := trigPoly_bounds ht0
  have hsLo : ((11009049 : ℝ) / 50000000) < sin (((222 : ℝ) / 1000)) := by
    have hnum : ((11009049 : ℝ) / 50000000) <
        ((222 : ℝ) / 1000) - (((222 : ℝ) / 1000)) ^ 3 / 6 + (((222 : ℝ) / 1000)) ^ 5 / 120 - (((222 : ℝ) / 1000)) ^ 7 / 5040 := by norm_num
    linarith
  have hsHi : sin (((222 : ℝ) / 1000)) < ((110090493 : ℝ) / 500000000) := by
    have hnum : ((222 : ℝ) / 1000) - (((222 : ℝ) / 1000)) ^ 3 / 6 + (((222 : ℝ) / 1000)) ^ 5 / 120 < ((110090493 : ℝ) / 500000000) := by norm_num
    linarith
  have hcLo : ((487729519 : ℝ) / 500000000) < cos (((222 : ℝ) / 1000)) := by
    have hnum : ((487729519 : ℝ) / 500000000) <
        1 - (((222 : ℝ) / 1000)) ^ 2 / 2 + (((222 : ℝ) / 1000)) ^ 4 / 24 - (((222 : ℝ) / 1000)) ^ 6 / 720 := by norm_num
    linarith
  have hcHi : cos (((222 : ℝ) / 1000)) < ((195091841 : ℝ) / 200000000) := by
    have hnum : 1 - (((222 : ℝ) / 1000)) ^ 2 / 2 + (((222 : ℝ) / 1000)) ^ 4 / 24 < ((195091841 : ℝ) / 200000000) := by norm_num
    linarith
  have hexp := exp_between (x := ((222 : ℝ) / 1000)) (n := 8) (lo := ((1248571377 : ℝ) / 1000000000)) (hi := ((624285689 : ℝ) / 500000000))
    ht0.le ht1 (by decide)
    (by norm_num [sum_range_succ, Nat.factorial])
    (by norm_num [sum_range_succ, Nat.factorial])
  have hph : ((225628999 : ℝ) / 1000000000) < chordAmp (((222 : ℝ) / 1000)) ∧ chordAmp (((222 : ℝ) / 1000)) < ((112814503 : ℝ) / 500000000) ∧
      ((950312511 : ℝ) / 1000000000) < gammaSEqual (((222 : ℝ) / 1000)) ∧ gammaSEqual (((222 : ℝ) / 1000)) < ((190062537 : ℝ) / 200000000) := by
    exact phase_bounds ht0 ht1 hsLo hsHi hcLo hcHi hexp.1 hexp.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨ht0, ht1, by norm_num, by norm_num, hph.1, hph.2.1, by norm_num, hph.2.2.1, hph.2.2.2⟩


private lemma phaseAt_223 :
    phaseHolds (((223 : ℝ) / 1000)) ((14167381 : ℝ) / 62500000) ((226678103 : ℝ) / 1000000000) ((949860203 : ℝ) / 1000000000) ((949860383 : ℝ) / 1000000000) := by
  have ht0 : (0 : ℝ) < ((223 : ℝ) / 1000) := by norm_num
  have ht1 : ((223 : ℝ) / 1000) ≤ 1 := by norm_num
  obtain ⟨hs7, hs5, hc6, hc4⟩ := trigPoly_bounds ht0
  have hsLo : ((221156329 : ℝ) / 1000000000) < sin (((223 : ℝ) / 1000)) := by
    have hnum : ((221156329 : ℝ) / 1000000000) <
        ((223 : ℝ) / 1000) - (((223 : ℝ) / 1000)) ^ 3 / 6 + (((223 : ℝ) / 1000)) ^ 5 / 120 - (((223 : ℝ) / 1000)) ^ 7 / 5040 := by norm_num
    linarith
  have hsHi : sin (((223 : ℝ) / 1000)) < ((44231267 : ℝ) / 200000000) := by
    have hnum : ((223 : ℝ) / 1000) - (((223 : ℝ) / 1000)) ^ 3 / 6 + (((223 : ℝ) / 1000)) ^ 5 / 120 < ((44231267 : ℝ) / 200000000) := by norm_num
    linarith
  have hcLo : ((975238369 : ℝ) / 1000000000) < cos (((223 : ℝ) / 1000)) := by
    have hnum : ((975238369 : ℝ) / 1000000000) <
        1 - (((223 : ℝ) / 1000)) ^ 2 / 2 + (((223 : ℝ) / 1000)) ^ 4 / 24 - (((223 : ℝ) / 1000)) ^ 6 / 720 := by norm_num
    linarith
  have hcHi : cos (((223 : ℝ) / 1000)) < ((975238541 : ℝ) / 1000000000) := by
    have hnum : 1 - (((223 : ℝ) / 1000)) ^ 2 / 2 + (((223 : ℝ) / 1000)) ^ 4 / 24 < ((975238541 : ℝ) / 1000000000) := by norm_num
    linarith
  have hexp := exp_between (x := ((223 : ℝ) / 1000)) (n := 8) (lo := ((1249820573 : ℝ) / 1000000000)) (hi := ((624910287 : ℝ) / 500000000))
    ht0.le ht1 (by decide)
    (by norm_num [sum_range_succ, Nat.factorial])
    (by norm_num [sum_range_succ, Nat.factorial])
  have hph : ((14167381 : ℝ) / 62500000) < chordAmp (((223 : ℝ) / 1000)) ∧ chordAmp (((223 : ℝ) / 1000)) < ((226678103 : ℝ) / 1000000000) ∧
      ((949860203 : ℝ) / 1000000000) < gammaSEqual (((223 : ℝ) / 1000)) ∧ gammaSEqual (((223 : ℝ) / 1000)) < ((949860383 : ℝ) / 1000000000) := by
    exact phase_bounds ht0 ht1 hsLo hsHi hcLo hcHi hexp.1 hexp.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨ht0, ht1, by norm_num, by norm_num, hph.1, hph.2.1, by norm_num, hph.2.2.1, hph.2.2.2⟩


private lemma phaseAt_229 :
    phaseHolds (((229 : ℝ) / 1000)) ((232981951 : ℝ) / 1000000000) ((232981959 : ℝ) / 1000000000) ((947102259 : ℝ) / 1000000000) ((947102469 : ℝ) / 1000000000) := by
  have ht0 : (0 : ℝ) < ((229 : ℝ) / 1000) := by norm_num
  have ht1 : ((229 : ℝ) / 1000) ≤ 1 := by norm_num
  obtain ⟨hs7, hs5, hc6, hc4⟩ := trigPoly_bounds ht0
  have hsLo : ((227003743 : ℝ) / 1000000000) < sin (((229 : ℝ) / 1000)) := by
    have hnum : ((227003743 : ℝ) / 1000000000) <
        ((229 : ℝ) / 1000) - (((229 : ℝ) / 1000)) ^ 3 / 6 + (((229 : ℝ) / 1000)) ^ 5 / 120 - (((229 : ℝ) / 1000)) ^ 7 / 5040 := by norm_num
    linarith
  have hsHi : sin (((229 : ℝ) / 1000)) < ((181603 : ℝ) / 800000) := by
    have hnum : ((229 : ℝ) / 1000) - (((229 : ℝ) / 1000)) ^ 3 / 6 + (((229 : ℝ) / 1000)) ^ 5 / 120 < ((181603 : ℝ) / 800000) := by norm_num
    linarith
  have hcLo : ((194778777 : ℝ) / 200000000) < cos (((229 : ℝ) / 1000)) := by
    have hnum : ((194778777 : ℝ) / 200000000) <
        1 - (((229 : ℝ) / 1000)) ^ 2 / 2 + (((229 : ℝ) / 1000)) ^ 4 / 24 - (((229 : ℝ) / 1000)) ^ 6 / 720 := by norm_num
    linarith
  have hcHi : cos (((229 : ℝ) / 1000)) < ((486947043 : ℝ) / 500000000) := by
    have hnum : 1 - (((229 : ℝ) / 1000)) ^ 2 / 2 + (((229 : ℝ) / 1000)) ^ 4 / 24 < ((486947043 : ℝ) / 500000000) := by norm_num
    linarith
  have hexp := exp_between (x := ((229 : ℝ) / 1000)) (n := 8) (lo := ((628671019 : ℝ) / 500000000)) (hi := ((31433551 : ℝ) / 25000000))
    ht0.le ht1 (by decide)
    (by norm_num [sum_range_succ, Nat.factorial])
    (by norm_num [sum_range_succ, Nat.factorial])
  have hph : ((232981951 : ℝ) / 1000000000) < chordAmp (((229 : ℝ) / 1000)) ∧ chordAmp (((229 : ℝ) / 1000)) < ((232981959 : ℝ) / 1000000000) ∧
      ((947102259 : ℝ) / 1000000000) < gammaSEqual (((229 : ℝ) / 1000)) ∧ gammaSEqual (((229 : ℝ) / 1000)) < ((947102469 : ℝ) / 1000000000) := by
    exact phase_bounds ht0 ht1 hsLo hsHi hcLo hcHi hexp.1 hexp.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨ht0, ht1, by norm_num, by norm_num, hph.1, hph.2.1, by norm_num, hph.2.2.1, hph.2.2.2⟩


private lemma phaseAt_230 :
    phaseHolds (((230 : ℝ) / 1000)) ((234034157 : ℝ) / 1000000000) ((117017083 : ℝ) / 500000000) ((946635243 : ℝ) / 1000000000) ((946635459 : ℝ) / 1000000000) := by
  have ht0 : (0 : ℝ) < ((230 : ℝ) / 1000) := by norm_num
  have ht1 : ((230 : ℝ) / 1000) ≤ 1 := by norm_num
  obtain ⟨hs7, hs5, hc6, hc4⟩ := trigPoly_bounds ht0
  have hsLo : ((227977523 : ℝ) / 1000000000) < sin (((230 : ℝ) / 1000)) := by
    have hnum : ((227977523 : ℝ) / 1000000000) <
        ((230 : ℝ) / 1000) - (((230 : ℝ) / 1000)) ^ 3 / 6 + (((230 : ℝ) / 1000)) ^ 5 / 120 - (((230 : ℝ) / 1000)) ^ 7 / 5040 := by norm_num
    linarith
  have hsHi : sin (((230 : ℝ) / 1000)) < ((227977531 : ℝ) / 1000000000) := by
    have hnum : ((230 : ℝ) / 1000) - (((230 : ℝ) / 1000)) ^ 3 / 6 + (((230 : ℝ) / 1000)) ^ 5 / 120 < ((227977531 : ℝ) / 1000000000) := by norm_num
    linarith
  have hcLo : ((486833197 : ℝ) / 500000000) < cos (((230 : ℝ) / 1000)) := by
    have hnum : ((486833197 : ℝ) / 500000000) <
        1 - (((230 : ℝ) / 1000)) ^ 2 / 2 + (((230 : ℝ) / 1000)) ^ 4 / 24 - (((230 : ℝ) / 1000)) ^ 6 / 720 := by norm_num
    linarith
  have hcHi : cos (((230 : ℝ) / 1000)) < ((973666601 : ℝ) / 1000000000) := by
    have hnum : 1 - (((230 : ℝ) / 1000)) ^ 2 / 2 + (((230 : ℝ) / 1000)) ^ 4 / 24 < ((973666601 : ℝ) / 1000000000) := by norm_num
    linarith
  have hexp := exp_between (x := ((230 : ℝ) / 1000)) (n := 8) (lo := ((1258600009 : ℝ) / 1000000000)) (hi := ((125860001 : ℝ) / 100000000))
    ht0.le ht1 (by decide)
    (by norm_num [sum_range_succ, Nat.factorial])
    (by norm_num [sum_range_succ, Nat.factorial])
  have hph : ((234034157 : ℝ) / 1000000000) < chordAmp (((230 : ℝ) / 1000)) ∧ chordAmp (((230 : ℝ) / 1000)) < ((117017083 : ℝ) / 500000000) ∧
      ((946635243 : ℝ) / 1000000000) < gammaSEqual (((230 : ℝ) / 1000)) ∧ gammaSEqual (((230 : ℝ) / 1000)) < ((946635459 : ℝ) / 1000000000) := by
    exact phase_bounds ht0 ht1 hsLo hsHi hcLo hcHi hexp.1 hexp.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨ht0, ht1, by norm_num, by norm_num, hph.1, hph.2.1, by norm_num, hph.2.2.1, hph.2.2.2⟩


private lemma phaseAt_238 :
    phaseHolds (((238 : ℝ) / 1000)) ((242468233 : ℝ) / 1000000000) ((60617061 : ℝ) / 250000000) ((471411631 : ℝ) / 500000000) ((117852941 : ℝ) / 125000000) := by
  have ht0 : (0 : ℝ) < ((238 : ℝ) / 1000) := by norm_num
  have ht1 : ((238 : ℝ) / 1000) ≤ 1 := by norm_num
  obtain ⟨hs7, hs5, hc6, hc4⟩ := trigPoly_bounds ht0
  have hsLo : ((58939869 : ℝ) / 250000000) < sin (((238 : ℝ) / 1000)) := by
    have hnum : ((58939869 : ℝ) / 250000000) <
        ((238 : ℝ) / 1000) - (((238 : ℝ) / 1000)) ^ 3 / 6 + (((238 : ℝ) / 1000)) ^ 5 / 120 - (((238 : ℝ) / 1000)) ^ 7 / 5040 := by norm_num
    linarith
  have hsHi : sin (((238 : ℝ) / 1000)) < ((47151897 : ℝ) / 200000000) := by
    have hnum : ((238 : ℝ) / 1000) - (((238 : ℝ) / 1000)) ^ 3 / 6 + (((238 : ℝ) / 1000)) ^ 5 / 120 < ((47151897 : ℝ) / 200000000) := by norm_num
    linarith
  have hcLo : ((242952859 : ℝ) / 250000000) < cos (((238 : ℝ) / 1000)) := by
    have hnum : ((242952859 : ℝ) / 250000000) <
        1 - (((238 : ℝ) / 1000)) ^ 2 / 2 + (((238 : ℝ) / 1000)) ^ 4 / 24 - (((238 : ℝ) / 1000)) ^ 6 / 720 := by norm_num
    linarith
  have hcHi : cos (((238 : ℝ) / 1000)) < ((97181169 : ℝ) / 100000000) := by
    have hnum : 1 - (((238 : ℝ) / 1000)) ^ 2 / 2 + (((238 : ℝ) / 1000)) ^ 4 / 24 < ((97181169 : ℝ) / 100000000) := by norm_num
    linarith
  have hexp := exp_between (x := ((238 : ℝ) / 1000)) (n := 8) (lo := ((158588649 : ℝ) / 125000000)) (hi := ((1268709193 : ℝ) / 1000000000))
    ht0.le ht1 (by decide)
    (by norm_num [sum_range_succ, Nat.factorial])
    (by norm_num [sum_range_succ, Nat.factorial])
  have hph : ((242468233 : ℝ) / 1000000000) < chordAmp (((238 : ℝ) / 1000)) ∧ chordAmp (((238 : ℝ) / 1000)) < ((60617061 : ℝ) / 250000000) ∧
      ((471411631 : ℝ) / 500000000) < gammaSEqual (((238 : ℝ) / 1000)) ∧ gammaSEqual (((238 : ℝ) / 1000)) < ((117852941 : ℝ) / 125000000) := by
    exact phase_bounds ht0 ht1 hsLo hsHi hcLo hcHi hexp.1 hexp.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨ht0, ht1, by norm_num, by norm_num, hph.1, hph.2.1, by norm_num, hph.2.2.1, hph.2.2.2⟩


private lemma phaseAt_239 :
    phaseHolds (((239 : ℝ) / 1000)) ((121762287 : ℝ) / 500000000) ((48704917 : ℝ) / 200000000) ((94233727 : ℝ) / 100000000) ((942337541 : ℝ) / 1000000000) := by
  have ht0 : (0 : ℝ) < ((239 : ℝ) / 1000) := by norm_num
  have ht1 : ((239 : ℝ) / 1000) ≤ 1 := by norm_num
  obtain ⟨hs7, hs5, hc6, hc4⟩ := trigPoly_bounds ht0
  have hsLo : ((236731169 : ℝ) / 1000000000) < sin (((239 : ℝ) / 1000)) := by
    have hnum : ((236731169 : ℝ) / 1000000000) <
        ((239 : ℝ) / 1000) - (((239 : ℝ) / 1000)) ^ 3 / 6 + (((239 : ℝ) / 1000)) ^ 5 / 120 - (((239 : ℝ) / 1000)) ^ 7 / 5040 := by norm_num
    linarith
  have hsHi : sin (((239 : ℝ) / 1000)) < ((236731179 : ℝ) / 1000000000) := by
    have hnum : ((239 : ℝ) / 1000) - (((239 : ℝ) / 1000)) ^ 3 / 6 + (((239 : ℝ) / 1000)) ^ 5 / 120 < ((236731179 : ℝ) / 1000000000) := by norm_num
    linarith
  have hcLo : ((971575191 : ℝ) / 1000000000) < cos (((239 : ℝ) / 1000)) := by
    have hnum : ((971575191 : ℝ) / 1000000000) <
        1 - (((239 : ℝ) / 1000)) ^ 2 / 2 + (((239 : ℝ) / 1000)) ^ 4 / 24 - (((239 : ℝ) / 1000)) ^ 6 / 720 := by norm_num
    linarith
  have hcHi : cos (((239 : ℝ) / 1000)) < ((971575451 : ℝ) / 1000000000) := by
    have hnum : 1 - (((239 : ℝ) / 1000)) ^ 2 / 2 + (((239 : ℝ) / 1000)) ^ 4 / 24 < ((971575451 : ℝ) / 1000000000) := by norm_num
    linarith
  have hexp := exp_between (x := ((239 : ℝ) / 1000)) (n := 8) (lo := ((158747317 : ℝ) / 125000000)) (hi := ((1269978537 : ℝ) / 1000000000))
    ht0.le ht1 (by decide)
    (by norm_num [sum_range_succ, Nat.factorial])
    (by norm_num [sum_range_succ, Nat.factorial])
  have hph : ((121762287 : ℝ) / 500000000) < chordAmp (((239 : ℝ) / 1000)) ∧ chordAmp (((239 : ℝ) / 1000)) < ((48704917 : ℝ) / 200000000) ∧
      ((94233727 : ℝ) / 100000000) < gammaSEqual (((239 : ℝ) / 1000)) ∧ gammaSEqual (((239 : ℝ) / 1000)) < ((942337541 : ℝ) / 1000000000) := by
    exact phase_bounds ht0 ht1 hsLo hsHi hcLo hcHi hexp.1 hexp.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨ht0, ht1, by norm_num, by norm_num, hph.1, hph.2.1, by norm_num, hph.2.2.1, hph.2.2.2⟩


private lemma phaseAt_241 :
    phaseHolds (((241 : ℝ) / 1000)) ((49127733 : ℝ) / 200000000) ((61409669 : ℝ) / 250000000) ((941358943 : ℝ) / 1000000000) ((94135923 : ℝ) / 100000000) := by
  have ht0 : (0 : ℝ) < ((241 : ℝ) / 1000) := by norm_num
  have ht1 : ((241 : ℝ) / 1000) ≤ 1 := by norm_num
  obtain ⟨hs7, hs5, hc6, hc4⟩ := trigPoly_bounds ht0
  have hsLo : ((47734769 : ℝ) / 200000000) < sin (((241 : ℝ) / 1000)) := by
    have hnum : ((47734769 : ℝ) / 200000000) <
        ((241 : ℝ) / 1000) - (((241 : ℝ) / 1000)) ^ 3 / 6 + (((241 : ℝ) / 1000)) ^ 5 / 120 - (((241 : ℝ) / 1000)) ^ 7 / 5040 := by norm_num
    linarith
  have hsHi : sin (((241 : ℝ) / 1000)) < ((47734771 : ℝ) / 200000000) := by
    have hnum : ((241 : ℝ) / 1000) - (((241 : ℝ) / 1000)) ^ 3 / 6 + (((241 : ℝ) / 1000)) ^ 5 / 120 < ((47734771 : ℝ) / 200000000) := by norm_num
    linarith
  have hcLo : ((485549893 : ℝ) / 500000000) < cos (((241 : ℝ) / 1000)) := by
    have hnum : ((485549893 : ℝ) / 500000000) <
        1 - (((241 : ℝ) / 1000)) ^ 2 / 2 + (((241 : ℝ) / 1000)) ^ 4 / 24 - (((241 : ℝ) / 1000)) ^ 6 / 720 := by norm_num
    linarith
  have hcHi : cos (((241 : ℝ) / 1000)) < ((971100059 : ℝ) / 1000000000) := by
    have hnum : 1 - (((241 : ℝ) / 1000)) ^ 2 / 2 + (((241 : ℝ) / 1000)) ^ 4 / 24 < ((971100059 : ℝ) / 1000000000) := by norm_num
    linarith
  have hexp := exp_between (x := ((241 : ℝ) / 1000)) (n := 8) (lo := ((636260517 : ℝ) / 500000000)) (hi := ((318130259 : ℝ) / 250000000))
    ht0.le ht1 (by decide)
    (by norm_num [sum_range_succ, Nat.factorial])
    (by norm_num [sum_range_succ, Nat.factorial])
  have hph : ((49127733 : ℝ) / 200000000) < chordAmp (((241 : ℝ) / 1000)) ∧ chordAmp (((241 : ℝ) / 1000)) < ((61409669 : ℝ) / 250000000) ∧
      ((941358943 : ℝ) / 1000000000) < gammaSEqual (((241 : ℝ) / 1000)) ∧ gammaSEqual (((241 : ℝ) / 1000)) < ((94135923 : ℝ) / 100000000) := by
    exact phase_bounds ht0 ht1 hsLo hsHi hcLo hcHi hexp.1 hexp.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨ht0, ht1, by norm_num, by norm_num, hph.1, hph.2.1, by norm_num, hph.2.2.1, hph.2.2.2⟩


private lemma phaseAt_242 :
    phaseHolds (((242 : ℝ) / 1000)) ((123348209 : ℝ) / 500000000) ((24669643 : ℝ) / 100000000) ((58804163 : ℝ) / 62500000) ((940866901 : ℝ) / 1000000000) := by
  have ht0 : (0 : ℝ) < ((242 : ℝ) / 1000) := by norm_num
  have ht1 : ((242 : ℝ) / 1000) ≤ 1 := by norm_num
  obtain ⟨hs7, hs5, hc6, hc4⟩ := trigPoly_bounds ht0
  have hsLo : ((9585793 : ℝ) / 40000000) < sin (((242 : ℝ) / 1000)) := by
    have hnum : ((9585793 : ℝ) / 40000000) <
        ((242 : ℝ) / 1000) - (((242 : ℝ) / 1000)) ^ 3 / 6 + (((242 : ℝ) / 1000)) ^ 5 / 120 - (((242 : ℝ) / 1000)) ^ 7 / 5040 := by norm_num
    linarith
  have hsHi : sin (((242 : ℝ) / 1000)) < ((59911209 : ℝ) / 250000000) := by
    have hnum : ((242 : ℝ) / 1000) - (((242 : ℝ) / 1000)) ^ 3 / 6 + (((242 : ℝ) / 1000)) ^ 5 / 120 < ((59911209 : ℝ) / 250000000) := by norm_num
    linarith
  have hcLo : ((485430313 : ℝ) / 500000000) < cos (((242 : ℝ) / 1000)) := by
    have hnum : ((485430313 : ℝ) / 500000000) <
        1 - (((242 : ℝ) / 1000)) ^ 2 / 2 + (((242 : ℝ) / 1000)) ^ 4 / 24 - (((242 : ℝ) / 1000)) ^ 6 / 720 := by norm_num
    linarith
  have hcHi : cos (((242 : ℝ) / 1000)) < ((485430453 : ℝ) / 500000000) := by
    have hnum : 1 - (((242 : ℝ) / 1000)) ^ 2 / 2 + (((242 : ℝ) / 1000)) ^ 4 / 24 < ((485430453 : ℝ) / 500000000) := by norm_num
    linarith
  have hexp := exp_between (x := ((242 : ℝ) / 1000)) (n := 8) (lo := ((79612137 : ℝ) / 62500000)) (hi := ((1273794193 : ℝ) / 1000000000))
    ht0.le ht1 (by decide)
    (by norm_num [sum_range_succ, Nat.factorial])
    (by norm_num [sum_range_succ, Nat.factorial])
  have hph : ((123348209 : ℝ) / 500000000) < chordAmp (((242 : ℝ) / 1000)) ∧ chordAmp (((242 : ℝ) / 1000)) < ((24669643 : ℝ) / 100000000) ∧
      ((58804163 : ℝ) / 62500000) < gammaSEqual (((242 : ℝ) / 1000)) ∧ gammaSEqual (((242 : ℝ) / 1000)) < ((940866901 : ℝ) / 1000000000) := by
    exact phase_bounds ht0 ht1 hsLo hsHi hcLo hcHi hexp.1 hexp.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨ht0, ht1, by norm_num, by norm_num, hph.1, hph.2.1, by norm_num, hph.2.2.1, hph.2.2.2⟩


private lemma phaseAt_243 :
    phaseHolds (((243 : ℝ) / 1000)) ((123877323 : ℝ) / 500000000) ((123877329 : ℝ) / 500000000) ((940372157 : ℝ) / 1000000000) ((470186229 : ℝ) / 500000000) := by
  have ht0 : (0 : ℝ) < ((243 : ℝ) / 1000) := by norm_num
  have ht1 : ((243 : ℝ) / 1000) ≤ 1 := by norm_num
  obtain ⟨hs7, hs5, hc6, hc4⟩ := trigPoly_bounds ht0
  have hsLo : ((120307783 : ℝ) / 500000000) < sin (((243 : ℝ) / 1000)) := by
    have hnum : ((120307783 : ℝ) / 500000000) <
        ((243 : ℝ) / 1000) - (((243 : ℝ) / 1000)) ^ 3 / 6 + (((243 : ℝ) / 1000)) ^ 5 / 120 - (((243 : ℝ) / 1000)) ^ 7 / 5040 := by norm_num
    linarith
  have hsHi : sin (((243 : ℝ) / 1000)) < ((240615577 : ℝ) / 1000000000) := by
    have hnum : ((243 : ℝ) / 1000) - (((243 : ℝ) / 1000)) ^ 3 / 6 + (((243 : ℝ) / 1000)) ^ 5 / 120 < ((240615577 : ℝ) / 1000000000) := by norm_num
    linarith
  have hcLo : ((60663781 : ℝ) / 62500000) < cos (((243 : ℝ) / 1000)) := by
    have hnum : ((60663781 : ℝ) / 62500000) <
        1 - (((243 : ℝ) / 1000)) ^ 2 / 2 + (((243 : ℝ) / 1000)) ^ 4 / 24 - (((243 : ℝ) / 1000)) ^ 6 / 720 := by norm_num
    linarith
  have hcHi : cos (((243 : ℝ) / 1000)) < ((970620783 : ℝ) / 1000000000) := by
    have hnum : 1 - (((243 : ℝ) / 1000)) ^ 2 / 2 + (((243 : ℝ) / 1000)) ^ 4 / 24 < ((970620783 : ℝ) / 1000000000) := by norm_num
    linarith
  have hexp := exp_between (x := ((243 : ℝ) / 1000)) (n := 8) (lo := ((1275068623 : ℝ) / 1000000000)) (hi := ((10200549 : ℝ) / 8000000))
    ht0.le ht1 (by decide)
    (by norm_num [sum_range_succ, Nat.factorial])
    (by norm_num [sum_range_succ, Nat.factorial])
  have hph : ((123877323 : ℝ) / 500000000) < chordAmp (((243 : ℝ) / 1000)) ∧ chordAmp (((243 : ℝ) / 1000)) < ((123877329 : ℝ) / 500000000) ∧
      ((940372157 : ℝ) / 1000000000) < gammaSEqual (((243 : ℝ) / 1000)) ∧ gammaSEqual (((243 : ℝ) / 1000)) < ((470186229 : ℝ) / 500000000) := by
    exact phase_bounds ht0 ht1 hsLo hsHi hcLo hcHi hexp.1 hexp.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨ht0, ht1, by norm_num, by norm_num, hph.1, hph.2.1, by norm_num, hph.2.2.1, hph.2.2.2⟩


private lemma phaseAt_254 :
    phaseHolds (((254 : ℝ) / 1000)) ((51885401 : ℝ) / 200000000) ((12971351 : ℝ) / 50000000) ((186958653 : ℝ) / 200000000) ((467396829 : ℝ) / 500000000) := by
  have ht0 : (0 : ℝ) < ((254 : ℝ) / 1000) := by norm_num
  have ht1 : ((254 : ℝ) / 1000) ≤ 1 := by norm_num
  obtain ⟨hs7, hs5, hc6, hc4⟩ := trigPoly_bounds ht0
  have hsLo : ((251277619 : ℝ) / 1000000000) < sin (((254 : ℝ) / 1000)) := by
    have hnum : ((251277619 : ℝ) / 1000000000) <
        ((254 : ℝ) / 1000) - (((254 : ℝ) / 1000)) ^ 3 / 6 + (((254 : ℝ) / 1000)) ^ 5 / 120 - (((254 : ℝ) / 1000)) ^ 7 / 5040 := by norm_num
    linarith
  have hsHi : sin (((254 : ℝ) / 1000)) < ((251277633 : ℝ) / 1000000000) := by
    have hnum : ((254 : ℝ) / 1000) - (((254 : ℝ) / 1000)) ^ 3 / 6 + (((254 : ℝ) / 1000)) ^ 5 / 120 < ((251277633 : ℝ) / 1000000000) := by norm_num
    linarith
  have hcLo : ((60494691 : ℝ) / 62500000) < cos (((254 : ℝ) / 1000)) := by
    have hnum : ((60494691 : ℝ) / 62500000) <
        1 - (((254 : ℝ) / 1000)) ^ 2 / 2 + (((254 : ℝ) / 1000)) ^ 4 / 24 - (((254 : ℝ) / 1000)) ^ 6 / 720 := by norm_num
    linarith
  have hcHi : cos (((254 : ℝ) / 1000)) < ((96791543 : ℝ) / 100000000) := by
    have hnum : 1 - (((254 : ℝ) / 1000)) ^ 2 / 2 + (((254 : ℝ) / 1000)) ^ 4 / 24 < ((96791543 : ℝ) / 100000000) := by norm_num
    linarith
  have hexp := exp_between (x := ((254 : ℝ) / 1000)) (n := 8) (lo := ((1289171803 : ℝ) / 1000000000)) (hi := ((257834361 : ℝ) / 200000000))
    ht0.le ht1 (by decide)
    (by norm_num [sum_range_succ, Nat.factorial])
    (by norm_num [sum_range_succ, Nat.factorial])
  have hph : ((51885401 : ℝ) / 200000000) < chordAmp (((254 : ℝ) / 1000)) ∧ chordAmp (((254 : ℝ) / 1000)) < ((12971351 : ℝ) / 50000000) ∧
      ((186958653 : ℝ) / 200000000) < gammaSEqual (((254 : ℝ) / 1000)) ∧ gammaSEqual (((254 : ℝ) / 1000)) < ((467396829 : ℝ) / 500000000) := by
    exact phase_bounds ht0 ht1 hsLo hsHi hcLo hcHi hexp.1 hexp.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨ht0, ht1, by norm_num, by norm_num, hph.1, hph.2.1, by norm_num, hph.2.2.1, hph.2.2.2⟩


private lemma phaseAt_255 :
    phaseHolds (((255 : ℝ) / 1000)) ((4070173 : ℝ) / 15625000) ((260491089 : ℝ) / 1000000000) ((233568337 : ℝ) / 250000000) ((747419 : ℝ) / 800000) := by
  have ht0 : (0 : ℝ) < ((255 : ℝ) / 1000) := by norm_num
  have ht1 : ((255 : ℝ) / 1000) ≤ 1 := by norm_num
  obtain ⟨hs7, hs5, hc6, hc4⟩ := trigPoly_bounds ht0
  have hsLo : ((7882669 : ℝ) / 31250000) < sin (((255 : ℝ) / 1000)) := by
    have hnum : ((7882669 : ℝ) / 31250000) <
        ((255 : ℝ) / 1000) - (((255 : ℝ) / 1000)) ^ 3 / 6 + (((255 : ℝ) / 1000)) ^ 5 / 120 - (((255 : ℝ) / 1000)) ^ 7 / 5040 := by norm_num
    linarith
  have hsHi : sin (((255 : ℝ) / 1000)) < ((252245423 : ℝ) / 1000000000) := by
    have hnum : ((255 : ℝ) / 1000) - (((255 : ℝ) / 1000)) ^ 3 / 6 + (((255 : ℝ) / 1000)) ^ 5 / 120 < ((252245423 : ℝ) / 1000000000) := by norm_num
    linarith
  have hcLo : ((193532659 : ℝ) / 200000000) < cos (((255 : ℝ) / 1000)) := by
    have hnum : ((193532659 : ℝ) / 200000000) <
        1 - (((255 : ℝ) / 1000)) ^ 2 / 2 + (((255 : ℝ) / 1000)) ^ 4 / 24 - (((255 : ℝ) / 1000)) ^ 6 / 720 := by norm_num
    linarith
  have hcHi : cos (((255 : ℝ) / 1000)) < ((483831839 : ℝ) / 500000000) := by
    have hnum : 1 - (((255 : ℝ) / 1000)) ^ 2 / 2 + (((255 : ℝ) / 1000)) ^ 4 / 24 < ((483831839 : ℝ) / 500000000) := by norm_num
    linarith
  have hexp := exp_between (x := ((255 : ℝ) / 1000)) (n := 8) (lo := ((1290461619 : ℝ) / 1000000000)) (hi := ((1290461621 : ℝ) / 1000000000))
    ht0.le ht1 (by decide)
    (by norm_num [sum_range_succ, Nat.factorial])
    (by norm_num [sum_range_succ, Nat.factorial])
  have hph : ((4070173 : ℝ) / 15625000) < chordAmp (((255 : ℝ) / 1000)) ∧ chordAmp (((255 : ℝ) / 1000)) < ((260491089 : ℝ) / 1000000000) ∧
      ((233568337 : ℝ) / 250000000) < gammaSEqual (((255 : ℝ) / 1000)) ∧ gammaSEqual (((255 : ℝ) / 1000)) < ((747419 : ℝ) / 800000) := by
    exact phase_bounds ht0 ht1 hsLo hsHi hcLo hcHi hexp.1 hexp.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨ht0, ht1, by norm_num, by norm_num, hph.1, hph.2.1, by norm_num, hph.2.2.1, hph.2.2.2⟩


private lemma phaseAt_259 :
    phaseHolds (((259 : ℝ) / 1000)) ((8273511 : ℝ) / 31250000) ((264752371 : ℝ) / 1000000000) ((466086189 : ℝ) / 500000000) ((932172821 : ℝ) / 1000000000) := by
  have ht0 : (0 : ℝ) < ((259 : ℝ) / 1000) := by norm_num
  have ht1 : ((259 : ℝ) / 1000) ≤ 1 := by norm_num
  obtain ⟨hs7, hs5, hc6, hc4⟩ := trigPoly_bounds ht0
  have hsLo : ((256114033 : ℝ) / 1000000000) < sin (((259 : ℝ) / 1000)) := by
    have hnum : ((256114033 : ℝ) / 1000000000) <
        ((259 : ℝ) / 1000) - (((259 : ℝ) / 1000)) ^ 3 / 6 + (((259 : ℝ) / 1000)) ^ 5 / 120 - (((259 : ℝ) / 1000)) ^ 7 / 5040 := by norm_num
    linarith
  have hsHi : sin (((259 : ℝ) / 1000)) < ((5122281 : ℝ) / 20000000) := by
    have hnum : ((259 : ℝ) / 1000) - (((259 : ℝ) / 1000)) ^ 3 / 6 + (((259 : ℝ) / 1000)) ^ 5 / 120 < ((5122281 : ℝ) / 20000000) := by norm_num
    linarith
  have hcLo : ((483323287 : ℝ) / 500000000) < cos (((259 : ℝ) / 1000)) := by
    have hnum : ((483323287 : ℝ) / 500000000) <
        1 - (((259 : ℝ) / 1000)) ^ 2 / 2 + (((259 : ℝ) / 1000)) ^ 4 / 24 - (((259 : ℝ) / 1000)) ^ 6 / 720 := by norm_num
    linarith
  have hcHi : cos (((259 : ℝ) / 1000)) < ((193329399 : ℝ) / 200000000) := by
    have hnum : 1 - (((259 : ℝ) / 1000)) ^ 2 / 2 + (((259 : ℝ) / 1000)) ^ 4 / 24 < ((193329399 : ℝ) / 200000000) := by norm_num
    linarith
  have hexp := exp_between (x := ((259 : ℝ) / 1000)) (n := 8) (lo := ((1295633803 : ℝ) / 1000000000)) (hi := ((259126761 : ℝ) / 200000000))
    ht0.le ht1 (by decide)
    (by norm_num [sum_range_succ, Nat.factorial])
    (by norm_num [sum_range_succ, Nat.factorial])
  have hph : ((8273511 : ℝ) / 31250000) < chordAmp (((259 : ℝ) / 1000)) ∧ chordAmp (((259 : ℝ) / 1000)) < ((264752371 : ℝ) / 1000000000) ∧
      ((466086189 : ℝ) / 500000000) < gammaSEqual (((259 : ℝ) / 1000)) ∧ gammaSEqual (((259 : ℝ) / 1000)) < ((932172821 : ℝ) / 1000000000) := by
    exact phase_bounds ht0 ht1 hsLo hsHi hcLo hcHi hexp.1 hexp.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨ht0, ht1, by norm_num, by norm_num, hph.1, hph.2.1, by norm_num, hph.2.2.1, hph.2.2.2⟩


private lemma phaseAt_260 :
    phaseHolds (((260 : ℝ) / 1000)) ((265818933 : ℝ) / 1000000000) ((33227369 : ℝ) / 125000000) ((931641807 : ℝ) / 1000000000) ((931642259 : ℝ) / 1000000000) := by
  have ht0 : (0 : ℝ) < ((260 : ℝ) / 1000) := by norm_num
  have ht1 : ((260 : ℝ) / 1000) ≤ 1 := by norm_num
  obtain ⟨hs7, hs5, hc6, hc4⟩ := trigPoly_bounds ht0
  have hsLo : ((257080551 : ℝ) / 1000000000) < sin (((260 : ℝ) / 1000)) := by
    have hnum : ((257080551 : ℝ) / 1000000000) <
        ((260 : ℝ) / 1000) - (((260 : ℝ) / 1000)) ^ 3 / 6 + (((260 : ℝ) / 1000)) ^ 5 / 120 - (((260 : ℝ) / 1000)) ^ 7 / 5040 := by norm_num
    linarith
  have hsHi : sin (((260 : ℝ) / 1000)) < ((32135071 : ℝ) / 125000000) := by
    have hnum : ((260 : ℝ) / 1000) - (((260 : ℝ) / 1000)) ^ 3 / 6 + (((260 : ℝ) / 1000)) ^ 5 / 120 < ((32135071 : ℝ) / 125000000) := by norm_num
    linarith
  have hcLo : ((966389977 : ℝ) / 1000000000) < cos (((260 : ℝ) / 1000)) := by
    have hnum : ((966389977 : ℝ) / 1000000000) <
        1 - (((260 : ℝ) / 1000)) ^ 2 / 2 + (((260 : ℝ) / 1000)) ^ 4 / 24 - (((260 : ℝ) / 1000)) ^ 6 / 720 := by norm_num
    linarith
  have hcHi : cos (((260 : ℝ) / 1000)) < ((966390407 : ℝ) / 1000000000) := by
    have hnum : 1 - (((260 : ℝ) / 1000)) ^ 2 / 2 + (((260 : ℝ) / 1000)) ^ 4 / 24 < ((966390407 : ℝ) / 1000000000) := by norm_num
    linarith
  have hexp := exp_between (x := ((260 : ℝ) / 1000)) (n := 8) (lo := ((259386017 : ℝ) / 200000000)) (hi := ((1296930087 : ℝ) / 1000000000))
    ht0.le ht1 (by decide)
    (by norm_num [sum_range_succ, Nat.factorial])
    (by norm_num [sum_range_succ, Nat.factorial])
  have hph : ((265818933 : ℝ) / 1000000000) < chordAmp (((260 : ℝ) / 1000)) ∧ chordAmp (((260 : ℝ) / 1000)) < ((33227369 : ℝ) / 125000000) ∧
      ((931641807 : ℝ) / 1000000000) < gammaSEqual (((260 : ℝ) / 1000)) ∧ gammaSEqual (((260 : ℝ) / 1000)) < ((931642259 : ℝ) / 1000000000) := by
    exact phase_bounds ht0 ht1 hsLo hsHi hcLo hcHi hexp.1 hexp.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨ht0, ht1, by norm_num, by norm_num, hph.1, hph.2.1, by norm_num, hph.2.2.1, hph.2.2.2⟩


private lemma phaseAt_262 :
    phaseHolds (((262 : ℝ) / 1000)) ((133976811 : ℝ) / 500000000) ((267953643 : ℝ) / 1000000000) ((930574263 : ℝ) / 1000000000) ((58160921 : ℝ) / 62500000) := by
  have ht0 : (0 : ℝ) < ((262 : ℝ) / 1000) := by norm_num
  have ht1 : ((262 : ℝ) / 1000) ≤ 1 := by norm_num
  obtain ⟨hs7, hs5, hc6, hc4⟩ := trigPoly_bounds ht0
  have hsLo : ((16188301 : ℝ) / 62500000) < sin (((262 : ℝ) / 1000)) := by
    have hnum : ((16188301 : ℝ) / 62500000) <
        ((262 : ℝ) / 1000) - (((262 : ℝ) / 1000)) ^ 3 / 6 + (((262 : ℝ) / 1000)) ^ 5 / 120 - (((262 : ℝ) / 1000)) ^ 7 / 5040 := by norm_num
    linarith
  have hsHi : sin (((262 : ℝ) / 1000)) < ((129506417 : ℝ) / 500000000) := by
    have hnum : ((262 : ℝ) / 1000) - (((262 : ℝ) / 1000)) ^ 3 / 6 + (((262 : ℝ) / 1000)) ^ 5 / 120 < ((129506417 : ℝ) / 500000000) := by norm_num
    linarith
  have hcLo : ((241468471 : ℝ) / 250000000) < cos (((262 : ℝ) / 1000)) := by
    have hnum : ((241468471 : ℝ) / 250000000) <
        1 - (((262 : ℝ) / 1000)) ^ 2 / 2 + (((262 : ℝ) / 1000)) ^ 4 / 24 - (((262 : ℝ) / 1000)) ^ 6 / 720 := by norm_num
    linarith
  have hcHi : cos (((262 : ℝ) / 1000)) < ((482937167 : ℝ) / 500000000) := by
    have hnum : 1 - (((262 : ℝ) / 1000)) ^ 2 / 2 + (((262 : ℝ) / 1000)) ^ 4 / 24 < ((482937167 : ℝ) / 500000000) := by norm_num
    linarith
  have hexp := exp_between (x := ((262 : ℝ) / 1000)) (n := 8) (lo := ((1299526541 : ℝ) / 1000000000)) (hi := ((1299526543 : ℝ) / 1000000000))
    ht0.le ht1 (by decide)
    (by norm_num [sum_range_succ, Nat.factorial])
    (by norm_num [sum_range_succ, Nat.factorial])
  have hph : ((133976811 : ℝ) / 500000000) < chordAmp (((262 : ℝ) / 1000)) ∧ chordAmp (((262 : ℝ) / 1000)) < ((267953643 : ℝ) / 1000000000) ∧
      ((930574263 : ℝ) / 1000000000) < gammaSEqual (((262 : ℝ) / 1000)) ∧ gammaSEqual (((262 : ℝ) / 1000)) < ((58160921 : ℝ) / 62500000) := by
    exact phase_bounds ht0 ht1 hsLo hsHi hcLo hcHi hexp.1 hexp.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨ht0, ht1, by norm_num, by norm_num, hph.1, hph.2.1, by norm_num, hph.2.2.1, hph.2.2.2⟩


private lemma phaseAt_263 :
    phaseHolds (((263 : ℝ) / 1000)) ((134510867 : ℝ) / 500000000) ((134510877 : ℝ) / 500000000) ((930037287 : ℝ) / 1000000000) ((232509443 : ℝ) / 250000000) := by
  have ht0 : (0 : ℝ) < ((263 : ℝ) / 1000) := by norm_num
  have ht1 : ((263 : ℝ) / 1000) ≤ 1 := by norm_num
  obtain ⟨hs7, hs5, hc6, hc4⟩ := trigPoly_bounds ht0
  have hsLo : ((812433 : ℝ) / 3125000) < sin (((263 : ℝ) / 1000)) := by
    have hnum : ((812433 : ℝ) / 3125000) <
        ((263 : ℝ) / 1000) - (((263 : ℝ) / 1000)) ^ 3 / 6 + (((263 : ℝ) / 1000)) ^ 5 / 120 - (((263 : ℝ) / 1000)) ^ 7 / 5040 := by norm_num
    linarith
  have hsHi : sin (((263 : ℝ) / 1000)) < ((129989289 : ℝ) / 500000000) := by
    have hnum : ((263 : ℝ) / 1000) - (((263 : ℝ) / 1000)) ^ 3 / 6 + (((263 : ℝ) / 1000)) ^ 5 / 120 < ((129989289 : ℝ) / 500000000) := by norm_num
    linarith
  have hcLo : ((241403597 : ℝ) / 250000000) < cos (((263 : ℝ) / 1000)) := by
    have hnum : ((241403597 : ℝ) / 250000000) <
        1 - (((263 : ℝ) / 1000)) ^ 2 / 2 + (((263 : ℝ) / 1000)) ^ 4 / 24 - (((263 : ℝ) / 1000)) ^ 6 / 720 := by norm_num
    linarith
  have hcHi : cos (((263 : ℝ) / 1000)) < ((3771933 : ℝ) / 3906250) := by
    have hnum : 1 - (((263 : ℝ) / 1000)) ^ 2 / 2 + (((263 : ℝ) / 1000)) ^ 4 / 24 < ((3771933 : ℝ) / 3906250) := by norm_num
    linarith
  have hexp := exp_between (x := ((263 : ℝ) / 1000)) (n := 8) (lo := ((1300826717 : ℝ) / 1000000000)) (hi := ((8130167 : ℝ) / 6250000))
    ht0.le ht1 (by decide)
    (by norm_num [sum_range_succ, Nat.factorial])
    (by norm_num [sum_range_succ, Nat.factorial])
  have hph : ((134510867 : ℝ) / 500000000) < chordAmp (((263 : ℝ) / 1000)) ∧ chordAmp (((263 : ℝ) / 1000)) < ((134510877 : ℝ) / 500000000) ∧
      ((930037287 : ℝ) / 1000000000) < gammaSEqual (((263 : ℝ) / 1000)) ∧ gammaSEqual (((263 : ℝ) / 1000)) < ((232509443 : ℝ) / 250000000) := by
    exact phase_bounds ht0 ht1 hsLo hsHi hcLo hcHi hexp.1 hexp.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨ht0, ht1, by norm_num, by norm_num, hph.1, hph.2.1, by norm_num, hph.2.2.1, hph.2.2.2⟩


private lemma phaseAt_272 :
    phaseHolds (((272 : ℝ) / 1000)) ((278658079 : ℝ) / 1000000000) ((34832263 : ℝ) / 125000000) ((92510823 : ℝ) / 100000000) ((37004353 : ℝ) / 40000000) := by
  have ht0 : (0 : ℝ) < ((272 : ℝ) / 1000) := by norm_num
  have ht1 : ((272 : ℝ) / 1000) ≤ 1 := by norm_num
  obtain ⟨hs7, hs5, hc6, hc4⟩ := trigPoly_bounds ht0
  have hsLo : ((268658443 : ℝ) / 1000000000) < sin (((272 : ℝ) / 1000)) := by
    have hnum : ((268658443 : ℝ) / 1000000000) <
        ((272 : ℝ) / 1000) - (((272 : ℝ) / 1000)) ^ 3 / 6 + (((272 : ℝ) / 1000)) ^ 5 / 120 - (((272 : ℝ) / 1000)) ^ 7 / 5040 := by norm_num
    linarith
  have hsHi : sin (((272 : ℝ) / 1000)) < ((134329233 : ℝ) / 500000000) := by
    have hnum : ((272 : ℝ) / 1000) - (((272 : ℝ) / 1000)) ^ 3 / 6 + (((272 : ℝ) / 1000)) ^ 5 / 120 < ((134329233 : ℝ) / 500000000) := by norm_num
    linarith
  have hcLo : ((192647101 : ℝ) / 200000000) < cos (((272 : ℝ) / 1000)) := by
    have hnum : ((192647101 : ℝ) / 200000000) <
        1 - (((272 : ℝ) / 1000)) ^ 2 / 2 + (((272 : ℝ) / 1000)) ^ 4 / 24 - (((272 : ℝ) / 1000)) ^ 6 / 720 := by norm_num
    linarith
  have hcHi : cos (((272 : ℝ) / 1000)) < ((963236069 : ℝ) / 1000000000) := by
    have hnum : 1 - (((272 : ℝ) / 1000)) ^ 2 / 2 + (((272 : ℝ) / 1000)) ^ 4 / 24 < ((963236069 : ℝ) / 1000000000) := by norm_num
    linarith
  have hexp := exp_between (x := ((272 : ℝ) / 1000)) (n := 8) (lo := ((1312586999 : ℝ) / 1000000000)) (hi := ((656293501 : ℝ) / 500000000))
    ht0.le ht1 (by decide)
    (by norm_num [sum_range_succ, Nat.factorial])
    (by norm_num [sum_range_succ, Nat.factorial])
  have hph : ((278658079 : ℝ) / 1000000000) < chordAmp (((272 : ℝ) / 1000)) ∧ chordAmp (((272 : ℝ) / 1000)) < ((34832263 : ℝ) / 125000000) ∧
      ((92510823 : ℝ) / 100000000) < gammaSEqual (((272 : ℝ) / 1000)) ∧ gammaSEqual (((272 : ℝ) / 1000)) < ((37004353 : ℝ) / 40000000) := by
    exact phase_bounds ht0 ht1 hsLo hsHi hcLo hcHi hexp.1 hexp.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨ht0, ht1, by norm_num, by norm_num, hph.1, hph.2.1, by norm_num, hph.2.2.1, hph.2.2.2⟩


private lemma phaseAt_273 :
    phaseHolds (((273 : ℝ) / 1000)) ((69932853 : ℝ) / 250000000) ((139865719 : ℝ) / 500000000) ((924549841 : ℝ) / 1000000000) ((57784403 : ℝ) / 62500000) := by
  have ht0 : (0 : ℝ) < ((273 : ℝ) / 1000) := by norm_num
  have ht1 : ((273 : ℝ) / 1000) ≤ 1 := by norm_num
  obtain ⟨hs7, hs5, hc6, hc4⟩ := trigPoly_bounds ht0
  have hsLo : ((33702693 : ℝ) / 125000000) < sin (((273 : ℝ) / 1000)) := by
    have hnum : ((33702693 : ℝ) / 125000000) <
        ((273 : ℝ) / 1000) - (((273 : ℝ) / 1000)) ^ 3 / 6 + (((273 : ℝ) / 1000)) ^ 5 / 120 - (((273 : ℝ) / 1000)) ^ 7 / 5040 := by norm_num
    linarith
  have hsHi : sin (((273 : ℝ) / 1000)) < ((4212837 : ℝ) / 15625000) := by
    have hnum : ((273 : ℝ) / 1000) - (((273 : ℝ) / 1000)) ^ 3 / 6 + (((273 : ℝ) / 1000)) ^ 5 / 120 < ((4212837 : ℝ) / 15625000) := by norm_num
    linarith
  have hcLo : ((192593273 : ℝ) / 200000000) < cos (((273 : ℝ) / 1000)) := by
    have hnum : ((192593273 : ℝ) / 200000000) <
        1 - (((273 : ℝ) / 1000)) ^ 2 / 2 + (((273 : ℝ) / 1000)) ^ 4 / 24 - (((273 : ℝ) / 1000)) ^ 6 / 720 := by norm_num
    linarith
  have hcHi : cos (((273 : ℝ) / 1000)) < ((962966941 : ℝ) / 1000000000) := by
    have hnum : 1 - (((273 : ℝ) / 1000)) ^ 2 / 2 + (((273 : ℝ) / 1000)) ^ 4 / 24 < ((962966941 : ℝ) / 1000000000) := by norm_num
    linarith
  have hexp := exp_between (x := ((273 : ℝ) / 1000)) (n := 8) (lo := ((1313900243 : ℝ) / 1000000000)) (hi := ((262780049 : ℝ) / 200000000))
    ht0.le ht1 (by decide)
    (by norm_num [sum_range_succ, Nat.factorial])
    (by norm_num [sum_range_succ, Nat.factorial])
  have hph : ((69932853 : ℝ) / 250000000) < chordAmp (((273 : ℝ) / 1000)) ∧ chordAmp (((273 : ℝ) / 1000)) < ((139865719 : ℝ) / 500000000) ∧
      ((924549841 : ℝ) / 1000000000) < gammaSEqual (((273 : ℝ) / 1000)) ∧ gammaSEqual (((273 : ℝ) / 1000)) < ((57784403 : ℝ) / 62500000) := by
    exact phase_bounds ht0 ht1 hsLo hsHi hcLo hcHi hexp.1 hexp.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨ht0, ht1, by norm_num, by norm_num, hph.1, hph.2.1, by norm_num, hph.2.2.1, hph.2.2.2⟩


private lemma phaseAt_280 :
    phaseHolds (((280 : ℝ) / 1000)) ((1149039 : ℝ) / 4000000) ((287259781 : ℝ) / 1000000000) ((230145233 : ℝ) / 250000000) ((23014541 : ℝ) / 25000000) := by
  have ht0 : (0 : ℝ) < ((280 : ℝ) / 1000) := by norm_num
  have ht1 : ((280 : ℝ) / 1000) ≤ 1 := by norm_num
  obtain ⟨hs7, hs5, hc6, hc4⟩ := trigPoly_bounds ht0
  have hsLo : ((4318057 : ℝ) / 15625000) < sin (((280 : ℝ) / 1000)) := by
    have hnum : ((4318057 : ℝ) / 15625000) <
        ((280 : ℝ) / 1000) - (((280 : ℝ) / 1000)) ^ 3 / 6 + (((280 : ℝ) / 1000)) ^ 5 / 120 - (((280 : ℝ) / 1000)) ^ 7 / 5040 := by norm_num
    linarith
  have hsHi : sin (((280 : ℝ) / 1000)) < ((69088919 : ℝ) / 250000000) := by
    have hnum : ((280 : ℝ) / 1000) - (((280 : ℝ) / 1000)) ^ 3 / 6 + (((280 : ℝ) / 1000)) ^ 5 / 120 < ((69088919 : ℝ) / 250000000) := by norm_num
    linarith
  have hcLo : ((961055437 : ℝ) / 1000000000) < cos (((280 : ℝ) / 1000)) := by
    have hnum : ((961055437 : ℝ) / 1000000000) <
        1 - (((280 : ℝ) / 1000)) ^ 2 / 2 + (((280 : ℝ) / 1000)) ^ 4 / 24 - (((280 : ℝ) / 1000)) ^ 6 / 720 := by norm_num
    linarith
  have hcHi : cos (((280 : ℝ) / 1000)) < ((961056107 : ℝ) / 1000000000) := by
    have hnum : 1 - (((280 : ℝ) / 1000)) ^ 2 / 2 + (((280 : ℝ) / 1000)) ^ 4 / 24 < ((961056107 : ℝ) / 1000000000) := by norm_num
    linarith
  have hexp := exp_between (x := ((280 : ℝ) / 1000)) (n := 8) (lo := ((132312981 : ℝ) / 100000000)) (hi := ((1323129813 : ℝ) / 1000000000))
    ht0.le ht1 (by decide)
    (by norm_num [sum_range_succ, Nat.factorial])
    (by norm_num [sum_range_succ, Nat.factorial])
  have hph : ((1149039 : ℝ) / 4000000) < chordAmp (((280 : ℝ) / 1000)) ∧ chordAmp (((280 : ℝ) / 1000)) < ((287259781 : ℝ) / 1000000000) ∧
      ((230145233 : ℝ) / 250000000) < gammaSEqual (((280 : ℝ) / 1000)) ∧ gammaSEqual (((280 : ℝ) / 1000)) < ((23014541 : ℝ) / 25000000) := by
    exact phase_bounds ht0 ht1 hsLo hsHi hcLo hcHi hexp.1 hexp.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨ht0, ht1, by norm_num, by norm_num, hph.1, hph.2.1, by norm_num, hph.2.2.1, hph.2.2.2⟩


private lemma phaseAt_281 :
    phaseHolds (((281 : ℝ) / 1000)) ((288337393 : ℝ) / 1000000000) ((11533497 : ℝ) / 40000000) ((460002667 : ℝ) / 500000000) ((460003029 : ℝ) / 500000000) := by
  have ht0 : (0 : ℝ) < ((281 : ℝ) / 1000) := by norm_num
  have ht1 : ((281 : ℝ) / 1000) ≤ 1 := by norm_num
  obtain ⟨hs7, hs5, hc6, hc4⟩ := trigPoly_bounds ht0
  have hsLo : ((55463313 : ℝ) / 200000000) < sin (((281 : ℝ) / 1000)) := by
    have hnum : ((55463313 : ℝ) / 200000000) <
        ((281 : ℝ) / 1000) - (((281 : ℝ) / 1000)) ^ 3 / 6 + (((281 : ℝ) / 1000)) ^ 5 / 120 - (((281 : ℝ) / 1000)) ^ 7 / 5040 := by norm_num
    linarith
  have hsHi : sin (((281 : ℝ) / 1000)) < ((138658297 : ℝ) / 500000000) := by
    have hnum : ((281 : ℝ) / 1000) - (((281 : ℝ) / 1000)) ^ 3 / 6 + (((281 : ℝ) / 1000)) ^ 5 / 120 < ((138658297 : ℝ) / 500000000) := by norm_num
    linarith
  have hcLo : ((960778601 : ℝ) / 1000000000) < cos (((281 : ℝ) / 1000)) := by
    have hnum : ((960778601 : ℝ) / 1000000000) <
        1 - (((281 : ℝ) / 1000)) ^ 2 / 2 + (((281 : ℝ) / 1000)) ^ 4 / 24 - (((281 : ℝ) / 1000)) ^ 6 / 720 := by norm_num
    linarith
  have hcHi : cos (((281 : ℝ) / 1000)) < ((192155857 : ℝ) / 200000000) := by
    have hnum : 1 - (((281 : ℝ) / 1000)) ^ 2 / 2 + (((281 : ℝ) / 1000)) ^ 4 / 24 < ((192155857 : ℝ) / 200000000) := by norm_num
    linarith
  have hexp := exp_between (x := ((281 : ℝ) / 1000)) (n := 8) (lo := ((1324453601 : ℝ) / 1000000000)) (hi := ((264890721 : ℝ) / 200000000))
    ht0.le ht1 (by decide)
    (by norm_num [sum_range_succ, Nat.factorial])
    (by norm_num [sum_range_succ, Nat.factorial])
  have hph : ((288337393 : ℝ) / 1000000000) < chordAmp (((281 : ℝ) / 1000)) ∧ chordAmp (((281 : ℝ) / 1000)) < ((11533497 : ℝ) / 40000000) ∧
      ((460002667 : ℝ) / 500000000) < gammaSEqual (((281 : ℝ) / 1000)) ∧ gammaSEqual (((281 : ℝ) / 1000)) < ((460003029 : ℝ) / 500000000) := by
    exact phase_bounds ht0 ht1 hsLo hsHi hcLo hcHi hexp.1 hexp.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨ht0, ht1, by norm_num, by norm_num, hph.1, hph.2.1, by norm_num, hph.2.2.1, hph.2.2.2⟩


private lemma phaseAt_282 :
    phaseHolds (((282 : ℝ) / 1000)) ((9044237 : ℝ) / 31250000) ((4522119 : ℝ) / 15625000) ((919427581 : ℝ) / 1000000000) ((919428321 : ℝ) / 1000000000) := by
  have ht0 : (0 : ℝ) < ((282 : ℝ) / 1000) := by norm_num
  have ht1 : ((282 : ℝ) / 1000) ≤ 1 := by norm_num
  obtain ⟨hs7, hs5, hc6, hc4⟩ := trigPoly_bounds ht0
  have hsLo : ((55655441 : ℝ) / 200000000) < sin (((282 : ℝ) / 1000)) := by
    have hnum : ((55655441 : ℝ) / 200000000) <
        ((282 : ℝ) / 1000) - (((282 : ℝ) / 1000)) ^ 3 / 6 + (((282 : ℝ) / 1000)) ^ 5 / 120 - (((282 : ℝ) / 1000)) ^ 7 / 5040 := by norm_num
    linarith
  have hsHi : sin (((282 : ℝ) / 1000)) < ((139138617 : ℝ) / 500000000) := by
    have hnum : ((282 : ℝ) / 1000) - (((282 : ℝ) / 1000)) ^ 3 / 6 + (((282 : ℝ) / 1000)) ^ 5 / 120 < ((139138617 : ℝ) / 500000000) := by norm_num
    linarith
  have hcLo : ((240125201 : ℝ) / 250000000) < cos (((282 : ℝ) / 1000)) := by
    have hnum : ((240125201 : ℝ) / 250000000) <
        1 - (((282 : ℝ) / 1000)) ^ 2 / 2 + (((282 : ℝ) / 1000)) ^ 4 / 24 - (((282 : ℝ) / 1000)) ^ 6 / 720 := by norm_num
    linarith
  have hcHi : cos (((282 : ℝ) / 1000)) < ((960501503 : ℝ) / 1000000000) := by
    have hnum : 1 - (((282 : ℝ) / 1000)) ^ 2 / 2 + (((282 : ℝ) / 1000)) ^ 4 / 24 < ((960501503 : ℝ) / 1000000000) := by norm_num
    linarith
  have hexp := exp_between (x := ((282 : ℝ) / 1000)) (n := 8) (lo := ((1325778717 : ℝ) / 1000000000)) (hi := ((1325778721 : ℝ) / 1000000000))
    ht0.le ht1 (by decide)
    (by norm_num [sum_range_succ, Nat.factorial])
    (by norm_num [sum_range_succ, Nat.factorial])
  have hph : ((9044237 : ℝ) / 31250000) < chordAmp (((282 : ℝ) / 1000)) ∧ chordAmp (((282 : ℝ) / 1000)) < ((4522119 : ℝ) / 15625000) ∧
      ((919427581 : ℝ) / 1000000000) < gammaSEqual (((282 : ℝ) / 1000)) ∧ gammaSEqual (((282 : ℝ) / 1000)) < ((919428321 : ℝ) / 1000000000) := by
    exact phase_bounds ht0 ht1 hsLo hsHi hcLo hcHi hexp.1 hexp.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨ht0, ht1, by norm_num, by norm_num, hph.1, hph.2.1, by norm_num, hph.2.2.1, hph.2.2.2⟩


private lemma phaseAt_283 :
    phaseHolds (((283 : ℝ) / 1000)) ((145247161 : ℝ) / 500000000) ((58098871 : ℝ) / 200000000) ((918847671 : ℝ) / 1000000000) ((918848427 : ℝ) / 1000000000) := by
  have ht0 : (0 : ℝ) < ((283 : ℝ) / 1000) := by norm_num
  have ht1 : ((283 : ℝ) / 1000) ≤ 1 := by norm_num
  obtain ⟨hs7, hs5, hc6, hc4⟩ := trigPoly_bounds ht0
  have hsLo : ((139618783 : ℝ) / 500000000) < sin (((283 : ℝ) / 1000)) := by
    have hnum : ((139618783 : ℝ) / 500000000) <
        ((283 : ℝ) / 1000) - (((283 : ℝ) / 1000)) ^ 3 / 6 + (((283 : ℝ) / 1000)) ^ 5 / 120 - (((283 : ℝ) / 1000)) ^ 7 / 5040 := by norm_num
    linarith
  have hsHi : sin (((283 : ℝ) / 1000)) < ((69809399 : ℝ) / 250000000) := by
    have hnum : ((283 : ℝ) / 1000) - (((283 : ℝ) / 1000)) ^ 3 / 6 + (((283 : ℝ) / 1000)) ^ 5 / 120 < ((69809399 : ℝ) / 250000000) := by norm_num
    linarith
  have hcLo : ((480111023 : ℝ) / 500000000) < cos (((283 : ℝ) / 1000)) := by
    have hnum : ((480111023 : ℝ) / 500000000) <
        1 - (((283 : ℝ) / 1000)) ^ 2 / 2 + (((283 : ℝ) / 1000)) ^ 4 / 24 - (((283 : ℝ) / 1000)) ^ 6 / 720 := by norm_num
    linarith
  have hcHi : cos (((283 : ℝ) / 1000)) < ((960222761 : ℝ) / 1000000000) := by
    have hnum : 1 - (((283 : ℝ) / 1000)) ^ 2 / 2 + (((283 : ℝ) / 1000)) ^ 4 / 24 < ((960222761 : ℝ) / 1000000000) := by norm_num
    linarith
  have hexp := exp_between (x := ((283 : ℝ) / 1000)) (n := 8) (lo := ((1327105159 : ℝ) / 1000000000)) (hi := ((663552581 : ℝ) / 500000000))
    ht0.le ht1 (by decide)
    (by norm_num [sum_range_succ, Nat.factorial])
    (by norm_num [sum_range_succ, Nat.factorial])
  have hph : ((145247161 : ℝ) / 500000000) < chordAmp (((283 : ℝ) / 1000)) ∧ chordAmp (((283 : ℝ) / 1000)) < ((58098871 : ℝ) / 200000000) ∧
      ((918847671 : ℝ) / 1000000000) < gammaSEqual (((283 : ℝ) / 1000)) ∧ gammaSEqual (((283 : ℝ) / 1000)) < ((918848427 : ℝ) / 1000000000) := by
    exact phase_bounds ht0 ht1 hsLo hsHi hcLo hcHi hexp.1 hexp.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨ht0, ht1, by norm_num, by norm_num, hph.1, hph.2.1, by norm_num, hph.2.2.1, hph.2.2.2⟩


private lemma phaseAt_297 :
    phaseHolds (((297 : ℝ) / 1000)) ((38206917 : ℝ) / 125000000) ((152827691 : ℝ) / 500000000) ((227625457 : ℝ) / 250000000) ((910502843 : ℝ) / 1000000000) := by
  have ht0 : (0 : ℝ) < ((297 : ℝ) / 1000) := by norm_num
  have ht1 : ((297 : ℝ) / 1000) ≤ 1 := by norm_num
  obtain ⟨hs7, hs5, hc6, hc4⟩ := trigPoly_bounds ht0
  have hsLo : ((292652871 : ℝ) / 1000000000) < sin (((297 : ℝ) / 1000)) := by
    have hnum : ((292652871 : ℝ) / 1000000000) <
        ((297 : ℝ) / 1000) - (((297 : ℝ) / 1000)) ^ 3 / 6 + (((297 : ℝ) / 1000)) ^ 5 / 120 - (((297 : ℝ) / 1000)) ^ 7 / 5040 := by norm_num
    linarith
  have hsHi : sin (((297 : ℝ) / 1000)) < ((292652913 : ℝ) / 1000000000) := by
    have hnum : ((297 : ℝ) / 1000) - (((297 : ℝ) / 1000)) ^ 3 / 6 + (((297 : ℝ) / 1000)) ^ 5 / 120 < ((292652913 : ℝ) / 1000000000) := by norm_num
    linarith
  have hcLo : ((956218747 : ℝ) / 1000000000) < cos (((297 : ℝ) / 1000)) := by
    have hnum : ((956218747 : ℝ) / 1000000000) <
        1 - (((297 : ℝ) / 1000)) ^ 2 / 2 + (((297 : ℝ) / 1000)) ^ 4 / 24 - (((297 : ℝ) / 1000)) ^ 6 / 720 := by norm_num
    linarith
  have hcHi : cos (((297 : ℝ) / 1000)) < ((478109851 : ℝ) / 500000000) := by
    have hnum : 1 - (((297 : ℝ) / 1000)) ^ 2 / 2 + (((297 : ℝ) / 1000)) ^ 4 / 24 < ((478109851 : ℝ) / 500000000) := by norm_num
    linarith
  have hexp := exp_between (x := ((297 : ℝ) / 1000)) (n := 8) (lo := ((5257091 : ℝ) / 3906250)) (hi := ((13458153 : ℝ) / 10000000))
    ht0.le ht1 (by decide)
    (by norm_num [sum_range_succ, Nat.factorial])
    (by norm_num [sum_range_succ, Nat.factorial])
  have hph : ((38206917 : ℝ) / 125000000) < chordAmp (((297 : ℝ) / 1000)) ∧ chordAmp (((297 : ℝ) / 1000)) < ((152827691 : ℝ) / 500000000) ∧
      ((227625457 : ℝ) / 250000000) < gammaSEqual (((297 : ℝ) / 1000)) ∧ gammaSEqual (((297 : ℝ) / 1000)) < ((910502843 : ℝ) / 1000000000) := by
    exact phase_bounds ht0 ht1 hsLo hsHi hcLo hcHi hexp.1 hexp.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨ht0, ht1, by norm_num, by norm_num, hph.1, hph.2.1, by norm_num, hph.2.2.1, hph.2.2.2⟩


private lemma phaseAt_298 :
    phaseHolds (((298 : ℝ) / 1000)) ((306742529 : ℝ) / 1000000000) ((19171411 : ℝ) / 62500000) ((909889429 : ℝ) / 1000000000) ((454945233 : ℝ) / 500000000) := by
  have ht0 : (0 : ℝ) < ((298 : ℝ) / 1000) := by norm_num
  have ht1 : ((298 : ℝ) / 1000) ≤ 1 := by norm_num
  obtain ⟨hs7, hs5, hc6, hc4⟩ := trigPoly_bounds ht0
  have hsLo : ((293608943 : ℝ) / 1000000000) < sin (((298 : ℝ) / 1000)) := by
    have hnum : ((293608943 : ℝ) / 1000000000) <
        ((298 : ℝ) / 1000) - (((298 : ℝ) / 1000)) ^ 3 / 6 + (((298 : ℝ) / 1000)) ^ 5 / 120 - (((298 : ℝ) / 1000)) ^ 7 / 5040 := by norm_num
    linarith
  have hsHi : sin (((298 : ℝ) / 1000)) < ((146804493 : ℝ) / 500000000) := by
    have hnum : ((298 : ℝ) / 1000) - (((298 : ℝ) / 1000)) ^ 3 / 6 + (((298 : ℝ) / 1000)) ^ 5 / 120 < ((146804493 : ℝ) / 500000000) := by norm_num
    linarith
  have hcLo : ((59745351 : ℝ) / 62500000) < cos (((298 : ℝ) / 1000)) := by
    have hnum : ((59745351 : ℝ) / 62500000) <
        1 - (((298 : ℝ) / 1000)) ^ 2 / 2 + (((298 : ℝ) / 1000)) ^ 4 / 24 - (((298 : ℝ) / 1000)) ^ 6 / 720 := by norm_num
    linarith
  have hcHi : cos (((298 : ℝ) / 1000)) < ((95592659 : ℝ) / 100000000) := by
    have hnum : 1 - (((298 : ℝ) / 1000)) ^ 2 / 2 + (((298 : ℝ) / 1000)) ^ 4 / 24 < ((95592659 : ℝ) / 100000000) := by norm_num
    linarith
  have hexp := exp_between (x := ((298 : ℝ) / 1000)) (n := 8) (lo := ((168395223 : ℝ) / 125000000)) (hi := ((1347161789 : ℝ) / 1000000000))
    ht0.le ht1 (by decide)
    (by norm_num [sum_range_succ, Nat.factorial])
    (by norm_num [sum_range_succ, Nat.factorial])
  have hph : ((306742529 : ℝ) / 1000000000) < chordAmp (((298 : ℝ) / 1000)) ∧ chordAmp (((298 : ℝ) / 1000)) < ((19171411 : ℝ) / 62500000) ∧
      ((909889429 : ℝ) / 1000000000) < gammaSEqual (((298 : ℝ) / 1000)) ∧ gammaSEqual (((298 : ℝ) / 1000)) < ((454945233 : ℝ) / 500000000) := by
    exact phase_bounds ht0 ht1 hsLo hsHi hcLo hcHi hexp.1 hexp.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨ht0, ht1, by norm_num, by norm_num, hph.1, hph.2.1, by norm_num, hph.2.2.1, hph.2.2.2⟩


private lemma phaseAt_302 :
    phaseHolds (((302 : ℝ) / 1000)) ((155548551 : ℝ) / 500000000) ((4860893 : ℝ) / 15625000) ((226854519 : ℝ) / 250000000) ((907419199 : ℝ) / 1000000000) := by
  have ht0 : (0 : ℝ) < ((302 : ℝ) / 1000) := by norm_num
  have ht1 : ((302 : ℝ) / 1000) ≤ 1 := by norm_num
  obtain ⟨hs7, hs5, hc6, hc4⟩ := trigPoly_bounds ht0
  have hsLo : ((297430287 : ℝ) / 1000000000) < sin (((302 : ℝ) / 1000)) := by
    have hnum : ((297430287 : ℝ) / 1000000000) <
        ((302 : ℝ) / 1000) - (((302 : ℝ) / 1000)) ^ 3 / 6 + (((302 : ℝ) / 1000)) ^ 5 / 120 - (((302 : ℝ) / 1000)) ^ 7 / 5040 := by norm_num
    linarith
  have hsHi : sin (((302 : ℝ) / 1000)) < ((297430333 : ℝ) / 1000000000) := by
    have hnum : ((302 : ℝ) / 1000) - (((302 : ℝ) / 1000)) ^ 3 / 6 + (((302 : ℝ) / 1000)) ^ 5 / 120 < ((297430333 : ℝ) / 1000000000) := by norm_num
    linarith
  have hcLo : ((59671471 : ℝ) / 62500000) < cos (((302 : ℝ) / 1000)) := by
    have hnum : ((59671471 : ℝ) / 62500000) <
        1 - (((302 : ℝ) / 1000)) ^ 2 / 2 + (((302 : ℝ) / 1000)) ^ 4 / 24 - (((302 : ℝ) / 1000)) ^ 6 / 720 := by norm_num
    linarith
  have hcHi : cos (((302 : ℝ) / 1000)) < ((954744591 : ℝ) / 1000000000) := by
    have hnum : 1 - (((302 : ℝ) / 1000)) ^ 2 / 2 + (((302 : ℝ) / 1000)) ^ 4 / 24 < ((954744591 : ℝ) / 1000000000) := by norm_num
    linarith
  have hexp := exp_between (x := ((302 : ℝ) / 1000)) (n := 8) (lo := ((1352561223 : ℝ) / 1000000000)) (hi := ((1352561227 : ℝ) / 1000000000))
    ht0.le ht1 (by decide)
    (by norm_num [sum_range_succ, Nat.factorial])
    (by norm_num [sum_range_succ, Nat.factorial])
  have hph : ((155548551 : ℝ) / 500000000) < chordAmp (((302 : ℝ) / 1000)) ∧ chordAmp (((302 : ℝ) / 1000)) < ((4860893 : ℝ) / 15625000) ∧
      ((226854519 : ℝ) / 250000000) < gammaSEqual (((302 : ℝ) / 1000)) ∧ gammaSEqual (((302 : ℝ) / 1000)) < ((907419199 : ℝ) / 1000000000) := by
    exact phase_bounds ht0 ht1 hsLo hsHi hcLo hcHi hexp.1 hexp.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨ht0, ht1, by norm_num, by norm_num, hph.1, hph.2.1, by norm_num, hph.2.2.1, hph.2.2.2⟩


private lemma phaseAt_303 :
    phaseHolds (((303 : ℝ) / 1000)) ((78046801 : ℝ) / 250000000) ((39023407 : ℝ) / 125000000) ((113349349 : ℝ) / 125000000) ((906795937 : ℝ) / 1000000000) := by
  have ht0 : (0 : ℝ) < ((303 : ℝ) / 1000) := by norm_num
  have ht1 : ((303 : ℝ) / 1000) ≤ 1 := by norm_num
  obtain ⟨hs7, hs5, hc6, hc4⟩ := trigPoly_bounds ht0
  have hsLo : ((298384881 : ℝ) / 1000000000) < sin (((303 : ℝ) / 1000)) := by
    have hnum : ((298384881 : ℝ) / 1000000000) <
        ((303 : ℝ) / 1000) - (((303 : ℝ) / 1000)) ^ 3 / 6 + (((303 : ℝ) / 1000)) ^ 5 / 120 - (((303 : ℝ) / 1000)) ^ 7 / 5040 := by norm_num
    linarith
  have hsHi : sin (((303 : ℝ) / 1000)) < ((298384929 : ℝ) / 1000000000) := by
    have hnum : ((303 : ℝ) / 1000) - (((303 : ℝ) / 1000)) ^ 3 / 6 + (((303 : ℝ) / 1000)) ^ 5 / 120 < ((298384929 : ℝ) / 1000000000) := by norm_num
    linarith
  have hcLo : ((954445629 : ℝ) / 1000000000) < cos (((303 : ℝ) / 1000)) := by
    have hnum : ((954445629 : ℝ) / 1000000000) <
        1 - (((303 : ℝ) / 1000)) ^ 2 / 2 + (((303 : ℝ) / 1000)) ^ 4 / 24 - (((303 : ℝ) / 1000)) ^ 6 / 720 := by norm_num
    linarith
  have hcHi : cos (((303 : ℝ) / 1000)) < ((59652919 : ℝ) / 62500000) := by
    have hnum : 1 - (((303 : ℝ) / 1000)) ^ 2 / 2 + (((303 : ℝ) / 1000)) ^ 4 / 24 < ((59652919 : ℝ) / 62500000) := by norm_num
    linarith
  have hexp := exp_between (x := ((303 : ℝ) / 1000)) (n := 8) (lo := ((67695723 : ℝ) / 50000000)) (hi := ((270782893 : ℝ) / 200000000))
    ht0.le ht1 (by decide)
    (by norm_num [sum_range_succ, Nat.factorial])
    (by norm_num [sum_range_succ, Nat.factorial])
  have hph : ((78046801 : ℝ) / 250000000) < chordAmp (((303 : ℝ) / 1000)) ∧ chordAmp (((303 : ℝ) / 1000)) < ((39023407 : ℝ) / 125000000) ∧
      ((113349349 : ℝ) / 125000000) < gammaSEqual (((303 : ℝ) / 1000)) ∧ gammaSEqual (((303 : ℝ) / 1000)) < ((906795937 : ℝ) / 1000000000) := by
    exact phase_bounds ht0 ht1 hsLo hsHi hcLo hcHi hexp.1 hexp.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨ht0, ht1, by norm_num, by norm_num, hph.1, hph.2.1, by norm_num, hph.2.2.1, hph.2.2.2⟩


private lemma phaseAt_311 :
    phaseHolds (((311 : ℝ) / 1000)) ((320929317 : ℝ) / 1000000000) ((320929379 : ℝ) / 1000000000) ((180345981 : ℝ) / 200000000) ((901731249 : ℝ) / 1000000000) := by
  have ht0 : (0 : ℝ) < ((311 : ℝ) / 1000) := by norm_num
  have ht1 : ((311 : ℝ) / 1000) ≤ 1 := by norm_num
  obtain ⟨hs7, hs5, hc6, hc4⟩ := trigPoly_bounds ht0
  have hsLo : ((306010817 : ℝ) / 1000000000) < sin (((311 : ℝ) / 1000)) := by
    have hnum : ((306010817 : ℝ) / 1000000000) <
        ((311 : ℝ) / 1000) - (((311 : ℝ) / 1000)) ^ 3 / 6 + (((311 : ℝ) / 1000)) ^ 5 / 120 - (((311 : ℝ) / 1000)) ^ 7 / 5040 := by norm_num
    linarith
  have hsHi : sin (((311 : ℝ) / 1000)) < ((153005437 : ℝ) / 500000000) := by
    have hnum : ((311 : ℝ) / 1000) - (((311 : ℝ) / 1000)) ^ 3 / 6 + (((311 : ℝ) / 1000)) ^ 5 / 120 < ((153005437 : ℝ) / 500000000) := by norm_num
    linarith
  have hcLo : ((7437719 : ℝ) / 7812500) < cos (((311 : ℝ) / 1000)) := by
    have hnum : ((7437719 : ℝ) / 7812500) <
        1 - (((311 : ℝ) / 1000)) ^ 2 / 2 + (((311 : ℝ) / 1000)) ^ 4 / 24 - (((311 : ℝ) / 1000)) ^ 6 / 720 := by norm_num
    linarith
  have hcHi : cos (((311 : ℝ) / 1000)) < ((95202929 : ℝ) / 100000000) := by
    have hnum : 1 - (((311 : ℝ) / 1000)) ^ 2 / 2 + (((311 : ℝ) / 1000)) ^ 4 / 24 < ((95202929 : ℝ) / 100000000) := by norm_num
    linarith
  have hexp := exp_between (x := ((311 : ℝ) / 1000)) (n := 8) (lo := ((42649663 : ℝ) / 31250000)) (hi := ((682394611 : ℝ) / 500000000))
    ht0.le ht1 (by decide)
    (by norm_num [sum_range_succ, Nat.factorial])
    (by norm_num [sum_range_succ, Nat.factorial])
  have hph : ((320929317 : ℝ) / 1000000000) < chordAmp (((311 : ℝ) / 1000)) ∧ chordAmp (((311 : ℝ) / 1000)) < ((320929379 : ℝ) / 1000000000) ∧
      ((180345981 : ℝ) / 200000000) < gammaSEqual (((311 : ℝ) / 1000)) ∧ gammaSEqual (((311 : ℝ) / 1000)) < ((901731249 : ℝ) / 1000000000) := by
    exact phase_bounds ht0 ht1 hsLo hsHi hcLo hcHi hexp.1 hexp.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨ht0, ht1, by norm_num, by norm_num, hph.1, hph.2.1, by norm_num, hph.2.2.1, hph.2.2.2⟩


private lemma phaseAt_312 :
    phaseHolds (((312 : ℝ) / 1000)) ((32202477 : ℝ) / 100000000) ((322024833 : ℝ) / 1000000000) ((901086951 : ℝ) / 1000000000) ((450544161 : ℝ) / 500000000) := by
  have ht0 : (0 : ℝ) < ((312 : ℝ) / 1000) := by norm_num
  have ht1 : ((312 : ℝ) / 1000) ≤ 1 := by norm_num
  obtain ⟨hs7, hs5, hc6, hc4⟩ := trigPoly_bounds ht0
  have hsLo : ((76740673 : ℝ) / 250000000) < sin (((312 : ℝ) / 1000)) := by
    have hnum : ((76740673 : ℝ) / 250000000) <
        ((312 : ℝ) / 1000) - (((312 : ℝ) / 1000)) ^ 3 / 6 + (((312 : ℝ) / 1000)) ^ 5 / 120 - (((312 : ℝ) / 1000)) ^ 7 / 5040 := by norm_num
    linarith
  have hsHi : sin (((312 : ℝ) / 1000)) < ((1227851 : ℝ) / 4000000) := by
    have hnum : ((312 : ℝ) / 1000) - (((312 : ℝ) / 1000)) ^ 3 / 6 + (((312 : ℝ) / 1000)) ^ 5 / 120 < ((1227851 : ℝ) / 4000000) := by norm_num
    linarith
  have hcLo : ((475860773 : ℝ) / 500000000) < cos (((312 : ℝ) / 1000)) := by
    have hnum : ((475860773 : ℝ) / 500000000) <
        1 - (((312 : ℝ) / 1000)) ^ 2 / 2 + (((312 : ℝ) / 1000)) ^ 4 / 24 - (((312 : ℝ) / 1000)) ^ 6 / 720 := by norm_num
    linarith
  have hcHi : cos (((312 : ℝ) / 1000)) < ((237930707 : ℝ) / 250000000) := by
    have hnum : 1 - (((312 : ℝ) / 1000)) ^ 2 / 2 + (((312 : ℝ) / 1000)) ^ 4 / 24 < ((237930707 : ℝ) / 250000000) := by norm_num
    linarith
  have hexp := exp_between (x := ((312 : ℝ) / 1000)) (n := 8) (lo := ((21346167 : ℝ) / 15625000)) (hi := ((683077347 : ℝ) / 500000000))
    ht0.le ht1 (by decide)
    (by norm_num [sum_range_succ, Nat.factorial])
    (by norm_num [sum_range_succ, Nat.factorial])
  have hph : ((32202477 : ℝ) / 100000000) < chordAmp (((312 : ℝ) / 1000)) ∧ chordAmp (((312 : ℝ) / 1000)) < ((322024833 : ℝ) / 1000000000) ∧
      ((901086951 : ℝ) / 1000000000) < gammaSEqual (((312 : ℝ) / 1000)) ∧ gammaSEqual (((312 : ℝ) / 1000)) < ((450544161 : ℝ) / 500000000) := by
    exact phase_bounds ht0 ht1 hsLo hsHi hcLo hcHi hexp.1 hexp.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨ht0, ht1, by norm_num, by norm_num, hph.1, hph.2.1, by norm_num, hph.2.2.1, hph.2.2.2⟩


private lemma phaseAt_321 :
    phaseHolds (((321 : ℝ) / 1000)) ((165955611 : ℝ) / 500000000) ((3319113 : ℝ) / 10000000) ((223800399 : ℝ) / 250000000) ((447601613 : ℝ) / 500000000) := by
  have ht0 : (0 : ℝ) < ((321 : ℝ) / 1000) := by norm_num
  have ht1 : ((321 : ℝ) / 1000) ≤ 1 := by norm_num
  obtain ⟨hs7, hs5, hc6, hc4⟩ := trigPoly_bounds ht0
  have hsLo : ((157757819 : ℝ) / 500000000) < sin (((321 : ℝ) / 1000)) := by
    have hnum : ((157757819 : ℝ) / 500000000) <
        ((321 : ℝ) / 1000) - (((321 : ℝ) / 1000)) ^ 3 / 6 + (((321 : ℝ) / 1000)) ^ 5 / 120 - (((321 : ℝ) / 1000)) ^ 7 / 5040 := by norm_num
    linarith
  have hsHi : sin (((321 : ℝ) / 1000)) < ((315515709 : ℝ) / 1000000000) := by
    have hnum : ((321 : ℝ) / 1000) - (((321 : ℝ) / 1000)) ^ 3 / 6 + (((321 : ℝ) / 1000)) ^ 5 / 120 < ((315515709 : ℝ) / 1000000000) := by norm_num
    linarith
  have hcLo : ((474460187 : ℝ) / 500000000) < cos (((321 : ℝ) / 1000)) := by
    have hnum : ((474460187 : ℝ) / 500000000) <
        1 - (((321 : ℝ) / 1000)) ^ 2 / 2 + (((321 : ℝ) / 1000)) ^ 4 / 24 - (((321 : ℝ) / 1000)) ^ 6 / 720 := by norm_num
    linarith
  have hcHi : cos (((321 : ℝ) / 1000)) < ((474460947 : ℝ) / 500000000) := by
    have hnum : 1 - (((321 : ℝ) / 1000)) ^ 2 / 2 + (((321 : ℝ) / 1000)) ^ 4 / 24 < ((474460947 : ℝ) / 500000000) := by norm_num
    linarith
  have hexp := exp_between (x := ((321 : ℝ) / 1000)) (n := 8) (lo := ((689252787 : ℝ) / 500000000)) (hi := ((689252791 : ℝ) / 500000000))
    ht0.le ht1 (by decide)
    (by norm_num [sum_range_succ, Nat.factorial])
    (by norm_num [sum_range_succ, Nat.factorial])
  have hph : ((165955611 : ℝ) / 500000000) < chordAmp (((321 : ℝ) / 1000)) ∧ chordAmp (((321 : ℝ) / 1000)) < ((3319113 : ℝ) / 10000000) ∧
      ((223800399 : ℝ) / 250000000) < gammaSEqual (((321 : ℝ) / 1000)) ∧ gammaSEqual (((321 : ℝ) / 1000)) < ((447601613 : ℝ) / 500000000) := by
    exact phase_bounds ht0 ht1 hsLo hsHi hcLo hcHi hexp.1 hexp.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨ht0, ht1, by norm_num, by norm_num, hph.1, hph.2.1, by norm_num, hph.2.2.1, hph.2.2.2⟩


private lemma phaseAt_322 :
    phaseHolds (((322 : ℝ) / 1000)) ((333012791 : ℝ) / 1000000000) ((333012871 : ℝ) / 1000000000) ((894536671 : ℝ) / 1000000000) ((447269167 : ℝ) / 500000000) := by
  have ht0 : (0 : ℝ) < ((322 : ℝ) / 1000) := by norm_num
  have ht1 : ((322 : ℝ) / 1000) ≤ 1 := by norm_num
  obtain ⟨hs7, hs5, hc6, hc4⟩ := trigPoly_bounds ht0
  have hsLo : ((791161 : ℝ) / 2500000) < sin (((322 : ℝ) / 1000)) := by
    have hnum : ((791161 : ℝ) / 2500000) <
        ((322 : ℝ) / 1000) - (((322 : ℝ) / 1000)) ^ 3 / 6 + (((322 : ℝ) / 1000)) ^ 5 / 120 - (((322 : ℝ) / 1000)) ^ 7 / 5040 := by norm_num
    linarith
  have hsHi : sin (((322 : ℝ) / 1000)) < ((316464473 : ℝ) / 1000000000) := by
    have hnum : ((322 : ℝ) / 1000) - (((322 : ℝ) / 1000)) ^ 3 / 6 + (((322 : ℝ) / 1000)) ^ 5 / 120 < ((316464473 : ℝ) / 1000000000) := by norm_num
    linarith
  have hcLo : ((29643887 : ℝ) / 31250000) < cos (((322 : ℝ) / 1000)) := by
    have hnum : ((29643887 : ℝ) / 31250000) <
        1 - (((322 : ℝ) / 1000)) ^ 2 / 2 + (((322 : ℝ) / 1000)) ^ 4 / 24 - (((322 : ℝ) / 1000)) ^ 6 / 720 := by norm_num
    linarith
  have hcHi : cos (((322 : ℝ) / 1000)) < ((948605933 : ℝ) / 1000000000) := by
    have hnum : 1 - (((322 : ℝ) / 1000)) ^ 2 / 2 + (((322 : ℝ) / 1000)) ^ 4 / 24 < ((948605933 : ℝ) / 1000000000) := by norm_num
    linarith
  have hexp := exp_between (x := ((322 : ℝ) / 1000)) (n := 8) (lo := ((1379884769 : ℝ) / 1000000000)) (hi := ((1379884777 : ℝ) / 1000000000))
    ht0.le ht1 (by decide)
    (by norm_num [sum_range_succ, Nat.factorial])
    (by norm_num [sum_range_succ, Nat.factorial])
  have hph : ((333012791 : ℝ) / 1000000000) < chordAmp (((322 : ℝ) / 1000)) ∧ chordAmp (((322 : ℝ) / 1000)) < ((333012871 : ℝ) / 1000000000) ∧
      ((894536671 : ℝ) / 1000000000) < gammaSEqual (((322 : ℝ) / 1000)) ∧ gammaSEqual (((322 : ℝ) / 1000)) < ((447269167 : ℝ) / 500000000) := by
    exact phase_bounds ht0 ht1 hsLo hsHi hcLo hcHi hexp.1 hexp.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨ht0, ht1, by norm_num, by norm_num, hph.1, hph.2.1, by norm_num, hph.2.2.1, hph.2.2.2⟩


private lemma phaseAt_323 :
    phaseHolds (((323 : ℝ) / 1000)) ((167057491 : ℝ) / 500000000) ((334115063 : ℝ) / 1000000000) ((893869543 : ℝ) / 1000000000) ((893871237 : ℝ) / 1000000000) := by
  have ht0 : (0 : ℝ) < ((323 : ℝ) / 1000) := by norm_num
  have ht1 : ((323 : ℝ) / 1000) ≤ 1 := by norm_num
  obtain ⟨hs7, hs5, hc6, hc4⟩ := trigPoly_bounds ht0
  have hsLo : ((158706423 : ℝ) / 500000000) < sin (((323 : ℝ) / 1000)) := by
    have hnum : ((158706423 : ℝ) / 500000000) <
        ((323 : ℝ) / 1000) - (((323 : ℝ) / 1000)) ^ 3 / 6 + (((323 : ℝ) / 1000)) ^ 5 / 120 - (((323 : ℝ) / 1000)) ^ 7 / 5040 := by norm_num
    linarith
  have hsHi : sin (((323 : ℝ) / 1000)) < ((7935323 : ℝ) / 25000000) := by
    have hnum : ((323 : ℝ) / 1000) - (((323 : ℝ) / 1000)) ^ 3 / 6 + (((323 : ℝ) / 1000)) ^ 5 / 120 < ((7935323 : ℝ) / 25000000) := by norm_num
    linarith
  have hcLo : ((189657489 : ℝ) / 200000000) < cos (((323 : ℝ) / 1000)) := by
    have hnum : ((189657489 : ℝ) / 200000000) <
        1 - (((323 : ℝ) / 1000)) ^ 2 / 2 + (((323 : ℝ) / 1000)) ^ 4 / 24 - (((323 : ℝ) / 1000)) ^ 6 / 720 := by norm_num
    linarith
  have hcHi : cos (((323 : ℝ) / 1000)) < ((948289023 : ℝ) / 1000000000) := by
    have hnum : 1 - (((323 : ℝ) / 1000)) ^ 2 / 2 + (((323 : ℝ) / 1000)) ^ 4 / 24 < ((948289023 : ℝ) / 1000000000) := by norm_num
    linarith
  have hexp := exp_between (x := ((323 : ℝ) / 1000)) (n := 8) (lo := ((21582271 : ℝ) / 15625000)) (hi := ((172658169 : ℝ) / 125000000))
    ht0.le ht1 (by decide)
    (by norm_num [sum_range_succ, Nat.factorial])
    (by norm_num [sum_range_succ, Nat.factorial])
  have hph : ((167057491 : ℝ) / 500000000) < chordAmp (((323 : ℝ) / 1000)) ∧ chordAmp (((323 : ℝ) / 1000)) < ((334115063 : ℝ) / 1000000000) ∧
      ((893869543 : ℝ) / 1000000000) < gammaSEqual (((323 : ℝ) / 1000)) ∧ gammaSEqual (((323 : ℝ) / 1000)) < ((893871237 : ℝ) / 1000000000) := by
    exact phase_bounds ht0 ht1 hsLo hsHi hcLo hcHi hexp.1 hexp.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨ht0, ht1, by norm_num, by norm_num, hph.1, hph.2.1, by norm_num, hph.2.2.1, hph.2.2.2⟩


private lemma phaseAt_324 :
    phaseHolds (((324 : ℝ) / 1000)) ((335217797 : ℝ) / 1000000000) ((335217879 : ℝ) / 1000000000) ((893200209 : ℝ) / 1000000000) ((55825121 : ℝ) / 62500000) := by
  have ht0 : (0 : ℝ) < ((324 : ℝ) / 1000) := by norm_num
  have ht1 : ((324 : ℝ) / 1000) ≤ 1 := by norm_num
  obtain ⟨hs7, hs5, hc6, hc4⟩ := trigPoly_bounds ht0
  have hsLo : ((12734439 : ℝ) / 40000000) < sin (((324 : ℝ) / 1000)) := by
    have hnum : ((12734439 : ℝ) / 40000000) <
        ((324 : ℝ) / 1000) - (((324 : ℝ) / 1000)) ^ 3 / 6 + (((324 : ℝ) / 1000)) ^ 5 / 120 - (((324 : ℝ) / 1000)) ^ 7 / 5040 := by norm_num
    linarith
  have hsHi : sin (((324 : ℝ) / 1000)) < ((6367221 : ℝ) / 20000000) := by
    have hnum : ((324 : ℝ) / 1000) - (((324 : ℝ) / 1000)) ^ 3 / 6 + (((324 : ℝ) / 1000)) ^ 5 / 120 < ((6367221 : ℝ) / 20000000) := by norm_num
    linarith
  have hcLo : ((473984779 : ℝ) / 500000000) < cos (((324 : ℝ) / 1000)) := by
    have hnum : ((473984779 : ℝ) / 500000000) <
        1 - (((324 : ℝ) / 1000)) ^ 2 / 2 + (((324 : ℝ) / 1000)) ^ 4 / 24 - (((324 : ℝ) / 1000)) ^ 6 / 720 := by norm_num
    linarith
  have hcHi : cos (((324 : ℝ) / 1000)) < ((473985583 : ℝ) / 500000000) := by
    have hnum : 1 - (((324 : ℝ) / 1000)) ^ 2 / 2 + (((324 : ℝ) / 1000)) ^ 4 / 24 < ((473985583 : ℝ) / 500000000) := by norm_num
    linarith
  have hexp := exp_between (x := ((324 : ℝ) / 1000)) (n := 8) (lo := ((13826473 : ℝ) / 10000000)) (hi := ((345661827 : ℝ) / 250000000))
    ht0.le ht1 (by decide)
    (by norm_num [sum_range_succ, Nat.factorial])
    (by norm_num [sum_range_succ, Nat.factorial])
  have hph : ((335217797 : ℝ) / 1000000000) < chordAmp (((324 : ℝ) / 1000)) ∧ chordAmp (((324 : ℝ) / 1000)) < ((335217879 : ℝ) / 1000000000) ∧
      ((893200209 : ℝ) / 1000000000) < gammaSEqual (((324 : ℝ) / 1000)) ∧ gammaSEqual (((324 : ℝ) / 1000)) < ((55825121 : ℝ) / 62500000) := by
    exact phase_bounds ht0 ht1 hsLo hsHi hcLo hcHi hexp.1 hexp.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨ht0, ht1, by norm_num, by norm_num, hph.1, hph.2.1, by norm_num, hph.2.2.1, hph.2.2.2⟩


private lemma phaseAt_325 :
    phaseHolds (((325 : ℝ) / 1000)) ((84080309 : ℝ) / 250000000) ((8408033 : ℝ) / 25000000) ((89252867 : ℝ) / 100000000) ((892530429 : ℝ) / 1000000000) := by
  have ht0 : (0 : ℝ) < ((325 : ℝ) / 1000) := by norm_num
  have ht1 : ((325 : ℝ) / 1000) ≤ 1 := by norm_num
  obtain ⟨hs7, hs5, hc6, hc4⟩ := trigPoly_bounds ht0
  have hsLo : ((63861757 : ℝ) / 200000000) < sin (((325 : ℝ) / 1000)) := by
    have hnum : ((63861757 : ℝ) / 200000000) <
        ((325 : ℝ) / 1000) - (((325 : ℝ) / 1000)) ^ 3 / 6 + (((325 : ℝ) / 1000)) ^ 5 / 120 - (((325 : ℝ) / 1000)) ^ 7 / 5040 := by norm_num
    linarith
  have hsHi : sin (((325 : ℝ) / 1000)) < ((159654431 : ℝ) / 500000000) := by
    have hnum : ((325 : ℝ) / 1000) - (((325 : ℝ) / 1000)) ^ 3 / 6 + (((325 : ℝ) / 1000)) ^ 5 / 120 < ((159654431 : ℝ) / 500000000) := by norm_num
    linarith
  have hcLo : ((947650723 : ℝ) / 1000000000) < cos (((325 : ℝ) / 1000)) := by
    have hnum : ((947650723 : ℝ) / 1000000000) <
        1 - (((325 : ℝ) / 1000)) ^ 2 / 2 + (((325 : ℝ) / 1000)) ^ 4 / 24 - (((325 : ℝ) / 1000)) ^ 6 / 720 := by norm_num
    linarith
  have hcHi : cos (((325 : ℝ) / 1000)) < ((947652361 : ℝ) / 1000000000) := by
    have hnum : 1 - (((325 : ℝ) / 1000)) ^ 2 / 2 + (((325 : ℝ) / 1000)) ^ 4 / 24 < ((947652361 : ℝ) / 1000000000) := by norm_num
    linarith
  have hexp := exp_between (x := ((325 : ℝ) / 1000)) (n := 8) (lo := ((1384030639 : ℝ) / 1000000000)) (hi := ((1384030647 : ℝ) / 1000000000))
    ht0.le ht1 (by decide)
    (by norm_num [sum_range_succ, Nat.factorial])
    (by norm_num [sum_range_succ, Nat.factorial])
  have hph : ((84080309 : ℝ) / 250000000) < chordAmp (((325 : ℝ) / 1000)) ∧ chordAmp (((325 : ℝ) / 1000)) < ((8408033 : ℝ) / 25000000) ∧
      ((89252867 : ℝ) / 100000000) < gammaSEqual (((325 : ℝ) / 1000)) ∧ gammaSEqual (((325 : ℝ) / 1000)) < ((892530429 : ℝ) / 1000000000) := by
    exact phase_bounds ht0 ht1 hsLo hsHi hcLo hcHi hexp.1 hexp.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨ht0, ht1, by norm_num, by norm_num, hph.1, hph.2.1, by norm_num, hph.2.2.1, hph.2.2.2⟩


private lemma phaseAt_330 :
    phaseHolds (((330 : ℝ) / 1000)) ((5341373 : ℝ) / 15625000) ((68369593 : ℝ) / 200000000) ((889137833 : ℝ) / 1000000000) ((222284941 : ℝ) / 250000000) := by
  have ht0 : (0 : ℝ) < ((330 : ℝ) / 1000) := by norm_num
  have ht1 : ((330 : ℝ) / 1000) ≤ 1 := by norm_num
  obtain ⟨hs7, hs5, hc6, hc4⟩ := trigPoly_bounds ht0
  have hsLo : ((81010757 : ℝ) / 250000000) < sin (((330 : ℝ) / 1000)) := by
    have hnum : ((81010757 : ℝ) / 250000000) <
        ((330 : ℝ) / 1000) - (((330 : ℝ) / 1000)) ^ 3 / 6 + (((330 : ℝ) / 1000)) ^ 5 / 120 - (((330 : ℝ) / 1000)) ^ 7 / 5040 := by norm_num
    linarith
  have hsHi : sin (((330 : ℝ) / 1000)) < ((324043113 : ℝ) / 1000000000) := by
    have hnum : ((330 : ℝ) / 1000) - (((330 : ℝ) / 1000)) ^ 3 / 6 + (((330 : ℝ) / 1000)) ^ 5 / 120 < ((324043113 : ℝ) / 1000000000) := by norm_num
    linarith
  have hcLo : ((47302117 : ℝ) / 50000000) < cos (((330 : ℝ) / 1000)) := by
    have hnum : ((47302117 : ℝ) / 50000000) <
        1 - (((330 : ℝ) / 1000)) ^ 2 / 2 + (((330 : ℝ) / 1000)) ^ 4 / 24 - (((330 : ℝ) / 1000)) ^ 6 / 720 := by norm_num
    linarith
  have hcHi : cos (((330 : ℝ) / 1000)) < ((473022067 : ℝ) / 500000000) := by
    have hnum : 1 - (((330 : ℝ) / 1000)) ^ 2 / 2 + (((330 : ℝ) / 1000)) ^ 4 / 24 < ((473022067 : ℝ) / 500000000) := by norm_num
    linarith
  have hexp := exp_between (x := ((330 : ℝ) / 1000)) (n := 8) (lo := ((34774203 : ℝ) / 25000000)) (hi := ((1390968129 : ℝ) / 1000000000))
    ht0.le ht1 (by decide)
    (by norm_num [sum_range_succ, Nat.factorial])
    (by norm_num [sum_range_succ, Nat.factorial])
  have hph : ((5341373 : ℝ) / 15625000) < chordAmp (((330 : ℝ) / 1000)) ∧ chordAmp (((330 : ℝ) / 1000)) < ((68369593 : ℝ) / 200000000) ∧
      ((889137833 : ℝ) / 1000000000) < gammaSEqual (((330 : ℝ) / 1000)) ∧ gammaSEqual (((330 : ℝ) / 1000)) < ((222284941 : ℝ) / 250000000) := by
    exact phase_bounds ht0 ht1 hsLo hsHi hcLo hcHi hexp.1 hexp.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨ht0, ht1, by norm_num, by norm_num, hph.1, hph.2.1, by norm_num, hph.2.2.1, hph.2.2.2⟩


private lemma phaseAt_342 :
    phaseHolds (((342 : ℝ) / 1000)) ((355177069 : ℝ) / 1000000000) ((88794297 : ℝ) / 250000000) ((220193427 : ℝ) / 250000000) ((880776113 : ℝ) / 1000000000) := by
  have ht0 : (0 : ℝ) < ((342 : ℝ) / 1000) := by norm_num
  have ht1 : ((342 : ℝ) / 1000) ≤ 1 := by norm_num
  obtain ⟨hs7, hs5, hc6, hc4⟩ := trigPoly_bounds ht0
  have hsLo : ((335371933 : ℝ) / 1000000000) < sin (((342 : ℝ) / 1000)) := by
    have hnum : ((335371933 : ℝ) / 1000000000) <
        ((342 : ℝ) / 1000) - (((342 : ℝ) / 1000)) ^ 3 / 6 + (((342 : ℝ) / 1000)) ^ 5 / 120 - (((342 : ℝ) / 1000)) ^ 7 / 5040 := by norm_num
    linarith
  have hsHi : sin (((342 : ℝ) / 1000)) < ((167686021 : ℝ) / 500000000) := by
    have hnum : ((342 : ℝ) / 1000) - (((342 : ℝ) / 1000)) ^ 3 / 6 + (((342 : ℝ) / 1000)) ^ 5 / 120 < ((167686021 : ℝ) / 500000000) := by norm_num
    linarith
  have hcLo : ((942085801 : ℝ) / 1000000000) < cos (((342 : ℝ) / 1000)) := by
    have hnum : ((942085801 : ℝ) / 1000000000) <
        1 - (((342 : ℝ) / 1000)) ^ 2 / 2 + (((342 : ℝ) / 1000)) ^ 4 / 24 - (((342 : ℝ) / 1000)) ^ 6 / 720 := by norm_num
    linarith
  have hcHi : cos (((342 : ℝ) / 1000)) < ((37683521 : ℝ) / 40000000) := by
    have hnum : 1 - (((342 : ℝ) / 1000)) ^ 2 / 2 + (((342 : ℝ) / 1000)) ^ 4 / 24 < ((37683521 : ℝ) / 40000000) := by norm_num
    linarith
  have hexp := exp_between (x := ((342 : ℝ) / 1000)) (n := 8) (lo := ((1407760287 : ℝ) / 1000000000)) (hi := ((703880149 : ℝ) / 500000000))
    ht0.le ht1 (by decide)
    (by norm_num [sum_range_succ, Nat.factorial])
    (by norm_num [sum_range_succ, Nat.factorial])
  have hph : ((355177069 : ℝ) / 1000000000) < chordAmp (((342 : ℝ) / 1000)) ∧ chordAmp (((342 : ℝ) / 1000)) < ((88794297 : ℝ) / 250000000) ∧
      ((220193427 : ℝ) / 250000000) < gammaSEqual (((342 : ℝ) / 1000)) ∧ gammaSEqual (((342 : ℝ) / 1000)) < ((880776113 : ℝ) / 1000000000) := by
    exact phase_bounds ht0 ht1 hsLo hsHi hcLo hcHi hexp.1 hexp.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨ht0, ht1, by norm_num, by norm_num, hph.1, hph.2.1, by norm_num, hph.2.2.1, hph.2.2.2⟩


private lemma phaseAt_343 :
    phaseHolds (((343 : ℝ) / 1000)) ((11134127 : ℝ) / 31250000) ((178146093 : ℝ) / 500000000) ((440031119 : ℝ) / 500000000) ((440032343 : ℝ) / 500000000) := by
  have ht0 : (0 : ℝ) < ((343 : ℝ) / 1000) := by norm_num
  have ht1 : ((343 : ℝ) / 1000) ≤ 1 := by norm_num
  obtain ⟨hs7, hs5, hc6, hc4⟩ := trigPoly_bounds ht0
  have hsLo : ((336313851 : ℝ) / 1000000000) < sin (((343 : ℝ) / 1000)) := by
    have hnum : ((336313851 : ℝ) / 1000000000) <
        ((343 : ℝ) / 1000) - (((343 : ℝ) / 1000)) ^ 3 / 6 + (((343 : ℝ) / 1000)) ^ 5 / 120 - (((343 : ℝ) / 1000)) ^ 7 / 5040 := by norm_num
    linarith
  have hsHi : sin (((343 : ℝ) / 1000)) < ((168156981 : ℝ) / 500000000) := by
    have hnum : ((343 : ℝ) / 1000) - (((343 : ℝ) / 1000)) ^ 3 / 6 + (((343 : ℝ) / 1000)) ^ 5 / 120 < ((168156981 : ℝ) / 500000000) := by norm_num
    linarith
  have hcLo : ((470874979 : ℝ) / 500000000) < cos (((343 : ℝ) / 1000)) := by
    have hnum : ((470874979 : ℝ) / 500000000) <
        1 - (((343 : ℝ) / 1000)) ^ 2 / 2 + (((343 : ℝ) / 1000)) ^ 4 / 24 - (((343 : ℝ) / 1000)) ^ 6 / 720 := by norm_num
    linarith
  have hcHi : cos (((343 : ℝ) / 1000)) < ((941752221 : ℝ) / 1000000000) := by
    have hnum : 1 - (((343 : ℝ) / 1000)) ^ 2 / 2 + (((343 : ℝ) / 1000)) ^ 4 / 24 < ((941752221 : ℝ) / 1000000000) := by norm_num
    linarith
  have hexp := exp_between (x := ((343 : ℝ) / 1000)) (n := 8) (lo := ((1409168751 : ℝ) / 1000000000)) (hi := ((1409168763 : ℝ) / 1000000000))
    ht0.le ht1 (by decide)
    (by norm_num [sum_range_succ, Nat.factorial])
    (by norm_num [sum_range_succ, Nat.factorial])
  have hph : ((11134127 : ℝ) / 31250000) < chordAmp (((343 : ℝ) / 1000)) ∧ chordAmp (((343 : ℝ) / 1000)) < ((178146093 : ℝ) / 500000000) ∧
      ((440031119 : ℝ) / 500000000) < gammaSEqual (((343 : ℝ) / 1000)) ∧ gammaSEqual (((343 : ℝ) / 1000)) < ((440032343 : ℝ) / 500000000) := by
    exact phase_bounds ht0 ht1 hsLo hsHi hcLo hcHi hexp.1 hexp.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨ht0, ht1, by norm_num, by norm_num, hph.1, hph.2.1, by norm_num, hph.2.2.1, hph.2.2.2⟩


private lemma phaseAt_345 :
    phaseHolds (((345 : ℝ) / 1000)) ((2800969 : ℝ) / 7812500) ((358524159 : ℝ) / 1000000000) ((878632603 : ℝ) / 1000000000) ((439317571 : ℝ) / 500000000) := by
  have ht0 : (0 : ℝ) < ((345 : ℝ) / 1000) := by norm_num
  have ht1 : ((345 : ℝ) / 1000) ≤ 1 := by norm_num
  obtain ⟨hs7, hs5, hc6, hc4⟩ := trigPoly_bounds ht0
  have hsLo : ((338196677 : ℝ) / 1000000000) < sin (((345 : ℝ) / 1000)) := by
    have hnum : ((338196677 : ℝ) / 1000000000) <
        ((345 : ℝ) / 1000) - (((345 : ℝ) / 1000)) ^ 3 / 6 + (((345 : ℝ) / 1000)) ^ 5 / 120 - (((345 : ℝ) / 1000)) ^ 7 / 5040 := by norm_num
    linarith
  have hsHi : sin (((345 : ℝ) / 1000)) < ((338196793 : ℝ) / 1000000000) := by
    have hnum : ((345 : ℝ) / 1000) - (((345 : ℝ) / 1000)) ^ 3 / 6 + (((345 : ℝ) / 1000)) ^ 5 / 120 < ((338196793 : ℝ) / 1000000000) := by norm_num
    linarith
  have hcLo : ((941075447 : ℝ) / 1000000000) < cos (((345 : ℝ) / 1000)) := by
    have hnum : ((941075447 : ℝ) / 1000000000) <
        1 - (((345 : ℝ) / 1000)) ^ 2 / 2 + (((345 : ℝ) / 1000)) ^ 4 / 24 - (((345 : ℝ) / 1000)) ^ 6 / 720 := by norm_num
    linarith
  have hcHi : cos (((345 : ℝ) / 1000)) < ((94107779 : ℝ) / 100000000) := by
    have hnum : 1 - (((345 : ℝ) / 1000)) ^ 2 / 2 + (((345 : ℝ) / 1000)) ^ 4 / 24 < ((94107779 : ℝ) / 100000000) := by norm_num
    linarith
  have hexp := exp_between (x := ((345 : ℝ) / 1000)) (n := 8) (lo := ((352997477 : ℝ) / 250000000)) (hi := ((1411989921 : ℝ) / 1000000000))
    ht0.le ht1 (by decide)
    (by norm_num [sum_range_succ, Nat.factorial])
    (by norm_num [sum_range_succ, Nat.factorial])
  have hph : ((2800969 : ℝ) / 7812500) < chordAmp (((345 : ℝ) / 1000)) ∧ chordAmp (((345 : ℝ) / 1000)) < ((358524159 : ℝ) / 1000000000) ∧
      ((878632603 : ℝ) / 1000000000) < gammaSEqual (((345 : ℝ) / 1000)) ∧ gammaSEqual (((345 : ℝ) / 1000)) < ((439317571 : ℝ) / 500000000) := by
    exact phase_bounds ht0 ht1 hsLo hsHi hcLo hcHi hexp.1 hexp.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨ht0, ht1, by norm_num, by norm_num, hph.1, hph.2.1, by norm_num, hph.2.2.1, hph.2.2.2⟩


private lemma phaseAt_346 :
    phaseHolds (((346 : ℝ) / 1000)) ((22477563 : ℝ) / 62500000) ((359641139 : ℝ) / 1000000000) ((438957219 : ℝ) / 500000000) ((877917021 : ℝ) / 1000000000) := by
  have ht0 : (0 : ℝ) < ((346 : ℝ) / 1000) := by norm_num
  have ht1 : ((346 : ℝ) / 1000) ≤ 1 := by norm_num
  obtain ⟨hs7, hs5, hc6, hc4⟩ := trigPoly_bounds ht0
  have hsLo : ((339137583 : ℝ) / 1000000000) < sin (((346 : ℝ) / 1000)) := by
    have hnum : ((339137583 : ℝ) / 1000000000) <
        ((346 : ℝ) / 1000) - (((346 : ℝ) / 1000)) ^ 3 / 6 + (((346 : ℝ) / 1000)) ^ 5 / 120 - (((346 : ℝ) / 1000)) ^ 7 / 5040 := by norm_num
    linarith
  have hsHi : sin (((346 : ℝ) / 1000)) < ((169568851 : ℝ) / 500000000) := by
    have hnum : ((346 : ℝ) / 1000) - (((346 : ℝ) / 1000)) ^ 3 / 6 + (((346 : ℝ) / 1000)) ^ 5 / 120 < ((169568851 : ℝ) / 500000000) := by norm_num
    linarith
  have hcLo : ((47036839 : ℝ) / 50000000) < cos (((346 : ℝ) / 1000)) := by
    have hnum : ((47036839 : ℝ) / 50000000) <
        1 - (((346 : ℝ) / 1000)) ^ 2 / 2 + (((346 : ℝ) / 1000)) ^ 4 / 24 - (((346 : ℝ) / 1000)) ^ 6 / 720 := by norm_num
    linarith
  have hcHi : cos (((346 : ℝ) / 1000)) < ((235184791 : ℝ) / 250000000) := by
    have hnum : 1 - (((346 : ℝ) / 1000)) ^ 2 / 2 + (((346 : ℝ) / 1000)) ^ 4 / 24 < ((235184791 : ℝ) / 250000000) := by norm_num
    linarith
  have hexp := exp_between (x := ((346 : ℝ) / 1000)) (n := 8) (lo := ((353350651 : ℝ) / 250000000)) (hi := ((1413402617 : ℝ) / 1000000000))
    ht0.le ht1 (by decide)
    (by norm_num [sum_range_succ, Nat.factorial])
    (by norm_num [sum_range_succ, Nat.factorial])
  have hph : ((22477563 : ℝ) / 62500000) < chordAmp (((346 : ℝ) / 1000)) ∧ chordAmp (((346 : ℝ) / 1000)) < ((359641139 : ℝ) / 1000000000) ∧
      ((438957219 : ℝ) / 500000000) < gammaSEqual (((346 : ℝ) / 1000)) ∧ gammaSEqual (((346 : ℝ) / 1000)) < ((877917021 : ℝ) / 1000000000) := by
    exact phase_bounds ht0 ht1 hsLo hsHi hcLo hcHi hexp.1 hexp.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨ht0, ht1, by norm_num, by norm_num, hph.1, hph.2.1, by norm_num, hph.2.2.1, hph.2.2.2⟩


private lemma phaseAt_350 :
    phaseHolds (((350 : ℝ) / 1000)) ((364115573 : ℝ) / 1000000000) ((364115713 : ℝ) / 1000000000) ((437509707 : ℝ) / 500000000) ((437511093 : ℝ) / 500000000) := by
  have ht0 : (0 : ℝ) < ((350 : ℝ) / 1000) := by norm_num
  have ht1 : ((350 : ℝ) / 1000) ≤ 1 := by norm_num
  obtain ⟨hs7, hs5, hc6, hc4⟩ := trigPoly_bounds ht0
  have hsLo : ((342897807 : ℝ) / 1000000000) < sin (((350 : ℝ) / 1000)) := by
    have hnum : ((342897807 : ℝ) / 1000000000) <
        ((350 : ℝ) / 1000) - (((350 : ℝ) / 1000)) ^ 3 / 6 + (((350 : ℝ) / 1000)) ^ 5 / 120 - (((350 : ℝ) / 1000)) ^ 7 / 5040 := by norm_num
    linarith
  have hsHi : sin (((350 : ℝ) / 1000)) < ((68579587 : ℝ) / 200000000) := by
    have hnum : ((350 : ℝ) / 1000) - (((350 : ℝ) / 1000)) ^ 3 / 6 + (((350 : ℝ) / 1000)) ^ 5 / 120 < ((68579587 : ℝ) / 200000000) := by norm_num
    linarith
  have hcLo : ((939372707 : ℝ) / 1000000000) < cos (((350 : ℝ) / 1000)) := by
    have hnum : ((939372707 : ℝ) / 1000000000) <
        1 - (((350 : ℝ) / 1000)) ^ 2 / 2 + (((350 : ℝ) / 1000)) ^ 4 / 24 - (((350 : ℝ) / 1000)) ^ 6 / 720 := by norm_num
    linarith
  have hcHi : cos (((350 : ℝ) / 1000)) < ((939375261 : ℝ) / 1000000000) := by
    have hnum : 1 - (((350 : ℝ) / 1000)) ^ 2 / 2 + (((350 : ℝ) / 1000)) ^ 4 / 24 < ((939375261 : ℝ) / 1000000000) := by norm_num
    linarith
  have hexp := exp_between (x := ((350 : ℝ) / 1000)) (n := 8) (lo := ((88691721 : ℝ) / 62500000)) (hi := ((28381351 : ℝ) / 20000000))
    ht0.le ht1 (by decide)
    (by norm_num [sum_range_succ, Nat.factorial])
    (by norm_num [sum_range_succ, Nat.factorial])
  have hph : ((364115573 : ℝ) / 1000000000) < chordAmp (((350 : ℝ) / 1000)) ∧ chordAmp (((350 : ℝ) / 1000)) < ((364115713 : ℝ) / 1000000000) ∧
      ((437509707 : ℝ) / 500000000) < gammaSEqual (((350 : ℝ) / 1000)) ∧ gammaSEqual (((350 : ℝ) / 1000)) < ((437511093 : ℝ) / 500000000) := by
    exact phase_bounds ht0 ht1 hsLo hsHi hcLo hcHi hexp.1 hexp.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨ht0, ht1, by norm_num, by norm_num, hph.1, hph.2.1, by norm_num, hph.2.2.1, hph.2.2.2⟩


private lemma phaseAt_353 :
    phaseHolds (((353 : ℝ) / 1000)) ((45934817 : ℝ) / 125000000) ((73495737 : ℝ) / 200000000) ((87282463 : ℝ) / 100000000) ((27275861 : ℝ) / 31250000) := by
  have ht0 : (0 : ℝ) < ((353 : ℝ) / 1000) := by norm_num
  have ht1 : ((353 : ℝ) / 1000) ≤ 1 := by norm_num
  obtain ⟨hs7, hs5, hc6, hc4⟩ := trigPoly_bounds ht0
  have hsLo : ((172857189 : ℝ) / 500000000) < sin (((353 : ℝ) / 1000)) := by
    have hnum : ((172857189 : ℝ) / 500000000) <
        ((353 : ℝ) / 1000) - (((353 : ℝ) / 1000)) ^ 3 / 6 + (((353 : ℝ) / 1000)) ^ 5 / 120 - (((353 : ℝ) / 1000)) ^ 7 / 5040 := by norm_num
    linarith
  have hsHi : sin (((353 : ℝ) / 1000)) < ((172857257 : ℝ) / 500000000) := by
    have hnum : ((353 : ℝ) / 1000) - (((353 : ℝ) / 1000)) ^ 3 / 6 + (((353 : ℝ) / 1000)) ^ 5 / 120 < ((172857257 : ℝ) / 500000000) := by norm_num
    linarith
  have hcLo : ((938339787 : ℝ) / 1000000000) < cos (((353 : ℝ) / 1000)) := by
    have hnum : ((938339787 : ℝ) / 1000000000) <
        1 - (((353 : ℝ) / 1000)) ^ 2 / 2 + (((353 : ℝ) / 1000)) ^ 4 / 24 - (((353 : ℝ) / 1000)) ^ 6 / 720 := by norm_num
    linarith
  have hcHi : cos (((353 : ℝ) / 1000)) < ((234585619 : ℝ) / 250000000) := by
    have hnum : 1 - (((353 : ℝ) / 1000)) ^ 2 / 2 + (((353 : ℝ) / 1000)) ^ 4 / 24 < ((234585619 : ℝ) / 250000000) := by norm_num
    linarith
  have hexp := exp_between (x := ((353 : ℝ) / 1000)) (n := 8) (lo := ((142333113 : ℝ) / 100000000)) (hi := ((177916393 : ℝ) / 125000000))
    ht0.le ht1 (by decide)
    (by norm_num [sum_range_succ, Nat.factorial])
    (by norm_num [sum_range_succ, Nat.factorial])
  have hph : ((45934817 : ℝ) / 125000000) < chordAmp (((353 : ℝ) / 1000)) ∧ chordAmp (((353 : ℝ) / 1000)) < ((73495737 : ℝ) / 200000000) ∧
      ((87282463 : ℝ) / 100000000) < gammaSEqual (((353 : ℝ) / 1000)) ∧ gammaSEqual (((353 : ℝ) / 1000)) < ((27275861 : ℝ) / 31250000) := by
    exact phase_bounds ht0 ht1 hsLo hsHi hcLo hcHi hexp.1 hexp.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨ht0, ht1, by norm_num, by norm_num, hph.1, hph.2.1, by norm_num, hph.2.2.1, hph.2.2.2⟩


private lemma phaseAt_354 :
    phaseHolds (((354 : ℝ) / 1000)) ((184300437 : ℝ) / 500000000) ((368601027 : ℝ) / 1000000000) ((17441771 : ℝ) / 20000000) ((436045761 : ℝ) / 500000000) := by
  have ht0 : (0 : ℝ) < ((354 : ℝ) / 1000) := by norm_num
  have ht1 : ((354 : ℝ) / 1000) ≤ 1 := by norm_num
  obtain ⟨hs7, hs5, hc6, hc4⟩ := trigPoly_bounds ht0
  have hsLo : ((2708223 : ℝ) / 7812500) < sin (((354 : ℝ) / 1000)) := by
    have hnum : ((2708223 : ℝ) / 7812500) <
        ((354 : ℝ) / 1000) - (((354 : ℝ) / 1000)) ^ 3 / 6 + (((354 : ℝ) / 1000)) ^ 5 / 120 - (((354 : ℝ) / 1000)) ^ 7 / 5040 := by norm_num
    linarith
  have hsHi : sin (((354 : ℝ) / 1000)) < ((86663171 : ℝ) / 250000000) := by
    have hnum : ((354 : ℝ) / 1000) - (((354 : ℝ) / 1000)) ^ 3 / 6 + (((354 : ℝ) / 1000)) ^ 5 / 120 < ((86663171 : ℝ) / 250000000) := by norm_num
    linarith
  have hcLo : ((234498401 : ℝ) / 250000000) < cos (((354 : ℝ) / 1000)) := by
    have hnum : ((234498401 : ℝ) / 250000000) <
        1 - (((354 : ℝ) / 1000)) ^ 2 / 2 + (((354 : ℝ) / 1000)) ^ 4 / 24 - (((354 : ℝ) / 1000)) ^ 6 / 720 := by norm_num
    linarith
  have hcHi : cos (((354 : ℝ) / 1000)) < ((468998169 : ℝ) / 500000000) := by
    have hnum : 1 - (((354 : ℝ) / 1000)) ^ 2 / 2 + (((354 : ℝ) / 1000)) ^ 4 / 24 < ((468998169 : ℝ) / 500000000) := by norm_num
    linarith
  have hexp := exp_between (x := ((354 : ℝ) / 1000)) (n := 8) (lo := ((1424755173 : ℝ) / 1000000000)) (hi := ((1424755187 : ℝ) / 1000000000))
    ht0.le ht1 (by decide)
    (by norm_num [sum_range_succ, Nat.factorial])
    (by norm_num [sum_range_succ, Nat.factorial])
  have hph : ((184300437 : ℝ) / 500000000) < chordAmp (((354 : ℝ) / 1000)) ∧ chordAmp (((354 : ℝ) / 1000)) < ((368601027 : ℝ) / 1000000000) ∧
      ((17441771 : ℝ) / 20000000) < gammaSEqual (((354 : ℝ) / 1000)) ∧ gammaSEqual (((354 : ℝ) / 1000)) < ((436045761 : ℝ) / 500000000) := by
    exact phase_bounds ht0 ht1 hsLo hsHi hcLo hcHi hexp.1 hexp.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨ht0, ht1, by norm_num, by norm_num, hph.1, hph.2.1, by norm_num, hph.2.2.1, hph.2.2.2⟩


private lemma phaseAt_358 :
    phaseHolds (((358 : ℝ) / 1000)) ((14923881 : ℝ) / 40000000) ((37309719 : ℝ) / 100000000) ((869121759 : ℝ) / 1000000000) ((434562473 : ℝ) / 500000000) := by
  have ht0 : (0 : ℝ) < ((358 : ℝ) / 1000) := by norm_num
  have ht1 : ((358 : ℝ) / 1000) ≤ 1 := by norm_num
  obtain ⟨hs7, hs5, hc6, hc4⟩ := trigPoly_bounds ht0
  have hsLo : ((43800217 : ℝ) / 125000000) < sin (((358 : ℝ) / 1000)) := by
    have hnum : ((43800217 : ℝ) / 125000000) <
        ((358 : ℝ) / 1000) - (((358 : ℝ) / 1000)) ^ 3 / 6 + (((358 : ℝ) / 1000)) ^ 5 / 120 - (((358 : ℝ) / 1000)) ^ 7 / 5040 := by norm_num
    linarith
  have hsHi : sin (((358 : ℝ) / 1000)) < ((175200943 : ℝ) / 500000000) := by
    have hnum : ((358 : ℝ) / 1000) - (((358 : ℝ) / 1000)) ^ 3 / 6 + (((358 : ℝ) / 1000)) ^ 5 / 120 < ((175200943 : ℝ) / 500000000) := by norm_num
    linarith
  have hcLo : ((936599493 : ℝ) / 1000000000) < cos (((358 : ℝ) / 1000)) := by
    have hnum : ((936599493 : ℝ) / 1000000000) <
        1 - (((358 : ℝ) / 1000)) ^ 2 / 2 + (((358 : ℝ) / 1000)) ^ 4 / 24 - (((358 : ℝ) / 1000)) ^ 6 / 720 := by norm_num
    linarith
  have hcHi : cos (((358 : ℝ) / 1000)) < ((468301209 : ℝ) / 500000000) := by
    have hnum : 1 - (((358 : ℝ) / 1000)) ^ 2 / 2 + (((358 : ℝ) / 1000)) ^ 4 / 24 < ((468301209 : ℝ) / 500000000) := by norm_num
    linarith
  have hexp := exp_between (x := ((358 : ℝ) / 1000)) (n := 8) (lo := ((286093121 : ℝ) / 200000000)) (hi := ((715232811 : ℝ) / 500000000))
    ht0.le ht1 (by decide)
    (by norm_num [sum_range_succ, Nat.factorial])
    (by norm_num [sum_range_succ, Nat.factorial])
  have hph : ((14923881 : ℝ) / 40000000) < chordAmp (((358 : ℝ) / 1000)) ∧ chordAmp (((358 : ℝ) / 1000)) < ((37309719 : ℝ) / 100000000) ∧
      ((869121759 : ℝ) / 1000000000) < gammaSEqual (((358 : ℝ) / 1000)) ∧ gammaSEqual (((358 : ℝ) / 1000)) < ((434562473 : ℝ) / 500000000) := by
    exact phase_bounds ht0 ht1 hsLo hsHi hcLo hcHi hexp.1 hexp.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨ht0, ht1, by norm_num, by norm_num, hph.1, hph.2.1, by norm_num, hph.2.2.1, hph.2.2.2⟩


private lemma phaseAt_359 :
    phaseHolds (((359 : ℝ) / 1000)) ((37422277 : ℝ) / 100000000) ((374222939 : ℝ) / 1000000000) ((434187219 : ℝ) / 500000000) ((868377679 : ℝ) / 1000000000) := by
  have ht0 : (0 : ℝ) < ((359 : ℝ) / 1000) := by norm_num
  have ht1 : ((359 : ℝ) / 1000) ≤ 1 := by norm_num
  obtain ⟨hs7, hs5, hc6, hc4⟩ := trigPoly_bounds ht0
  have hsLo : ((4391727 : ℝ) / 12500000) < sin (((359 : ℝ) / 1000)) := by
    have hnum : ((4391727 : ℝ) / 12500000) <
        ((359 : ℝ) / 1000) - (((359 : ℝ) / 1000)) ^ 3 / 6 + (((359 : ℝ) / 1000)) ^ 5 / 120 - (((359 : ℝ) / 1000)) ^ 7 / 5040 := by norm_num
    linarith
  have hsHi : sin (((359 : ℝ) / 1000)) < ((351338313 : ℝ) / 1000000000) := by
    have hnum : ((359 : ℝ) / 1000) - (((359 : ℝ) / 1000)) ^ 3 / 6 + (((359 : ℝ) / 1000)) ^ 5 / 120 < ((351338313 : ℝ) / 1000000000) := by norm_num
    linarith
  have hcLo : ((936248623 : ℝ) / 1000000000) < cos (((359 : ℝ) / 1000)) := by
    have hnum : ((936248623 : ℝ) / 1000000000) <
        1 - (((359 : ℝ) / 1000)) ^ 2 / 2 + (((359 : ℝ) / 1000)) ^ 4 / 24 - (((359 : ℝ) / 1000)) ^ 6 / 720 := by norm_num
    linarith
  have hcHi : cos (((359 : ℝ) / 1000)) < ((936251597 : ℝ) / 1000000000) := by
    have hnum : 1 - (((359 : ℝ) / 1000)) ^ 2 / 2 + (((359 : ℝ) / 1000)) ^ 4 / 24 < ((936251597 : ℝ) / 1000000000) := by norm_num
    linarith
  have hexp := exp_between (x := ((359 : ℝ) / 1000)) (n := 8) (lo := ((715948393 : ℝ) / 500000000)) (hi := ((1431896803 : ℝ) / 1000000000))
    ht0.le ht1 (by decide)
    (by norm_num [sum_range_succ, Nat.factorial])
    (by norm_num [sum_range_succ, Nat.factorial])
  have hph : ((37422277 : ℝ) / 100000000) < chordAmp (((359 : ℝ) / 1000)) ∧ chordAmp (((359 : ℝ) / 1000)) < ((374222939 : ℝ) / 1000000000) ∧
      ((434187219 : ℝ) / 500000000) < gammaSEqual (((359 : ℝ) / 1000)) ∧ gammaSEqual (((359 : ℝ) / 1000)) < ((868377679 : ℝ) / 1000000000) := by
    exact phase_bounds ht0 ht1 hsLo hsHi hcLo hcHi hexp.1 hexp.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨ht0, ht1, by norm_num, by norm_num, hph.1, hph.2.1, by norm_num, hph.2.2.1, hph.2.2.2⟩


private lemma phaseAt_360 :
    phaseHolds (((360 : ℝ) / 1000)) ((187674601 : ℝ) / 500000000) ((600559 : ℝ) / 1600000) ((27113277 : ℝ) / 31250000) ((433814081 : ℝ) / 500000000) := by
  have ht0 : (0 : ℝ) < ((360 : ℝ) / 1000) := by norm_num
  have ht1 : ((360 : ℝ) / 1000) ≤ 1 := by norm_num
  obtain ⟨hs7, hs5, hc6, hc4⟩ := trigPoly_bounds ht0
  have hsLo : ((44034279 : ℝ) / 125000000) < sin (((360 : ℝ) / 1000)) := by
    have hnum : ((44034279 : ℝ) / 125000000) <
        ((360 : ℝ) / 1000) - (((360 : ℝ) / 1000)) ^ 3 / 6 + (((360 : ℝ) / 1000)) ^ 5 / 120 - (((360 : ℝ) / 1000)) ^ 7 / 5040 := by norm_num
    linarith
  have hsHi : sin (((360 : ℝ) / 1000)) < ((352274389 : ℝ) / 1000000000) := by
    have hnum : ((360 : ℝ) / 1000) - (((360 : ℝ) / 1000)) ^ 3 / 6 + (((360 : ℝ) / 1000)) ^ 5 / 120 < ((352274389 : ℝ) / 1000000000) := by norm_num
    linarith
  have hcLo : ((58493551 : ℝ) / 62500000) < cos (((360 : ℝ) / 1000)) := by
    have hnum : ((58493551 : ℝ) / 62500000) <
        1 - (((360 : ℝ) / 1000)) ^ 2 / 2 + (((360 : ℝ) / 1000)) ^ 4 / 24 - (((360 : ℝ) / 1000)) ^ 6 / 720 := by norm_num
    linarith
  have hcHi : cos (((360 : ℝ) / 1000)) < ((935899841 : ℝ) / 1000000000) := by
    have hnum : 1 - (((360 : ℝ) / 1000)) ^ 2 / 2 + (((360 : ℝ) / 1000)) ^ 4 / 24 < ((935899841 : ℝ) / 1000000000) := by norm_num
    linarith
  have hexp := exp_between (x := ((360 : ℝ) / 1000)) (n := 8) (lo := ((1433329399 : ℝ) / 1000000000)) (hi := ((179166177 : ℝ) / 125000000))
    ht0.le ht1 (by decide)
    (by norm_num [sum_range_succ, Nat.factorial])
    (by norm_num [sum_range_succ, Nat.factorial])
  have hph : ((187674601 : ℝ) / 500000000) < chordAmp (((360 : ℝ) / 1000)) ∧ chordAmp (((360 : ℝ) / 1000)) < ((600559 : ℝ) / 1600000) ∧
      ((27113277 : ℝ) / 31250000) < gammaSEqual (((360 : ℝ) / 1000)) ∧ gammaSEqual (((360 : ℝ) / 1000)) < ((433814081 : ℝ) / 500000000) := by
    exact phase_bounds ht0 ht1 hsLo hsHi hcLo hcHi hexp.1 hexp.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨ht0, ht1, by norm_num, by norm_num, hph.1, hph.2.1, by norm_num, hph.2.2.1, hph.2.2.2⟩


private lemma phaseAt_370 :
    phaseHolds (((370 : ℝ) / 1000)) ((2416573 : ℝ) / 6250000) ((386651889 : ℝ) / 1000000000) ((430002477 : ℝ) / 500000000) ((430004429 : ℝ) / 500000000) := by
  have ht0 : (0 : ℝ) < ((370 : ℝ) / 1000) := by norm_num
  have ht1 : ((370 : ℝ) / 1000) ≤ 1 := by norm_num
  obtain ⟨hs7, hs5, hc6, hc4⟩ := trigPoly_bounds ht0
  have hsLo : ((361615431 : ℝ) / 1000000000) < sin (((370 : ℝ) / 1000)) := by
    have hnum : ((361615431 : ℝ) / 1000000000) <
        ((370 : ℝ) / 1000) - (((370 : ℝ) / 1000)) ^ 3 / 6 + (((370 : ℝ) / 1000)) ^ 5 / 120 - (((370 : ℝ) / 1000)) ^ 7 / 5040 := by norm_num
    linarith
  have hsHi : sin (((370 : ℝ) / 1000)) < ((18080781 : ℝ) / 50000000) := by
    have hnum : ((370 : ℝ) / 1000) - (((370 : ℝ) / 1000)) ^ 3 / 6 + (((370 : ℝ) / 1000)) ^ 5 / 120 < ((18080781 : ℝ) / 50000000) := by norm_num
    linarith
  have hcLo : ((116540917 : ℝ) / 125000000) < cos (((370 : ℝ) / 1000)) := by
    have hnum : ((116540917 : ℝ) / 125000000) <
        1 - (((370 : ℝ) / 1000)) ^ 2 / 2 + (((370 : ℝ) / 1000)) ^ 4 / 24 - (((370 : ℝ) / 1000)) ^ 6 / 720 := by norm_num
    linarith
  have hcHi : cos (((370 : ℝ) / 1000)) < ((932330901 : ℝ) / 1000000000) := by
    have hnum : 1 - (((370 : ℝ) / 1000)) ^ 2 / 2 + (((370 : ℝ) / 1000)) ^ 4 / 24 < ((932330901 : ℝ) / 1000000000) := by norm_num
    linarith
  have hexp := exp_between (x := ((370 : ℝ) / 1000)) (n := 8) (lo := ((289546919 : ℝ) / 200000000)) (hi := ((180966827 : ℝ) / 125000000))
    ht0.le ht1 (by decide)
    (by norm_num [sum_range_succ, Nat.factorial])
    (by norm_num [sum_range_succ, Nat.factorial])
  have hph : ((2416573 : ℝ) / 6250000) < chordAmp (((370 : ℝ) / 1000)) ∧ chordAmp (((370 : ℝ) / 1000)) < ((386651889 : ℝ) / 1000000000) ∧
      ((430002477 : ℝ) / 500000000) < gammaSEqual (((370 : ℝ) / 1000)) ∧ gammaSEqual (((370 : ℝ) / 1000)) < ((430004429 : ℝ) / 500000000) := by
    exact phase_bounds ht0 ht1 hsLo hsHi hcLo hcHi hexp.1 hexp.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨ht0, ht1, by norm_num, by norm_num, hph.1, hph.2.1, by norm_num, hph.2.2.1, hph.2.2.2⟩


private lemma phaseAt_371 :
    phaseHolds (((371 : ℝ) / 1000)) ((387785781 : ℝ) / 1000000000) ((193892997 : ℝ) / 500000000) ((171846103 : ℝ) / 200000000) ((214808621 : ℝ) / 250000000) := by
  have ht0 : (0 : ℝ) < ((371 : ℝ) / 1000) := by norm_num
  have ht1 : ((371 : ℝ) / 1000) ≤ 1 := by norm_num
  obtain ⟨hs7, hs5, hc6, hc4⟩ := trigPoly_bounds ht0
  have hsLo : ((362547577 : ℝ) / 1000000000) < sin (((371 : ℝ) / 1000)) := by
    have hnum : ((362547577 : ℝ) / 1000000000) <
        ((371 : ℝ) / 1000) - (((371 : ℝ) / 1000)) ^ 3 / 6 + (((371 : ℝ) / 1000)) ^ 5 / 120 - (((371 : ℝ) / 1000)) ^ 7 / 5040 := by norm_num
    linarith
  have hsHi : sin (((371 : ℝ) / 1000)) < ((36254777 : ℝ) / 100000000) := by
    have hnum : ((371 : ℝ) / 1000) - (((371 : ℝ) / 1000)) ^ 3 / 6 + (((371 : ℝ) / 1000)) ^ 5 / 120 < ((36254777 : ℝ) / 100000000) := by norm_num
    linarith
  have hcLo : ((186393051 : ℝ) / 200000000) < cos (((371 : ℝ) / 1000)) := by
    have hnum : ((186393051 : ℝ) / 200000000) <
        1 - (((371 : ℝ) / 1000)) ^ 2 / 2 + (((371 : ℝ) / 1000)) ^ 4 / 24 - (((371 : ℝ) / 1000)) ^ 6 / 720 := by norm_num
    linarith
  have hcHi : cos (((371 : ℝ) / 1000)) < ((931968877 : ℝ) / 1000000000) := by
    have hnum : 1 - (((371 : ℝ) / 1000)) ^ 2 / 2 + (((371 : ℝ) / 1000)) ^ 4 / 24 < ((931968877 : ℝ) / 1000000000) := by norm_num
    linarith
  have hexp := exp_between (x := ((371 : ℝ) / 1000)) (n := 8) (lo := ((724591527 : ℝ) / 500000000)) (hi := ((57967323 : ℝ) / 40000000))
    ht0.le ht1 (by decide)
    (by norm_num [sum_range_succ, Nat.factorial])
    (by norm_num [sum_range_succ, Nat.factorial])
  have hph : ((387785781 : ℝ) / 1000000000) < chordAmp (((371 : ℝ) / 1000)) ∧ chordAmp (((371 : ℝ) / 1000)) < ((193892997 : ℝ) / 500000000) ∧
      ((171846103 : ℝ) / 200000000) < gammaSEqual (((371 : ℝ) / 1000)) ∧ gammaSEqual (((371 : ℝ) / 1000)) < ((214808621 : ℝ) / 250000000) := by
    exact phase_bounds ht0 ht1 hsLo hsHi hcLo hcHi hexp.1 hexp.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨ht0, ht1, by norm_num, by norm_num, hph.1, hph.2.1, by norm_num, hph.2.2.1, hph.2.2.2⟩


private lemma phaseAt_375 :
    phaseHolds (((375 : ℝ) / 1000)) ((196164639 : ℝ) / 500000000) ((98082377 : ℝ) / 250000000) ((428055027 : ℝ) / 500000000) ((171222859 : ℝ) / 200000000) := by
  have ht0 : (0 : ℝ) < ((375 : ℝ) / 1000) := by norm_num
  have ht1 : ((375 : ℝ) / 1000) ≤ 1 := by norm_num
  obtain ⟨hs7, hs5, hc6, hc4⟩ := trigPoly_bounds ht0
  have hsLo : ((22892033 : ℝ) / 62500000) < sin (((375 : ℝ) / 1000)) := by
    have hnum : ((22892033 : ℝ) / 62500000) <
        ((375 : ℝ) / 1000) - (((375 : ℝ) / 1000)) ^ 3 / 6 + (((375 : ℝ) / 1000)) ^ 5 / 120 - (((375 : ℝ) / 1000)) ^ 7 / 5040 := by norm_num
    linarith
  have hsHi : sin (((375 : ℝ) / 1000)) < ((11446023 : ℝ) / 31250000) := by
    have hnum : ((375 : ℝ) / 1000) - (((375 : ℝ) / 1000)) ^ 3 / 6 + (((375 : ℝ) / 1000)) ^ 5 / 120 < ((11446023 : ℝ) / 31250000) := by norm_num
    linarith
  have hcLo : ((232626903 : ℝ) / 250000000) < cos (((375 : ℝ) / 1000)) := by
    have hnum : ((232626903 : ℝ) / 250000000) <
        1 - (((375 : ℝ) / 1000)) ^ 2 / 2 + (((375 : ℝ) / 1000)) ^ 4 / 24 - (((375 : ℝ) / 1000)) ^ 6 / 720 := by norm_num
    linarith
  have hcHi : cos (((375 : ℝ) / 1000)) < ((37220459 : ℝ) / 40000000) := by
    have hnum : 1 - (((375 : ℝ) / 1000)) ^ 2 / 2 + (((375 : ℝ) / 1000)) ^ 4 / 24 < ((37220459 : ℝ) / 40000000) := by norm_num
    linarith
  have hexp := exp_between (x := ((375 : ℝ) / 1000)) (n := 8) (lo := ((1454991393 : ℝ) / 1000000000)) (hi := ((181873927 : ℝ) / 125000000))
    ht0.le ht1 (by decide)
    (by norm_num [sum_range_succ, Nat.factorial])
    (by norm_num [sum_range_succ, Nat.factorial])
  have hph : ((196164639 : ℝ) / 500000000) < chordAmp (((375 : ℝ) / 1000)) ∧ chordAmp (((375 : ℝ) / 1000)) < ((98082377 : ℝ) / 250000000) ∧
      ((428055027 : ℝ) / 500000000) < gammaSEqual (((375 : ℝ) / 1000)) ∧ gammaSEqual (((375 : ℝ) / 1000)) < ((171222859 : ℝ) / 200000000) := by
    exact phase_bounds ht0 ht1 hsLo hsHi hcLo hcHi hexp.1 hexp.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨ht0, ht1, by norm_num, by norm_num, hph.1, hph.2.1, by norm_num, hph.2.2.1, hph.2.2.2⟩


private lemma phaseAt_383 :
    phaseHolds (((383 : ℝ) / 1000)) ((401450669 : ℝ) / 1000000000) ((50181367 : ℝ) / 125000000) ((424879929 : ℝ) / 500000000) ((849764689 : ℝ) / 1000000000) := by
  have ht0 : (0 : ℝ) < ((383 : ℝ) / 1000) := by norm_num
  have ht1 : ((383 : ℝ) / 1000) ≤ 1 := by norm_num
  obtain ⟨hs7, hs5, hc6, hc4⟩ := trigPoly_bounds ht0
  have hsLo : ((373704789 : ℝ) / 1000000000) < sin (((383 : ℝ) / 1000)) := by
    have hnum : ((373704789 : ℝ) / 1000000000) <
        ((383 : ℝ) / 1000) - (((383 : ℝ) / 1000)) ^ 3 / 6 + (((383 : ℝ) / 1000)) ^ 5 / 120 - (((383 : ℝ) / 1000)) ^ 7 / 5040 := by norm_num
    linarith
  have hsHi : sin (((383 : ℝ) / 1000)) < ((37370503 : ℝ) / 100000000) := by
    have hnum : ((383 : ℝ) / 1000) - (((383 : ℝ) / 1000)) ^ 3 / 6 + (((383 : ℝ) / 1000)) ^ 5 / 120 < ((37370503 : ℝ) / 100000000) := by norm_num
    linarith
  have hcLo : ((185509537 : ℝ) / 200000000) < cos (((383 : ℝ) / 1000)) := by
    have hnum : ((185509537 : ℝ) / 200000000) <
        1 - (((383 : ℝ) / 1000)) ^ 2 / 2 + (((383 : ℝ) / 1000)) ^ 4 / 24 - (((383 : ℝ) / 1000)) ^ 6 / 720 := by norm_num
    linarith
  have hcHi : cos (((383 : ℝ) / 1000)) < ((92755207 : ℝ) / 100000000) := by
    have hnum : 1 - (((383 : ℝ) / 1000)) ^ 2 / 2 + (((383 : ℝ) / 1000)) ^ 4 / 24 < ((92755207 : ℝ) / 100000000) := by norm_num
    linarith
  have hexp := exp_between (x := ((383 : ℝ) / 1000)) (n := 8) (lo := ((293335601 : ℝ) / 200000000)) (hi := ((1466678031 : ℝ) / 1000000000))
    ht0.le ht1 (by decide)
    (by norm_num [sum_range_succ, Nat.factorial])
    (by norm_num [sum_range_succ, Nat.factorial])
  have hph : ((401450669 : ℝ) / 1000000000) < chordAmp (((383 : ℝ) / 1000)) ∧ chordAmp (((383 : ℝ) / 1000)) < ((50181367 : ℝ) / 125000000) ∧
      ((424879929 : ℝ) / 500000000) < gammaSEqual (((383 : ℝ) / 1000)) ∧ gammaSEqual (((383 : ℝ) / 1000)) < ((849764689 : ℝ) / 1000000000) := by
    exact phase_bounds ht0 ht1 hsLo hsHi hcLo hcHi hexp.1 hexp.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨ht0, ht1, by norm_num, by norm_num, hph.1, hph.2.1, by norm_num, hph.2.2.1, hph.2.2.2⟩


private lemma phaseAt_385 :
    phaseHolds (((385 : ℝ) / 1000)) ((403738263 : ℝ) / 1000000000) ((403738541 : ℝ) / 1000000000) ((33925979 : ℝ) / 40000000) ((169630893 : ℝ) / 200000000) := by
  have ht0 : (0 : ℝ) < ((385 : ℝ) / 1000) := by norm_num
  have ht1 : ((385 : ℝ) / 1000) ≤ 1 := by norm_num
  obtain ⟨hs7, hs5, hc6, hc4⟩ := trigPoly_bounds ht0
  have hsLo : ((11736223 : ℝ) / 31250000) < sin (((385 : ℝ) / 1000)) := by
    have hnum : ((11736223 : ℝ) / 31250000) <
        ((385 : ℝ) / 1000) - (((385 : ℝ) / 1000)) ^ 3 / 6 + (((385 : ℝ) / 1000)) ^ 5 / 120 - (((385 : ℝ) / 1000)) ^ 7 / 5040 := by norm_num
    linarith
  have hsHi : sin (((385 : ℝ) / 1000)) < ((187779693 : ℝ) / 500000000) := by
    have hnum : ((385 : ℝ) / 1000) - (((385 : ℝ) / 1000)) ^ 3 / 6 + (((385 : ℝ) / 1000)) ^ 5 / 120 < ((187779693 : ℝ) / 500000000) := by norm_num
    linarith
  have hcLo : ((46339921 : ℝ) / 50000000) < cos (((385 : ℝ) / 1000)) := by
    have hnum : ((46339921 : ℝ) / 50000000) <
        1 - (((385 : ℝ) / 1000)) ^ 2 / 2 + (((385 : ℝ) / 1000)) ^ 4 / 24 - (((385 : ℝ) / 1000)) ^ 6 / 720 := by norm_num
    linarith
  have hcHi : cos (((385 : ℝ) / 1000)) < ((1810162 : ℝ) / 1953125) := by
    have hnum : 1 - (((385 : ℝ) / 1000)) ^ 2 / 2 + (((385 : ℝ) / 1000)) ^ 4 / 24 < ((1810162 : ℝ) / 1953125) := by norm_num
    linarith
  have hexp := exp_between (x := ((385 : ℝ) / 1000)) (n := 8) (lo := ((293922859 : ℝ) / 200000000)) (hi := ((1469614323 : ℝ) / 1000000000))
    ht0.le ht1 (by decide)
    (by norm_num [sum_range_succ, Nat.factorial])
    (by norm_num [sum_range_succ, Nat.factorial])
  have hph : ((403738263 : ℝ) / 1000000000) < chordAmp (((385 : ℝ) / 1000)) ∧ chordAmp (((385 : ℝ) / 1000)) < ((403738541 : ℝ) / 1000000000) ∧
      ((33925979 : ℝ) / 40000000) < gammaSEqual (((385 : ℝ) / 1000)) ∧ gammaSEqual (((385 : ℝ) / 1000)) < ((169630893 : ℝ) / 200000000) := by
    exact phase_bounds ht0 ht1 hsLo hsHi hcLo hcHi hexp.1 hexp.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨ht0, ht1, by norm_num, by norm_num, hph.1, hph.2.1, by norm_num, hph.2.2.1, hph.2.2.2⟩


private lemma phaseAt_386 :
    phaseHolds (((386 : ℝ) / 1000)) ((101220789 : ℝ) / 250000000) ((404883439 : ℝ) / 1000000000) ((847340851 : ℝ) / 1000000000) ((423672961 : ℝ) / 500000000) := by
  have ht0 : (0 : ℝ) < ((386 : ℝ) / 1000) := by norm_num
  have ht1 : ((386 : ℝ) / 1000) ≤ 1 := by norm_num
  obtain ⟨hs7, hs5, hc6, hc4⟩ := trigPoly_bounds ht0
  have hsLo : ((188242873 : ℝ) / 500000000) < sin (((386 : ℝ) / 1000)) := by
    have hnum : ((188242873 : ℝ) / 500000000) <
        ((386 : ℝ) / 1000) - (((386 : ℝ) / 1000)) ^ 3 / 6 + (((386 : ℝ) / 1000)) ^ 5 / 120 - (((386 : ℝ) / 1000)) ^ 7 / 5040 := by norm_num
    linarith
  have hsHi : sin (((386 : ℝ) / 1000)) < ((376486001 : ℝ) / 1000000000) := by
    have hnum : ((386 : ℝ) / 1000) - (((386 : ℝ) / 1000)) ^ 3 / 6 + (((386 : ℝ) / 1000)) ^ 5 / 120 < ((376486001 : ℝ) / 1000000000) := by norm_num
    linarith
  have hcLo : ((926422397 : ℝ) / 1000000000) < cos (((386 : ℝ) / 1000)) := by
    have hnum : ((926422397 : ℝ) / 1000000000) <
        1 - (((386 : ℝ) / 1000)) ^ 2 / 2 + (((386 : ℝ) / 1000)) ^ 4 / 24 - (((386 : ℝ) / 1000)) ^ 6 / 720 := by norm_num
    linarith
  have hcHi : cos (((386 : ℝ) / 1000)) < ((926426993 : ℝ) / 1000000000) := by
    have hnum : 1 - (((386 : ℝ) / 1000)) ^ 2 / 2 + (((386 : ℝ) / 1000)) ^ 4 / 24 < ((926426993 : ℝ) / 1000000000) := by norm_num
    linarith
  have hexp := exp_between (x := ((386 : ℝ) / 1000)) (n := 8) (lo := ((367771161 : ℝ) / 250000000)) (hi := ((11492849 : ℝ) / 7812500))
    ht0.le ht1 (by decide)
    (by norm_num [sum_range_succ, Nat.factorial])
    (by norm_num [sum_range_succ, Nat.factorial])
  have hph : ((101220789 : ℝ) / 250000000) < chordAmp (((386 : ℝ) / 1000)) ∧ chordAmp (((386 : ℝ) / 1000)) < ((404883439 : ℝ) / 1000000000) ∧
      ((847340851 : ℝ) / 1000000000) < gammaSEqual (((386 : ℝ) / 1000)) ∧ gammaSEqual (((386 : ℝ) / 1000)) < ((423672961 : ℝ) / 500000000) := by
    exact phase_bounds ht0 ht1 hsLo hsHi hcLo hcHi hexp.1 hexp.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨ht0, ht1, by norm_num, by norm_num, hph.1, hph.2.1, by norm_num, hph.2.2.1, hph.2.2.2⟩


private lemma phaseAt_394 :
    phaseHolds (((394 : ℝ) / 1000)) ((207034417 : ℝ) / 500000000) ((10351729 : ℝ) / 25000000) ((210197319 : ℝ) / 250000000) ((840795033 : ℝ) / 1000000000) := by
  have ht0 : (0 : ℝ) < ((394 : ℝ) / 1000) := by norm_num
  have ht1 : ((394 : ℝ) / 1000) ≤ 1 := by norm_num
  obtain ⟨hs7, hs5, hc6, hc4⟩ := trigPoly_bounds ht0
  have hsLo : ((383884999 : ℝ) / 1000000000) < sin (((394 : ℝ) / 1000)) := by
    have hnum : ((383884999 : ℝ) / 1000000000) <
        ((394 : ℝ) / 1000) - (((394 : ℝ) / 1000)) ^ 3 / 6 + (((394 : ℝ) / 1000)) ^ 5 / 120 - (((394 : ℝ) / 1000)) ^ 7 / 5040 := by norm_num
    linarith
  have hsHi : sin (((394 : ℝ) / 1000)) < ((95971323 : ℝ) / 250000000) := by
    have hnum : ((394 : ℝ) / 1000) - (((394 : ℝ) / 1000)) ^ 3 / 6 + (((394 : ℝ) / 1000)) ^ 5 / 120 < ((95971323 : ℝ) / 250000000) := by norm_num
    linarith
  have hcLo : ((28855653 : ℝ) / 31250000) < cos (((394 : ℝ) / 1000)) := by
    have hnum : ((28855653 : ℝ) / 31250000) <
        1 - (((394 : ℝ) / 1000)) ^ 2 / 2 + (((394 : ℝ) / 1000)) ^ 4 / 24 - (((394 : ℝ) / 1000)) ^ 6 / 720 := by norm_num
    linarith
  have hcHi : cos (((394 : ℝ) / 1000)) < ((923386093 : ℝ) / 1000000000) := by
    have hnum : 1 - (((394 : ℝ) / 1000)) ^ 2 / 2 + (((394 : ℝ) / 1000)) ^ 4 / 24 < ((923386093 : ℝ) / 1000000000) := by norm_num
    linarith
  have hexp := exp_between (x := ((394 : ℝ) / 1000)) (n := 8) (lo := ((1482900517 : ℝ) / 1000000000)) (hi := ((29658011 : ℝ) / 20000000))
    ht0.le ht1 (by decide)
    (by norm_num [sum_range_succ, Nat.factorial])
    (by norm_num [sum_range_succ, Nat.factorial])
  have hph : ((207034417 : ℝ) / 500000000) < chordAmp (((394 : ℝ) / 1000)) ∧ chordAmp (((394 : ℝ) / 1000)) < ((10351729 : ℝ) / 25000000) ∧
      ((210197319 : ℝ) / 250000000) < gammaSEqual (((394 : ℝ) / 1000)) ∧ gammaSEqual (((394 : ℝ) / 1000)) < ((840795033 : ℝ) / 1000000000) := by
    exact phase_bounds ht0 ht1 hsLo hsHi hcLo hcHi hexp.1 hexp.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨ht0, ht1, by norm_num, by norm_num, hph.1, hph.2.1, by norm_num, hph.2.2.1, hph.2.2.2⟩


private lemma phaseAt_395 :
    phaseHolds (((395 : ℝ) / 1000)) ((207610193 : ℝ) / 500000000) ((207610359 : ℝ) / 500000000) ((52497499 : ℝ) / 62500000) ((104995729 : ℝ) / 125000000) := by
  have ht0 : (0 : ℝ) < ((395 : ℝ) / 1000) := by norm_num
  have ht1 : ((395 : ℝ) / 1000) ≤ 1 := by norm_num
  obtain ⟨hs7, hs5, hc6, hc4⟩ := trigPoly_bounds ht0
  have hsLo : ((96202047 : ℝ) / 250000000) < sin (((395 : ℝ) / 1000)) := by
    have hnum : ((96202047 : ℝ) / 250000000) <
        ((395 : ℝ) / 1000) - (((395 : ℝ) / 1000)) ^ 3 / 6 + (((395 : ℝ) / 1000)) ^ 5 / 120 - (((395 : ℝ) / 1000)) ^ 7 / 5040 := by norm_num
    linarith
  have hsHi : sin (((395 : ℝ) / 1000)) < ((192404243 : ℝ) / 500000000) := by
    have hnum : ((395 : ℝ) / 1000) - (((395 : ℝ) / 1000)) ^ 3 / 6 + (((395 : ℝ) / 1000)) ^ 5 / 120 < ((192404243 : ℝ) / 500000000) := by norm_num
    linarith
  have hcLo : ((922996549 : ℝ) / 1000000000) < cos (((395 : ℝ) / 1000)) := by
    have hnum : ((922996549 : ℝ) / 1000000000) <
        1 - (((395 : ℝ) / 1000)) ^ 2 / 2 + (((395 : ℝ) / 1000)) ^ 4 / 24 - (((395 : ℝ) / 1000)) ^ 6 / 720 := by norm_num
    linarith
  have hcHi : cos (((395 : ℝ) / 1000)) < ((461500913 : ℝ) / 500000000) := by
    have hnum : 1 - (((395 : ℝ) / 1000)) ^ 2 / 2 + (((395 : ℝ) / 1000)) ^ 4 / 24 < ((461500913 : ℝ) / 500000000) := by norm_num
    linarith
  have hexp := exp_between (x := ((395 : ℝ) / 1000)) (n := 8) (lo := ((1484384159 : ℝ) / 1000000000)) (hi := ((1484384193 : ℝ) / 1000000000))
    ht0.le ht1 (by decide)
    (by norm_num [sum_range_succ, Nat.factorial])
    (by norm_num [sum_range_succ, Nat.factorial])
  have hph : ((207610193 : ℝ) / 500000000) < chordAmp (((395 : ℝ) / 1000)) ∧ chordAmp (((395 : ℝ) / 1000)) < ((207610359 : ℝ) / 500000000) ∧
      ((52497499 : ℝ) / 62500000) < gammaSEqual (((395 : ℝ) / 1000)) ∧ gammaSEqual (((395 : ℝ) / 1000)) < ((104995729 : ℝ) / 125000000) := by
    exact phase_bounds ht0 ht1 hsLo hsHi hcLo hcHi hexp.1 hexp.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨ht0, ht1, by norm_num, by norm_num, hph.1, hph.2.1, by norm_num, hph.2.2.1, hph.2.2.2⟩


private lemma phaseAt_404 :
    phaseHolds (((404 : ℝ) / 1000)) ((17024729 : ℝ) / 40000000) ((85123723 : ℝ) / 200000000) ((832392497 : ℝ) / 1000000000) ((416199611 : ℝ) / 500000000) := by
  have ht0 : (0 : ℝ) < ((404 : ℝ) / 1000) := by norm_num
  have ht1 : ((404 : ℝ) / 1000) ≤ 1 := by norm_num
  obtain ⟨hs7, hs5, hc6, hc4⟩ := trigPoly_bounds ht0
  have hsLo : ((19654973 : ℝ) / 50000000) < sin (((404 : ℝ) / 1000)) := by
    have hnum : ((19654973 : ℝ) / 50000000) <
        ((404 : ℝ) / 1000) - (((404 : ℝ) / 1000)) ^ 3 / 6 + (((404 : ℝ) / 1000)) ^ 5 / 120 - (((404 : ℝ) / 1000)) ^ 7 / 5040 := by norm_num
    linarith
  have hsHi : sin (((404 : ℝ) / 1000)) < ((393099809 : ℝ) / 1000000000) := by
    have hnum : ((404 : ℝ) / 1000) - (((404 : ℝ) / 1000)) ^ 3 / 6 + (((404 : ℝ) / 1000)) ^ 5 / 120 < ((393099809 : ℝ) / 1000000000) := by norm_num
    linarith
  have hcLo : ((459747969 : ℝ) / 500000000) < cos (((404 : ℝ) / 1000)) := by
    have hnum : ((459747969 : ℝ) / 500000000) <
        1 - (((404 : ℝ) / 1000)) ^ 2 / 2 + (((404 : ℝ) / 1000)) ^ 4 / 24 - (((404 : ℝ) / 1000)) ^ 6 / 720 := by norm_num
    linarith
  have hcHi : cos (((404 : ℝ) / 1000)) < ((459750989 : ℝ) / 500000000) := by
    have hnum : 1 - (((404 : ℝ) / 1000)) ^ 2 / 2 + (((404 : ℝ) / 1000)) ^ 4 / 24 < ((459750989 : ℝ) / 500000000) := by norm_num
    linarith
  have hexp := exp_between (x := ((404 : ℝ) / 1000)) (n := 8) (lo := ((374450977 : ℝ) / 250000000)) (hi := ((1497803949 : ℝ) / 1000000000))
    ht0.le ht1 (by decide)
    (by norm_num [sum_range_succ, Nat.factorial])
    (by norm_num [sum_range_succ, Nat.factorial])
  have hph : ((17024729 : ℝ) / 40000000) < chordAmp (((404 : ℝ) / 1000)) ∧ chordAmp (((404 : ℝ) / 1000)) < ((85123723 : ℝ) / 200000000) ∧
      ((832392497 : ℝ) / 1000000000) < gammaSEqual (((404 : ℝ) / 1000)) ∧ gammaSEqual (((404 : ℝ) / 1000)) < ((416199611 : ℝ) / 500000000) := by
    exact phase_bounds ht0 ht1 hsLo hsHi hcLo hcHi hexp.1 hexp.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨ht0, ht1, by norm_num, by norm_num, hph.1, hph.2.1, by norm_num, hph.2.2.1, hph.2.2.2⟩


private lemma phaseAt_405 :
    phaseHolds (((405 : ℝ) / 1000)) ((85355467 : ℝ) / 200000000) ((426777733 : ℝ) / 1000000000) ((831540099 : ℝ) / 1000000000) ((831546927 : ℝ) / 1000000000) := by
  have ht0 : (0 : ℝ) < ((405 : ℝ) / 1000) := by norm_num
  have ht1 : ((405 : ℝ) / 1000) ≤ 1 := by norm_num
  obtain ⟨hs7, hs5, hc6, hc4⟩ := trigPoly_bounds ht0
  have hsLo : ((394018759 : ℝ) / 1000000000) < sin (((405 : ℝ) / 1000)) := by
    have hnum : ((394018759 : ℝ) / 1000000000) <
        ((405 : ℝ) / 1000) - (((405 : ℝ) / 1000)) ^ 3 / 6 + (((405 : ℝ) / 1000)) ^ 5 / 120 - (((405 : ℝ) / 1000)) ^ 7 / 5040 := by norm_num
    linarith
  have hsHi : sin (((405 : ℝ) / 1000)) < ((78803823 : ℝ) / 200000000) := by
    have hnum : ((405 : ℝ) / 1000) - (((405 : ℝ) / 1000)) ^ 3 / 6 + (((405 : ℝ) / 1000)) ^ 5 / 120 < ((78803823 : ℝ) / 200000000) := by norm_num
    linarith
  have hcLo : ((919102379 : ℝ) / 1000000000) < cos (((405 : ℝ) / 1000)) := by
    have hnum : ((919102379 : ℝ) / 1000000000) <
        1 - (((405 : ℝ) / 1000)) ^ 2 / 2 + (((405 : ℝ) / 1000)) ^ 4 / 24 - (((405 : ℝ) / 1000)) ^ 6 / 720 := by norm_num
    linarith
  have hcHi : cos (((405 : ℝ) / 1000)) < ((919108509 : ℝ) / 1000000000) := by
    have hnum : 1 - (((405 : ℝ) / 1000)) ^ 2 / 2 + (((405 : ℝ) / 1000)) ^ 4 / 24 < ((919108509 : ℝ) / 1000000000) := by norm_num
    linarith
  have hexp := exp_between (x := ((405 : ℝ) / 1000)) (n := 8) (lo := ((1499302461 : ℝ) / 1000000000)) (hi := ((749651251 : ℝ) / 500000000))
    ht0.le ht1 (by decide)
    (by norm_num [sum_range_succ, Nat.factorial])
    (by norm_num [sum_range_succ, Nat.factorial])
  have hph : ((85355467 : ℝ) / 200000000) < chordAmp (((405 : ℝ) / 1000)) ∧ chordAmp (((405 : ℝ) / 1000)) < ((426777733 : ℝ) / 1000000000) ∧
      ((831540099 : ℝ) / 1000000000) < gammaSEqual (((405 : ℝ) / 1000)) ∧ gammaSEqual (((405 : ℝ) / 1000)) < ((831546927 : ℝ) / 1000000000) := by
    exact phase_bounds ht0 ht1 hsLo hsHi hcLo hcHi hexp.1 hexp.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨ht0, ht1, by norm_num, by norm_num, hph.1, hph.2.1, by norm_num, hph.2.2.1, hph.2.2.2⟩


private lemma phaseAt_415 :
    phaseHolds (((415 : ℝ) / 1000)) ((438410781 : ℝ) / 1000000000) ((87682251 : ℝ) / 200000000) ((411444153 : ℝ) / 500000000) ((658317 : ℝ) / 800000) := by
  have ht0 : (0 : ℝ) < ((415 : ℝ) / 1000) := by norm_num
  have ht1 : ((415 : ℝ) / 1000) ≤ 1 := by norm_num
  obtain ⟨hs7, hs5, hc6, hc4⟩ := trigPoly_bounds ht0
  have hsLo : ((403189929 : ℝ) / 1000000000) < sin (((415 : ℝ) / 1000)) := by
    have hnum : ((403189929 : ℝ) / 1000000000) <
        ((415 : ℝ) / 1000) - (((415 : ℝ) / 1000)) ^ 3 / 6 + (((415 : ℝ) / 1000)) ^ 5 / 120 - (((415 : ℝ) / 1000)) ^ 7 / 5040 := by norm_num
    linarith
  have hsHi : sin (((415 : ℝ) / 1000)) < ((403190351 : ℝ) / 1000000000) := by
    have hnum : ((415 : ℝ) / 1000) - (((415 : ℝ) / 1000)) ^ 3 / 6 + (((415 : ℝ) / 1000)) ^ 5 / 120 < ((403190351 : ℝ) / 1000000000) := by norm_num
    linarith
  have hcLo : ((457558149 : ℝ) / 500000000) < cos (((415 : ℝ) / 1000)) := by
    have hnum : ((457558149 : ℝ) / 500000000) <
        1 - (((415 : ℝ) / 1000)) ^ 2 / 2 + (((415 : ℝ) / 1000)) ^ 4 / 24 - (((415 : ℝ) / 1000)) ^ 6 / 720 := by norm_num
    linarith
  have hcHi : cos (((415 : ℝ) / 1000)) < ((457561697 : ℝ) / 500000000) := by
    have hnum : 1 - (((415 : ℝ) / 1000)) ^ 2 / 2 + (((415 : ℝ) / 1000)) ^ 4 / 24 < ((457561697 : ℝ) / 500000000) := by norm_num
    linarith
  have hexp := exp_between (x := ((415 : ℝ) / 1000)) (n := 8) (lo := ((1514370693 : ℝ) / 1000000000)) (hi := ((1514370743 : ℝ) / 1000000000))
    ht0.le ht1 (by decide)
    (by norm_num [sum_range_succ, Nat.factorial])
    (by norm_num [sum_range_succ, Nat.factorial])
  have hph : ((438410781 : ℝ) / 1000000000) < chordAmp (((415 : ℝ) / 1000)) ∧ chordAmp (((415 : ℝ) / 1000)) < ((87682251 : ℝ) / 200000000) ∧
      ((411444153 : ℝ) / 500000000) < gammaSEqual (((415 : ℝ) / 1000)) ∧ gammaSEqual (((415 : ℝ) / 1000)) < ((658317 : ℝ) / 800000) := by
    exact phase_bounds ht0 ht1 hsLo hsHi hcLo hcHi hexp.1 hexp.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨ht0, ht1, by norm_num, by norm_num, hph.1, hph.2.1, by norm_num, hph.2.2.1, hph.2.2.2⟩


private lemma phaseAt_420 :
    phaseHolds (((420 : ℝ) / 1000)) ((111064177 : ℝ) / 250000000) ((17770289 : ℝ) / 40000000) ((409237481 : ℝ) / 500000000) ((818483521 : ℝ) / 1000000000) := by
  have ht0 : (0 : ℝ) < ((420 : ℝ) / 1000) := by norm_num
  have ht1 : ((420 : ℝ) / 1000) ≤ 1 := by norm_num
  obtain ⟨hs7, hs5, hc6, hc4⟩ := trigPoly_bounds ht0
  have hsLo : ((407760451 : ℝ) / 1000000000) < sin (((420 : ℝ) / 1000)) := by
    have hnum : ((407760451 : ℝ) / 1000000000) <
        ((420 : ℝ) / 1000) - (((420 : ℝ) / 1000)) ^ 3 / 6 + (((420 : ℝ) / 1000)) ^ 5 / 120 - (((420 : ℝ) / 1000)) ^ 7 / 5040 := by norm_num
    linarith
  have hsHi : sin (((420 : ℝ) / 1000)) < ((40776091 : ℝ) / 100000000) := by
    have hnum : ((420 : ℝ) / 1000) - (((420 : ℝ) / 1000)) ^ 3 / 6 + (((420 : ℝ) / 1000)) ^ 5 / 120 < ((40776091 : ℝ) / 100000000) := by norm_num
    linarith
  have hcLo : ((228272229 : ℝ) / 250000000) < cos (((420 : ℝ) / 1000)) := by
    have hnum : ((228272229 : ℝ) / 250000000) <
        1 - (((420 : ℝ) / 1000)) ^ 2 / 2 + (((420 : ℝ) / 1000)) ^ 4 / 24 - (((420 : ℝ) / 1000)) ^ 6 / 720 := by norm_num
    linarith
  have hcHi : cos (((420 : ℝ) / 1000)) < ((913096541 : ℝ) / 1000000000) := by
    have hnum : 1 - (((420 : ℝ) / 1000)) ^ 2 / 2 + (((420 : ℝ) / 1000)) ^ 4 / 24 < ((913096541 : ℝ) / 1000000000) := by norm_num
    linarith
  have hexp := exp_between (x := ((420 : ℝ) / 1000)) (n := 8) (lo := ((1521961503 : ℝ) / 1000000000)) (hi := ((760980779 : ℝ) / 500000000))
    ht0.le ht1 (by decide)
    (by norm_num [sum_range_succ, Nat.factorial])
    (by norm_num [sum_range_succ, Nat.factorial])
  have hph : ((111064177 : ℝ) / 250000000) < chordAmp (((420 : ℝ) / 1000)) ∧ chordAmp (((420 : ℝ) / 1000)) < ((17770289 : ℝ) / 40000000) ∧
      ((409237481 : ℝ) / 500000000) < gammaSEqual (((420 : ℝ) / 1000)) ∧ gammaSEqual (((420 : ℝ) / 1000)) < ((818483521 : ℝ) / 1000000000) := by
    exact phase_bounds ht0 ht1 hsLo hsHi hcLo hcHi hexp.1 hexp.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨ht0, ht1, by norm_num, by norm_num, hph.1, hph.2.1, by norm_num, hph.2.2.1, hph.2.2.2⟩


private lemma phaseAt_421 :
    phaseHolds (((421 : ℝ) / 1000)) ((13919633 : ℝ) / 31250000) ((445428781 : ℝ) / 1000000000) ((102198159 : ℝ) / 125000000) ((817593959 : ℝ) / 1000000000) := by
  have ht0 : (0 : ℝ) < ((421 : ℝ) / 1000) := by norm_num
  have ht1 : ((421 : ℝ) / 1000) ≤ 1 := by norm_num
  obtain ⟨hs7, hs5, hc6, hc4⟩ := trigPoly_bounds ht0
  have hsLo : ((51084167 : ℝ) / 125000000) < sin (((421 : ℝ) / 1000)) := by
    have hnum : ((51084167 : ℝ) / 125000000) <
        ((421 : ℝ) / 1000) - (((421 : ℝ) / 1000)) ^ 3 / 6 + (((421 : ℝ) / 1000)) ^ 5 / 120 - (((421 : ℝ) / 1000)) ^ 7 / 5040 := by norm_num
    linarith
  have hsHi : sin (((421 : ℝ) / 1000)) < ((204336901 : ℝ) / 500000000) := by
    have hnum : ((421 : ℝ) / 1000) - (((421 : ℝ) / 1000)) ^ 3 / 6 + (((421 : ℝ) / 1000)) ^ 5 / 120 < ((204336901 : ℝ) / 500000000) := by norm_num
    linarith
  have hcLo : ((456340349 : ℝ) / 500000000) < cos (((421 : ℝ) / 1000)) := by
    have hnum : ((456340349 : ℝ) / 500000000) <
        1 - (((421 : ℝ) / 1000)) ^ 2 / 2 + (((421 : ℝ) / 1000)) ^ 4 / 24 - (((421 : ℝ) / 1000)) ^ 6 / 720 := by norm_num
    linarith
  have hcHi : cos (((421 : ℝ) / 1000)) < ((912688433 : ℝ) / 1000000000) := by
    have hnum : 1 - (((421 : ℝ) / 1000)) ^ 2 / 2 + (((421 : ℝ) / 1000)) ^ 4 / 24 < ((912688433 : ℝ) / 1000000000) := by norm_num
    linarith
  have hexp := exp_between (x := ((421 : ℝ) / 1000)) (n := 8) (lo := ((60939369 : ℝ) / 40000000)) (hi := ((1523484281 : ℝ) / 1000000000))
    ht0.le ht1 (by decide)
    (by norm_num [sum_range_succ, Nat.factorial])
    (by norm_num [sum_range_succ, Nat.factorial])
  have hph : ((13919633 : ℝ) / 31250000) < chordAmp (((421 : ℝ) / 1000)) ∧ chordAmp (((421 : ℝ) / 1000)) < ((445428781 : ℝ) / 1000000000) ∧
      ((102198159 : ℝ) / 125000000) < gammaSEqual (((421 : ℝ) / 1000)) ∧ gammaSEqual (((421 : ℝ) / 1000)) < ((817593959 : ℝ) / 1000000000) := by
    exact phase_bounds ht0 ht1 hsLo hsHi hcLo hcHi hexp.1 hexp.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨ht0, ht1, by norm_num, by norm_num, hph.1, hph.2.1, by norm_num, hph.2.2.1, hph.2.2.2⟩


private lemma phaseAt_438 :
    phaseHolds (((438 : ℝ) / 1000)) ((465466983 : ℝ) / 1000000000) ((465467681 : ℝ) / 1000000000) ((802100617 : ℝ) / 1000000000) ((200527933 : ℝ) / 250000000) := by
  have ht0 : (0 : ℝ) < ((438 : ℝ) / 1000) := by norm_num
  have ht1 : ((438 : ℝ) / 1000) ≤ 1 := by norm_num
  obtain ⟨hs7, hs5, hc6, hc4⟩ := trigPoly_bounds ht0
  have hsLo : ((424129109 : ℝ) / 1000000000) < sin (((438 : ℝ) / 1000)) := by
    have hnum : ((424129109 : ℝ) / 1000000000) <
        ((438 : ℝ) / 1000) - (((438 : ℝ) / 1000)) ^ 3 / 6 + (((438 : ℝ) / 1000)) ^ 5 / 120 - (((438 : ℝ) / 1000)) ^ 7 / 5040 := by norm_num
    linarith
  have hsHi : sin (((438 : ℝ) / 1000)) < ((106032431 : ℝ) / 250000000) := by
    have hnum : ((438 : ℝ) / 1000) - (((438 : ℝ) / 1000)) ^ 3 / 6 + (((438 : ℝ) / 1000)) ^ 5 / 120 < ((106032431 : ℝ) / 250000000) := by norm_num
    linarith
  have hcLo : ((452800849 : ℝ) / 500000000) < cos (((438 : ℝ) / 1000)) := by
    have hnum : ((452800849 : ℝ) / 500000000) <
        1 - (((438 : ℝ) / 1000)) ^ 2 / 2 + (((438 : ℝ) / 1000)) ^ 4 / 24 - (((438 : ℝ) / 1000)) ^ 6 / 720 := by norm_num
    linarith
  have hcHi : cos (((438 : ℝ) / 1000)) < ((452805753 : ℝ) / 500000000) := by
    have hnum : 1 - (((438 : ℝ) / 1000)) ^ 2 / 2 + (((438 : ℝ) / 1000)) ^ 4 / 24 < ((452805753 : ℝ) / 500000000) := by norm_num
    linarith
  have hexp := exp_between (x := ((438 : ℝ) / 1000)) (n := 8) (lo := ((774802417 : ℝ) / 500000000)) (hi := ((154960491 : ℝ) / 100000000))
    ht0.le ht1 (by decide)
    (by norm_num [sum_range_succ, Nat.factorial])
    (by norm_num [sum_range_succ, Nat.factorial])
  have hph : ((465466983 : ℝ) / 1000000000) < chordAmp (((438 : ℝ) / 1000)) ∧ chordAmp (((438 : ℝ) / 1000)) < ((465467681 : ℝ) / 1000000000) ∧
      ((802100617 : ℝ) / 1000000000) < gammaSEqual (((438 : ℝ) / 1000)) ∧ gammaSEqual (((438 : ℝ) / 1000)) < ((200527933 : ℝ) / 250000000) := by
    exact phase_bounds ht0 ht1 hsLo hsHi hcLo hcHi hexp.1 hexp.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨ht0, ht1, by norm_num, by norm_num, hph.1, hph.2.1, by norm_num, hph.2.2.1, hph.2.2.2⟩


private lemma phaseAt_445 :
    phaseHolds (((445 : ℝ) / 1000)) ((473786559 : ℝ) / 1000000000) ((473787343 : ℝ) / 1000000000) ((397762921 : ℝ) / 500000000) ((12430283 : ℝ) / 15625000) := by
  have ht0 : (0 : ℝ) < ((445 : ℝ) / 1000) := by norm_num
  have ht1 : ((445 : ℝ) / 1000) ≤ 1 := by norm_num
  obtain ⟨hs7, hs5, hc6, hc4⟩ := trigPoly_bounds ht0
  have hsLo : ((215228939 : ℝ) / 500000000) < sin (((445 : ℝ) / 1000)) := by
    have hnum : ((215228939 : ℝ) / 500000000) <
        ((445 : ℝ) / 1000) - (((445 : ℝ) / 1000)) ^ 3 / 6 + (((445 : ℝ) / 1000)) ^ 5 / 120 - (((445 : ℝ) / 1000)) ^ 7 / 5040 := by norm_num
    linarith
  have hsHi : sin (((445 : ℝ) / 1000)) < ((86091713 : ℝ) / 200000000) := by
    have hnum : ((445 : ℝ) / 1000) - (((445 : ℝ) / 1000)) ^ 3 / 6 + (((445 : ℝ) / 1000)) ^ 5 / 120 < ((86091713 : ℝ) / 200000000) := by norm_num
    linarith
  have hcLo : ((902610627 : ℝ) / 1000000000) < cos (((445 : ℝ) / 1000)) := by
    have hnum : ((902610627 : ℝ) / 1000000000) <
        1 - (((445 : ℝ) / 1000)) ^ 2 / 2 + (((445 : ℝ) / 1000)) ^ 4 / 24 - (((445 : ℝ) / 1000)) ^ 6 / 720 := by norm_num
    linarith
  have hcHi : cos (((445 : ℝ) / 1000)) < ((902621413 : ℝ) / 1000000000) := by
    have hnum : 1 - (((445 : ℝ) / 1000)) ^ 2 / 2 + (((445 : ℝ) / 1000)) ^ 4 / 24 < ((902621413 : ℝ) / 1000000000) := by norm_num
    linarith
  have hexp := exp_between (x := ((445 : ℝ) / 1000)) (n := 8) (lo := ((12191329 : ℝ) / 7812500)) (hi := ((1560490199 : ℝ) / 1000000000))
    ht0.le ht1 (by decide)
    (by norm_num [sum_range_succ, Nat.factorial])
    (by norm_num [sum_range_succ, Nat.factorial])
  have hph : ((473786559 : ℝ) / 1000000000) < chordAmp (((445 : ℝ) / 1000)) ∧ chordAmp (((445 : ℝ) / 1000)) < ((473787343 : ℝ) / 1000000000) ∧
      ((397762921 : ℝ) / 500000000) < gammaSEqual (((445 : ℝ) / 1000)) ∧ gammaSEqual (((445 : ℝ) / 1000)) < ((12430283 : ℝ) / 15625000) := by
    exact phase_bounds ht0 ht1 hsLo hsHi hcLo hcHi hexp.1 hexp.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨ht0, ht1, by norm_num, by norm_num, hph.1, hph.2.1, by norm_num, hph.2.2.1, hph.2.2.2⟩


private lemma phaseAt_454 :
    phaseHolds (((454 : ℝ) / 1000)) ((484543 : ℝ) / 1000000) ((96908781 : ℝ) / 200000000) ((196725227 : ℝ) / 250000000) ((393457407 : ℝ) / 500000000) := by
  have ht0 : (0 : ℝ) < ((454 : ℝ) / 1000) := by norm_num
  have ht1 : ((454 : ℝ) / 1000) ≤ 1 := by norm_num
  obtain ⟨hs7, hs5, hc6, hc4⟩ := trigPoly_bounds ht0
  have hsLo : ((43856383 : ℝ) / 100000000) < sin (((454 : ℝ) / 1000)) := by
    have hnum : ((43856383 : ℝ) / 100000000) <
        ((454 : ℝ) / 1000) - (((454 : ℝ) / 1000)) ^ 3 / 6 + (((454 : ℝ) / 1000)) ^ 5 / 120 - (((454 : ℝ) / 1000)) ^ 7 / 5040 := by norm_num
    linarith
  have hsHi : sin (((454 : ℝ) / 1000)) < ((21928231 : ℝ) / 50000000) := by
    have hnum : ((454 : ℝ) / 1000) - (((454 : ℝ) / 1000)) ^ 3 / 6 + (((454 : ℝ) / 1000)) ^ 5 / 120 < ((21928231 : ℝ) / 50000000) := by norm_num
    linarith
  have hcLo : ((224674999 : ℝ) / 250000000) < cos (((454 : ℝ) / 1000)) := by
    have hnum : ((224674999 : ℝ) / 250000000) <
        1 - (((454 : ℝ) / 1000)) ^ 2 / 2 + (((454 : ℝ) / 1000)) ^ 4 / 24 - (((454 : ℝ) / 1000)) ^ 6 / 720 := by norm_num
    linarith
  have hcHi : cos (((454 : ℝ) / 1000)) < ((898712159 : ℝ) / 1000000000) := by
    have hnum : 1 - (((454 : ℝ) / 1000)) ^ 2 / 2 + (((454 : ℝ) / 1000)) ^ 4 / 24 < ((898712159 : ℝ) / 1000000000) := by norm_num
    linarith
  have hexp := exp_between (x := ((454 : ℝ) / 1000)) (n := 8) (lo := ((1574597899 : ℝ) / 1000000000)) (hi := ((1574598001 : ℝ) / 1000000000))
    ht0.le ht1 (by decide)
    (by norm_num [sum_range_succ, Nat.factorial])
    (by norm_num [sum_range_succ, Nat.factorial])
  have hph : ((484543 : ℝ) / 1000000) < chordAmp (((454 : ℝ) / 1000)) ∧ chordAmp (((454 : ℝ) / 1000)) < ((96908781 : ℝ) / 200000000) ∧
      ((196725227 : ℝ) / 250000000) < gammaSEqual (((454 : ℝ) / 1000)) ∧ gammaSEqual (((454 : ℝ) / 1000)) < ((393457407 : ℝ) / 500000000) := by
    exact phase_bounds ht0 ht1 hsLo hsHi hcLo hcHi hexp.1 hexp.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨ht0, ht1, by norm_num, by norm_num, hph.1, hph.2.1, by norm_num, hph.2.2.1, hph.2.2.2⟩


private lemma phaseAt_455 :
    phaseHolds (((455 : ℝ) / 1000)) ((485742361 : ℝ) / 1000000000) ((485743281 : ℝ) / 1000000000) ((392965307 : ℝ) / 500000000) ((785944713 : ℝ) / 1000000000) := by
  have ht0 : (0 : ℝ) < ((455 : ℝ) / 1000) := by norm_num
  have ht1 : ((455 : ℝ) / 1000) ≤ 1 := by norm_num
  obtain ⟨hs7, hs5, hc6, hc4⟩ := trigPoly_bounds ht0
  have hsLo : ((439462311 : ℝ) / 1000000000) < sin (((455 : ℝ) / 1000)) := by
    have hnum : ((439462311 : ℝ) / 1000000000) <
        ((455 : ℝ) / 1000) - (((455 : ℝ) / 1000)) ^ 3 / 6 + (((455 : ℝ) / 1000)) ^ 5 / 120 - (((455 : ℝ) / 1000)) ^ 7 / 5040 := by norm_num
    linarith
  have hsHi : sin (((455 : ℝ) / 1000)) < ((439463113 : ℝ) / 1000000000) := by
    have hnum : ((455 : ℝ) / 1000) - (((455 : ℝ) / 1000)) ^ 3 / 6 + (((455 : ℝ) / 1000)) ^ 5 / 120 < ((439463113 : ℝ) / 1000000000) := by norm_num
    linarith
  have hcLo : ((449130491 : ℝ) / 500000000) < cos (((455 : ℝ) / 1000)) := by
    have hnum : ((449130491 : ℝ) / 500000000) <
        1 - (((455 : ℝ) / 1000)) ^ 2 / 2 + (((455 : ℝ) / 1000)) ^ 4 / 24 - (((455 : ℝ) / 1000)) ^ 6 / 720 := by norm_num
    linarith
  have hcHi : cos (((455 : ℝ) / 1000)) < ((898273307 : ℝ) / 1000000000) := by
    have hnum : 1 - (((455 : ℝ) / 1000)) ^ 2 / 2 + (((455 : ℝ) / 1000)) ^ 4 / 24 < ((898273307 : ℝ) / 1000000000) := by norm_num
    linarith
  have hexp := exp_between (x := ((455 : ℝ) / 1000)) (n := 8) (lo := ((1576173283 : ℝ) / 1000000000)) (hi := ((1576173387 : ℝ) / 1000000000))
    ht0.le ht1 (by decide)
    (by norm_num [sum_range_succ, Nat.factorial])
    (by norm_num [sum_range_succ, Nat.factorial])
  have hph : ((485742361 : ℝ) / 1000000000) < chordAmp (((455 : ℝ) / 1000)) ∧ chordAmp (((455 : ℝ) / 1000)) < ((485743281 : ℝ) / 1000000000) ∧
      ((392965307 : ℝ) / 500000000) < gammaSEqual (((455 : ℝ) / 1000)) ∧ gammaSEqual (((455 : ℝ) / 1000)) < ((785944713 : ℝ) / 1000000000) := by
    exact phase_bounds ht0 ht1 hsLo hsHi hcLo hcHi hexp.1 hexp.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨ht0, ht1, by norm_num, by norm_num, hph.1, hph.2.1, by norm_num, hph.2.2.1, hph.2.2.2⟩


private lemma phaseAt_485 :
    phaseHolds (((485 : ℝ) / 1000)) ((65265441 : ℝ) / 125000000) ((130531247 : ℝ) / 250000000) ((75569823 : ℝ) / 100000000) ((755719269 : ℝ) / 1000000000) := by
  have ht0 : (0 : ℝ) < ((485 : ℝ) / 1000) := by norm_num
  have ht1 : ((485 : ℝ) / 1000) ≤ 1 := by norm_num
  obtain ⟨hs7, hs5, hc6, hc4⟩ := trigPoly_bounds ht0
  have hsLo : ((93241671 : ℝ) / 200000000) < sin (((485 : ℝ) / 1000)) := by
    have hnum : ((93241671 : ℝ) / 200000000) <
        ((485 : ℝ) / 1000) - (((485 : ℝ) / 1000)) ^ 3 / 6 + (((485 : ℝ) / 1000)) ^ 5 / 120 - (((485 : ℝ) / 1000)) ^ 7 / 5040 := by norm_num
    linarith
  have hsHi : sin (((485 : ℝ) / 1000)) < ((58276201 : ℝ) / 125000000) := by
    have hnum : ((485 : ℝ) / 1000) - (((485 : ℝ) / 1000)) ^ 3 / 6 + (((485 : ℝ) / 1000)) ^ 5 / 120 < ((58276201 : ℝ) / 125000000) := by norm_num
    linarith
  have hcLo : ((884674873 : ℝ) / 1000000000) < cos (((485 : ℝ) / 1000)) := by
    have hnum : ((884674873 : ℝ) / 1000000000) <
        1 - (((485 : ℝ) / 1000)) ^ 2 / 2 + (((485 : ℝ) / 1000)) ^ 4 / 24 - (((485 : ℝ) / 1000)) ^ 6 / 720 := by norm_num
    linarith
  have hcHi : cos (((485 : ℝ) / 1000)) < ((884692951 : ℝ) / 1000000000) := by
    have hnum : 1 - (((485 : ℝ) / 1000)) ^ 2 / 2 + (((485 : ℝ) / 1000)) ^ 4 / 24 < ((884692951 : ℝ) / 1000000000) := by norm_num
    linarith
  have hexp := exp_between (x := ((485 : ℝ) / 1000)) (n := 8) (lo := ((1624174843 : ℝ) / 1000000000)) (hi := ((324835003 : ℝ) / 200000000))
    ht0.le ht1 (by decide)
    (by norm_num [sum_range_succ, Nat.factorial])
    (by norm_num [sum_range_succ, Nat.factorial])
  have hph : ((65265441 : ℝ) / 125000000) < chordAmp (((485 : ℝ) / 1000)) ∧ chordAmp (((485 : ℝ) / 1000)) < ((130531247 : ℝ) / 250000000) ∧
      ((75569823 : ℝ) / 100000000) < gammaSEqual (((485 : ℝ) / 1000)) ∧ gammaSEqual (((485 : ℝ) / 1000)) < ((755719269 : ℝ) / 1000000000) := by
    exact phase_bounds ht0 ht1 hsLo hsHi hcLo hcHi hexp.1 hexp.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨ht0, ht1, by norm_num, by norm_num, hph.1, hph.2.1, by norm_num, hph.2.2.1, hph.2.2.2⟩


private lemma phaseAt_489 :
    phaseHolds (((489 : ℝ) / 1000)) ((527034117 : ℝ) / 1000000000) ((131758917 : ℝ) / 250000000) ((375750777 : ℝ) / 500000000) ((751523709 : ℝ) / 1000000000) := by
  have ht0 : (0 : ℝ) < ((489 : ℝ) / 1000) := by norm_num
  have ht1 : ((489 : ℝ) / 1000) ≤ 1 := by norm_num
  obtain ⟨hs7, hs5, hc6, hc4⟩ := trigPoly_bounds ht0
  have hsLo : ((93948663 : ℝ) / 200000000) < sin (((489 : ℝ) / 1000)) := by
    have hnum : ((93948663 : ℝ) / 200000000) <
        ((489 : ℝ) / 1000) - (((489 : ℝ) / 1000)) ^ 3 / 6 + (((489 : ℝ) / 1000)) ^ 5 / 120 - (((489 : ℝ) / 1000)) ^ 7 / 5040 := by norm_num
    linarith
  have hsHi : sin (((489 : ℝ) / 1000)) < ((469744643 : ℝ) / 1000000000) := by
    have hnum : ((489 : ℝ) / 1000) - (((489 : ℝ) / 1000)) ^ 3 / 6 + (((489 : ℝ) / 1000)) ^ 5 / 120 < ((469744643 : ℝ) / 1000000000) := by norm_num
    linarith
  have hcLo : ((441401481 : ℝ) / 500000000) < cos (((489 : ℝ) / 1000)) := by
    have hnum : ((441401481 : ℝ) / 500000000) <
        1 - (((489 : ℝ) / 1000)) ^ 2 / 2 + (((489 : ℝ) / 1000)) ^ 4 / 24 - (((489 : ℝ) / 1000)) ^ 6 / 720 := by norm_num
    linarith
  have hcHi : cos (((489 : ℝ) / 1000)) < ((882821953 : ℝ) / 1000000000) := by
    have hnum : 1 - (((489 : ℝ) / 1000)) ^ 2 / 2 + (((489 : ℝ) / 1000)) ^ 4 / 24 < ((882821953 : ℝ) / 1000000000) := by norm_num
    linarith
  have hexp := exp_between (x := ((489 : ℝ) / 1000)) (n := 8) (lo := ((815342271 : ℝ) / 500000000)) (hi := ((815342363 : ℝ) / 500000000))
    ht0.le ht1 (by decide)
    (by norm_num [sum_range_succ, Nat.factorial])
    (by norm_num [sum_range_succ, Nat.factorial])
  have hph : ((527034117 : ℝ) / 1000000000) < chordAmp (((489 : ℝ) / 1000)) ∧ chordAmp (((489 : ℝ) / 1000)) < ((131758917 : ℝ) / 250000000) ∧
      ((375750777 : ℝ) / 500000000) < gammaSEqual (((489 : ℝ) / 1000)) ∧ gammaSEqual (((489 : ℝ) / 1000)) < ((751523709 : ℝ) / 1000000000) := by
    exact phase_bounds ht0 ht1 hsLo hsHi hcLo hcHi hexp.1 hexp.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨ht0, ht1, by norm_num, by norm_num, hph.1, hph.2.1, by norm_num, hph.2.2.1, hph.2.2.2⟩


private lemma phaseAt_490 :
    phaseHolds (((490 : ℝ) / 1000)) ((528264007 : ℝ) / 1000000000) ((26413279 : ℝ) / 50000000) ((375223121 : ℝ) / 500000000) ((750468683 : ℝ) / 1000000000) := by
  have ht0 : (0 : ℝ) < ((490 : ℝ) / 1000) := by norm_num
  have ht1 : ((490 : ℝ) / 1000) ≤ 1 := by norm_num
  obtain ⟨hs7, hs5, hc6, hc4⟩ := trigPoly_bounds ht0
  have hsLo : ((470625883 : ℝ) / 1000000000) < sin (((490 : ℝ) / 1000)) := by
    have hnum : ((470625883 : ℝ) / 1000000000) <
        ((490 : ℝ) / 1000) - (((490 : ℝ) / 1000)) ^ 3 / 6 + (((490 : ℝ) / 1000)) ^ 5 / 120 - (((490 : ℝ) / 1000)) ^ 7 / 5040 := by norm_num
    linarith
  have hsHi : sin (((490 : ℝ) / 1000)) < ((47062723 : ℝ) / 100000000) := by
    have hnum : ((490 : ℝ) / 1000) - (((490 : ℝ) / 1000)) ^ 3 / 6 + (((490 : ℝ) / 1000)) ^ 5 / 120 < ((47062723 : ℝ) / 100000000) := by norm_num
    linarith
  have hcLo : ((110291597 : ℝ) / 125000000) < cos (((490 : ℝ) / 1000)) := by
    have hnum : ((110291597 : ℝ) / 125000000) <
        1 - (((490 : ℝ) / 1000)) ^ 2 / 2 + (((490 : ℝ) / 1000)) ^ 4 / 24 - (((490 : ℝ) / 1000)) ^ 6 / 720 := by norm_num
    linarith
  have hcHi : cos (((490 : ℝ) / 1000)) < ((882352001 : ℝ) / 1000000000) := by
    have hnum : 1 - (((490 : ℝ) / 1000)) ^ 2 / 2 + (((490 : ℝ) / 1000)) ^ 4 / 24 < ((882352001 : ℝ) / 1000000000) := by norm_num
    linarith
  have hexp := exp_between (x := ((490 : ℝ) / 1000)) (n := 8) (lo := ((40807901 : ℝ) / 25000000)) (hi := ((816158113 : ℝ) / 500000000))
    ht0.le ht1 (by decide)
    (by norm_num [sum_range_succ, Nat.factorial])
    (by norm_num [sum_range_succ, Nat.factorial])
  have hph : ((528264007 : ℝ) / 1000000000) < chordAmp (((490 : ℝ) / 1000)) ∧ chordAmp (((490 : ℝ) / 1000)) < ((26413279 : ℝ) / 50000000) ∧
      ((375223121 : ℝ) / 500000000) < gammaSEqual (((490 : ℝ) / 1000)) ∧ gammaSEqual (((490 : ℝ) / 1000)) < ((750468683 : ℝ) / 1000000000) := by
    exact phase_bounds ht0 ht1 hsLo hsHi hcLo hcHi hexp.1 hexp.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨ht0, ht1, by norm_num, by norm_num, hph.1, hph.2.1, by norm_num, hph.2.2.1, hph.2.2.2⟩


private lemma phaseAt_504 :
    phaseHolds (((504 : ℝ) / 1000)) ((545577601 : ℝ) / 1000000000) ((545579531 : ℝ) / 1000000000) ((45963291 : ℝ) / 62500000) ((735439453 : ℝ) / 1000000000) := by
  have ht0 : (0 : ℝ) < ((504 : ℝ) / 1000) := by norm_num
  have ht1 : ((504 : ℝ) / 1000) ≤ 1 := by norm_num
  obtain ⟨hs7, hs5, hc6, hc4⟩ := trigPoly_bounds ht0
  have hsLo : ((241466009 : ℝ) / 500000000) < sin (((504 : ℝ) / 1000)) := by
    have hnum : ((241466009 : ℝ) / 500000000) <
        ((504 : ℝ) / 1000) - (((504 : ℝ) / 1000)) ^ 3 / 6 + (((504 : ℝ) / 1000)) ^ 5 / 120 - (((504 : ℝ) / 1000)) ^ 7 / 5040 := by norm_num
    linarith
  have hsHi : sin (((504 : ℝ) / 1000)) < ((241466829 : ℝ) / 500000000) := by
    have hnum : ((504 : ℝ) / 1000) - (((504 : ℝ) / 1000)) ^ 3 / 6 + (((504 : ℝ) / 1000)) ^ 5 / 120 < ((241466829 : ℝ) / 500000000) := by norm_num
    linarith
  have hcLo : ((875657741 : ℝ) / 1000000000) < cos (((504 : ℝ) / 1000)) := by
    have hnum : ((875657741 : ℝ) / 1000000000) <
        1 - (((504 : ℝ) / 1000)) ^ 2 / 2 + (((504 : ℝ) / 1000)) ^ 4 / 24 - (((504 : ℝ) / 1000)) ^ 6 / 720 := by norm_num
    linarith
  have hcHi : cos (((504 : ℝ) / 1000)) < ((437840253 : ℝ) / 500000000) := by
    have hnum : 1 - (((504 : ℝ) / 1000)) ^ 2 / 2 + (((504 : ℝ) / 1000)) ^ 4 / 24 < ((437840253 : ℝ) / 500000000) := by norm_num
    linarith
  have hexp := exp_between (x := ((504 : ℝ) / 1000)) (n := 8) (lo := ((1655329137 : ℝ) / 1000000000)) (hi := ((165532937 : ℝ) / 100000000))
    ht0.le ht1 (by decide)
    (by norm_num [sum_range_succ, Nat.factorial])
    (by norm_num [sum_range_succ, Nat.factorial])
  have hph : ((545577601 : ℝ) / 1000000000) < chordAmp (((504 : ℝ) / 1000)) ∧ chordAmp (((504 : ℝ) / 1000)) < ((545579531 : ℝ) / 1000000000) ∧
      ((45963291 : ℝ) / 62500000) < gammaSEqual (((504 : ℝ) / 1000)) ∧ gammaSEqual (((504 : ℝ) / 1000)) < ((735439453 : ℝ) / 1000000000) := by
    exact phase_bounds ht0 ht1 hsLo hsHi hcLo hcHi hexp.1 hexp.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨ht0, ht1, by norm_num, by norm_num, hph.1, hph.2.1, by norm_num, hph.2.2.1, hph.2.2.2⟩


private lemma phaseAt_523 :
    phaseHolds (((523 : ℝ) / 1000)) ((569363947 : ℝ) / 1000000000) ((142341619 : ℝ) / 250000000) ((44639341 : ℝ) / 62500000) ((44641457 : ℝ) / 62500000) := by
  have ht0 : (0 : ℝ) < ((523 : ℝ) / 1000) := by norm_num
  have ht1 : ((523 : ℝ) / 1000) ≤ 1 := by norm_num
  obtain ⟨hs7, hs5, hc6, hc4⟩ := trigPoly_bounds ht0
  have hsLo : ((499481347 : ℝ) / 1000000000) < sin (((523 : ℝ) / 1000)) := by
    have hnum : ((499481347 : ℝ) / 1000000000) <
        ((523 : ℝ) / 1000) - (((523 : ℝ) / 1000)) ^ 3 / 6 + (((523 : ℝ) / 1000)) ^ 5 / 120 - (((523 : ℝ) / 1000)) ^ 7 / 5040 := by norm_num
    linarith
  have hsHi : sin (((523 : ℝ) / 1000)) < ((31217717 : ℝ) / 62500000) := by
    have hnum : ((523 : ℝ) / 1000) - (((523 : ℝ) / 1000)) ^ 3 / 6 + (((523 : ℝ) / 1000)) ^ 5 / 120 < ((31217717 : ℝ) / 62500000) := by norm_num
    linarith
  have hcLo : ((866324497 : ℝ) / 1000000000) < cos (((523 : ℝ) / 1000)) := by
    have hnum : ((866324497 : ℝ) / 1000000000) <
        1 - (((523 : ℝ) / 1000)) ^ 2 / 2 + (((523 : ℝ) / 1000)) ^ 4 / 24 - (((523 : ℝ) / 1000)) ^ 6 / 720 := by norm_num
    linarith
  have hcHi : cos (((523 : ℝ) / 1000)) < ((433176461 : ℝ) / 500000000) := by
    have hnum : 1 - (((523 : ℝ) / 1000)) ^ 2 / 2 + (((523 : ℝ) / 1000)) ^ 4 / 24 < ((433176461 : ℝ) / 500000000) := by norm_num
    linarith
  have hexp := exp_between (x := ((523 : ℝ) / 1000)) (n := 8) (lo := ((337416201 : ℝ) / 200000000)) (hi := ((1687081319 : ℝ) / 1000000000))
    ht0.le ht1 (by decide)
    (by norm_num [sum_range_succ, Nat.factorial])
    (by norm_num [sum_range_succ, Nat.factorial])
  have hph : ((569363947 : ℝ) / 1000000000) < chordAmp (((523 : ℝ) / 1000)) ∧ chordAmp (((523 : ℝ) / 1000)) < ((142341619 : ℝ) / 250000000) ∧
      ((44639341 : ℝ) / 62500000) < gammaSEqual (((523 : ℝ) / 1000)) ∧ gammaSEqual (((523 : ℝ) / 1000)) < ((44641457 : ℝ) / 62500000) := by
    exact phase_bounds ht0 ht1 hsLo hsHi hcLo hcHi hexp.1 hexp.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨ht0, ht1, by norm_num, by norm_num, hph.1, hph.2.1, by norm_num, hph.2.2.1, hph.2.2.2⟩


private lemma phaseAt_524 :
    phaseHolds (((524 : ℝ) / 1000)) ((285312627 : ℝ) / 500000000) ((285313909 : ℝ) / 500000000) ((356544723 : ℝ) / 500000000) ((713123711 : ℝ) / 1000000000) := by
  have ht0 : (0 : ℝ) < ((524 : ℝ) / 1000) := by norm_num
  have ht1 : ((524 : ℝ) / 1000) ≤ 1 := by norm_num
  obtain ⟨hs7, hs5, hc6, hc4⟩ := trigPoly_bounds ht0
  have hsLo : ((250173711 : ℝ) / 500000000) < sin (((524 : ℝ) / 1000)) := by
    have hnum : ((250173711 : ℝ) / 500000000) <
        ((524 : ℝ) / 1000) - (((524 : ℝ) / 1000)) ^ 3 / 6 + (((524 : ℝ) / 1000)) ^ 5 / 120 - (((524 : ℝ) / 1000)) ^ 7 / 5040 := by norm_num
    linarith
  have hsHi : sin (((524 : ℝ) / 1000)) < ((20013983 : ℝ) / 40000000) := by
    have hnum : ((524 : ℝ) / 1000) - (((524 : ℝ) / 1000)) ^ 3 / 6 + (((524 : ℝ) / 1000)) ^ 5 / 120 < ((20013983 : ℝ) / 40000000) := by norm_num
    linarith
  have hcLo : ((865824581 : ℝ) / 1000000000) < cos (((524 : ℝ) / 1000)) := by
    have hnum : ((865824581 : ℝ) / 1000000000) <
        1 - (((524 : ℝ) / 1000)) ^ 2 / 2 + (((524 : ℝ) / 1000)) ^ 4 / 24 - (((524 : ℝ) / 1000)) ^ 6 / 720 := by norm_num
    linarith
  have hcHi : cos (((524 : ℝ) / 1000)) < ((865853333 : ℝ) / 1000000000) := by
    have hnum : 1 - (((524 : ℝ) / 1000)) ^ 2 / 2 + (((524 : ℝ) / 1000)) ^ 4 / 24 < ((865853333 : ℝ) / 1000000000) := by norm_num
    linarith
  have hexp := exp_between (x := ((524 : ℝ) / 1000)) (n := 8) (lo := ((844384463 : ℝ) / 500000000)) (hi := ((422192311 : ℝ) / 250000000))
    ht0.le ht1 (by decide)
    (by norm_num [sum_range_succ, Nat.factorial])
    (by norm_num [sum_range_succ, Nat.factorial])
  have hph : ((285312627 : ℝ) / 500000000) < chordAmp (((524 : ℝ) / 1000)) ∧ chordAmp (((524 : ℝ) / 1000)) < ((285313909 : ℝ) / 500000000) ∧
      ((356544723 : ℝ) / 500000000) < gammaSEqual (((524 : ℝ) / 1000)) ∧ gammaSEqual (((524 : ℝ) / 1000)) < ((713123711 : ℝ) / 1000000000) := by
    exact phase_bounds ht0 ht1 hsLo hsHi hcLo hcHi hexp.1 hexp.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨ht0, ht1, by norm_num, by norm_num, hph.1, hph.2.1, by norm_num, hph.2.2.1, hph.2.2.2⟩


private lemma phaseAt_525 :
    phaseHolds (((525 : ℝ) / 1000)) ((57188751 : ℝ) / 100000000) ((57189011 : ℝ) / 100000000) ((711946909 : ℝ) / 1000000000) ((711981591 : ℝ) / 1000000000) := by
  have ht0 : (0 : ℝ) < ((525 : ℝ) / 1000) := by norm_num
  have ht1 : ((525 : ℝ) / 1000) ≤ 1 := by norm_num
  obtain ⟨hs7, hs5, hc6, hc4⟩ := trigPoly_bounds ht0
  have hsLo : ((125303249 : ℝ) / 250000000) < sin (((525 : ℝ) / 1000)) := by
    have hnum : ((125303249 : ℝ) / 250000000) <
        ((525 : ℝ) / 1000) - (((525 : ℝ) / 1000)) ^ 3 / 6 + (((525 : ℝ) / 1000)) ^ 5 / 120 - (((525 : ℝ) / 1000)) ^ 7 / 5040 := by norm_num
    linarith
  have hsHi : sin (((525 : ℝ) / 1000)) < ((250607589 : ℝ) / 500000000) := by
    have hnum : ((525 : ℝ) / 1000) - (((525 : ℝ) / 1000)) ^ 3 / 6 + (((525 : ℝ) / 1000)) ^ 5 / 120 < ((250607589 : ℝ) / 500000000) := by norm_num
    linarith
  have hcLo : ((432661899 : ℝ) / 500000000) < cos (((525 : ℝ) / 1000)) := by
    have hnum : ((432661899 : ℝ) / 500000000) <
        1 - (((525 : ℝ) / 1000)) ^ 2 / 2 + (((525 : ℝ) / 1000)) ^ 4 / 24 - (((525 : ℝ) / 1000)) ^ 6 / 720 := by norm_num
    linarith
  have hcHi : cos (((525 : ℝ) / 1000)) < ((865352881 : ℝ) / 1000000000) := by
    have hnum : 1 - (((525 : ℝ) / 1000)) ^ 2 / 2 + (((525 : ℝ) / 1000)) ^ 4 / 24 < ((865352881 : ℝ) / 1000000000) := by norm_num
    linarith
  have hexp := exp_between (x := ((525 : ℝ) / 1000)) (n := 8) (lo := ((338091707 : ℝ) / 200000000)) (hi := ((845229429 : ℝ) / 500000000))
    ht0.le ht1 (by decide)
    (by norm_num [sum_range_succ, Nat.factorial])
    (by norm_num [sum_range_succ, Nat.factorial])
  have hph : ((57188751 : ℝ) / 100000000) < chordAmp (((525 : ℝ) / 1000)) ∧ chordAmp (((525 : ℝ) / 1000)) < ((57189011 : ℝ) / 100000000) ∧
      ((711946909 : ℝ) / 1000000000) < gammaSEqual (((525 : ℝ) / 1000)) ∧ gammaSEqual (((525 : ℝ) / 1000)) < ((711981591 : ℝ) / 1000000000) := by
    exact phase_bounds ht0 ht1 hsLo hsHi hcLo hcHi hexp.1 hexp.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨ht0, ht1, by norm_num, by norm_num, hph.1, hph.2.1, by norm_num, hph.2.2.1, hph.2.2.2⟩


private lemma phaseAt_553 :
    phaseHolds (((553 : ℝ) / 1000)) ((607621891 : ℝ) / 1000000000) ((121525139 : ℝ) / 200000000) ((169730853 : ℝ) / 250000000) ((339485819 : ℝ) / 500000000) := by
  have ht0 : (0 : ℝ) < ((553 : ℝ) / 1000) := by norm_num
  have ht1 : ((553 : ℝ) / 1000) ≤ 1 := by norm_num
  obtain ⟨hs7, hs5, hc6, hc4⟩ := trigPoly_bounds ht0
  have hsLo : ((525242433 : ℝ) / 1000000000) < sin (((553 : ℝ) / 1000)) := by
    have hnum : ((525242433 : ℝ) / 1000000000) <
        ((553 : ℝ) / 1000) - (((553 : ℝ) / 1000)) ^ 3 / 6 + (((553 : ℝ) / 1000)) ^ 5 / 120 - (((553 : ℝ) / 1000)) ^ 7 / 5040 := by norm_num
    linarith
  have hsHi : sin (((553 : ℝ) / 1000)) < ((131311393 : ℝ) / 250000000) := by
    have hnum : ((553 : ℝ) / 1000) - (((553 : ℝ) / 1000)) ^ 3 / 6 + (((553 : ℝ) / 1000)) ^ 5 / 120 < ((131311393 : ℝ) / 250000000) := by norm_num
    linarith
  have hcLo : ((85095241 : ℝ) / 100000000) < cos (((553 : ℝ) / 1000)) := by
    have hnum : ((85095241 : ℝ) / 100000000) <
        1 - (((553 : ℝ) / 1000)) ^ 2 / 2 + (((553 : ℝ) / 1000)) ^ 4 / 24 - (((553 : ℝ) / 1000)) ^ 6 / 720 := by norm_num
    linarith
  have hcHi : cos (((553 : ℝ) / 1000)) < ((212748033 : ℝ) / 250000000) := by
    have hnum : 1 - (((553 : ℝ) / 1000)) ^ 2 / 2 + (((553 : ℝ) / 1000)) ^ 4 / 24 < ((212748033 : ℝ) / 250000000) := by norm_num
    linarith
  have hexp := exp_between (x := ((553 : ℝ) / 1000)) (n := 8) (lo := ((1738460109 : ℝ) / 1000000000)) (hi := ((869230299 : ℝ) / 500000000))
    ht0.le ht1 (by decide)
    (by norm_num [sum_range_succ, Nat.factorial])
    (by norm_num [sum_range_succ, Nat.factorial])
  have hph : ((607621891 : ℝ) / 1000000000) < chordAmp (((553 : ℝ) / 1000)) ∧ chordAmp (((553 : ℝ) / 1000)) < ((121525139 : ℝ) / 200000000) ∧
      ((169730853 : ℝ) / 250000000) < gammaSEqual (((553 : ℝ) / 1000)) ∧ gammaSEqual (((553 : ℝ) / 1000)) < ((339485819 : ℝ) / 500000000) := by
    exact phase_bounds ht0 ht1 hsLo hsHi hcLo hcHi hexp.1 hexp.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨ht0, ht1, by norm_num, by norm_num, hph.1, hph.2.1, by norm_num, hph.2.2.1, hph.2.2.2⟩


private lemma phaseAt_558 :
    phaseHolds (((558 : ℝ) / 1000)) ((307041911 : ℝ) / 500000000) ((122817577 : ℝ) / 200000000) ((67281473 : ℝ) / 100000000) ((3364329 : ℝ) / 5000000) := by
  have ht0 : (0 : ℝ) < ((558 : ℝ) / 1000) := by norm_num
  have ht1 : ((558 : ℝ) / 1000) ≤ 1 := by norm_num
  obtain ⟨hs7, hs5, hc6, hc4⟩ := trigPoly_bounds ht0
  have hsLo : ((132372653 : ℝ) / 250000000) < sin (((558 : ℝ) / 1000)) := by
    have hnum : ((132372653 : ℝ) / 250000000) <
        ((558 : ℝ) / 1000) - (((558 : ℝ) / 1000)) ^ 3 / 6 + (((558 : ℝ) / 1000)) ^ 5 / 120 - (((558 : ℝ) / 1000)) ^ 7 / 5040 := by norm_num
    linarith
  have hsHi : sin (((558 : ℝ) / 1000)) < ((105898791 : ℝ) / 200000000) := by
    have hnum : ((558 : ℝ) / 1000) - (((558 : ℝ) / 1000)) ^ 3 / 6 + (((558 : ℝ) / 1000)) ^ 5 / 120 < ((105898791 : ℝ) / 200000000) := by norm_num
    linarith
  have hcLo : ((169663111 : ℝ) / 200000000) < cos (((558 : ℝ) / 1000)) := by
    have hnum : ((169663111 : ℝ) / 200000000) <
        1 - (((558 : ℝ) / 1000)) ^ 2 / 2 + (((558 : ℝ) / 1000)) ^ 4 / 24 - (((558 : ℝ) / 1000)) ^ 6 / 720 := by norm_num
    linarith
  have hcHi : cos (((558 : ℝ) / 1000)) < ((848357481 : ℝ) / 1000000000) := by
    have hnum : 1 - (((558 : ℝ) / 1000)) ^ 2 / 2 + (((558 : ℝ) / 1000)) ^ 4 / 24 < ((848357481 : ℝ) / 1000000000) := by norm_num
    linarith
  have hexp := exp_between (x := ((558 : ℝ) / 1000)) (n := 8) (lo := ((1747174143 : ℝ) / 1000000000)) (hi := ((1747174669 : ℝ) / 1000000000))
    ht0.le ht1 (by decide)
    (by norm_num [sum_range_succ, Nat.factorial])
    (by norm_num [sum_range_succ, Nat.factorial])
  have hph : ((307041911 : ℝ) / 500000000) < chordAmp (((558 : ℝ) / 1000)) ∧ chordAmp (((558 : ℝ) / 1000)) < ((122817577 : ℝ) / 200000000) ∧
      ((67281473 : ℝ) / 100000000) < gammaSEqual (((558 : ℝ) / 1000)) ∧ gammaSEqual (((558 : ℝ) / 1000)) < ((3364329 : ℝ) / 5000000) := by
    exact phase_bounds ht0 ht1 hsLo hsHi hcLo hcHi hexp.1 hexp.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨ht0, ht1, by norm_num, by norm_num, hph.1, hph.2.1, by norm_num, hph.2.2.1, hph.2.2.2⟩


private lemma phaseAt_559 :
    phaseHolds (((559 : ℝ) / 1000)) ((76922399 : ℝ) / 125000000) ((153845827 : ℝ) / 250000000) ((41974077 : ℝ) / 62500000) ((671636887 : ℝ) / 1000000000) := by
  have ht0 : (0 : ℝ) < ((559 : ℝ) / 1000) := by norm_num
  have ht1 : ((559 : ℝ) / 1000) ≤ 1 := by norm_num
  obtain ⟨hs7, hs5, hc6, hc4⟩ := trigPoly_bounds ht0
  have hsLo : ((265169331 : ℝ) / 500000000) < sin (((559 : ℝ) / 1000)) := by
    have hnum : ((265169331 : ℝ) / 500000000) <
        ((559 : ℝ) / 1000) - (((559 : ℝ) / 1000)) ^ 3 / 6 + (((559 : ℝ) / 1000)) ^ 5 / 120 - (((559 : ℝ) / 1000)) ^ 7 / 5040 := by norm_num
    linarith
  have hsHi : sin (((559 : ℝ) / 1000)) < ((530342047 : ℝ) / 1000000000) := by
    have hnum : ((559 : ℝ) / 1000) - (((559 : ℝ) / 1000)) ^ 3 / 6 + (((559 : ℝ) / 1000)) ^ 5 / 120 < ((530342047 : ℝ) / 1000000000) := by norm_num
    linarith
  have hcLo : ((847785637 : ℝ) / 1000000000) < cos (((559 : ℝ) / 1000)) := by
    have hnum : ((847785637 : ℝ) / 1000000000) <
        1 - (((559 : ℝ) / 1000)) ^ 2 / 2 + (((559 : ℝ) / 1000)) ^ 4 / 24 - (((559 : ℝ) / 1000)) ^ 6 / 720 := by norm_num
    linarith
  have hcHi : cos (((559 : ℝ) / 1000)) < ((52989251 : ℝ) / 62500000) := by
    have hnum : 1 - (((559 : ℝ) / 1000)) ^ 2 / 2 + (((559 : ℝ) / 1000)) ^ 4 / 24 < ((52989251 : ℝ) / 62500000) := by norm_num
    linarith
  have hexp := exp_between (x := ((559 : ℝ) / 1000)) (n := 8) (lo := ((218615273 : ℝ) / 125000000)) (hi := ((1748922717 : ℝ) / 1000000000))
    ht0.le ht1 (by decide)
    (by norm_num [sum_range_succ, Nat.factorial])
    (by norm_num [sum_range_succ, Nat.factorial])
  have hph : ((76922399 : ℝ) / 125000000) < chordAmp (((559 : ℝ) / 1000)) ∧ chordAmp (((559 : ℝ) / 1000)) < ((153845827 : ℝ) / 250000000) ∧
      ((41974077 : ℝ) / 62500000) < gammaSEqual (((559 : ℝ) / 1000)) ∧ gammaSEqual (((559 : ℝ) / 1000)) < ((671636887 : ℝ) / 1000000000) := by
    exact phase_bounds ht0 ht1 hsLo hsHi hcLo hcHi hexp.1 hexp.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨ht0, ht1, by norm_num, by norm_num, hph.1, hph.2.1, by norm_num, hph.2.2.1, hph.2.2.2⟩


private lemma phaseAt_565 :
    phaseHolds (((565 : ℝ) / 1000)) ((311586209 : ℝ) / 500000000) ((623176871 : ℝ) / 1000000000) ((664153733 : ℝ) / 1000000000) ((26568361 : ℝ) / 40000000) := by
  have ht0 : (0 : ℝ) < ((565 : ℝ) / 1000) := by norm_num
  have ht1 : ((565 : ℝ) / 1000) ≤ 1 := by norm_num
  obtain ⟨hs7, hs5, hc6, hc4⟩ := trigPoly_bounds ht0
  have hsLo : ((535415799 : ℝ) / 1000000000) < sin (((565 : ℝ) / 1000)) := by
    have hnum : ((535415799 : ℝ) / 1000000000) <
        ((565 : ℝ) / 1000) - (((565 : ℝ) / 1000)) ^ 3 / 6 + (((565 : ℝ) / 1000)) ^ 5 / 120 - (((565 : ℝ) / 1000)) ^ 7 / 5040 := by norm_num
    linarith
  have hsHi : sin (((565 : ℝ) / 1000)) < ((535419447 : ℝ) / 1000000000) := by
    have hnum : ((565 : ℝ) / 1000) - (((565 : ℝ) / 1000)) ^ 3 / 6 + (((565 : ℝ) / 1000)) ^ 5 / 120 < ((535419447 : ℝ) / 1000000000) := by norm_num
    linarith
  have hcLo : ((844588343 : ℝ) / 1000000000) < cos (((565 : ℝ) / 1000)) := by
    have hnum : ((844588343 : ℝ) / 1000000000) <
        1 - (((565 : ℝ) / 1000)) ^ 2 / 2 + (((565 : ℝ) / 1000)) ^ 4 / 24 - (((565 : ℝ) / 1000)) ^ 6 / 720 := by norm_num
    linarith
  have hcHi : cos (((565 : ℝ) / 1000)) < ((422316763 : ℝ) / 500000000) := by
    have hnum : 1 - (((565 : ℝ) / 1000)) ^ 2 / 2 + (((565 : ℝ) / 1000)) ^ 4 / 24 < ((422316763 : ℝ) / 500000000) := by norm_num
    linarith
  have hexp := exp_between (x := ((565 : ℝ) / 1000)) (n := 8) (lo := ((879723609 : ℝ) / 500000000)) (hi := ((879723899 : ℝ) / 500000000))
    ht0.le ht1 (by decide)
    (by norm_num [sum_range_succ, Nat.factorial])
    (by norm_num [sum_range_succ, Nat.factorial])
  have hph : ((311586209 : ℝ) / 500000000) < chordAmp (((565 : ℝ) / 1000)) ∧ chordAmp (((565 : ℝ) / 1000)) < ((623176871 : ℝ) / 1000000000) ∧
      ((664153733 : ℝ) / 1000000000) < gammaSEqual (((565 : ℝ) / 1000)) ∧ gammaSEqual (((565 : ℝ) / 1000)) < ((26568361 : ℝ) / 40000000) := by
    exact phase_bounds ht0 ht1 hsLo hsHi hcLo hcHi hexp.1 hexp.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨ht0, ht1, by norm_num, by norm_num, hph.1, hph.2.1, by norm_num, hph.2.2.1, hph.2.2.2⟩


private lemma phaseAt_571 :
    phaseHolds (((571 : ℝ) / 1000)) ((631001859 : ℝ) / 1000000000) ((63100667 : ℝ) / 100000000) ((656628481 : ℝ) / 1000000000) ((5253501 : ℝ) / 8000000) := by
  have ht0 : (0 : ℝ) < ((571 : ℝ) / 1000) := by norm_num
  have ht1 : ((571 : ℝ) / 1000) ≤ 1 := by norm_num
  obtain ⟨hs7, hs5, hc6, hc4⟩ := trigPoly_bounds ht0
  have hsLo : ((270236831 : ℝ) / 500000000) < sin (((571 : ℝ) / 1000)) := by
    have hnum : ((270236831 : ℝ) / 500000000) <
        ((571 : ℝ) / 1000) - (((571 : ℝ) / 1000)) ^ 3 / 6 + (((571 : ℝ) / 1000)) ^ 5 / 120 - (((571 : ℝ) / 1000)) ^ 7 / 5040 := by norm_num
    linarith
  have hsHi : sin (((571 : ℝ) / 1000)) < ((540477589 : ℝ) / 1000000000) := by
    have hnum : ((571 : ℝ) / 1000) - (((571 : ℝ) / 1000)) ^ 3 / 6 + (((571 : ℝ) / 1000)) ^ 5 / 120 < ((540477589 : ℝ) / 1000000000) := by norm_num
    linarith
  have hcLo : ((841360643 : ℝ) / 1000000000) < cos (((571 : ℝ) / 1000)) := by
    have hnum : ((841360643 : ℝ) / 1000000000) <
        1 - (((571 : ℝ) / 1000)) ^ 2 / 2 + (((571 : ℝ) / 1000)) ^ 4 / 24 - (((571 : ℝ) / 1000)) ^ 6 / 720 := by norm_num
    linarith
  have hcHi : cos (((571 : ℝ) / 1000)) < ((841408781 : ℝ) / 1000000000) := by
    have hnum : 1 - (((571 : ℝ) / 1000)) ^ 2 / 2 + (((571 : ℝ) / 1000)) ^ 4 / 24 < ((841408781 : ℝ) / 1000000000) := by norm_num
    linarith
  have hexp := exp_between (x := ((571 : ℝ) / 1000)) (n := 8) (lo := ((442508897 : ℝ) / 250000000)) (hi := ((88501811 : ℝ) / 50000000))
    ht0.le ht1 (by decide)
    (by norm_num [sum_range_succ, Nat.factorial])
    (by norm_num [sum_range_succ, Nat.factorial])
  have hph : ((631001859 : ℝ) / 1000000000) < chordAmp (((571 : ℝ) / 1000)) ∧ chordAmp (((571 : ℝ) / 1000)) < ((63100667 : ℝ) / 100000000) ∧
      ((656628481 : ℝ) / 1000000000) < gammaSEqual (((571 : ℝ) / 1000)) ∧ gammaSEqual (((571 : ℝ) / 1000)) < ((5253501 : ℝ) / 8000000) := by
    exact phase_bounds ht0 ht1 hsLo hsHi hcLo hcHi hexp.1 hexp.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨ht0, ht1, by norm_num, by norm_num, hph.1, hph.2.1, by norm_num, hph.2.2.1, hph.2.2.2⟩


private lemma phaseAt_572 :
    phaseHolds (((572 : ℝ) / 1000)) ((316155153 : ℝ) / 500000000) ((31615759 : ℝ) / 50000000) ((327682563 : ℝ) / 500000000) ((131084987 : ℝ) / 200000000) := by
  have ht0 : (0 : ℝ) < ((572 : ℝ) / 1000) := by norm_num
  have ht1 : ((572 : ℝ) / 1000) ≤ 1 := by norm_num
  obtain ⟨hs7, hs5, hc6, hc4⟩ := trigPoly_bounds ht0
  have hsLo : ((8458043 : ℝ) / 15625000) < sin (((572 : ℝ) / 1000)) := by
    have hnum : ((8458043 : ℝ) / 15625000) <
        ((572 : ℝ) / 1000) - (((572 : ℝ) / 1000)) ^ 3 / 6 + (((572 : ℝ) / 1000)) ^ 5 / 120 - (((572 : ℝ) / 1000)) ^ 7 / 5040 := by norm_num
    linarith
  have hsHi : sin (((572 : ℝ) / 1000)) < ((67664841 : ℝ) / 125000000) := by
    have hnum : ((572 : ℝ) / 1000) - (((572 : ℝ) / 1000)) ^ 3 / 6 + (((572 : ℝ) / 1000)) ^ 5 / 120 < ((67664841 : ℝ) / 125000000) := by norm_num
    linarith
  have hcLo : ((26275617 : ℝ) / 31250000) < cos (((572 : ℝ) / 1000)) := by
    have hnum : ((26275617 : ℝ) / 31250000) <
        1 - (((572 : ℝ) / 1000)) ^ 2 / 2 + (((572 : ℝ) / 1000)) ^ 4 / 24 - (((572 : ℝ) / 1000)) ^ 6 / 720 := by norm_num
    linarith
  have hcHi : cos (((572 : ℝ) / 1000)) < ((840868391 : ℝ) / 1000000000) := by
    have hnum : 1 - (((572 : ℝ) / 1000)) ^ 2 / 2 + (((572 : ℝ) / 1000)) ^ 4 / 24 < ((840868391 : ℝ) / 1000000000) := by norm_num
    linarith
  have hexp := exp_between (x := ((572 : ℝ) / 1000)) (n := 8) (lo := ((1771806501 : ℝ) / 1000000000)) (hi := ((1771807141 : ℝ) / 1000000000))
    ht0.le ht1 (by decide)
    (by norm_num [sum_range_succ, Nat.factorial])
    (by norm_num [sum_range_succ, Nat.factorial])
  have hph : ((316155153 : ℝ) / 500000000) < chordAmp (((572 : ℝ) / 1000)) ∧ chordAmp (((572 : ℝ) / 1000)) < ((31615759 : ℝ) / 50000000) ∧
      ((327682563 : ℝ) / 500000000) < gammaSEqual (((572 : ℝ) / 1000)) ∧ gammaSEqual (((572 : ℝ) / 1000)) < ((131084987 : ℝ) / 200000000) := by
    exact phase_bounds ht0 ht1 hsLo hsHi hcLo hcHi hexp.1 hexp.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨ht0, ht1, by norm_num, by norm_num, hph.1, hph.2.1, by norm_num, hph.2.2.1, hph.2.2.2⟩


private lemma phaseAt_581 :
    phaseHolds (((581 : ℝ) / 1000)) ((644132173 : ℝ) / 1000000000) ((16103441 : ℝ) / 25000000) ((643876863 : ℝ) / 1000000000) ((643942943 : ℝ) / 1000000000) := by
  have ht0 : (0 : ℝ) < ((581 : ℝ) / 1000) := by norm_num
  have ht1 : ((581 : ℝ) / 1000) ≤ 1 := by norm_num
  obtain ⟨hs7, hs5, hc6, hc4⟩ := trigPoly_bounds ht0
  have hsLo : ((68607513 : ℝ) / 125000000) < sin (((581 : ℝ) / 1000)) := by
    have hnum : ((68607513 : ℝ) / 125000000) <
        ((581 : ℝ) / 1000) - (((581 : ℝ) / 1000)) ^ 3 / 6 + (((581 : ℝ) / 1000)) ^ 5 / 120 - (((581 : ℝ) / 1000)) ^ 7 / 5040 := by norm_num
    linarith
  have hsHi : sin (((581 : ℝ) / 1000)) < ((548864539 : ℝ) / 1000000000) := by
    have hnum : ((581 : ℝ) / 1000) - (((581 : ℝ) / 1000)) ^ 3 / 6 + (((581 : ℝ) / 1000)) ^ 5 / 120 < ((548864539 : ℝ) / 1000000000) := by norm_num
    linarith
  have hcLo : ((835913887 : ℝ) / 1000000000) < cos (((581 : ℝ) / 1000)) := by
    have hnum : ((835913887 : ℝ) / 1000000000) <
        1 - (((581 : ℝ) / 1000)) ^ 2 / 2 + (((581 : ℝ) / 1000)) ^ 4 / 24 - (((581 : ℝ) / 1000)) ^ 6 / 720 := by norm_num
    linarith
  have hcHi : cos (((581 : ℝ) / 1000)) < ((83596731 : ℝ) / 100000000) := by
    have hnum : 1 - (((581 : ℝ) / 1000)) ^ 2 / 2 + (((581 : ℝ) / 1000)) ^ 4 / 24 < ((83596731 : ℝ) / 100000000) := by norm_num
    linarith
  have hexp := exp_between (x := ((581 : ℝ) / 1000)) (n := 8) (lo := ((111739041 : ℝ) / 62500000)) (hi := ((1787825381 : ℝ) / 1000000000))
    ht0.le ht1 (by decide)
    (by norm_num [sum_range_succ, Nat.factorial])
    (by norm_num [sum_range_succ, Nat.factorial])
  have hph : ((644132173 : ℝ) / 1000000000) < chordAmp (((581 : ℝ) / 1000)) ∧ chordAmp (((581 : ℝ) / 1000)) < ((16103441 : ℝ) / 25000000) ∧
      ((643876863 : ℝ) / 1000000000) < gammaSEqual (((581 : ℝ) / 1000)) ∧ gammaSEqual (((581 : ℝ) / 1000)) < ((643942943 : ℝ) / 1000000000) := by
    exact phase_bounds ht0 ht1 hsLo hsHi hcLo hcHi hexp.1 hexp.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨ht0, ht1, by norm_num, by norm_num, hph.1, hph.2.1, by norm_num, hph.2.2.1, hph.2.2.2⟩


private lemma phaseAt_605 :
    phaseHolds (((605 : ℝ) / 1000)) ((6760663 : ℝ) / 10000000) ((676073669 : ℝ) / 1000000000) ((24487727 : ℝ) / 40000000) ((306139411 : ℝ) / 500000000) := by
  have ht0 : (0 : ℝ) < ((605 : ℝ) / 1000) := by norm_num
  have ht1 : ((605 : ℝ) / 1000) ≤ 1 := by norm_num
  obtain ⟨hs7, hs5, hc6, hc4⟩ := trigPoly_bounds ht0
  have hsLo : ((284381023 : ℝ) / 500000000) < sin (((605 : ℝ) / 1000)) := by
    have hnum : ((284381023 : ℝ) / 500000000) <
        ((605 : ℝ) / 1000) - (((605 : ℝ) / 1000)) ^ 3 / 6 + (((605 : ℝ) / 1000)) ^ 5 / 120 - (((605 : ℝ) / 1000)) ^ 7 / 5040 := by norm_num
    linarith
  have hsHi : sin (((605 : ℝ) / 1000)) < ((568767933 : ℝ) / 1000000000) := by
    have hnum : ((605 : ℝ) / 1000) - (((605 : ℝ) / 1000)) ^ 3 / 6 + (((605 : ℝ) / 1000)) ^ 5 / 120 < ((568767933 : ℝ) / 1000000000) := by norm_num
    linarith
  have hcLo : ((411250827 : ℝ) / 500000000) < cos (((605 : ℝ) / 1000)) := by
    have hnum : ((411250827 : ℝ) / 500000000) <
        1 - (((605 : ℝ) / 1000)) ^ 2 / 2 + (((605 : ℝ) / 1000)) ^ 4 / 24 - (((605 : ℝ) / 1000)) ^ 6 / 720 := by norm_num
    linarith
  have hcHi : cos (((605 : ℝ) / 1000)) < ((822569763 : ℝ) / 1000000000) := by
    have hnum : 1 - (((605 : ℝ) / 1000)) ^ 2 / 2 + (((605 : ℝ) / 1000)) ^ 4 / 24 < ((822569763 : ℝ) / 1000000000) := by norm_num
    linarith
  have hexp := exp_between (x := ((605 : ℝ) / 1000)) (n := 8) (lo := ((1831251231 : ℝ) / 1000000000)) (hi := ((1831252233 : ℝ) / 1000000000))
    ht0.le ht1 (by decide)
    (by norm_num [sum_range_succ, Nat.factorial])
    (by norm_num [sum_range_succ, Nat.factorial])
  have hph : ((6760663 : ℝ) / 10000000) < chordAmp (((605 : ℝ) / 1000)) ∧ chordAmp (((605 : ℝ) / 1000)) < ((676073669 : ℝ) / 1000000000) ∧
      ((24487727 : ℝ) / 40000000) < gammaSEqual (((605 : ℝ) / 1000)) ∧ gammaSEqual (((605 : ℝ) / 1000)) < ((306139411 : ℝ) / 500000000) := by
    exact phase_bounds ht0 ht1 hsLo hsHi hcLo hcHi hexp.1 hexp.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨ht0, ht1, by norm_num, by norm_num, hph.1, hph.2.1, by norm_num, hph.2.2.1, hph.2.2.2⟩


private lemma phaseAt_620 :
    phaseHolds (((620 : ℝ) / 1000)) ((696333199 : ℝ) / 1000000000) ((696342031 : ℝ) / 1000000000) ((29580337 : ℝ) / 50000000) ((295853499 : ℝ) / 500000000) := by
  have ht0 : (0 : ℝ) < ((620 : ℝ) / 1000) := by norm_num
  have ht1 : ((620 : ℝ) / 1000) ≤ 1 := by norm_num
  obtain ⟨hs7, hs5, hc6, hc4⟩ := trigPoly_bounds ht0
  have hsLo : ((581035123 : ℝ) / 1000000000) < sin (((620 : ℝ) / 1000)) := by
    have hnum : ((581035123 : ℝ) / 1000000000) <
        ((620 : ℝ) / 1000) - (((620 : ℝ) / 1000)) ^ 3 / 6 + (((620 : ℝ) / 1000)) ^ 5 / 120 - (((620 : ℝ) / 1000)) ^ 7 / 5040 := by norm_num
    linarith
  have hsHi : sin (((620 : ℝ) / 1000)) < ((581042111 : ℝ) / 1000000000) := by
    have hnum : ((620 : ℝ) / 1000) - (((620 : ℝ) / 1000)) ^ 3 / 6 + (((620 : ℝ) / 1000)) ^ 5 / 120 < ((581042111 : ℝ) / 1000000000) := by norm_num
    linarith
  have hcLo : ((813877917 : ℝ) / 1000000000) < cos (((620 : ℝ) / 1000)) := by
    have hnum : ((813877917 : ℝ) / 1000000000) <
        1 - (((620 : ℝ) / 1000)) ^ 2 / 2 + (((620 : ℝ) / 1000)) ^ 4 / 24 - (((620 : ℝ) / 1000)) ^ 6 / 720 := by norm_num
    linarith
  have hcHi : cos (((620 : ℝ) / 1000)) < ((813956807 : ℝ) / 1000000000) := by
    have hnum : 1 - (((620 : ℝ) / 1000)) ^ 2 / 2 + (((620 : ℝ) / 1000)) ^ 4 / 24 < ((813956807 : ℝ) / 1000000000) := by norm_num
    linarith
  have hexp := exp_between (x := ((620 : ℝ) / 1000)) (n := 8) (lo := ((1858926851 : ℝ) / 1000000000)) (hi := ((185892807 : ℝ) / 100000000))
    ht0.le ht1 (by decide)
    (by norm_num [sum_range_succ, Nat.factorial])
    (by norm_num [sum_range_succ, Nat.factorial])
  have hph : ((696333199 : ℝ) / 1000000000) < chordAmp (((620 : ℝ) / 1000)) ∧ chordAmp (((620 : ℝ) / 1000)) < ((696342031 : ℝ) / 1000000000) ∧
      ((29580337 : ℝ) / 50000000) < gammaSEqual (((620 : ℝ) / 1000)) ∧ gammaSEqual (((620 : ℝ) / 1000)) < ((295853499 : ℝ) / 500000000) := by
    exact phase_bounds ht0 ht1 hsLo hsHi hcLo hcHi hexp.1 hexp.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨ht0, ht1, by norm_num, by norm_num, hph.1, hph.2.1, by norm_num, hph.2.2.1, hph.2.2.2⟩


private lemma phaseAt_623 :
    phaseHolds (((623 : ℝ) / 1000)) ((175103869 : ℝ) / 250000000) ((700424631 : ℝ) / 1000000000) ((587416267 : ℝ) / 1000000000) ((587519693 : ℝ) / 1000000000) := by
  have ht0 : (0 : ℝ) < ((623 : ℝ) / 1000) := by norm_num
  have ht1 : ((623 : ℝ) / 1000) ≤ 1 := by norm_num
  obtain ⟨hs7, hs5, hc6, hc4⟩ := trigPoly_bounds ht0
  have hsLo : ((291737069 : ℝ) / 500000000) < sin (((623 : ℝ) / 1000)) := by
    have hnum : ((291737069 : ℝ) / 500000000) <
        ((623 : ℝ) / 1000) - (((623 : ℝ) / 1000)) ^ 3 / 6 + (((623 : ℝ) / 1000)) ^ 5 / 120 - (((623 : ℝ) / 1000)) ^ 7 / 5040 := by norm_num
    linarith
  have hsHi : sin (((623 : ℝ) / 1000)) < ((583481367 : ℝ) / 1000000000) := by
    have hnum : ((623 : ℝ) / 1000) - (((623 : ℝ) / 1000)) ^ 3 / 6 + (((623 : ℝ) / 1000)) ^ 5 / 120 < ((583481367 : ℝ) / 1000000000) := by norm_num
    linarith
  have hcLo : ((81213113 : ℝ) / 100000000) < cos (((623 : ℝ) / 1000)) := by
    have hnum : ((81213113 : ℝ) / 100000000) <
        1 - (((623 : ℝ) / 1000)) ^ 2 / 2 + (((623 : ℝ) / 1000)) ^ 4 / 24 - (((623 : ℝ) / 1000)) ^ 6 / 720 := by norm_num
    linarith
  have hcHi : cos (((623 : ℝ) / 1000)) < ((812212339 : ℝ) / 1000000000) := by
    have hnum : 1 - (((623 : ℝ) / 1000)) ^ 2 / 2 + (((623 : ℝ) / 1000)) ^ 4 / 24 < ((812212339 : ℝ) / 1000000000) := by norm_num
    linarith
  have hexp := exp_between (x := ((623 : ℝ) / 1000)) (n := 8) (lo := ((1864511961 : ℝ) / 1000000000)) (hi := ((1864513229 : ℝ) / 1000000000))
    ht0.le ht1 (by decide)
    (by norm_num [sum_range_succ, Nat.factorial])
    (by norm_num [sum_range_succ, Nat.factorial])
  have hph : ((175103869 : ℝ) / 250000000) < chordAmp (((623 : ℝ) / 1000)) ∧ chordAmp (((623 : ℝ) / 1000)) < ((700424631 : ℝ) / 1000000000) ∧
      ((587416267 : ℝ) / 1000000000) < gammaSEqual (((623 : ℝ) / 1000)) ∧ gammaSEqual (((623 : ℝ) / 1000)) < ((587519693 : ℝ) / 1000000000) := by
    exact phase_bounds ht0 ht1 hsLo hsHi hcLo hcHi hexp.1 hexp.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨ht0, ht1, by norm_num, by norm_num, hph.1, hph.2.1, by norm_num, hph.2.2.1, hph.2.2.2⟩


private lemma phaseAt_645 :
    phaseHolds (((645 : ℝ) / 1000)) ((730650803 : ℝ) / 1000000000) ((365331323 : ℝ) / 500000000) ((555932791 : ℝ) / 1000000000) ((34753887 : ℝ) / 62500000) := by
  have ht0 : (0 : ℝ) < ((645 : ℝ) / 1000) := by norm_num
  have ht1 : ((645 : ℝ) / 1000) ≤ 1 := by norm_num
  obtain ⟨hs7, hs5, hc6, hc4⟩ := trigPoly_bounds ht0
  have hsLo : ((120239677 : ℝ) / 200000000) < sin (((645 : ℝ) / 1000)) := by
    have hnum : ((120239677 : ℝ) / 200000000) <
        ((645 : ℝ) / 1000) - (((645 : ℝ) / 1000)) ^ 3 / 6 + (((645 : ℝ) / 1000)) ^ 5 / 120 - (((645 : ℝ) / 1000)) ^ 7 / 5040 := by norm_num
    linarith
  have hsHi : sin (((645 : ℝ) / 1000)) < ((601207601 : ℝ) / 1000000000) := by
    have hnum : ((645 : ℝ) / 1000) - (((645 : ℝ) / 1000)) ^ 3 / 6 + (((645 : ℝ) / 1000)) ^ 5 / 120 < ((601207601 : ℝ) / 1000000000) := by norm_num
    linarith
  have hcLo : ((799099027 : ℝ) / 1000000000) < cos (((645 : ℝ) / 1000)) := by
    have hnum : ((799099027 : ℝ) / 1000000000) <
        1 - (((645 : ℝ) / 1000)) ^ 2 / 2 + (((645 : ℝ) / 1000)) ^ 4 / 24 - (((645 : ℝ) / 1000)) ^ 6 / 720 := by norm_num
    linarith
  have hcHi : cos (((645 : ℝ) / 1000)) < ((399599517 : ℝ) / 500000000) := by
    have hnum : 1 - (((645 : ℝ) / 1000)) ^ 2 / 2 + (((645 : ℝ) / 1000)) ^ 4 / 24 < ((399599517 : ℝ) / 500000000) := by norm_num
    linarith
  have hexp := exp_between (x := ((645 : ℝ) / 1000)) (n := 8) (lo := ((1905985393 : ℝ) / 1000000000)) (hi := ((952993533 : ℝ) / 500000000))
    ht0.le ht1 (by decide)
    (by norm_num [sum_range_succ, Nat.factorial])
    (by norm_num [sum_range_succ, Nat.factorial])
  have hph : ((730650803 : ℝ) / 1000000000) < chordAmp (((645 : ℝ) / 1000)) ∧ chordAmp (((645 : ℝ) / 1000)) < ((365331323 : ℝ) / 500000000) ∧
      ((555932791 : ℝ) / 1000000000) < gammaSEqual (((645 : ℝ) / 1000)) ∧ gammaSEqual (((645 : ℝ) / 1000)) < ((34753887 : ℝ) / 62500000) := by
    exact phase_bounds ht0 ht1 hsLo hsHi hcLo hcHi hexp.1 hexp.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨ht0, ht1, by norm_num, by norm_num, hph.1, hph.2.1, by norm_num, hph.2.2.1, hph.2.2.2⟩


private lemma phaseAt_660 :
    phaseHolds (((660 : ℝ) / 1000)) ((93946417 : ℝ) / 125000000) ((751585387 : ℝ) / 1000000000) ((533698449 : ℝ) / 1000000000) ((266924317 : ℝ) / 500000000) := by
  have ht0 : (0 : ℝ) < ((660 : ℝ) / 1000) := by norm_num
  have ht1 : ((660 : ℝ) / 1000) ≤ 1 := by norm_num
  obtain ⟨hs7, hs5, hc6, hc4⟩ := trigPoly_bounds ht0
  have hsLo : ((306558393 : ℝ) / 500000000) < sin (((660 : ℝ) / 1000)) := by
    have hnum : ((306558393 : ℝ) / 500000000) <
        ((660 : ℝ) / 1000) - (((660 : ℝ) / 1000)) ^ 3 / 6 + (((660 : ℝ) / 1000)) ^ 5 / 120 - (((660 : ℝ) / 1000)) ^ 7 / 5040 := by norm_num
    linarith
  have hsHi : sin (((660 : ℝ) / 1000)) < ((613127611 : ℝ) / 1000000000) := by
    have hnum : ((660 : ℝ) / 1000) - (((660 : ℝ) / 1000)) ^ 3 / 6 + (((660 : ℝ) / 1000)) ^ 5 / 120 < ((613127611 : ℝ) / 1000000000) := by norm_num
    linarith
  have hcLo : ((394995671 : ℝ) / 500000000) < cos (((660 : ℝ) / 1000)) := by
    have hnum : ((394995671 : ℝ) / 500000000) <
        1 - (((660 : ℝ) / 1000)) ^ 2 / 2 + (((660 : ℝ) / 1000)) ^ 4 / 24 - (((660 : ℝ) / 1000)) ^ 6 / 720 := by norm_num
    linarith
  have hcHi : cos (((660 : ℝ) / 1000)) < ((790106141 : ℝ) / 1000000000) := by
    have hnum : 1 - (((660 : ℝ) / 1000)) ^ 2 / 2 + (((660 : ℝ) / 1000)) ^ 4 / 24 < ((790106141 : ℝ) / 1000000000) := by norm_num
    linarith
  have hexp := exp_between (x := ((660 : ℝ) / 1000)) (n := 8) (lo := ((967395183 : ℝ) / 500000000)) (hi := ((241849047 : ℝ) / 125000000))
    ht0.le ht1 (by decide)
    (by norm_num [sum_range_succ, Nat.factorial])
    (by norm_num [sum_range_succ, Nat.factorial])
  have hph : ((93946417 : ℝ) / 125000000) < chordAmp (((660 : ℝ) / 1000)) ∧ chordAmp (((660 : ℝ) / 1000)) < ((751585387 : ℝ) / 1000000000) ∧
      ((533698449 : ℝ) / 1000000000) < gammaSEqual (((660 : ℝ) / 1000)) ∧ gammaSEqual (((660 : ℝ) / 1000)) < ((266924317 : ℝ) / 500000000) := by
    exact phase_bounds ht0 ht1 hsLo hsHi hcLo hcHi hexp.1 hexp.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨ht0, ht1, by norm_num, by norm_num, hph.1, hph.2.1, by norm_num, hph.2.2.1, hph.2.2.2⟩


private lemma phaseAt_679 :
    phaseHolds (((679 : ℝ) / 1000)) ((778432889 : ℝ) / 1000000000) ((778450253 : ℝ) / 1000000000) ((50462717 : ℝ) / 100000000) ((25240389 : ℝ) / 50000000) := by
  have ht0 : (0 : ℝ) < ((679 : ℝ) / 1000) := by norm_num
  have ht1 : ((679 : ℝ) / 1000) ≤ 1 := by norm_num
  obtain ⟨hs7, hs5, hc6, hc4⟩ := trigPoly_bounds ht0
  have hsLo : ((157003763 : ℝ) / 250000000) < sin (((679 : ℝ) / 1000)) := by
    have hnum : ((157003763 : ℝ) / 250000000) <
        ((679 : ℝ) / 1000) - (((679 : ℝ) / 1000)) ^ 3 / 6 + (((679 : ℝ) / 1000)) ^ 5 / 120 - (((679 : ℝ) / 1000)) ^ 7 / 5040 := by norm_num
    linarith
  have hsHi : sin (((679 : ℝ) / 1000)) < ((19625883 : ℝ) / 31250000) := by
    have hnum : ((679 : ℝ) / 1000) - (((679 : ℝ) / 1000)) ^ 3 / 6 + (((679 : ℝ) / 1000)) ^ 5 / 120 < ((19625883 : ℝ) / 31250000) := by norm_num
    linarith
  have hcLo : ((97275001 : ℝ) / 125000000) < cos (((679 : ℝ) / 1000)) := by
    have hnum : ((97275001 : ℝ) / 125000000) <
        1 - (((679 : ℝ) / 1000)) ^ 2 / 2 + (((679 : ℝ) / 1000)) ^ 4 / 24 - (((679 : ℝ) / 1000)) ^ 6 / 720 := by norm_num
    linarith
  have hcHi : cos (((679 : ℝ) / 1000)) < ((778336117 : ℝ) / 1000000000) := by
    have hnum : 1 - (((679 : ℝ) / 1000)) ^ 2 / 2 + (((679 : ℝ) / 1000)) ^ 4 / 24 < ((778336117 : ℝ) / 1000000000) := by norm_num
    linarith
  have hexp := exp_between (x := ((679 : ℝ) / 1000)) (n := 8) (lo := ((1971902369 : ℝ) / 1000000000)) (hi := ((1971904891 : ℝ) / 1000000000))
    ht0.le ht1 (by decide)
    (by norm_num [sum_range_succ, Nat.factorial])
    (by norm_num [sum_range_succ, Nat.factorial])
  have hph : ((778432889 : ℝ) / 1000000000) < chordAmp (((679 : ℝ) / 1000)) ∧ chordAmp (((679 : ℝ) / 1000)) < ((778450253 : ℝ) / 1000000000) ∧
      ((50462717 : ℝ) / 100000000) < gammaSEqual (((679 : ℝ) / 1000)) ∧ gammaSEqual (((679 : ℝ) / 1000)) < ((25240389 : ℝ) / 50000000) := by
    exact phase_bounds ht0 ht1 hsLo hsHi hcLo hcHi hexp.1 hexp.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨ht0, ht1, by norm_num, by norm_num, hph.1, hph.2.1, by norm_num, hph.2.2.1, hph.2.2.2⟩


private lemma phaseAt_715 :
    phaseHolds (((715 : ℝ) / 1000)) ((415231113 : ℝ) / 500000000) ((207621947 : ℝ) / 250000000) ((55838703 : ℝ) / 125000000) ((446962757 : ℝ) / 1000000000) := by
  have ht0 : (0 : ℝ) < ((715 : ℝ) / 1000) := by norm_num
  have ht1 : ((715 : ℝ) / 1000) ≤ 1 := by norm_num
  obtain ⟨hs7, hs5, hc6, hc4⟩ := trigPoly_bounds ht0
  have hsLo : ((327808641 : ℝ) / 500000000) < sin (((715 : ℝ) / 1000)) := by
    have hnum : ((327808641 : ℝ) / 500000000) <
        ((715 : ℝ) / 1000) - (((715 : ℝ) / 1000)) ^ 3 / 6 + (((715 : ℝ) / 1000)) ^ 5 / 120 - (((715 : ℝ) / 1000)) ^ 7 / 5040 := by norm_num
    linarith
  have hsHi : sin (((715 : ℝ) / 1000)) < ((327818119 : ℝ) / 500000000) := by
    have hnum : ((715 : ℝ) / 1000) - (((715 : ℝ) / 1000)) ^ 3 / 6 + (((715 : ℝ) / 1000)) ^ 5 / 120 < ((327818119 : ℝ) / 500000000) := by norm_num
    linarith
  have hcLo : ((188772889 : ℝ) / 250000000) < cos (((715 : ℝ) / 1000)) := by
    have hnum : ((188772889 : ℝ) / 250000000) <
        1 - (((715 : ℝ) / 1000)) ^ 2 / 2 + (((715 : ℝ) / 1000)) ^ 4 / 24 - (((715 : ℝ) / 1000)) ^ 6 / 720 := by norm_num
    linarith
  have hcHi : cos (((715 : ℝ) / 1000)) < ((377638563 : ℝ) / 500000000) := by
    have hnum : 1 - (((715 : ℝ) / 1000)) ^ 2 / 2 + (((715 : ℝ) / 1000)) ^ 4 / 24 < ((377638563 : ℝ) / 500000000) := by norm_num
    linarith
  have hexp := exp_between (x := ((715 : ℝ) / 1000)) (n := 8) (lo := ((2044182937 : ℝ) / 1000000000)) (hi := ((8176747 : ℝ) / 4000000))
    ht0.le ht1 (by decide)
    (by norm_num [sum_range_succ, Nat.factorial])
    (by norm_num [sum_range_succ, Nat.factorial])
  have hph : ((415231113 : ℝ) / 500000000) < chordAmp (((715 : ℝ) / 1000)) ∧ chordAmp (((715 : ℝ) / 1000)) < ((207621947 : ℝ) / 250000000) ∧
      ((55838703 : ℝ) / 125000000) < gammaSEqual (((715 : ℝ) / 1000)) ∧ gammaSEqual (((715 : ℝ) / 1000)) < ((446962757 : ℝ) / 1000000000) := by
    exact phase_bounds ht0 ht1 hsLo hsHi hcLo hcHi hexp.1 hexp.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨ht0, ht1, by norm_num, by norm_num, hph.1, hph.2.1, by norm_num, hph.2.2.1, hph.2.2.2⟩


private lemma phaseAt_735 :
    phaseHolds (((735 : ℝ) / 1000)) ((107502753 : ℝ) / 125000000) ((34402139 : ℝ) / 40000000) ((103224219 : ℝ) / 250000000) ((82640061 : ℝ) / 200000000) := by
  have ht0 : (0 : ℝ) < ((735 : ℝ) / 1000) := by norm_num
  have ht1 : ((735 : ℝ) / 1000) ≤ 1 := by norm_num
  obtain ⟨hs7, hs5, hc6, hc4⟩ := trigPoly_bounds ht0
  have hsLo : ((670586983 : ℝ) / 1000000000) < sin (((735 : ℝ) / 1000)) := by
    have hnum : ((670586983 : ℝ) / 1000000000) <
        ((735 : ℝ) / 1000) - (((735 : ℝ) / 1000)) ^ 3 / 6 + (((735 : ℝ) / 1000)) ^ 5 / 120 - (((735 : ℝ) / 1000)) ^ 7 / 5040 := by norm_num
    linarith
  have hsHi : sin (((735 : ℝ) / 1000)) < ((670609977 : ℝ) / 1000000000) := by
    have hnum : ((735 : ℝ) / 1000) - (((735 : ℝ) / 1000)) ^ 3 / 6 + (((735 : ℝ) / 1000)) ^ 5 / 120 < ((670609977 : ℝ) / 1000000000) := by norm_num
    linarith
  have hcLo : ((741828653 : ℝ) / 1000000000) < cos (((735 : ℝ) / 1000)) := by
    have hnum : ((741828653 : ℝ) / 1000000000) <
        1 - (((735 : ℝ) / 1000)) ^ 2 / 2 + (((735 : ℝ) / 1000)) ^ 4 / 24 - (((735 : ℝ) / 1000)) ^ 6 / 720 := by norm_num
    linarith
  have hcHi : cos (((735 : ℝ) / 1000)) < ((185511907 : ℝ) / 250000000) := by
    have hnum : 1 - (((735 : ℝ) / 1000)) ^ 2 / 2 + (((735 : ℝ) / 1000)) ^ 4 / 24 < ((185511907 : ℝ) / 250000000) := by norm_num
    linarith
  have hexp := exp_between (x := ((735 : ℝ) / 1000)) (n := 8) (lo := ((2085477317 : ℝ) / 1000000000)) (hi := ((2085482071 : ℝ) / 1000000000))
    ht0.le ht1 (by decide)
    (by norm_num [sum_range_succ, Nat.factorial])
    (by norm_num [sum_range_succ, Nat.factorial])
  have hph : ((107502753 : ℝ) / 125000000) < chordAmp (((735 : ℝ) / 1000)) ∧ chordAmp (((735 : ℝ) / 1000)) < ((34402139 : ℝ) / 40000000) ∧
      ((103224219 : ℝ) / 250000000) < gammaSEqual (((735 : ℝ) / 1000)) ∧ gammaSEqual (((735 : ℝ) / 1000)) < ((82640061 : ℝ) / 200000000) := by
    exact phase_bounds ht0 ht1 hsLo hsHi hcLo hcHi hexp.1 hexp.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨ht0, ht1, by norm_num, by norm_num, hph.1, hph.2.1, by norm_num, hph.2.2.1, hph.2.2.2⟩


private lemma phaseAt_791 :
    phaseHolds (((791 : ℝ) / 1000)) ((472671853 : ℝ) / 500000000) ((945398483 : ℝ) / 1000000000) ((1948831 : ℝ) / 6250000) ((312306221 : ℝ) / 1000000000) := by
  have ht0 : (0 : ℝ) < ((791 : ℝ) / 1000) := by norm_num
  have ht1 : ((791 : ℝ) / 1000) ≤ 1 := by norm_num
  obtain ⟨hs7, hs5, hc6, hc4⟩ := trigPoly_bounds ht0
  have hsLo : ((71105643 : ℝ) / 100000000) < sin (((791 : ℝ) / 1000)) := by
    have hnum : ((71105643 : ℝ) / 100000000) <
        ((791 : ℝ) / 1000) - (((791 : ℝ) / 1000)) ^ 3 / 6 + (((791 : ℝ) / 1000)) ^ 5 / 120 - (((791 : ℝ) / 1000)) ^ 7 / 5040 := by norm_num
    linarith
  have hsHi : sin (((791 : ℝ) / 1000)) < ((711094873 : ℝ) / 1000000000) := by
    have hnum : ((791 : ℝ) / 1000) - (((791 : ℝ) / 1000)) ^ 3 / 6 + (((791 : ℝ) / 1000)) ^ 5 / 120 < ((711094873 : ℝ) / 1000000000) := by norm_num
    linarith
  have hcLo : ((140626167 : ℝ) / 200000000) < cos (((791 : ℝ) / 1000)) := by
    have hnum : ((140626167 : ℝ) / 200000000) <
        1 - (((791 : ℝ) / 1000)) ^ 2 / 2 + (((791 : ℝ) / 1000)) ^ 4 / 24 - (((791 : ℝ) / 1000)) ^ 6 / 720 := by norm_num
    linarith
  have hcHi : cos (((791 : ℝ) / 1000)) < ((70347103 : ℝ) / 100000000) := by
    have hnum : 1 - (((791 : ℝ) / 1000)) ^ 2 / 2 + (((791 : ℝ) / 1000)) ^ 4 / 24 < ((70347103 : ℝ) / 100000000) := by norm_num
    linarith
  have hexp := exp_between (x := ((791 : ℝ) / 1000)) (n := 8) (lo := ((441118497 : ℝ) / 200000000)) (hi := ((1102800519 : ℝ) / 500000000))
    ht0.le ht1 (by decide)
    (by norm_num [sum_range_succ, Nat.factorial])
    (by norm_num [sum_range_succ, Nat.factorial])
  have hph : ((472671853 : ℝ) / 500000000) < chordAmp (((791 : ℝ) / 1000)) ∧ chordAmp (((791 : ℝ) / 1000)) < ((945398483 : ℝ) / 1000000000) ∧
      ((1948831 : ℝ) / 6250000) < gammaSEqual (((791 : ℝ) / 1000)) ∧ gammaSEqual (((791 : ℝ) / 1000)) < ((312306221 : ℝ) / 1000000000) := by
    exact phase_bounds ht0 ht1 hsLo hsHi hcLo hcHi hexp.1 hexp.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨ht0, ht1, by norm_num, by norm_num, hph.1, hph.2.1, by norm_num, hph.2.2.1, hph.2.2.2⟩


private lemma phaseAt_847 :
    phaseHolds (((847 : ℝ) / 1000)) ((1034524729 : ℝ) / 1000000000) ((1034616961 : ℝ) / 1000000000) ((50236331 : ℝ) / 250000000) ((201724789 : ℝ) / 1000000000) := by
  have ht0 : (0 : ℝ) < ((847 : ℝ) / 1000) := by norm_num
  have ht1 : ((847 : ℝ) / 1000) ≤ 1 := by norm_num
  obtain ⟨hs7, hs5, hc6, hc4⟩ := trigPoly_bounds ht0
  have hsLo : ((749296463 : ℝ) / 1000000000) < sin (((847 : ℝ) / 1000)) := by
    have hnum : ((749296463 : ℝ) / 1000000000) <
        ((847 : ℝ) / 1000) - (((847 : ℝ) / 1000)) ^ 3 / 6 + (((847 : ℝ) / 1000)) ^ 5 / 120 - (((847 : ℝ) / 1000)) ^ 7 / 5040 := by norm_num
    linarith
  have hsHi : sin (((847 : ℝ) / 1000)) < ((187339629 : ℝ) / 250000000) := by
    have hnum : ((847 : ℝ) / 1000) - (((847 : ℝ) / 1000)) ^ 3 / 6 + (((847 : ℝ) / 1000)) ^ 5 / 120 < ((187339629 : ℝ) / 250000000) := by norm_num
    linarith
  have hcLo : ((82778437 : ℝ) / 125000000) < cos (((847 : ℝ) / 1000)) := by
    have hnum : ((82778437 : ℝ) / 125000000) <
        1 - (((847 : ℝ) / 1000)) ^ 2 / 2 + (((847 : ℝ) / 1000)) ^ 4 / 24 - (((847 : ℝ) / 1000)) ^ 6 / 720 := by norm_num
    linarith
  have hcHi : cos (((847 : ℝ) / 1000)) < ((4142127 : ℝ) / 6250000) := by
    have hnum : 1 - (((847 : ℝ) / 1000)) ^ 2 / 2 + (((847 : ℝ) / 1000)) ^ 4 / 24 < ((4142127 : ℝ) / 6250000) := by norm_num
    linarith
  have hexp := exp_between (x := ((847 : ℝ) / 1000)) (n := 8) (lo := ((2332623793 : ℝ) / 1000000000)) (hi := ((145789911 : ℝ) / 62500000))
    ht0.le ht1 (by decide)
    (by norm_num [sum_range_succ, Nat.factorial])
    (by norm_num [sum_range_succ, Nat.factorial])
  have hph : ((1034524729 : ℝ) / 1000000000) < chordAmp (((847 : ℝ) / 1000)) ∧ chordAmp (((847 : ℝ) / 1000)) < ((1034616961 : ℝ) / 1000000000) ∧
      ((50236331 : ℝ) / 250000000) < gammaSEqual (((847 : ℝ) / 1000)) ∧ gammaSEqual (((847 : ℝ) / 1000)) < ((201724789 : ℝ) / 1000000000) := by
    exact phase_bounds ht0 ht1 hsLo hsHi hcLo hcHi hexp.1 hexp.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨ht0, ht1, by norm_num, by norm_num, hph.1, hph.2.1, by norm_num, hph.2.2.1, hph.2.2.2⟩


private lemma phaseAt_903 :
    phaseHolds (((903 : ℝ) / 1000)) ((281913607 : ℝ) / 250000000) ((1127805213 : ℝ) / 1000000000) ((79849609 : ℝ) / 1000000000) ((81051351 : ℝ) / 1000000000) := by
  have ht0 : (0 : ℝ) < ((903 : ℝ) / 1000) := by norm_num
  have ht1 : ((903 : ℝ) / 1000) ≤ 1 := by norm_num
  obtain ⟨hs7, hs5, hc6, hc4⟩ := trigPoly_bounds ht0
  have hsLo : ((785187119 : ℝ) / 1000000000) < sin (((903 : ℝ) / 1000)) := by
    have hnum : ((785187119 : ℝ) / 1000000000) <
        ((903 : ℝ) / 1000) - (((903 : ℝ) / 1000)) ^ 3 / 6 + (((903 : ℝ) / 1000)) ^ 5 / 120 - (((903 : ℝ) / 1000)) ^ 7 / 5040 := by norm_num
    linarith
  have hsHi : sin (((903 : ℝ) / 1000)) < ((785284257 : ℝ) / 1000000000) := by
    have hnum : ((903 : ℝ) / 1000) - (((903 : ℝ) / 1000)) ^ 3 / 6 + (((903 : ℝ) / 1000)) ^ 5 / 120 < ((785284257 : ℝ) / 1000000000) := by norm_num
    linarith
  have hcLo : ((77405791 : ℝ) / 125000000) < cos (((903 : ℝ) / 1000)) := by
    have hnum : ((77405791 : ℝ) / 125000000) <
        1 - (((903 : ℝ) / 1000)) ^ 2 / 2 + (((903 : ℝ) / 1000)) ^ 4 / 24 - (((903 : ℝ) / 1000)) ^ 6 / 720 := by norm_num
    linarith
  have hcHi : cos (((903 : ℝ) / 1000)) < ((619999327 : ℝ) / 1000000000) := by
    have hnum : 1 - (((903 : ℝ) / 1000)) ^ 2 / 2 + (((903 : ℝ) / 1000)) ^ 4 / 24 < ((619999327 : ℝ) / 1000000000) := by norm_num
    linarith
  have hexp := exp_between (x := ((903 : ℝ) / 1000)) (n := 8) (lo := ((616742123 : ℝ) / 250000000)) (hi := ((2466993163 : ℝ) / 1000000000))
    ht0.le ht1 (by decide)
    (by norm_num [sum_range_succ, Nat.factorial])
    (by norm_num [sum_range_succ, Nat.factorial])
  have hph : ((281913607 : ℝ) / 250000000) < chordAmp (((903 : ℝ) / 1000)) ∧ chordAmp (((903 : ℝ) / 1000)) < ((1127805213 : ℝ) / 1000000000) ∧
      ((79849609 : ℝ) / 1000000000) < gammaSEqual (((903 : ℝ) / 1000)) ∧ gammaSEqual (((903 : ℝ) / 1000)) < ((81051351 : ℝ) / 1000000000) := by
    exact phase_bounds ht0 ht1 hsLo hsHi hcLo hcHi hexp.1 hexp.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨ht0, ht1, by norm_num, by norm_num, hph.1, hph.2.1, by norm_num, hph.2.2.1, hph.2.2.2⟩


private lemma phaseAt_924 :
    phaseHolds (((924 : ℝ) / 1000)) ((581803663 : ℝ) / 500000000) ((1163787393 : ℝ) / 1000000000) ((6341837 : ℝ) / 200000000) ((16557339 : ℝ) / 500000000) := by
  have ht0 : (0 : ℝ) < ((924 : ℝ) / 1000) := by norm_num
  have ht1 : ((924 : ℝ) / 1000) ≤ 1 := by norm_num
  obtain ⟨hs7, hs5, hc6, hc4⟩ := trigPoly_bounds ht0
  have hsLo : ((399008593 : ℝ) / 500000000) < sin (((924 : ℝ) / 1000)) := by
    have hnum : ((399008593 : ℝ) / 500000000) <
        ((924 : ℝ) / 1000) - (((924 : ℝ) / 1000)) ^ 3 / 6 + (((924 : ℝ) / 1000)) ^ 5 / 120 - (((924 : ℝ) / 1000)) ^ 7 / 5040 := by norm_num
    linarith
  have hsHi : sin (((924 : ℝ) / 1000)) < ((199532821 : ℝ) / 250000000) := by
    have hnum : ((924 : ℝ) / 1000) - (((924 : ℝ) / 1000)) ^ 3 / 6 + (((924 : ℝ) / 1000)) ^ 5 / 120 < ((199532821 : ℝ) / 250000000) := by norm_num
    linarith
  have hcLo : ((301309929 : ℝ) / 500000000) < cos (((924 : ℝ) / 1000)) := by
    have hnum : ((301309929 : ℝ) / 500000000) <
        1 - (((924 : ℝ) / 1000)) ^ 2 / 2 + (((924 : ℝ) / 1000)) ^ 4 / 24 - (((924 : ℝ) / 1000)) ^ 6 / 720 := by norm_num
    linarith
  have hcHi : cos (((924 : ℝ) / 1000)) < ((150871057 : ℝ) / 250000000) := by
    have hnum : 1 - (((924 : ℝ) / 1000)) ^ 2 / 2 + (((924 : ℝ) / 1000)) ^ 4 / 24 < ((150871057 : ℝ) / 250000000) := by norm_num
    linarith
  have hexp := exp_between (x := ((924 : ℝ) / 1000)) (n := 8) (lo := ((2519318159 : ℝ) / 1000000000)) (hi := ((2519347811 : ℝ) / 1000000000))
    ht0.le ht1 (by decide)
    (by norm_num [sum_range_succ, Nat.factorial])
    (by norm_num [sum_range_succ, Nat.factorial])
  have hph : ((581803663 : ℝ) / 500000000) < chordAmp (((924 : ℝ) / 1000)) ∧ chordAmp (((924 : ℝ) / 1000)) < ((1163787393 : ℝ) / 1000000000) ∧
      ((6341837 : ℝ) / 200000000) < gammaSEqual (((924 : ℝ) / 1000)) ∧ gammaSEqual (((924 : ℝ) / 1000)) < ((16557339 : ℝ) / 500000000) := by
    exact phase_bounds ht0 ht1 hsLo hsHi hcLo hcHi hexp.1 hexp.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨ht0, ht1, by norm_num, by norm_num, hph.1, hph.2.1, by norm_num, hph.2.2.1, hph.2.2.2⟩

set_option maxHeartbeats 0 in
-- The cleared gap is a rational with several hundred bits.
private lemma deriv_pos_Ioc_350_360 {x : ℝ}
    (hx : x ∈ Ioc ((350 : ℝ) / 1000) ((360 : ℝ) / 1000)) :
    0 < deriv dodecaResponse x := by
  have hb1 : ((360 : ℝ) / 1000) ≤ 1 := by norm_num
  have hbW : ((360 : ℝ) / 1000) < dodecaWall := lt_trans (by norm_num) dodecaWall_gt_thirtyThree_fiftieths
  have hwall : x < dodecaWall := lt_of_le_of_lt hx.2 hbW
  have hx0 : 0 < x := lt_trans (by norm_num) hx.1
  have hxI : x ∈ Ioo (0 : ℝ) dodecaWall := ⟨hx0, hwall⟩
  have hx1 : x ≤ 1 := le_trans hx.2 hb1
  have hbR : ((360 : ℝ) / 1000) < resonanceRoot1 := lt_trans hbW dodecaWall_lt_firstNode
  have hsc := dodeca_scales_lt_near
  rcases phaseAt_350 with
    ⟨a0, a1, _, aA0, aAlo, aAhi, aG0, aGlt, aGgt⟩
  rcases phaseAt_360 with
    ⟨b0, b1, _, bA0, bAlo, bAhi, bG0, bGlt, bGgt⟩
  rcases phaseAt_490 with
    ⟨n0, n1, _, nA0, nAlo, nAhi, nG0, nGlt, nGgt⟩
  rcases phaseAt_303 with
    ⟨p30, p31, _, p3A0, p3Alo, p3Ahi, p3G0, p3Glt, p3Ggt⟩
  rcases phaseAt_312 with
    ⟨q30, q31, _, q3A0, q3Alo, q3Ahi, q3G0, q3Glt, q3Ggt⟩
  rcases phaseAt_214 with
    ⟨p60, p61, _, p6A0, p6Alo, p6Ahi, p6G0, p6Glt, p6Ggt⟩
  rcases phaseAt_221 with
    ⟨q60, q61, _, q6A0, q6Alo, q6Ahi, q6G0, q6Glt, q6Ggt⟩
  rcases phaseAt_187 with
    ⟨pF0, pF1, _, pFA0, pFAlo, pFAhi, pFG0, pFGlt, pFGgt⟩
  rcases phaseAt_193 with
    ⟨qF0, qF1, _, qFA0, qFAlo, qFAhi, qFG0, qFGlt, qFGgt⟩
  rcases phaseAt_175 with
    ⟨pH0, pH1, _, pHA0, pHAlo, pHAhi, pHG0, pHGlt, pHGgt⟩
  rcases phaseAt_180 with
    ⟨qH0, qH1, _, qHA0, qHAlo, qHAhi, qHG0, qHGlt, qHGgt⟩
  have hN := near_lower
    a0 hx0 hx.1 hx1 hx.2 hbR n0 n1
    (by norm_num : ((490 : ℝ) / 1000) ≤ (700629 : ℝ) / 500000 * ((350 : ℝ) / 1000))
    aAlo aA0 nAlo nA0 nGgt (lt_trans nG0 nGlt)
    bAhi (lt_trans bA0 bAlo) bGlt bG0 (lt_trans (lt_trans bA0 bAlo) bAhi)
    (by norm_num : (0 : ℝ) < (700629 : ℝ) / 500000 * (((27113277 : ℝ) / 31250000) / ((600559 : ℝ) / 1600000)) - ((750468683 : ℝ) / 1000000000) / ((528264007 : ℝ) / 1000000000))
    hxI
  have h3 := far_upper
    (c := sqrt 3 / 2) (cLo := ((34641 : ℝ) / 40000)) (cHi := ((433013 : ℝ) / 500000)) (k := 3 * sqrt 3 / 2) (kHi := 3 * ((433013 : ℝ) / 500000))
    a0 hx0 hx.1 hx.2 hb1 hbR p30 q31
    (lt_trans (by norm_num) sqrt_three_div_two_gt_34641) (sqrt_three_div_two_lt_one) (sqrt_three_div_two_gt_34641.le) (sqrt_three_div_two_lt_433013.le) (by positivity) (by norm_num) (s3_weight_le)
    (by norm_num : ((303 : ℝ) / 1000) ≤ ((34641 : ℝ) / 40000) * ((350 : ℝ) / 1000))
    (by norm_num : ((433013 : ℝ) / 500000) * ((360 : ℝ) / 1000) ≤ ((312 : ℝ) / 1000))
    bAhi (lt_trans bA0 bAlo) bGlt p3Alo p3A0 p3Ggt (lt_trans p3G0 p3Glt)
    q3Ahi q3Glt q3G0 bG0 (lt_trans (lt_trans bA0 bAlo) bAhi)
    (by norm_num : (0 : ℝ) < ((906795937 : ℝ) / 1000000000) / ((78046801 : ℝ) / 250000000) - ((34641 : ℝ) / 40000) * (((27113277 : ℝ) / 31250000) / ((600559 : ℝ) / 1600000)))
    hsc.1.le hxI
  have h6 := far_upper
    (c := sqrt 6 / 4) (cLo := ((153093 : ℝ) / 250000)) (cHi := ((612373 : ℝ) / 1000000)) (k := 3 * sqrt 6 / 4) (kHi := 3 * ((612373 : ℝ) / 1000000))
    a0 hx0 hx.1 hx.2 hb1 hbR p60 q61
    (lt_trans (by norm_num) sqrt_six_div_four_gt_153093) (sqrt_six_div_four_lt_one) (sqrt_six_div_four_gt_153093.le) (sqrt_six_div_four_lt_612373.le) (by positivity) (by norm_num) (s6_weight_le)
    (by norm_num : ((214 : ℝ) / 1000) ≤ ((153093 : ℝ) / 250000) * ((350 : ℝ) / 1000))
    (by norm_num : ((612373 : ℝ) / 1000000) * ((360 : ℝ) / 1000) ≤ ((221 : ℝ) / 1000))
    bAhi (lt_trans bA0 bAlo) bGlt p6Alo p6A0 p6Ggt (lt_trans p6G0 p6Glt)
    q6Ahi q6Glt q6G0 bG0 (lt_trans (lt_trans bA0 bAlo) bAhi)
    (by norm_num : (0 : ℝ) < ((953855661 : ℝ) / 1000000000) / ((217251787 : ℝ) / 1000000000) - ((153093 : ℝ) / 250000) * (((27113277 : ℝ) / 31250000) / ((600559 : ℝ) / 1600000)))
    hsc.2.1.le hxI
  have hF := far_upper
    (c := dodecaFarScale) (cLo := ((535233 : ℝ) / 1000000)) (cHi := ((267617 : ℝ) / 500000)) (k := 3 / 2 * dodecaFarScale) (kHi := 3 / 2 * ((267617 : ℝ) / 500000))
    a0 hx0 hx.1 hx.2 hb1 hbR pF0 qF1
    (lt_trans (by norm_num) dodecaFarScale_gt_535233) (dodecaFarScale_lt_one) (dodecaFarScale_gt_535233.le) (dodecaFarScale_lt_267617.le) (mul_pos (by norm_num : (0 : ℝ) < 3 / 2) (lt_trans (by norm_num) dodecaFarScale_gt_535233)) (by norm_num) (far_weight_le)
    (by norm_num : ((187 : ℝ) / 1000) ≤ ((535233 : ℝ) / 1000000) * ((350 : ℝ) / 1000))
    (by norm_num : ((267617 : ℝ) / 500000) * ((360 : ℝ) / 1000) ≤ ((193 : ℝ) / 1000))
    bAhi (lt_trans bA0 bAlo) bGlt pFAlo pFA0 pFGgt (lt_trans pFG0 pFGlt)
    qFAhi qFGlt qFG0 bG0 (lt_trans (lt_trans bA0 bAlo) bAhi)
    (by norm_num : (0 : ℝ) < ((964827733 : ℝ) / 1000000000) / ((94586049 : ℝ) / 500000000) - ((535233 : ℝ) / 1000000) * (((27113277 : ℝ) / 31250000) / ((600559 : ℝ) / 1600000)))
    hsc.2.2.1.le hxI
  have hH := far_upper
    (c := (1 / 2)) (cLo := (1 / 2)) (cHi := (1 / 2)) (k := (1 / 4)) (kHi := (1 / 4))
    a0 hx0 hx.1 hx.2 hb1 hbR pH0 qH1
    (by norm_num) (by norm_num) (le_rfl) (le_rfl) (by norm_num) (by norm_num) (le_rfl)
    (by norm_num : ((175 : ℝ) / 1000) ≤ (1 / 2) * ((350 : ℝ) / 1000))
    (by norm_num : (1 / 2) * ((360 : ℝ) / 1000) ≤ ((180 : ℝ) / 1000))
    bAhi (lt_trans bA0 bAlo) bGlt pHAlo pHA0 pHGgt (lt_trans pHG0 pHGlt)
    qHAhi qHGlt qHG0 bG0 (lt_trans (lt_trans bA0 bAlo) bAhi)
    (by norm_num : (0 : ℝ) < ((484609523 : ℝ) / 500000000) / ((88390489 : ℝ) / 500000000) - (1 / 2) * (((27113277 : ℝ) / 31250000) / ((600559 : ℝ) / 1600000)))
    hsc.2.2.2.le hxI
  exact deriv_pos_of_gap hxI hN h3 h6 hF hH (by norm_num)

set_option maxHeartbeats 0 in
-- The cleared gap is a rational with several hundred bits.
private lemma deriv_pos_Ioc_360_375 {x : ℝ}
    (hx : x ∈ Ioc ((360 : ℝ) / 1000) ((375 : ℝ) / 1000)) :
    0 < deriv dodecaResponse x := by
  have hb1 : ((375 : ℝ) / 1000) ≤ 1 := by norm_num
  have hbW : ((375 : ℝ) / 1000) < dodecaWall := lt_trans (by norm_num) dodecaWall_gt_thirtyThree_fiftieths
  have hwall : x < dodecaWall := lt_of_le_of_lt hx.2 hbW
  have hx0 : 0 < x := lt_trans (by norm_num) hx.1
  have hxI : x ∈ Ioo (0 : ℝ) dodecaWall := ⟨hx0, hwall⟩
  have hx1 : x ≤ 1 := le_trans hx.2 hb1
  have hbR : ((375 : ℝ) / 1000) < resonanceRoot1 := lt_trans hbW dodecaWall_lt_firstNode
  have hsc := dodeca_scales_lt_near
  rcases phaseAt_360 with
    ⟨a0, a1, _, aA0, aAlo, aAhi, aG0, aGlt, aGgt⟩
  rcases phaseAt_375 with
    ⟨b0, b1, _, bA0, bAlo, bAhi, bG0, bGlt, bGgt⟩
  rcases phaseAt_504 with
    ⟨n0, n1, _, nA0, nAlo, nAhi, nG0, nGlt, nGgt⟩
  rcases phaseAt_311 with
    ⟨p30, p31, _, p3A0, p3Alo, p3Ahi, p3G0, p3Glt, p3Ggt⟩
  rcases phaseAt_325 with
    ⟨q30, q31, _, q3A0, q3Alo, q3Ahi, q3G0, q3Glt, q3Ggt⟩
  rcases phaseAt_220 with
    ⟨p60, p61, _, p6A0, p6Alo, p6Ahi, p6G0, p6Glt, p6Ggt⟩
  rcases phaseAt_230 with
    ⟨q60, q61, _, q6A0, q6Alo, q6Ahi, q6G0, q6Glt, q6Ggt⟩
  rcases phaseAt_192 with
    ⟨pF0, pF1, _, pFA0, pFAlo, pFAhi, pFG0, pFGlt, pFGgt⟩
  rcases phaseAt_201 with
    ⟨qF0, qF1, _, qFA0, qFAlo, qFAhi, qFG0, qFGlt, qFGgt⟩
  rcases phaseAt_180 with
    ⟨pH0, pH1, _, pHA0, pHAlo, pHAhi, pHG0, pHGlt, pHGgt⟩
  rcases phaseAt_188 with
    ⟨qH0, qH1, _, qHA0, qHAlo, qHAhi, qHG0, qHGlt, qHGgt⟩
  have hN := near_lower
    a0 hx0 hx.1 hx1 hx.2 hbR n0 n1
    (by norm_num : ((504 : ℝ) / 1000) ≤ (700629 : ℝ) / 500000 * ((360 : ℝ) / 1000))
    aAlo aA0 nAlo nA0 nGgt (lt_trans nG0 nGlt)
    bAhi (lt_trans bA0 bAlo) bGlt bG0 (lt_trans (lt_trans bA0 bAlo) bAhi)
    (by norm_num : (0 : ℝ) < (700629 : ℝ) / 500000 * (((428055027 : ℝ) / 500000000) / ((98082377 : ℝ) / 250000000)) - ((735439453 : ℝ) / 1000000000) / ((545577601 : ℝ) / 1000000000))
    hxI
  have h3 := far_upper
    (c := sqrt 3 / 2) (cLo := ((34641 : ℝ) / 40000)) (cHi := ((433013 : ℝ) / 500000)) (k := 3 * sqrt 3 / 2) (kHi := 3 * ((433013 : ℝ) / 500000))
    a0 hx0 hx.1 hx.2 hb1 hbR p30 q31
    (lt_trans (by norm_num) sqrt_three_div_two_gt_34641) (sqrt_three_div_two_lt_one) (sqrt_three_div_two_gt_34641.le) (sqrt_three_div_two_lt_433013.le) (by positivity) (by norm_num) (s3_weight_le)
    (by norm_num : ((311 : ℝ) / 1000) ≤ ((34641 : ℝ) / 40000) * ((360 : ℝ) / 1000))
    (by norm_num : ((433013 : ℝ) / 500000) * ((375 : ℝ) / 1000) ≤ ((325 : ℝ) / 1000))
    bAhi (lt_trans bA0 bAlo) bGlt p3Alo p3A0 p3Ggt (lt_trans p3G0 p3Glt)
    q3Ahi q3Glt q3G0 bG0 (lt_trans (lt_trans bA0 bAlo) bAhi)
    (by norm_num : (0 : ℝ) < ((901731249 : ℝ) / 1000000000) / ((320929317 : ℝ) / 1000000000) - ((34641 : ℝ) / 40000) * (((428055027 : ℝ) / 500000000) / ((98082377 : ℝ) / 250000000)))
    hsc.1.le hxI
  have h6 := far_upper
    (c := sqrt 6 / 4) (cLo := ((153093 : ℝ) / 250000)) (cHi := ((612373 : ℝ) / 1000000)) (k := 3 * sqrt 6 / 4) (kHi := 3 * ((612373 : ℝ) / 1000000))
    a0 hx0 hx.1 hx.2 hb1 hbR p60 q61
    (lt_trans (by norm_num) sqrt_six_div_four_gt_153093) (sqrt_six_div_four_lt_one) (sqrt_six_div_four_gt_153093.le) (sqrt_six_div_four_lt_612373.le) (by positivity) (by norm_num) (s6_weight_le)
    (by norm_num : ((220 : ℝ) / 1000) ≤ ((153093 : ℝ) / 250000) * ((360 : ℝ) / 1000))
    (by norm_num : ((612373 : ℝ) / 1000000) * ((375 : ℝ) / 1000) ≤ ((230 : ℝ) / 1000))
    bAhi (lt_trans bA0 bAlo) bGlt p6Alo p6A0 p6Ggt (lt_trans p6G0 p6Glt)
    q6Ahi q6Glt q6G0 bG0 (lt_trans (lt_trans bA0 bAlo) bAhi)
    (by norm_num : (0 : ℝ) < ((475605499 : ℝ) / 500000000) / ((111766057 : ℝ) / 500000000) - ((153093 : ℝ) / 250000) * (((428055027 : ℝ) / 500000000) / ((98082377 : ℝ) / 250000000)))
    hsc.2.1.le hxI
  have hF := far_upper
    (c := dodecaFarScale) (cLo := ((535233 : ℝ) / 1000000)) (cHi := ((267617 : ℝ) / 500000)) (k := 3 / 2 * dodecaFarScale) (kHi := 3 / 2 * ((267617 : ℝ) / 500000))
    a0 hx0 hx.1 hx.2 hb1 hbR pF0 qF1
    (lt_trans (by norm_num) dodecaFarScale_gt_535233) (dodecaFarScale_lt_one) (dodecaFarScale_gt_535233.le) (dodecaFarScale_lt_267617.le) (mul_pos (by norm_num : (0 : ℝ) < 3 / 2) (lt_trans (by norm_num) dodecaFarScale_gt_535233)) (by norm_num) (far_weight_le)
    (by norm_num : ((192 : ℝ) / 1000) ≤ ((535233 : ℝ) / 1000000) * ((360 : ℝ) / 1000))
    (by norm_num : ((267617 : ℝ) / 500000) * ((375 : ℝ) / 1000) ≤ ((201 : ℝ) / 1000))
    bAhi (lt_trans bA0 bAlo) bGlt pFAlo pFA0 pFGgt (lt_trans pFG0 pFGlt)
    qFAhi qFGlt qFG0 bG0 (lt_trans (lt_trans bA0 bAlo) bAhi)
    (by norm_num : (0 : ℝ) < ((481455069 : ℝ) / 500000000) / ((97175291 : ℝ) / 500000000) - ((535233 : ℝ) / 1000000) * (((428055027 : ℝ) / 500000000) / ((98082377 : ℝ) / 250000000)))
    hsc.2.2.1.le hxI
  have hH := far_upper
    (c := (1 / 2)) (cLo := (1 / 2)) (cHi := (1 / 2)) (k := (1 / 4)) (kHi := (1 / 4))
    a0 hx0 hx.1 hx.2 hb1 hbR pH0 qH1
    (by norm_num) (by norm_num) (le_rfl) (le_rfl) (by norm_num) (by norm_num) (le_rfl)
    (by norm_num : ((180 : ℝ) / 1000) ≤ (1 / 2) * ((360 : ℝ) / 1000))
    (by norm_num : (1 / 2) * ((375 : ℝ) / 1000) ≤ ((188 : ℝ) / 1000))
    bAhi (lt_trans bA0 bAlo) bGlt pHAlo pHA0 pHGgt (lt_trans pHG0 pHGlt)
    qHAhi qHGlt qHG0 bG0 (lt_trans (lt_trans bA0 bAlo) bAhi)
    (by norm_num : (0 : ℝ) < ((241856367 : ℝ) / 250000000) / ((181937691 : ℝ) / 1000000000) - (1 / 2) * (((428055027 : ℝ) / 500000000) / ((98082377 : ℝ) / 250000000)))
    hsc.2.2.2.le hxI
  exact deriv_pos_of_gap hxI hN h3 h6 hF hH (by norm_num)

set_option maxHeartbeats 0 in
-- The cleared gap is a rational with several hundred bits.
private lemma deriv_pos_Ioc_375_395 {x : ℝ}
    (hx : x ∈ Ioc ((375 : ℝ) / 1000) ((395 : ℝ) / 1000)) :
    0 < deriv dodecaResponse x := by
  have hb1 : ((395 : ℝ) / 1000) ≤ 1 := by norm_num
  have hbW : ((395 : ℝ) / 1000) < dodecaWall := lt_trans (by norm_num) dodecaWall_gt_thirtyThree_fiftieths
  have hwall : x < dodecaWall := lt_of_le_of_lt hx.2 hbW
  have hx0 : 0 < x := lt_trans (by norm_num) hx.1
  have hxI : x ∈ Ioo (0 : ℝ) dodecaWall := ⟨hx0, hwall⟩
  have hx1 : x ≤ 1 := le_trans hx.2 hb1
  have hbR : ((395 : ℝ) / 1000) < resonanceRoot1 := lt_trans hbW dodecaWall_lt_firstNode
  have hsc := dodeca_scales_lt_near
  rcases phaseAt_375 with
    ⟨a0, a1, _, aA0, aAlo, aAhi, aG0, aGlt, aGgt⟩
  rcases phaseAt_395 with
    ⟨b0, b1, _, bA0, bAlo, bAhi, bG0, bGlt, bGgt⟩
  rcases phaseAt_525 with
    ⟨n0, n1, _, nA0, nAlo, nAhi, nG0, nGlt, nGgt⟩
  rcases phaseAt_324 with
    ⟨p30, p31, _, p3A0, p3Alo, p3Ahi, p3G0, p3Glt, p3Ggt⟩
  rcases phaseAt_343 with
    ⟨q30, q31, _, q3A0, q3Alo, q3Ahi, q3G0, q3Glt, q3Ggt⟩
  rcases phaseAt_229 with
    ⟨p60, p61, _, p6A0, p6Alo, p6Ahi, p6G0, p6Glt, p6Ggt⟩
  rcases phaseAt_242 with
    ⟨q60, q61, _, q6A0, q6Alo, q6Ahi, q6G0, q6Glt, q6Ggt⟩
  rcases phaseAt_200 with
    ⟨pF0, pF1, _, pFA0, pFAlo, pFAhi, pFG0, pFGlt, pFGgt⟩
  rcases phaseAt_212 with
    ⟨qF0, qF1, _, qFA0, qFAlo, qFAhi, qFG0, qFGlt, qFGgt⟩
  rcases phaseAt_187 with
    ⟨pH0, pH1, _, pHA0, pHAlo, pHAhi, pHG0, pHGlt, pHGgt⟩
  rcases phaseAt_198 with
    ⟨qH0, qH1, _, qHA0, qHAlo, qHAhi, qHG0, qHGlt, qHGgt⟩
  have hN := near_lower
    a0 hx0 hx.1 hx1 hx.2 hbR n0 n1
    (by norm_num : ((525 : ℝ) / 1000) ≤ (700629 : ℝ) / 500000 * ((375 : ℝ) / 1000))
    aAlo aA0 nAlo nA0 nGgt (lt_trans nG0 nGlt)
    bAhi (lt_trans bA0 bAlo) bGlt bG0 (lt_trans (lt_trans bA0 bAlo) bAhi)
    (by norm_num : (0 : ℝ) < (700629 : ℝ) / 500000 * (((52497499 : ℝ) / 62500000) / ((207610359 : ℝ) / 500000000)) - ((711981591 : ℝ) / 1000000000) / ((57188751 : ℝ) / 100000000))
    hxI
  have h3 := far_upper
    (c := sqrt 3 / 2) (cLo := ((34641 : ℝ) / 40000)) (cHi := ((433013 : ℝ) / 500000)) (k := 3 * sqrt 3 / 2) (kHi := 3 * ((433013 : ℝ) / 500000))
    a0 hx0 hx.1 hx.2 hb1 hbR p30 q31
    (lt_trans (by norm_num) sqrt_three_div_two_gt_34641) (sqrt_three_div_two_lt_one) (sqrt_three_div_two_gt_34641.le) (sqrt_three_div_two_lt_433013.le) (by positivity) (by norm_num) (s3_weight_le)
    (by norm_num : ((324 : ℝ) / 1000) ≤ ((34641 : ℝ) / 40000) * ((375 : ℝ) / 1000))
    (by norm_num : ((433013 : ℝ) / 500000) * ((395 : ℝ) / 1000) ≤ ((343 : ℝ) / 1000))
    bAhi (lt_trans bA0 bAlo) bGlt p3Alo p3A0 p3Ggt (lt_trans p3G0 p3Glt)
    q3Ahi q3Glt q3G0 bG0 (lt_trans (lt_trans bA0 bAlo) bAhi)
    (by norm_num : (0 : ℝ) < ((55825121 : ℝ) / 62500000) / ((335217797 : ℝ) / 1000000000) - ((34641 : ℝ) / 40000) * (((52497499 : ℝ) / 62500000) / ((207610359 : ℝ) / 500000000)))
    hsc.1.le hxI
  have h6 := far_upper
    (c := sqrt 6 / 4) (cLo := ((153093 : ℝ) / 250000)) (cHi := ((612373 : ℝ) / 1000000)) (k := 3 * sqrt 6 / 4) (kHi := 3 * ((612373 : ℝ) / 1000000))
    a0 hx0 hx.1 hx.2 hb1 hbR p60 q61
    (lt_trans (by norm_num) sqrt_six_div_four_gt_153093) (sqrt_six_div_four_lt_one) (sqrt_six_div_four_gt_153093.le) (sqrt_six_div_four_lt_612373.le) (by positivity) (by norm_num) (s6_weight_le)
    (by norm_num : ((229 : ℝ) / 1000) ≤ ((153093 : ℝ) / 250000) * ((375 : ℝ) / 1000))
    (by norm_num : ((612373 : ℝ) / 1000000) * ((395 : ℝ) / 1000) ≤ ((242 : ℝ) / 1000))
    bAhi (lt_trans bA0 bAlo) bGlt p6Alo p6A0 p6Ggt (lt_trans p6G0 p6Glt)
    q6Ahi q6Glt q6G0 bG0 (lt_trans (lt_trans bA0 bAlo) bAhi)
    (by norm_num : (0 : ℝ) < ((947102469 : ℝ) / 1000000000) / ((232981951 : ℝ) / 1000000000) - ((153093 : ℝ) / 250000) * (((52497499 : ℝ) / 62500000) / ((207610359 : ℝ) / 500000000)))
    hsc.2.1.le hxI
  have hF := far_upper
    (c := dodecaFarScale) (cLo := ((535233 : ℝ) / 1000000)) (cHi := ((267617 : ℝ) / 500000)) (k := 3 / 2 * dodecaFarScale) (kHi := 3 / 2 * ((267617 : ℝ) / 500000))
    a0 hx0 hx.1 hx.2 hb1 hbR pF0 qF1
    (lt_trans (by norm_num) dodecaFarScale_gt_535233) (dodecaFarScale_lt_one) (dodecaFarScale_gt_535233.le) (dodecaFarScale_lt_267617.le) (mul_pos (by norm_num : (0 : ℝ) < 3 / 2) (lt_trans (by norm_num) dodecaFarScale_gt_535233)) (by norm_num) (far_weight_le)
    (by norm_num : ((200 : ℝ) / 1000) ≤ ((535233 : ℝ) / 1000000) * ((375 : ℝ) / 1000))
    (by norm_num : ((267617 : ℝ) / 500000) * ((395 : ℝ) / 1000) ≤ ((212 : ℝ) / 1000))
    bAhi (lt_trans bA0 bAlo) bGlt pFAlo pFA0 pFGgt (lt_trans pFG0 pFGlt)
    qFAhi qFGlt qFG0 bG0 (lt_trans (lt_trans bA0 bAlo) bAhi)
    (by norm_num : (0 : ℝ) < ((479867069 : ℝ) / 500000000) / ((101327989 : ℝ) / 500000000) - ((535233 : ℝ) / 1000000) * (((52497499 : ℝ) / 62500000) / ((207610359 : ℝ) / 500000000)))
    hsc.2.2.1.le hxI
  have hH := far_upper
    (c := (1 / 2)) (cLo := (1 / 2)) (cHi := (1 / 2)) (k := (1 / 4)) (kHi := (1 / 4))
    a0 hx0 hx.1 hx.2 hb1 hbR pH0 qH1
    (by norm_num) (by norm_num) (le_rfl) (le_rfl) (by norm_num) (by norm_num) (le_rfl)
    (by norm_num : ((187 : ℝ) / 1000) ≤ (1 / 2) * ((375 : ℝ) / 1000))
    (by norm_num : (1 / 2) * ((395 : ℝ) / 1000) ≤ ((198 : ℝ) / 1000))
    bAhi (lt_trans bA0 bAlo) bGlt pHAlo pHA0 pHGgt (lt_trans pHG0 pHGlt)
    qHAhi qHGlt qHG0 bG0 (lt_trans (lt_trans bA0 bAlo) bAhi)
    (by norm_num : (0 : ℝ) < ((964827733 : ℝ) / 1000000000) / ((94586049 : ℝ) / 500000000) - (1 / 2) * (((52497499 : ℝ) / 62500000) / ((207610359 : ℝ) / 500000000)))
    hsc.2.2.2.le hxI
  exact deriv_pos_of_gap hxI hN h3 h6 hF hH (by norm_num)

set_option maxHeartbeats 0 in
-- The cleared gap is a rational with several hundred bits.
private lemma deriv_pos_Ioc_395_415 {x : ℝ}
    (hx : x ∈ Ioc ((395 : ℝ) / 1000) ((415 : ℝ) / 1000)) :
    0 < deriv dodecaResponse x := by
  have hb1 : ((415 : ℝ) / 1000) ≤ 1 := by norm_num
  have hbW : ((415 : ℝ) / 1000) < dodecaWall := lt_trans (by norm_num) dodecaWall_gt_thirtyThree_fiftieths
  have hwall : x < dodecaWall := lt_of_le_of_lt hx.2 hbW
  have hx0 : 0 < x := lt_trans (by norm_num) hx.1
  have hxI : x ∈ Ioo (0 : ℝ) dodecaWall := ⟨hx0, hwall⟩
  have hx1 : x ≤ 1 := le_trans hx.2 hb1
  have hbR : ((415 : ℝ) / 1000) < resonanceRoot1 := lt_trans hbW dodecaWall_lt_firstNode
  have hsc := dodeca_scales_lt_near
  rcases phaseAt_395 with
    ⟨a0, a1, _, aA0, aAlo, aAhi, aG0, aGlt, aGgt⟩
  rcases phaseAt_415 with
    ⟨b0, b1, _, bA0, bAlo, bAhi, bG0, bGlt, bGgt⟩
  rcases phaseAt_553 with
    ⟨n0, n1, _, nA0, nAlo, nAhi, nG0, nGlt, nGgt⟩
  rcases phaseAt_342 with
    ⟨p30, p31, _, p3A0, p3Alo, p3Ahi, p3G0, p3Glt, p3Ggt⟩
  rcases phaseAt_360 with
    ⟨q30, q31, _, q3A0, q3Alo, q3Ahi, q3G0, q3Glt, q3Ggt⟩
  rcases phaseAt_241 with
    ⟨p60, p61, _, p6A0, p6Alo, p6Ahi, p6G0, p6Glt, p6Ggt⟩
  rcases phaseAt_255 with
    ⟨q60, q61, _, q6A0, q6Alo, q6Ahi, q6G0, q6Glt, q6Ggt⟩
  rcases phaseAt_211 with
    ⟨pF0, pF1, _, pFA0, pFAlo, pFAhi, pFG0, pFGlt, pFGgt⟩
  rcases phaseAt_223 with
    ⟨qF0, qF1, _, qFA0, qFAlo, qFAhi, qFG0, qFGlt, qFGgt⟩
  rcases phaseAt_197 with
    ⟨pH0, pH1, _, pHA0, pHAlo, pHAhi, pHG0, pHGlt, pHGgt⟩
  rcases phaseAt_208 with
    ⟨qH0, qH1, _, qHA0, qHAlo, qHAhi, qHG0, qHGlt, qHGgt⟩
  have hN := near_lower
    a0 hx0 hx.1 hx1 hx.2 hbR n0 n1
    (by norm_num : ((553 : ℝ) / 1000) ≤ (700629 : ℝ) / 500000 * ((395 : ℝ) / 1000))
    aAlo aA0 nAlo nA0 nGgt (lt_trans nG0 nGlt)
    bAhi (lt_trans bA0 bAlo) bGlt bG0 (lt_trans (lt_trans bA0 bAlo) bAhi)
    (by norm_num : (0 : ℝ) < (700629 : ℝ) / 500000 * (((411444153 : ℝ) / 500000000) / ((87682251 : ℝ) / 200000000)) - ((339485819 : ℝ) / 500000000) / ((607621891 : ℝ) / 1000000000))
    hxI
  have h3 := far_upper
    (c := sqrt 3 / 2) (cLo := ((34641 : ℝ) / 40000)) (cHi := ((433013 : ℝ) / 500000)) (k := 3 * sqrt 3 / 2) (kHi := 3 * ((433013 : ℝ) / 500000))
    a0 hx0 hx.1 hx.2 hb1 hbR p30 q31
    (lt_trans (by norm_num) sqrt_three_div_two_gt_34641) (sqrt_three_div_two_lt_one) (sqrt_three_div_two_gt_34641.le) (sqrt_three_div_two_lt_433013.le) (by positivity) (by norm_num) (s3_weight_le)
    (by norm_num : ((342 : ℝ) / 1000) ≤ ((34641 : ℝ) / 40000) * ((395 : ℝ) / 1000))
    (by norm_num : ((433013 : ℝ) / 500000) * ((415 : ℝ) / 1000) ≤ ((360 : ℝ) / 1000))
    bAhi (lt_trans bA0 bAlo) bGlt p3Alo p3A0 p3Ggt (lt_trans p3G0 p3Glt)
    q3Ahi q3Glt q3G0 bG0 (lt_trans (lt_trans bA0 bAlo) bAhi)
    (by norm_num : (0 : ℝ) < ((880776113 : ℝ) / 1000000000) / ((355177069 : ℝ) / 1000000000) - ((34641 : ℝ) / 40000) * (((411444153 : ℝ) / 500000000) / ((87682251 : ℝ) / 200000000)))
    hsc.1.le hxI
  have h6 := far_upper
    (c := sqrt 6 / 4) (cLo := ((153093 : ℝ) / 250000)) (cHi := ((612373 : ℝ) / 1000000)) (k := 3 * sqrt 6 / 4) (kHi := 3 * ((612373 : ℝ) / 1000000))
    a0 hx0 hx.1 hx.2 hb1 hbR p60 q61
    (lt_trans (by norm_num) sqrt_six_div_four_gt_153093) (sqrt_six_div_four_lt_one) (sqrt_six_div_four_gt_153093.le) (sqrt_six_div_four_lt_612373.le) (by positivity) (by norm_num) (s6_weight_le)
    (by norm_num : ((241 : ℝ) / 1000) ≤ ((153093 : ℝ) / 250000) * ((395 : ℝ) / 1000))
    (by norm_num : ((612373 : ℝ) / 1000000) * ((415 : ℝ) / 1000) ≤ ((255 : ℝ) / 1000))
    bAhi (lt_trans bA0 bAlo) bGlt p6Alo p6A0 p6Ggt (lt_trans p6G0 p6Glt)
    q6Ahi q6Glt q6G0 bG0 (lt_trans (lt_trans bA0 bAlo) bAhi)
    (by norm_num : (0 : ℝ) < ((94135923 : ℝ) / 100000000) / ((49127733 : ℝ) / 200000000) - ((153093 : ℝ) / 250000) * (((411444153 : ℝ) / 500000000) / ((87682251 : ℝ) / 200000000)))
    hsc.2.1.le hxI
  have hF := far_upper
    (c := dodecaFarScale) (cLo := ((535233 : ℝ) / 1000000)) (cHi := ((267617 : ℝ) / 500000)) (k := 3 / 2 * dodecaFarScale) (kHi := 3 / 2 * ((267617 : ℝ) / 500000))
    a0 hx0 hx.1 hx.2 hb1 hbR pF0 qF1
    (lt_trans (by norm_num) dodecaFarScale_gt_535233) (dodecaFarScale_lt_one) (dodecaFarScale_gt_535233.le) (dodecaFarScale_lt_267617.le) (mul_pos (by norm_num : (0 : ℝ) < 3 / 2) (lt_trans (by norm_num) dodecaFarScale_gt_535233)) (by norm_num) (far_weight_le)
    (by norm_num : ((211 : ℝ) / 1000) ≤ ((535233 : ℝ) / 1000000) * ((395 : ℝ) / 1000))
    (by norm_num : ((267617 : ℝ) / 500000) * ((415 : ℝ) / 1000) ≤ ((223 : ℝ) / 1000))
    bAhi (lt_trans bA0 bAlo) bGlt pFAlo pFA0 pFGgt (lt_trans pFG0 pFGlt)
    qFAhi qFGlt qFG0 bG0 (lt_trans (lt_trans bA0 bAlo) bAhi)
    (by norm_num : (0 : ℝ) < ((238787439 : ℝ) / 250000000) / ((214117339 : ℝ) / 1000000000) - ((535233 : ℝ) / 1000000) * (((411444153 : ℝ) / 500000000) / ((87682251 : ℝ) / 200000000)))
    hsc.2.2.1.le hxI
  have hH := far_upper
    (c := (1 / 2)) (cLo := (1 / 2)) (cHi := (1 / 2)) (k := (1 / 4)) (kHi := (1 / 4))
    a0 hx0 hx.1 hx.2 hb1 hbR pH0 qH1
    (by norm_num) (by norm_num) (le_rfl) (le_rfl) (by norm_num) (by norm_num) (le_rfl)
    (by norm_num : ((197 : ℝ) / 1000) ≤ (1 / 2) * ((395 : ℝ) / 1000))
    (by norm_num : (1 / 2) * ((415 : ℝ) / 1000) ≤ ((208 : ℝ) / 1000))
    bAhi (lt_trans bA0 bAlo) bGlt pHAlo pHA0 pHGgt (lt_trans pHG0 pHGlt)
    qHAhi qHGlt qHG0 bG0 (lt_trans (lt_trans bA0 bAlo) bAhi)
    (by norm_num : (0 : ℝ) < ((960940711 : ℝ) / 1000000000) / ((49884637 : ℝ) / 250000000) - (1 / 2) * (((411444153 : ℝ) / 500000000) / ((87682251 : ℝ) / 200000000)))
    hsc.2.2.2.le hxI
  exact deriv_pos_of_gap hxI hN h3 h6 hF hH (by norm_num)

set_option maxHeartbeats 0 in
-- The cleared gap is a rational with several hundred bits.
private lemma deriv_pos_Ioc_415_445 {x : ℝ}
    (hx : x ∈ Ioc ((415 : ℝ) / 1000) ((445 : ℝ) / 1000)) :
    0 < deriv dodecaResponse x := by
  have hb1 : ((445 : ℝ) / 1000) ≤ 1 := by norm_num
  have hbW : ((445 : ℝ) / 1000) < dodecaWall := lt_trans (by norm_num) dodecaWall_gt_thirtyThree_fiftieths
  have hwall : x < dodecaWall := lt_of_le_of_lt hx.2 hbW
  have hx0 : 0 < x := lt_trans (by norm_num) hx.1
  have hxI : x ∈ Ioo (0 : ℝ) dodecaWall := ⟨hx0, hwall⟩
  have hx1 : x ≤ 1 := le_trans hx.2 hb1
  have hbR : ((445 : ℝ) / 1000) < resonanceRoot1 := lt_trans hbW dodecaWall_lt_firstNode
  have hsc := dodeca_scales_lt_near
  rcases phaseAt_415 with
    ⟨a0, a1, _, aA0, aAlo, aAhi, aG0, aGlt, aGgt⟩
  rcases phaseAt_445 with
    ⟨b0, b1, _, bA0, bAlo, bAhi, bG0, bGlt, bGgt⟩
  rcases phaseAt_581 with
    ⟨n0, n1, _, nA0, nAlo, nAhi, nG0, nGlt, nGgt⟩
  rcases phaseAt_359 with
    ⟨p30, p31, _, p3A0, p3Alo, p3Ahi, p3G0, p3Glt, p3Ggt⟩
  rcases phaseAt_386 with
    ⟨q30, q31, _, q3A0, q3Alo, q3Ahi, q3G0, q3Glt, q3Ggt⟩
  rcases phaseAt_254 with
    ⟨p60, p61, _, p6A0, p6Alo, p6Ahi, p6G0, p6Glt, p6Ggt⟩
  rcases phaseAt_273 with
    ⟨q60, q61, _, q6A0, q6Alo, q6Ahi, q6G0, q6Glt, q6Ggt⟩
  rcases phaseAt_222 with
    ⟨pF0, pF1, _, pFA0, pFAlo, pFAhi, pFG0, pFGlt, pFGgt⟩
  rcases phaseAt_239 with
    ⟨qF0, qF1, _, qFA0, qFAlo, qFAhi, qFG0, qFGlt, qFGgt⟩
  rcases phaseAt_207 with
    ⟨pH0, pH1, _, pHA0, pHAlo, pHAhi, pHG0, pHGlt, pHGgt⟩
  rcases phaseAt_223 with
    ⟨qH0, qH1, _, qHA0, qHAlo, qHAhi, qHG0, qHGlt, qHGgt⟩
  have hN := near_lower
    a0 hx0 hx.1 hx1 hx.2 hbR n0 n1
    (by norm_num : ((581 : ℝ) / 1000) ≤ (700629 : ℝ) / 500000 * ((415 : ℝ) / 1000))
    aAlo aA0 nAlo nA0 nGgt (lt_trans nG0 nGlt)
    bAhi (lt_trans bA0 bAlo) bGlt bG0 (lt_trans (lt_trans bA0 bAlo) bAhi)
    (by norm_num : (0 : ℝ) < (700629 : ℝ) / 500000 * (((397762921 : ℝ) / 500000000) / ((473787343 : ℝ) / 1000000000)) - ((643942943 : ℝ) / 1000000000) / ((644132173 : ℝ) / 1000000000))
    hxI
  have h3 := far_upper
    (c := sqrt 3 / 2) (cLo := ((34641 : ℝ) / 40000)) (cHi := ((433013 : ℝ) / 500000)) (k := 3 * sqrt 3 / 2) (kHi := 3 * ((433013 : ℝ) / 500000))
    a0 hx0 hx.1 hx.2 hb1 hbR p30 q31
    (lt_trans (by norm_num) sqrt_three_div_two_gt_34641) (sqrt_three_div_two_lt_one) (sqrt_three_div_two_gt_34641.le) (sqrt_three_div_two_lt_433013.le) (by positivity) (by norm_num) (s3_weight_le)
    (by norm_num : ((359 : ℝ) / 1000) ≤ ((34641 : ℝ) / 40000) * ((415 : ℝ) / 1000))
    (by norm_num : ((433013 : ℝ) / 500000) * ((445 : ℝ) / 1000) ≤ ((386 : ℝ) / 1000))
    bAhi (lt_trans bA0 bAlo) bGlt p3Alo p3A0 p3Ggt (lt_trans p3G0 p3Glt)
    q3Ahi q3Glt q3G0 bG0 (lt_trans (lt_trans bA0 bAlo) bAhi)
    (by norm_num : (0 : ℝ) < ((868377679 : ℝ) / 1000000000) / ((37422277 : ℝ) / 100000000) - ((34641 : ℝ) / 40000) * (((397762921 : ℝ) / 500000000) / ((473787343 : ℝ) / 1000000000)))
    hsc.1.le hxI
  have h6 := far_upper
    (c := sqrt 6 / 4) (cLo := ((153093 : ℝ) / 250000)) (cHi := ((612373 : ℝ) / 1000000)) (k := 3 * sqrt 6 / 4) (kHi := 3 * ((612373 : ℝ) / 1000000))
    a0 hx0 hx.1 hx.2 hb1 hbR p60 q61
    (lt_trans (by norm_num) sqrt_six_div_four_gt_153093) (sqrt_six_div_four_lt_one) (sqrt_six_div_four_gt_153093.le) (sqrt_six_div_four_lt_612373.le) (by positivity) (by norm_num) (s6_weight_le)
    (by norm_num : ((254 : ℝ) / 1000) ≤ ((153093 : ℝ) / 250000) * ((415 : ℝ) / 1000))
    (by norm_num : ((612373 : ℝ) / 1000000) * ((445 : ℝ) / 1000) ≤ ((273 : ℝ) / 1000))
    bAhi (lt_trans bA0 bAlo) bGlt p6Alo p6A0 p6Ggt (lt_trans p6G0 p6Glt)
    q6Ahi q6Glt q6G0 bG0 (lt_trans (lt_trans bA0 bAlo) bAhi)
    (by norm_num : (0 : ℝ) < ((467396829 : ℝ) / 500000000) / ((51885401 : ℝ) / 200000000) - ((153093 : ℝ) / 250000) * (((397762921 : ℝ) / 500000000) / ((473787343 : ℝ) / 1000000000)))
    hsc.2.1.le hxI
  have hF := far_upper
    (c := dodecaFarScale) (cLo := ((535233 : ℝ) / 1000000)) (cHi := ((267617 : ℝ) / 500000)) (k := 3 / 2 * dodecaFarScale) (kHi := 3 / 2 * ((267617 : ℝ) / 500000))
    a0 hx0 hx.1 hx.2 hb1 hbR pF0 qF1
    (lt_trans (by norm_num) dodecaFarScale_gt_535233) (dodecaFarScale_lt_one) (dodecaFarScale_gt_535233.le) (dodecaFarScale_lt_267617.le) (mul_pos (by norm_num : (0 : ℝ) < 3 / 2) (lt_trans (by norm_num) dodecaFarScale_gt_535233)) (by norm_num) (far_weight_le)
    (by norm_num : ((222 : ℝ) / 1000) ≤ ((535233 : ℝ) / 1000000) * ((415 : ℝ) / 1000))
    (by norm_num : ((267617 : ℝ) / 500000) * ((445 : ℝ) / 1000) ≤ ((239 : ℝ) / 1000))
    bAhi (lt_trans bA0 bAlo) bGlt pFAlo pFA0 pFGgt (lt_trans pFG0 pFGlt)
    qFAhi qFGlt qFG0 bG0 (lt_trans (lt_trans bA0 bAlo) bAhi)
    (by norm_num : (0 : ℝ) < ((190062537 : ℝ) / 200000000) / ((225628999 : ℝ) / 1000000000) - ((535233 : ℝ) / 1000000) * (((397762921 : ℝ) / 500000000) / ((473787343 : ℝ) / 1000000000)))
    hsc.2.2.1.le hxI
  have hH := far_upper
    (c := (1 / 2)) (cLo := (1 / 2)) (cHi := (1 / 2)) (k := (1 / 4)) (kHi := (1 / 4))
    a0 hx0 hx.1 hx.2 hb1 hbR pH0 qH1
    (by norm_num) (by norm_num) (le_rfl) (le_rfl) (by norm_num) (by norm_num) (le_rfl)
    (by norm_num : ((207 : ℝ) / 1000) ≤ (1 / 2) * ((415 : ℝ) / 1000))
    (by norm_num : (1 / 2) * ((445 : ℝ) / 1000) ≤ ((223 : ℝ) / 1000))
    bAhi (lt_trans bA0 bAlo) bGlt pHAlo pHA0 pHGgt (lt_trans pHG0 pHGlt)
    qHAhi qHGlt qHG0 bG0 (lt_trans (lt_trans bA0 bAlo) bAhi)
    (by norm_num : (0 : ℝ) < ((478422991 : ℝ) / 500000000) / ((41988777 : ℝ) / 200000000) - (1 / 2) * (((397762921 : ℝ) / 500000000) / ((473787343 : ℝ) / 1000000000)))
    hsc.2.2.2.le hxI
  exact deriv_pos_of_gap hxI hN h3 h6 hF hH (by norm_num)

set_option maxHeartbeats 0 in
-- The cleared gap is a rational with several hundred bits.
private lemma deriv_pos_Ioc_445_485 {x : ℝ}
    (hx : x ∈ Ioc ((445 : ℝ) / 1000) ((485 : ℝ) / 1000)) :
    0 < deriv dodecaResponse x := by
  have hb1 : ((485 : ℝ) / 1000) ≤ 1 := by norm_num
  have hbW : ((485 : ℝ) / 1000) < dodecaWall := lt_trans (by norm_num) dodecaWall_gt_thirtyThree_fiftieths
  have hwall : x < dodecaWall := lt_of_le_of_lt hx.2 hbW
  have hx0 : 0 < x := lt_trans (by norm_num) hx.1
  have hxI : x ∈ Ioo (0 : ℝ) dodecaWall := ⟨hx0, hwall⟩
  have hx1 : x ≤ 1 := le_trans hx.2 hb1
  have hbR : ((485 : ℝ) / 1000) < resonanceRoot1 := lt_trans hbW dodecaWall_lt_firstNode
  have hsc := dodeca_scales_lt_near
  rcases phaseAt_445 with
    ⟨a0, a1, _, aA0, aAlo, aAhi, aG0, aGlt, aGgt⟩
  rcases phaseAt_485 with
    ⟨b0, b1, _, bA0, bAlo, bAhi, bG0, bGlt, bGgt⟩
  rcases phaseAt_623 with
    ⟨n0, n1, _, nA0, nAlo, nAhi, nG0, nGlt, nGgt⟩
  rcases phaseAt_385 with
    ⟨p30, p31, _, p3A0, p3Alo, p3Ahi, p3G0, p3Glt, p3Ggt⟩
  rcases phaseAt_421 with
    ⟨q30, q31, _, q3A0, q3Alo, q3Ahi, q3G0, q3Glt, q3Ggt⟩
  rcases phaseAt_272 with
    ⟨p60, p61, _, p6A0, p6Alo, p6Ahi, p6G0, p6Glt, p6Ggt⟩
  rcases phaseAt_298 with
    ⟨q60, q61, _, q6A0, q6Alo, q6Ahi, q6G0, q6Glt, q6Ggt⟩
  rcases phaseAt_238 with
    ⟨pF0, pF1, _, pFA0, pFAlo, pFAhi, pFG0, pFGlt, pFGgt⟩
  rcases phaseAt_260 with
    ⟨qF0, qF1, _, qFA0, qFAlo, qFAhi, qFG0, qFGlt, qFGgt⟩
  rcases phaseAt_222 with
    ⟨pH0, pH1, _, pHA0, pHAlo, pHAhi, pHG0, pHGlt, pHGgt⟩
  rcases phaseAt_243 with
    ⟨qH0, qH1, _, qHA0, qHAlo, qHAhi, qHG0, qHGlt, qHGgt⟩
  have hN := near_lower
    a0 hx0 hx.1 hx1 hx.2 hbR n0 n1
    (by norm_num : ((623 : ℝ) / 1000) ≤ (700629 : ℝ) / 500000 * ((445 : ℝ) / 1000))
    aAlo aA0 nAlo nA0 nGgt (lt_trans nG0 nGlt)
    bAhi (lt_trans bA0 bAlo) bGlt bG0 (lt_trans (lt_trans bA0 bAlo) bAhi)
    (by norm_num : (0 : ℝ) < (700629 : ℝ) / 500000 * (((75569823 : ℝ) / 100000000) / ((130531247 : ℝ) / 250000000)) - ((587519693 : ℝ) / 1000000000) / ((175103869 : ℝ) / 250000000))
    hxI
  have h3 := far_upper
    (c := sqrt 3 / 2) (cLo := ((34641 : ℝ) / 40000)) (cHi := ((433013 : ℝ) / 500000)) (k := 3 * sqrt 3 / 2) (kHi := 3 * ((433013 : ℝ) / 500000))
    a0 hx0 hx.1 hx.2 hb1 hbR p30 q31
    (lt_trans (by norm_num) sqrt_three_div_two_gt_34641) (sqrt_three_div_two_lt_one) (sqrt_three_div_two_gt_34641.le) (sqrt_three_div_two_lt_433013.le) (by positivity) (by norm_num) (s3_weight_le)
    (by norm_num : ((385 : ℝ) / 1000) ≤ ((34641 : ℝ) / 40000) * ((445 : ℝ) / 1000))
    (by norm_num : ((433013 : ℝ) / 500000) * ((485 : ℝ) / 1000) ≤ ((421 : ℝ) / 1000))
    bAhi (lt_trans bA0 bAlo) bGlt p3Alo p3A0 p3Ggt (lt_trans p3G0 p3Glt)
    q3Ahi q3Glt q3G0 bG0 (lt_trans (lt_trans bA0 bAlo) bAhi)
    (by norm_num : (0 : ℝ) < ((169630893 : ℝ) / 200000000) / ((403738263 : ℝ) / 1000000000) - ((34641 : ℝ) / 40000) * (((75569823 : ℝ) / 100000000) / ((130531247 : ℝ) / 250000000)))
    hsc.1.le hxI
  have h6 := far_upper
    (c := sqrt 6 / 4) (cLo := ((153093 : ℝ) / 250000)) (cHi := ((612373 : ℝ) / 1000000)) (k := 3 * sqrt 6 / 4) (kHi := 3 * ((612373 : ℝ) / 1000000))
    a0 hx0 hx.1 hx.2 hb1 hbR p60 q61
    (lt_trans (by norm_num) sqrt_six_div_four_gt_153093) (sqrt_six_div_four_lt_one) (sqrt_six_div_four_gt_153093.le) (sqrt_six_div_four_lt_612373.le) (by positivity) (by norm_num) (s6_weight_le)
    (by norm_num : ((272 : ℝ) / 1000) ≤ ((153093 : ℝ) / 250000) * ((445 : ℝ) / 1000))
    (by norm_num : ((612373 : ℝ) / 1000000) * ((485 : ℝ) / 1000) ≤ ((298 : ℝ) / 1000))
    bAhi (lt_trans bA0 bAlo) bGlt p6Alo p6A0 p6Ggt (lt_trans p6G0 p6Glt)
    q6Ahi q6Glt q6G0 bG0 (lt_trans (lt_trans bA0 bAlo) bAhi)
    (by norm_num : (0 : ℝ) < ((37004353 : ℝ) / 40000000) / ((278658079 : ℝ) / 1000000000) - ((153093 : ℝ) / 250000) * (((75569823 : ℝ) / 100000000) / ((130531247 : ℝ) / 250000000)))
    hsc.2.1.le hxI
  have hF := far_upper
    (c := dodecaFarScale) (cLo := ((535233 : ℝ) / 1000000)) (cHi := ((267617 : ℝ) / 500000)) (k := 3 / 2 * dodecaFarScale) (kHi := 3 / 2 * ((267617 : ℝ) / 500000))
    a0 hx0 hx.1 hx.2 hb1 hbR pF0 qF1
    (lt_trans (by norm_num) dodecaFarScale_gt_535233) (dodecaFarScale_lt_one) (dodecaFarScale_gt_535233.le) (dodecaFarScale_lt_267617.le) (mul_pos (by norm_num : (0 : ℝ) < 3 / 2) (lt_trans (by norm_num) dodecaFarScale_gt_535233)) (by norm_num) (far_weight_le)
    (by norm_num : ((238 : ℝ) / 1000) ≤ ((535233 : ℝ) / 1000000) * ((445 : ℝ) / 1000))
    (by norm_num : ((267617 : ℝ) / 500000) * ((485 : ℝ) / 1000) ≤ ((260 : ℝ) / 1000))
    bAhi (lt_trans bA0 bAlo) bGlt pFAlo pFA0 pFGgt (lt_trans pFG0 pFGlt)
    qFAhi qFGlt qFG0 bG0 (lt_trans (lt_trans bA0 bAlo) bAhi)
    (by norm_num : (0 : ℝ) < ((117852941 : ℝ) / 125000000) / ((242468233 : ℝ) / 1000000000) - ((535233 : ℝ) / 1000000) * (((75569823 : ℝ) / 100000000) / ((130531247 : ℝ) / 250000000)))
    hsc.2.2.1.le hxI
  have hH := far_upper
    (c := (1 / 2)) (cLo := (1 / 2)) (cHi := (1 / 2)) (k := (1 / 4)) (kHi := (1 / 4))
    a0 hx0 hx.1 hx.2 hb1 hbR pH0 qH1
    (by norm_num) (by norm_num) (le_rfl) (le_rfl) (by norm_num) (by norm_num) (le_rfl)
    (by norm_num : ((222 : ℝ) / 1000) ≤ (1 / 2) * ((445 : ℝ) / 1000))
    (by norm_num : (1 / 2) * ((485 : ℝ) / 1000) ≤ ((243 : ℝ) / 1000))
    bAhi (lt_trans bA0 bAlo) bGlt pHAlo pHA0 pHGgt (lt_trans pHG0 pHGlt)
    qHAhi qHGlt qHG0 bG0 (lt_trans (lt_trans bA0 bAlo) bAhi)
    (by norm_num : (0 : ℝ) < ((190062537 : ℝ) / 200000000) / ((225628999 : ℝ) / 1000000000) - (1 / 2) * (((75569823 : ℝ) / 100000000) / ((130531247 : ℝ) / 250000000)))
    hsc.2.2.2.le hxI
  exact deriv_pos_of_gap hxI hN h3 h6 hF hH (by norm_num)

set_option maxHeartbeats 0 in
-- The cleared gap is a rational with several hundred bits.
private lemma deriv_pos_Ioc_485_525 {x : ℝ}
    (hx : x ∈ Ioc ((485 : ℝ) / 1000) ((525 : ℝ) / 1000)) :
    0 < deriv dodecaResponse x := by
  have hb1 : ((525 : ℝ) / 1000) ≤ 1 := by norm_num
  have hbW : ((525 : ℝ) / 1000) < dodecaWall := lt_trans (by norm_num) dodecaWall_gt_thirtyThree_fiftieths
  have hwall : x < dodecaWall := lt_of_le_of_lt hx.2 hbW
  have hx0 : 0 < x := lt_trans (by norm_num) hx.1
  have hxI : x ∈ Ioo (0 : ℝ) dodecaWall := ⟨hx0, hwall⟩
  have hx1 : x ≤ 1 := le_trans hx.2 hb1
  have hbR : ((525 : ℝ) / 1000) < resonanceRoot1 := lt_trans hbW dodecaWall_lt_firstNode
  have hsc := dodeca_scales_lt_near
  rcases phaseAt_485 with
    ⟨a0, a1, _, aA0, aAlo, aAhi, aG0, aGlt, aGgt⟩
  rcases phaseAt_525 with
    ⟨b0, b1, _, bA0, bAlo, bAhi, bG0, bGlt, bGgt⟩
  rcases phaseAt_679 with
    ⟨n0, n1, _, nA0, nAlo, nAhi, nG0, nGlt, nGgt⟩
  rcases phaseAt_420 with
    ⟨p30, p31, _, p3A0, p3Alo, p3Ahi, p3G0, p3Glt, p3Ggt⟩
  rcases phaseAt_455 with
    ⟨q30, q31, _, q3A0, q3Alo, q3Ahi, q3G0, q3Glt, q3Ggt⟩
  rcases phaseAt_297 with
    ⟨p60, p61, _, p6A0, p6Alo, p6Ahi, p6G0, p6Glt, p6Ggt⟩
  rcases phaseAt_322 with
    ⟨q60, q61, _, q6A0, q6Alo, q6Ahi, q6G0, q6Glt, q6Ggt⟩
  rcases phaseAt_259 with
    ⟨pF0, pF1, _, pFA0, pFAlo, pFAhi, pFG0, pFGlt, pFGgt⟩
  rcases phaseAt_281 with
    ⟨qF0, qF1, _, qFA0, qFAlo, qFAhi, qFG0, qFGlt, qFGgt⟩
  rcases phaseAt_242 with
    ⟨pH0, pH1, _, pHA0, pHAlo, pHAhi, pHG0, pHGlt, pHGgt⟩
  rcases phaseAt_263 with
    ⟨qH0, qH1, _, qHA0, qHAlo, qHAhi, qHG0, qHGlt, qHGgt⟩
  have hN := near_lower
    a0 hx0 hx.1 hx1 hx.2 hbR n0 n1
    (by norm_num : ((679 : ℝ) / 1000) ≤ (700629 : ℝ) / 500000 * ((485 : ℝ) / 1000))
    aAlo aA0 nAlo nA0 nGgt (lt_trans nG0 nGlt)
    bAhi (lt_trans bA0 bAlo) bGlt bG0 (lt_trans (lt_trans bA0 bAlo) bAhi)
    (by norm_num : (0 : ℝ) < (700629 : ℝ) / 500000 * (((711946909 : ℝ) / 1000000000) / ((57189011 : ℝ) / 100000000)) - ((25240389 : ℝ) / 50000000) / ((778432889 : ℝ) / 1000000000))
    hxI
  have h3 := far_upper
    (c := sqrt 3 / 2) (cLo := ((34641 : ℝ) / 40000)) (cHi := ((433013 : ℝ) / 500000)) (k := 3 * sqrt 3 / 2) (kHi := 3 * ((433013 : ℝ) / 500000))
    a0 hx0 hx.1 hx.2 hb1 hbR p30 q31
    (lt_trans (by norm_num) sqrt_three_div_two_gt_34641) (sqrt_three_div_two_lt_one) (sqrt_three_div_two_gt_34641.le) (sqrt_three_div_two_lt_433013.le) (by positivity) (by norm_num) (s3_weight_le)
    (by norm_num : ((420 : ℝ) / 1000) ≤ ((34641 : ℝ) / 40000) * ((485 : ℝ) / 1000))
    (by norm_num : ((433013 : ℝ) / 500000) * ((525 : ℝ) / 1000) ≤ ((455 : ℝ) / 1000))
    bAhi (lt_trans bA0 bAlo) bGlt p3Alo p3A0 p3Ggt (lt_trans p3G0 p3Glt)
    q3Ahi q3Glt q3G0 bG0 (lt_trans (lt_trans bA0 bAlo) bAhi)
    (by norm_num : (0 : ℝ) < ((818483521 : ℝ) / 1000000000) / ((111064177 : ℝ) / 250000000) - ((34641 : ℝ) / 40000) * (((711946909 : ℝ) / 1000000000) / ((57189011 : ℝ) / 100000000)))
    hsc.1.le hxI
  have h6 := far_upper
    (c := sqrt 6 / 4) (cLo := ((153093 : ℝ) / 250000)) (cHi := ((612373 : ℝ) / 1000000)) (k := 3 * sqrt 6 / 4) (kHi := 3 * ((612373 : ℝ) / 1000000))
    a0 hx0 hx.1 hx.2 hb1 hbR p60 q61
    (lt_trans (by norm_num) sqrt_six_div_four_gt_153093) (sqrt_six_div_four_lt_one) (sqrt_six_div_four_gt_153093.le) (sqrt_six_div_four_lt_612373.le) (by positivity) (by norm_num) (s6_weight_le)
    (by norm_num : ((297 : ℝ) / 1000) ≤ ((153093 : ℝ) / 250000) * ((485 : ℝ) / 1000))
    (by norm_num : ((612373 : ℝ) / 1000000) * ((525 : ℝ) / 1000) ≤ ((322 : ℝ) / 1000))
    bAhi (lt_trans bA0 bAlo) bGlt p6Alo p6A0 p6Ggt (lt_trans p6G0 p6Glt)
    q6Ahi q6Glt q6G0 bG0 (lt_trans (lt_trans bA0 bAlo) bAhi)
    (by norm_num : (0 : ℝ) < ((910502843 : ℝ) / 1000000000) / ((38206917 : ℝ) / 125000000) - ((153093 : ℝ) / 250000) * (((711946909 : ℝ) / 1000000000) / ((57189011 : ℝ) / 100000000)))
    hsc.2.1.le hxI
  have hF := far_upper
    (c := dodecaFarScale) (cLo := ((535233 : ℝ) / 1000000)) (cHi := ((267617 : ℝ) / 500000)) (k := 3 / 2 * dodecaFarScale) (kHi := 3 / 2 * ((267617 : ℝ) / 500000))
    a0 hx0 hx.1 hx.2 hb1 hbR pF0 qF1
    (lt_trans (by norm_num) dodecaFarScale_gt_535233) (dodecaFarScale_lt_one) (dodecaFarScale_gt_535233.le) (dodecaFarScale_lt_267617.le) (mul_pos (by norm_num : (0 : ℝ) < 3 / 2) (lt_trans (by norm_num) dodecaFarScale_gt_535233)) (by norm_num) (far_weight_le)
    (by norm_num : ((259 : ℝ) / 1000) ≤ ((535233 : ℝ) / 1000000) * ((485 : ℝ) / 1000))
    (by norm_num : ((267617 : ℝ) / 500000) * ((525 : ℝ) / 1000) ≤ ((281 : ℝ) / 1000))
    bAhi (lt_trans bA0 bAlo) bGlt pFAlo pFA0 pFGgt (lt_trans pFG0 pFGlt)
    qFAhi qFGlt qFG0 bG0 (lt_trans (lt_trans bA0 bAlo) bAhi)
    (by norm_num : (0 : ℝ) < ((932172821 : ℝ) / 1000000000) / ((8273511 : ℝ) / 31250000) - ((535233 : ℝ) / 1000000) * (((711946909 : ℝ) / 1000000000) / ((57189011 : ℝ) / 100000000)))
    hsc.2.2.1.le hxI
  have hH := far_upper
    (c := (1 / 2)) (cLo := (1 / 2)) (cHi := (1 / 2)) (k := (1 / 4)) (kHi := (1 / 4))
    a0 hx0 hx.1 hx.2 hb1 hbR pH0 qH1
    (by norm_num) (by norm_num) (le_rfl) (le_rfl) (by norm_num) (by norm_num) (le_rfl)
    (by norm_num : ((242 : ℝ) / 1000) ≤ (1 / 2) * ((485 : ℝ) / 1000))
    (by norm_num : (1 / 2) * ((525 : ℝ) / 1000) ≤ ((263 : ℝ) / 1000))
    bAhi (lt_trans bA0 bAlo) bGlt pHAlo pHA0 pHGgt (lt_trans pHG0 pHGlt)
    qHAhi qHGlt qHG0 bG0 (lt_trans (lt_trans bA0 bAlo) bAhi)
    (by norm_num : (0 : ℝ) < ((940866901 : ℝ) / 1000000000) / ((123348209 : ℝ) / 500000000) - (1 / 2) * (((711946909 : ℝ) / 1000000000) / ((57189011 : ℝ) / 100000000)))
    hsc.2.2.2.le hxI
  exact deriv_pos_of_gap hxI hN h3 h6 hF hH (by norm_num)

set_option maxHeartbeats 0 in
-- The cleared gap is a rational with several hundred bits.
private lemma deriv_pos_Ioc_525_565 {x : ℝ}
    (hx : x ∈ Ioc ((525 : ℝ) / 1000) ((565 : ℝ) / 1000)) :
    0 < deriv dodecaResponse x := by
  have hb1 : ((565 : ℝ) / 1000) ≤ 1 := by norm_num
  have hbW : ((565 : ℝ) / 1000) < dodecaWall := lt_trans (by norm_num) dodecaWall_gt_thirtyThree_fiftieths
  have hwall : x < dodecaWall := lt_of_le_of_lt hx.2 hbW
  have hx0 : 0 < x := lt_trans (by norm_num) hx.1
  have hxI : x ∈ Ioo (0 : ℝ) dodecaWall := ⟨hx0, hwall⟩
  have hx1 : x ≤ 1 := le_trans hx.2 hb1
  have hbR : ((565 : ℝ) / 1000) < resonanceRoot1 := lt_trans hbW dodecaWall_lt_firstNode
  have hsc := dodeca_scales_lt_near
  rcases phaseAt_525 with
    ⟨a0, a1, _, aA0, aAlo, aAhi, aG0, aGlt, aGgt⟩
  rcases phaseAt_565 with
    ⟨b0, b1, _, bA0, bAlo, bAhi, bG0, bGlt, bGgt⟩
  rcases phaseAt_735 with
    ⟨n0, n1, _, nA0, nAlo, nAhi, nG0, nGlt, nGgt⟩
  rcases phaseAt_454 with
    ⟨p30, p31, _, p3A0, p3Alo, p3Ahi, p3G0, p3Glt, p3Ggt⟩
  rcases phaseAt_490 with
    ⟨q30, q31, _, q3A0, q3Alo, q3Ahi, q3G0, q3Glt, q3Ggt⟩
  rcases phaseAt_321 with
    ⟨p60, p61, _, p6A0, p6Alo, p6Ahi, p6G0, p6Glt, p6Ggt⟩
  rcases phaseAt_346 with
    ⟨q60, q61, _, q6A0, q6Alo, q6Ahi, q6G0, q6Glt, q6Ggt⟩
  rcases phaseAt_280 with
    ⟨pF0, pF1, _, pFA0, pFAlo, pFAhi, pFG0, pFGlt, pFGgt⟩
  rcases phaseAt_303 with
    ⟨qF0, qF1, _, qFA0, qFAlo, qFAhi, qFG0, qFGlt, qFGgt⟩
  rcases phaseAt_262 with
    ⟨pH0, pH1, _, pHA0, pHAlo, pHAhi, pHG0, pHGlt, pHGgt⟩
  rcases phaseAt_283 with
    ⟨qH0, qH1, _, qHA0, qHAlo, qHAhi, qHG0, qHGlt, qHGgt⟩
  have hN := near_lower
    a0 hx0 hx.1 hx1 hx.2 hbR n0 n1
    (by norm_num : ((735 : ℝ) / 1000) ≤ (700629 : ℝ) / 500000 * ((525 : ℝ) / 1000))
    aAlo aA0 nAlo nA0 nGgt (lt_trans nG0 nGlt)
    bAhi (lt_trans bA0 bAlo) bGlt bG0 (lt_trans (lt_trans bA0 bAlo) bAhi)
    (by norm_num : (0 : ℝ) < (700629 : ℝ) / 500000 * (((664153733 : ℝ) / 1000000000) / ((623176871 : ℝ) / 1000000000)) - ((82640061 : ℝ) / 200000000) / ((107502753 : ℝ) / 125000000))
    hxI
  have h3 := far_upper
    (c := sqrt 3 / 2) (cLo := ((34641 : ℝ) / 40000)) (cHi := ((433013 : ℝ) / 500000)) (k := 3 * sqrt 3 / 2) (kHi := 3 * ((433013 : ℝ) / 500000))
    a0 hx0 hx.1 hx.2 hb1 hbR p30 q31
    (lt_trans (by norm_num) sqrt_three_div_two_gt_34641) (sqrt_three_div_two_lt_one) (sqrt_three_div_two_gt_34641.le) (sqrt_three_div_two_lt_433013.le) (by positivity) (by norm_num) (s3_weight_le)
    (by norm_num : ((454 : ℝ) / 1000) ≤ ((34641 : ℝ) / 40000) * ((525 : ℝ) / 1000))
    (by norm_num : ((433013 : ℝ) / 500000) * ((565 : ℝ) / 1000) ≤ ((490 : ℝ) / 1000))
    bAhi (lt_trans bA0 bAlo) bGlt p3Alo p3A0 p3Ggt (lt_trans p3G0 p3Glt)
    q3Ahi q3Glt q3G0 bG0 (lt_trans (lt_trans bA0 bAlo) bAhi)
    (by norm_num : (0 : ℝ) < ((393457407 : ℝ) / 500000000) / ((484543 : ℝ) / 1000000) - ((34641 : ℝ) / 40000) * (((664153733 : ℝ) / 1000000000) / ((623176871 : ℝ) / 1000000000)))
    hsc.1.le hxI
  have h6 := far_upper
    (c := sqrt 6 / 4) (cLo := ((153093 : ℝ) / 250000)) (cHi := ((612373 : ℝ) / 1000000)) (k := 3 * sqrt 6 / 4) (kHi := 3 * ((612373 : ℝ) / 1000000))
    a0 hx0 hx.1 hx.2 hb1 hbR p60 q61
    (lt_trans (by norm_num) sqrt_six_div_four_gt_153093) (sqrt_six_div_four_lt_one) (sqrt_six_div_four_gt_153093.le) (sqrt_six_div_four_lt_612373.le) (by positivity) (by norm_num) (s6_weight_le)
    (by norm_num : ((321 : ℝ) / 1000) ≤ ((153093 : ℝ) / 250000) * ((525 : ℝ) / 1000))
    (by norm_num : ((612373 : ℝ) / 1000000) * ((565 : ℝ) / 1000) ≤ ((346 : ℝ) / 1000))
    bAhi (lt_trans bA0 bAlo) bGlt p6Alo p6A0 p6Ggt (lt_trans p6G0 p6Glt)
    q6Ahi q6Glt q6G0 bG0 (lt_trans (lt_trans bA0 bAlo) bAhi)
    (by norm_num : (0 : ℝ) < ((447601613 : ℝ) / 500000000) / ((165955611 : ℝ) / 500000000) - ((153093 : ℝ) / 250000) * (((664153733 : ℝ) / 1000000000) / ((623176871 : ℝ) / 1000000000)))
    hsc.2.1.le hxI
  have hF := far_upper
    (c := dodecaFarScale) (cLo := ((535233 : ℝ) / 1000000)) (cHi := ((267617 : ℝ) / 500000)) (k := 3 / 2 * dodecaFarScale) (kHi := 3 / 2 * ((267617 : ℝ) / 500000))
    a0 hx0 hx.1 hx.2 hb1 hbR pF0 qF1
    (lt_trans (by norm_num) dodecaFarScale_gt_535233) (dodecaFarScale_lt_one) (dodecaFarScale_gt_535233.le) (dodecaFarScale_lt_267617.le) (mul_pos (by norm_num : (0 : ℝ) < 3 / 2) (lt_trans (by norm_num) dodecaFarScale_gt_535233)) (by norm_num) (far_weight_le)
    (by norm_num : ((280 : ℝ) / 1000) ≤ ((535233 : ℝ) / 1000000) * ((525 : ℝ) / 1000))
    (by norm_num : ((267617 : ℝ) / 500000) * ((565 : ℝ) / 1000) ≤ ((303 : ℝ) / 1000))
    bAhi (lt_trans bA0 bAlo) bGlt pFAlo pFA0 pFGgt (lt_trans pFG0 pFGlt)
    qFAhi qFGlt qFG0 bG0 (lt_trans (lt_trans bA0 bAlo) bAhi)
    (by norm_num : (0 : ℝ) < ((23014541 : ℝ) / 25000000) / ((1149039 : ℝ) / 4000000) - ((535233 : ℝ) / 1000000) * (((664153733 : ℝ) / 1000000000) / ((623176871 : ℝ) / 1000000000)))
    hsc.2.2.1.le hxI
  have hH := far_upper
    (c := (1 / 2)) (cLo := (1 / 2)) (cHi := (1 / 2)) (k := (1 / 4)) (kHi := (1 / 4))
    a0 hx0 hx.1 hx.2 hb1 hbR pH0 qH1
    (by norm_num) (by norm_num) (le_rfl) (le_rfl) (by norm_num) (by norm_num) (le_rfl)
    (by norm_num : ((262 : ℝ) / 1000) ≤ (1 / 2) * ((525 : ℝ) / 1000))
    (by norm_num : (1 / 2) * ((565 : ℝ) / 1000) ≤ ((283 : ℝ) / 1000))
    bAhi (lt_trans bA0 bAlo) bGlt pHAlo pHA0 pHGgt (lt_trans pHG0 pHGlt)
    qHAhi qHGlt qHG0 bG0 (lt_trans (lt_trans bA0 bAlo) bAhi)
    (by norm_num : (0 : ℝ) < ((58160921 : ℝ) / 62500000) / ((133976811 : ℝ) / 500000000) - (1 / 2) * (((664153733 : ℝ) / 1000000000) / ((623176871 : ℝ) / 1000000000)))
    hsc.2.2.2.le hxI
  exact deriv_pos_of_gap hxI hN h3 h6 hF hH (by norm_num)

set_option maxHeartbeats 0 in
-- The cleared gap is a rational with several hundred bits.
private lemma deriv_pos_Ioc_565_605 {x : ℝ}
    (hx : x ∈ Ioc ((565 : ℝ) / 1000) ((605 : ℝ) / 1000)) :
    0 < deriv dodecaResponse x := by
  have hb1 : ((605 : ℝ) / 1000) ≤ 1 := by norm_num
  have hbW : ((605 : ℝ) / 1000) < dodecaWall := lt_trans (by norm_num) dodecaWall_gt_thirtyThree_fiftieths
  have hwall : x < dodecaWall := lt_of_le_of_lt hx.2 hbW
  have hx0 : 0 < x := lt_trans (by norm_num) hx.1
  have hxI : x ∈ Ioo (0 : ℝ) dodecaWall := ⟨hx0, hwall⟩
  have hx1 : x ≤ 1 := le_trans hx.2 hb1
  have hbR : ((605 : ℝ) / 1000) < resonanceRoot1 := lt_trans hbW dodecaWall_lt_firstNode
  have hsc := dodeca_scales_lt_near
  rcases phaseAt_565 with
    ⟨a0, a1, _, aA0, aAlo, aAhi, aG0, aGlt, aGgt⟩
  rcases phaseAt_605 with
    ⟨b0, b1, _, bA0, bAlo, bAhi, bG0, bGlt, bGgt⟩
  rcases phaseAt_791 with
    ⟨n0, n1, _, nA0, nAlo, nAhi, nG0, nGlt, nGgt⟩
  rcases phaseAt_489 with
    ⟨p30, p31, _, p3A0, p3Alo, p3Ahi, p3G0, p3Glt, p3Ggt⟩
  rcases phaseAt_524 with
    ⟨q30, q31, _, q3A0, q3Alo, q3Ahi, q3G0, q3Glt, q3Ggt⟩
  rcases phaseAt_345 with
    ⟨p60, p61, _, p6A0, p6Alo, p6Ahi, p6G0, p6Glt, p6Ggt⟩
  rcases phaseAt_371 with
    ⟨q60, q61, _, q6A0, q6Alo, q6Ahi, q6G0, q6Glt, q6Ggt⟩
  rcases phaseAt_302 with
    ⟨pF0, pF1, _, pFA0, pFAlo, pFAhi, pFG0, pFGlt, pFGgt⟩
  rcases phaseAt_324 with
    ⟨qF0, qF1, _, qFA0, qFAlo, qFAhi, qFG0, qFGlt, qFGgt⟩
  rcases phaseAt_282 with
    ⟨pH0, pH1, _, pHA0, pHAlo, pHAhi, pHG0, pHGlt, pHGgt⟩
  rcases phaseAt_303 with
    ⟨qH0, qH1, _, qHA0, qHAlo, qHAhi, qHG0, qHGlt, qHGgt⟩
  have hN := near_lower
    a0 hx0 hx.1 hx1 hx.2 hbR n0 n1
    (by norm_num : ((791 : ℝ) / 1000) ≤ (700629 : ℝ) / 500000 * ((565 : ℝ) / 1000))
    aAlo aA0 nAlo nA0 nGgt (lt_trans nG0 nGlt)
    bAhi (lt_trans bA0 bAlo) bGlt bG0 (lt_trans (lt_trans bA0 bAlo) bAhi)
    (by norm_num : (0 : ℝ) < (700629 : ℝ) / 500000 * (((24487727 : ℝ) / 40000000) / ((676073669 : ℝ) / 1000000000)) - ((312306221 : ℝ) / 1000000000) / ((472671853 : ℝ) / 500000000))
    hxI
  have h3 := far_upper
    (c := sqrt 3 / 2) (cLo := ((34641 : ℝ) / 40000)) (cHi := ((433013 : ℝ) / 500000)) (k := 3 * sqrt 3 / 2) (kHi := 3 * ((433013 : ℝ) / 500000))
    a0 hx0 hx.1 hx.2 hb1 hbR p30 q31
    (lt_trans (by norm_num) sqrt_three_div_two_gt_34641) (sqrt_three_div_two_lt_one) (sqrt_three_div_two_gt_34641.le) (sqrt_three_div_two_lt_433013.le) (by positivity) (by norm_num) (s3_weight_le)
    (by norm_num : ((489 : ℝ) / 1000) ≤ ((34641 : ℝ) / 40000) * ((565 : ℝ) / 1000))
    (by norm_num : ((433013 : ℝ) / 500000) * ((605 : ℝ) / 1000) ≤ ((524 : ℝ) / 1000))
    bAhi (lt_trans bA0 bAlo) bGlt p3Alo p3A0 p3Ggt (lt_trans p3G0 p3Glt)
    q3Ahi q3Glt q3G0 bG0 (lt_trans (lt_trans bA0 bAlo) bAhi)
    (by norm_num : (0 : ℝ) < ((751523709 : ℝ) / 1000000000) / ((527034117 : ℝ) / 1000000000) - ((34641 : ℝ) / 40000) * (((24487727 : ℝ) / 40000000) / ((676073669 : ℝ) / 1000000000)))
    hsc.1.le hxI
  have h6 := far_upper
    (c := sqrt 6 / 4) (cLo := ((153093 : ℝ) / 250000)) (cHi := ((612373 : ℝ) / 1000000)) (k := 3 * sqrt 6 / 4) (kHi := 3 * ((612373 : ℝ) / 1000000))
    a0 hx0 hx.1 hx.2 hb1 hbR p60 q61
    (lt_trans (by norm_num) sqrt_six_div_four_gt_153093) (sqrt_six_div_four_lt_one) (sqrt_six_div_four_gt_153093.le) (sqrt_six_div_four_lt_612373.le) (by positivity) (by norm_num) (s6_weight_le)
    (by norm_num : ((345 : ℝ) / 1000) ≤ ((153093 : ℝ) / 250000) * ((565 : ℝ) / 1000))
    (by norm_num : ((612373 : ℝ) / 1000000) * ((605 : ℝ) / 1000) ≤ ((371 : ℝ) / 1000))
    bAhi (lt_trans bA0 bAlo) bGlt p6Alo p6A0 p6Ggt (lt_trans p6G0 p6Glt)
    q6Ahi q6Glt q6G0 bG0 (lt_trans (lt_trans bA0 bAlo) bAhi)
    (by norm_num : (0 : ℝ) < ((439317571 : ℝ) / 500000000) / ((2800969 : ℝ) / 7812500) - ((153093 : ℝ) / 250000) * (((24487727 : ℝ) / 40000000) / ((676073669 : ℝ) / 1000000000)))
    hsc.2.1.le hxI
  have hF := far_upper
    (c := dodecaFarScale) (cLo := ((535233 : ℝ) / 1000000)) (cHi := ((267617 : ℝ) / 500000)) (k := 3 / 2 * dodecaFarScale) (kHi := 3 / 2 * ((267617 : ℝ) / 500000))
    a0 hx0 hx.1 hx.2 hb1 hbR pF0 qF1
    (lt_trans (by norm_num) dodecaFarScale_gt_535233) (dodecaFarScale_lt_one) (dodecaFarScale_gt_535233.le) (dodecaFarScale_lt_267617.le) (mul_pos (by norm_num : (0 : ℝ) < 3 / 2) (lt_trans (by norm_num) dodecaFarScale_gt_535233)) (by norm_num) (far_weight_le)
    (by norm_num : ((302 : ℝ) / 1000) ≤ ((535233 : ℝ) / 1000000) * ((565 : ℝ) / 1000))
    (by norm_num : ((267617 : ℝ) / 500000) * ((605 : ℝ) / 1000) ≤ ((324 : ℝ) / 1000))
    bAhi (lt_trans bA0 bAlo) bGlt pFAlo pFA0 pFGgt (lt_trans pFG0 pFGlt)
    qFAhi qFGlt qFG0 bG0 (lt_trans (lt_trans bA0 bAlo) bAhi)
    (by norm_num : (0 : ℝ) < ((907419199 : ℝ) / 1000000000) / ((155548551 : ℝ) / 500000000) - ((535233 : ℝ) / 1000000) * (((24487727 : ℝ) / 40000000) / ((676073669 : ℝ) / 1000000000)))
    hsc.2.2.1.le hxI
  have hH := far_upper
    (c := (1 / 2)) (cLo := (1 / 2)) (cHi := (1 / 2)) (k := (1 / 4)) (kHi := (1 / 4))
    a0 hx0 hx.1 hx.2 hb1 hbR pH0 qH1
    (by norm_num) (by norm_num) (le_rfl) (le_rfl) (by norm_num) (by norm_num) (le_rfl)
    (by norm_num : ((282 : ℝ) / 1000) ≤ (1 / 2) * ((565 : ℝ) / 1000))
    (by norm_num : (1 / 2) * ((605 : ℝ) / 1000) ≤ ((303 : ℝ) / 1000))
    bAhi (lt_trans bA0 bAlo) bGlt pHAlo pHA0 pHGgt (lt_trans pHG0 pHGlt)
    qHAhi qHGlt qHG0 bG0 (lt_trans (lt_trans bA0 bAlo) bAhi)
    (by norm_num : (0 : ℝ) < ((919428321 : ℝ) / 1000000000) / ((9044237 : ℝ) / 31250000) - (1 / 2) * (((24487727 : ℝ) / 40000000) / ((676073669 : ℝ) / 1000000000)))
    hsc.2.2.2.le hxI
  exact deriv_pos_of_gap hxI hN h3 h6 hF hH (by norm_num)

set_option maxHeartbeats 0 in
-- The cleared gap is a rational with several hundred bits.
private lemma deriv_pos_Ioc_605_645 {x : ℝ}
    (hx : x ∈ Ioc ((605 : ℝ) / 1000) ((645 : ℝ) / 1000)) :
    0 < deriv dodecaResponse x := by
  have hb1 : ((645 : ℝ) / 1000) ≤ 1 := by norm_num
  have hbW : ((645 : ℝ) / 1000) < dodecaWall := lt_trans (by norm_num) dodecaWall_gt_thirtyThree_fiftieths
  have hwall : x < dodecaWall := lt_of_le_of_lt hx.2 hbW
  have hx0 : 0 < x := lt_trans (by norm_num) hx.1
  have hxI : x ∈ Ioo (0 : ℝ) dodecaWall := ⟨hx0, hwall⟩
  have hx1 : x ≤ 1 := le_trans hx.2 hb1
  have hbR : ((645 : ℝ) / 1000) < resonanceRoot1 := lt_trans hbW dodecaWall_lt_firstNode
  have hsc := dodeca_scales_lt_near
  rcases phaseAt_605 with
    ⟨a0, a1, _, aA0, aAlo, aAhi, aG0, aGlt, aGgt⟩
  rcases phaseAt_645 with
    ⟨b0, b1, _, bA0, bAlo, bAhi, bG0, bGlt, bGgt⟩
  rcases phaseAt_847 with
    ⟨n0, n1, _, nA0, nAlo, nAhi, nG0, nGlt, nGgt⟩
  rcases phaseAt_523 with
    ⟨p30, p31, _, p3A0, p3Alo, p3Ahi, p3G0, p3Glt, p3Ggt⟩
  rcases phaseAt_559 with
    ⟨q30, q31, _, q3A0, q3Alo, q3Ahi, q3G0, q3Glt, q3Ggt⟩
  rcases phaseAt_370 with
    ⟨p60, p61, _, p6A0, p6Alo, p6Ahi, p6G0, p6Glt, p6Ggt⟩
  rcases phaseAt_395 with
    ⟨q60, q61, _, q6A0, q6Alo, q6Ahi, q6G0, q6Glt, q6Ggt⟩
  rcases phaseAt_323 with
    ⟨pF0, pF1, _, pFA0, pFAlo, pFAhi, pFG0, pFGlt, pFGgt⟩
  rcases phaseAt_346 with
    ⟨qF0, qF1, _, qFA0, qFAlo, qFAhi, qFG0, qFGlt, qFGgt⟩
  rcases phaseAt_302 with
    ⟨pH0, pH1, _, pHA0, pHAlo, pHAhi, pHG0, pHGlt, pHGgt⟩
  rcases phaseAt_323 with
    ⟨qH0, qH1, _, qHA0, qHAlo, qHAhi, qHG0, qHGlt, qHGgt⟩
  have hN := near_lower
    a0 hx0 hx.1 hx1 hx.2 hbR n0 n1
    (by norm_num : ((847 : ℝ) / 1000) ≤ (700629 : ℝ) / 500000 * ((605 : ℝ) / 1000))
    aAlo aA0 nAlo nA0 nGgt (lt_trans nG0 nGlt)
    bAhi (lt_trans bA0 bAlo) bGlt bG0 (lt_trans (lt_trans bA0 bAlo) bAhi)
    (by norm_num : (0 : ℝ) < (700629 : ℝ) / 500000 * (((555932791 : ℝ) / 1000000000) / ((365331323 : ℝ) / 500000000)) - ((201724789 : ℝ) / 1000000000) / ((1034524729 : ℝ) / 1000000000))
    hxI
  have h3 := far_upper
    (c := sqrt 3 / 2) (cLo := ((34641 : ℝ) / 40000)) (cHi := ((433013 : ℝ) / 500000)) (k := 3 * sqrt 3 / 2) (kHi := 3 * ((433013 : ℝ) / 500000))
    a0 hx0 hx.1 hx.2 hb1 hbR p30 q31
    (lt_trans (by norm_num) sqrt_three_div_two_gt_34641) (sqrt_three_div_two_lt_one) (sqrt_three_div_two_gt_34641.le) (sqrt_three_div_two_lt_433013.le) (by positivity) (by norm_num) (s3_weight_le)
    (by norm_num : ((523 : ℝ) / 1000) ≤ ((34641 : ℝ) / 40000) * ((605 : ℝ) / 1000))
    (by norm_num : ((433013 : ℝ) / 500000) * ((645 : ℝ) / 1000) ≤ ((559 : ℝ) / 1000))
    bAhi (lt_trans bA0 bAlo) bGlt p3Alo p3A0 p3Ggt (lt_trans p3G0 p3Glt)
    q3Ahi q3Glt q3G0 bG0 (lt_trans (lt_trans bA0 bAlo) bAhi)
    (by norm_num : (0 : ℝ) < ((44641457 : ℝ) / 62500000) / ((569363947 : ℝ) / 1000000000) - ((34641 : ℝ) / 40000) * (((555932791 : ℝ) / 1000000000) / ((365331323 : ℝ) / 500000000)))
    hsc.1.le hxI
  have h6 := far_upper
    (c := sqrt 6 / 4) (cLo := ((153093 : ℝ) / 250000)) (cHi := ((612373 : ℝ) / 1000000)) (k := 3 * sqrt 6 / 4) (kHi := 3 * ((612373 : ℝ) / 1000000))
    a0 hx0 hx.1 hx.2 hb1 hbR p60 q61
    (lt_trans (by norm_num) sqrt_six_div_four_gt_153093) (sqrt_six_div_four_lt_one) (sqrt_six_div_four_gt_153093.le) (sqrt_six_div_four_lt_612373.le) (by positivity) (by norm_num) (s6_weight_le)
    (by norm_num : ((370 : ℝ) / 1000) ≤ ((153093 : ℝ) / 250000) * ((605 : ℝ) / 1000))
    (by norm_num : ((612373 : ℝ) / 1000000) * ((645 : ℝ) / 1000) ≤ ((395 : ℝ) / 1000))
    bAhi (lt_trans bA0 bAlo) bGlt p6Alo p6A0 p6Ggt (lt_trans p6G0 p6Glt)
    q6Ahi q6Glt q6G0 bG0 (lt_trans (lt_trans bA0 bAlo) bAhi)
    (by norm_num : (0 : ℝ) < ((430004429 : ℝ) / 500000000) / ((2416573 : ℝ) / 6250000) - ((153093 : ℝ) / 250000) * (((555932791 : ℝ) / 1000000000) / ((365331323 : ℝ) / 500000000)))
    hsc.2.1.le hxI
  have hF := far_upper
    (c := dodecaFarScale) (cLo := ((535233 : ℝ) / 1000000)) (cHi := ((267617 : ℝ) / 500000)) (k := 3 / 2 * dodecaFarScale) (kHi := 3 / 2 * ((267617 : ℝ) / 500000))
    a0 hx0 hx.1 hx.2 hb1 hbR pF0 qF1
    (lt_trans (by norm_num) dodecaFarScale_gt_535233) (dodecaFarScale_lt_one) (dodecaFarScale_gt_535233.le) (dodecaFarScale_lt_267617.le) (mul_pos (by norm_num : (0 : ℝ) < 3 / 2) (lt_trans (by norm_num) dodecaFarScale_gt_535233)) (by norm_num) (far_weight_le)
    (by norm_num : ((323 : ℝ) / 1000) ≤ ((535233 : ℝ) / 1000000) * ((605 : ℝ) / 1000))
    (by norm_num : ((267617 : ℝ) / 500000) * ((645 : ℝ) / 1000) ≤ ((346 : ℝ) / 1000))
    bAhi (lt_trans bA0 bAlo) bGlt pFAlo pFA0 pFGgt (lt_trans pFG0 pFGlt)
    qFAhi qFGlt qFG0 bG0 (lt_trans (lt_trans bA0 bAlo) bAhi)
    (by norm_num : (0 : ℝ) < ((893871237 : ℝ) / 1000000000) / ((167057491 : ℝ) / 500000000) - ((535233 : ℝ) / 1000000) * (((555932791 : ℝ) / 1000000000) / ((365331323 : ℝ) / 500000000)))
    hsc.2.2.1.le hxI
  have hH := far_upper
    (c := (1 / 2)) (cLo := (1 / 2)) (cHi := (1 / 2)) (k := (1 / 4)) (kHi := (1 / 4))
    a0 hx0 hx.1 hx.2 hb1 hbR pH0 qH1
    (by norm_num) (by norm_num) (le_rfl) (le_rfl) (by norm_num) (by norm_num) (le_rfl)
    (by norm_num : ((302 : ℝ) / 1000) ≤ (1 / 2) * ((605 : ℝ) / 1000))
    (by norm_num : (1 / 2) * ((645 : ℝ) / 1000) ≤ ((323 : ℝ) / 1000))
    bAhi (lt_trans bA0 bAlo) bGlt pHAlo pHA0 pHGgt (lt_trans pHG0 pHGlt)
    qHAhi qHGlt qHG0 bG0 (lt_trans (lt_trans bA0 bAlo) bAhi)
    (by norm_num : (0 : ℝ) < ((907419199 : ℝ) / 1000000000) / ((155548551 : ℝ) / 500000000) - (1 / 2) * (((555932791 : ℝ) / 1000000000) / ((365331323 : ℝ) / 500000000)))
    hsc.2.2.2.le hxI
  exact deriv_pos_of_gap hxI hN h3 h6 hF hH (by norm_num)

set_option maxHeartbeats 0 in
-- The cleared gap is a rational with several hundred bits.
private lemma deriv_pos_Ioc_645_660 {x : ℝ}
    (hx : x ∈ Ioc ((645 : ℝ) / 1000) ((660 : ℝ) / 1000)) :
    0 < deriv dodecaResponse x := by
  have hb1 : ((660 : ℝ) / 1000) ≤ 1 := by norm_num
  have hbW : ((660 : ℝ) / 1000) < dodecaWall := by
    have hbEq : ((660 : ℝ) / 1000) = 33 / 50 := by norm_num
    simpa [hbEq] using dodecaWall_gt_thirtyThree_fiftieths
  have hwall : x < dodecaWall := lt_of_le_of_lt hx.2 hbW
  have hx0 : 0 < x := lt_trans (by norm_num) hx.1
  have hxI : x ∈ Ioo (0 : ℝ) dodecaWall := ⟨hx0, hwall⟩
  have hx1 : x ≤ 1 := le_trans hx.2 hb1
  have hbR : ((660 : ℝ) / 1000) < resonanceRoot1 := lt_trans hbW dodecaWall_lt_firstNode
  have hsc := dodeca_scales_lt_near
  rcases phaseAt_645 with
    ⟨a0, a1, _, aA0, aAlo, aAhi, aG0, aGlt, aGgt⟩
  rcases phaseAt_660 with
    ⟨b0, b1, _, bA0, bAlo, bAhi, bG0, bGlt, bGgt⟩
  rcases phaseAt_903 with
    ⟨n0, n1, _, nA0, nAlo, nAhi, nG0, nGlt, nGgt⟩
  rcases phaseAt_558 with
    ⟨p30, p31, _, p3A0, p3Alo, p3Ahi, p3G0, p3Glt, p3Ggt⟩
  rcases phaseAt_572 with
    ⟨q30, q31, _, q3A0, q3Alo, q3Ahi, q3G0, q3Glt, q3Ggt⟩
  rcases phaseAt_394 with
    ⟨p60, p61, _, p6A0, p6Alo, p6Ahi, p6G0, p6Glt, p6Ggt⟩
  rcases phaseAt_405 with
    ⟨q60, q61, _, q6A0, q6Alo, q6Ahi, q6G0, q6Glt, q6Ggt⟩
  rcases phaseAt_345 with
    ⟨pF0, pF1, _, pFA0, pFAlo, pFAhi, pFG0, pFGlt, pFGgt⟩
  rcases phaseAt_354 with
    ⟨qF0, qF1, _, qFA0, qFAlo, qFAhi, qFG0, qFGlt, qFGgt⟩
  rcases phaseAt_322 with
    ⟨pH0, pH1, _, pHA0, pHAlo, pHAhi, pHG0, pHGlt, pHGgt⟩
  rcases phaseAt_330 with
    ⟨qH0, qH1, _, qHA0, qHAlo, qHAhi, qHG0, qHGlt, qHGgt⟩
  have hN := near_lower
    a0 hx0 hx.1 hx1 hx.2 hbR n0 n1
    (by norm_num : ((903 : ℝ) / 1000) ≤ (700629 : ℝ) / 500000 * ((645 : ℝ) / 1000))
    aAlo aA0 nAlo nA0 nGgt (lt_trans nG0 nGlt)
    bAhi (lt_trans bA0 bAlo) bGlt bG0 (lt_trans (lt_trans bA0 bAlo) bAhi)
    (by norm_num : (0 : ℝ) < (700629 : ℝ) / 500000 * (((533698449 : ℝ) / 1000000000) / ((751585387 : ℝ) / 1000000000)) - ((81051351 : ℝ) / 1000000000) / ((281913607 : ℝ) / 250000000))
    hxI
  have h3 := far_upper
    (c := sqrt 3 / 2) (cLo := ((34641 : ℝ) / 40000)) (cHi := ((433013 : ℝ) / 500000)) (k := 3 * sqrt 3 / 2) (kHi := 3 * ((433013 : ℝ) / 500000))
    a0 hx0 hx.1 hx.2 hb1 hbR p30 q31
    (lt_trans (by norm_num) sqrt_three_div_two_gt_34641) (sqrt_three_div_two_lt_one) (sqrt_three_div_two_gt_34641.le) (sqrt_three_div_two_lt_433013.le) (by positivity) (by norm_num) (s3_weight_le)
    (by norm_num : ((558 : ℝ) / 1000) ≤ ((34641 : ℝ) / 40000) * ((645 : ℝ) / 1000))
    (by norm_num : ((433013 : ℝ) / 500000) * ((660 : ℝ) / 1000) ≤ ((572 : ℝ) / 1000))
    bAhi (lt_trans bA0 bAlo) bGlt p3Alo p3A0 p3Ggt (lt_trans p3G0 p3Glt)
    q3Ahi q3Glt q3G0 bG0 (lt_trans (lt_trans bA0 bAlo) bAhi)
    (by norm_num : (0 : ℝ) < ((3364329 : ℝ) / 5000000) / ((307041911 : ℝ) / 500000000) - ((34641 : ℝ) / 40000) * (((533698449 : ℝ) / 1000000000) / ((751585387 : ℝ) / 1000000000)))
    hsc.1.le hxI
  have h6 := far_upper
    (c := sqrt 6 / 4) (cLo := ((153093 : ℝ) / 250000)) (cHi := ((612373 : ℝ) / 1000000)) (k := 3 * sqrt 6 / 4) (kHi := 3 * ((612373 : ℝ) / 1000000))
    a0 hx0 hx.1 hx.2 hb1 hbR p60 q61
    (lt_trans (by norm_num) sqrt_six_div_four_gt_153093) (sqrt_six_div_four_lt_one) (sqrt_six_div_four_gt_153093.le) (sqrt_six_div_four_lt_612373.le) (by positivity) (by norm_num) (s6_weight_le)
    (by norm_num : ((394 : ℝ) / 1000) ≤ ((153093 : ℝ) / 250000) * ((645 : ℝ) / 1000))
    (by norm_num : ((612373 : ℝ) / 1000000) * ((660 : ℝ) / 1000) ≤ ((405 : ℝ) / 1000))
    bAhi (lt_trans bA0 bAlo) bGlt p6Alo p6A0 p6Ggt (lt_trans p6G0 p6Glt)
    q6Ahi q6Glt q6G0 bG0 (lt_trans (lt_trans bA0 bAlo) bAhi)
    (by norm_num : (0 : ℝ) < ((840795033 : ℝ) / 1000000000) / ((207034417 : ℝ) / 500000000) - ((153093 : ℝ) / 250000) * (((533698449 : ℝ) / 1000000000) / ((751585387 : ℝ) / 1000000000)))
    hsc.2.1.le hxI
  have hF := far_upper
    (c := dodecaFarScale) (cLo := ((535233 : ℝ) / 1000000)) (cHi := ((267617 : ℝ) / 500000)) (k := 3 / 2 * dodecaFarScale) (kHi := 3 / 2 * ((267617 : ℝ) / 500000))
    a0 hx0 hx.1 hx.2 hb1 hbR pF0 qF1
    (lt_trans (by norm_num) dodecaFarScale_gt_535233) (dodecaFarScale_lt_one) (dodecaFarScale_gt_535233.le) (dodecaFarScale_lt_267617.le) (mul_pos (by norm_num : (0 : ℝ) < 3 / 2) (lt_trans (by norm_num) dodecaFarScale_gt_535233)) (by norm_num) (far_weight_le)
    (by norm_num : ((345 : ℝ) / 1000) ≤ ((535233 : ℝ) / 1000000) * ((645 : ℝ) / 1000))
    (by norm_num : ((267617 : ℝ) / 500000) * ((660 : ℝ) / 1000) ≤ ((354 : ℝ) / 1000))
    bAhi (lt_trans bA0 bAlo) bGlt pFAlo pFA0 pFGgt (lt_trans pFG0 pFGlt)
    qFAhi qFGlt qFG0 bG0 (lt_trans (lt_trans bA0 bAlo) bAhi)
    (by norm_num : (0 : ℝ) < ((439317571 : ℝ) / 500000000) / ((2800969 : ℝ) / 7812500) - ((535233 : ℝ) / 1000000) * (((533698449 : ℝ) / 1000000000) / ((751585387 : ℝ) / 1000000000)))
    hsc.2.2.1.le hxI
  have hH := far_upper
    (c := (1 / 2)) (cLo := (1 / 2)) (cHi := (1 / 2)) (k := (1 / 4)) (kHi := (1 / 4))
    a0 hx0 hx.1 hx.2 hb1 hbR pH0 qH1
    (by norm_num) (by norm_num) (le_rfl) (le_rfl) (by norm_num) (by norm_num) (le_rfl)
    (by norm_num : ((322 : ℝ) / 1000) ≤ (1 / 2) * ((645 : ℝ) / 1000))
    (by norm_num : (1 / 2) * ((660 : ℝ) / 1000) ≤ ((330 : ℝ) / 1000))
    bAhi (lt_trans bA0 bAlo) bGlt pHAlo pHA0 pHGgt (lt_trans pHG0 pHGlt)
    qHAhi qHGlt qHG0 bG0 (lt_trans (lt_trans bA0 bAlo) bAhi)
    (by norm_num : (0 : ℝ) < ((447269167 : ℝ) / 500000000) / ((333012791 : ℝ) / 1000000000) - (1 / 2) * (((533698449 : ℝ) / 1000000000) / ((751585387 : ℝ) / 1000000000)))
    hsc.2.2.2.le hxI
  exact deriv_pos_of_gap hxI hN h3 h6 hF hH (by norm_num)

set_option maxHeartbeats 0 in
-- The cleared gap is a rational with several hundred bits.
private lemma deriv_pos_Ioo_660_wall {x : ℝ}
    (hx : x ∈ Ioo ((660 : ℝ) / 1000) dodecaWall) :
    0 < deriv dodecaResponse x := by
  have hb1 : ((715 : ℝ) / 1000) ≤ 1 := by norm_num
  have h5 : (5 : ℝ) / 7 < ((715 : ℝ) / 1000) := by norm_num
  have hxb : x ≤ ((715 : ℝ) / 1000) := le_of_lt (lt_trans hx.2 (lt_trans dodecaWall_lt_five_sevenths h5))
  have hx0 : 0 < x := lt_trans (by norm_num) hx.1
  have hxI : x ∈ Ioo (0 : ℝ) dodecaWall := ⟨hx0, hx.2⟩
  have hx1 : x ≤ 1 := le_trans hxb hb1
  have hbR : ((715 : ℝ) / 1000) < resonanceRoot1 := lt_trans (by norm_num) ninetyThree_hundredths_lt_resonanceRoot1
  have hsc := dodeca_scales_lt_near
  rcases phaseAt_660 with
    ⟨a0, a1, _, aA0, aAlo, aAhi, aG0, aGlt, aGgt⟩
  rcases phaseAt_715 with
    ⟨b0, b1, _, bA0, bAlo, bAhi, bG0, bGlt, bGgt⟩
  rcases phaseAt_924 with
    ⟨n0, n1, _, nA0, nAlo, nAhi, nG0, nGlt, nGgt⟩
  rcases phaseAt_571 with
    ⟨p30, p31, _, p3A0, p3Alo, p3Ahi, p3G0, p3Glt, p3Ggt⟩
  rcases phaseAt_620 with
    ⟨q30, q31, _, q3A0, q3Alo, q3Ahi, q3G0, q3Glt, q3Ggt⟩
  rcases phaseAt_404 with
    ⟨p60, p61, _, p6A0, p6Alo, p6Ahi, p6G0, p6Glt, p6Ggt⟩
  rcases phaseAt_438 with
    ⟨q60, q61, _, q6A0, q6Alo, q6Ahi, q6G0, q6Glt, q6Ggt⟩
  rcases phaseAt_353 with
    ⟨pF0, pF1, _, pFA0, pFAlo, pFAhi, pFG0, pFGlt, pFGgt⟩
  rcases phaseAt_383 with
    ⟨qF0, qF1, _, qFA0, qFAlo, qFAhi, qFG0, qFGlt, qFGgt⟩
  rcases phaseAt_330 with
    ⟨pH0, pH1, _, pHA0, pHAlo, pHAhi, pHG0, pHGlt, pHGgt⟩
  rcases phaseAt_358 with
    ⟨qH0, qH1, _, qHA0, qHAlo, qHAhi, qHG0, qHGlt, qHGgt⟩
  have hN := near_lower
    a0 hx0 hx.1 hx1 hxb hbR n0 n1
    (by norm_num : ((924 : ℝ) / 1000) ≤ (700629 : ℝ) / 500000 * ((660 : ℝ) / 1000))
    aAlo aA0 nAlo nA0 nGgt (lt_trans nG0 nGlt)
    bAhi (lt_trans bA0 bAlo) bGlt bG0 (lt_trans (lt_trans bA0 bAlo) bAhi)
    (by norm_num : (0 : ℝ) < (700629 : ℝ) / 500000 * (((55838703 : ℝ) / 125000000) / ((207621947 : ℝ) / 250000000)) - ((16557339 : ℝ) / 500000000) / ((581803663 : ℝ) / 500000000))
    hxI
  have h3 := far_upper
    (c := sqrt 3 / 2) (cLo := ((34641 : ℝ) / 40000)) (cHi := ((433013 : ℝ) / 500000)) (k := 3 * sqrt 3 / 2) (kHi := 3 * ((433013 : ℝ) / 500000))
    a0 hx0 hx.1 hxb hb1 hbR p30 q31
    (lt_trans (by norm_num) sqrt_three_div_two_gt_34641) (sqrt_three_div_two_lt_one) (sqrt_three_div_two_gt_34641.le) (sqrt_three_div_two_lt_433013.le) (by positivity) (by norm_num) (s3_weight_le)
    (by norm_num : ((571 : ℝ) / 1000) ≤ ((34641 : ℝ) / 40000) * ((660 : ℝ) / 1000))
    (by norm_num : ((433013 : ℝ) / 500000) * ((715 : ℝ) / 1000) ≤ ((620 : ℝ) / 1000))
    bAhi (lt_trans bA0 bAlo) bGlt p3Alo p3A0 p3Ggt (lt_trans p3G0 p3Glt)
    q3Ahi q3Glt q3G0 bG0 (lt_trans (lt_trans bA0 bAlo) bAhi)
    (by norm_num : (0 : ℝ) < ((5253501 : ℝ) / 8000000) / ((631001859 : ℝ) / 1000000000) - ((34641 : ℝ) / 40000) * (((55838703 : ℝ) / 125000000) / ((207621947 : ℝ) / 250000000)))
    hsc.1.le hxI
  have h6 := far_upper
    (c := sqrt 6 / 4) (cLo := ((153093 : ℝ) / 250000)) (cHi := ((612373 : ℝ) / 1000000)) (k := 3 * sqrt 6 / 4) (kHi := 3 * ((612373 : ℝ) / 1000000))
    a0 hx0 hx.1 hxb hb1 hbR p60 q61
    (lt_trans (by norm_num) sqrt_six_div_four_gt_153093) (sqrt_six_div_four_lt_one) (sqrt_six_div_four_gt_153093.le) (sqrt_six_div_four_lt_612373.le) (by positivity) (by norm_num) (s6_weight_le)
    (by norm_num : ((404 : ℝ) / 1000) ≤ ((153093 : ℝ) / 250000) * ((660 : ℝ) / 1000))
    (by norm_num : ((612373 : ℝ) / 1000000) * ((715 : ℝ) / 1000) ≤ ((438 : ℝ) / 1000))
    bAhi (lt_trans bA0 bAlo) bGlt p6Alo p6A0 p6Ggt (lt_trans p6G0 p6Glt)
    q6Ahi q6Glt q6G0 bG0 (lt_trans (lt_trans bA0 bAlo) bAhi)
    (by norm_num : (0 : ℝ) < ((416199611 : ℝ) / 500000000) / ((17024729 : ℝ) / 40000000) - ((153093 : ℝ) / 250000) * (((55838703 : ℝ) / 125000000) / ((207621947 : ℝ) / 250000000)))
    hsc.2.1.le hxI
  have hF := far_upper
    (c := dodecaFarScale) (cLo := ((535233 : ℝ) / 1000000)) (cHi := ((267617 : ℝ) / 500000)) (k := 3 / 2 * dodecaFarScale) (kHi := 3 / 2 * ((267617 : ℝ) / 500000))
    a0 hx0 hx.1 hxb hb1 hbR pF0 qF1
    (lt_trans (by norm_num) dodecaFarScale_gt_535233) (dodecaFarScale_lt_one) (dodecaFarScale_gt_535233.le) (dodecaFarScale_lt_267617.le) (mul_pos (by norm_num : (0 : ℝ) < 3 / 2) (lt_trans (by norm_num) dodecaFarScale_gt_535233)) (by norm_num) (far_weight_le)
    (by norm_num : ((353 : ℝ) / 1000) ≤ ((535233 : ℝ) / 1000000) * ((660 : ℝ) / 1000))
    (by norm_num : ((267617 : ℝ) / 500000) * ((715 : ℝ) / 1000) ≤ ((383 : ℝ) / 1000))
    bAhi (lt_trans bA0 bAlo) bGlt pFAlo pFA0 pFGgt (lt_trans pFG0 pFGlt)
    qFAhi qFGlt qFG0 bG0 (lt_trans (lt_trans bA0 bAlo) bAhi)
    (by norm_num : (0 : ℝ) < ((27275861 : ℝ) / 31250000) / ((45934817 : ℝ) / 125000000) - ((535233 : ℝ) / 1000000) * (((55838703 : ℝ) / 125000000) / ((207621947 : ℝ) / 250000000)))
    hsc.2.2.1.le hxI
  have hH := far_upper
    (c := (1 / 2)) (cLo := (1 / 2)) (cHi := (1 / 2)) (k := (1 / 4)) (kHi := (1 / 4))
    a0 hx0 hx.1 hxb hb1 hbR pH0 qH1
    (by norm_num) (by norm_num) (le_rfl) (le_rfl) (by norm_num) (by norm_num) (le_rfl)
    (by norm_num : ((330 : ℝ) / 1000) ≤ (1 / 2) * ((660 : ℝ) / 1000))
    (by norm_num : (1 / 2) * ((715 : ℝ) / 1000) ≤ ((358 : ℝ) / 1000))
    bAhi (lt_trans bA0 bAlo) bGlt pHAlo pHA0 pHGgt (lt_trans pHG0 pHGlt)
    qHAhi qHGlt qHG0 bG0 (lt_trans (lt_trans bA0 bAlo) bAhi)
    (by norm_num : (0 : ℝ) < ((222284941 : ℝ) / 250000000) / ((5341373 : ℝ) / 15625000) - (1 / 2) * (((55838703 : ℝ) / 125000000) / ((207621947 : ℝ) / 250000000)))
    hsc.2.2.2.le hxI
  exact deriv_pos_of_gap hxI hN h3 h6 hF hH (by norm_num)

private lemma deriv_pos_above_seven_twentieths {x : ℝ}
    (hx : x ∈ Ioo ((7 : ℝ) / 20) dodecaWall) : 0 < deriv dodecaResponse x := by
  have h7 : (7 : ℝ) / 20 = (350 : ℝ) / 1000 := by norm_num
  have hx350 : (350 : ℝ) / 1000 < x := by simpa [h7] using hx.1
  rcases le_or_gt x ((360 : ℝ) / 1000) with h360 | h360
  · exact deriv_pos_Ioc_350_360 ⟨hx350, h360⟩
  have hx360 : ((360 : ℝ) / 1000) < x := h360
  rcases le_or_gt x ((375 : ℝ) / 1000) with h375 | h375
  · exact deriv_pos_Ioc_360_375 ⟨hx360, h375⟩
  have hx375 : ((375 : ℝ) / 1000) < x := h375
  rcases le_or_gt x ((395 : ℝ) / 1000) with h395 | h395
  · exact deriv_pos_Ioc_375_395 ⟨hx375, h395⟩
  have hx395 : ((395 : ℝ) / 1000) < x := h395
  rcases le_or_gt x ((415 : ℝ) / 1000) with h415 | h415
  · exact deriv_pos_Ioc_395_415 ⟨hx395, h415⟩
  have hx415 : ((415 : ℝ) / 1000) < x := h415
  rcases le_or_gt x ((445 : ℝ) / 1000) with h445 | h445
  · exact deriv_pos_Ioc_415_445 ⟨hx415, h445⟩
  have hx445 : ((445 : ℝ) / 1000) < x := h445
  rcases le_or_gt x ((485 : ℝ) / 1000) with h485 | h485
  · exact deriv_pos_Ioc_445_485 ⟨hx445, h485⟩
  have hx485 : ((485 : ℝ) / 1000) < x := h485
  rcases le_or_gt x ((525 : ℝ) / 1000) with h525 | h525
  · exact deriv_pos_Ioc_485_525 ⟨hx485, h525⟩
  have hx525 : ((525 : ℝ) / 1000) < x := h525
  rcases le_or_gt x ((565 : ℝ) / 1000) with h565 | h565
  · exact deriv_pos_Ioc_525_565 ⟨hx525, h565⟩
  have hx565 : ((565 : ℝ) / 1000) < x := h565
  rcases le_or_gt x ((605 : ℝ) / 1000) with h605 | h605
  · exact deriv_pos_Ioc_565_605 ⟨hx565, h605⟩
  have hx605 : ((605 : ℝ) / 1000) < x := h605
  rcases le_or_gt x ((645 : ℝ) / 1000) with h645 | h645
  · exact deriv_pos_Ioc_605_645 ⟨hx605, h645⟩
  have hx645 : ((645 : ℝ) / 1000) < x := h645
  rcases le_or_gt x ((660 : ℝ) / 1000) with h660 | h660
  · exact deriv_pos_Ioc_645_660 ⟨hx645, h660⟩
  have hx660 : ((660 : ℝ) / 1000) < x := h660
  exact deriv_pos_Ioo_660_wall ⟨hx660, hx.2⟩

theorem strictMonoOn_dodecaResponse_past :
    StrictMonoOn dodecaResponse (Ico ((7 : ℝ) / 20) dodecaWall) := by
  refine strictMonoOn_of_deriv_pos (convex_Ico _ _) ?_ ?_
  · refine continuousOn_dodecaResponse.mono ?_
    intro x hx
    exact ⟨lt_of_lt_of_le (by norm_num : (0 : ℝ) < 7 / 20) hx.1, hx.2⟩
  · intro x hx
    rw [interior_Ico] at hx
    exact deriv_pos_above_seven_twentieths hx

theorem dodeca_root_gt_seven_twentieths {Z x : ℝ} (hZ : (8 : ℝ) ≤ Z)
    (hx : x ∈ Ioo (0 : ℝ) dodecaWall) (hR : dodecaResponse x = Z) :
    (7 : ℝ) / 20 < x := by
  by_contra hle
  have hlt := dodecaResponse_lt_eight_early ⟨hx.1, le_of_not_gt hle⟩
  linarith

theorem exists_unique_dodeca_outer_root {Z : ℝ} (hZ : (8 : ℝ) ≤ Z) :
    ∃! x : ℝ, x ∈ Ioo (0 : ℝ) dodecaWall ∧ dodecaResponse x = Z := by
  have hcut : dodecaResponse (7 / 20 : ℝ) < Z :=
    lt_of_lt_of_le (dodecaResponse_lt_eight_early ⟨by norm_num, le_rfl⟩) hZ
  obtain ⟨u, hu, hugt⟩ :=
    exists_dodecaResponse_gt (M := Z) (lt_of_lt_of_le (by norm_num) hZ)
  have hu7 : (7 : ℝ) / 20 < u := by
    by_contra hle
    have hlt := dodecaResponse_lt_eight_early ⟨hu.1, le_of_not_gt hle⟩
    linarith
  have hcont : ContinuousOn dodecaResponse (Icc ((7 : ℝ) / 20) u) := by
    refine continuousOn_dodecaResponse.mono ?_
    intro t ht
    exact ⟨lt_of_lt_of_le (by norm_num : (0 : ℝ) < 7 / 20) ht.1,
      lt_of_le_of_lt ht.2 hu.2⟩
  obtain ⟨x, hxI, hxeq⟩ := intermediate_value_Ioo hu7.le hcont
    (show Z ∈ Ioo (dodecaResponse (7 / 20 : ℝ)) (dodecaResponse u) from ⟨hcut, hugt⟩)
  have hx : x ∈ Ioo (0 : ℝ) dodecaWall :=
    ⟨lt_trans (by norm_num) hxI.1, lt_trans hxI.2 hu.2⟩
  refine ExistsUnique.intro x ⟨hx, hxeq⟩ ?_
  intro y hy
  have hy7 : (7 : ℝ) / 20 < y := dodeca_root_gt_seven_twentieths hZ hy.1 hy.2
  have hx7 : (7 : ℝ) / 20 < x := hxI.1
  exact strictMonoOn_dodecaResponse_past.injOn
    ⟨hy7.le, hy.1.2⟩ ⟨hx7.le, hx.2⟩ (hy.2.trans hxeq.symm)

theorem dodeca_outer_root_radius {Z x : ℝ} (hZ : (8 : ℝ) ≤ Z)
    (hx : x ∈ Ioo (0 : ℝ) dodecaWall) (hR : dodecaResponse x = Z) :
    (7 : ℝ) / 10 < 1 / (2 * x) ∧ 1 / (2 * x) < (10 : ℝ) / 7 := by
  have hx7 : (7 : ℝ) / 20 < x := dodeca_root_gt_seven_twentieths hZ hx hR
  have hx5 : x < (5 : ℝ) / 7 := lt_trans hx.2 dodecaWall_lt_five_sevenths
  have h2 : (0 : ℝ) < 2 * x := mul_pos (by norm_num) hx.1
  refine ⟨?_, ?_⟩
  · rw [lt_div_iff₀ h2]
    have hx2 : 2 * x < 2 * ((5 : ℝ) / 7) := mul_lt_mul_of_pos_left hx5 (by norm_num)
    have hx2' : 2 * x < (10 : ℝ) / 7 := by
      have h10 : 2 * ((5 : ℝ) / 7) = 10 / 7 := by norm_num
      linarith
    have hmul : (7 : ℝ) / 10 * (2 * x) < (7 : ℝ) / 10 * ((10 : ℝ) / 7) :=
      mul_lt_mul_of_pos_left hx2' (by norm_num)
    have hone : (7 : ℝ) / 10 * ((10 : ℝ) / 7) = 1 := by norm_num
    linarith
  · rw [div_lt_iff₀ h2]
    have hx2 : 2 * ((7 : ℝ) / 20) < 2 * x := mul_lt_mul_of_pos_left hx7 (by norm_num)
    have hx2' : (7 : ℝ) / 10 < 2 * x := by
      have h7 : 2 * ((7 : ℝ) / 20) = 7 / 10 := by norm_num
      linarith
    have hmul : (10 : ℝ) / 7 * ((7 : ℝ) / 10) < (10 : ℝ) / 7 * (2 * x) :=
      mul_lt_mul_of_pos_left hx2' (by norm_num)
    have hone : (10 : ℝ) / 7 * ((7 : ℝ) / 10) = 1 := by norm_num
    linarith

theorem dodeca_outer_root_restoring {Z x y : ℝ} (hZ : (8 : ℝ) ≤ Z)
    (hx : x ∈ Ioo (0 : ℝ) dodecaWall) (hR : dodecaResponse x = Z)
    (hy : y ∈ Ioo (0 : ℝ) dodecaWall) :
    (y < x → dodecaOutward Z y < 0) ∧ (y = x → dodecaOutward Z y = 0) ∧
      (x < y → 0 < dodecaOutward Z y) := by
  have hγ : 0 < gammaSEqual y :=
    gammaSEqual_pos_left_of_first_node ⟨hy.1, lt_trans hy.2 dodecaWall_mem_Ioo.2⟩
  have hx7 : (7 : ℝ) / 20 < x := dodeca_root_gt_seven_twentieths hZ hx hR
  refine ⟨?_, ?_, ?_⟩
  · intro hyx
    rw [dodecaOutward_eq_on_wall hy]
    rcases le_or_gt y ((7 : ℝ) / 20) with hle | hgt
    · apply div_neg_of_neg_of_pos _ hγ
      have hlt := dodecaResponse_lt_eight_early ⟨hy.1, hle⟩
      linarith
    · apply div_neg_of_neg_of_pos _ hγ
      have hlt := strictMonoOn_dodecaResponse_past ⟨hgt.le, hy.2⟩ ⟨hx7.le, hx.2⟩ hyx
      linarith
  · intro heq
    have hzero : dodecaResponse y - Z = 0 := by rw [heq, hR, sub_self]
    rw [dodecaOutward_eq_on_wall hy, hzero, zero_div]
  · intro hxy
    rw [dodecaOutward_eq_on_wall hy]
    apply div_pos _ hγ
    have hlt := strictMonoOn_dodecaResponse_past
      ⟨hx7.le, hx.2⟩ ⟨(lt_trans hx7 hxy).le, hy.2⟩ hxy
    linarith

end Gravity

end DstDiophantine
