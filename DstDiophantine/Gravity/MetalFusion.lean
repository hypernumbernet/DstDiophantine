import DstDiophantine.Gravity.ElectronMetal
import DstDiophantine.Gravity.ElectronNumbers
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# A proton pair in an octahedral hole

Lengths are in units of the electromagnetic `ℓ`, and the axial component is
in units of `k e²/ℓ²`. Six ions of charge `Z` sit at `±a` on each axis of an
orthonormal frame. Two protons sit at `±t` on the third axis.

The separation-increasing component on the proton at `+t` is
`octaPairOutward`. Each ion contributes `Z · pullRate(x) · ⟨p - c, axis⟩`,
and `pullRate(x) · r = pairAttraction(x)` when the separation from that ion
is `r`. The partner contributes `pairAttraction` at the phase of separation
`2t`.

## Paper boundary (do **not** claim)

No rate, no heat, and no choice among experiments is derived. The
electromagnetic length and the nuclear length are not identified. No
infinite lattice sum is taken. Screening is not introduced.

## What is proved

* For every ion charge `Z ≥ 1`, at cage radius `2` and proton half-separation
  `1`, the axial component is strictly negative.
* As the half-separation descends to `1/(4x₁)`, the component tends to `+∞`.
* On the half-separations strictly between `1/(4x₁)` and `1`, the component
  falls strictly. The balance is therefore unique, outward on its inner side
  and inward on its outer side.
-/

namespace DstDiophantine

namespace Gravity

open Real Set Filter

/-! ### Bounds on the interference factor -/

/-- `γ_s(x) ≥ 1 - x² cosh x` for `x ≥ 0`. -/
private lemma gammaSEqual_ge_one_sub_sq_cosh {x : ℝ} (hx : 0 ≤ x) :
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
private lemma gammaSEqual_le_two_cos_sub_one {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
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

private lemma exp_one_sixth_le : exp (1 / 6 : ℝ) ≤ 6 / 5 := by
  have h := exp_bound' (x := 1 / 6) (by norm_num) (by norm_num) (n := 4) (by decide)
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h
  exact h.trans (by norm_num)

private lemma exp_one_quarter_le : exp (1 / 4 : ℝ) ≤ 13 / 10 := by
  have h := exp_bound' (x := 1 / 4) (by norm_num) (by norm_num) (n := 5) (by decide)
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h
  exact h.trans (by norm_num)

private lemma gamma_one_sixth_ge : (29 / 30 : ℝ) ≤ gammaSEqual (1 / 6) := by
  have h := gammaSEqual_ge_one_sub_sq_cosh (x := 1 / 6) (by norm_num)
  have hc := cosh_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 6)
  have hexp := exp_one_sixth_le
  have : (1 / 6 : ℝ) ^ 2 * cosh (1 / 6) ≤ (1 / 36) * (6 / 5) := by nlinarith
  linarith

private lemma gamma_one_quarter_ge : (147 / 160 : ℝ) ≤ gammaSEqual (1 / 4) := by
  have h := gammaSEqual_ge_one_sub_sq_cosh (x := 1 / 4) (by norm_num)
  have hc := cosh_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4)
  have hexp := exp_one_quarter_le
  have : (1 / 4 : ℝ) ^ 2 * cosh (1 / 4) ≤ (1 / 16) * (13 / 10) := by nlinarith
  linarith

private lemma cos_half_le : cos (1 / 2 : ℝ) ≤ 1349 / 1536 := by
  have hb := cos_bound (x := (1 / 2 : ℝ)) (by norm_num)
  have hle := (abs_sub_le_iff.mp hb).1
  have hpoly : (1 : ℝ) - (1 / 2) ^ 2 / 2 = 7 / 8 := by norm_num
  have hpow : ((1 / 2 : ℝ) ^ 4) * (5 / 96) = 5 / 1536 := by norm_num
  have hsum : (7 / 8 : ℝ) + 5 / 1536 = 1349 / 1536 := by norm_num
  linarith

private lemma gamma_half_le : gammaSEqual (1 / 2 : ℝ) ≤ 581 / 768 := by
  have hγ := gammaSEqual_le_two_cos_sub_one (x := 1 / 2) (by norm_num) (by norm_num)
  have hc := cos_half_le
  have : 2 * cos (1 / 2 : ℝ) - 1 ≤ 581 / 768 := by
    have h2 : 2 * (1349 / 1536 : ℝ) - 1 = 581 / 768 := by norm_num
    linarith
  linarith

/-! ### The axial component -/

/-- Separation-increasing component for ions of charge `Z` on the octahedron
of radius `a`, with protons at half-separation `t`. -/
noncomputable def octaPairOutward (Z a t : ℝ) : ℝ :=
  -Z * pairAttraction (1 / (2 * (a - t)))
  + Z * pairAttraction (1 / (2 * (a + t)))
  + 4 * Z * pullRate (1 / (2 * sqrt (a ^ 2 + t ^ 2))) * t
  + pairAttraction (1 / (4 * t))

private lemma sqrt_five_gt : (11 / 5 : ℝ) < sqrt 5 := by
  have hsq : (11 / 5 : ℝ) ^ 2 < (sqrt 5) ^ 2 := by
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)]
    norm_num
  exact (sq_lt_sq₀ (by norm_num) (Real.sqrt_nonneg 5)).mp hsq

private lemma gamma_eqPhase_ge : (187 / 200 : ℝ) ≤ gammaSEqual (1 / (2 * sqrt 5)) := by
  have hx0 : 0 ≤ 1 / (2 * sqrt 5) := by positivity
  have hx : 1 / (2 * sqrt 5) ≤ 1 / 4 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have hs : (11 / 5 : ℝ) < sqrt 5 := sqrt_five_gt
    nlinarith
  have h := gammaSEqual_ge_one_sub_sq_cosh hx0
  have hc := cosh_le_exp_of_nonneg hx0
  have hexp : exp (1 / (2 * sqrt 5)) ≤ 13 / 10 :=
    le_trans (exp_le_exp.mpr hx) exp_one_quarter_le
  have hx2 : (1 / (2 * sqrt 5)) ^ 2 = 1 / 20 := by
    rw [div_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)]
    norm_num
  have : (1 / (2 * sqrt 5)) ^ 2 * cosh (1 / (2 * sqrt 5)) ≤ (1 / 20) * (13 / 10) := by
    rw [hx2]
    have hc' : cosh (1 / (2 * sqrt 5)) ≤ 13 / 10 := le_trans hc hexp
    nlinarith
  linarith

private lemma equatorial_le : 4 * pullRate (1 / (2 * sqrt 5)) ≤ 800 / 2057 := by
  have hγ := gamma_eqPhase_ge
  have hγpos : 0 < gammaSEqual (1 / (2 * sqrt 5)) := by linarith
  have hcube : (sqrt 5) ^ 3 = 5 * sqrt 5 := by
    have hsq : sqrt 5 * sqrt 5 = 5 := Real.mul_self_sqrt (by norm_num)
    calc (sqrt 5) ^ 3 = sqrt 5 * (sqrt 5 * sqrt 5) := by ring
      _ = sqrt 5 * 5 := by rw [hsq]
      _ = 5 * sqrt 5 := by ring
  have hden5 : (2 * sqrt 5) ^ 3 = 40 * sqrt 5 := by
    rw [mul_pow, hcube]
    ring
  have hnum : 4 * (8 * (1 / (2 * sqrt 5)) ^ 3) = 4 / (5 * sqrt 5) := by
    rw [div_pow, hden5]
    field_simp
    ring
  unfold pullRate
  have hrew : 4 * (8 * (1 / (2 * sqrt 5)) ^ 3 / gammaSEqual (1 / (2 * sqrt 5)))
      = (4 / (5 * sqrt 5)) / gammaSEqual (1 / (2 * sqrt 5)) := by
    rw [← hnum]
    field_simp
  rw [hrew, div_div]
  have hden : 5 * (11 / 5) * (187 / 200) ≤ 5 * sqrt 5 * gammaSEqual (1 / (2 * sqrt 5)) := by
    have hs := sqrt_five_gt.le
    nlinarith
  have hfrac : 4 / (5 * sqrt 5 * gammaSEqual (1 / (2 * sqrt 5)))
      ≤ 4 / (5 * (11 / 5) * (187 / 200)) := by
    have hpos : (0 : ℝ) < 5 * (11 / 5) * (187 / 200) := by norm_num
    exact div_le_div_of_nonneg_left (by norm_num) hpos hden
  have hr : (4 : ℝ) / (5 * (11 / 5) * (187 / 200)) = 800 / 2057 := by norm_num
  linarith

private lemma positive_pieces_lt :
    pairAttraction (1 / 6) + 4 * pullRate (1 / (2 * sqrt 5)) + pairAttraction (1 / 4)
      < 768 / 581 := by
  have h6 := gamma_one_sixth_ge
  have h4 := gamma_one_quarter_ge
  have h6pos : 0 < gammaSEqual (1 / 6 : ℝ) := by linarith
  have h4pos : 0 < gammaSEqual (1 / 4 : ℝ) := by linarith
  have hy6 : pairAttraction (1 / 6) ≤ 10 / 87 := by
    unfold pairAttraction
    have hnum : (4 : ℝ) * (1 / 6) ^ 2 = 1 / 9 := by norm_num
    rw [hnum, div_le_iff₀ h6pos]
    have : (10 / 87 : ℝ) * (29 / 30) = 1 / 9 := by norm_num
    nlinarith
  have hy4 : pairAttraction (1 / 4) ≤ 40 / 147 := by
    unfold pairAttraction
    have hnum : (4 : ℝ) * (1 / 4) ^ 2 = 1 / 4 := by norm_num
    rw [hnum, div_le_iff₀ h4pos]
    have : (40 / 147 : ℝ) * (147 / 160) = 1 / 4 := by norm_num
    nlinarith
  have heq := equatorial_le
  have hsum : (10 / 87 : ℝ) + 800 / 2057 + 40 / 147 < 768 / 581 := by norm_num
  linarith

theorem octaPairOutward_neg_at_halfRadius {Z : ℝ} (hZ : 1 ≤ Z) :
    octaPairOutward Z 2 1 < 0 := by
  have hhalf := gamma_half_le
  have hpos : 0 < gammaSEqual (1 / 2 : ℝ) :=
    gammaSEqual_pos_left_of_first_node ⟨by norm_num, lt_trans (by norm_num) firstNode_num_window.1⟩
  have hy : 768 / 581 ≤ pairAttraction (1 / 2) := by
    unfold pairAttraction
    have hnum : (4 : ℝ) * (1 / 2) ^ 2 = 1 := by norm_num
    rw [hnum, le_div_iff₀ hpos]
    nlinarith
  have hpieces := positive_pieces_lt
  have hnear : 0 ≤ pairAttraction (1 / 2) :=
    (pairAttraction_pos_outer ⟨by norm_num, lt_trans (by norm_num) firstNode_num_window.1⟩).le
  have hfar : 0 ≤ pairAttraction (1 / 6) :=
    (pairAttraction_pos_outer ⟨by norm_num, lt_trans (by norm_num) firstNode_num_window.1⟩).le
  have hpull : 0 ≤ pullRate (1 / (2 * sqrt 5)) := by
    unfold pullRate
    have hγ : 0 < gammaSEqual (1 / (2 * sqrt 5)) := by linarith [gamma_eqPhase_ge]
    positivity
  unfold octaPairOutward
  have hnearφ : 1 / (2 * ((2 : ℝ) - 1)) = 1 / 2 := by norm_num
  have hfarφ : 1 / (2 * ((2 : ℝ) + 1)) = 1 / 6 := by norm_num
  have hs : (2 : ℝ) ^ 2 + 1 ^ 2 = 5 := by norm_num
  have heqφ : 1 / (2 * sqrt ((2 : ℝ) ^ 2 + 1 ^ 2)) = 1 / (2 * sqrt 5) := by rw [hs]
  have hp : 1 / (4 * (1 : ℝ)) = 1 / 4 := by norm_num
  rw [hnearφ, hfarφ, heqφ, hp]
  have hC : -pairAttraction (1 / 2) + pairAttraction (1 / 6) + 4 * pullRate (1 / (2 * sqrt 5))
      < -pairAttraction (1 / 4) := by
    linarith [hpieces]
  have hCneg : -pairAttraction (1 / 2) + pairAttraction (1 / 6) + 4 * pullRate (1 / (2 * sqrt 5))
      < 0 := by
    have hp4 : 0 < pairAttraction (1 / 4) :=
      pairAttraction_pos_outer ⟨by norm_num, lt_trans (by norm_num) firstNode_num_window.1⟩
    linarith
  have hscale : -Z * pairAttraction (1 / 2) + Z * pairAttraction (1 / 6)
      + 4 * Z * pullRate (1 / (2 * sqrt 5))
      ≤ -pairAttraction (1 / 2) + pairAttraction (1 / 6) + 4 * pullRate (1 / (2 * sqrt 5)) := by
    have hmul : (Z - 1) * (-pairAttraction (1 / 2) + pairAttraction (1 / 6)
        + 4 * pullRate (1 / (2 * sqrt 5))) ≤ 0 := by
      have hZ0 : 0 ≤ Z - 1 := by linarith
      exact mul_nonpos_of_nonneg_of_nonpos hZ0 (le_of_lt hCneg)
    linarith
  linarith

/-! ### Divergence at the charge node -/

theorem tendsto_pairAttraction_firstNode :
    Tendsto pairAttraction (nhdsWithin resonanceRoot1 (Iio resonanceRoot1)) atTop := by
  rw [tendsto_atTop]
  intro b
  obtain ⟨δ, hδ0, hδ⟩ :=
    (Metric.continuousAt_iff.mp continuous_gammaSEqual.continuousAt) (1 / (|b| + 1)) (by positivity)
  have hx1pos : 0 < resonanceRoot1 := lt_trans (by norm_num) firstNode_num_window.1
  set η := min δ (resonanceRoot1 / 2)
  have hη0 : 0 < η := lt_min hδ0 (by linarith)
  set x := resonanceRoot1 - η / 2
  have hx_lt : x < resonanceRoot1 := by dsimp [x]; linarith
  have hx_gt : 1 / 2 < x := by
    have hmin : η ≤ resonanceRoot1 / 2 := min_le_right _ _
    have hx1 := firstNode_num_window.1
    dsimp [x]
    nlinarith
  have hdist : dist x resonanceRoot1 < δ := by
    rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (by linarith : 0 ≤ resonanceRoot1 - x)]
    have : resonanceRoot1 - x = η / 2 := by dsimp [x]; ring
    have hηδ : η ≤ δ := min_le_left _ _
    linarith
  have hγabs : |gammaSEqual x| < 1 / (|b| + 1) := by
    simpa [resonanceRoot1_gammaSEqual_zero] using hδ hdist
  have hγpos : 0 < gammaSEqual x :=
    gammaSEqual_pos_left_of_first_node ⟨by linarith, hx_lt⟩
  have hγlt : gammaSEqual x < 1 / (|b| + 1) := (abs_lt.mp hγabs).2
  have hY : |b| + 1 < pairAttraction x := by
    unfold pairAttraction
    rw [lt_div_iff₀ hγpos]
    have hmul : (|b| + 1) * gammaSEqual x < 1 := by
      have h1 : (|b| + 1) * (1 / (|b| + 1)) = 1 := by field_simp
      have := mul_lt_mul_of_pos_left hγlt (by positivity : 0 < |b| + 1)
      linarith
    have hx2 : 1 < 4 * x ^ 2 := by nlinarith
    linarith
  have hmem : Ioo x resonanceRoot1 ∈ nhdsWithin resonanceRoot1 (Iio resonanceRoot1) := by
    rw [mem_nhdsWithin]
    refine ⟨Ioi x, isOpen_Ioi, hx_lt, ?_⟩
    intro y hy
    exact ⟨hy.1, hy.2⟩
  refine eventually_of_mem hmem ?_
  intro y hy
  have hyx : x < y := hy.1
  have hy0 : 0 < y := by linarith [hx_gt, hyx]
  have hγy : 0 < gammaSEqual y := gammaSEqual_pos_left_of_first_node ⟨hy0, hy.2⟩
  have hγy_lt : gammaSEqual y < gammaSEqual x := by
    have hanti := strictAntiOn_gammaSEqual_even 0
    have hπx : x < π := by linarith [pi_gt_three, hx_lt, firstNode_num_window.2]
    have hπy : y < π := by linarith [pi_gt_three, hy.2, firstNode_num_window.2]
    have hxI : x ∈ Icc (((2 * 0 : ℕ) : ℝ) * π) (((2 * 0 : ℕ) : ℝ) * π + π) := by
      simpa using (⟨by linarith, hπx.le⟩ : x ∈ Icc (0 : ℝ) π)
    have hyI : y ∈ Icc (((2 * 0 : ℕ) : ℝ) * π) (((2 * 0 : ℕ) : ℝ) * π + π) := by
      simpa using (⟨by linarith, hπy.le⟩ : y ∈ Icc (0 : ℝ) π)
    exact hanti hxI hyI hyx
  have hdiv : |b| + 1 < pairAttraction y := by
    unfold pairAttraction
    rw [lt_div_iff₀ hγy]
    have hleft : (|b| + 1) * gammaSEqual y < (|b| + 1) * gammaSEqual x :=
      mul_lt_mul_of_pos_left hγy_lt (by positivity)
    have hmid : (|b| + 1) * gammaSEqual x < 4 * x ^ 2 := by
      unfold pairAttraction at hY
      rwa [lt_div_iff₀ hγpos] at hY
    have hy2 : 4 * x ^ 2 < 4 * y ^ 2 := by nlinarith [hyx, hx_gt]
    linarith
  have hb : b ≤ |b| := le_abs_self b
  linarith

private lemma nodeHalf_mem : 1 / (4 * resonanceRoot1) ∈ Ioo (5 / 19 : ℝ) (15 / 56) := by
  have h := firstNode_num_window
  have hx : 0 < resonanceRoot1 := lt_trans (by norm_num) h.1
  refine ⟨?_, ?_⟩
  · have hmul : (5 / 19 : ℝ) * (4 * resonanceRoot1) < 1 := by nlinarith
    rw [lt_div_iff₀ (by positivity)]
    linarith
  · have hmul : 1 < (15 / 56 : ℝ) * (4 * resonanceRoot1) := by nlinarith
    rw [div_lt_iff₀ (by positivity)]
    linarith

private lemma phase_outer_on_cage {u : ℝ} (hu0 : 5 / 19 ≤ u) (hu1 : u ≤ 1) :
    1 / (2 * (2 - u)) ∈ Ioo 0 resonanceRoot1 ∧
      1 / (2 * (2 + u)) ∈ Ioo 0 resonanceRoot1 ∧
      1 / (2 * sqrt (4 + u ^ 2)) ∈ Ioo 0 resonanceRoot1 := by
  have hx1 : 1 / 2 < resonanceRoot1 := lt_trans (by norm_num) firstNode_num_window.1
  have hden : 0 < 2 - u := by linarith
  have hnear : 1 / (2 * (2 - u)) ≤ 1 / 2 := by
    have hge : (2 : ℝ) ≤ 2 * (2 - u) := by nlinarith
    exact one_div_le_one_div_of_le (by norm_num) hge
  have hfar : 1 / (2 * (2 + u)) < 1 / 4 := by
    have hgt : (4 : ℝ) < 2 * (2 + u) := by nlinarith
    exact one_div_lt_one_div_of_lt (by norm_num) hgt
  have hsqrt : (2 : ℝ) ≤ sqrt (4 + u ^ 2) := by
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have heq : 1 / (2 * sqrt (4 + u ^ 2)) ≤ 1 / 4 :=
    one_div_le_one_div_of_le (by norm_num) (by nlinarith)
  exact ⟨⟨by positivity, lt_of_le_of_lt hnear hx1⟩,
    ⟨by positivity, lt_trans hfar (lt_trans (by norm_num) hx1)⟩,
    ⟨by positivity, lt_of_le_of_lt heq (lt_trans (by norm_num) hx1)⟩⟩

private lemma continuousOn_pairAttraction_outer :
    ContinuousOn pairAttraction (Ioo 0 resonanceRoot1) := by
  unfold pairAttraction
  refine ContinuousOn.div (continuousOn_id.pow 2 |>.const_mul 4)
    continuous_gammaSEqual.continuousOn ?_
  intro x hx
  exact (gammaSEqual_pos_left_of_first_node hx).ne'

private lemma continuousOn_pullRate_outer :
    ContinuousOn pullRate (Ioo 0 resonanceRoot1) := by
  unfold pullRate
  refine ContinuousOn.div (continuousOn_id.pow 3 |>.const_mul 8)
    continuous_gammaSEqual.continuousOn ?_
  intro x hx
  exact (gammaSEqual_pos_left_of_first_node hx).ne'

private lemma continuousOn_cage {Z : ℝ} :
    ContinuousOn (fun t : ℝ =>
      -Z * pairAttraction (1 / (2 * (2 - t))) + Z * pairAttraction (1 / (2 * (2 + t)))
        + 4 * Z * pullRate (1 / (2 * sqrt (4 + t ^ 2))) * t) (Icc (5 / 19) 1) := by
  have hY := continuousOn_pairAttraction_outer
  have hP := continuousOn_pullRate_outer
  have hnear : ContinuousOn (fun u : ℝ => 1 / (2 * (2 - u))) (Icc (5 / 19) 1) := by
    refine ContinuousOn.div continuousOn_const
      (continuousOn_const.mul (continuousOn_const.sub continuousOn_id)) ?_
    intro u hu
    exact ne_of_gt (by linarith [hu.2] : (0 : ℝ) < 2 * (2 - u))
  have hfar : ContinuousOn (fun u : ℝ => 1 / (2 * (2 + u))) (Icc (5 / 19) 1) := by
    refine ContinuousOn.div continuousOn_const
      (continuousOn_const.mul (continuousOn_const.add continuousOn_id)) ?_
    intro u hu
    exact ne_of_gt (by linarith [hu.1] : (0 : ℝ) < 2 * (2 + u))
  have heq : ContinuousOn (fun u : ℝ => 1 / (2 * sqrt (4 + u ^ 2))) (Icc (5 / 19) 1) := by
    have hsq : ContinuousOn (fun u : ℝ => sqrt (4 + u ^ 2)) (Icc (5 / 19) 1) :=
      continuous_sqrt.comp_continuousOn (continuousOn_const.add (continuousOn_id.pow 2))
    refine ContinuousOn.div continuousOn_const (continuousOn_const.mul hsq) ?_
    intro u hu
    exact ne_of_gt (by positivity : (0 : ℝ) < 2 * sqrt (4 + u ^ 2))
  have h1 : ContinuousOn (fun u : ℝ => -Z * pairAttraction (1 / (2 * (2 - u))))
      (Icc (5 / 19) 1) := by
    refine ContinuousOn.congr
      ((hY.comp hnear (fun u hu => (phase_outer_on_cage hu.1 hu.2).1)).const_mul (-Z)) ?_
    intro u _
    simp [Function.comp_apply]
  have h2 : ContinuousOn (fun u : ℝ => Z * pairAttraction (1 / (2 * (2 + u))))
      (Icc (5 / 19) 1) := by
    refine ContinuousOn.congr
      ((hY.comp hfar (fun u hu => (phase_outer_on_cage hu.1 hu.2).2.1)).const_mul Z) ?_
    intro u _
    simp [Function.comp_apply]
  have h3 : ContinuousOn
      (fun u : ℝ => 4 * Z * pullRate (1 / (2 * sqrt (4 + u ^ 2))) * u) (Icc (5 / 19) 1) := by
    refine ContinuousOn.congr
      (((hP.comp heq (fun u hu => (phase_outer_on_cage hu.1 hu.2).2.2)).const_mul (4 * Z)).mul
        continuousOn_id) ?_
    intro u _
    simp [Function.comp_apply]
  refine ContinuousOn.congr (h1.add (h2.add h3)) ?_
  intro u _
  simp only [Pi.add_apply]
  abel

theorem tendsto_octaPairOutward_node {Z : ℝ} :
    Tendsto (octaPairOutward Z 2)
      (nhdsWithin (1 / (4 * resonanceRoot1)) (Ioi (1 / (4 * resonanceRoot1)))) atTop := by
  set t0 := 1 / (4 * resonanceRoot1)
  have ht0 := nodeHalf_mem
  let cage : ℝ → ℝ := fun t =>
    -Z * pairAttraction (1 / (2 * (2 - t))) + Z * pairAttraction (1 / (2 * (2 + t)))
      + 4 * Z * pullRate (1 / (2 * sqrt (4 + t ^ 2))) * t
  have hcage : ContinuousOn cage (Icc (5 / 19) 1) := continuousOn_cage
  have ht0int : t0 ∈ Ioo (5 / 19) 1 := ⟨ht0.1, lt_trans ht0.2 (by norm_num)⟩
  have htend_cage : Tendsto cage (nhdsWithin t0 (Ioi t0)) (nhds (cage t0)) := by
    refine ((hcage.continuousAt
      (Icc_mem_nhds (by linarith [ht0int.1]) (by linarith [ht0int.2]))).tendsto.mono_left
        nhdsWithin_le_nhds)
  have hphase : Tendsto (fun t : ℝ => 1 / (4 * t)) (nhdsWithin t0 (Ioi t0))
      (nhdsWithin resonanceRoot1 (Iio resonanceRoot1)) := by
    have hcont : ContinuousAt (fun t : ℝ => 1 / (4 * t)) t0 := by
      refine ContinuousAt.div₀ continuousAt_const (continuousAt_const.mul continuousAt_id) ?_
      exact ne_of_gt (by linarith [ht0.1] : (0 : ℝ) < 4 * t0)
    have hnhds : Tendsto (fun t : ℝ => 1 / (4 * t)) (nhds t0) (nhds resonanceRoot1) := by
      have heq : 1 / (4 * t0) = resonanceRoot1 := by
        dsimp [t0]
        field_simp
      simpa [heq] using hcont.tendsto
    refine tendsto_nhdsWithin_iff.mpr ⟨hnhds.mono_left nhdsWithin_le_nhds, ?_⟩
    refine eventually_of_mem self_mem_nhdsWithin ?_
    intro t ht
    have ht0pos : (0 : ℝ) < t0 := lt_trans (by norm_num) ht0.1
    have hlt : t0 < t := ht
    have : 1 / (4 * t) < 1 / (4 * t0) :=
      one_div_lt_one_div_of_lt (by nlinarith [ht0pos]) (by nlinarith [hlt])
    have ht0eq : 1 / (4 * t0) = resonanceRoot1 := by
      dsimp [t0]
      field_simp
    rw [← ht0eq]
    exact this
  have hpartner := tendsto_pairAttraction_firstNode.comp hphase
  have hsum := htend_cage.add_atTop hpartner
  have hEq : ∀ t : ℝ, octaPairOutward Z 2 t = cage t + pairAttraction (1 / (4 * t)) := by
    intro t
    unfold octaPairOutward cage
    rw [show (2 : ℝ) ^ 2 = 4 by norm_num]
  refine hsum.congr' ?_
  exact Filter.Eventually.of_forall fun t => by
    simp only [Function.comp_apply]
    exact (hEq t).symm

/-- For an ion charge at least one, the axial component changes from outward,
just outside the first charge node, to inward at separation `2`. A balance
lies strictly between them. -/
theorem exists_octa_pair_balance {Z : ℝ} (hZ : 1 ≤ Z) :
    ∃ s, 1 / (2 * resonanceRoot1) < s ∧ s < 2 ∧ octaPairOutward Z 2 (s / 2) = 0 := by
  set t0 := 1 / (4 * resonanceRoot1)
  have ht0 := nodeHalf_mem
  have hdiv := tendsto_octaPairOutward_node (Z := Z)
  have hpos : ∀ᶠ t in nhdsWithin t0 (Ioi t0), 0 < octaPairOutward Z 2 t :=
    hdiv.eventually (eventually_gt_atTop 0)
  have hI : Ioo t0 1 ∈ nhdsWithin t0 (Ioi t0) := by
    rw [mem_nhdsWithin]
    refine ⟨Iio 1, isOpen_Iio, lt_trans ht0.2 (by norm_num), ?_⟩
    intro t ht
    exact ⟨ht.2, ht.1⟩
  obtain ⟨t, hFt, htI⟩ := (hpos.and (eventually_of_mem hI fun _ h => h)).exists
  have hneg := octaPairOutward_neg_at_halfRadius (Z := Z) hZ
  have hcont : ContinuousOn (octaPairOutward Z 2) (Icc t 1) := by
    have hY := continuousOn_pairAttraction_outer
    have htpos : (0 : ℝ) < t := lt_trans (lt_trans (by norm_num) ht0.1) htI.1
    have hpart : ContinuousOn (fun u : ℝ => 1 / (4 * u)) (Icc t 1) := by
      refine ContinuousOn.div continuousOn_const (continuousOn_const.mul continuousOn_id) ?_
      intro u hu
      exact ne_of_gt (by nlinarith [htpos, hu.1] : (0 : ℝ) < 4 * u)
    have hpartS : MapsTo (fun u : ℝ => 1 / (4 * u)) (Icc t 1) (Ioo 0 resonanceRoot1) := by
      intro u hu
      have hu0 : 0 < u := by nlinarith [htpos, hu.1]
      refine ⟨by positivity, ?_⟩
      have hle : 1 / (4 * u) ≤ 1 / (4 * t) :=
        one_div_le_one_div_of_le (by linarith) (by nlinarith [hu.1])
      have hlt : 1 / (4 * t) < 1 / (4 * t0) :=
        one_div_lt_one_div_of_lt (by nlinarith [ht0.1]) (by nlinarith [htI.1])
      have ht0eq : 1 / (4 * t0) = resonanceRoot1 := by
        dsimp [t0]; field_simp
      linarith
    have hcage : ContinuousOn (fun u : ℝ =>
        -Z * pairAttraction (1 / (2 * (2 - u))) + Z * pairAttraction (1 / (2 * (2 + u)))
          + 4 * Z * pullRate (1 / (2 * sqrt (4 + u ^ 2))) * u) (Icc t 1) :=
      continuousOn_cage.mono (by
        intro u hu
        exact ⟨le_trans (le_of_lt ht0.1) (le_trans (le_of_lt htI.1) hu.1), hu.2⟩)
    have hpartner : ContinuousOn (fun u : ℝ => pairAttraction (1 / (4 * u))) (Icc t 1) := by
      refine ContinuousOn.congr (hY.comp hpart hpartS) ?_
      intro u _
      simp [Function.comp_apply]
    refine (hcage.add hpartner).congr ?_
    intro u _
    unfold octaPairOutward
    rw [show (2 : ℝ) ^ 2 = 4 by norm_num]
    simp only [Pi.add_apply]
  have h0 : (0 : ℝ) ∈ Icc (octaPairOutward Z 2 1) (octaPairOutward Z 2 t) :=
    ⟨hneg.le, hFt.le⟩
  have himg := intermediate_value_Icc' htI.2.le hcont h0
  rw [mem_image] at himg
  obtain ⟨c, hc, hc0⟩ := himg
  have hc_lt : c < 1 := by
    by_contra hge
    have hc1 : c = 1 := le_antisymm hc.2 (not_lt.mp hge)
    have : octaPairOutward Z 2 1 < 0 := hneg
    rw [hc1] at hc0
    linarith
  have hc_gt : t0 < c := lt_of_lt_of_le htI.1 hc.1
  refine ⟨2 * c, ?_, ?_, ?_⟩
  · dsimp [t0] at hc_gt
    have : 1 / (2 * resonanceRoot1) = 2 * (1 / (4 * resonanceRoot1)) := by field_simp; ring
    linarith
  · linarith
  · have hhalf : 2 * c / 2 = c := by ring
    simpa [hhalf] using hc0

/-! ### The balance is unique -/

private noncomputable def nearPhase (t : ℝ) : ℝ := 1 / (2 * (2 - t))

private noncomputable def farPhase (t : ℝ) : ℝ := 1 / (2 * (2 + t))

private noncomputable def eqPhase (t : ℝ) : ℝ := 1 / (2 * sqrt (4 + t ^ 2))

/-- `24φ⁵ − φ³`, the numerator that bounds the equatorial slope. -/
private noncomputable def equatorialNum (φ : ℝ) : ℝ := 24 * φ ^ 5 - φ ^ 3

private noncomputable def cageOutward (t : ℝ) : ℝ :=
  -pairAttraction (nearPhase t) + pairAttraction (farPhase t) + 4 * pullRate (eqPhase t) * t

private noncomputable def cageOutwardDeriv (t : ℝ) : ℝ :=
  -((8 * nearPhase t * forceCrit (nearPhase t) / gammaSEqual (nearPhase t) ^ 2) *
      (2 * nearPhase t ^ 2))
    + (8 * farPhase t * forceCrit (farPhase t) / gammaSEqual (farPhase t) ^ 2) *
      (-(2 * farPhase t ^ 2))
    + 4 * (pullRate (eqPhase t) * (48 * eqPhase t ^ 2 - 2) +
      ionOutflow (eqPhase t) * (16 * eqPhase t ^ 2 - 1))

private lemma gammaSEqual_le_taylor {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    gammaSEqual x ≤ 1 - x ^ 2 + x ^ 4 * (5 / 48) := by
  have hcos := cos_bound (x := x) (by rwa [abs_of_nonneg hx0])
  have hle : cos x ≤ 1 - x ^ 2 / 2 + x ^ 4 * (5 / 96) := by
    have h := (abs_sub_le_iff.mp hcos).1
    rw [abs_of_nonneg hx0] at h
    linarith
  have hγ := gammaSEqual_le_two_cos_sub_one hx0 hx1
  have hpoly : 2 * (1 - x ^ 2 / 2 + x ^ 4 * (5 / 96)) - 1
      = 1 - x ^ 2 + x ^ 4 * (5 / 48) := by ring
  linarith

private lemma hasDerivAt_equatorialNum (φ : ℝ) :
    HasDerivAt equatorialNum (3 * φ ^ 2 * (40 * φ ^ 2 - 1)) φ := by
  unfold equatorialNum
  have h5 : HasDerivAt (fun y : ℝ => y ^ 5) (5 * φ ^ 4) φ := by
    simpa using hasDerivAt_pow 5 φ
  have h3 : HasDerivAt (fun y : ℝ => y ^ 3) (3 * φ ^ 2) φ := by
    simpa using hasDerivAt_pow 3 φ
  have h := (h5.const_mul 24).sub h3
  refine h.congr_deriv ?_
  ring

private lemma equatorialNum_monotone :
    MonotoneOn equatorialNum (Icc (1 / 5 : ℝ) (1 / 2)) := by
  refine monotoneOn_of_deriv_nonneg (convex_Icc (1 / 5) (1 / 2)) ?_ ?_ ?_
  · unfold equatorialNum
    exact ((continuous_id.pow 5).const_mul 24).continuousOn.sub
      (continuous_id.pow 3).continuousOn
  · intro y hy
    rw [interior_Icc] at hy
    exact (hasDerivAt_equatorialNum y).differentiableAt.differentiableWithinAt
  · intro y hy
    rw [interior_Icc] at hy
    rw [(hasDerivAt_equatorialNum y).deriv]
    have hy5 : (1 / 5 : ℝ) < y := hy.1
    have hy0 : 0 < y := by linarith
    have hsq : (1 / 5 : ℝ) ^ 2 < y ^ 2 := (sq_lt_sq₀ (by norm_num) hy0.le).mpr hy5
    nlinarith [hsq]

private lemma nearPhase_mono {s t : ℝ} (hs : s ≤ t) (ht : t < 2) :
    nearPhase s ≤ nearPhase t := by
  unfold nearPhase
  have hle : 2 * (2 - t) ≤ 2 * (2 - s) := by nlinarith
  exact one_div_le_one_div_of_le (by linarith) hle

private lemma farPhase_anti {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    farPhase t ≤ farPhase s := by
  unfold farPhase
  have hle : 2 * (2 + s) ≤ 2 * (2 + t) := by nlinarith
  exact one_div_le_one_div_of_le (by linarith) hle

private lemma cubic_over_gamma_ge {x y : ℝ} (hx : x ∈ Ioo 0 resonanceRoot1)
    (hy : y ∈ Ioo 0 resonanceRoot1) (hyx : y ≤ x) :
    y ^ 3 / (1 - y ^ 2 + y ^ 4 * (5 / 48)) ≤ x ^ 3 / gammaSEqual x := by
  have hy1 : y ≤ 1 := le_of_lt (lt_trans hy.2 resonanceRoot1_bounds.2)
  have hU : gammaSEqual y ≤ 1 - y ^ 2 + y ^ 4 * (5 / 48) :=
    gammaSEqual_le_taylor hy.1.le hy1
  have hγy : 0 < gammaSEqual y := gammaSEqual_pos_left_of_first_node hy
  have hγx : 0 < gammaSEqual x := gammaSEqual_pos_left_of_first_node hx
  set U : ℝ := 1 - y ^ 2 + y ^ 4 * (5 / 48)
  have hUpos : 0 < U := lt_of_lt_of_le hγy hU
  have hγle : gammaSEqual x ≤ gammaSEqual y := by
    rcases eq_or_lt_of_le hyx with rfl | hlt
    · rfl
    · have hanti := strictAntiOn_gammaSEqual_even 0
      have hxI : x ∈ Icc (((2 * 0 : ℕ) : ℝ) * π) (((2 * 0 : ℕ) : ℝ) * π + π) := by
        simpa using (⟨hx.1.le, by linarith [hx.2, resonanceRoot1_bounds.2, pi_gt_three]⟩ :
          x ∈ Icc (0 : ℝ) π)
      have hyI : y ∈ Icc (((2 * 0 : ℕ) : ℝ) * π) (((2 * 0 : ℕ) : ℝ) * π + π) := by
        simpa using (⟨hy.1.le, by linarith [hy.2, resonanceRoot1_bounds.2, pi_gt_three]⟩ :
          y ∈ Icc (0 : ℝ) π)
      exact (hanti hyI hxI hlt).le
  have hpow : y ^ 3 ≤ x ^ 3 := pow_le_pow_left₀ hy.1.le hyx 3
  have h1 : y ^ 3 / U ≤ x ^ 3 / U := div_le_div_of_nonneg_right hpow hUpos.le
  have hden : gammaSEqual x ≤ U := le_trans hγle hU
  have h2 : x ^ 3 / U ≤ x ^ 3 / gammaSEqual x :=
    div_le_div_of_nonneg_left (by have hx0 := hx.1; positivity) hγx hden
  exact h1.trans h2

private lemma eqPhase_lt_quarter {t : ℝ} (ht : t ∈ Icc (5 / 19 : ℝ) 1) :
    eqPhase t < 1 / 4 := by
  have ht0 : 0 < t := by linarith [ht.1]
  have hsqrt : (2 : ℝ) < sqrt (4 + t ^ 2) := by
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
    exact Real.sqrt_lt_sqrt (by positivity) (by nlinarith [ht0])
  have h4 : (4 : ℝ) < 2 * sqrt (4 + t ^ 2) := by linarith
  unfold eqPhase
  exact one_div_lt_one_div_of_lt (by norm_num) h4

private lemma fifth_lt_eqPhase {t : ℝ} (ht : t ∈ Icc (5 / 19 : ℝ) 1) :
    1 / 5 < eqPhase t := by
  have ht2 : t ^ 2 ≤ 1 := by
    have hpow := pow_le_pow_left₀ (by linarith [ht.1] : (0 : ℝ) ≤ t) ht.2 2
    simpa using hpow
  have hsqrt_le : sqrt (4 + t ^ 2) ≤ sqrt 5 :=
    Real.sqrt_le_sqrt (by linarith [ht2])
  have hsqrt5 : sqrt 5 < 5 / 2 := by
    have hsq : (sqrt 5) ^ 2 < ((5 : ℝ) / 2) ^ 2 := by
      rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)]
      norm_num
    exact (sq_lt_sq₀ (Real.sqrt_nonneg 5) (by norm_num)).mp hsq
  have hden : 2 * sqrt (4 + t ^ 2) ≤ 2 * sqrt 5 := by nlinarith
  have h5 : 2 * sqrt 5 < 5 := by linarith
  have hcomp : 1 / (2 * sqrt 5) ≤ 1 / (2 * sqrt (4 + t ^ 2)) :=
    one_div_le_one_div_of_le (by positivity) hden
  have hfifth : (1 / 5 : ℝ) < 1 / (2 * sqrt 5) :=
    one_div_lt_one_div_of_lt (by positivity) h5
  unfold eqPhase
  linarith

private lemma equatorial_over_gamma_le {t : ℝ} (ht : t ∈ Icc (5 / 19 : ℝ) 1) :
    64 * equatorialNum (eqPhase t) / gammaSEqual (eqPhase t) ≤ 80 / 147 := by
  have hph := phase_outer_on_cage ht.1 ht.2
  have hφmem : eqPhase t ∈ Ioo 0 resonanceRoot1 := by
    simpa [eqPhase] using hph.2.2
  have hγ : 0 < gammaSEqual (eqPhase t) := gammaSEqual_pos_left_of_first_node hφmem
  have hγ4pos : 0 < gammaSEqual (1 / 4) := by linarith [gamma_one_quarter_ge]
  have hφ4 := eqPhase_lt_quarter ht
  have hφ5 := fifth_lt_eqPhase ht
  have hφI : eqPhase t ∈ Icc (1 / 5 : ℝ) (1 / 2) := ⟨hφ5.le, by linarith⟩
  have h14I : (1 / 4 : ℝ) ∈ Icc (1 / 5) (1 / 2) := ⟨by norm_num, by norm_num⟩
  have hu : equatorialNum (eqPhase t) ≤ equatorialNum (1 / 4) :=
    equatorialNum_monotone hφI h14I hφ4.le
  have hu4 : equatorialNum (1 / 4) = 1 / 128 := by
    unfold equatorialNum
    norm_num
  have hanti := strictAntiOn_gammaSEqual_even 0
  have hφπ : eqPhase t ≤ π := by
    linarith [hφmem.2, resonanceRoot1_bounds.2, pi_gt_three]
  have hφIcc : eqPhase t ∈ Icc (((2 * 0 : ℕ) : ℝ) * π) (((2 * 0 : ℕ) : ℝ) * π + π) := by
    simpa using (⟨hφmem.1.le, hφπ⟩ : eqPhase t ∈ Icc (0 : ℝ) π)
  have h14π : (1 / 4 : ℝ) ∈ Icc (((2 * 0 : ℕ) : ℝ) * π) (((2 * 0 : ℕ) : ℝ) * π + π) := by
    simpa using (⟨by norm_num, by linarith [pi_gt_three]⟩ : (1 / 4 : ℝ) ∈ Icc (0 : ℝ) π)
  have hγle : gammaSEqual (1 / 4) < gammaSEqual (eqPhase t) := hanti hφIcc h14π hφ4
  have h1 : equatorialNum (eqPhase t) / gammaSEqual (eqPhase t) ≤
      equatorialNum (1 / 4) / gammaSEqual (eqPhase t) :=
    div_le_div_of_nonneg_right hu hγ.le
  have hu0 : 0 ≤ equatorialNum (1 / 4) := by rw [hu4]; norm_num
  have h2 : equatorialNum (1 / 4) / gammaSEqual (eqPhase t) ≤
      equatorialNum (1 / 4) / gammaSEqual (1 / 4) :=
    div_le_div_of_nonneg_left hu0 hγ4pos hγle.le
  have h3 : equatorialNum (1 / 4) / gammaSEqual (1 / 4) ≤
      equatorialNum (1 / 4) / (147 / 160) :=
    div_le_div_of_nonneg_left hu0 (by norm_num) gamma_one_quarter_ge
  have hconst : (64 : ℝ) * ((1 / 128) / (147 / 160)) = 80 / 147 := by norm_num
  have h64 : 64 * (equatorialNum (eqPhase t) / gammaSEqual (eqPhase t)) ≤
      64 * (equatorialNum (1 / 4) / (147 / 160)) := by
    have hstep := h1.trans (h2.trans h3)
    exact mul_le_mul_of_nonneg_left hstep (by norm_num)
  rw [hu4] at h64
  calc
    64 * equatorialNum (eqPhase t) / gammaSEqual (eqPhase t)
        = 64 * (equatorialNum (eqPhase t) / gammaSEqual (eqPhase t)) := by ring
    _ ≤ 64 * ((1 / 128) / (147 / 160)) := h64
    _ = 80 / 147 := hconst

private lemma axialSlope_gt {x : ℝ} (hx : x ∈ Ioo 0 resonanceRoot1) :
    16 * x ^ 3 / gammaSEqual x <
      8 * x * forceCrit x / gammaSEqual x ^ 2 * (2 * x ^ 2) := by
  have hγ : 0 < gammaSEqual x := gammaSEqual_pos_left_of_first_node hx
  have hsin : 0 < sin x :=
    sin_pos_of_pos_of_lt_pi hx.1 (by linarith [hx.2, resonanceRoot1_bounds.2, pi_gt_three])
  have hdiff : 8 * x * forceCrit x / gammaSEqual x ^ 2 * (2 * x ^ 2) -
      16 * x ^ 3 / gammaSEqual x =
      16 * x ^ 4 * cosh x * sin x / gammaSEqual x ^ 2 := by
    unfold forceCrit
    field_simp [hγ.ne']
    ring
  have hpos : 0 < 16 * x ^ 4 * cosh x * sin x / gammaSEqual x ^ 2 := by
    have hnum : 0 < 16 * x ^ 4 * cosh x * sin x :=
      mul_pos (mul_pos (mul_pos (by norm_num) (pow_pos hx.1 4)) (cosh_pos x)) hsin
    exact div_pos hnum (sq_pos_of_pos hγ)
  linarith

private lemma equatorialSlope_lt {φ : ℝ} (hφ : φ ∈ Ioo 0 resonanceRoot1) (hφ4 : φ < 1 / 4) :
    pullRate φ * (48 * φ ^ 2 - 2) + ionOutflow φ * (16 * φ ^ 2 - 1) <
      16 * φ ^ 3 * (24 * φ ^ 2 - 1) / gammaSEqual φ := by
  have hion : 0 < ionOutflow φ := ionOutflow_pos_outer hφ
  have hneg : 16 * φ ^ 2 - 1 < 0 := by nlinarith [hφ.1, hφ4]
  have hlt : ionOutflow φ * (16 * φ ^ 2 - 1) < 0 := mul_neg_of_pos_of_neg hion hneg
  have hγ : gammaSEqual φ ≠ 0 := (gammaSEqual_pos_left_of_first_node hφ).ne'
  have heq : pullRate φ * (48 * φ ^ 2 - 2) =
      16 * φ ^ 3 * (24 * φ ^ 2 - 1) / gammaSEqual φ := by
    unfold pullRate
    field_simp [hγ]
    ring
  linarith

private lemma cageOutwardDeriv_lt_ratios {t : ℝ} (ht : t ∈ Icc (5 / 19 : ℝ) 1) :
    cageOutwardDeriv t <
      -(16 * nearPhase t ^ 3 / gammaSEqual (nearPhase t)) +
        -(16 * farPhase t ^ 3 / gammaSEqual (farPhase t)) +
        64 * equatorialNum (eqPhase t) / gammaSEqual (eqPhase t) := by
  have hph := phase_outer_on_cage ht.1 ht.2
  have hn : nearPhase t ∈ Ioo 0 resonanceRoot1 := by simpa [nearPhase] using hph.1
  have hf : farPhase t ∈ Ioo 0 resonanceRoot1 := by simpa [farPhase] using hph.2.1
  have he : eqPhase t ∈ Ioo 0 resonanceRoot1 := by simpa [eqPhase] using hph.2.2
  have hφ4 := eqPhase_lt_quarter ht
  have hnear := axialSlope_gt hn
  have hfar := axialSlope_gt hf
  have heq := equatorialSlope_lt he hφ4
  have h4 : 4 * (pullRate (eqPhase t) * (48 * eqPhase t ^ 2 - 2) +
      ionOutflow (eqPhase t) * (16 * eqPhase t ^ 2 - 1)) <
      64 * equatorialNum (eqPhase t) / gammaSEqual (eqPhase t) := by
    have hmul := mul_lt_mul_of_pos_left heq (by norm_num : (0 : ℝ) < 4)
    have hγ : gammaSEqual (eqPhase t) ≠ 0 := (gammaSEqual_pos_left_of_first_node he).ne'
    have hid : 4 * (16 * eqPhase t ^ 3 * (24 * eqPhase t ^ 2 - 1) / gammaSEqual (eqPhase t)) =
        64 * equatorialNum (eqPhase t) / gammaSEqual (eqPhase t) := by
      unfold equatorialNum
      field_simp [hγ]
      ring
    linarith
  have hfarEq : 8 * farPhase t * forceCrit (farPhase t) / gammaSEqual (farPhase t) ^ 2 *
      (-(2 * farPhase t ^ 2)) =
      -((8 * farPhase t * forceCrit (farPhase t) / gammaSEqual (farPhase t) ^ 2) *
        (2 * farPhase t ^ 2)) := by ring
  unfold cageOutwardDeriv
  exact add_lt_add (add_lt_add (neg_lt_neg hnear) (by rw [hfarEq]; exact neg_lt_neg hfar)) h4

private lemma cageOutwardDeriv_neg_of_margin {a b : ℝ}
    (ha0 : (5 / 19 : ℝ) ≤ a) (hb1 : b ≤ 1) (hab : a ≤ b)
    (hmargin : (80 / 147 : ℝ) <
      16 * nearPhase a ^ 3 / (1 - nearPhase a ^ 2 + nearPhase a ^ 4 * (5 / 48)) +
      16 * farPhase b ^ 3 / (1 - farPhase b ^ 2 + farPhase b ^ 4 * (5 / 48))) :
    ∀ t ∈ Icc a b, cageOutwardDeriv t < 0 := by
  intro t ht
  have htI : t ∈ Icc (5 / 19 : ℝ) 1 := ⟨le_trans ha0 ht.1, le_trans ht.2 hb1⟩
  have haI : a ∈ Icc (5 / 19 : ℝ) 1 := ⟨ha0, le_trans hab hb1⟩
  have hbI : b ∈ Icc (5 / 19 : ℝ) 1 := ⟨le_trans ha0 hab, hb1⟩
  have htn := phase_outer_on_cage htI.1 htI.2
  have han := phase_outer_on_cage haI.1 haI.2
  have hbn := phase_outer_on_cage hbI.1 hbI.2
  have hnear_le : nearPhase a ≤ nearPhase t :=
    nearPhase_mono ht.1 (by linarith [htI.2])
  have hfar_le : farPhase b ≤ farPhase t :=
    farPhase_anti (s := t) (t := b) (by linarith [htI.1]) ht.2
  have hna : nearPhase a ∈ Ioo 0 resonanceRoot1 := by simpa [nearPhase] using han.1
  have hnt : nearPhase t ∈ Ioo 0 resonanceRoot1 := by simpa [nearPhase] using htn.1
  have hfb : farPhase b ∈ Ioo 0 resonanceRoot1 := by simpa [farPhase] using hbn.2.1
  have hft : farPhase t ∈ Ioo 0 resonanceRoot1 := by simpa [farPhase] using htn.2.1
  have hnear := cubic_over_gamma_ge hnt hna hnear_le
  have hfar := cubic_over_gamma_ge hft hfb hfar_le
  have heq := equatorial_over_gamma_le htI
  have hpoint := cageOutwardDeriv_lt_ratios htI
  have hnear16 : 16 * (nearPhase a ^ 3 /
        (1 - nearPhase a ^ 2 + nearPhase a ^ 4 * (5 / 48))) ≤
      16 * (nearPhase t ^ 3 / gammaSEqual (nearPhase t)) :=
    mul_le_mul_of_nonneg_left hnear (by norm_num)
  have hfar16 : 16 * (farPhase b ^ 3 /
        (1 - farPhase b ^ 2 + farPhase b ^ 4 * (5 / 48))) ≤
      16 * (farPhase t ^ 3 / gammaSEqual (farPhase t)) :=
    mul_le_mul_of_nonneg_left hfar (by norm_num)
  have hnearA : 16 * (nearPhase a ^ 3 /
        (1 - nearPhase a ^ 2 + nearPhase a ^ 4 * (5 / 48))) =
      16 * nearPhase a ^ 3 / (1 - nearPhase a ^ 2 + nearPhase a ^ 4 * (5 / 48)) := by ring
  have hfarB : 16 * (farPhase b ^ 3 /
        (1 - farPhase b ^ 2 + farPhase b ^ 4 * (5 / 48))) =
      16 * farPhase b ^ 3 / (1 - farPhase b ^ 2 + farPhase b ^ 4 * (5 / 48)) := by ring
  rw [← hnearA, ← hfarB] at hmargin
  have htop : -(16 * (nearPhase a ^ 3 / (1 - nearPhase a ^ 2 + nearPhase a ^ 4 * (5 / 48)))) +
      -(16 * (farPhase b ^ 3 / (1 - farPhase b ^ 2 + farPhase b ^ 4 * (5 / 48)))) +
      80 / 147 < 0 := by linarith [hmargin]
  have hle := add_le_add (add_le_add (neg_le_neg hnear16) (neg_le_neg hfar16)) heq
  have hnearT : 16 * (nearPhase t ^ 3 / gammaSEqual (nearPhase t)) =
      16 * nearPhase t ^ 3 / gammaSEqual (nearPhase t) := by ring
  have hfarT : 16 * (farPhase t ^ 3 / gammaSEqual (farPhase t)) =
      16 * farPhase t ^ 3 / gammaSEqual (farPhase t) := by ring
  rw [hnearT, hfarT] at hle
  linarith

private lemma margin_5_19_3_10 :
    (80 / 147 : ℝ) <
      16 * nearPhase (5 / 19) ^ 3 /
        (1 - nearPhase (5 / 19) ^ 2 + nearPhase (5 / 19) ^ 4 * (5 / 48)) +
      16 * farPhase (3 / 10) ^ 3 /
        (1 - farPhase (3 / 10) ^ 2 + farPhase (3 / 10) ^ 4 * (5 / 48)) := by
  unfold nearPhase farPhase
  norm_num

private lemma margin_3_10_2_5 :
    (80 / 147 : ℝ) <
      16 * nearPhase (3 / 10) ^ 3 /
        (1 - nearPhase (3 / 10) ^ 2 + nearPhase (3 / 10) ^ 4 * (5 / 48)) +
      16 * farPhase (2 / 5) ^ 3 /
        (1 - farPhase (2 / 5) ^ 2 + farPhase (2 / 5) ^ 4 * (5 / 48)) := by
  unfold nearPhase farPhase
  norm_num

private lemma margin_2_5_1_2 :
    (80 / 147 : ℝ) <
      16 * nearPhase (2 / 5) ^ 3 /
        (1 - nearPhase (2 / 5) ^ 2 + nearPhase (2 / 5) ^ 4 * (5 / 48)) +
      16 * farPhase (1 / 2) ^ 3 /
        (1 - farPhase (1 / 2) ^ 2 + farPhase (1 / 2) ^ 4 * (5 / 48)) := by
  unfold nearPhase farPhase
  norm_num

private lemma margin_1_2_3_5 :
    (80 / 147 : ℝ) <
      16 * nearPhase (1 / 2) ^ 3 /
        (1 - nearPhase (1 / 2) ^ 2 + nearPhase (1 / 2) ^ 4 * (5 / 48)) +
      16 * farPhase (3 / 5) ^ 3 /
        (1 - farPhase (3 / 5) ^ 2 + farPhase (3 / 5) ^ 4 * (5 / 48)) := by
  unfold nearPhase farPhase
  norm_num

private lemma margin_3_5_4_5 :
    (80 / 147 : ℝ) <
      16 * nearPhase (3 / 5) ^ 3 /
        (1 - nearPhase (3 / 5) ^ 2 + nearPhase (3 / 5) ^ 4 * (5 / 48)) +
      16 * farPhase (4 / 5) ^ 3 /
        (1 - farPhase (4 / 5) ^ 2 + farPhase (4 / 5) ^ 4 * (5 / 48)) := by
  unfold nearPhase farPhase
  norm_num

private lemma margin_4_5_1 :
    (80 / 147 : ℝ) <
      16 * nearPhase (4 / 5) ^ 3 /
        (1 - nearPhase (4 / 5) ^ 2 + nearPhase (4 / 5) ^ 4 * (5 / 48)) +
      16 * farPhase 1 ^ 3 /
        (1 - farPhase 1 ^ 2 + farPhase 1 ^ 4 * (5 / 48)) := by
  unfold nearPhase farPhase
  norm_num

private lemma cageOutwardDeriv_neg {t : ℝ} (ht : t ∈ Icc (5 / 19 : ℝ) 1) :
    cageOutwardDeriv t < 0 := by
  by_cases h1 : t ≤ 3 / 10
  · exact cageOutwardDeriv_neg_of_margin (a := 5 / 19) (b := 3 / 10)
      (by norm_num) (by norm_num) (by norm_num) margin_5_19_3_10 t ⟨ht.1, h1⟩
  by_cases h2 : t ≤ 2 / 5
  · exact cageOutwardDeriv_neg_of_margin (a := 3 / 10) (b := 2 / 5)
      (by norm_num) (by norm_num) (by norm_num) margin_3_10_2_5 t ⟨(not_le.mp h1).le, h2⟩
  by_cases h3 : t ≤ 1 / 2
  · exact cageOutwardDeriv_neg_of_margin (a := 2 / 5) (b := 1 / 2)
      (by norm_num) (by norm_num) (by norm_num) margin_2_5_1_2 t ⟨(not_le.mp h2).le, h3⟩
  by_cases h4 : t ≤ 3 / 5
  · exact cageOutwardDeriv_neg_of_margin (a := 1 / 2) (b := 3 / 5)
      (by norm_num) (by norm_num) (by norm_num) margin_1_2_3_5 t ⟨(not_le.mp h3).le, h4⟩
  by_cases h5 : t ≤ 4 / 5
  · exact cageOutwardDeriv_neg_of_margin (a := 3 / 5) (b := 4 / 5)
      (by norm_num) (by norm_num) (by norm_num) margin_3_5_4_5 t ⟨(not_le.mp h4).le, h5⟩
  · exact cageOutwardDeriv_neg_of_margin (a := 4 / 5) (b := 1)
      (by norm_num) (by norm_num) (by norm_num) margin_4_5_1 t ⟨(not_le.mp h5).le, ht.2⟩

private lemma hasDerivAt_nearPhase {t : ℝ} (ht : t < 2) :
    HasDerivAt nearPhase (2 * nearPhase t ^ 2) t := by
  unfold nearPhase
  have hsub0 := (hasDerivAt_const t (2 : ℝ)).sub (hasDerivAt_id t)
  have hsub : HasDerivAt (fun s : ℝ => 2 - s) (-1) t := by
    refine (hsub0.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun s => ?_)).congr_deriv (by ring)
    simp [Pi.sub_apply]
  have hlin : HasDerivAt (fun s : ℝ => 2 * (2 - s)) (-2) t :=
    (hsub.const_mul (2 : ℝ)).congr_deriv (by ring)
  have hnz : (2 : ℝ) * (2 - t) ≠ 0 :=
    mul_ne_zero (by norm_num) (by linarith : (2 : ℝ) - t ≠ 0)
  refine (((hasDerivAt_inv hnz).comp t hlin).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun s => ?_)).congr_deriv ?_
  · simp [Function.comp_apply]
  · field_simp [hnz]

private lemma hasDerivAt_farPhase {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt farPhase (-(2 * farPhase t ^ 2)) t := by
  unfold farPhase
  have hadd0 := (hasDerivAt_const t (2 : ℝ)).add (hasDerivAt_id t)
  have hadd : HasDerivAt (fun s : ℝ => 2 + s) 1 t := by
    refine (hadd0.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun s => ?_)).congr_deriv (by ring)
    simp [Pi.add_apply]
  have hlin : HasDerivAt (fun s : ℝ => 2 * (2 + s)) 2 t :=
    (hadd.const_mul (2 : ℝ)).congr_deriv (by ring)
  have hnz : (2 : ℝ) * (2 + t) ≠ 0 := by positivity
  refine (((hasDerivAt_inv hnz).comp t hlin).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun s => ?_)).congr_deriv ?_
  · simp [Function.comp_apply]
  · field_simp [hnz]

private lemma hasDerivAt_eqPhase {t : ℝ} (_ht : 0 < t) :
    HasDerivAt eqPhase (-(t / (2 * (sqrt (4 + t ^ 2)) ^ 3))) t := by
  unfold eqPhase
  have hpow : HasDerivAt (fun s : ℝ => s ^ 2) (2 * t) t := by
    simpa using hasDerivAt_pow 2 t
  have hu0 := (hasDerivAt_const t (4 : ℝ)).add hpow
  have hu : HasDerivAt (fun s : ℝ => 4 + s ^ 2) (2 * t) t := by
    refine (hu0.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun s => ?_)).congr_deriv (by ring)
    simp [Pi.add_apply]
  have hsqrt := (hasDerivAt_sqrt (by positivity : (4 : ℝ) + t ^ 2 ≠ 0)).comp t hu
  have hR : sqrt (4 + t ^ 2) ≠ 0 := by positivity
  have hinv := (hasDerivAt_inv hR).comp t hsqrt
  have hhalf0 := hinv.const_mul ((1 : ℝ) / 2)
  have hhalf : HasDerivAt eqPhase
      ((1 / 2) * (-(sqrt (4 + t ^ 2) ^ 2)⁻¹ *
        (1 / (2 * sqrt (4 + t ^ 2)) * (2 * t)))) t := by
    unfold eqPhase
    refine hhalf0.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
    simp [Function.comp_apply]
    ring
  refine hhalf.congr_deriv (by field_simp [hR])

private lemma eqPhase_weight {t : ℝ} (_ht : 0 ≤ t) :
    t ^ 2 / (2 * (sqrt (4 + t ^ 2)) ^ 3) =
      eqPhase t * (1 - 16 * eqPhase t ^ 2) := by
  set R := sqrt (4 + t ^ 2)
  have hR : 0 < R := by unfold R; positivity
  have hsq : R ^ 2 = 4 + t ^ 2 := by
    unfold R
    exact Real.sq_sqrt (by positivity)
  have hRne : R ≠ 0 := hR.ne'
  have ht2 : t ^ 2 = R ^ 2 - 4 := by rw [hsq]; ring
  have hRdef : sqrt (4 + t ^ 2) = R := rfl
  unfold eqPhase
  rw [hRdef, ht2]
  have hpow : (1 / (2 * R)) ^ 2 = 1 / (4 * R ^ 2) := by
    field_simp [hRne]
    ring
  rw [hpow]
  field_simp [hRne]
  ring

private lemma eqSlope_eq {t : ℝ} (ht : 0 < t) (hγ : gammaSEqual (eqPhase t) ≠ 0) :
    pullRateDeriv (eqPhase t) * (-(t / (2 * (sqrt (4 + t ^ 2)) ^ 3))) * t +
        pullRate (eqPhase t) =
      pullRate (eqPhase t) * (48 * eqPhase t ^ 2 - 2) +
        ionOutflow (eqPhase t) * (16 * eqPhase t ^ 2 - 1) := by
  have hw := eqPhase_weight (le_of_lt ht)
  have hflow := pullRate_outflow hγ
  have hφd : eqPhase t * pullRateDeriv (eqPhase t) =
      3 * pullRate (eqPhase t) + ionOutflow (eqPhase t) := by
    linarith
  have hneg : -(t / (2 * (sqrt (4 + t ^ 2)) ^ 3)) * t =
      -(eqPhase t * (1 - 16 * eqPhase t ^ 2)) := by
    have hmul : t / (2 * (sqrt (4 + t ^ 2)) ^ 3) * t =
        t ^ 2 / (2 * (sqrt (4 + t ^ 2)) ^ 3) := by
      field_simp
    linarith
  have hstep : pullRateDeriv (eqPhase t) * (-(t / (2 * (sqrt (4 + t ^ 2)) ^ 3))) * t =
      pullRateDeriv (eqPhase t) * (-(eqPhase t * (1 - 16 * eqPhase t ^ 2))) := by
    have hassoc : pullRateDeriv (eqPhase t) * (-(t / (2 * (sqrt (4 + t ^ 2)) ^ 3))) * t =
        pullRateDeriv (eqPhase t) *
          ((-(t / (2 * (sqrt (4 + t ^ 2)) ^ 3))) * t) := by ring
    rw [hassoc, hneg]
  calc
    pullRateDeriv (eqPhase t) * (-(t / (2 * (sqrt (4 + t ^ 2)) ^ 3))) * t +
        pullRate (eqPhase t) =
      pullRate (eqPhase t) +
        pullRateDeriv (eqPhase t) * (-(eqPhase t * (1 - 16 * eqPhase t ^ 2))) := by
      rw [hstep]
      ring
    _ = pullRate (eqPhase t) -
        eqPhase t * pullRateDeriv (eqPhase t) * (1 - 16 * eqPhase t ^ 2) := by
      ring
    _ = pullRate (eqPhase t) -
        (3 * pullRate (eqPhase t) + ionOutflow (eqPhase t)) *
          (1 - 16 * eqPhase t ^ 2) := by
      rw [hφd]
    _ = pullRate (eqPhase t) * (48 * eqPhase t ^ 2 - 2) +
        ionOutflow (eqPhase t) * (16 * eqPhase t ^ 2 - 1) := by
      ring

private lemma hasDerivAt_cageOutward {t : ℝ} (ht0 : 0 < t) (ht2 : t < 2)
    (hγn : gammaSEqual (nearPhase t) ≠ 0) (hγf : gammaSEqual (farPhase t) ≠ 0)
    (hγe : gammaSEqual (eqPhase t) ≠ 0) :
    HasDerivAt cageOutward (cageOutwardDeriv t) t := by
  have hnear := ((hasDerivAt_pairAttraction hγn).comp t
    (hasDerivAt_nearPhase ht2)).const_mul (-1)
  have hfar := (hasDerivAt_pairAttraction hγf).comp t (hasDerivAt_farPhase ht0.le)
  have hpull := (hasDerivAt_pullRate hγe).comp t (hasDerivAt_eqPhase ht0)
  have heq := (hpull.const_mul 4).mul (hasDerivAt_id t)
  have hsum := (hnear.add hfar).add heq
  refine (hsum.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)).congr_deriv ?_
  · simp only [Function.comp_apply, neg_mul, one_mul, Pi.add_apply, Pi.mul_apply, id_eq]
    unfold cageOutward
    ring
  · have hslope := eqSlope_eq ht0 hγe
    unfold cageOutwardDeriv
    have hcomp : (pullRate ∘ eqPhase) t = pullRate (eqPhase t) := rfl
    have hid : id t = t := rfl
    rw [hcomp, hid]
    have hthird : 4 * (pullRateDeriv (eqPhase t) * -(t / (2 * (sqrt (4 + t ^ 2)) ^ 3))) * t +
        4 * pullRate (eqPhase t) * 1 =
        4 * (pullRate (eqPhase t) * (48 * eqPhase t ^ 2 - 2) +
          ionOutflow (eqPhase t) * (16 * eqPhase t ^ 2 - 1)) := by
      linarith [hslope]
    rw [hthird]
    ring

private lemma octaPairOutward_eq_cage {Z t : ℝ} :
    octaPairOutward Z 2 t = Z * cageOutward t + pairAttraction (1 / (4 * t)) := by
  unfold octaPairOutward cageOutward nearPhase farPhase eqPhase
  rw [show (2 : ℝ) ^ 2 = 4 by norm_num]
  ring

private lemma hasDerivAt_partnerPhase {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => 1 / (4 * s)) (-(4 * (1 / (4 * t)) ^ 2)) t := by
  have hlin : HasDerivAt (fun s : ℝ => 4 * s) 4 t :=
    ((hasDerivAt_id t).const_mul 4).congr_deriv (by ring)
  have hnz : (4 : ℝ) * t ≠ 0 := by positivity
  refine (((hasDerivAt_inv hnz).comp t hlin).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun s => ?_)).congr_deriv ?_
  · simp [Function.comp_apply]
  · field_simp [hnz]

private lemma continuousOn_octaPair_aboveNode {Z : ℝ} :
    ContinuousOn (octaPairOutward Z 2) (Ioc (1 / (4 * resonanceRoot1)) 1) := by
  set t0 := 1 / (4 * resonanceRoot1)
  have ht0 := nodeHalf_mem
  have hsub : Ioc t0 1 ⊆ Icc (5 / 19 : ℝ) 1 := by
    intro u hu
    exact ⟨le_of_lt (lt_trans ht0.1 hu.1), hu.2⟩
  have hcage : ContinuousOn cageOutward (Ioc t0 1) := by
    have h := continuousOn_cage (Z := 1)
    refine (h.mono hsub).congr ?_
    intro u _
    unfold cageOutward nearPhase farPhase eqPhase
    ring
  have hY := continuousOn_pairAttraction_outer
  have hphase : ContinuousOn (fun u : ℝ => 1 / (4 * u)) (Ioc t0 1) := by
    refine ContinuousOn.div continuousOn_const (continuousOn_const.mul continuousOn_id) ?_
    intro u hu
    exact ne_of_gt (by linarith [ht0.1, hu.1] : (0 : ℝ) < 4 * u)
  have hmap : MapsTo (fun u : ℝ => 1 / (4 * u)) (Ioc t0 1) (Ioo 0 resonanceRoot1) := by
    intro u hu
    have hu0 : 0 < u := by linarith [ht0.1, hu.1]
    refine ⟨by positivity, ?_⟩
    have hlt : 1 / (4 * u) < 1 / (4 * t0) :=
      one_div_lt_one_div_of_lt (by nlinarith [ht0.1]) (by nlinarith [hu.1])
    have ht0eq : 1 / (4 * t0) = resonanceRoot1 := by
      dsimp [t0]; field_simp
    linarith
  have hpartner : ContinuousOn (fun u : ℝ => pairAttraction (1 / (4 * u))) (Ioc t0 1) :=
    (hY.comp hphase hmap).congr fun u _ => by simp [Function.comp_apply]
  refine (hcage.const_mul Z |>.add hpartner).congr ?_
  intro u _
  rw [Pi.add_apply]
  exact octaPairOutward_eq_cage (Z := Z) (t := u)

private lemma hasDerivAt_octaPairOutward_aboveNode {Z t : ℝ} (_hZ : 1 ≤ Z)
    (ht : t ∈ Ioo (1 / (4 * resonanceRoot1)) 1) :
    HasDerivAt (octaPairOutward Z 2)
      (Z * cageOutwardDeriv t +
        (8 * (1 / (4 * t)) * forceCrit (1 / (4 * t)) / gammaSEqual (1 / (4 * t)) ^ 2) *
          (-(4 * (1 / (4 * t)) ^ 2))) t := by
  have ht0mem := nodeHalf_mem
  have htI : t ∈ Icc (5 / 19 : ℝ) 1 :=
    ⟨le_of_lt (lt_trans ht0mem.1 ht.1), ht.2.le⟩
  have hph := phase_outer_on_cage htI.1 htI.2
  have hγn : gammaSEqual (nearPhase t) ≠ 0 := by
    exact (gammaSEqual_pos_left_of_first_node (by simpa [nearPhase] using hph.1)).ne'
  have hγf : gammaSEqual (farPhase t) ≠ 0 := by
    exact (gammaSEqual_pos_left_of_first_node (by simpa [farPhase] using hph.2.1)).ne'
  have hγe : gammaSEqual (eqPhase t) ≠ 0 := by
    exact (gammaSEqual_pos_left_of_first_node (by simpa [eqPhase] using hph.2.2)).ne'
  have htpos : 0 < t := by linarith [htI.1]
  have htlt : t < 2 := by linarith [ht.2]
  have hcage := hasDerivAt_cageOutward htpos htlt hγn hγf hγe
  have hpartnerPhase := hasDerivAt_partnerPhase htpos
  have hmem : 1 / (4 * t) ∈ Ioo 0 resonanceRoot1 := by
    have ht0 : 0 < 1 / (4 * resonanceRoot1) := lt_trans (by norm_num) ht0mem.1
    have h4t : 0 < 4 * t := by linarith [ht0mem.1, ht.1]
    refine ⟨one_div_pos.mpr h4t, ?_⟩
    have hden : 0 < 4 * (1 / (4 * resonanceRoot1)) := by nlinarith
    have hab : 4 * (1 / (4 * resonanceRoot1)) < 4 * t := by nlinarith [ht.1]
    have hlt : 1 / (4 * t) < 1 / (4 * (1 / (4 * resonanceRoot1))) :=
      one_div_lt_one_div_of_lt hden hab
    have heq : 1 / (4 * (1 / (4 * resonanceRoot1))) = resonanceRoot1 := by field_simp
    linarith
  have hγp : gammaSEqual (1 / (4 * t)) ≠ 0 :=
    (gammaSEqual_pos_left_of_first_node hmem).ne'
  have hpartner := (hasDerivAt_pairAttraction hγp).comp t hpartnerPhase
  have hsum := (hcage.const_mul Z).add hpartner
  refine hsum.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
  simp only [Function.comp_apply, Pi.add_apply]
  exact octaPairOutward_eq_cage (Z := Z) (t := s)

/-- For an ion charge at least one, the axial component falls strictly from just
outside the first charge node through separation `2`. -/
theorem octaPairOutward_strictAnti {Z : ℝ} (hZ : 1 ≤ Z) :
    StrictAntiOn (octaPairOutward Z 2) (Ioc (1 / (4 * resonanceRoot1)) 1) := by
  refine strictAntiOn_of_deriv_neg (convex_Ioc _ _) (continuousOn_octaPair_aboveNode (Z := Z)) ?_
  intro t ht
  rw [interior_Ioc] at ht
  have hderiv := hasDerivAt_octaPairOutward_aboveNode hZ ht
  rw [hderiv.deriv]
  have htI : t ∈ Icc (5 / 19 : ℝ) 1 :=
    ⟨le_of_lt (lt_trans nodeHalf_mem.1 ht.1), ht.2.le⟩
  have hcage := cageOutwardDeriv_neg htI
  have hZneg : Z * cageOutwardDeriv t ≤ cageOutwardDeriv t := by
    have hmul : (Z - 1) * cageOutwardDeriv t ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith) hcage.le
    linarith
  have hmem : 1 / (4 * t) ∈ Ioo 0 resonanceRoot1 := by
    have ht0 : 0 < 1 / (4 * resonanceRoot1) := lt_trans (by norm_num) nodeHalf_mem.1
    have h4t : 0 < 4 * t := by linarith [nodeHalf_mem.1, ht.1]
    refine ⟨one_div_pos.mpr h4t, ?_⟩
    have hden : 0 < 4 * (1 / (4 * resonanceRoot1)) := by nlinarith
    have hab : 4 * (1 / (4 * resonanceRoot1)) < 4 * t := by nlinarith [ht.1]
    have hlt : 1 / (4 * t) < 1 / (4 * (1 / (4 * resonanceRoot1))) :=
      one_div_lt_one_div_of_lt hden hab
    have heq : 1 / (4 * (1 / (4 * resonanceRoot1))) = resonanceRoot1 := by field_simp
    linarith
  have hpart : (8 * (1 / (4 * t)) * forceCrit (1 / (4 * t)) /
      gammaSEqual (1 / (4 * t)) ^ 2) * (-(4 * (1 / (4 * t)) ^ 2)) < 0 := by
    have hγ : 0 < gammaSEqual (1 / (4 * t)) := gammaSEqual_pos_left_of_first_node hmem
    have hcrit : 0 < forceCrit (1 / (4 * t)) := forceCrit_pos_outer hmem
    have hφ : 0 < 1 / (4 * t) := hmem.1
    have hnum : 0 < 8 * (1 / (4 * t)) * forceCrit (1 / (4 * t)) /
        gammaSEqual (1 / (4 * t)) ^ 2 := by positivity
    have hneg : -(4 * (1 / (4 * t)) ^ 2) < 0 := by nlinarith
    exact mul_neg_of_pos_of_neg hnum hneg
  linarith

/-- The axial balance lies at one separation. Inside it the component is outward,
and outside it the component is inward. -/
theorem octa_pair_seat {Z : ℝ} (hZ : 1 ≤ Z) :
    ∃ s, 1 / (2 * resonanceRoot1) < s ∧ s < 2 ∧ octaPairOutward Z 2 (s / 2) = 0 ∧
      (∀ s', 1 / (2 * resonanceRoot1) < s' → s' < 2 →
        octaPairOutward Z 2 (s' / 2) = 0 → s' = s) ∧
      ∀ t, 1 / (4 * resonanceRoot1) < t → t ≤ 1 →
        (t < s / 2 → 0 < octaPairOutward Z 2 t) ∧
        (s / 2 < t → octaPairOutward Z 2 t < 0) := by
  obtain ⟨s, hs1, hs2, hs0⟩ := exists_octa_pair_balance hZ
  have hanti := octaPairOutward_strictAnti hZ
  set t0 := 1 / (4 * resonanceRoot1)
  have htwo : 2 * t0 = 1 / (2 * resonanceRoot1) := by
    dsimp [t0]; field_simp; ring
  have hsI : s / 2 ∈ Ioc t0 1 := by
    refine ⟨?_, by linarith⟩
    rw [← htwo] at hs1
    linarith
  refine ⟨s, hs1, hs2, hs0, ?_, ?_⟩
  · intro s' hs1' hs2' hs0'
    have hs'I : s' / 2 ∈ Ioc t0 1 := by
      refine ⟨?_, by linarith⟩
      rw [← htwo] at hs1'
      linarith
    have hhalf := hanti.injOn hsI hs'I (by rw [hs0, hs0'])
    linarith
  · intro t ht0' ht1
    have htI : t ∈ Ioc t0 1 := ⟨ht0', ht1⟩
    refine ⟨?_, ?_⟩
    · intro hlt
      have hlt' := hanti htI hsI hlt
      rw [hs0] at hlt'
      linarith
    · intro hgt
      have hlt' := hanti hsI htI hgt
      rw [hs0] at hlt'
      linarith

end Gravity

end DstDiophantine
