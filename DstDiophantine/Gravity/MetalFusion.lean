import DstDiophantine.Gravity.ElectronMetal
import DstDiophantine.Gravity.ElectronNumbers
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

* On `[0, ∞)`, `γ_s(x) ≥ 1 - x² cosh x`. Up to phase `1`,
  `γ_s(x) ≤ 2 cos x - 1`.
* For every ion charge `Z ≥ 1`, at cage radius `2` and proton half-separation
  `1`, the axial component is strictly negative.
* As the half-separation descends to `1/(4x₁)`, the component tends to `+∞`.
* A zero therefore lies at a separation strictly between the first charge
  node and `2`.
-/

namespace DstDiophantine

namespace Gravity

open Real Set Filter

/-! ### Bounds on the interference factor -/

/-- `γ_s(x) ≥ 1 - x² cosh x` for `x ≥ 0`. -/
theorem gammaSEqual_ge_one_sub_sq_cosh {x : ℝ} (hx : 0 ≤ x) :
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
theorem gammaSEqual_le_two_cos_sub_one {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
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

private lemma exp_one_third_le : exp (1 / 3 : ℝ) ≤ 3 / 2 := by
  have h := exp_bound' (x := 1 / 3) (by norm_num) (by norm_num) (n := 4) (by decide)
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_zero] at h
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

private lemma gamma_of_le_third {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 3) :
    5 / 6 ≤ gammaSEqual x := by
  have h := gammaSEqual_ge_one_sub_sq_cosh hx0
  have hc := cosh_le_exp_of_nonneg hx0
  have hexp : exp x ≤ 3 / 2 := le_trans (exp_le_exp.mpr hx) exp_one_third_le
  have hx2 : x ^ 2 ≤ 1 / 9 := by nlinarith
  have : x ^ 2 * cosh x ≤ (1 / 9) * (3 / 2) := by
    have hc' : cosh x ≤ 3 / 2 := le_trans hc hexp
    nlinarith
  linarith

private lemma pairAttraction_le_third {x : ℝ} (hx0 : 0 < x) (hx : x ≤ 1 / 3) :
    pairAttraction x ≤ 8 / 15 := by
  have hγ := gamma_of_le_third hx0.le hx
  have hγpos : 0 < gammaSEqual x := by linarith
  have hx2 : x ^ 2 ≤ 1 / 9 := by nlinarith
  unfold pairAttraction
  have hgoal : 4 * x ^ 2 / gammaSEqual x ≤ 8 / 15 := by
    rw [div_le_iff₀ hγpos]
    have hnum : 4 * x ^ 2 ≤ 4 / 9 := by linarith
    have : (4 / 9) * (6 / 5) = 8 / 15 := by norm_num
    have hγ' : 5 / 6 ≤ gammaSEqual x := hγ
    nlinarith
  exact hgoal

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

lemma pullRate_mul_radius {r : ℝ} (hr : 0 < r) :
    pullRate (1 / (2 * r)) * r = pairAttraction (1 / (2 * r)) := by
  unfold pullRate pairAttraction
  field_simp
  ring

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

lemma nodeHalf_mem : 1 / (4 * resonanceRoot1) ∈ Ioo (5 / 19 : ℝ) (15 / 56) := by
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

end Gravity

end DstDiophantine
