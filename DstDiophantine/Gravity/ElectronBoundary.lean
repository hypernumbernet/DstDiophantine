import DstDiophantine.Gravity.ElectronCapacity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Laboratory shell boundary

## Paper boundary (do **not** claim)

The length `ℓ` is not derived. Nothing here produces a Bohr spectrum, a
numerical ionization energy, or the noble-gas counts from a polyhedron.
Twenty is the number of vertices of the dodecahedron, not a principal shell.
Uniqueness of the dodecahedral root is not claimed.

## What is proved

* The cube's far-field coefficient lies strictly between `2` and `3`. On the
  outer well every chord scale is less than one, so the cube response lies
  strictly below that coefficient. For every nuclear charge `Z ≥ 3` the cube
  therefore has no radial root in the outer well.
* The tetrahedron, the octahedron, and the icosahedron likewise have every
  chord longer than the radius. Their far-field coefficients lie strictly
  below `1`, `2`, and `5`. For every nuclear charge at least that large, the
  outward force stays inward through the outer well.
* The nearest chord of a regular dodecahedron is shorter than the radius, and
  the far-field coefficient of its twenty vertices is strictly less than `8`.
  For every nuclear charge `Z ≥ 8` the radial response therefore passes through
  `Z` while every pair is still outside the first node: the force is inward at
  large separation and outward beside that chord node.
-/

namespace DstDiophantine

namespace Gravity

open Real Set Filter

/-! ### Cube coefficient in the outer well -/

noncomputable def cubeFar : ℝ :=
  cubeCoeffEdge + cubeCoeffFace + cubeCoeffBody

lemma sqrt_six_gt_twelve_fifths : (12 / 5 : ℝ) < sqrt 6 := by
  rw [← sqrt_sq (by norm_num : (0 : ℝ) ≤ 12 / 5)]
  exact (sqrt_lt_sqrt_iff (by positivity)).mpr (by norm_num)

theorem cubeFar_bounds : (2 : ℝ) < cubeFar ∧ cubeFar < 3 := by
  unfold cubeFar cubeCoeffEdge cubeCoeffFace cubeCoeffBody
  constructor
  · have h3 : (173 / 100 : ℝ) < sqrt 3 := sqrt_three_gt_oneSevenThree
    have h6 : (12 / 5 : ℝ) < sqrt 6 := sqrt_six_gt_twelve_fifths
    have h3' : (519 / 400 : ℝ) < 3 * sqrt 3 / 4 := by nlinarith
    have h6' : (9 / 10 : ℝ) < 3 * sqrt 6 / 8 := by nlinarith
    linarith
  · have h3 : sqrt 3 < (26 / 15 : ℝ) := sqrt_three_lt_twentySix_fifteenths
    have h6 : sqrt 6 < (5 / 2 : ℝ) := sqrt_six_lt_five_halves
    have h3' : 3 * sqrt 3 / 4 < (13 / 10 : ℝ) := by nlinarith
    have h6' : 3 * sqrt 6 / 8 < (15 / 16 : ℝ) := by nlinarith
    linarith

theorem scaledRatio_lt_one {c x : ℝ} (hc0 : 0 < c) (hc1 : c < 1) (hx0 : 0 < x)
    (hx1 : x < resonanceRoot1) : scaledRatio c x < 1 := by
  have hcx : c * x < x := by nlinarith
  have hxπ : x < π :=
    lt_trans hx1 (lt_trans resonanceRoot1_sharp_bounds.2 (by linarith [pi_gt_three]))
  have hcx0 : 0 ≤ c * x := by positivity
  have hmemx : x ∈ Icc (0 : ℝ) π := ⟨hx0.le, hxπ.le⟩
  have hmemcx : c * x ∈ Icc (0 : ℝ) π := ⟨hcx0, le_trans hcx.le hxπ.le⟩
  have hγ : gammaSEqual x < gammaSEqual (c * x) :=
    strictAntiOn_gammaSEqual_even 0 (by simpa using hmemcx) (by simpa using hmemx) hcx
  have hpos : 0 < gammaSEqual (c * x) :=
    gammaSEqual_pos_of_lt_firstNode hcx0 (lt_trans hcx hx1)
  unfold scaledRatio
  rw [div_lt_one hpos]
  exact hγ

theorem cubeResponse_lt_cubeFar {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) resonanceRoot1) :
    cubeResponse x < cubeFar := by
  have hscale := cubeScale_mem_Ioo
  have hedge := scaledRatio_lt_one (c := cubeEdge)
      (by nlinarith [hscale.1, hscale.2.1]) hscale.2.2 hx.1 hx.2
  have hface := scaledRatio_lt_one (c := cubeFace)
      (by nlinarith [hscale.1]) (by nlinarith [hscale.2.1]) hx.1 hx.2
  have hbody := scaledRatio_lt_one (c := (1 / 2 : ℝ)) (by norm_num) (by norm_num) hx.1 hx.2
  have hcoeff := cubeCoeff_pos
  unfold cubeResponse cubeFar
  nlinarith

/-- For every nuclear charge `Z ≥ 3`, eight electrons at the vertices of a cube
have no radial balance in the outer well. -/
theorem cube_no_outer_root {Z x : ℝ} (hZ : 3 ≤ Z) (hx : x ∈ Ioo (0 : ℝ) resonanceRoot1) :
    cubeOutward Z x < 0 := by
  have hγ : 0 < gammaSEqual x := gammaSEqual_pos_left_of_first_node hx
  have hscale := cubeScale_mem_Ioo
  have hx0 : 0 < x := hx.1
  have hedge0 : 0 < cubeEdge := by nlinarith [hscale.1, hscale.2.1]
  have hface0 : 0 < cubeFace := by nlinarith [hscale.1]
  have he : gammaSEqual (cubeEdge * x) ≠ 0 :=
    (gammaSEqual_pos_of_lt_firstNode (mul_nonneg hedge0.le hx0.le)
      (by nlinarith [hscale.2.2, hx.2])).ne'
  have hf : gammaSEqual (cubeFace * x) ≠ 0 :=
    (gammaSEqual_pos_of_lt_firstNode (mul_nonneg hface0.le hx0.le)
      (by nlinarith [hscale.2.1, hx.2])).ne'
  have hb : gammaSEqual (x / 2) ≠ 0 :=
    (gammaSEqual_pos_of_lt_firstNode (by positivity) (by linarith [hx.2])).ne'
  rw [cubeOutward_eq_response hγ.ne' he hf hb]
  have hresp : cubeResponse x < Z := by
    have hfar : cubeFar < 3 := cubeFar_bounds.2
    have hlt : cubeResponse x < cubeFar := cubeResponse_lt_cubeFar hx
    linarith
  exact div_neg_of_neg_of_pos (by linarith) hγ

/-! ### The dodecahedron meets the node on a chord -/

noncomputable def dodecaNear : ℝ := sqrt (3 * (3 + sqrt 5) / 8)

noncomputable def dodecaFarScale : ℝ := sqrt (3 * (3 - sqrt 5) / 8)

noncomputable def dodecaCoeff : ℝ :=
  3 / 2 * dodecaNear + 3 * sqrt 3 / 2 + 3 * sqrt 6 / 4 + 3 / 2 * dodecaFarScale + 1 / 4

noncomputable def dodecaResponse (x : ℝ) : ℝ :=
  (3 / 2 * dodecaNear) * scaledRatio dodecaNear x +
    (3 * sqrt 3 / 2) * scaledRatio (sqrt 3 / 2) x +
    (3 * sqrt 6 / 4) * scaledRatio (sqrt 6 / 4) x +
    (3 / 2 * dodecaFarScale) * scaledRatio dodecaFarScale x +
    (1 / 4) * scaledRatio (1 / 2) x

noncomputable def dodecaWall : ℝ := resonanceRoot1 / dodecaNear

noncomputable def dodecaOutward (Z x : ℝ) : ℝ :=
  -Z / gammaSEqual x +
    (3 / 2 * dodecaNear) / gammaSEqual (dodecaNear * x) +
    (3 * sqrt 3 / 2) / gammaSEqual ((sqrt 3 / 2) * x) +
    (3 * sqrt 6 / 4) / gammaSEqual ((sqrt 6 / 4) * x) +
    (3 / 2 * dodecaFarScale) / gammaSEqual (dodecaFarScale * x) +
    (1 / 4) / gammaSEqual (x / 2)

theorem dodecaOutward_eq_response {Z x : ℝ}
    (hx : gammaSEqual x ≠ 0) (hnear : gammaSEqual (dodecaNear * x) ≠ 0)
    (_h3 : gammaSEqual ((sqrt 3 / 2) * x) ≠ 0) (_h6 : gammaSEqual ((sqrt 6 / 4) * x) ≠ 0)
    (_hfar : gammaSEqual (dodecaFarScale * x) ≠ 0) (hhalf : gammaSEqual (x / 2) ≠ 0) :
    dodecaOutward Z x = (dodecaResponse x - Z) / gammaSEqual x := by
  unfold dodecaOutward dodecaResponse scaledRatio
  field_simp [hx, hnear, _h3, _h6, _hfar, hhalf]
  ring

theorem dodecaNear_gt_one : (1 : ℝ) < dodecaNear := by
  have hsq : dodecaNear ^ 2 = 3 * (3 + sqrt 5) / 8 := by
    unfold dodecaNear
    exact sq_sqrt (by nlinarith [sqrt_nonneg (5 : ℝ)])
  have hlt : (1 : ℝ) ^ 2 < dodecaNear ^ 2 := by
    rw [hsq, lt_div_iff₀ (by norm_num)]
    nlinarith [sqrt_pos.mpr (by norm_num : (0 : ℝ) < 5)]
  have hnn : 0 ≤ dodecaNear := by
    unfold dodecaNear
    exact sqrt_nonneg _
  rw [← abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1), ← abs_of_nonneg hnn]
  exact (sq_lt_sq).mp hlt

theorem dodecaFarScale_lt_one : dodecaFarScale < 1 := by
  have h5sq : (2 : ℝ) ^ 2 < (sqrt 5) ^ 2 := by
    rw [sq_sqrt (by norm_num)]
    norm_num
  have h5 : (2 : ℝ) < sqrt 5 := by
    rw [← abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
      ← abs_of_nonneg (sqrt_nonneg (5 : ℝ))]
    exact (sq_lt_sq).mp h5sq
  have h5lt : sqrt 5 < 3 := by
    have hsq5 : (sqrt 5) ^ 2 < (3 : ℝ) ^ 2 := by
      rw [sq_sqrt (by norm_num)]
      norm_num
    rw [← abs_of_nonneg (sqrt_nonneg (5 : ℝ)), ← abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)]
    exact (sq_lt_sq).mp hsq5
  have hsq : dodecaFarScale ^ 2 = 3 * (3 - sqrt 5) / 8 := by
    unfold dodecaFarScale
    exact sq_sqrt (by nlinarith [h5lt])
  have hlt : dodecaFarScale ^ 2 < (1 : ℝ) ^ 2 := by
    rw [hsq, div_lt_iff₀ (by norm_num)]
    nlinarith [h5]
  have hnn : 0 ≤ dodecaFarScale := by
    unfold dodecaFarScale
    exact sqrt_nonneg _
  rw [← abs_of_nonneg hnn, ← abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)]
  exact (sq_lt_sq).mp hlt

theorem dodecaCoeff_lt_eight : dodecaCoeff < 8 := by
  have hsq : (sqrt 5) ^ 2 = 5 := sq_sqrt (by norm_num)
  have hnear : dodecaNear < (141 / 100 : ℝ) := by
    have h5sq : (sqrt 5) ^ 2 < (9 / 4 : ℝ) ^ 2 := by
      rw [hsq]; norm_num
    have h5 : sqrt 5 < 9 / 4 := by
      rw [← abs_of_nonneg (sqrt_nonneg (5 : ℝ)),
        ← abs_of_pos (by norm_num : (0 : ℝ) < 9 / 4)]
      exact (sq_lt_sq).mp h5sq
    have hpow : dodecaNear ^ 2 = 3 * (3 + sqrt 5) / 8 := by
      unfold dodecaNear
      exact sq_sqrt (by nlinarith [sqrt_nonneg (5 : ℝ)])
    have hlt : dodecaNear ^ 2 < (141 / 100 : ℝ) ^ 2 := by
      rw [hpow]; nlinarith [h5]
    have hnn : 0 ≤ dodecaNear := by
      unfold dodecaNear
      exact sqrt_nonneg _
    rw [← abs_of_nonneg hnn, ← abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 141 / 100)]
    exact (sq_lt_sq).mp hlt
  have hfar : dodecaFarScale < (3 / 5 : ℝ) := by
    unfold dodecaFarScale
    have h5sq : (51 / 25 : ℝ) ^ 2 < (sqrt 5) ^ 2 := by
      rw [hsq]
      norm_num
    have h5 : 51 / 25 < sqrt 5 := by
      rw [← abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 51 / 25),
        ← abs_of_nonneg (sqrt_nonneg (5 : ℝ))]
      exact (sq_lt_sq).mp h5sq
    have h5lt : sqrt 5 < 3 := by
      have hsq3 : (sqrt 5) ^ 2 < (3 : ℝ) ^ 2 := by
        rw [sq_sqrt (by norm_num)]; norm_num
      rw [← abs_of_nonneg (sqrt_nonneg (5 : ℝ)), ← abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)]
      exact (sq_lt_sq).mp hsq3
    have hpow : dodecaFarScale ^ 2 = 3 * (3 - sqrt 5) / 8 := by
      unfold dodecaFarScale
      exact sq_sqrt (by nlinarith [h5lt])
    have hlt : dodecaFarScale ^ 2 < (3 / 5 : ℝ) ^ 2 := by
      rw [hpow]; nlinarith [h5]
    have hnn0 : 0 ≤ sqrt (3 * (3 - sqrt 5) / 8) := sqrt_nonneg _
    rw [← abs_of_nonneg hnn0, ← abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 5)]
    apply (sq_lt_sq).mp
    rw [sq_sqrt (by nlinarith [h5lt])]
    nlinarith [h5]
  have h3 : sqrt 3 < (26 / 15 : ℝ) := sqrt_three_lt_twentySix_fifteenths
  have h6 : sqrt 6 < (5 / 2 : ℝ) := sqrt_six_lt_five_halves
  unfold dodecaCoeff
  nlinarith

theorem dodecaWall_mem_Ioo : dodecaWall ∈ Ioo (0 : ℝ) resonanceRoot1 := by
  unfold dodecaWall
  have hnear := dodecaNear_gt_one
  have hx1 : 0 < resonanceRoot1 := lt_trans (by norm_num : (0 : ℝ) < 1 / 2) resonanceRoot1_bounds.1
  refine ⟨div_pos hx1 (by linarith), ?_⟩
  rw [div_lt_iff₀ (by linarith)]
  nlinarith

lemma dodeca_scales_lt_near :
    sqrt 3 / 2 < dodecaNear ∧ sqrt 6 / 4 < dodecaNear ∧
      dodecaFarScale < dodecaNear ∧ (1 / 2 : ℝ) < dodecaNear := by
  have hnear := dodecaNear_gt_one
  have hfar := dodecaFarScale_lt_one
  have h3 : sqrt 3 / 2 < 1 := by
    rw [div_lt_one (by norm_num : (0 : ℝ) < 2)]
    exact lt_trans sqrt_three_lt_twentySix_fifteenths (by norm_num)
  have h6 : sqrt 6 / 4 < 1 := by
    rw [div_lt_one (by norm_num : (0 : ℝ) < 4)]
    exact lt_trans sqrt_six_lt_five_halves (by norm_num)
  exact ⟨lt_trans h3 hnear, lt_trans h6 hnear, lt_trans hfar hnear, by linarith⟩

lemma gamma_pos_dodeca_phase {s x : ℝ} (hs0 : 0 < s) (hs : s ≤ dodecaNear)
    (hx : x ∈ Ioo (0 : ℝ) dodecaWall) : 0 < gammaSEqual (s * x) := by
  have hx1 : s * x < resonanceRoot1 := by
    have hwall : dodecaNear * x < resonanceRoot1 := by
      have hw := dodecaWall_mem_Ioo
      unfold dodecaWall at hw
      have hpos : 0 < dodecaNear := by linarith [dodecaNear_gt_one]
      have hx2 : x < resonanceRoot1 / dodecaNear := by simpa [dodecaWall] using hx.2
      rw [lt_div_iff₀ hpos] at hx2
      simpa [mul_comm] using hx2
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hs (le_of_lt hx.1)) hwall
  exact gammaSEqual_pos_of_lt_firstNode (mul_nonneg (le_of_lt hs0) (le_of_lt hx.1)) hx1

theorem continuousOn_dodecaResponse :
    ContinuousOn dodecaResponse (Ioo (0 : ℝ) dodecaWall) := by
  have hsc := dodeca_scales_lt_near
  unfold dodecaResponse scaledRatio
  refine ContinuousOn.add (ContinuousOn.add (ContinuousOn.add (ContinuousOn.add ?_ ?_) ?_) ?_) ?_
  · refine ContinuousOn.mul continuousOn_const
      (ContinuousOn.div continuous_gammaSEqual.continuousOn
        (continuous_gammaSEqual.comp (continuous_const.mul continuous_id)).continuousOn ?_)
    intro x hx
    exact (gamma_pos_dodeca_phase (by linarith [dodecaNear_gt_one]) le_rfl hx).ne'
  · refine ContinuousOn.mul continuousOn_const
      (ContinuousOn.div continuous_gammaSEqual.continuousOn
        (continuous_gammaSEqual.comp (continuous_const.mul continuous_id)).continuousOn ?_)
    intro x hx
    exact (gamma_pos_dodeca_phase (div_pos (sqrt_pos.mpr (by norm_num)) (by norm_num)) hsc.1.le hx).ne'
  · refine ContinuousOn.mul continuousOn_const
      (ContinuousOn.div continuous_gammaSEqual.continuousOn
        (continuous_gammaSEqual.comp (continuous_const.mul continuous_id)).continuousOn ?_)
    intro x hx
    exact (gamma_pos_dodeca_phase (div_pos (sqrt_pos.mpr (by norm_num)) (by norm_num)) hsc.2.1.le hx).ne'
  · refine ContinuousOn.mul continuousOn_const
      (ContinuousOn.div continuous_gammaSEqual.continuousOn
        (continuous_gammaSEqual.comp (continuous_const.mul continuous_id)).continuousOn ?_)
    intro x hx
    exact (gamma_pos_dodeca_phase (sqrt_pos.mpr (by nlinarith [sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]))
      hsc.2.2.1.le hx).ne'
  · refine ContinuousOn.mul continuousOn_const
      (ContinuousOn.div continuous_gammaSEqual.continuousOn
        (continuous_gammaSEqual.comp (continuous_const.mul continuous_id)).continuousOn ?_)
    intro x hx
    exact (gamma_pos_dodeca_phase (by norm_num) hsc.2.2.2.le hx).ne'

theorem exists_dodecaResponse_gt {M : ℝ} (hM : 0 < M) :
    ∃ x ∈ Ioo (0 : ℝ) dodecaWall, M < dodecaResponse x := by
  set a : ℝ := 3 / 2 * dodecaNear
  have ha : 0 < a := by
    unfold a
    nlinarith [dodecaNear_gt_one]
  have hw := dodecaWall_mem_Ioo
  have hγw : 0 < gammaSEqual dodecaWall := gammaSEqual_pos_left_of_first_node hw
  set ε : ℝ := a * gammaSEqual dodecaWall / (M + 1)
  have hε : 0 < ε := by positivity
  have hcont : ContinuousAt gammaSEqual resonanceRoot1 := continuous_gammaSEqual.continuousAt
  obtain ⟨δ, hδpos, hδ⟩ := Metric.mem_nhds_iff.mp (hcont (Metric.ball_mem_nhds _ hε))
  have hx1 : 0 < resonanceRoot1 :=
    lt_trans (by norm_num : (0 : ℝ) < 1 / 2) resonanceRoot1_bounds.1
  set t : ℝ := resonanceRoot1 - min (δ / 2) (resonanceRoot1 / 2)
  have ht0 : 0 < t := by
    have hmin : min (δ / 2) (resonanceRoot1 / 2) ≤ resonanceRoot1 / 2 := min_le_right _ _
    linarith
  have ht1 : t < resonanceRoot1 := by
    have hmin : 0 < min (δ / 2) (resonanceRoot1 / 2) := by positivity
    linarith
  have hdist : |t - resonanceRoot1| < δ := by
    have habs : |t - resonanceRoot1| = min (δ / 2) (resonanceRoot1 / 2) := by
      rw [show t - resonanceRoot1 = -(min (δ / 2) (resonanceRoot1 / 2)) by ring, abs_neg,
        abs_of_pos (by positivity)]
    have hle : min (δ / 2) (resonanceRoot1 / 2) ≤ δ / 2 := min_le_left _ _
    linarith
  have hball : t ∈ Metric.ball resonanceRoot1 δ := by
    rw [Metric.mem_ball, Real.dist_eq, abs_sub_comm]
    simpa [abs_sub_comm] using hdist
  have hγclose := hδ hball
  have hγabs : |gammaSEqual t| < ε := by
    have hmem : gammaSEqual t ∈ Metric.ball (gammaSEqual resonanceRoot1) ε := hγclose
    rwa [Metric.mem_ball, resonanceRoot1_gammaSEqual_zero, Real.dist_eq, sub_zero] at hmem
  have hγt : 0 < gammaSEqual t :=
    gammaSEqual_pos_of_lt_firstNode (le_of_lt ht0) ht1
  have hγt_lt : gammaSEqual t < ε := by
    rw [abs_lt] at hγabs
    exact hγabs.2
  set x : ℝ := t / dodecaNear
  have hxmem : x ∈ Ioo (0 : ℝ) dodecaWall := by
    refine ⟨div_pos ht0 (by linarith [dodecaNear_gt_one]), ?_⟩
    unfold dodecaWall
    rw [div_lt_div_iff_of_pos_right (by linarith [dodecaNear_gt_one])]
    exact ht1
  have hphase : dodecaNear * x = t := by
    unfold x
    field_simp [show dodecaNear ≠ 0 by linarith [dodecaNear_gt_one]]
  have hxγ : gammaSEqual dodecaWall < gammaSEqual x := by
    have hxlt : x < dodecaWall := hxmem.2
    have hxπ : dodecaWall < π :=
      lt_trans hw.2 (lt_trans resonanceRoot1_sharp_bounds.2 (by linarith [pi_gt_three]))
    have hmemw : dodecaWall ∈ Icc (0 : ℝ) π := ⟨le_of_lt hw.1, hxπ.le⟩
    have hmemx : x ∈ Icc (0 : ℝ) π := ⟨le_of_lt hxmem.1, le_trans hxlt.le hxπ.le⟩
    exact strictAntiOn_gammaSEqual_even 0 (by simpa using hmemx) (by simpa using hmemw) hxlt
  have hnear : M < a * scaledRatio dodecaNear x := by
    unfold scaledRatio
    rw [hphase]
    have hden : 0 < gammaSEqual t := hγt
    have hdiv : a * gammaSEqual dodecaWall / gammaSEqual t <
        a * gammaSEqual x / gammaSEqual t := by
      have hquot : gammaSEqual dodecaWall / gammaSEqual t < gammaSEqual x / gammaSEqual t :=
        (div_lt_div_iff_of_pos_right hden).mpr hxγ
      simpa [mul_div_assoc] using mul_lt_mul_of_pos_left hquot ha
    have hbig : M < a * gammaSEqual dodecaWall / gammaSEqual t := by
      have hεt : gammaSEqual t * (M + 1) < a * gammaSEqual dodecaWall := by
        have hdiv := hγt_lt
        rwa [lt_div_iff₀ (by linarith : (0 : ℝ) < M + 1)] at hdiv
      have hsum : gammaSEqual t * M + gammaSEqual t < a * gammaSEqual dodecaWall := by
        simpa [mul_add, mul_one] using hεt
      have hMγ : M * gammaSEqual t < a * gammaSEqual dodecaWall := by
        simpa [mul_comm] using (by nlinarith [hγt, hsum] : gammaSEqual t * M < a * gammaSEqual dodecaWall)
      exact (lt_div_iff₀ hden).mpr hMγ
    have hdiv' : a * gammaSEqual dodecaWall / gammaSEqual t <
        a * (gammaSEqual x / gammaSEqual t) := by
      simpa [div_eq_mul_inv, mul_assoc] using hdiv
    have hbig' : M < a * gammaSEqual dodecaWall / gammaSEqual t := by
      simpa [div_eq_mul_inv, mul_assoc] using hbig
    simpa [div_eq_mul_inv, mul_assoc] using lt_trans hbig' hdiv'
  have hrest : 0 ≤ dodecaResponse x - a * scaledRatio dodecaNear x := by
    unfold dodecaResponse
    have hsc := dodeca_scales_lt_near
    have hpos := fun s hs0 hs => gamma_pos_dodeca_phase (s := s) hs0 hs hxmem
    have h1 : 0 < scaledRatio (sqrt 3 / 2) x := by
      unfold scaledRatio
      exact div_pos (gammaSEqual_pos_left_of_first_node ⟨hxmem.1,
        lt_trans hxmem.2 (dodecaWall_mem_Ioo.2)⟩)
        (hpos _ (div_pos (sqrt_pos.mpr (by norm_num)) (by norm_num)) hsc.1.le)
    have h2 : 0 < scaledRatio (sqrt 6 / 4) x := by
      unfold scaledRatio
      exact div_pos (gammaSEqual_pos_left_of_first_node ⟨hxmem.1,
        lt_trans hxmem.2 (dodecaWall_mem_Ioo.2)⟩)
        (hpos _ (div_pos (sqrt_pos.mpr (by norm_num)) (by norm_num)) hsc.2.1.le)
    have h3 : 0 < scaledRatio dodecaFarScale x := by
      unfold scaledRatio
      exact div_pos (gammaSEqual_pos_left_of_first_node ⟨hxmem.1,
        lt_trans hxmem.2 (dodecaWall_mem_Ioo.2)⟩)
        (hpos _ (by unfold dodecaFarScale; exact sqrt_pos.mpr (by
          nlinarith [sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num),
            show sqrt 5 < 3 by
              have hsq3 : (sqrt 5) ^ 2 < (3 : ℝ) ^ 2 := by
                rw [sq_sqrt (by norm_num)]; norm_num
              rw [← abs_of_nonneg (sqrt_nonneg (5 : ℝ)), ← abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)]
              exact (sq_lt_sq).mp hsq3])) hsc.2.2.1.le)
    have h4 : 0 < scaledRatio (1 / 2) x := by
      unfold scaledRatio
      exact div_pos (gammaSEqual_pos_left_of_first_node ⟨hxmem.1,
        lt_trans hxmem.2 (dodecaWall_mem_Ioo.2)⟩)
        (hpos _ (by norm_num) hsc.2.2.2.le)
    have hc3 : 0 < 3 * sqrt 3 / 2 := by
      nlinarith [sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3)]
    have hc6 : 0 < 3 * sqrt 6 / 4 := by
      nlinarith [sqrt_pos.mpr (by norm_num : (0 : ℝ) < 6)]
    have h5lt : sqrt 5 < 3 := by
      have hsq3 : (sqrt 5) ^ 2 < (3 : ℝ) ^ 2 := by
        rw [sq_sqrt (by norm_num)]; norm_num
      rw [← abs_of_nonneg (sqrt_nonneg (5 : ℝ)), ← abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)]
      exact (sq_lt_sq).mp hsq3
    have hcf : 0 < 3 / 2 * dodecaFarScale := by
      have hpos : 0 < dodecaFarScale := by
        unfold dodecaFarScale
        exact sqrt_pos.mpr (by nlinarith [h5lt])
      nlinarith
    have hp1 : 0 ≤ (3 * sqrt 3 / 2) * scaledRatio (sqrt 3 / 2) x := (mul_pos hc3 h1).le
    have hp2 : 0 ≤ (3 * sqrt 6 / 4) * scaledRatio (sqrt 6 / 4) x := (mul_pos hc6 h2).le
    have hp3 : 0 ≤ (3 / 2 * dodecaFarScale) * scaledRatio dodecaFarScale x := (mul_pos hcf h3).le
    have hp4 : 0 ≤ (1 / 4) * scaledRatio (1 / 2) x := by nlinarith [h4]
    have hcancel : (3 / 2 * dodecaNear) * scaledRatio dodecaNear x -
        a * scaledRatio dodecaNear x = 0 := by
      unfold a; ring
    linarith [hp1, hp2, hp3, hp4, hcancel]
  refine ⟨x, hxmem, ?_⟩
  linarith [hnear, hrest]

lemma tendsto_scaledRatio_zero {c : ℝ} (_hc : c ≠ 0) :
    Tendsto (scaledRatio c) (nhds 0) (nhds 1) := by
  have hγ : Tendsto gammaSEqual (nhds 0) (nhds 1) := by
    simpa [gammaSEqual_zero] using continuous_gammaSEqual.tendsto 0
  have hmul : Tendsto (fun x : ℝ => c * x) (nhds 0) (nhds 0) := by
    simpa [mul_zero] using
      (tendsto_const_nhds.mul (tendsto_id : Tendsto id (nhds (0 : ℝ)) (nhds 0)))
  have hcomp : Tendsto (fun x => gammaSEqual (c * x)) (nhds 0) (nhds 1) := by
    simpa [Function.comp_def, gammaSEqual_zero] using hγ.comp hmul
  unfold scaledRatio
  convert hγ.div hcomp one_ne_zero using 1
  · ext x
    rfl
  · simp

lemma tendsto_dodecaResponse_zero :
    Tendsto dodecaResponse (nhds 0) (nhds dodecaCoeff) := by
  unfold dodecaResponse
  have h1 := (tendsto_scaledRatio_zero (show dodecaNear ≠ 0 by linarith [dodecaNear_gt_one])).const_mul
    (3 / 2 * dodecaNear)
  have h2 := (tendsto_scaledRatio_zero (div_pos (sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3))
      (by norm_num : (0 : ℝ) < 2)).ne').const_mul (3 * sqrt 3 / 2)
  have h3 := (tendsto_scaledRatio_zero (div_pos (sqrt_pos.mpr (by norm_num : (0 : ℝ) < 6))
      (by norm_num : (0 : ℝ) < 4)).ne').const_mul (3 * sqrt 6 / 4)
  have h4 := (tendsto_scaledRatio_zero (by
    have hnn : 0 ≤ dodecaFarScale := by unfold dodecaFarScale; exact sqrt_nonneg _
    have hne : dodecaFarScale ≠ 0 := by
      intro h
      have hsq : dodecaFarScale ^ 2 = 0 := by simp [h]
      have hpos : 0 < dodecaFarScale ^ 2 := by
        have h5 : sqrt 5 < 3 := by
          have hsq3 : (sqrt 5) ^ 2 < (3 : ℝ) ^ 2 := by rw [sq_sqrt (by norm_num)]; norm_num
          rw [← abs_of_nonneg (sqrt_nonneg (5 : ℝ)), ← abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)]
          exact (sq_lt_sq).mp hsq3
        have hpow : dodecaFarScale ^ 2 = 3 * (3 - sqrt 5) / 8 := by
          unfold dodecaFarScale
          exact sq_sqrt (by nlinarith [h5])
        rw [hpow]; nlinarith [h5]
      linarith
    exact hne)).const_mul (3 / 2 * dodecaFarScale)
  have h5 := (tendsto_scaledRatio_zero (by norm_num : (1 / 2 : ℝ) ≠ 0)).const_mul ((1 / 4 : ℝ))
  have hsum := (((h1.add h2).add h3).add h4).add h5
  simpa [dodecaCoeff, mul_one] using hsum

theorem exists_dodeca_outer_root {Z : ℝ} (hZ : 8 ≤ Z) :
    ∃ x ∈ Ioo (0 : ℝ) dodecaWall, dodecaResponse x = Z := by
  have hcoeff : dodecaCoeff < Z := lt_of_lt_of_le dodecaCoeff_lt_eight hZ
  obtain ⟨δ, hδpos, hδ⟩ := Metric.mem_nhds_iff.mp
      (tendsto_dodecaResponse_zero (Metric.ball_mem_nhds _ (sub_pos.mpr hcoeff)))
  have hx1 : 0 < dodecaWall := dodecaWall_mem_Ioo.1
  set a : ℝ := min (δ / 2) (dodecaWall / 2)
  have ha0 : 0 < a := by positivity
  have haδ : |a - 0| < δ := by
    rw [sub_zero, abs_of_pos ha0]
    exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hball : a ∈ Metric.ball 0 δ := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero]
    simpa [sub_zero] using haδ
  have hclose := hδ hball
  have hlt : dodecaResponse a < Z := by
    have hmem : dodecaResponse a ∈ Metric.ball dodecaCoeff (Z - dodecaCoeff) := hclose
    rw [Metric.mem_ball, Real.dist_eq] at hmem
    rw [abs_lt] at hmem
    linarith
  have hgt := exists_dodecaResponse_gt (M := Z) (by linarith)
  obtain ⟨b, hb, hbgt⟩ := hgt
  have ha_wall : a < dodecaWall := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have ha_pos : 0 < a := by positivity
  have hne : a ≠ b := by
    intro h
    rw [h] at hlt
    exact lt_irrefl _ (hlt.trans hbgt)
  have hcont : ContinuousOn dodecaResponse (Ioo (0 : ℝ) dodecaWall) :=
    continuousOn_dodecaResponse
  rcases lt_trichotomy a b with hab | heq | hba
  · obtain ⟨x, hxI, hx0⟩ := intermediate_value_Ioo hab.le
      (hcont.mono fun t ht => ⟨lt_of_lt_of_le ha_pos ht.1, lt_of_le_of_lt ht.2 hb.2⟩)
      (show Z ∈ Ioo (dodecaResponse a) (dodecaResponse b) from ⟨hlt, hbgt⟩)
    exact ⟨x, ⟨lt_trans ha_pos hxI.1, lt_trans hxI.2 hb.2⟩, hx0⟩
  · exact absurd heq hne
  · obtain ⟨x, hxI, hx0⟩ := intermediate_value_Ioo' (a := b) (b := a) hba.le
      (hcont.mono fun t ht => ⟨lt_of_lt_of_le hb.1 ht.1, lt_of_le_of_lt ht.2 ha_wall⟩)
      (show Z ∈ Ioo (dodecaResponse a) (dodecaResponse b) from ⟨hlt, hbgt⟩)
    exact ⟨x, ⟨lt_trans hb.1 hxI.1, lt_trans hxI.2 ha_wall⟩, hx0⟩

/-! ### Regular shells with every chord longer than the radius -/

lemma chordPhase_lt_root {c x : ℝ} (hc1 : c < 1) (hx0 : 0 < x) (hx1 : x < resonanceRoot1) :
    c * x < resonanceRoot1 := by
  have hcx : c * x < x := by
    simpa using mul_lt_mul_of_pos_right hc1 hx0
  exact lt_trans hcx hx1

lemma halfPhase_lt_root {x : ℝ} (hx0 : 0 < x) (hx1 : x < resonanceRoot1) :
    x / 2 < resonanceRoot1 :=
  lt_trans (div_lt_self hx0 (by norm_num : (1 : ℝ) < 2)) hx1

noncomputable def tetraScale : ℝ := sqrt 6 / 4

noncomputable def tetraCoeff : ℝ := 3 * sqrt 6 / 8

noncomputable def tetraResponse (x : ℝ) : ℝ :=
  tetraCoeff * scaledRatio tetraScale x

noncomputable def tetraOutward (Z x : ℝ) : ℝ :=
  -Z / gammaSEqual x + tetraCoeff / gammaSEqual (tetraScale * x)

noncomputable def octaEdge : ℝ := sqrt 2 / 2

noncomputable def octaCoeff : ℝ := sqrt 2 + 1 / 4

noncomputable def octaResponse (x : ℝ) : ℝ :=
  sqrt 2 * scaledRatio octaEdge x + (1 / 4) * scaledRatio (1 / 2) x

noncomputable def octaOutward (Z x : ℝ) : ℝ :=
  -Z / gammaSEqual x +
    sqrt 2 / gammaSEqual (octaEdge * x) +
    (1 / 4) / gammaSEqual (x / 2)

noncomputable def icosaRadius : ℝ := sqrt ((5 + sqrt 5) / 2)

noncomputable def icosaEdge : ℝ := icosaRadius / 2

noncomputable def icosaMid : ℝ := icosaRadius * (sqrt 5 - 1) / 4

noncomputable def icosaCoeff : ℝ := (5 / 4) * sqrt (5 + 2 * sqrt 5) + 1 / 4

noncomputable def icosaResponse (x : ℝ) : ℝ :=
  (5 / 2 * icosaEdge) * scaledRatio icosaEdge x +
    (5 / 2 * icosaMid) * scaledRatio icosaMid x +
    (1 / 4) * scaledRatio (1 / 2) x

noncomputable def icosaOutward (Z x : ℝ) : ℝ :=
  -Z / gammaSEqual x +
    (5 / 2 * icosaEdge) / gammaSEqual (icosaEdge * x) +
    (5 / 2 * icosaMid) / gammaSEqual (icosaMid * x) +
    (1 / 4) / gammaSEqual (x / 2)

theorem tetraScale_mem_Ioo : tetraScale ∈ Ioo (0 : ℝ) 1 := by
  refine ⟨by unfold tetraScale; positivity, ?_⟩
  unfold tetraScale
  have h6 : sqrt 6 < 5 / 2 := sqrt_six_lt_five_halves
  nlinarith

theorem tetraCoeff_lt_one : tetraCoeff < 1 := by
  have h6 : sqrt 6 < 5 / 2 := sqrt_six_lt_five_halves
  unfold tetraCoeff
  nlinarith

theorem tetraOutward_eq_response {Z x : ℝ}
    (hx : gammaSEqual x ≠ 0) (hs : gammaSEqual (tetraScale * x) ≠ 0) :
    tetraOutward Z x = (tetraResponse x - Z) / gammaSEqual x := by
  unfold tetraOutward tetraResponse scaledRatio
  field_simp [hx, hs]
  ring

theorem tetraResponse_lt_tetraCoeff {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) resonanceRoot1) :
    tetraResponse x < tetraCoeff := by
  have hscale := tetraScale_mem_Ioo
  have hratio := scaledRatio_lt_one (c := tetraScale) hscale.1 hscale.2 hx.1 hx.2
  have hcoeff : 0 < tetraCoeff := by unfold tetraCoeff; positivity
  unfold tetraResponse
  nlinarith

/-- For every nuclear charge `Z ≥ 1`, four electrons at the vertices of a
regular tetrahedron have no radial balance in the outer well. -/
theorem tetra_no_outer_root {Z x : ℝ} (hZ : 1 ≤ Z) (hx : x ∈ Ioo (0 : ℝ) resonanceRoot1) :
    tetraOutward Z x < 0 := by
  have hγ : 0 < gammaSEqual x := gammaSEqual_pos_left_of_first_node hx
  have hscale := tetraScale_mem_Ioo
  have hs : gammaSEqual (tetraScale * x) ≠ 0 :=
    (gammaSEqual_pos_of_lt_firstNode (mul_nonneg hscale.1.le hx.1.le)
      (chordPhase_lt_root hscale.2 hx.1 hx.2)).ne'
  rw [tetraOutward_eq_response hγ.ne' hs]
  have hresp : tetraResponse x < Z := by
    linarith [tetraResponse_lt_tetraCoeff hx, tetraCoeff_lt_one, hZ]
  exact div_neg_of_neg_of_pos (by linarith) hγ

theorem sqrt_two_lt_seven_quarters : sqrt 2 < 7 / 4 := by
  have hsq : (sqrt 2) ^ 2 < (7 / 4 : ℝ) ^ 2 := by
    rw [sq_sqrt (by norm_num)]
    norm_num
  have habs : |sqrt 2| < |(7 / 4 : ℝ)| := (sq_lt_sq).1 hsq
  rwa [abs_of_nonneg (sqrt_nonneg _), abs_of_pos (by norm_num : (0 : ℝ) < 7 / 4)] at habs

theorem octaEdge_mem_Ioo : octaEdge ∈ Ioo (0 : ℝ) 1 := by
  refine ⟨by unfold octaEdge; positivity, ?_⟩
  unfold octaEdge
  have h2 : sqrt 2 < 2 := by
    have hsq : (sqrt 2) ^ 2 < (2 : ℝ) ^ 2 := by
      rw [sq_sqrt (by norm_num)]
      norm_num
    have habs : |sqrt 2| < |(2 : ℝ)| := (sq_lt_sq).1 hsq
    rwa [abs_of_nonneg (sqrt_nonneg _), abs_of_pos (by norm_num : (0 : ℝ) < 2)] at habs
  nlinarith

theorem octaCoeff_lt_two : octaCoeff < 2 := by
  have h2 : sqrt 2 < 7 / 4 := sqrt_two_lt_seven_quarters
  unfold octaCoeff
  linarith

theorem octaOutward_eq_response {Z x : ℝ}
    (hx : gammaSEqual x ≠ 0) (he : gammaSEqual (octaEdge * x) ≠ 0)
    (hb : gammaSEqual (x / 2) ≠ 0) :
    octaOutward Z x = (octaResponse x - Z) / gammaSEqual x := by
  unfold octaOutward octaResponse scaledRatio
  field_simp [hx, he, hb]
  ring

theorem octaResponse_lt_octaCoeff {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) resonanceRoot1) :
    octaResponse x < octaCoeff := by
  have hedge := octaEdge_mem_Ioo
  have he := scaledRatio_lt_one (c := octaEdge) hedge.1 hedge.2 hx.1 hx.2
  have hb := scaledRatio_lt_one (c := (1 / 2 : ℝ)) (by norm_num) (by norm_num) hx.1 hx.2
  have hcoeff : 0 < sqrt 2 := sqrt_pos.mpr (by norm_num)
  unfold octaResponse octaCoeff
  nlinarith

/-- For every nuclear charge `Z ≥ 2`, six electrons at the vertices of a
regular octahedron have no radial balance in the outer well. -/
theorem octa_no_outer_root {Z x : ℝ} (hZ : 2 ≤ Z) (hx : x ∈ Ioo (0 : ℝ) resonanceRoot1) :
    octaOutward Z x < 0 := by
  have hγ : 0 < gammaSEqual x := gammaSEqual_pos_left_of_first_node hx
  have hedge := octaEdge_mem_Ioo
  have he : gammaSEqual (octaEdge * x) ≠ 0 :=
    (gammaSEqual_pos_of_lt_firstNode (mul_nonneg hedge.1.le hx.1.le)
      (chordPhase_lt_root hedge.2 hx.1 hx.2)).ne'
  have hb : gammaSEqual (x / 2) ≠ 0 :=
    (gammaSEqual_pos_of_lt_firstNode (div_nonneg hx.1.le (by norm_num))
      (halfPhase_lt_root hx.1 hx.2)).ne'
  rw [octaOutward_eq_response hγ.ne' he hb]
  have hresp : octaResponse x < Z := by
    linarith [octaResponse_lt_octaCoeff hx, octaCoeff_lt_two, hZ]
  exact div_neg_of_neg_of_pos (by linarith) hγ

theorem icosaRadius_mem_Ioo : icosaRadius ∈ Ioo (0 : ℝ) 2 := by
  refine ⟨by unfold icosaRadius; positivity, ?_⟩
  have hsq : icosaRadius ^ 2 = (5 + sqrt 5) / 2 := by
    unfold icosaRadius
    exact sq_sqrt (by positivity)
  have h5 : sqrt 5 < 3 := by
    have hpow : (sqrt 5) ^ 2 < (3 : ℝ) ^ 2 := by
      rw [sq_sqrt (by norm_num)]
      norm_num
    have habs : |sqrt 5| < |(3 : ℝ)| := (sq_lt_sq).1 hpow
    rwa [abs_of_nonneg (sqrt_nonneg _), abs_of_pos (by norm_num : (0 : ℝ) < 3)] at habs
  have hlt : icosaRadius ^ 2 < (2 : ℝ) ^ 2 := by
    rw [hsq]
    nlinarith [h5]
  have hnn : 0 ≤ icosaRadius := by unfold icosaRadius; exact sqrt_nonneg _
  rw [← abs_of_nonneg hnn, ← abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  exact (sq_lt_sq).mp hlt

theorem icosaEdge_mem_Ioo : icosaEdge ∈ Ioo (0 : ℝ) 1 := by
  have hR := icosaRadius_mem_Ioo
  unfold icosaEdge
  constructor
  · exact div_pos hR.1 (by norm_num)
  · nlinarith [hR.2]

theorem sqrt_five_gt_one : (1 : ℝ) < sqrt 5 := by
  have hsq : (1 : ℝ) ^ 2 < (sqrt 5) ^ 2 := by
    rw [sq_sqrt (by norm_num)]
    norm_num
  have habs : |(1 : ℝ)| < |sqrt 5| := (sq_lt_sq).1 hsq
  rwa [abs_of_pos (by norm_num : (0 : ℝ) < 1), abs_of_nonneg (sqrt_nonneg _)] at habs

theorem icosaMid_mem_Ioo : icosaMid ∈ Ioo (0 : ℝ) 1 := by
  have hR := icosaRadius_mem_Ioo
  have h5 : 1 < sqrt 5 := sqrt_five_gt_one
  have h5lt : sqrt 5 < 3 := by
    have hpow : (sqrt 5) ^ 2 < (3 : ℝ) ^ 2 := by
      rw [sq_sqrt (by norm_num)]
      norm_num
    have habs : |sqrt 5| < |(3 : ℝ)| := (sq_lt_sq).1 hpow
    rwa [abs_of_nonneg (sqrt_nonneg _), abs_of_pos (by norm_num : (0 : ℝ) < 3)] at habs
  unfold icosaMid
  constructor
  · exact div_pos (mul_pos hR.1 (by linarith)) (by norm_num)
  · nlinarith [hR.2, h5, h5lt]

theorem icosaCoeff_eq :
    icosaCoeff = 5 / 2 * icosaEdge + 5 / 2 * icosaMid + 1 / 4 := by
  have hRsq : icosaRadius ^ 2 = (5 + sqrt 5) / 2 := by
    unfold icosaRadius
    exact sq_sqrt (by positivity)
  have hSsq : (sqrt (5 + 2 * sqrt 5)) ^ 2 = 5 + 2 * sqrt 5 :=
    sq_sqrt (by positivity)
  have hsq_eq : (2 * sqrt (5 + 2 * sqrt 5)) ^ 2 =
      (icosaRadius * (1 + sqrt 5)) ^ 2 := by
    have hL : (2 * sqrt (5 + 2 * sqrt 5)) ^ 2 = 20 + 8 * sqrt 5 := by
      rw [show (2 * sqrt (5 + 2 * sqrt 5)) ^ 2 = 4 * (sqrt (5 + 2 * sqrt 5)) ^ 2 by ring, hSsq]
      ring
    have hφ : (1 + sqrt 5) ^ 2 = 6 + 2 * sqrt 5 := by
      rw [show (1 + sqrt 5) ^ 2 = 1 + 2 * sqrt 5 + (sqrt 5) ^ 2 by ring, sq_sqrt (by norm_num)]
      ring
    have hRight : (icosaRadius * (1 + sqrt 5)) ^ 2 = 20 + 8 * sqrt 5 := by
      calc (icosaRadius * (1 + sqrt 5)) ^ 2
          = icosaRadius ^ 2 * (1 + sqrt 5) ^ 2 := by ring
        _ = (5 + sqrt 5) / 2 * (6 + 2 * sqrt 5) := by rw [hRsq, hφ]
        _ = (5 + sqrt 5) * (3 + sqrt 5) := by ring
        _ = 15 + 8 * sqrt 5 + (sqrt 5) ^ 2 := by ring
        _ = 15 + 8 * sqrt 5 + 5 := by rw [sq_sqrt (by norm_num)]
        _ = 20 + 8 * sqrt 5 := by ring
    linarith
  have hsum_pos : 0 < 2 * sqrt (5 + 2 * sqrt 5) + icosaRadius * (1 + sqrt 5) := by
    have hR : 0 < icosaRadius := icosaRadius_mem_Ioo.1
    positivity
  have hdiff : 2 * sqrt (5 + 2 * sqrt 5) - icosaRadius * (1 + sqrt 5) = 0 := by
    have hfactor : (2 * sqrt (5 + 2 * sqrt 5) - icosaRadius * (1 + sqrt 5)) *
        (2 * sqrt (5 + 2 * sqrt 5) + icosaRadius * (1 + sqrt 5)) =
        (2 * sqrt (5 + 2 * sqrt 5)) ^ 2 - (icosaRadius * (1 + sqrt 5)) ^ 2 := by ring
    have hzero : (2 * sqrt (5 + 2 * sqrt 5)) ^ 2 - (icosaRadius * (1 + sqrt 5)) ^ 2 = 0 := by
      linarith [hsq_eq]
    exact (mul_eq_zero.mp (hfactor.trans hzero)).resolve_right hsum_pos.ne'
  have heq : 2 * sqrt (5 + 2 * sqrt 5) = icosaRadius * (1 + sqrt 5) := by linarith
  have hlin : (5 / 4) * sqrt (5 + 2 * sqrt 5) =
      (5 / 8) * (icosaRadius * (1 + sqrt 5)) := by
    calc (5 / 4) * sqrt (5 + 2 * sqrt 5)
        = (5 / 8) * (2 * sqrt (5 + 2 * sqrt 5)) := by ring
      _ = (5 / 8) * (icosaRadius * (1 + sqrt 5)) := by rw [heq]
  unfold icosaCoeff icosaEdge icosaMid
  calc (5 / 4) * sqrt (5 + 2 * sqrt 5) + 1 / 4
      = (5 / 8) * (icosaRadius * (1 + sqrt 5)) + 1 / 4 := by rw [hlin]
    _ = 5 / 2 * (icosaRadius / 2) + 5 / 2 * (icosaRadius * (sqrt 5 - 1) / 4) + 1 / 4 := by ring

theorem icosaCoeff_lt_five : icosaCoeff < 5 := by
  have h5 : sqrt 5 < 118 / 25 := by
    have hpow : (sqrt 5) ^ 2 < (118 / 25 : ℝ) ^ 2 := by
      rw [sq_sqrt (by norm_num)]
      norm_num
    have habs : |sqrt 5| < |(118 / 25 : ℝ)| := (sq_lt_sq).1 hpow
    rwa [abs_of_nonneg (sqrt_nonneg _), abs_of_pos (by norm_num : (0 : ℝ) < 118 / 25)] at habs
  have hinner : 5 + 2 * sqrt 5 < (19 / 5 : ℝ) ^ 2 := by
    have h19 : (19 / 5 : ℝ) ^ 2 = 361 / 25 := by norm_num
    rw [h19]
    nlinarith [h5]
  have hsqrt : sqrt (5 + 2 * sqrt 5) < 19 / 5 := by
    have hnn := sqrt_nonneg (5 + 2 * sqrt 5)
    rw [← abs_of_nonneg hnn, ← abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 19 / 5)]
    apply (sq_lt_sq).mp
    rw [sq_sqrt (by positivity)]
    exact hinner
  unfold icosaCoeff
  nlinarith [hsqrt]

theorem icosaOutward_eq_response {Z x : ℝ}
    (hx : gammaSEqual x ≠ 0) (he : gammaSEqual (icosaEdge * x) ≠ 0)
    (_hm : gammaSEqual (icosaMid * x) ≠ 0) (hb : gammaSEqual (x / 2) ≠ 0) :
    icosaOutward Z x = (icosaResponse x - Z) / gammaSEqual x := by
  unfold icosaOutward icosaResponse scaledRatio
  field_simp [hx, he, _hm, hb]
  ring

theorem icosaResponse_lt_icosaCoeff {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) resonanceRoot1) :
    icosaResponse x < icosaCoeff := by
  have hedge := icosaEdge_mem_Ioo
  have hmid := icosaMid_mem_Ioo
  have he := scaledRatio_lt_one (c := icosaEdge) hedge.1 hedge.2 hx.1 hx.2
  have hm := scaledRatio_lt_one (c := icosaMid) hmid.1 hmid.2 hx.1 hx.2
  have hb := scaledRatio_lt_one (c := (1 / 2 : ℝ)) (by norm_num) (by norm_num) hx.1 hx.2
  have hE : 0 < 5 / 2 * icosaEdge := by
    have h := icosaEdge_mem_Ioo.1
    positivity
  have hM : 0 < 5 / 2 * icosaMid := by
    have h := icosaMid_mem_Ioo.1
    positivity
  rw [icosaCoeff_eq]
  unfold icosaResponse
  nlinarith

/-- For every nuclear charge `Z ≥ 5`, twelve electrons at the vertices of a
regular icosahedron have no radial balance in the outer well. -/
theorem icosa_no_outer_root {Z x : ℝ} (hZ : 5 ≤ Z) (hx : x ∈ Ioo (0 : ℝ) resonanceRoot1) :
    icosaOutward Z x < 0 := by
  have hγ : 0 < gammaSEqual x := gammaSEqual_pos_left_of_first_node hx
  have hedge := icosaEdge_mem_Ioo
  have hmid := icosaMid_mem_Ioo
  have he : gammaSEqual (icosaEdge * x) ≠ 0 :=
    (gammaSEqual_pos_of_lt_firstNode (mul_nonneg hedge.1.le hx.1.le)
      (chordPhase_lt_root hedge.2 hx.1 hx.2)).ne'
  have hm : gammaSEqual (icosaMid * x) ≠ 0 :=
    (gammaSEqual_pos_of_lt_firstNode (mul_nonneg hmid.1.le hx.1.le)
      (chordPhase_lt_root hmid.2 hx.1 hx.2)).ne'
  have hb : gammaSEqual (x / 2) ≠ 0 :=
    (gammaSEqual_pos_of_lt_firstNode (div_nonneg hx.1.le (by norm_num))
      (halfPhase_lt_root hx.1 hx.2)).ne'
  rw [icosaOutward_eq_response hγ.ne' he hm hb]
  have hresp : icosaResponse x < Z := by
    linarith [icosaResponse_lt_icosaCoeff hx, icosaCoeff_lt_five, hZ]
  exact div_neg_of_neg_of_pos (by linarith) hγ

end Gravity

end DstDiophantine

