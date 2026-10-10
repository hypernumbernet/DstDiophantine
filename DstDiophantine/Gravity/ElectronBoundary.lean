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
Monotonicity of the response on the whole outer interval is not claimed.

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
  the far-field coefficient of its twenty vertices lies strictly between
  `15/2` and `8`. Before that chord meets the first node the response stays
  strictly above `7`, so every nuclear charge `Z ≤ 7` is pushed outward on
  the whole of that interval. For every `Z ≥ 8` the force is inward at large
  separation, and the response passes through `Z` while every pair is still
  outside the first node. For every `Z ≥ 8` it meets the charge exactly once,
  at a radius strictly between `7ℓ/10` and `10ℓ/7`, and the outward force
  restores that radius. The comparison is in `ElectronDodeca`.
* Two electrons whose mutual separation and whose distances to the nucleus all
  lie in the outer well have no force-free placement once the nuclear charge
  is at least `1/4`. On opposite rays the repulsion is strictly less than a
  quarter of the attraction of unit nuclear charge. Distances are in units of `ℓ`.
* Four vertices of a regular tetrahedron, and six of a regular octahedron,
  each have exactly one radial balance in the first repulsive shell for every
  nuclear charge `Z ≥ 1`. The outward force restores that radius. Four and six
  are vertex counts, not seat counts. The icosahedron's reversed-shell root is
  not claimed here.
-/

namespace DstDiophantine

namespace Gravity

open Real Set Filter Finset

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

/-! ### The dodecahedral coefficient lies between 15/2 and 8 -/

private theorem sqrt_five_lt_fiftySix_twentyFifths : sqrt 5 < 56 / 25 := by
  have hsq : (sqrt 5) ^ 2 < (56 / 25 : ℝ) ^ 2 := by
    rw [sq_sqrt (by norm_num)]
    norm_num
  have habs : |sqrt 5| < |(56 / 25 : ℝ)| := (sq_lt_sq).1 hsq
  rwa [abs_of_nonneg (sqrt_nonneg _), abs_of_pos (by norm_num : (0 : ℝ) < 56 / 25)] at habs

private theorem sqrt_five_gt_oneSixSeven_seventyFive : 167 / 75 < sqrt 5 := by
  have hsq : (167 / 75 : ℝ) ^ 2 < (sqrt 5) ^ 2 := by
    rw [sq_sqrt (by norm_num)]
    norm_num
  have habs : |(167 / 75 : ℝ)| < |sqrt 5| := (sq_lt_sq).1 hsq
  rwa [abs_of_pos (by norm_num : (0 : ℝ) < 167 / 75), abs_of_nonneg (sqrt_nonneg _)] at habs

theorem dodecaNear_gt_seven_fifths : 7 / 5 < dodecaNear := by
  have hsq : dodecaNear ^ 2 = 3 * (3 + sqrt 5) / 8 := by
    unfold dodecaNear
    exact sq_sqrt (by nlinarith [sqrt_nonneg (5 : ℝ), sqrt_five_gt_one])
  have hlt : (7 / 5 : ℝ) ^ 2 < dodecaNear ^ 2 := by
    rw [hsq]
    have h5 : 167 / 75 < sqrt 5 := sqrt_five_gt_oneSixSeven_seventyFive
    rw [lt_div_iff₀ (by norm_num)]
    nlinarith
  have hnn : 0 ≤ dodecaNear := by
    unfold dodecaNear
    exact sqrt_nonneg _
  rw [← abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 7 / 5), ← abs_of_nonneg hnn]
  exact (sq_lt_sq).mp hlt

theorem dodecaNear_lt_sevenHundredOne_fiveHundred : dodecaNear < 701 / 500 := by
  have h5 : sqrt 5 < 56 / 25 := sqrt_five_lt_fiftySix_twentyFifths
  have hsq : dodecaNear ^ 2 = 3 * (3 + sqrt 5) / 8 := by
    unfold dodecaNear
    exact sq_sqrt (by nlinarith [sqrt_nonneg (5 : ℝ), h5])
  have hlt : dodecaNear ^ 2 < (701 / 500 : ℝ) ^ 2 := by
    rw [hsq]
    nlinarith [h5]
  have hnn : 0 ≤ dodecaNear := by
    unfold dodecaNear
    exact sqrt_nonneg _
  rw [← abs_of_nonneg hnn, ← abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 701 / 500)]
  exact (sq_lt_sq).mp hlt

private theorem sqrt_three_div_two_gt : 433 / 500 < sqrt 3 / 2 := by
  have h3 : 433 / 250 < sqrt 3 := by
    have hsq : (433 / 250 : ℝ) ^ 2 < (sqrt 3) ^ 2 := by
      rw [sq_sqrt (by norm_num)]
      norm_num
    have habs : |(433 / 250 : ℝ)| < |sqrt 3| := (sq_lt_sq).1 hsq
    rwa [abs_of_pos (by norm_num : (0 : ℝ) < 433 / 250), abs_of_nonneg (sqrt_nonneg _)] at habs
  nlinarith

private theorem sqrt_six_div_four_gt : 61 / 100 < sqrt 6 / 4 := by
  have h6 : 61 / 25 < sqrt 6 := by
    have hsq : (61 / 25 : ℝ) ^ 2 < (sqrt 6) ^ 2 := by
      rw [sq_sqrt (by norm_num)]
      norm_num
    have habs : |(61 / 25 : ℝ)| < |sqrt 6| := (sq_lt_sq).1 hsq
    rwa [abs_of_pos (by norm_num : (0 : ℝ) < 61 / 25), abs_of_nonneg (sqrt_nonneg _)] at habs
  nlinarith

private theorem sqrt_five_lt_nine_quarters : sqrt 5 < 9 / 4 := by
  have hsq : (sqrt 5) ^ 2 < (9 / 4 : ℝ) ^ 2 := by
    rw [sq_sqrt (by norm_num)]
    norm_num
  have habs : |sqrt 5| < |(9 / 4 : ℝ)| := (sq_lt_sq).1 hsq
  rwa [abs_of_nonneg (sqrt_nonneg _), abs_of_pos (by norm_num : (0 : ℝ) < 9 / 4)] at habs

private theorem dodecaFarScale_gt_fiftyThree_hundredths : 53 / 100 < dodecaFarScale := by
  have h5 : sqrt 5 < 9 / 4 := sqrt_five_lt_nine_quarters
  have hsq : dodecaFarScale ^ 2 = 3 * (3 - sqrt 5) / 8 := by
    unfold dodecaFarScale
    exact sq_sqrt (by nlinarith [h5])
  have hlt : (53 / 100 : ℝ) ^ 2 < dodecaFarScale ^ 2 := by
    rw [hsq]
    nlinarith [h5]
  have hnn : 0 ≤ dodecaFarScale := by
    unfold dodecaFarScale
    exact sqrt_nonneg _
  rw [← abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 53 / 100), ← abs_of_nonneg hnn]
  exact (sq_lt_sq).mp hlt

theorem dodecaCoeff_gt_fifteen_halves : 15 / 2 < dodecaCoeff := by
  have hnear : 7 / 5 < dodecaNear := dodecaNear_gt_seven_fifths
  have h3 : 433 / 500 < sqrt 3 / 2 := sqrt_three_div_two_gt
  have h6 : 61 / 100 < sqrt 6 / 4 := sqrt_six_div_four_gt
  have hfar : 53 / 100 < dodecaFarScale := dodecaFarScale_gt_fiftyThree_hundredths
  unfold dodecaCoeff
  nlinarith

/-! ### Polynomial bounds for the interference factor -/

private noncomputable def subSq (y : ℝ) : ℝ := 1 - y ^ 2 - gammaSEqual y

private noncomputable def subSq1 (y : ℝ) : ℝ := 2 * (cosh y * sin y - y)

private noncomputable def subSq2 (y : ℝ) : ℝ :=
  2 * (sinh y * sin y + cosh y * cos y - 1)

private noncomputable def subSq3 (y : ℝ) : ℝ := 4 * (sinh y * cos y)

private theorem hasDerivAt_subSq (y : ℝ) : HasDerivAt subSq (subSq1 y) y := by
  have hpow : HasDerivAt (fun t : ℝ => t ^ 2) (2 * y) y := by
    simpa using hasDerivAt_pow 2 y
  have hpoly := (hasDerivAt_const y (1 : ℝ)).sub hpow
  have h := hpoly.sub (hasDerivAt_gammaSEqual y)
  unfold subSq
  refine h.congr_deriv ?_
  unfold subSq1
  ring

private theorem hasDerivAt_subSq1 (y : ℝ) : HasDerivAt subSq1 (subSq2 y) y := by
  have hmul : HasDerivAt (fun t : ℝ => cosh t * sin t)
      (sinh y * sin y + cosh y * cos y) y :=
    (hasDerivAt_cosh y).mul (hasDerivAt_sin y)
  have hdiff : HasDerivAt (fun t : ℝ => cosh t * sin t - t)
      (sinh y * sin y + cosh y * cos y - 1) y :=
    hmul.sub (hasDerivAt_id' y)
  have h := hdiff.const_mul 2
  unfold subSq1
  refine h.congr_deriv ?_
  unfold subSq2
  ring

private theorem hasDerivAt_subSq2 (y : ℝ) : HasDerivAt subSq2 (subSq3 y) y := by
  have h1 : HasDerivAt (fun t : ℝ => sinh t * sin t)
      (cosh y * sin y + sinh y * cos y) y :=
    (hasDerivAt_sinh y).mul (hasDerivAt_sin y)
  have h2 : HasDerivAt (fun t : ℝ => cosh t * cos t)
      (sinh y * cos y + cosh y * -sin y) y :=
    (hasDerivAt_cosh y).mul (hasDerivAt_cos y)
  have hdiff : HasDerivAt (fun t : ℝ => sinh t * sin t + cosh t * cos t - 1)
      (cosh y * sin y + sinh y * cos y + (sinh y * cos y + cosh y * -sin y) - 0) y :=
    (h1.add h2).sub (hasDerivAt_const y (1 : ℝ))
  have h := hdiff.const_mul 2
  unfold subSq2
  refine h.congr_deriv ?_
  unfold subSq3
  ring

private theorem hasDerivAt_subSq3 (y : ℝ) : HasDerivAt subSq3 (4 * gammaSEqual y) y := by
  have hmul : HasDerivAt (fun t : ℝ => sinh t * cos t)
      (cosh y * cos y + sinh y * -sin y) y :=
    (hasDerivAt_sinh y).mul (hasDerivAt_cos y)
  have h := hmul.const_mul 4
  unfold subSq3
  refine h.congr_deriv ?_
  unfold gammaSEqual
  ring

private theorem segment_strictMono {f f' : ℝ → ℝ} {b : ℝ} (hb : 0 < b)
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

private theorem gammaSEqual_anti_on_first {a b : ℝ}
    (ha : a ∈ Icc (0 : ℝ) π) (hb : b ∈ Icc (0 : ℝ) π) (hab : a < b) :
    gammaSEqual b < gammaSEqual a := by
  have hset : Icc (((2 * 0 : ℕ) : ℝ) * π) (((2 * 0 : ℕ) : ℝ) * π + π) = Icc (0 : ℝ) π := by
    simp
  exact strictAntiOn_gammaSEqual_even 0 (hset.symm ▸ ha) (hset.symm ▸ hb) hab

private theorem gammaSEqual_lt_one_of_pos {y : ℝ} (hy0 : 0 < y) (hy1 : y < resonanceRoot1) :
    gammaSEqual y < 1 := by
  have hπ : y < π :=
    lt_trans hy1 (lt_trans resonanceRoot1_sharp_bounds.2 (by linarith [pi_gt_three]))
  have hlt := gammaSEqual_anti_on_first ⟨le_rfl, pi_pos.le⟩ ⟨hy0.le, hπ.le⟩ hy0
  simpa [gammaSEqual_zero] using hlt

theorem gammaSEqual_lt_sub_sq {y : ℝ} (hy0 : 0 < y) (hy1 : y < resonanceRoot1) :
    gammaSEqual y < 1 - y ^ 2 := by
  have hγ : ∀ t ∈ Ioo (0 : ℝ) y, 0 < gammaSEqual t := by
    intro t ht
    exact gammaSEqual_pos_of_lt_firstNode ht.1.le (lt_trans ht.2 hy1)
  have h3pos : ∀ t ∈ Ioo (0 : ℝ) y, 0 < 4 * gammaSEqual t := by
    intro t ht
    exact mul_pos (by norm_num) (hγ t ht)
  have hcont3 : ContinuousOn subSq3 (Icc 0 y) := by
    unfold subSq3
    exact (by continuity : Continuous fun t : ℝ => 4 * (sinh t * cos t)).continuousOn
  have h3 := segment_pos hy0 (by unfold subSq3; simp) hcont3 (fun t ht => hasDerivAt_subSq3 t) h3pos
  have h2pos : ∀ t ∈ Ioo (0 : ℝ) y, 0 < subSq3 t := by
    intro t ht
    have hmono : StrictMonoOn subSq3 (Icc 0 y) :=
      segment_strictMono hy0 hcont3 (fun s hs => hasDerivAt_subSq3 s) h3pos
    have hlt := hmono (by simp [hy0.le]) ⟨ht.1.le, ht.2.le⟩ ht.1
    simpa [subSq3] using hlt
  have hcont2 : ContinuousOn subSq2 (Icc 0 y) := by
    unfold subSq2
    exact (by continuity :
      Continuous fun t : ℝ => 2 * (sinh t * sin t + cosh t * cos t - 1)).continuousOn
  have h2 := segment_pos hy0 (by unfold subSq2; simp) hcont2 (fun t ht => hasDerivAt_subSq2 t) h2pos
  have h1pos : ∀ t ∈ Ioo (0 : ℝ) y, 0 < subSq2 t := by
    intro t ht
    have hmono : StrictMonoOn subSq2 (Icc 0 y) :=
      segment_strictMono hy0 hcont2 (fun s hs => hasDerivAt_subSq2 s) h2pos
    have hlt := hmono (by simp [hy0.le]) ⟨ht.1.le, ht.2.le⟩ ht.1
    simpa [subSq2] using hlt
  have hcont1 : ContinuousOn subSq1 (Icc 0 y) := by
    unfold subSq1
    exact (by continuity : Continuous fun t : ℝ => 2 * (cosh t * sin t - t)).continuousOn
  have h1 := segment_pos hy0 (by unfold subSq1; simp) hcont1 (fun t ht => hasDerivAt_subSq1 t) h1pos
  have h0pos : ∀ t ∈ Ioo (0 : ℝ) y, 0 < subSq1 t := by
    intro t ht
    have hmono : StrictMonoOn subSq1 (Icc 0 y) :=
      segment_strictMono hy0 hcont1 (fun s hs => hasDerivAt_subSq1 s) h1pos
    have hlt := hmono (by simp [hy0.le]) ⟨ht.1.le, ht.2.le⟩ ht.1
    simpa [subSq1] using hlt
  have hcont0 : ContinuousOn subSq (Icc 0 y) := by
    unfold subSq
    exact ((continuous_const.sub (continuous_pow 2)).sub continuous_gammaSEqual).continuousOn
  have h0 := segment_pos hy0 (by unfold subSq; simp [gammaSEqual_zero]) hcont0
    (fun t ht => hasDerivAt_subSq t) h0pos
  simpa [subSq] using h0

private noncomputable def lowPoly (y : ℝ) : ℝ :=
  gammaSEqual y - (1 - y ^ 2 - y ^ 4 / 6)

private noncomputable def lowPoly1 (y : ℝ) : ℝ :=
  -2 * (cosh y * sin y) + 2 * y + (2 / 3) * y ^ 3

private noncomputable def lowPoly2 (y : ℝ) : ℝ :=
  2 * (1 + y ^ 2 - sinh y * sin y - cosh y * cos y)

private noncomputable def lowPoly3 (y : ℝ) : ℝ := 4 * (y - sinh y * cos y)

private theorem hasDerivAt_lowPoly (y : ℝ) : HasDerivAt lowPoly (lowPoly1 y) y := by
  have hsq : HasDerivAt (fun t : ℝ => t ^ 2) (2 * y) y := by
    simpa using hasDerivAt_pow 2 y
  have h4 : HasDerivAt (fun t : ℝ => t ^ 4 / 6) (4 * y ^ 3 / 6) y := by
    simpa using (hasDerivAt_pow 4 y).div_const 6
  have hinside := ((hasDerivAt_const y (1 : ℝ)).sub hsq).sub h4
  have h := (hasDerivAt_gammaSEqual y).sub hinside
  unfold lowPoly
  refine h.congr_deriv ?_
  unfold lowPoly1
  ring

private theorem hasDerivAt_lowPoly1 (y : ℝ) : HasDerivAt lowPoly1 (lowPoly2 y) y := by
  have hmul : HasDerivAt (fun t : ℝ => -2 * (cosh t * sin t))
      (-2 * (sinh y * sin y + cosh y * cos y)) y :=
    ((hasDerivAt_cosh y).mul (hasDerivAt_sin y)).const_mul (-2)
  have hy : HasDerivAt (fun t : ℝ => 2 * t) (2 * 1) y := (hasDerivAt_id' y).const_mul 2
  have hcube : HasDerivAt (fun t : ℝ => (2 / 3) * t ^ 3) ((2 / 3) * (3 * y ^ 2)) y := by
    simpa using (hasDerivAt_pow 3 y).const_mul (2 / 3)
  have h := (hmul.add hy).add hcube
  unfold lowPoly1
  refine h.congr_deriv ?_
  unfold lowPoly2
  ring

private theorem hasDerivAt_lowPoly2 (y : ℝ) : HasDerivAt lowPoly2 (lowPoly3 y) y := by
  have hpow : HasDerivAt (fun t : ℝ => t ^ 2) (2 * y) y := by
    simpa using hasDerivAt_pow 2 y
  have h1 := (hasDerivAt_const y (1 : ℝ)).add hpow
  have h2 : HasDerivAt (fun t : ℝ => sinh t * sin t)
      (cosh y * sin y + sinh y * cos y) y :=
    (hasDerivAt_sinh y).mul (hasDerivAt_sin y)
  have h3 : HasDerivAt (fun t : ℝ => cosh t * cos t)
      (sinh y * cos y + cosh y * -sin y) y :=
    (hasDerivAt_cosh y).mul (hasDerivAt_cos y)
  have h := ((h1.sub h2).sub h3).const_mul 2
  unfold lowPoly2
  refine h.congr_deriv ?_
  unfold lowPoly3
  ring

private theorem hasDerivAt_lowPoly3 (y : ℝ) : HasDerivAt lowPoly3 (4 * (1 - gammaSEqual y)) y := by
  have hmul : HasDerivAt (fun t : ℝ => sinh t * cos t)
      (cosh y * cos y + sinh y * -sin y) y :=
    (hasDerivAt_sinh y).mul (hasDerivAt_cos y)
  have h := ((hasDerivAt_id' y).sub hmul).const_mul 4
  unfold lowPoly3
  refine h.congr_deriv ?_
  unfold gammaSEqual
  ring

theorem gammaSEqual_gt_lowerPoly {y : ℝ} (hy0 : 0 < y) (hy1 : y < resonanceRoot1) :
    1 - y ^ 2 - y ^ 4 / 6 < gammaSEqual y := by
  have hgap : ∀ t ∈ Ioo (0 : ℝ) y, 0 < 1 - gammaSEqual t := by
    intro t ht
    exact sub_pos.mpr (gammaSEqual_lt_one_of_pos ht.1 (lt_trans ht.2 hy1))
  have h3pos : ∀ t ∈ Ioo (0 : ℝ) y, 0 < 4 * (1 - gammaSEqual t) := by
    intro t ht
    exact mul_pos (by norm_num) (hgap t ht)
  have hcont3 : ContinuousOn lowPoly3 (Icc 0 y) := by
    unfold lowPoly3
    exact (by continuity : Continuous fun t : ℝ => 4 * (t - sinh t * cos t)).continuousOn
  have h3 := segment_pos hy0 (by unfold lowPoly3; simp) hcont3
    (fun t ht => hasDerivAt_lowPoly3 t) h3pos
  have h2pos : ∀ t ∈ Ioo (0 : ℝ) y, 0 < lowPoly3 t := by
    intro t ht
    have hmono := segment_strictMono hy0 hcont3 (fun s hs => hasDerivAt_lowPoly3 s) h3pos
    have hlt := hmono (by simp [hy0.le]) ⟨ht.1.le, ht.2.le⟩ ht.1
    simpa [lowPoly3] using hlt
  have hcont2 : ContinuousOn lowPoly2 (Icc 0 y) := by
    unfold lowPoly2
    exact (by continuity : Continuous fun t : ℝ =>
      2 * (1 + t ^ 2 - sinh t * sin t - cosh t * cos t)).continuousOn
  have h2 := segment_pos hy0 (by unfold lowPoly2; simp) hcont2
    (fun t ht => hasDerivAt_lowPoly2 t) h2pos
  have h1pos : ∀ t ∈ Ioo (0 : ℝ) y, 0 < lowPoly2 t := by
    intro t ht
    have hmono := segment_strictMono hy0 hcont2 (fun s hs => hasDerivAt_lowPoly2 s) h2pos
    have hlt := hmono (by simp [hy0.le]) ⟨ht.1.le, ht.2.le⟩ ht.1
    simpa [lowPoly2] using hlt
  have hcont1 : ContinuousOn lowPoly1 (Icc 0 y) := by
    unfold lowPoly1
    exact (by continuity : Continuous fun t : ℝ =>
      -2 * (cosh t * sin t) + 2 * t + (2 / 3) * t ^ 3).continuousOn
  have h1 := segment_pos hy0 (by unfold lowPoly1; simp) hcont1
    (fun t ht => hasDerivAt_lowPoly1 t) h1pos
  have h0pos : ∀ t ∈ Ioo (0 : ℝ) y, 0 < lowPoly1 t := by
    intro t ht
    have hmono := segment_strictMono hy0 hcont1 (fun s hs => hasDerivAt_lowPoly1 s) h1pos
    have hlt := hmono (by simp [hy0.le]) ⟨ht.1.le, ht.2.le⟩ ht.1
    simpa [lowPoly1] using hlt
  have hcont0 : ContinuousOn lowPoly (Icc 0 y) := by
    unfold lowPoly
    exact (continuous_gammaSEqual.sub
      ((continuous_const.sub (continuous_pow 2)).sub ((continuous_pow 4).div_const 6))).continuousOn
  have h0 := segment_pos hy0 (by unfold lowPoly; simp [gammaSEqual_zero]) hcont0
    (fun t ht => hasDerivAt_lowPoly t) h0pos
  simpa [lowPoly] using h0

/-! ### Sine upper bound and cosine lower bound on `(0, π)` -/

private noncomputable def sinGap (y : ℝ) : ℝ := y - y ^ 3 / 6 + y ^ 5 / 120 - sin y

private noncomputable def sinGap1 (y : ℝ) : ℝ := 1 - y ^ 2 / 2 + y ^ 4 / 24 - cos y

private noncomputable def sinGap2 (y : ℝ) : ℝ := -y + y ^ 3 / 6 + sin y

private noncomputable def sinGap3 (y : ℝ) : ℝ := -1 + y ^ 2 / 2 + cos y

private noncomputable def sinGap4 (y : ℝ) : ℝ := y - sin y

private theorem hasDerivAt_sinGap (y : ℝ) : HasDerivAt sinGap (sinGap1 y) y := by
  have h3 : HasDerivAt (fun t : ℝ => t ^ 3 / 6) (3 * y ^ 2 / 6) y := by
    simpa using (hasDerivAt_pow 3 y).div_const 6
  have h5 : HasDerivAt (fun t : ℝ => t ^ 5 / 120) (5 * y ^ 4 / 120) y := by
    simpa using (hasDerivAt_pow 5 y).div_const 120
  have h := (((hasDerivAt_id' y).sub h3).add h5).sub (hasDerivAt_sin y)
  unfold sinGap
  refine h.congr_deriv ?_
  unfold sinGap1
  ring

private theorem hasDerivAt_sinGap1 (y : ℝ) : HasDerivAt sinGap1 (sinGap2 y) y := by
  have h2 : HasDerivAt (fun t : ℝ => t ^ 2 / 2) (2 * y / 2) y := by
    simpa using (hasDerivAt_pow 2 y).div_const 2
  have h4 : HasDerivAt (fun t : ℝ => t ^ 4 / 24) (4 * y ^ 3 / 24) y := by
    simpa using (hasDerivAt_pow 4 y).div_const 24
  have h := (((hasDerivAt_const y (1 : ℝ)).sub h2).add h4).sub (hasDerivAt_cos y)
  unfold sinGap1
  refine h.congr_deriv ?_
  unfold sinGap2
  ring

private theorem hasDerivAt_sinGap2 (y : ℝ) : HasDerivAt sinGap2 (sinGap3 y) y := by
  have h3 : HasDerivAt (fun t : ℝ => t ^ 3 / 6) (3 * y ^ 2 / 6) y := by
    simpa using (hasDerivAt_pow 3 y).div_const 6
  have h := (((hasDerivAt_id' y).neg.add h3).add (hasDerivAt_sin y))
  unfold sinGap2
  refine h.congr_deriv ?_
  unfold sinGap3
  ring

private theorem hasDerivAt_sinGap3 (y : ℝ) : HasDerivAt sinGap3 (sinGap4 y) y := by
  have h2 : HasDerivAt (fun t : ℝ => t ^ 2 / 2) (2 * y / 2) y := by
    simpa using (hasDerivAt_pow 2 y).div_const 2
  have h := ((hasDerivAt_const y (-1 : ℝ)).add h2).add (hasDerivAt_cos y)
  unfold sinGap3
  refine h.congr_deriv ?_
  unfold sinGap4
  ring

private theorem hasDerivAt_sinGap4 (y : ℝ) : HasDerivAt sinGap4 (1 - cos y) y := by
  have h := (hasDerivAt_id' y).sub (hasDerivAt_sin y)
  unfold sinGap4
  refine h.congr_deriv ?_
  ring

private theorem sin_lt_poly {y : ℝ} (hy0 : 0 < y) (hyπ : y < π) :
    sin y < y - y ^ 3 / 6 + y ^ 5 / 120 := by
  have h4pos : ∀ t ∈ Ioo (0 : ℝ) y, 0 < 1 - cos t := by
    intro t ht
    have htπ : t < π := lt_trans ht.2 hyπ
    exact sub_pos.mpr <| by
      simpa using cos_lt_cos_of_nonneg_of_le_pi (le_refl (0 : ℝ)) htπ.le ht.1
  have hcont4 : ContinuousOn sinGap4 (Icc 0 y) := by
    unfold sinGap4
    exact (continuous_id.sub continuous_sin).continuousOn
  have h4 := segment_pos hy0 (by unfold sinGap4; simp) hcont4
    (fun t _ => hasDerivAt_sinGap4 t) h4pos
  have h3pos : ∀ t ∈ Ioo (0 : ℝ) y, 0 < sinGap4 t := by
    intro t ht
    have hmono := segment_strictMono hy0 hcont4 (fun s _ => hasDerivAt_sinGap4 s) h4pos
    have hlt := hmono (by simp [hy0.le]) ⟨ht.1.le, ht.2.le⟩ ht.1
    simpa [sinGap4] using hlt
  have hcont3 : ContinuousOn sinGap3 (Icc 0 y) := by
    unfold sinGap3
    exact ((continuous_const.add ((continuous_pow 2).div_const 2)).add continuous_cos).continuousOn
  have h3 := segment_pos hy0 (by unfold sinGap3; simp) hcont3
    (fun t _ => hasDerivAt_sinGap3 t) h3pos
  have h2pos : ∀ t ∈ Ioo (0 : ℝ) y, 0 < sinGap3 t := by
    intro t ht
    have hmono := segment_strictMono hy0 hcont3 (fun s _ => hasDerivAt_sinGap3 s) h3pos
    have hlt := hmono (by simp [hy0.le]) ⟨ht.1.le, ht.2.le⟩ ht.1
    simpa [sinGap3] using hlt
  have hcont2 : ContinuousOn sinGap2 (Icc 0 y) := by
    unfold sinGap2
    exact ((continuous_id.neg.add ((continuous_pow 3).div_const 6)).add continuous_sin).continuousOn
  have h2 := segment_pos hy0 (by unfold sinGap2; simp) hcont2
    (fun t _ => hasDerivAt_sinGap2 t) h2pos
  have h1pos : ∀ t ∈ Ioo (0 : ℝ) y, 0 < sinGap2 t := by
    intro t ht
    have hmono := segment_strictMono hy0 hcont2 (fun s _ => hasDerivAt_sinGap2 s) h2pos
    have hlt := hmono (by simp [hy0.le]) ⟨ht.1.le, ht.2.le⟩ ht.1
    simpa [sinGap2] using hlt
  have hcont1 : ContinuousOn sinGap1 (Icc 0 y) := by
    unfold sinGap1
    exact (((continuous_const.sub ((continuous_pow 2).div_const 2)).add
      ((continuous_pow 4).div_const 24)).sub continuous_cos).continuousOn
  have h1 := segment_pos hy0 (by unfold sinGap1; simp) hcont1
    (fun t _ => hasDerivAt_sinGap1 t) h1pos
  have h0pos : ∀ t ∈ Ioo (0 : ℝ) y, 0 < sinGap1 t := by
    intro t ht
    have hmono := segment_strictMono hy0 hcont1 (fun s _ => hasDerivAt_sinGap1 s) h1pos
    have hlt := hmono (by simp [hy0.le]) ⟨ht.1.le, ht.2.le⟩ ht.1
    simpa [sinGap1] using hlt
  have hcont0 : ContinuousOn sinGap (Icc 0 y) := by
    unfold sinGap
    exact (((continuous_id.sub ((continuous_pow 3).div_const 6)).add
      ((continuous_pow 5).div_const 120)).sub continuous_sin).continuousOn
  have h0 := segment_pos hy0 (by unfold sinGap; simp) hcont0
    (fun t _ => hasDerivAt_sinGap t) h0pos
  simpa [sinGap] using h0

private theorem cos_gt_poly {y : ℝ} (hy0 : 0 < y) (hyπ : y < π) :
    1 - y ^ 2 / 2 + y ^ 4 / 24 - y ^ 6 / 720 < cos y := by
  have hsin : ∀ t ∈ Ioo (0 : ℝ) y, 0 < sinGap t := by
    intro t ht
    have hlt := sin_lt_poly ht.1 (lt_trans ht.2 hyπ)
    simpa [sinGap] using hlt
  let f : ℝ → ℝ := fun t => cos t - (1 - t ^ 2 / 2 + t ^ 4 / 24 - t ^ 6 / 720)
  have hderiv : ∀ t ∈ Ioo (0 : ℝ) y, HasDerivAt f (sinGap t) t := by
    intro t ht
    have h2 : HasDerivAt (fun s : ℝ => s ^ 2 / 2) (2 * t / 2) t := by
      simpa using (hasDerivAt_pow 2 t).div_const 2
    have h4 : HasDerivAt (fun s : ℝ => s ^ 4 / 24) (4 * t ^ 3 / 24) t := by
      simpa using (hasDerivAt_pow 4 t).div_const 24
    have h6 : HasDerivAt (fun s : ℝ => s ^ 6 / 720) (6 * t ^ 5 / 720) t := by
      simpa using (hasDerivAt_pow 6 t).div_const 720
    have hpoly := (((hasDerivAt_const t (1 : ℝ)).sub h2).add h4).sub h6
    have h := (hasDerivAt_cos t).sub hpoly
    refine h.congr_deriv ?_
    unfold sinGap
    ring
  have hcont : ContinuousOn f (Icc 0 y) := by
    have hpoly : Continuous (fun t : ℝ => 1 - t ^ 2 / 2 + t ^ 4 / 24 - t ^ 6 / 720) :=
      (((continuous_const.sub ((continuous_pow 2).div_const 2)).add
        ((continuous_pow 4).div_const 24)).sub ((continuous_pow 6).div_const 720))
    exact (continuous_cos.sub hpoly).continuousOn
  have h0 := segment_pos hy0 (by simp [f]) hcont hderiv hsin
  simpa [f] using h0

/-! ### The first node lies beyond 93/100 -/

private theorem exp_ninetyThree_hundredths_lt : exp (93 / 100) < 2535 / 1000 := by
  exact (exp_between (x := 93 / 100) (lo := 0) (hi := 2535 / 1000) (n := 8)
    (by norm_num) (by norm_num) (by decide)
    (by norm_num [sum_range_succ, Nat.factorial])
    (by norm_num [sum_range_succ, Nat.factorial])).2

private theorem tanh_exp_ratio (x : ℝ) :
    tanh x = (exp (2 * x) - 1) / (exp (2 * x) + 1) := by
  rw [tanh_eq x]
  have hx : exp x ≠ 0 := (exp_pos x).ne'
  have hden : exp x + exp (-x) ≠ 0 := (add_pos (exp_pos x) (exp_pos (-x))).ne'
  have hden' : exp (2 * x) + 1 ≠ 0 :=
    (add_pos_of_pos_of_nonneg (exp_pos _) (by norm_num : (0 : ℝ) ≤ 1)).ne'
  have h2 : exp (2 * x) = exp x * exp x := by
    rw [← exp_add]
    congr 1
    ring
  have h1 : (1 : ℝ) = exp (-x) * exp x := by
    rw [← exp_zero, ← exp_add]
    congr 1
    ring
  refine (div_eq_div_iff hden hden').mpr ?_
  rw [h2, h1]
  ring

private theorem resonanceProd_ninetyThree_hundredths_lt_one :
    resonanceProd (93 / 100) < 1 := by
  have hy0 : (0 : ℝ) < 93 / 100 := by norm_num
  have hyπ : (93 / 100 : ℝ) < π := by linarith [pi_gt_three]
  have hsin := sin_lt_poly hy0 hyπ
  have hcos := cos_gt_poly hy0 hyπ
  have hcospos : 0 < 1 - (93 / 100 : ℝ) ^ 2 / 2 + (93 / 100) ^ 4 / 24 -
      (93 / 100) ^ 6 / 720 := by norm_num
  have htan : tan (93 / 100) <
      ((93 / 100 : ℝ) - (93 / 100) ^ 3 / 6 + (93 / 100) ^ 5 / 120) /
        (1 - (93 / 100) ^ 2 / 2 + (93 / 100) ^ 4 / 24 - (93 / 100) ^ 6 / 720) := by
    rw [tan_eq_sin_div_cos]
    have hcos_pos : 0 < cos (93 / 100) := lt_trans hcospos hcos
    rw [div_lt_div_iff₀ hcos_pos (by linarith)]
    have hsinpos : 0 < sin (93 / 100) := sin_pos_of_pos_of_lt_pi hy0 hyπ
    nlinarith
  have hexp := exp_ninetyThree_hundredths_lt
  have h2 : exp (2 * (93 / 100 : ℝ)) < (2535 / 1000) ^ 2 := by
    have hpos : 0 < exp (93 / 100) := exp_pos _
    have hmul : exp (93 / 100) * exp (93 / 100) < (2535 / 1000) * (2535 / 1000) :=
      mul_lt_mul hexp hexp.le hpos (by norm_num)
    have hsum : exp (93 / 100) * exp (93 / 100) = exp (2 * (93 / 100)) := by
      rw [← exp_add]
      congr 1
      ring
    rw [← hsum, pow_two]
    exact hmul
  have htanh : tanh (93 / 100) <
      ((2535 / 1000 : ℝ) ^ 2 - 1) / ((2535 / 1000) ^ 2 + 1) := by
    rw [tanh_exp_ratio]
    have hden : 0 < exp (2 * (93 / 100 : ℝ)) + 1 := by positivity
    have hden' : 0 < (2535 / 1000 : ℝ) ^ 2 + 1 := by positivity
    have hinc : (exp (2 * (93 / 100 : ℝ)) - 1) / (exp (2 * (93 / 100 : ℝ)) + 1) <
        ((2535 / 1000 : ℝ) ^ 2 - 1) / ((2535 / 1000) ^ 2 + 1) := by
      rw [div_lt_div_iff₀ hden hden']
      nlinarith [h2]
    exact hinc
  have hprod : tan (93 / 100) * tanh (93 / 100) <
      (((93 / 100 : ℝ) - (93 / 100) ^ 3 / 6 + (93 / 100) ^ 5 / 120) /
        (1 - (93 / 100) ^ 2 / 2 + (93 / 100) ^ 4 / 24 - (93 / 100) ^ 6 / 720)) *
      (((2535 / 1000 : ℝ) ^ 2 - 1) / ((2535 / 1000) ^ 2 + 1)) := by
    have htanh_pos : 0 < tanh (93 / 100) := by
      rw [tanh_eq_sinh_div_cosh]
      exact div_pos (sinh_pos_iff.mpr hy0) (cosh_pos _)
    exact mul_lt_mul htan htanh.le htanh_pos (by positivity)
  have hnum : (((93 / 100 : ℝ) - (93 / 100) ^ 3 / 6 + (93 / 100) ^ 5 / 120) /
      (1 - (93 / 100) ^ 2 / 2 + (93 / 100) ^ 4 / 24 - (93 / 100) ^ 6 / 720)) *
      (((2535 / 1000 : ℝ) ^ 2 - 1) / ((2535 / 1000) ^ 2 + 1)) < 1 := by
    norm_num
  unfold resonanceProd
  rw [mul_comm]
  exact hprod.trans hnum

theorem ninetyThree_hundredths_lt_resonanceRoot1 : 93 / 100 < resonanceRoot1 := by
  have hprod := resonanceProd_ninetyThree_hundredths_lt_one
  by_contra h
  have hle : resonanceRoot1 ≤ 93 / 100 := le_of_not_gt h
  have hmem : (93 / 100 : ℝ) ∈ Ioo (0 : ℝ) (π / 2) := by
    refine ⟨by norm_num, ?_⟩
    linarith [pi_gt_three]
  have hroot : resonanceRoot1 ∈ Ioo (0 : ℝ) (π / 2) := by
    refine ⟨lt_trans (by norm_num) resonanceRoot1_bounds.1, ?_⟩
    linarith [resonanceRoot1_sharp_bounds.2, pi_gt_three]
  rcases lt_or_eq_of_le hle with hlt | heq
  · have hmono := strictMonoOn_resonanceProd hroot hmem hlt
    rw [resonanceRoot1_prod] at hmono
    exact lt_irrefl _ (hprod.trans hmono)
  · rw [← heq, resonanceRoot1_prod] at hprod
    exact lt_irrefl _ hprod

theorem dodecaWall_gt_thirtyThree_fiftieths : 33 / 50 < dodecaWall := by
  have hnear : dodecaNear < 701 / 500 := dodecaNear_lt_sevenHundredOne_fiveHundred
  have hx1 : 93 / 100 < resonanceRoot1 := ninetyThree_hundredths_lt_resonanceRoot1
  have hmul : dodecaNear * (33 / 50) < resonanceRoot1 := by
    have hcmp : (701 / 500 : ℝ) * (33 / 50) < 93 / 100 := by norm_num
    have hpos : (0 : ℝ) < 33 / 50 := by norm_num
    have hlt : dodecaNear * (33 / 50) < (701 / 500) * (33 / 50) :=
      mul_lt_mul_of_pos_right hnear hpos
    linarith
  unfold dodecaWall
  rw [lt_div_iff₀ (by linarith [dodecaNear_gt_one])]
  simpa [mul_comm] using hmul

/-! ### Monotonicity of a chord ratio -/

noncomputable def chordSlope (t : ℝ) : ℝ :=
  gammaSEqual t / (cosh t * sin t)

theorem chordSlope_pos {t : ℝ} (ht0 : 0 < t) (ht1 : t < resonanceRoot1) :
    0 < chordSlope t := by
  have hπ : t < π :=
    lt_trans ht1 (lt_trans resonanceRoot1_sharp_bounds.2 (by linarith [pi_gt_three]))
  have hγ : 0 < gammaSEqual t := gammaSEqual_pos_of_lt_firstNode ht0.le ht1
  have hden : 0 < cosh t * sin t := mul_pos (cosh_pos t) (sin_pos_of_pos_of_lt_pi ht0 hπ)
  unfold chordSlope
  exact div_pos hγ hden

private theorem hasDerivAt_chordSlope {t : ℝ} (ht0 : 0 < t) (htπ : t < π) :
    HasDerivAt chordSlope
      ((-2 * (cosh t * sin t) ^ 2 -
          gammaSEqual t * (sinh t * sin t + cosh t * cos t)) /
        (cosh t * sin t) ^ 2) t := by
  have hden_ne : cosh t * sin t ≠ 0 :=
    mul_ne_zero (cosh_pos t).ne' (sin_pos_of_pos_of_lt_pi ht0 htπ).ne'
  have hden : HasDerivAt (fun s : ℝ => cosh s * sin s)
      (sinh t * sin t + cosh t * cos t) t :=
    (hasDerivAt_cosh t).mul (hasDerivAt_sin t)
  have hdiv := (hasDerivAt_gammaSEqual t).div hden hden_ne
  unfold chordSlope
  refine hdiv.congr_deriv ?_
  ring

theorem strictAntiOn_chordSlope :
    StrictAntiOn chordSlope (Ioo (0 : ℝ) resonanceRoot1) := by
  refine strictAntiOn_of_deriv_neg (convex_Ioo 0 resonanceRoot1) ?_ ?_
  · refine ContinuousOn.div continuous_gammaSEqual.continuousOn
      ((continuous_cosh.mul continuous_sin).continuousOn) ?_
    intro t ht
    have hπ : t < π :=
      lt_trans ht.2 (lt_trans resonanceRoot1_sharp_bounds.2 (by linarith [pi_gt_three]))
    exact mul_ne_zero (cosh_pos t).ne' (sin_pos_of_pos_of_lt_pi ht.1 hπ).ne'
  · intro t ht
    rw [interior_Ioo] at ht
    have hπ : t < π :=
      lt_trans ht.2 (lt_trans resonanceRoot1_sharp_bounds.2 (by linarith [pi_gt_three]))
    rw [(hasDerivAt_chordSlope ht.1 hπ).deriv]
    have hden : 0 < (cosh t * sin t) ^ 2 := by
      exact sq_pos_of_pos (mul_pos (cosh_pos t) (sin_pos_of_pos_of_lt_pi ht.1 hπ))
    have hnum : -2 * (cosh t * sin t) ^ 2 -
        gammaSEqual t * (sinh t * sin t + cosh t * cos t) < 0 := by
      have hsq : 0 < (cosh t * sin t) ^ 2 := hden
      have hγ : 0 < gammaSEqual t := gammaSEqual_pos_of_lt_firstNode ht.1.le ht.2
      have hrest : 0 < sinh t * sin t + cosh t * cos t := by
        have hsinh : 0 < sinh t := sinh_pos_iff.mpr ht.1
        have hsin : 0 < sin t := sin_pos_of_pos_of_lt_pi ht.1 hπ
        have hhalf : t < π / 2 :=
          lt_trans ht.2 (lt_trans resonanceRoot1_sharp_bounds.2 (by linarith [pi_gt_three]))
        have hcos : 0 < cos t :=
          cos_pos_of_mem_Ioo ⟨lt_trans (neg_lt_zero.mpr (half_pos pi_pos)) ht.1, hhalf⟩
        positivity
      nlinarith
    exact div_neg_of_neg_of_pos hnum hden

theorem scaledRatio_numer_eq {c x : ℝ} (hx0 : 0 < x) (hcx0 : 0 < c * x)
    (hπx : x < π) (hπc : c * x < π) :
    deriv gammaSEqual x * gammaSEqual (c * x) -
        gammaSEqual x * (deriv gammaSEqual (c * x) * c) =
      2 * (cosh x * sin x) * (cosh (c * x) * sin (c * x)) *
        (c * chordSlope x - chordSlope (c * x)) := by
  rw [deriv_gammaSEqual, deriv_gammaSEqual]
  unfold chordSlope
  set a := cosh x * sin x
  set b := cosh (c * x) * sin (c * x)
  have ha : a ≠ 0 :=
    mul_ne_zero (cosh_pos x).ne' (sin_pos_of_pos_of_lt_pi hx0 hπx).ne'
  have hb : b ≠ 0 :=
    mul_ne_zero (cosh_pos _).ne' (sin_pos_of_pos_of_lt_pi hcx0 hπc).ne'
  field_simp [ha, hb]
  ring

private theorem scaledRatio_strictMono_of_gt_one {c : ℝ} (hc : 1 < c) :
    StrictMonoOn (scaledRatio c) (Ioo (0 : ℝ) (resonanceRoot1 / c)) := by
  refine strictMonoOn_of_deriv_pos (convex_Ioo 0 (resonanceRoot1 / c)) ?_ ?_
  · refine ContinuousOn.div continuous_gammaSEqual.continuousOn
      ((continuous_gammaSEqual.comp (continuous_const.mul continuous_id)).continuousOn) ?_
    intro x hx
    have hcpos : 0 < c := by linarith
    have hcx : c * x < resonanceRoot1 := by
      have hx' : x < resonanceRoot1 / c := hx.2
      rw [lt_div_iff₀ hcpos] at hx'
      simpa [mul_comm] using hx'
    exact (gammaSEqual_pos_of_lt_firstNode (mul_nonneg hcpos.le hx.1.le) hcx).ne'
  · intro x hx
    rw [interior_Ioo] at hx
    have hcpos : 0 < c := by linarith
    have hcx : c * x < resonanceRoot1 := by
      have hx' : x < resonanceRoot1 / c := hx.2
      rw [lt_div_iff₀ hcpos] at hx'
      simpa [mul_comm] using hx'
    have hxc : x < c * x := by nlinarith [hc, hx.1]
    have hx1 : x < resonanceRoot1 := lt_trans hxc hcx
    have hπx : x < π :=
      lt_trans hx1 (lt_trans resonanceRoot1_sharp_bounds.2 (by linarith [pi_gt_three]))
    have hπc : c * x < π :=
      lt_trans hcx (lt_trans resonanceRoot1_sharp_bounds.2 (by linarith [pi_gt_three]))
    have hden_pos : 0 < gammaSEqual (c * x) :=
      gammaSEqual_pos_of_lt_firstNode (mul_nonneg hcpos.le hx.1.le) hcx
    rw [(hasDerivAt_scaledRatio hden_pos.ne').deriv]
    have hbracket : 0 < c * chordSlope x - chordSlope (c * x) := by
      have hxmem : x ∈ Ioo (0 : ℝ) resonanceRoot1 := ⟨hx.1, hx1⟩
      have hcmem : c * x ∈ Ioo (0 : ℝ) resonanceRoot1 := ⟨mul_pos hcpos hx.1, hcx⟩
      have hlt : chordSlope (c * x) < chordSlope x :=
        strictAntiOn_chordSlope hxmem hcmem hxc
      have hpos := chordSlope_pos hx.1 hx1
      nlinarith
    have hfactor : 0 < 2 * (cosh x * sin x) * (cosh (c * x) * sin (c * x)) := by
      exact mul_pos
        (mul_pos (by norm_num) (mul_pos (cosh_pos x) (sin_pos_of_pos_of_lt_pi hx.1 hπx)))
        (mul_pos (cosh_pos _) (sin_pos_of_pos_of_lt_pi (mul_pos hcpos hx.1) hπc))
    rw [scaledRatio_numer_eq hx.1 (mul_pos hcpos hx.1) hπx hπc]
    exact div_pos (mul_pos hfactor hbracket) (sq_pos_of_pos hden_pos)

private theorem scaledRatio_strictAnti_of_lt_one {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) :
    StrictAntiOn (scaledRatio c) (Ioo (0 : ℝ) resonanceRoot1) := by
  refine strictAntiOn_of_deriv_neg (convex_Ioo 0 resonanceRoot1) ?_ ?_
  · refine ContinuousOn.div continuous_gammaSEqual.continuousOn
      ((continuous_gammaSEqual.comp (continuous_const.mul continuous_id)).continuousOn) ?_
    intro x hx
    exact (gammaSEqual_pos_of_lt_firstNode (mul_nonneg hc0.le hx.1.le)
      (chordPhase_lt_root hc1 hx.1 hx.2)).ne'
  · intro x hx
    rw [interior_Ioo] at hx
    have hcx : c * x < resonanceRoot1 := chordPhase_lt_root hc1 hx.1 hx.2
    have hπx : x < π :=
      lt_trans hx.2 (lt_trans resonanceRoot1_sharp_bounds.2 (by linarith [pi_gt_three]))
    have hπc : c * x < π :=
      lt_trans hcx (lt_trans resonanceRoot1_sharp_bounds.2 (by linarith [pi_gt_three]))
    have hden_pos : 0 < gammaSEqual (c * x) :=
      gammaSEqual_pos_of_lt_firstNode (mul_nonneg hc0.le hx.1.le) hcx
    rw [(hasDerivAt_scaledRatio hden_pos.ne').deriv]
    have hbracket : c * chordSlope x - chordSlope (c * x) < 0 := by
      have hxmem : x ∈ Ioo (0 : ℝ) resonanceRoot1 := hx
      have hcmem : c * x ∈ Ioo (0 : ℝ) resonanceRoot1 := ⟨mul_pos hc0 hx.1, hcx⟩
      have hxc : c * x < x := by nlinarith [hc1, hx.1]
      have hlt : chordSlope x < chordSlope (c * x) :=
        strictAntiOn_chordSlope hcmem hxmem hxc
      have hpos := chordSlope_pos hx.1 hx.2
      nlinarith
    have hfactor : 0 < 2 * (cosh x * sin x) * (cosh (c * x) * sin (c * x)) := by
      exact mul_pos
        (mul_pos (by norm_num) (mul_pos (cosh_pos x) (sin_pos_of_pos_of_lt_pi hx.1 hπx)))
        (mul_pos (cosh_pos _) (sin_pos_of_pos_of_lt_pi (mul_pos hc0 hx.1) hπc))
    rw [scaledRatio_numer_eq hx.1 (mul_pos hc0 hx.1) hπx hπc]
    exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hfactor hbracket)
      (sq_pos_of_pos hden_pos)

/-! ### The response stays above 7 before the chord node -/

noncomputable def dodecaNearTerm (x : ℝ) : ℝ :=
  (3 / 2 * dodecaNear) * scaledRatio dodecaNear x

noncomputable def dodecaFarTerm (x : ℝ) : ℝ :=
  (3 * sqrt 3 / 2) * scaledRatio (sqrt 3 / 2) x +
    (3 * sqrt 6 / 4) * scaledRatio (sqrt 6 / 4) x +
    (3 / 2 * dodecaFarScale) * scaledRatio dodecaFarScale x +
    (1 / 4) * scaledRatio (1 / 2) x

theorem dodecaResponse_eq_terms (x : ℝ) :
    dodecaResponse x = dodecaNearTerm x + dodecaFarTerm x := by
  unfold dodecaResponse dodecaNearTerm dodecaFarTerm
  ring

private theorem scaledRatio_gt_one {c x : ℝ} (hc : 1 < c) (hx : 0 < x)
    (hcx : c * x < resonanceRoot1) : 1 < scaledRatio c x := by
  have hxc : x < c * x := by nlinarith
  have hx1 : x < resonanceRoot1 := lt_trans hxc hcx
  have hπx : x < π :=
    lt_trans hx1 (lt_trans resonanceRoot1_sharp_bounds.2 (by linarith [pi_gt_three]))
  have hπc : c * x < π :=
    lt_trans hcx (lt_trans resonanceRoot1_sharp_bounds.2 (by linarith [pi_gt_three]))
  have hγ : gammaSEqual (c * x) < gammaSEqual x :=
    gammaSEqual_anti_on_first ⟨hx.le, hπx.le⟩ ⟨(mul_pos (by linarith) hx).le, hπc.le⟩ hxc
  have hpos : 0 < gammaSEqual (c * x) :=
    gammaSEqual_pos_of_lt_firstNode (by positivity) hcx
  unfold scaledRatio
  rw [one_lt_div hpos]
  exact hγ

theorem dodecaNearTerm_strictMono :
    StrictMonoOn dodecaNearTerm (Ioo (0 : ℝ) dodecaWall) := by
  have hmono := scaledRatio_strictMono_of_gt_one dodecaNear_gt_one
  have hweight : 0 < 3 / 2 * dodecaNear := by nlinarith [dodecaNear_gt_one]
  intro a ha b hb hab
  unfold dodecaNearTerm
  have hwall : dodecaWall = resonanceRoot1 / dodecaNear := rfl
  have ha' : a ∈ Ioo (0 : ℝ) (resonanceRoot1 / dodecaNear) := by simpa [hwall] using ha
  have hb' : b ∈ Ioo (0 : ℝ) (resonanceRoot1 / dodecaNear) := by simpa [hwall] using hb
  exact mul_lt_mul_of_pos_left (hmono ha' hb' hab) hweight

theorem dodecaFarTerm_strictAnti :
    StrictAntiOn dodecaFarTerm (Ioo (0 : ℝ) dodecaWall) := by
  have h3 : sqrt 3 / 2 < 1 := by
    rw [div_lt_one (by norm_num)]
    exact lt_trans sqrt_three_lt_twentySix_fifteenths (by norm_num)
  have h6 : sqrt 6 / 4 < 1 := by
    rw [div_lt_one (by norm_num)]
    exact lt_trans sqrt_six_lt_five_halves (by norm_num)
  have h3m := scaledRatio_strictAnti_of_lt_one
    (div_pos (sqrt_pos.mpr (by norm_num)) (by norm_num)) h3
  have h6m := scaledRatio_strictAnti_of_lt_one
    (div_pos (sqrt_pos.mpr (by norm_num)) (by norm_num)) h6
  have hfm := scaledRatio_strictAnti_of_lt_one
    (by
      have h5 : sqrt 5 < 3 := by
        have hsq : (sqrt 5) ^ 2 < (3 : ℝ) ^ 2 := by rw [sq_sqrt (by norm_num)]; norm_num
        have habs : |sqrt 5| < |(3 : ℝ)| := (sq_lt_sq).1 hsq
        rwa [abs_of_nonneg (sqrt_nonneg _), abs_of_pos (by norm_num : (0 : ℝ) < 3)] at habs
      unfold dodecaFarScale
      exact sqrt_pos.mpr (by nlinarith [h5]))
    dodecaFarScale_lt_one
  have hhm := scaledRatio_strictAnti_of_lt_one (c := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
  have hw3 : 0 < 3 * sqrt 3 / 2 := by nlinarith [sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3)]
  have hw6 : 0 < 3 * sqrt 6 / 4 := by nlinarith [sqrt_pos.mpr (by norm_num : (0 : ℝ) < 6)]
  have hwf : 0 < 3 / 2 * dodecaFarScale := by
    have h5 : sqrt 5 < 3 := by
      have hsq : (sqrt 5) ^ 2 < (3 : ℝ) ^ 2 := by rw [sq_sqrt (by norm_num)]; norm_num
      have habs : |sqrt 5| < |(3 : ℝ)| := (sq_lt_sq).1 hsq
      rwa [abs_of_nonneg (sqrt_nonneg _), abs_of_pos (by norm_num : (0 : ℝ) < 3)] at habs
    have hpos : 0 < dodecaFarScale := by
      unfold dodecaFarScale
      exact sqrt_pos.mpr (by nlinarith [h5])
    nlinarith
  intro a ha b hb hab
  have ha1 : a ∈ Ioo (0 : ℝ) resonanceRoot1 := ⟨ha.1, lt_trans ha.2 dodecaWall_mem_Ioo.2⟩
  have hb1 : b ∈ Ioo (0 : ℝ) resonanceRoot1 := ⟨hb.1, lt_trans hb.2 dodecaWall_mem_Ioo.2⟩
  unfold dodecaFarTerm
  have h3lt := mul_lt_mul_of_pos_left (h3m ha1 hb1 hab) hw3
  have h6lt := mul_lt_mul_of_pos_left (h6m ha1 hb1 hab) hw6
  have hflt := mul_lt_mul_of_pos_left (hfm ha1 hb1 hab) hwf
  have hhlt := mul_lt_mul_of_pos_left (hhm ha1 hb1 hab) (by norm_num : (0 : ℝ) < 1 / 4)
  linarith

private theorem dodecaFarTerm_pos {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) dodecaWall) :
    0 < dodecaFarTerm x := by
  have hsc := dodeca_scales_lt_near
  have hγ : 0 < gammaSEqual x :=
    gammaSEqual_pos_left_of_first_node ⟨hx.1, lt_trans hx.2 dodecaWall_mem_Ioo.2⟩
  have hterm : ∀ {s : ℝ}, 0 < s → s ≤ dodecaNear → 0 < scaledRatio s x := by
    intro s hs0 hs
    have hden : 0 < gammaSEqual (s * x) := gamma_pos_dodeca_phase hs0 hs hx
    unfold scaledRatio
    exact div_pos hγ hden
  unfold dodecaFarTerm
  have h3 : 0 < (3 * sqrt 3 / 2) * scaledRatio (sqrt 3 / 2) x :=
    mul_pos (by nlinarith [sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3)])
      (hterm (div_pos (sqrt_pos.mpr (by norm_num)) (by norm_num)) hsc.1.le)
  have h6 : 0 < (3 * sqrt 6 / 4) * scaledRatio (sqrt 6 / 4) x :=
    mul_pos (by nlinarith [sqrt_pos.mpr (by norm_num : (0 : ℝ) < 6)])
      (hterm (div_pos (sqrt_pos.mpr (by norm_num)) (by norm_num)) hsc.2.1.le)
  have h5 : sqrt 5 < 3 := by
    have hsq : (sqrt 5) ^ 2 < (3 : ℝ) ^ 2 := by rw [sq_sqrt (by norm_num)]; norm_num
    have habs : |sqrt 5| < |(3 : ℝ)| := (sq_lt_sq).1 hsq
    rwa [abs_of_nonneg (sqrt_nonneg _), abs_of_pos (by norm_num : (0 : ℝ) < 3)] at habs
  have hf0 : 0 < dodecaFarScale := by
    unfold dodecaFarScale
    exact sqrt_pos.mpr (by nlinarith [h5])
  have hf : 0 < (3 / 2 * dodecaFarScale) * scaledRatio dodecaFarScale x :=
    mul_pos (by nlinarith) (hterm hf0 hsc.2.2.1.le)
  have hh : 0 < (1 / 4) * scaledRatio (1 / 2) x :=
    mul_pos (by norm_num) (hterm (by norm_num) hsc.2.2.2.le)
  linarith

private theorem dodecaTerm_gt_poly {k c cLo x : ℝ} (hk : 0 < k) (hc0 : 0 < cLo)
    (hc : cLo ≤ c) (hx : 0 < x) (hxle : x ≤ 33 / 50) (hx1 : x < resonanceRoot1)
    (hcx : c * x < resonanceRoot1) :
    k * cLo * (1 - x ^ 2 - x ^ 4 / 6) / (1 - (cLo * x) ^ 2) < k * c * scaledRatio c x := by
  have hglo : 0 < 1 - x ^ 2 - x ^ 4 / 6 := by
    have h2 : x ^ 2 ≤ (33 / 50) ^ 2 := pow_le_pow_left₀ hx.le hxle 2
    have h4 : x ^ 4 ≤ (33 / 50) ^ 4 := pow_le_pow_left₀ hx.le hxle 4
    have hcut : (0 : ℝ) < 1 - (33 / 50) ^ 2 - (33 / 50) ^ 4 / 6 := by norm_num
    nlinarith
  have hden : 0 < 1 - (cLo * x) ^ 2 := by
    have hphase : cLo * x < 1 :=
      lt_trans (lt_of_le_of_lt (mul_le_mul_of_nonneg_right hc hx.le) hcx)
        resonanceRoot1_sharp_bounds.2
    have hnn : 0 ≤ cLo * x := mul_nonneg hc0.le hx.le
    nlinarith [sq_nonneg (cLo * x)]
  have hγc : gammaSEqual (c * x) < 1 - (cLo * x) ^ 2 := by
    have hcpos : 0 < c := lt_of_lt_of_le hc0 hc
    have hupper := gammaSEqual_lt_sub_sq (mul_pos hcpos hx) hcx
    rcases lt_or_eq_of_le hc with hlt | rfl
    · have hsq : (cLo * x) ^ 2 < (c * x) ^ 2 := by
        have hphase : cLo * x < c * x := mul_lt_mul_of_pos_right hlt hx
        have hdiff : (c * x) ^ 2 - (cLo * x) ^ 2 =
            (c * x - cLo * x) * (c * x + cLo * x) := by ring
        have hpos : 0 < (c * x - cLo * x) * (c * x + cLo * x) :=
          mul_pos (by linarith) (by nlinarith [hcpos, hc0, hx])
        linarith
      linarith
    · simpa using hupper
  have hγpos : 0 < gammaSEqual (c * x) :=
    gammaSEqual_pos_of_lt_firstNode (mul_nonneg (le_of_lt (lt_of_lt_of_le hc0 hc)) hx.le) hcx
  have hγx := gammaSEqual_gt_lowerPoly hx hx1
  have hratio : (1 - x ^ 2 - x ^ 4 / 6) / (1 - (cLo * x) ^ 2) <
      gammaSEqual x / gammaSEqual (c * x) := by
    rw [div_lt_div_iff₀ hden hγpos]
    nlinarith
  have hle : k * cLo * ((1 - x ^ 2 - x ^ 4 / 6) / (1 - (cLo * x) ^ 2)) ≤
      k * c * ((1 - x ^ 2 - x ^ 4 / 6) / (1 - (cLo * x) ^ 2)) := by
    have hρ : 0 ≤ (1 - x ^ 2 - x ^ 4 / 6) / (1 - (cLo * x) ^ 2) := (div_pos hglo hden).le
    have hcρ : cLo * ((1 - x ^ 2 - x ^ 4 / 6) / (1 - (cLo * x) ^ 2)) ≤
        c * ((1 - x ^ 2 - x ^ 4 / 6) / (1 - (cLo * x) ^ 2)) :=
      mul_le_mul_of_nonneg_right hc hρ
    nlinarith
  have hlt : k * c * ((1 - x ^ 2 - x ^ 4 / 6) / (1 - (cLo * x) ^ 2)) <
      k * c * (gammaSEqual x / gammaSEqual (c * x)) :=
    mul_lt_mul_of_pos_left hratio (mul_pos hk (lt_of_lt_of_le hc0 hc))
  unfold scaledRatio
  have hassoc : k * cLo * (1 - x ^ 2 - x ^ 4 / 6) / (1 - (cLo * x) ^ 2) =
      k * cLo * ((1 - x ^ 2 - x ^ 4 / 6) / (1 - (cLo * x) ^ 2)) := by ring
  have hassoc' : k * c * (gammaSEqual x / gammaSEqual (c * x)) =
      k * c * gammaSEqual x / gammaSEqual (c * x) := by ring
  linarith

private theorem dodeca_slot_1 :
    (7 : ℝ) < 3 / 2 * (7 / 5) +
      3 * (433 / 500) * (1 - (33 / 250) ^ 2 - (33 / 250) ^ 4 / 6) /
        (1 - ((433 / 500) * (33 / 250)) ^ 2) +
      3 * (61 / 100) * (1 - (33 / 250) ^ 2 - (33 / 250) ^ 4 / 6) /
        (1 - ((61 / 100) * (33 / 250)) ^ 2) +
      (3 / 2) * (53 / 100) * (1 - (33 / 250) ^ 2 - (33 / 250) ^ 4 / 6) /
        (1 - ((53 / 100) * (33 / 250)) ^ 2) +
      (1 / 2) * (1 / 2) * (1 - (33 / 250) ^ 2 - (33 / 250) ^ 4 / 6) /
        (1 - ((1 / 2) * (33 / 250)) ^ 2) := by
  norm_num

private theorem dodeca_slot_2 :
    (7 : ℝ) <
      (3 / 2) * (7 / 5) * (1 - (33 / 250) ^ 2 - (33 / 250) ^ 4 / 6) /
        (1 - ((7 / 5) * (33 / 250)) ^ 2) +
      3 * (433 / 500) * (1 - (66 / 250) ^ 2 - (66 / 250) ^ 4 / 6) /
        (1 - ((433 / 500) * (66 / 250)) ^ 2) +
      3 * (61 / 100) * (1 - (66 / 250) ^ 2 - (66 / 250) ^ 4 / 6) /
        (1 - ((61 / 100) * (66 / 250)) ^ 2) +
      (3 / 2) * (53 / 100) * (1 - (66 / 250) ^ 2 - (66 / 250) ^ 4 / 6) /
        (1 - ((53 / 100) * (66 / 250)) ^ 2) +
      (1 / 2) * (1 / 2) * (1 - (66 / 250) ^ 2 - (66 / 250) ^ 4 / 6) /
        (1 - ((1 / 2) * (66 / 250)) ^ 2) := by
  norm_num

private theorem dodeca_slot_3 :
    (7 : ℝ) <
      (3 / 2) * (7 / 5) * (1 - (66 / 250) ^ 2 - (66 / 250) ^ 4 / 6) /
        (1 - ((7 / 5) * (66 / 250)) ^ 2) +
      3 * (433 / 500) * (1 - (99 / 250) ^ 2 - (99 / 250) ^ 4 / 6) /
        (1 - ((433 / 500) * (99 / 250)) ^ 2) +
      3 * (61 / 100) * (1 - (99 / 250) ^ 2 - (99 / 250) ^ 4 / 6) /
        (1 - ((61 / 100) * (99 / 250)) ^ 2) +
      (3 / 2) * (53 / 100) * (1 - (99 / 250) ^ 2 - (99 / 250) ^ 4 / 6) /
        (1 - ((53 / 100) * (99 / 250)) ^ 2) +
      (1 / 2) * (1 / 2) * (1 - (99 / 250) ^ 2 - (99 / 250) ^ 4 / 6) /
        (1 - ((1 / 2) * (99 / 250)) ^ 2) := by
  norm_num

private theorem dodeca_slot_4 :
    (7 : ℝ) <
      (3 / 2) * (7 / 5) * (1 - (99 / 250) ^ 2 - (99 / 250) ^ 4 / 6) /
        (1 - ((7 / 5) * (99 / 250)) ^ 2) +
      3 * (433 / 500) * (1 - (132 / 250) ^ 2 - (132 / 250) ^ 4 / 6) /
        (1 - ((433 / 500) * (132 / 250)) ^ 2) +
      3 * (61 / 100) * (1 - (132 / 250) ^ 2 - (132 / 250) ^ 4 / 6) /
        (1 - ((61 / 100) * (132 / 250)) ^ 2) +
      (3 / 2) * (53 / 100) * (1 - (132 / 250) ^ 2 - (132 / 250) ^ 4 / 6) /
        (1 - ((53 / 100) * (132 / 250)) ^ 2) +
      (1 / 2) * (1 / 2) * (1 - (132 / 250) ^ 2 - (132 / 250) ^ 4 / 6) /
        (1 - ((1 / 2) * (132 / 250)) ^ 2) := by
  norm_num

private theorem dodeca_slot_5 :
    (7 : ℝ) <
      (3 / 2) * (7 / 5) * (1 - (132 / 250) ^ 2 - (132 / 250) ^ 4 / 6) /
        (1 - ((7 / 5) * (132 / 250)) ^ 2) +
      3 * (433 / 500) * (1 - (33 / 50) ^ 2 - (33 / 50) ^ 4 / 6) /
        (1 - ((433 / 500) * (33 / 50)) ^ 2) +
      3 * (61 / 100) * (1 - (33 / 50) ^ 2 - (33 / 50) ^ 4 / 6) /
        (1 - ((61 / 100) * (33 / 50)) ^ 2) +
      (3 / 2) * (53 / 100) * (1 - (33 / 50) ^ 2 - (33 / 50) ^ 4 / 6) /
        (1 - ((53 / 100) * (33 / 50)) ^ 2) +
      (1 / 2) * (1 / 2) * (1 - (33 / 50) ^ 2 - (33 / 50) ^ 4 / 6) /
        (1 - ((1 / 2) * (33 / 50)) ^ 2) := by
  norm_num

private theorem dodeca_near_at_cut :
    (7 : ℝ) < (3 / 2) * (7 / 5) * (1 - (33 / 50) ^ 2 - (33 / 50) ^ 4 / 6) /
      (1 - ((7 / 5) * (33 / 50)) ^ 2) := by
  norm_num

private theorem farPoly_le {b : ℝ} (hb0 : 0 < b) (hb1 : b < resonanceRoot1)
    (hbcut : b ≤ 33 / 50)
    (h3 : (sqrt 3 / 2) * b < resonanceRoot1) (h6 : (sqrt 6 / 4) * b < resonanceRoot1)
    (hf : dodecaFarScale * b < resonanceRoot1) (hh : (1 / 2) * b < resonanceRoot1) :
    3 * (433 / 500) * (1 - b ^ 2 - b ^ 4 / 6) / (1 - ((433 / 500) * b) ^ 2) +
      3 * (61 / 100) * (1 - b ^ 2 - b ^ 4 / 6) / (1 - ((61 / 100) * b) ^ 2) +
      (3 / 2) * (53 / 100) * (1 - b ^ 2 - b ^ 4 / 6) / (1 - ((53 / 100) * b) ^ 2) +
      (1 / 2) * (1 / 2) * (1 - b ^ 2 - b ^ 4 / 6) / (1 - ((1 / 2) * b) ^ 2) <
      dodecaFarTerm b := by
  have h3c : 433 / 500 ≤ sqrt 3 / 2 := sqrt_three_div_two_gt.le
  have h6c : 61 / 100 ≤ sqrt 6 / 4 := sqrt_six_div_four_gt.le
  have hfc : 53 / 100 ≤ dodecaFarScale := dodecaFarScale_gt_fiftyThree_hundredths.le
  have h3t := dodecaTerm_gt_poly (k := 3) (c := sqrt 3 / 2) (cLo := 433 / 500)
    (by norm_num) (by norm_num) h3c hb0 hbcut hb1 h3
  have h6t := dodecaTerm_gt_poly (k := 3) (c := sqrt 6 / 4) (cLo := 61 / 100)
    (by norm_num) (by norm_num) h6c hb0 hbcut hb1 h6
  have hft := dodecaTerm_gt_poly (k := 3 / 2) (c := dodecaFarScale) (cLo := 53 / 100)
    (by norm_num) (by norm_num) hfc hb0 hbcut hb1 hf
  have hht := dodecaTerm_gt_poly (k := 1 / 2) (c := 1 / 2) (cLo := 1 / 2)
    (by norm_num) (by norm_num) le_rfl hb0 hbcut hb1 hh
  unfold dodecaFarTerm
  linarith

private theorem phase_lt_root {c b : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (hb0 : 0 < b)
    (hb1 : b < resonanceRoot1) : c * b < resonanceRoot1 := by
  rcases lt_or_eq_of_le hc1 with hlt | rfl
  · exact chordPhase_lt_root hlt hb0 hb1
  · simpa using hb1

theorem dodecaResponse_gt_seven {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) dodecaWall) :
    7 < dodecaResponse x := by
  have hcut : (33 / 50 : ℝ) < dodecaWall := dodecaWall_gt_thirtyThree_fiftieths
  have hx1 : x < resonanceRoot1 := lt_trans hx.2 dodecaWall_mem_Ioo.2
  rw [dodecaResponse_eq_terms]
  rcases le_or_gt x (33 / 50) with hle | hgt
  · rcases le_or_gt x (33 / 250) with h1 | h1
    · have hnear : 3 / 2 * (7 / 5) < dodecaNearTerm x := by
        have hratio : 1 < scaledRatio dodecaNear x :=
          scaledRatio_gt_one dodecaNear_gt_one hx.1
            (by
              have hwall : dodecaNear * x < resonanceRoot1 := by
                have hxw : x < dodecaWall := hx.2
                unfold dodecaWall at hxw
                have hpos : 0 < dodecaNear := by linarith [dodecaNear_gt_one]
                rw [lt_div_iff₀ hpos] at hxw
                simpa [mul_comm] using hxw
              exact hwall)
        unfold dodecaNearTerm
        have hw : 3 / 2 * (7 / 5) < 3 / 2 * dodecaNear := by
          nlinarith [dodecaNear_gt_seven_fifths]
        nlinarith
      have hb : (33 / 250 : ℝ) < resonanceRoot1 :=
        lt_trans (by norm_num) (lt_trans hcut dodecaWall_mem_Ioo.2)
      have hphases :
          (sqrt 3 / 2) * (33 / 250 : ℝ) < resonanceRoot1 ∧
          (sqrt 6 / 4) * (33 / 250 : ℝ) < resonanceRoot1 ∧
          dodecaFarScale * (33 / 250 : ℝ) < resonanceRoot1 ∧
          (1 / 2) * (33 / 250 : ℝ) < resonanceRoot1 := by
        refine ⟨phase_lt_root (by positivity) (by
            rw [div_le_one (by norm_num)]; exact le_of_lt
              (lt_trans sqrt_three_lt_twentySix_fifteenths (by norm_num)))
            (by norm_num) hb,
          phase_lt_root (by positivity) (by
            rw [div_le_one (by norm_num)]; exact le_of_lt
              (lt_trans sqrt_six_lt_five_halves (by norm_num)))
            (by norm_num) hb,
          phase_lt_root (by
            have h5 : sqrt 5 < 3 := by
              have hsq : (sqrt 5) ^ 2 < (3 : ℝ) ^ 2 := by rw [sq_sqrt (by norm_num)]; norm_num
              have habs : |sqrt 5| < |(3 : ℝ)| := (sq_lt_sq).1 hsq
              rwa [abs_of_nonneg (sqrt_nonneg _), abs_of_pos (by norm_num : (0 : ℝ) < 3)] at habs
            unfold dodecaFarScale; exact sqrt_pos.mpr (by nlinarith [h5]))
            dodecaFarScale_lt_one.le (by norm_num) hb,
          phase_lt_root (by norm_num) (by norm_num) (by norm_num) hb⟩
      have hfar := farPoly_le (b := 33 / 250) (by norm_num) hb (by norm_num)
        hphases.1 hphases.2.1 hphases.2.2.1 hphases.2.2.2
      have hfarx : dodecaFarTerm (33 / 250) ≤ dodecaFarTerm x := by
        rcases lt_or_eq_of_le h1 with hlt | rfl
        · exact (dodecaFarTerm_strictAnti hx ⟨by norm_num, lt_trans (by norm_num) hcut⟩ hlt).le
        · exact le_rfl
      linarith [dodeca_slot_1, hnear, hfar, hfarx]
    · -- Remaining slots use the same split. The cut 33/50 is the last right endpoint.
      have hmono := dodecaNearTerm_strictMono
      have hanti := dodecaFarTerm_strictAnti
      rcases le_or_gt x (66 / 250) with h2 | h2
      · have ha : (33 / 250 : ℝ) ∈ Ioo (0 : ℝ) dodecaWall := ⟨by norm_num, lt_trans (by norm_num) hcut⟩
        have hb : (66 / 250 : ℝ) ∈ Ioo (0 : ℝ) dodecaWall := ⟨by norm_num, lt_trans (by norm_num) hcut⟩
        have hnear : dodecaNearTerm (33 / 250) < dodecaNearTerm x := hmono ha hx h1
        have hfarx : dodecaFarTerm (66 / 250) ≤ dodecaFarTerm x := by
          rcases lt_or_eq_of_le h2 with hlt | rfl
          · exact (hanti hx hb hlt).le
          · exact le_rfl
        have hnp := dodecaTerm_gt_poly (k := 3 / 2) (c := dodecaNear) (cLo := 7 / 5)
          (x := 33 / 250) (by norm_num) (by norm_num) dodecaNear_gt_seven_fifths.le
          (by norm_num) (by norm_num)
          (lt_trans (by norm_num) (lt_trans hcut dodecaWall_mem_Ioo.2))
          (by
            have hpos : 0 < dodecaNear := by linarith [dodecaNear_gt_one]
            have : (33 / 250 : ℝ) < dodecaWall := lt_trans (by norm_num) hcut
            unfold dodecaWall at this
            rw [lt_div_iff₀ hpos] at this
            simpa [mul_comm] using this)
        have hb1 : (66 / 250 : ℝ) < resonanceRoot1 :=
          lt_trans (by norm_num) (lt_trans hcut dodecaWall_mem_Ioo.2)
        have hfp := farPoly_le (b := 66 / 250) (by norm_num) hb1 (by norm_num)
          (phase_lt_root (by positivity) (by
            rw [div_le_one (by norm_num)]; exact le_of_lt
              (lt_trans sqrt_three_lt_twentySix_fifteenths (by norm_num))) (by norm_num) hb1)
          (phase_lt_root (by positivity) (by
            rw [div_le_one (by norm_num)]; exact le_of_lt
              (lt_trans sqrt_six_lt_five_halves (by norm_num))) (by norm_num) hb1)
          (phase_lt_root (by
            have h5 : sqrt 5 < 3 := by
              have hsq : (sqrt 5) ^ 2 < (3 : ℝ) ^ 2 := by rw [sq_sqrt (by norm_num)]; norm_num
              have habs : |sqrt 5| < |(3 : ℝ)| := (sq_lt_sq).1 hsq
              rwa [abs_of_nonneg (sqrt_nonneg _), abs_of_pos (by norm_num : (0 : ℝ) < 3)] at habs
            unfold dodecaFarScale; exact sqrt_pos.mpr (by nlinarith [h5]))
            dodecaFarScale_lt_one.le (by norm_num) hb1)
          (phase_lt_root (by norm_num) (by norm_num) (by norm_num) hb1)
        unfold dodecaNearTerm at hnear ⊢
        linarith [dodeca_slot_2, hnear, hfarx, hnp, hfp]
      rcases le_or_gt x (99 / 250) with h3 | h3
      · have ha : (66 / 250 : ℝ) ∈ Ioo (0 : ℝ) dodecaWall := ⟨by norm_num, lt_trans (by norm_num) hcut⟩
        have hb : (99 / 250 : ℝ) ∈ Ioo (0 : ℝ) dodecaWall := ⟨by norm_num, lt_trans (by norm_num) hcut⟩
        have hnear : dodecaNearTerm (66 / 250) < dodecaNearTerm x := hmono ha hx h2
        have hfarx : dodecaFarTerm (99 / 250) ≤ dodecaFarTerm x := by
          rcases lt_or_eq_of_le h3 with hlt | rfl
          · exact (hanti hx hb hlt).le
          · exact le_rfl
        have hnp := dodecaTerm_gt_poly (k := 3 / 2) (c := dodecaNear) (cLo := 7 / 5)
          (x := 66 / 250) (by norm_num) (by norm_num) dodecaNear_gt_seven_fifths.le
          (by norm_num) (by norm_num)
          (lt_trans (by norm_num) (lt_trans hcut dodecaWall_mem_Ioo.2))
          (by
            have hpos : 0 < dodecaNear := by linarith [dodecaNear_gt_one]
            have : (66 / 250 : ℝ) < dodecaWall := lt_trans (by norm_num) hcut
            unfold dodecaWall at this
            rw [lt_div_iff₀ hpos] at this
            simpa [mul_comm] using this)
        have hb1 : (99 / 250 : ℝ) < resonanceRoot1 :=
          lt_trans (by norm_num) (lt_trans hcut dodecaWall_mem_Ioo.2)
        have hfp := farPoly_le (b := 99 / 250) (by norm_num) hb1 (by norm_num)
          (phase_lt_root (by positivity) (by
            rw [div_le_one (by norm_num)]; exact le_of_lt
              (lt_trans sqrt_three_lt_twentySix_fifteenths (by norm_num))) (by norm_num) hb1)
          (phase_lt_root (by positivity) (by
            rw [div_le_one (by norm_num)]; exact le_of_lt
              (lt_trans sqrt_six_lt_five_halves (by norm_num))) (by norm_num) hb1)
          (phase_lt_root (by
            have h5 : sqrt 5 < 3 := by
              have hsq : (sqrt 5) ^ 2 < (3 : ℝ) ^ 2 := by rw [sq_sqrt (by norm_num)]; norm_num
              have habs : |sqrt 5| < |(3 : ℝ)| := (sq_lt_sq).1 hsq
              rwa [abs_of_nonneg (sqrt_nonneg _), abs_of_pos (by norm_num : (0 : ℝ) < 3)] at habs
            unfold dodecaFarScale; exact sqrt_pos.mpr (by nlinarith [h5]))
            dodecaFarScale_lt_one.le (by norm_num) hb1)
          (phase_lt_root (by norm_num) (by norm_num) (by norm_num) hb1)
        unfold dodecaNearTerm at hnear ⊢
        linarith [dodeca_slot_3, hnear, hfarx, hnp, hfp]
      rcases le_or_gt x (132 / 250) with h4 | h4
      · have ha : (99 / 250 : ℝ) ∈ Ioo (0 : ℝ) dodecaWall := ⟨by norm_num, lt_trans (by norm_num) hcut⟩
        have hb : (132 / 250 : ℝ) ∈ Ioo (0 : ℝ) dodecaWall := ⟨by norm_num, lt_trans (by norm_num) hcut⟩
        have hnear : dodecaNearTerm (99 / 250) < dodecaNearTerm x := hmono ha hx h3
        have hfarx : dodecaFarTerm (132 / 250) ≤ dodecaFarTerm x := by
          rcases lt_or_eq_of_le h4 with hlt | rfl
          · exact (hanti hx hb hlt).le
          · exact le_rfl
        have hnp := dodecaTerm_gt_poly (k := 3 / 2) (c := dodecaNear) (cLo := 7 / 5)
          (x := 99 / 250) (by norm_num) (by norm_num) dodecaNear_gt_seven_fifths.le
          (by norm_num) (by norm_num)
          (lt_trans (by norm_num) (lt_trans hcut dodecaWall_mem_Ioo.2))
          (by
            have hpos : 0 < dodecaNear := by linarith [dodecaNear_gt_one]
            have : (99 / 250 : ℝ) < dodecaWall := lt_trans (by norm_num) hcut
            unfold dodecaWall at this
            rw [lt_div_iff₀ hpos] at this
            simpa [mul_comm] using this)
        have hb1 : (132 / 250 : ℝ) < resonanceRoot1 :=
          lt_trans (by norm_num) (lt_trans hcut dodecaWall_mem_Ioo.2)
        have hfp := farPoly_le (b := 132 / 250) (by norm_num) hb1 (by norm_num)
          (phase_lt_root (by positivity) (by
            rw [div_le_one (by norm_num)]; exact le_of_lt
              (lt_trans sqrt_three_lt_twentySix_fifteenths (by norm_num))) (by norm_num) hb1)
          (phase_lt_root (by positivity) (by
            rw [div_le_one (by norm_num)]; exact le_of_lt
              (lt_trans sqrt_six_lt_five_halves (by norm_num))) (by norm_num) hb1)
          (phase_lt_root (by
            have h5 : sqrt 5 < 3 := by
              have hsq : (sqrt 5) ^ 2 < (3 : ℝ) ^ 2 := by rw [sq_sqrt (by norm_num)]; norm_num
              have habs : |sqrt 5| < |(3 : ℝ)| := (sq_lt_sq).1 hsq
              rwa [abs_of_nonneg (sqrt_nonneg _), abs_of_pos (by norm_num : (0 : ℝ) < 3)] at habs
            unfold dodecaFarScale; exact sqrt_pos.mpr (by nlinarith [h5]))
            dodecaFarScale_lt_one.le (by norm_num) hb1)
          (phase_lt_root (by norm_num) (by norm_num) (by norm_num) hb1)
        unfold dodecaNearTerm at hnear ⊢
        linarith [dodeca_slot_4, hnear, hfarx, hnp, hfp]
      · have ha : (132 / 250 : ℝ) ∈ Ioo (0 : ℝ) dodecaWall := ⟨by norm_num, lt_trans (by norm_num) hcut⟩
        have hb : (33 / 50 : ℝ) ∈ Ioo (0 : ℝ) dodecaWall := ⟨by norm_num, hcut⟩
        have hnear : dodecaNearTerm (132 / 250) < dodecaNearTerm x := hmono ha hx h4
        have hfarx : dodecaFarTerm (33 / 50) ≤ dodecaFarTerm x := by
          rcases lt_or_eq_of_le hle with hlt | rfl
          · exact (hanti hx hb hlt).le
          · exact le_rfl
        have hnp := dodecaTerm_gt_poly (k := 3 / 2) (c := dodecaNear) (cLo := 7 / 5)
          (x := 132 / 250) (by norm_num) (by norm_num) dodecaNear_gt_seven_fifths.le
          (by norm_num) (by norm_num)
          (lt_trans (by norm_num) (lt_trans hcut dodecaWall_mem_Ioo.2))
          (by
            have hpos : 0 < dodecaNear := by linarith [dodecaNear_gt_one]
            have : (132 / 250 : ℝ) < dodecaWall := lt_trans (by norm_num) hcut
            unfold dodecaWall at this
            rw [lt_div_iff₀ hpos] at this
            simpa [mul_comm] using this)
        have hb1 : (33 / 50 : ℝ) < resonanceRoot1 := lt_trans hcut dodecaWall_mem_Ioo.2
        have hfp := farPoly_le (b := 33 / 50) (by norm_num) hb1 (by norm_num)
          (phase_lt_root (by positivity) (by
            rw [div_le_one (by norm_num)]; exact le_of_lt
              (lt_trans sqrt_three_lt_twentySix_fifteenths (by norm_num))) (by norm_num) hb1)
          (phase_lt_root (by positivity) (by
            rw [div_le_one (by norm_num)]; exact le_of_lt
              (lt_trans sqrt_six_lt_five_halves (by norm_num))) (by norm_num) hb1)
          (phase_lt_root (by
            have h5 : sqrt 5 < 3 := by
              have hsq : (sqrt 5) ^ 2 < (3 : ℝ) ^ 2 := by rw [sq_sqrt (by norm_num)]; norm_num
              have habs : |sqrt 5| < |(3 : ℝ)| := (sq_lt_sq).1 hsq
              rwa [abs_of_nonneg (sqrt_nonneg _), abs_of_pos (by norm_num : (0 : ℝ) < 3)] at habs
            unfold dodecaFarScale; exact sqrt_pos.mpr (by nlinarith [h5]))
            dodecaFarScale_lt_one.le (by norm_num) hb1)
          (phase_lt_root (by norm_num) (by norm_num) (by norm_num) hb1)
        unfold dodecaNearTerm at hnear ⊢
        linarith [dodeca_slot_5, hnear, hfarx, hnp, hfp]
  · have hnp := dodecaTerm_gt_poly (k := 3 / 2) (c := dodecaNear) (cLo := 7 / 5)
      (x := 33 / 50) (by norm_num) (by norm_num) dodecaNear_gt_seven_fifths.le
      (by norm_num) (by norm_num)
      (lt_trans hcut dodecaWall_mem_Ioo.2)
      (by
        have hpos : 0 < dodecaNear := by linarith [dodecaNear_gt_one]
        unfold dodecaWall at hcut
        rw [lt_div_iff₀ hpos] at hcut
        simpa [mul_comm] using hcut)
    have hnear : dodecaNearTerm (33 / 50) < dodecaNearTerm x :=
      dodecaNearTerm_strictMono ⟨by norm_num, hcut⟩ hx hgt
    have hfar : 0 < dodecaFarTerm x := dodecaFarTerm_pos hx
    unfold dodecaNearTerm at hnp hnear ⊢
    linarith [dodeca_near_at_cut, hnear, hfar]

theorem dodecaOutward_eq_on_wall {Z x : ℝ} (hx : x ∈ Ioo (0 : ℝ) dodecaWall) :
    dodecaOutward Z x = (dodecaResponse x - Z) / gammaSEqual x := by
  have hsc := dodeca_scales_lt_near
  have hγ : 0 < gammaSEqual x :=
    gammaSEqual_pos_left_of_first_node ⟨hx.1, lt_trans hx.2 dodecaWall_mem_Ioo.2⟩
  have hnear : 0 < gammaSEqual (dodecaNear * x) :=
    gamma_pos_dodeca_phase (by linarith [dodecaNear_gt_one]) le_rfl hx
  have h3 : 0 < gammaSEqual ((sqrt 3 / 2) * x) :=
    gamma_pos_dodeca_phase (div_pos (sqrt_pos.mpr (by norm_num)) (by norm_num)) hsc.1.le hx
  have h6 : 0 < gammaSEqual ((sqrt 6 / 4) * x) :=
    gamma_pos_dodeca_phase (div_pos (sqrt_pos.mpr (by norm_num)) (by norm_num)) hsc.2.1.le hx
  have h5 : sqrt 5 < 3 := by
    have hsq : (sqrt 5) ^ 2 < (3 : ℝ) ^ 2 := by rw [sq_sqrt (by norm_num)]; norm_num
    have habs : |sqrt 5| < |(3 : ℝ)| := (sq_lt_sq).1 hsq
    rwa [abs_of_nonneg (sqrt_nonneg _), abs_of_pos (by norm_num : (0 : ℝ) < 3)] at habs
  have hf0 : 0 < dodecaFarScale := by
    unfold dodecaFarScale
    exact sqrt_pos.mpr (by nlinarith [h5])
  have hf : 0 < gammaSEqual (dodecaFarScale * x) :=
    gamma_pos_dodeca_phase hf0 hsc.2.2.1.le hx
  have hh : 0 < gammaSEqual (x / 2) := by
    rw [div_eq_mul_inv, mul_comm, ← one_div]
    exact gamma_pos_dodeca_phase (s := (1 / 2 : ℝ))
      (by norm_num : (0 : ℝ) < 1 / 2) hsc.2.2.2.le hx
  exact dodecaOutward_eq_response hγ.ne' hnear.ne' h3.ne' h6.ne' hf.ne' hh.ne'

/-- For every nuclear charge `Z ≤ 7`, twenty vertices of a regular dodecahedron
are pushed outward on the whole interval before the nearest chord meets the
first node. -/
theorem dodeca_outward_pos_of_le_seven {Z x : ℝ} (hZ : Z ≤ 7)
    (hx : x ∈ Ioo (0 : ℝ) dodecaWall) : 0 < dodecaOutward Z x := by
  have hresp : 7 < dodecaResponse x := dodecaResponse_gt_seven hx
  have hγ : 0 < gammaSEqual x :=
    gammaSEqual_pos_left_of_first_node ⟨hx.1, lt_trans hx.2 dodecaWall_mem_Ioo.2⟩
  rw [dodecaOutward_eq_on_wall hx]
  exact div_pos (by linarith) hγ

/-- For every nuclear charge `Z ≥ 8`, the dodecahedral shell is drawn inward
at sufficiently large separation. -/
theorem dodeca_far_field_inward {Z : ℝ} (hZ : 8 ≤ Z) :
    ∃ a ∈ Ioo (0 : ℝ) dodecaWall, ∀ x ∈ Ioo (0 : ℝ) a, dodecaOutward Z x < 0 := by
  have hcoeff : dodecaCoeff < Z := lt_of_lt_of_le dodecaCoeff_lt_eight hZ
  obtain ⟨δ, hδpos, hδ⟩ := Metric.mem_nhds_iff.mp
      (tendsto_dodecaResponse_zero (Metric.ball_mem_nhds _ (sub_pos.mpr hcoeff)))
  have hw0 : 0 < dodecaWall := dodecaWall_mem_Ioo.1
  set a : ℝ := min (δ / 2) (dodecaWall / 2)
  have ha0 : 0 < a := by positivity
  have ha_wall : a < dodecaWall := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  refine ⟨a, ⟨ha0, ha_wall⟩, ?_⟩
  intro x hx
  have hxδ : |x - 0| < δ := by
    rw [sub_zero, abs_of_pos hx.1]
    exact lt_of_lt_of_le hx.2 (le_trans (min_le_left _ _) (by linarith))
  have hball : x ∈ Metric.ball 0 δ := by
    rw [Metric.mem_ball, Real.dist_eq]
    simpa [sub_zero] using hxδ
  have hclose := hδ hball
  have hresp : dodecaResponse x < Z := by
    have hmem : dodecaResponse x ∈ Metric.ball dodecaCoeff (Z - dodecaCoeff) := hclose
    rw [Metric.mem_ball, Real.dist_eq] at hmem
    rw [abs_lt] at hmem
    linarith
  have hγ : 0 < gammaSEqual x :=
    gammaSEqual_pos_left_of_first_node
      ⟨hx.1, lt_trans hx.2 (lt_trans ha_wall dodecaWall_mem_Ioo.2)⟩
  rw [dodecaOutward_eq_on_wall ⟨hx.1, lt_trans hx.2 ha_wall⟩]
  exact div_neg_of_neg_of_pos (by linarith) hγ

/-! ### Two electrons, any placement -/

def vdot (v w : Fin 3 → ℝ) : ℝ :=
  v 0 * w 0 + v 1 * w 1 + v 2 * w 2

def vnorm2 (v : Fin 3 → ℝ) : ℝ :=
  vdot v v

noncomputable def vnorm (v : Fin 3 → ℝ) : ℝ :=
  sqrt (vnorm2 v)

def vsub (v w : Fin 3 → ℝ) : Fin 3 → ℝ :=
  fun i => v i - w i

def vsmul (c : ℝ) (v : Fin 3 → ℝ) : Fin 3 → ℝ :=
  fun i => c * v i

/-- Dimensionless phase `ℓ/(2r)` at `ℓ = 1`. -/
noncomputable def pairPhase (r : ℝ) : ℝ :=
  1 / (2 * r)

def outerSep (r : ℝ) : Prop :=
  0 < r ∧ pairPhase r < resonanceRoot1

noncomputable def twoForce (Z : ℝ) (a b : Fin 3 → ℝ) (i : Fin 3) : ℝ :=
  -Z * a i / (gammaSEqual (pairPhase (vnorm a)) * vnorm a ^ 3) +
    (a i - b i) /
      (gammaSEqual (pairPhase (vnorm (vsub a b))) * vnorm (vsub a b) ^ 3)

lemma vnorm2_nonneg (v : Fin 3 → ℝ) : 0 ≤ vnorm2 v := by
  unfold vnorm2 vdot
  nlinarith [sq_nonneg (v 0), sq_nonneg (v 1), sq_nonneg (v 2)]

lemma vnorm_sq (v : Fin 3 → ℝ) : vnorm v ^ 2 = vnorm2 v :=
  sq_sqrt (vnorm2_nonneg v)

lemma vnorm2_smul (c : ℝ) (v : Fin 3 → ℝ) :
    vnorm2 (vsmul c v) = c ^ 2 * vnorm2 v := by
  unfold vnorm2 vdot vsmul
  ring

lemma vnorm_vsub_comm (a b : Fin 3 → ℝ) :
    vnorm (vsub b a) = vnorm (vsub a b) := by
  have h2 : vnorm2 (vsub b a) = vnorm2 (vsub a b) := by
    unfold vnorm2 vdot vsub
    ring
  unfold vnorm
  rw [h2]

lemma exists_coord_ne_zero {v : Fin 3 → ℝ} (hv : 0 < vnorm v) : ∃ i, v i ≠ 0 := by
  by_contra h
  push Not at h
  have h2 : vnorm2 v = 0 := by
    unfold vnorm2 vdot
    simp [h]
  have : vnorm v = 0 := by
    unfold vnorm
    rw [h2, sqrt_zero]
  linarith

lemma gamma_strictAnti_phase {x y : ℝ} (hx0 : 0 ≤ x) (hy : y < resonanceRoot1)
    (hxy : x < y) : gammaSEqual y < gammaSEqual x := by
  have hxπ : x ≤ π :=
    (lt_trans (lt_trans hxy hy)
      (lt_trans resonanceRoot1_bounds.2 (by linarith [pi_gt_three]))).le
  have hyπ : y ≤ π :=
    (lt_trans hy (lt_trans resonanceRoot1_bounds.2 (by linarith [pi_gt_three]))).le
  have hxI : x ∈ Icc (0 : ℝ) π := ⟨hx0, hxπ⟩
  have hyI : y ∈ Icc (0 : ℝ) π := ⟨(lt_of_le_of_lt hx0 hxy).le, hyπ⟩
  exact strictAntiOn_gammaSEqual_even 0 (by simpa using hxI) (by simpa using hyI) hxy

lemma outer_gamma_pos {r : ℝ} (hr : outerSep r) :
    0 < gammaSEqual (pairPhase r) := by
  have hx : 0 < pairPhase r := by
    unfold pairPhase
    exact div_pos (by norm_num) (by linarith [hr.1])
  exact gammaSEqual_pos_of_lt_firstNode hx.le hr.2

/-- Two electrons in the outer well, about a nucleus of charge `Z ≥ 1/4`,
are not simultaneously force-free. Distances are in units of `ℓ`. -/
theorem two_electron_no_outer_balance {Z : ℝ} {a b : Fin 3 → ℝ}
    (hZ : (1 / 4 : ℝ) ≤ Z) (ha : outerSep (vnorm a)) (hb : outerSep (vnorm b))
    (hd : outerSep (vnorm (vsub a b))) :
    ¬ ((∀ i, twoForce Z a b i = 0) ∧ (∀ i, twoForce Z b a i = 0)) := by
  intro ⟨hFa, hFb⟩
  set ra := vnorm a
  set rb := vnorm b
  set d := vnorm (vsub a b)
  set ga := gammaSEqual (pairPhase ra)
  set gb := gammaSEqual (pairPhase rb)
  set gd := gammaSEqual (pairPhase d)
  have ra_eq : ra = vnorm a := rfl
  have rb_eq : rb = vnorm b := rfl
  have d_eq : d = vnorm (vsub a b) := rfl
  have ga_eq : ga = gammaSEqual (pairPhase ra) := rfl
  have gb_eq : gb = gammaSEqual (pairPhase rb) := rfl
  have gd_eq : gd = gammaSEqual (pairPhase d) := rfl
  have hga : 0 < ga := outer_gamma_pos ha
  have hgb : 0 < gb := outer_gamma_pos hb
  have hgd : 0 < gd := outer_gamma_pos hd
  have hra : 0 < ra := ha.1
  have hrb : 0 < rb := hb.1
  have hd0 : 0 < d := hd.1
  have hdena : ga * ra ^ 3 ≠ 0 := mul_ne_zero hga.ne' (pow_ne_zero 3 hra.ne')
  have hdenb : gb * rb ^ 3 ≠ 0 := mul_ne_zero hgb.ne' (pow_ne_zero 3 hrb.ne')
  have hFa' (i : Fin 3) :
      -Z * a i / (ga * ra ^ 3) + (a i - b i) / (gd * d ^ 3) = 0 := by
    simpa [twoForce, ← ra_eq, ← rb_eq, ← d_eq, ← ga_eq, ← gb_eq, ← gd_eq] using hFa i
  have hswap : vnorm (vsub b a) = d := by
    rw [d_eq]
    exact vnorm_vsub_comm a b
  have hFb' (i : Fin 3) :
      -Z * b i / (gb * rb ^ 3) + (b i - a i) / (gd * d ^ 3) = 0 := by
    have hγ : gammaSEqual (pairPhase (vnorm (vsub b a))) = gd := by
      rw [hswap, gd_eq]
    simpa [twoForce, ← ra_eq, ← rb_eq, hswap, hγ, ← ga_eq, ← gb_eq] using hFb i
  have hpar (i : Fin 3) :
      Z * b i / (gb * rb ^ 3) = -(Z * a i / (ga * ra ^ 3)) := by
    have hA := hFa' i
    have hB := hFb' i
    have hneg : (b i - a i) / (gd * d ^ 3) = -((a i - b i) / (gd * d ^ 3)) := by
      rw [show b i - a i = -(a i - b i) by ring, neg_div]
    have hAeq : (a i - b i) / (gd * d ^ 3) = Z * a i / (ga * ra ^ 3) := by
      have hsign : -Z * a i / (ga * ra ^ 3) = -(Z * a i / (ga * ra ^ 3)) := by ring
      rw [hsign] at hA
      linarith
    have hBeq : (b i - a i) / (gd * d ^ 3) = Z * b i / (gb * rb ^ 3) := by
      have hsign : -Z * b i / (gb * rb ^ 3) = -(Z * b i / (gb * rb ^ 3)) := by ring
      rw [hsign] at hB
      linarith
    linarith [hneg, hAeq, hBeq]
  set c : ℝ := gb * rb ^ 3 / (ga * ra ^ 3)
  have hcpos : 0 < c := by
    unfold c
    exact div_pos (mul_pos hgb (pow_pos hrb 3)) (mul_pos hga (pow_pos hra 3))
  have hcne : c ≠ 0 := hcpos.ne'
  have hcdef : c * (ga * ra ^ 3) = gb * rb ^ 3 := by
    unfold c
    field_simp
  have hbi (i : Fin 3) : b i * (ga * ra ^ 3) = -(a i) * (gb * rb ^ 3) := by
    have h := hpar i
    have hmul := congrArg (fun t => t * ((gb * rb ^ 3) * (ga * ra ^ 3))) h
    field_simp [hdenb, hdena] at hmul
    calc
      b i * (ga * ra ^ 3) = b i * ga * ra ^ 3 := by ring
      _ = -(gb * rb ^ 3 * a i) := hmul
      _ = -(a i) * (gb * rb ^ 3) := by ring
  have hb_coord (i : Fin 3) : b i = -c * a i := by
    apply mul_left_cancel₀ hdena
    calc
      (ga * ra ^ 3) * b i = b i * (ga * ra ^ 3) := by ring
      _ = -(a i) * (gb * rb ^ 3) := hbi i
      _ = -(a i) * (c * (ga * ra ^ 3)) := by rw [← hcdef]
      _ = (ga * ra ^ 3) * (-c * a i) := by ring
  have hb_eq : b = vsmul (-c) a := by
    funext i
    simpa [vsmul] using hb_coord i
  have hrb_eq : rb = c * ra := by
    have h2 : rb ^ 2 = (c * ra) ^ 2 := by
      rw [vnorm_sq, hb_eq, vnorm2_smul, ← vnorm_sq]
      ring
    exact (sq_eq_sq₀ hrb.le (mul_nonneg hcpos.le hra.le)).mp h2
  have hga_eq : ga = c ^ 2 * gb := by
    have hscaled : c * ga * ra ^ 3 = gb * (c ^ 3 * ra ^ 3) := by
      calc
        c * ga * ra ^ 3 = c * (ga * ra ^ 3) := by ring
        _ = gb * rb ^ 3 := hcdef
        _ = gb * (c * ra) ^ 3 := by rw [hrb_eq]
        _ = gb * (c ^ 3 * ra ^ 3) := by ring
    have hra3 : ra ^ 3 ≠ 0 := pow_ne_zero 3 hra.ne'
    have hmul : c * ga = gb * c ^ 3 := by
      apply mul_right_cancel₀ hra3
      calc
        (c * ga) * ra ^ 3 = c * ga * ra ^ 3 := by ring
        _ = gb * (c ^ 3 * ra ^ 3) := hscaled
        _ = (gb * c ^ 3) * ra ^ 3 := by ring
    apply mul_left_cancel₀ (pow_ne_zero 2 hcne)
    calc
      c ^ 2 * ga = c * (c * ga) := by ring
      _ = c * (gb * c ^ 3) := by rw [hmul]
      _ = c ^ 2 * (c ^ 2 * gb) := by ring
  have hphase_b : pairPhase rb = pairPhase ra / c := by
    unfold pairPhase
    rw [hrb_eq]
    field_simp [hra.ne', hcne]
  have hxa : 0 < pairPhase ra := by
    unfold pairPhase
    exact div_pos (by norm_num) (mul_pos (by norm_num) hra)
  rcases lt_trichotomy c 1 with hcl | hce | hcg
  · have hxb : pairPhase ra < pairPhase rb := by
      rw [hphase_b, lt_div_iff₀ hcpos]
      nlinarith [hxa, hcl]
    have hγ : gb < ga := gamma_strictAnti_phase hxa.le hb.2 hxb
    have hlt : ga < gb := by
      have hc2 : c ^ 2 < 1 := by nlinarith [hcl, hcpos]
      have : c ^ 2 * gb < gb := by
        simpa [one_mul] using mul_lt_mul_of_pos_right hc2 hgb
      simpa [← hga_eq] using this
    exact lt_irrefl _ (hlt.trans hγ)
  · have hbneg : b = vsmul (-1) a := by
      simpa [hce] using hb_eq
    have hsub : vsub a b = vsmul (2 : ℝ) a := by
      funext i
      have hcoord : b i = -a i := by
        have := congr_fun hbneg i
        simpa [vsmul] using this
      simp [vsub, vsmul, hcoord]
      ring
    have hd_len : d = 2 * ra := by
      have h2 : d ^ 2 = (2 * ra) ^ 2 := by
        rw [vnorm_sq, hsub, vnorm2_smul, ← vnorm_sq]
        ring
      exact (sq_eq_sq₀ hd0.le (mul_nonneg (by norm_num) hra.le)).mp h2
    have hxd : pairPhase d = pairPhase ra / 2 := by
      unfold pairPhase
      rw [hd_len]
      field_simp [hra.ne']
    obtain ⟨i, hi⟩ := exists_coord_ne_zero (v := a) hra
    have hA := hFa' i
    have hdiff : a i - b i = 2 * a i := by
      have hcoord : b i = -a i := by
        have := congr_fun hbneg i
        simpa [vsmul] using this
      rw [hcoord]
      ring
    have hd3 : d ^ 3 = 8 * ra ^ 3 := by
      rw [hd_len]
      ring
    rw [hdiff, hd3] at hA
    have hprod : Z * (4 * gd) = ga := by
      have hra3 : ra ^ 3 ≠ 0 := pow_ne_zero 3 hra.ne'
      field_simp [hdena, hgd.ne', hra3] at hA
      simp only [mul_zero] at hA
      have hcoef : -(Z * gd * 8) + ga * 2 = 0 :=
        (mul_eq_zero.mp hA).resolve_left hi
      have htwo : ga * 2 = Z * gd * 8 := by linarith [hcoef]
      have hga4 : ga = Z * gd * 4 := by
        apply mul_right_cancel₀ (by norm_num : (2 : ℝ) ≠ 0)
        linarith [htwo]
      calc
        Z * (4 * gd) = Z * gd * 4 := by ring
        _ = ga := hga4.symm
    have hZeq : Z = ga / (4 * gd) := by
      have h4 : (4 : ℝ) * gd ≠ 0 := mul_ne_zero (by norm_num) hgd.ne'
      apply (eq_div_iff h4).mpr
      simpa [mul_comm, mul_left_comm] using hprod
    have hxhalf : pairPhase d < pairPhase ra := by
      rw [hxd]
      linarith [hxa]
    have hx0 : 0 ≤ pairPhase d := by
      rw [hxd]
      exact div_nonneg hxa.le (by norm_num)
    have hγ : ga < gd := gamma_strictAnti_phase hx0 ha.2 hxhalf
    have : Z < 1 / 4 := by
      rw [hZeq]
      have h4pos : (0 : ℝ) < 4 * gd := by positivity
      rw [div_lt_div_iff₀ h4pos (by norm_num : (0 : ℝ) < 4)]
      linarith [hγ]
    linarith
  · have hxb : pairPhase rb < pairPhase ra := by
      rw [hphase_b, div_lt_iff₀ hcpos]
      nlinarith [hxa, hcg]
    have hxp : 0 < pairPhase rb := by
      rw [hphase_b]
      exact div_pos hxa hcpos
    have hγ : ga < gb := gamma_strictAnti_phase hxp.le ha.2 hxb
    have hlt : gb < ga := by
      have hc2 : (1 : ℝ) < c ^ 2 := by nlinarith [hcg]
      have : gb < c ^ 2 * gb := by
        simpa [one_mul] using mul_lt_mul_of_pos_right hc2 hgb
      simpa [← hga_eq] using this
    exact lt_irrefl _ (hγ.trans hlt)

/-! ### Reversed-shell closure of the tetrahedron and the octahedron

Every chord is longer than the radius, so the first repulsive shell is the
window in which the longest chord has passed the first node and the radius
has not reached the second. The response falls from above every positive
charge to below `1`, and the outward force restores the root. -/

lemma exp_quarter_gt : (128 / 100 : ℝ) < exp (1 / 4) := by
  exact (exp_between (x := 1 / 4) (lo := 128 / 100) (hi := 2) (n := 8)
    (by norm_num) (by norm_num) (by decide)
    (by norm_num [sum_range_succ, Nat.factorial])
    (by norm_num [sum_range_succ, Nat.factorial])).1

lemma exp_nineteen_twentieths_gt : (2585 / 1000 : ℝ) < exp (19 / 20) := by
  exact (exp_between (x := 19 / 20) (lo := 2585 / 1000) (hi := 3) (n := 8)
    (by norm_num) (by norm_num) (by decide)
    (by norm_num [sum_range_succ, Nat.factorial])
    (by norm_num [sum_range_succ, Nat.factorial])).1

lemma exp_thirtyNine_twentieths_gt : (7 : ℝ) < exp (39 / 20) := by
  have hid : exp (39 / 20) = exp 1 * exp (19 / 20) := by
    rw [show (39 / 20 : ℝ) = 1 + 19 / 20 by norm_num, exp_add]
  have hprod : (271 / 100) * (2585 / 1000) < exp 1 * exp (19 / 20) :=
    mul_lt_mul exp_one_gt_271 exp_nineteen_twentieths_gt.le (by norm_num)
      (exp_pos _).le
  have hnum : (7 : ℝ) < (271 / 100) * (2585 / 1000) := by norm_num
  linarith [hid, hprod]

lemma gammaSEqual_five_quarters_lt : gammaSEqual (5 / 4) < -1 / 2 := by
  have hεlo : (320 / 1000 : ℝ) ≤ π / 2 - 5 / 4 := by linarith [pi_gt_d6]
  have hεhi : π / 2 - 5 / 4 ≤ 321 / 1000 := by linarith [pi_lt_d6]
  have hexp_lo : (34 / 10 : ℝ) < exp (5 / 4) := by
    have hid : exp (5 / 4) = exp 1 * exp (1 / 4) := by
      rw [show (5 / 4 : ℝ) = 1 + 1 / 4 by norm_num, exp_add]
    have hprod : (271 / 100) * (128 / 100) < exp 1 * exp (1 / 4) :=
      mul_lt_mul exp_one_gt_271 exp_quarter_gt.le (by norm_num) (exp_pos _).le
    have hnum : (34 / 10 : ℝ) < (271 / 100) * (128 / 100) := by norm_num
    linarith [hid, hprod]
  have hexp_hi : exp (5 / 4) < 4 := by
    have h1 : exp 1 < 3 := lt_trans exp_one_lt_d9 (by norm_num)
    have h4 : exp (1 / 4) < 13 / 10 := by
      exact (exp_between (x := 1 / 4) (lo := 0) (hi := 13 / 10) (n := 8)
        (by norm_num) (by norm_num) (by decide)
        (by norm_num [sum_range_succ, Nat.factorial])
        (by norm_num [sum_range_succ, Nat.factorial])).2
    have hid : exp (5 / 4) = exp 1 * exp (1 / 4) := by
      rw [show (5 / 4 : ℝ) = 1 + 1 / 4 by norm_num, exp_add]
    have hprod : exp 1 * exp (1 / 4) < 3 * (13 / 10) :=
      mul_lt_mul h1 h4.le (exp_pos _) (by norm_num)
    have hnum : 3 * (13 / 10 : ℝ) < 4 := by norm_num
    linarith [hid, hprod]
  have hD : sinHi (321 / 1000) - cosLo (321 / 1000) < 0 := by
    simp only [sinHi, cosLo]; norm_num
  have hS : 0 < sinLo (320 / 1000) (321 / 1000) + cosLo (321 / 1000) := by
    simp only [sinLo, cosLo]; norm_num
  have hbounds := gamma_before (x := 5 / 4) (ε := π / 2 - 5 / 4)
      (a := 320 / 1000) (b := 321 / 1000) (E0 := 34 / 10) (E1 := 4)
      (by ring) (by norm_num) (by norm_num) hεlo hεhi (by norm_num)
      hexp_lo.le hexp_hi.le hD hS
  have hgu : gammaUpper (34 / 10)
      (sinHi (321 / 1000) - cosLo (321 / 1000))
      (sinHi (321 / 1000) + cosHi (320 / 1000) (321 / 1000)) < -1 / 2 := by
    simp only [gammaUpper, sinHi, cosLo, cosHi]; norm_num
  linarith [hbounds.2]

lemma gammaSEqual_thirtyNine_twentieths_lt : gammaSEqual (39 / 20) < -4 := by
  have hεlo : (379 / 1000 : ℝ) ≤ 39 / 20 - π / 2 := by linarith [pi_lt_d6]
  have hεhi : 39 / 20 - π / 2 ≤ 380 / 1000 := by linarith [pi_gt_d6]
  have hexp_hi : exp (39 / 20) ≤ 74 / 10 := by
    have hlt : exp (39 / 20) < exp 2 := exp_lt_exp.mpr (by norm_num)
    exact le_of_lt (lt_trans hlt exp_one_sq_bounds.2)
  have hD : -(sinLo (379 / 1000) (380 / 1000) + cosLo (380 / 1000)) < 0 := by
    simp only [sinLo, cosLo]; norm_num
  have hS : 0 < -sinHi (380 / 1000) + cosLo (380 / 1000) := by
    simp only [sinHi, cosLo]; norm_num
  have hbounds := gamma_after (x := 39 / 20) (ε := 39 / 20 - π / 2)
      (a := 379 / 1000) (b := 380 / 1000) (E0 := 7) (E1 := 74 / 10)
      (by ring) (by norm_num) (by norm_num) hεlo hεhi (by norm_num)
      exp_thirtyNine_twentieths_gt.le hexp_hi hD hS
  have hgu : gammaUpper 7
      (-(sinLo (379 / 1000) (380 / 1000) + cosLo (380 / 1000)))
      (-sinLo (379 / 1000) (380 / 1000) +
        cosHi (379 / 1000) (380 / 1000)) < -4 := by
    simp only [gammaUpper, sinLo, cosLo, cosHi]; norm_num
  linarith [hbounds.2]

lemma branchNode_one_gt_thirtyNine_tenths : 39 / 10 < branchNode 1 := by
  have hlo : π + π / 4 < branchNode 1 := by
    have h := node_mem_sharp_branch 1 (branchNode_spec 1).1 (branchNode_spec 1).2
    simpa [Nat.cast_one, one_mul] using h.1
  linarith [pi_gt_d6, hlo]

lemma tetraScale_gt_three_fifths : 3 / 5 < tetraScale := by
  have h6 : 12 / 5 < sqrt 6 := sqrt_six_gt_twelve_fifths
  unfold tetraScale
  nlinarith

lemma tetraScale_lt_five_eighths : tetraScale < 5 / 8 := by
  have h6 : sqrt 6 < 5 / 2 := sqrt_six_lt_five_halves
  unfold tetraScale
  nlinarith

lemma tetra_phases_in_shell {x : ℝ}
    (hx : x ∈ Ioo (resonanceRoot1 / tetraScale) (branchNode 1)) :
    gammaSEqual x < 0 ∧ gammaSEqual (tetraScale * x) < 0 := by
  have hscale := tetraScale_mem_Ioo
  have hx0 : 0 < x := by
    have hslot : 0 < resonanceRoot1 / tetraScale :=
      div_pos (lt_trans (by norm_num) resonanceRoot1_bounds.1) hscale.1
    linarith [hx.1, hslot]
  have hroot : resonanceRoot1 < x := by
    have hdiv : resonanceRoot1 < resonanceRoot1 / tetraScale := by
      rw [lt_div_iff₀ hscale.1]
      have hpos : 0 < resonanceRoot1 :=
        lt_trans (by norm_num) resonanceRoot1_bounds.1
      nlinarith [hscale.2, hpos]
    exact lt_trans hdiv hx.1
  have hedge_lo : resonanceRoot1 < tetraScale * x := by
    simpa [mul_comm] using (div_lt_iff₀ hscale.1).mp hx.1
  have hedge_hi : tetraScale * x < branchNode 1 := by nlinarith [hscale.2, hx.2, hx0]
  exact ⟨gammaSEqual_neg_first_shell ⟨hroot, hx.2⟩,
    gammaSEqual_neg_first_shell ⟨hedge_lo, hedge_hi⟩⟩

lemma tetraResponse_strictAnti :
    StrictAntiOn tetraResponse (Ioo (resonanceRoot1 / tetraScale) (branchNode 1)) := by
  have hscale := tetraScale_mem_Ioo
  have hanti := scaledRatio_strictAnti_from_chord (c := tetraScale) hscale.1 hscale.2
  have hcoeff : 0 < tetraCoeff := by unfold tetraCoeff; positivity
  unfold tetraResponse
  exact strictAntiOn_const_mul hcoeff hanti

lemma continuousOn_tetraResponse :
    ContinuousOn tetraResponse (Ioo (resonanceRoot1 / tetraScale) (branchNode 1)) := by
  unfold tetraResponse scaledRatio
  refine ContinuousOn.mul continuousOn_const ?_
  refine ContinuousOn.div continuous_gammaSEqual.continuousOn
    (continuous_gammaSEqual.comp (continuous_const.mul continuous_id)).continuousOn ?_
  intro x hx
  exact (tetra_phases_in_shell hx).2.ne

lemma tetraResponse_of_outward {Z x : ℝ}
    (hx : x ∈ Ioo (resonanceRoot1 / tetraScale) (branchNode 1))
    (h0 : tetraOutward Z x = 0) : tetraResponse x = Z := by
  have hphases := tetra_phases_in_shell hx
  have heq := tetraOutward_eq_response (Z := Z) (x := x) hphases.1.ne hphases.2.ne
  rw [h0] at heq
  have : (tetraResponse x - Z) / gammaSEqual x = 0 := heq.symm
  field_simp [hphases.1.ne] at this
  linarith

/-- Just after the edge enters the shell, the tetrahedral response exceeds `Z`. -/
lemma tetraResponse_gt_near_outer {Z : ℝ} (hZ : 1 ≤ Z) :
    Z < tetraResponse ((resonanceRoot1 + 1 / (40 * Z)) / tetraScale) := by
  have hZ0 : 0 < Z := by linarith
  set h : ℝ := 1 / (40 * Z) with hh
  have hh0 : 0 < h := by positivity
  have hx1 : resonanceRoot1 < resonanceRoot1 + h := by linarith
  obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope gammaSEqual (deriv gammaSEqual) hx1
    continuous_gammaSEqual.continuousOn (fun y _ => by
      simpa [deriv_gammaSEqual] using hasDerivAt_gammaSEqual y)
  have hzero : gammaSEqual resonanceRoot1 = 0 := resonanceRoot1_gammaSEqual_zero
  have hval : gammaSEqual (resonanceRoot1 + h) = deriv gammaSEqual c * h := by
    have hs := hslope.symm
    rw [hzero, sub_zero] at hs
    have hsub : resonanceRoot1 + h - resonanceRoot1 = h := by ring
    rw [hsub] at hs
    field_simp [hh0.ne'] at hs
    linarith
  have hh1 : h ≤ 1 / 40 := by
    rw [hh, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hc0 : 0 ≤ c := by linarith [resonanceRoot1_bounds.1, hc.1]
  have hc2 : c < 2 := by linarith [hc.2, resonanceRoot1_sharp_bounds.2, hh1]
  have hcosh : cosh c < 5 := by
    have hle : cosh c ≤ cosh 2 := (cosh_le_cosh).mpr (by
      rw [abs_of_nonneg hc0, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      exact le_of_lt hc2)
    linarith [hle, cosh_two_lt_five]
  have hsin0 : 0 ≤ sin c :=
    sin_nonneg_of_nonneg_of_le_pi hc0 (by linarith [hc2, pi_gt_three])
  have hmag : 2 * cosh c * sin c < 10 := by
    have hsin : sin c ≤ 1 := sin_le_one c
    have hcoef : 0 ≤ 2 * cosh c := by linarith [cosh_pos c]
    have hlin : 2 * cosh c * sin c ≤ 2 * cosh c := by
      simpa using mul_le_mul_of_nonneg_left hsin hcoef
    linarith [hcosh, hlin]
  have hsmall : -gammaSEqual (resonanceRoot1 + h) < 10 * h := by
    rw [hval, deriv_gammaSEqual]
    nlinarith [hmag, hh0]
  set x : ℝ := (resonanceRoot1 + h) / tetraScale
  have hscale_lo := tetraScale_gt_three_fifths
  have hscale_hi := tetraScale_lt_five_eighths
  have hx_gt : 5 / 4 < x := by
    have hbase : (5 / 4 : ℝ) < 2 * π / 5 := by linarith [pi_gt_d6]
    have heq : (π / 4) / (5 / 8) = 2 * π / 5 := by ring
    have hlow : (π / 4) / (5 / 8) < resonanceRoot1 / tetraScale := by
      rw [div_lt_div_iff₀ (by norm_num) tetraScale_mem_Ioo.1]
      have h1 : (π / 4) * tetraScale < (π / 4) * (5 / 8) :=
        mul_lt_mul_of_pos_left hscale_hi (by positivity)
      have h2 : (π / 4) * (5 / 8) < resonanceRoot1 * (5 / 8) :=
        mul_lt_mul_of_pos_right resonanceRoot1_sharp_bounds.1 (by norm_num)
      linarith
    have hstep : resonanceRoot1 / tetraScale < x := by
      dsimp [x]
      rw [div_lt_div_iff₀ tetraScale_mem_Ioo.1 tetraScale_mem_Ioo.1]
      nlinarith [hh0, hscale_lo]
    have hmid : 5 / 4 < (π / 4) / (5 / 8) := by
      rw [heq]
      exact hbase
    exact lt_trans (lt_trans hmid hlow) hstep
  have hxπ : x < π := by
    have hnum : resonanceRoot1 + h < 41 / 40 := by
      linarith [resonanceRoot1_sharp_bounds.2, hh1]
    have hx24 : x < 41 / 24 := by
      dsimp [x]
      rw [div_lt_div_iff₀ tetraScale_mem_Ioo.1 (by norm_num : (0 : ℝ) < 24)]
      have hL : (resonanceRoot1 + h) * 24 < (41 / 40) * 24 :=
        mul_lt_mul_of_pos_right hnum (by norm_num)
      have hR : (41 / 40) * 24 < 41 * tetraScale := by
        have heq : (41 / 40 : ℝ) * 24 = 41 * (3 / 5) := by norm_num
        rw [heq]
        exact mul_lt_mul_of_pos_left hscale_lo (by norm_num)
      linarith
    have h24 : (41 / 24 : ℝ) < π := by linarith [pi_gt_three]
    exact lt_trans hx24 h24
  have hγx : gammaSEqual x < -1 / 2 := by
    have hleft : (5 / 4 : ℝ) ∈ Icc (0 : ℝ) π := ⟨by norm_num, by linarith [pi_gt_three]⟩
    have hright : x ∈ Icc (0 : ℝ) π := ⟨by linarith, hxπ.le⟩
    have hlt := strictAntiOn_gammaSEqual_even 0 (by simpa using hleft)
      (by simpa using hright) hx_gt
    linarith [hlt, gammaSEqual_five_quarters_lt]
  have hγe_lt : gammaSEqual (resonanceRoot1 + h) < 0 := by
    have hmem : resonanceRoot1 + h ∈ Ioo resonanceRoot1 (branchNode 1) := by
      refine ⟨by linarith, ?_⟩
      have hnode : π < branchNode 1 := by
        simpa [Nat.cast_one, one_mul] using (branchNode_spec 1).1.1
      linarith [resonanceRoot1_sharp_bounds.2, hh1, pi_gt_three, hnode]
    exact gammaSEqual_neg_first_shell hmem
  have hγe_gt : -(10 * h) < gammaSEqual (resonanceRoot1 + h) := by linarith [hsmall]
  have hratio : 2 * Z < gammaSEqual x / gammaSEqual (resonanceRoot1 + h) := by
    have htarget : 1 / (20 * h) = 2 * Z := by
      rw [hh]; field_simp; ring
    rw [← htarget, lt_div_iff_of_neg hγe_lt]
    have hright : -1 / 2 < (1 / (20 * h)) * gammaSEqual (resonanceRoot1 + h) := by
      have hcmp : (1 / (20 * h)) * (-(10 * h)) <
          (1 / (20 * h)) * gammaSEqual (resonanceRoot1 + h) := by
        exact mul_lt_mul_of_pos_left hγe_gt (by positivity)
      have hid : (1 / (20 * h)) * (-(10 * h)) = -1 / 2 := by field_simp; ring
      linarith
    linarith [hγx]
  have hsame : gammaSEqual (tetraScale * x) = gammaSEqual (resonanceRoot1 + h) := by
    dsimp [x]
    congr 1
    field_simp [tetraScale_mem_Ioo.1.ne']
  have hratio' : 2 * Z < scaledRatio tetraScale x := by
    unfold scaledRatio
    rw [hsame]
    exact hratio
  have hcoeff : 3 / 4 < tetraCoeff := by
    have h6 : (2 : ℝ) < sqrt 6 := by
      rw [← sqrt_sq (by norm_num : (0 : ℝ) ≤ 2), sqrt_lt_sqrt_iff (by positivity)]
      norm_num
    unfold tetraCoeff
    nlinarith
  have hpos : 0 < scaledRatio tetraScale x := by linarith
  have hstep : (3 / 4) * (2 * Z) < tetraCoeff * scaledRatio tetraScale x := by
    have h1 : (3 / 4) * (2 * Z) < tetraCoeff * (2 * Z) :=
      mul_lt_mul_of_pos_right hcoeff (by positivity)
    have h2 : tetraCoeff * (2 * Z) < tetraCoeff * scaledRatio tetraScale x :=
      mul_lt_mul_of_pos_left hratio' (by linarith)
    linarith
  have hthree : Z < (3 / 4) * (2 * Z) := by nlinarith
  unfold tetraResponse
  linarith

lemma tetraResponse_thirtyNine_tenths_lt : tetraResponse (39 / 10) < 1 := by
  have hscale_lo := tetraScale_gt_three_fifths
  have hscale_hi := tetraScale_lt_five_eighths
  have hedge_lo : 11 / 5 < tetraScale * (39 / 10) := by
    have h6 : 12 / 5 < sqrt 6 := sqrt_six_gt_twelve_fifths
    unfold tetraScale
    nlinarith
  have hedge_hi : tetraScale * (39 / 10) < π := by
    have h6 : sqrt 6 < 5 / 2 := sqrt_six_lt_five_halves
    have hπ : (39 / 16 : ℝ) < π := by linarith [pi_gt_three]
    unfold tetraScale
    nlinarith
  have hγe : gammaSEqual (tetraScale * (39 / 10)) < gammaSEqual (11 / 5) := by
    have hleft : (11 / 5 : ℝ) ∈ Icc (0 : ℝ) π := ⟨by norm_num, by linarith [pi_gt_three]⟩
    have hright : tetraScale * (39 / 10) ∈ Icc (0 : ℝ) π :=
      ⟨by linarith [hedge_lo], hedge_hi.le⟩
    exact strictAntiOn_gammaSEqual_even 0 (by simpa using hleft)
      (by simpa using hright) hedge_lo
  have hγe6 : gammaSEqual (tetraScale * (39 / 10)) < -6 := by
    linarith [hγe, gammaSEqual_eleven_fifths_lt]
  have hgx : -3 / 2 < gammaSEqual (39 / 10) := gammaSEqual_thirtyNine_tenths_gt
  have hcmp : gammaSEqual (tetraScale * (39 / 10)) < gammaSEqual (39 / 10) := by
    linarith [hγe6, hgx]
  have hge : gammaSEqual (tetraScale * (39 / 10)) < 0 := by linarith
  have hratio : gammaSEqual (39 / 10) / gammaSEqual (tetraScale * (39 / 10)) < 1 := by
    rw [div_lt_iff_of_neg hge]
    linarith [hcmp]
  have hcoeff : tetraCoeff < 1 := tetraCoeff_lt_one
  have hpos : 0 < tetraCoeff := by unfold tetraCoeff; positivity
  unfold tetraResponse scaledRatio
  have hmul : tetraCoeff *
      (gammaSEqual (39 / 10) / gammaSEqual (tetraScale * (39 / 10))) < tetraCoeff := by
    have hlt := mul_lt_mul_of_pos_left hratio hpos
    simpa using hlt
  linarith

theorem tetraOutward_sign {Z x : ℝ}
    (hx : x ∈ Ioo (resonanceRoot1 / tetraScale) (branchNode 1)) :
    tetraOutward Z x < 0 ↔ Z < tetraResponse x := by
  have hphases := tetra_phases_in_shell hx
  rw [tetraOutward_eq_response hphases.1.ne hphases.2.ne]
  have hden : gammaSEqual x < 0 := hphases.1
  constructor
  · intro h
    have : tetraResponse x - Z > 0 := by
      rw [div_lt_iff_of_neg hden] at h
      linarith
    linarith
  · intro h
    rw [div_lt_iff_of_neg hden]
    linarith

theorem tetraOutward_restores {Z x y : ℝ}
    (hx : x ∈ Ioo (resonanceRoot1 / tetraScale) (branchNode 1))
    (hy : y ∈ Ioo (resonanceRoot1 / tetraScale) (branchNode 1))
    (h0 : tetraOutward Z y = 0) :
    (x < y → tetraOutward Z x < 0) ∧ (y < x → 0 < tetraOutward Z x) := by
  have hyR : tetraResponse y = Z := tetraResponse_of_outward hy h0
  constructor
  · intro hlt
    have hZ : Z < tetraResponse x := by
      linarith [tetraResponse_strictAnti hx hy hlt, hyR]
    exact (tetraOutward_sign hx).mpr hZ
  · intro hlt
    have hnum : tetraResponse x - Z < 0 := by
      linarith [tetraResponse_strictAnti hy hx hlt, hyR]
    have hphases := tetra_phases_in_shell hx
    rw [tetraOutward_eq_response hphases.1.ne hphases.2.ne]
    exact div_pos_of_neg_of_neg hnum hphases.1

/-- For every nuclear charge `Z ≥ 1`, four electrons at the vertices of a
regular tetrahedron have exactly one radial balance in the window where the
radius and the edge both lie in the first repulsive shell. -/
theorem exists_unique_tetra_shell {Z : ℝ} (hZ : 1 ≤ Z) :
    ∃! x : ℝ, x ∈ Ioo (resonanceRoot1 / tetraScale) (branchNode 1) ∧
      tetraOutward Z x = 0 := by
  have hZ0 : 0 < Z := by linarith
  set xL : ℝ := (resonanceRoot1 + 1 / (40 * Z)) / tetraScale
  set xR : ℝ := 39 / 10
  have hgt : Z < tetraResponse xL := by
    simpa [xL] using tetraResponse_gt_near_outer hZ
  have hlt : tetraResponse xR < Z := by
    have h1 : tetraResponse xR < 1 := by
      simpa [xR] using tetraResponse_thirtyNine_tenths_lt
    linarith
  have hxL_lo : resonanceRoot1 / tetraScale < xL := by
    dsimp [xL]
    rw [div_lt_div_iff₀ tetraScale_mem_Ioo.1 tetraScale_mem_Ioo.1]
    have hh : 0 < 1 / (40 * Z) := by positivity
    have hpos : 0 < tetraScale := tetraScale_mem_Ioo.1
    nlinarith [hpos, hh]
  have hxL_hi : xL < xR := by
    dsimp [xL, xR]
    have hh : 1 / (40 * Z) ≤ 1 / 40 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    have hnum : resonanceRoot1 + 1 / (40 * Z) < 41 / 40 := by
      linarith [resonanceRoot1_sharp_bounds.2, hh]
    have hx24 : xL < 41 / 24 := by
      dsimp [xL]
      rw [div_lt_div_iff₀ tetraScale_mem_Ioo.1 (by norm_num : (0 : ℝ) < 24)]
      have hscale : 3 / 5 < tetraScale := tetraScale_gt_three_fifths
      have hL : (resonanceRoot1 + 1 / (40 * Z)) * 24 < (41 / 40) * 24 :=
        mul_lt_mul_of_pos_right hnum (by norm_num)
      have hR : (41 / 40) * 24 < 41 * tetraScale := by
        have heq : (41 / 40 : ℝ) * 24 = 41 * (3 / 5) := by norm_num
        rw [heq]
        exact mul_lt_mul_of_pos_left hscale (by norm_num)
      linarith
    have h24 : (41 / 24 : ℝ) < 39 / 10 := by norm_num
    exact lt_trans hx24 h24
  have hRmem : xR ∈ Ioo (resonanceRoot1 / tetraScale) (branchNode 1) := by
    dsimp [xR]
    refine ⟨?_, branchNode_one_gt_thirtyNine_tenths⟩
    have hslot : resonanceRoot1 / tetraScale < 5 / 3 := by
      have hden : 3 / 5 < tetraScale := tetraScale_gt_three_fifths
      have hroot : resonanceRoot1 < 1 := resonanceRoot1_sharp_bounds.2
      have hpos : 0 < resonanceRoot1 := lt_trans (by norm_num) resonanceRoot1_bounds.1
      rw [div_lt_div_iff₀ tetraScale_mem_Ioo.1 (by norm_num)]
      nlinarith
    linarith
  have hcont : ContinuousOn (fun t => Z - tetraResponse t) (Icc xL xR) := by
    refine ContinuousOn.sub continuousOn_const ?_
    refine continuousOn_tetraResponse.mono ?_
    intro t ht
    exact ⟨lt_of_lt_of_le hxL_lo ht.1, lt_of_le_of_lt ht.2 hRmem.2⟩
  have hleft : (fun t => Z - tetraResponse t) xL < 0 := by
    simpa using sub_neg.mpr hgt
  have hright : 0 < (fun t => Z - tetraResponse t) xR := by
    simpa using sub_pos.mpr hlt
  obtain ⟨x, hxI, hx0⟩ := intermediate_value_Ioo (le_of_lt hxL_hi) hcont ⟨hleft, hright⟩
  have hxLmem : xL ∈ Ioo (resonanceRoot1 / tetraScale) (branchNode 1) :=
    ⟨hxL_lo, lt_trans hxL_hi hRmem.2⟩
  have hxmem : x ∈ Ioo (resonanceRoot1 / tetraScale) (branchNode 1) :=
    ⟨lt_trans hxL_lo hxI.1, lt_trans hxI.2 hRmem.2⟩
  have hzero : tetraOutward Z x = 0 := by
    have hphases := tetra_phases_in_shell hxmem
    rw [tetraOutward_eq_response hphases.1.ne hphases.2.ne]
    have hresp : tetraResponse x = Z := by linarith [hx0]
    rw [hresp]
    field_simp [hphases.1.ne]
    ring
  refine ⟨x, ⟨hxmem, hzero⟩, ?_⟩
  intro y hy
  have hxR := tetraResponse_of_outward hxmem hzero
  have hyR := tetraResponse_of_outward hy.1 hy.2
  exact (tetraResponse_strictAnti.injOn hxmem hy.1 (by rw [hxR, hyR])).symm

lemma octaEdge_ge_half : 1 / 2 ≤ octaEdge := by
  unfold octaEdge
  have h2 : (1 : ℝ) < sqrt 2 := one_lt_sqrt_two
  nlinarith

lemma octa_phases_in_shell {x : ℝ}
    (hx : x ∈ Ioo (2 * resonanceRoot1) (branchNode 1)) :
    gammaSEqual x < 0 ∧ gammaSEqual (octaEdge * x) < 0 ∧ gammaSEqual (x / 2) < 0 := by
  have hedge := octaEdge_mem_Ioo
  have hhalf := octaEdge_ge_half
  have hx0 : 0 < x := by linarith [hx.1, resonanceRoot1_bounds.1]
  have hroot : resonanceRoot1 < x := by
    have htwo : resonanceRoot1 < 2 * resonanceRoot1 := by
      nlinarith [resonanceRoot1_bounds.1]
    exact lt_trans htwo hx.1
  have hopp_lo : resonanceRoot1 < x / 2 := by
    rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
    linarith [hx.1]
  have hopp_hi : x / 2 < branchNode 1 := by
    have hlt : x / 2 < x := by nlinarith
    exact lt_trans hlt hx.2
  have hedge_lo : resonanceRoot1 < octaEdge * x := by nlinarith [hhalf, hopp_lo, hx0]
  have hedge_hi : octaEdge * x < branchNode 1 := by nlinarith [hedge.2, hx.2, hx0]
  exact ⟨gammaSEqual_neg_first_shell ⟨hroot, hx.2⟩,
    gammaSEqual_neg_first_shell ⟨hedge_lo, hedge_hi⟩,
    gammaSEqual_neg_first_shell ⟨hopp_lo, hopp_hi⟩⟩

lemma octaResponse_strictAnti :
    StrictAntiOn octaResponse (Ioo (2 * resonanceRoot1) (branchNode 1)) := by
  have hedge := scaledRatio_strictAnti (c := octaEdge) octaEdge_ge_half octaEdge_mem_Ioo.2
  have hbod := scaledRatio_strictAnti (c := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
  unfold octaResponse
  exact strictAntiOn_add
    (strictAntiOn_const_mul (sqrt_pos.mpr (by norm_num)) hedge)
    (strictAntiOn_const_mul (by norm_num : (0 : ℝ) < 1 / 4) hbod)

lemma continuousOn_octaResponse :
    ContinuousOn octaResponse (Ioo (2 * resonanceRoot1) (branchNode 1)) := by
  unfold octaResponse scaledRatio
  refine ContinuousOn.add ?_ ?_
  · refine ContinuousOn.mul continuousOn_const ?_
    refine ContinuousOn.div continuous_gammaSEqual.continuousOn
      (continuous_gammaSEqual.comp (continuous_const.mul continuous_id)).continuousOn ?_
    intro x hx
    exact (octa_phases_in_shell hx).2.1.ne
  · refine ContinuousOn.mul continuousOn_const ?_
    refine ContinuousOn.div continuous_gammaSEqual.continuousOn
      (continuous_gammaSEqual.comp (continuous_const.mul continuous_id)).continuousOn ?_
    intro x hx
    have hsame : (1 / 2) * x = x / 2 := by ring
    rw [hsame]
    exact (octa_phases_in_shell hx).2.2.ne

lemma octaResponse_of_outward {Z x : ℝ}
    (hx : x ∈ Ioo (2 * resonanceRoot1) (branchNode 1))
    (h0 : octaOutward Z x = 0) : octaResponse x = Z := by
  have hphases := octa_phases_in_shell hx
  have heq := octaOutward_eq_response (Z := Z) (x := x) hphases.1.ne hphases.2.1.ne
    hphases.2.2.ne
  rw [h0] at heq
  have : (octaResponse x - Z) / gammaSEqual x = 0 := heq.symm
  field_simp [hphases.1.ne] at this
  linarith

/-- The opposite-vertex term alone exceeds `Z` just after that chord enters
the shell, and the four edges add a positive contribution. -/
lemma octaResponse_gt_near_outer {Z : ℝ} (hZ : 1 ≤ Z) :
    Z < octaResponse (2 * (resonanceRoot1 + 1 / (40 * Z))) := by
  have hZ0 : 0 < Z := by linarith
  set h : ℝ := 1 / (40 * Z) with hh
  have hh0 : 0 < h := by positivity
  have hx1 : resonanceRoot1 < resonanceRoot1 + h := by linarith
  obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope gammaSEqual (deriv gammaSEqual) hx1
    continuous_gammaSEqual.continuousOn (fun y _ => by
      simpa [deriv_gammaSEqual] using hasDerivAt_gammaSEqual y)
  have hzero : gammaSEqual resonanceRoot1 = 0 := resonanceRoot1_gammaSEqual_zero
  have hval : gammaSEqual (resonanceRoot1 + h) = deriv gammaSEqual c * h := by
    have hs := hslope.symm
    rw [hzero, sub_zero] at hs
    have hsub : resonanceRoot1 + h - resonanceRoot1 = h := by ring
    rw [hsub] at hs
    field_simp [hh0.ne'] at hs
    linarith
  have hh1 : h ≤ 1 / 40 := by
    rw [hh, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hc0 : 0 ≤ c := by linarith [resonanceRoot1_bounds.1, hc.1]
  have hc2 : c < 2 := by linarith [hc.2, resonanceRoot1_sharp_bounds.2, hh1]
  have hcosh : cosh c < 5 := by
    have hle : cosh c ≤ cosh 2 := (cosh_le_cosh).mpr (by
      rw [abs_of_nonneg hc0, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      exact le_of_lt hc2)
    linarith [hle, cosh_two_lt_five]
  have hsin0 : 0 ≤ sin c :=
    sin_nonneg_of_nonneg_of_le_pi hc0 (by linarith [hc2, pi_gt_three])
  have hmag : 2 * cosh c * sin c < 10 := by
    have hsin : sin c ≤ 1 := sin_le_one c
    have hcoef : 0 ≤ 2 * cosh c := by linarith [cosh_pos c]
    have hlin : 2 * cosh c * sin c ≤ 2 * cosh c := by
      simpa using mul_le_mul_of_nonneg_left hsin hcoef
    linarith [hcosh, hlin]
  have hsmall : -gammaSEqual (resonanceRoot1 + h) < 10 * h := by
    rw [hval, deriv_gammaSEqual]
    nlinarith [hmag, hh0]
  set x : ℝ := 2 * (resonanceRoot1 + h)
  have hxbig : 8 / 5 < x := by
    dsimp [x]; linarith [four_fifths_lt_resonanceRoot1]
  have hxπ : x < π := by
    dsimp [x]; linarith [resonanceRoot1_sharp_bounds.2, pi_gt_three, hh1]
  have hmemL : (8 / 5 : ℝ) ∈ Icc (0 : ℝ) π := ⟨by norm_num, by linarith [pi_gt_three]⟩
  have hmemx : x ∈ Icc (0 : ℝ) π :=
    ⟨by dsimp [x]; linarith [resonanceRoot1_bounds.1], hxπ.le⟩
  have hγx : gammaSEqual x < gammaSEqual (8 / 5) :=
    strictAntiOn_gammaSEqual_even 0 (by simpa using hmemL) (by simpa using hmemx) hxbig
  have hγlt : gammaSEqual x < -1 := by linarith [hγx, gammaSEqual_eight_fifths_lt]
  have harg : x / 2 = resonanceRoot1 + h := by dsimp [x]; ring
  have hhalf_gt : -(10 * h) < gammaSEqual (x / 2) := by
    rw [harg]; linarith [hsmall]
  have hhalf_lt : gammaSEqual (x / 2) < 0 := by
    rw [harg]
    exact gammaSEqual_neg_right_of_first_node ⟨lt_add_of_pos_right _ hh0,
      by linarith [resonanceRoot1_sharp_bounds.2, hh1, pi_gt_three]⟩
  have hratio : 1 / (10 * h) < gammaSEqual x / gammaSEqual (x / 2) := by
    rw [lt_div_iff_of_neg hhalf_lt]
    have hright : -1 < (1 / (10 * h)) * gammaSEqual (x / 2) := by
      have hid : (1 / (10 * h)) * (-(10 * h)) = -1 := by field_simp [hh0.ne']
      nlinarith [hhalf_gt, hid, hh0]
    linarith [hγlt]
  have hquarter : Z < (1 / 4) * (gammaSEqual x / gammaSEqual (x / 2)) := by
    have hlt : (1 / 4) * (1 / (10 * h)) < (1 / 4) * (gammaSEqual x / gammaSEqual (x / 2)) := by
      exact mul_lt_mul_of_pos_left hratio (by norm_num)
    have hZeq : Z = (1 / 4) * (1 / (10 * h)) := by
      rw [hh]; field_simp; ring
    linarith
  have hsame : x / 2 = (1 / 2) * x := by ring
  have hquarter' : Z < (1 / 4) * scaledRatio (1 / 2) x := by
    unfold scaledRatio
    rw [← hsame]
    linarith [hquarter]
  have hshell : x ∈ Ioo (2 * resonanceRoot1) (branchNode 1) := by
    refine ⟨by dsimp [x]; linarith, ?_⟩
    have hnode : π < branchNode 1 := by
      simpa [Nat.cast_one, one_mul] using (branchNode_spec 1).1.1
    dsimp [x]; linarith [hxπ, hnode]
  have hphases := octa_phases_in_shell hshell
  have hedge : 0 < sqrt 2 * scaledRatio octaEdge x := by
    unfold scaledRatio
    exact mul_pos (sqrt_pos.mpr (by norm_num))
      (div_pos_of_neg_of_neg hphases.1 hphases.2.1)
  unfold octaResponse
  linarith [hquarter', hedge]

lemma octaResponse_thirtyNine_tenths_lt : octaResponse (39 / 10) < 1 := by
  have hopp : gammaSEqual (39 / 20) < -4 := gammaSEqual_thirtyNine_twentieths_lt
  have hgx : -3 / 2 < gammaSEqual (39 / 10) := gammaSEqual_thirtyNine_tenths_gt
  have hgx0 : gammaSEqual (39 / 10) < 0 := by
    have hmem : (39 / 10 : ℝ) ∈ Ioo (2 * resonanceRoot1) (branchNode 1) := by
      refine ⟨by linarith [resonanceRoot1_sharp_bounds.2], branchNode_one_gt_thirtyNine_tenths⟩
    exact (octa_phases_in_shell hmem).1
  have hrop : gammaSEqual (39 / 10) / gammaSEqual (39 / 20) < 1 / 2 := by
    have hneg : gammaSEqual (39 / 20) < 0 := by linarith
    rw [div_lt_iff_of_neg hneg]
    have hhalf : (1 / 2) * gammaSEqual (39 / 20) < -2 := by nlinarith
    linarith [hgx]
  have hedge_lo : 11 / 5 < octaEdge * (39 / 10) := by
    have h2 : 7 / 5 < sqrt 2 := by
      rw [← sqrt_sq (by norm_num : (0 : ℝ) ≤ 7 / 5), sqrt_lt_sqrt_iff (by positivity)]
      norm_num
    unfold octaEdge
    nlinarith
  have hedge_hi : octaEdge * (39 / 10) < π := by
    have h2 : sqrt 2 < 99 / 70 := sqrt_two_bounds.2
    have hπ : (3861 / 1400 : ℝ) < π := by linarith [pi_gt_three]
    unfold octaEdge
    nlinarith
  have hγe : gammaSEqual (octaEdge * (39 / 10)) < gammaSEqual (11 / 5) := by
    have hleft : (11 / 5 : ℝ) ∈ Icc (0 : ℝ) π := ⟨by norm_num, by linarith [pi_gt_three]⟩
    have hright : octaEdge * (39 / 10) ∈ Icc (0 : ℝ) π :=
      ⟨by linarith [hedge_lo], hedge_hi.le⟩
    exact strictAntiOn_gammaSEqual_even 0 (by simpa using hleft)
      (by simpa using hright) hedge_lo
  have hγe6 : gammaSEqual (octaEdge * (39 / 10)) < -6 := by
    linarith [hγe, gammaSEqual_eleven_fifths_lt]
  have hre : gammaSEqual (39 / 10) / gammaSEqual (octaEdge * (39 / 10)) < 1 / 2 := by
    have hneg : gammaSEqual (octaEdge * (39 / 10)) < 0 := by linarith
    rw [div_lt_iff_of_neg hneg]
    have hhalf : (1 / 2) * gammaSEqual (octaEdge * (39 / 10)) < -3 := by nlinarith
    linarith [hgx]
  have hsqrt : sqrt 2 / 2 < 7 / 8 := by
    have h2 : sqrt 2 < 7 / 4 := sqrt_two_lt_seven_quarters
    nlinarith
  have hposE : 0 < gammaSEqual (39 / 10) / gammaSEqual (octaEdge * (39 / 10)) :=
    div_pos_of_neg_of_neg hgx0 (by linarith)
  have hposH : 0 < gammaSEqual (39 / 10) / gammaSEqual (39 / 20) :=
    div_pos_of_neg_of_neg hgx0 (by linarith)
  have hpe : sqrt 2 * (gammaSEqual (39 / 10) / gammaSEqual (octaEdge * (39 / 10))) <
      7 / 8 := by
    have h1 : sqrt 2 * (gammaSEqual (39 / 10) / gammaSEqual (octaEdge * (39 / 10))) <
        sqrt 2 * (1 / 2) := mul_lt_mul_of_pos_left hre (sqrt_pos.mpr (by norm_num))
    have heq : sqrt 2 * (1 / 2) = sqrt 2 / 2 := by ring
    linarith [h1, heq, hsqrt]
  have hph : (1 / 4) * (gammaSEqual (39 / 10) / gammaSEqual (39 / 20)) < 1 / 8 := by
    have h1 := mul_lt_mul_of_pos_left hrop (by norm_num : (0 : ℝ) < 1 / 4)
    have heq : (1 / 4) * (1 / 2) = (1 / 8 : ℝ) := by norm_num
    linarith
  unfold octaResponse scaledRatio
  have hhalf_same : gammaSEqual ((1 / 2) * (39 / 10)) = gammaSEqual (39 / 20) := by
    congr 1
    norm_num
  rw [hhalf_same]
  linarith [hpe, hph]

theorem octaOutward_sign {Z x : ℝ}
    (hx : x ∈ Ioo (2 * resonanceRoot1) (branchNode 1)) :
    octaOutward Z x < 0 ↔ Z < octaResponse x := by
  have hphases := octa_phases_in_shell hx
  rw [octaOutward_eq_response hphases.1.ne hphases.2.1.ne hphases.2.2.ne]
  have hden : gammaSEqual x < 0 := hphases.1
  constructor
  · intro h
    have : octaResponse x - Z > 0 := by
      rw [div_lt_iff_of_neg hden] at h
      linarith
    linarith
  · intro h
    rw [div_lt_iff_of_neg hden]
    linarith

theorem octaOutward_restores {Z x y : ℝ}
    (hx : x ∈ Ioo (2 * resonanceRoot1) (branchNode 1))
    (hy : y ∈ Ioo (2 * resonanceRoot1) (branchNode 1))
    (h0 : octaOutward Z y = 0) :
    (x < y → octaOutward Z x < 0) ∧ (y < x → 0 < octaOutward Z x) := by
  have hyR : octaResponse y = Z := octaResponse_of_outward hy h0
  constructor
  · intro hlt
    exact (octaOutward_sign hx).mpr (by linarith [octaResponse_strictAnti hx hy hlt, hyR])
  · intro hlt
    have hnum : octaResponse x - Z < 0 := by
      linarith [octaResponse_strictAnti hy hx hlt, hyR]
    have hphases := octa_phases_in_shell hx
    rw [octaOutward_eq_response hphases.1.ne hphases.2.1.ne hphases.2.2.ne]
    exact div_pos_of_neg_of_neg hnum hphases.1

/-- For every nuclear charge `Z ≥ 1`, six electrons at the vertices of a
regular octahedron have exactly one radial balance in the window where the
radius, the edge, and the opposite vertex all lie in the first repulsive shell. -/
theorem exists_unique_octa_shell {Z : ℝ} (hZ : 1 ≤ Z) :
    ∃! x : ℝ, x ∈ Ioo (2 * resonanceRoot1) (branchNode 1) ∧ octaOutward Z x = 0 := by
  have hZ0 : 0 < Z := by linarith
  set xL : ℝ := 2 * (resonanceRoot1 + 1 / (40 * Z))
  set xR : ℝ := 39 / 10
  have hgt : Z < octaResponse xL := by
    simpa [xL] using octaResponse_gt_near_outer hZ
  have hlt : octaResponse xR < Z := by
    have h1 : octaResponse xR < 1 := by simpa [xR] using octaResponse_thirtyNine_tenths_lt
    linarith
  have hxL_hi : xL < xR := by
    dsimp [xL, xR]
    have hh : 1 / (40 * Z) ≤ 1 / 40 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    linarith [resonanceRoot1_sharp_bounds.2]
  have hRmem : xR ∈ Ioo (2 * resonanceRoot1) (branchNode 1) := by
    dsimp [xR]
    exact ⟨by linarith [resonanceRoot1_sharp_bounds.2], branchNode_one_gt_thirtyNine_tenths⟩
  have hxL_lo : 2 * resonanceRoot1 < xL := by
    dsimp [xL]
    have : 0 < 1 / (40 * Z) := by positivity
    linarith
  have hcont : ContinuousOn (fun t => Z - octaResponse t) (Icc xL xR) := by
    refine ContinuousOn.sub continuousOn_const ?_
    refine continuousOn_octaResponse.mono ?_
    intro t ht
    exact ⟨lt_of_lt_of_le hxL_lo ht.1, lt_of_le_of_lt ht.2 hRmem.2⟩
  have hleft : (fun t => Z - octaResponse t) xL < 0 := by
    simpa using sub_neg.mpr hgt
  have hright : 0 < (fun t => Z - octaResponse t) xR := by
    simpa using sub_pos.mpr hlt
  obtain ⟨x, hxI, hx0⟩ := intermediate_value_Ioo (le_of_lt hxL_hi) hcont ⟨hleft, hright⟩
  have hxmem : x ∈ Ioo (2 * resonanceRoot1) (branchNode 1) :=
    ⟨lt_trans hxL_lo hxI.1, lt_trans hxI.2 hRmem.2⟩
  have hzero : octaOutward Z x = 0 := by
    have hphases := octa_phases_in_shell hxmem
    rw [octaOutward_eq_response hphases.1.ne hphases.2.1.ne hphases.2.2.ne]
    have hresp : octaResponse x = Z := by linarith [hx0]
    rw [hresp]
    field_simp [hphases.1.ne]
    ring
  refine ⟨x, ⟨hxmem, hzero⟩, ?_⟩
  intro y hy
  have hxR := octaResponse_of_outward hxmem hzero
  have hyR := octaResponse_of_outward hy.1 hy.2
  exact (octaResponse_strictAnti.injOn hxmem hy.1 (by rw [hxR, hyR])).symm

end Gravity

end DstDiophantine
