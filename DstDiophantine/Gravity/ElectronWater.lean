import DstDiophantine.Gravity.ElectronBoundary
import DstDiophantine.Gravity.ElectronForce
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The water skeleton

## Paper boundary (do **not** claim)

The length `ℓ` is not derived. Nothing here produces a bond angle, a
dissociation energy, a value of `a₀`, or a lone pair. The skeleton is one
electron on each of two rays, not a shell of eight and not the cube.
No equilibrium is claimed in the reversed shell, and none is claimed once a
second electron is added to a ray.

## What is proved

* While the electron–electron and proton–proton separations lie in the outer
  well and the cross factor is not a node, the tangential force on the
  electron and the tangential force on its proton do not vanish together at
  any angle strictly between ray coincidence and a straight line. The
  electron and the proton on one ray are distinct. The nuclear charge does
  not enter.
* On a straight line, with each electron between the nucleus and its proton
  and with both nucleus distances in the outer well, the outward force on the
  electron plus the outward force on the proton is strictly negative whenever
  the nuclear charge is at least `1/4` and the factor on the segment between
  them is not a node. Distances are in units of `ℓ`.
-/

namespace DstDiophantine.Gravity

noncomputable section

open Real Set

/-! ### Derivative of the critical numerator -/

private theorem hasDerivAt_forceCrit_local (x : ℝ) :
    HasDerivAt forceCrit ((x * sinh x - cosh x) * sin x + x * cosh x * cos x) x := by
  unfold forceCrit
  have hmul : HasDerivAt (fun y : ℝ => y * cosh y * sin y)
      (cosh x * sin x + x * sinh x * sin x + x * cosh x * cos x) x := by
    have h := ((hasDerivAt_id x).mul (Real.hasDerivAt_cosh x)).mul (hasDerivAt_sin x)
    refine h.congr_deriv ?_
    simp only [id_eq, Pi.mul_apply]
    ring
  have h := (hasDerivAt_gammaSEqual x).add hmul
  refine h.congr_deriv ?_
  ring

private theorem continuous_forceCrit_local : Continuous forceCrit := by
  unfold forceCrit
  exact continuous_gammaSEqual.add ((continuous_id.mul continuous_cosh).mul continuous_sin)

/-- Numerator of the derivative of `forceCrit / γ_s²` on the outer well. -/
private def slopeNumer (x : ℝ) : ℝ :=
  x * (cosh x ^ 2 + sin x ^ 2 * (2 * cosh x ^ 2 + 1)) +
    3 * sin x * cosh x * gammaSEqual x

private theorem slopeNumer_eq (x : ℝ) :
    ((x * sinh x - cosh x) * sin x + x * cosh x * cos x) * gammaSEqual x -
        2 * forceCrit x * (-2 * cosh x * sin x) =
      slopeNumer x := by
  unfold slopeNumer forceCrit gammaSEqual
  have hch : cosh x ^ 2 = sinh x ^ 2 + 1 := cosh_sq x
  have hsc : cos x ^ 2 = 1 - sin x ^ 2 := by
    have h := sin_sq_add_cos_sq x
    linarith
  ring_nf
  rw [hch, hsc]
  ring

private theorem slopeNumer_pos {x : ℝ} (hx : x ∈ Ioo 0 resonanceRoot1) :
    0 < slopeNumer x := by
  have hsin : 0 < sin x :=
    sin_pos_of_pos_of_lt_pi hx.1
      (lt_trans hx.2 (lt_trans resonanceRoot1_sharp_bounds.2 (by linarith [pi_gt_three])))
  have hγ : 0 < gammaSEqual x := gammaSEqual_pos_left_of_first_node hx
  have hc : 0 < cosh x := cosh_pos x
  unfold slopeNumer
  have hinner : 0 < cosh x ^ 2 + sin x ^ 2 * (2 * cosh x ^ 2 + 1) := by
    have hcosh2 : 0 < cosh x ^ 2 := sq_pos_of_pos hc
    have hrest : 0 ≤ sin x ^ 2 * (2 * cosh x ^ 2 + 1) := by positivity
    linarith
  have h1 : 0 < x * (cosh x ^ 2 + sin x ^ 2 * (2 * cosh x ^ 2 + 1)) :=
    mul_pos hx.1 hinner
  have h2 : 0 < 3 * sin x * cosh x * gammaSEqual x := by positivity
  linarith

/-- `forceCrit / γ_s²`, strictly increasing on the outer well. -/
private def forceSlope (x : ℝ) : ℝ :=
  forceCrit x / gammaSEqual x ^ 2

private theorem hasDerivAt_forceSlope {x : ℝ} (hγ : gammaSEqual x ≠ 0) :
    HasDerivAt forceSlope (slopeNumer x / gammaSEqual x ^ 3) x := by
  unfold forceSlope
  have hγ2 : HasDerivAt (fun y : ℝ => gammaSEqual y ^ 2)
      (2 * gammaSEqual x * (-2 * cosh x * sin x)) x := by
    have h := (hasDerivAt_gammaSEqual x).pow 2
    refine h.congr_deriv ?_
    simp only [Nat.cast_ofNat]
    ring
  have hdiv := (hasDerivAt_forceCrit_local x).fun_div hγ2 (pow_ne_zero 2 hγ)
  refine hdiv.congr_deriv ?_
  have hN := slopeNumer_eq x
  have hnum :
      ((x * sinh x - cosh x) * sin x + x * cosh x * cos x) * gammaSEqual x ^ 2 -
          forceCrit x * (2 * gammaSEqual x * (-2 * cosh x * sin x)) =
        gammaSEqual x * slopeNumer x := by
    calc
      ((x * sinh x - cosh x) * sin x + x * cosh x * cos x) * gammaSEqual x ^ 2 -
            forceCrit x * (2 * gammaSEqual x * (-2 * cosh x * sin x)) =
          gammaSEqual x * (((x * sinh x - cosh x) * sin x + x * cosh x * cos x) *
              gammaSEqual x - 2 * forceCrit x * (-2 * cosh x * sin x)) := by ring
      _ = gammaSEqual x * slopeNumer x := by rw [hN]
  calc
    (((x * sinh x - cosh x) * sin x + x * cosh x * cos x) * gammaSEqual x ^ 2 -
          forceCrit x * (2 * gammaSEqual x * (-2 * cosh x * sin x))) /
        (gammaSEqual x ^ 2) ^ 2 =
      (gammaSEqual x * slopeNumer x) / (gammaSEqual x ^ 2) ^ 2 := by rw [hnum]
    _ = slopeNumer x / gammaSEqual x ^ 3 := by field_simp [hγ]

private theorem continuousOn_forceSlope :
    ContinuousOn forceSlope (Ioo 0 resonanceRoot1) := by
  refine ContinuousOn.div continuous_forceCrit_local.continuousOn ?_ ?_
  · exact (continuous_gammaSEqual.pow 2).continuousOn
  · intro x hx
    exact pow_ne_zero 2 (gammaSEqual_pos_left_of_first_node hx).ne'

private theorem forceSlope_strictMono :
    StrictMonoOn forceSlope (Ioo 0 resonanceRoot1) := by
  refine strictMonoOn_of_deriv_pos (convex_Ioo 0 resonanceRoot1) continuousOn_forceSlope ?_
  intro x hx
  rw [interior_Ioo] at hx
  have hγ : gammaSEqual x ≠ 0 := (gammaSEqual_pos_left_of_first_node hx).ne'
  rw [(hasDerivAt_forceSlope hγ).deriv]
  exact div_pos (slopeNumer_pos hx) (pow_pos (gammaSEqual_pos_left_of_first_node hx) 3)

/-! ### Phase weight `x²/γ_s` -/

/-- `x²/γ_s(x)`. The attraction-positive force is four times this weight. -/
private def waterWeight (x : ℝ) : ℝ :=
  x ^ 2 / gammaSEqual x

private theorem pairAttraction_eq_four_waterWeight (x : ℝ) :
    pairAttraction x = 4 * waterWeight x := by
  unfold pairAttraction waterWeight
  ring

private theorem hasDerivAt_waterWeight {x : ℝ} (hγ : gammaSEqual x ≠ 0) :
    HasDerivAt waterWeight (2 * x * forceSlope x) x := by
  unfold waterWeight
  have hsq : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
    simpa [pow_one] using hasDerivAt_pow 2 x
  have hdiv := hsq.fun_div (hasDerivAt_gammaSEqual x) hγ
  refine hdiv.congr_deriv ?_
  unfold forceSlope forceCrit
  ring

private theorem continuousOn_waterWeight :
    ContinuousOn waterWeight (Ioo 0 resonanceRoot1) := by
  refine ContinuousOn.div ?_ continuous_gammaSEqual.continuousOn ?_
  · exact (continuous_id.pow 2).continuousOn
  · intro x hx
    exact (gammaSEqual_pos_left_of_first_node hx).ne'

private theorem waterWeight_strictMono :
    StrictMonoOn waterWeight (Ioo 0 resonanceRoot1) := by
  refine strictMonoOn_of_deriv_pos (convex_Ioo 0 resonanceRoot1) continuousOn_waterWeight ?_
  intro x hx
  rw [interior_Ioo] at hx
  have hγ : gammaSEqual x ≠ 0 := (gammaSEqual_pos_left_of_first_node hx).ne'
  rw [(hasDerivAt_waterWeight hγ).deriv]
  unfold forceSlope
  exact mul_pos (mul_pos (by norm_num) hx.1)
    (div_pos (forceCrit_pos_outer hx)
      (sq_pos_of_pos (gammaSEqual_pos_left_of_first_node hx)))

/-- `ψ(s) - 4 ψ(s/2)`. Positive growth of this gap is the quarter bound. -/
private def halfGap (s : ℝ) : ℝ :=
  waterWeight s - 4 * waterWeight (s / 2)

private theorem hasDerivAt_halfGap {s : ℝ}
    (hs : gammaSEqual s ≠ 0) (hh : gammaSEqual (s / 2) ≠ 0) :
    HasDerivAt halfGap (2 * s * (forceSlope s - forceSlope (s / 2))) s := by
  have h1 := hasDerivAt_waterWeight hs
  have hlin : HasDerivAt (fun t : ℝ => t / 2) ((1 : ℝ) / 2) s :=
    (hasDerivAt_id s).div_const 2
  have h2 := (hasDerivAt_waterWeight hh).comp s hlin
  have h := h1.sub (h2.const_mul 4)
  refine h.congr_deriv ?_
  unfold forceSlope
  ring

private theorem continuousOn_halfGap :
    ContinuousOn halfGap (Ioo 0 resonanceRoot1) := by
  have hmap : MapsTo (fun s : ℝ => s / 2) (Ioo 0 resonanceRoot1) (Ioo 0 resonanceRoot1) := by
    intro s hs
    exact ⟨by linarith [hs.1], by linarith [hs.1, hs.2]⟩
  unfold halfGap
  exact continuousOn_waterWeight.sub
    ((continuousOn_waterWeight.comp (continuous_id.div_const 2).continuousOn hmap).const_mul 4)

private theorem halfGap_strictMono :
    StrictMonoOn halfGap (Ioo 0 resonanceRoot1) := by
  refine strictMonoOn_of_deriv_pos (convex_Ioo 0 resonanceRoot1) continuousOn_halfGap ?_
  intro s hs
  rw [interior_Ioo] at hs
  have hs2 : s / 2 ∈ Ioo 0 resonanceRoot1 :=
    ⟨by linarith [hs.1], by linarith [hs.1, hs.2]⟩
  have hγs : gammaSEqual s ≠ 0 := (gammaSEqual_pos_left_of_first_node hs).ne'
  have hγ2 : gammaSEqual (s / 2) ≠ 0 := (gammaSEqual_pos_left_of_first_node hs2).ne'
  rw [(hasDerivAt_halfGap hγs hγ2).deriv]
  have hμ : forceSlope (s / 2) < forceSlope s :=
    forceSlope_strictMono hs2 hs (by linarith [hs.1])
  nlinarith [hs.1, hμ]

private theorem half_lt_harmonic {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (hxy : y < x) :
    y / 2 < x * y / (x + y) ∧ x * y / (x + y) < x / 2 := by
  have hsum : 0 < x + y := by linarith
  refine ⟨?_, ?_⟩
  · have : y * (x + y) < x * y * 2 := by nlinarith
    exact (div_lt_div_iff₀ (by norm_num : (0 : ℝ) < 2) hsum).mpr this
  · have : x * y * 2 < x * (x + y) := by nlinarith
    exact (div_lt_div_iff₀ hsum (by norm_num : (0 : ℝ) < 2)).mpr this

private theorem waterWeight_quarter_gap {x y : ℝ}
    (hy : 0 < y) (hxy : y < x) (hx : x < resonanceRoot1) :
    4 * (waterWeight (x / 2) + waterWeight (y / 2) - 2 * waterWeight (x * y / (x + y))) <
      waterWeight x - waterWeight y := by
  have hx0 : 0 < x := lt_trans hy hxy
  have hxI : x ∈ Ioo 0 resonanceRoot1 := ⟨hx0, hx⟩
  have hyI : y ∈ Ioo 0 resonanceRoot1 := ⟨hy, lt_trans hxy hx⟩
  have hmono := halfGap_strictMono hyI hxI hxy
  have hord := half_lt_harmonic hx0 hy hxy
  have hy2I : y / 2 ∈ Ioo 0 resonanceRoot1 := ⟨by linarith [hy], by linarith [hy, hxy, hx]⟩
  have hhI : x * y / (x + y) ∈ Ioo 0 resonanceRoot1 :=
    ⟨lt_trans (by linarith [hy]) hord.1, lt_trans hord.2 (by linarith [hx0, hx])⟩
  have hψ := waterWeight_strictMono hy2I hhI hord.1
  unfold halfGap at hmono
  nlinarith [hmono, hψ]

private theorem quarter_bracket_neg {Z x y : ℝ}
    (hZ : (1 / 4 : ℝ) ≤ Z) (hy : 0 < y) (hxy : y < x) (hx : x < resonanceRoot1) :
    Z * (waterWeight y - waterWeight x) + waterWeight (x / 2) + waterWeight (y / 2) -
        2 * waterWeight (x * y / (x + y)) < 0 := by
  have hgap := waterWeight_quarter_gap hy hxy hx
  have hx0 : 0 < x := lt_trans hy hxy
  have hψ : waterWeight y < waterWeight x :=
    waterWeight_strictMono ⟨hy, lt_trans hxy hx⟩ ⟨hx0, hx⟩ hxy
  have hdiff : 0 < waterWeight x - waterWeight y := sub_pos.mpr hψ
  have hb : waterWeight (x / 2) + waterWeight (y / 2) -
      2 * waterWeight (x * y / (x + y)) <
      (1 / 4) * (waterWeight x - waterWeight y) := by
    linarith
  have hmul : (1 / 4) * (waterWeight x - waterWeight y) ≤
      Z * (waterWeight x - waterWeight y) :=
    mul_le_mul_of_nonneg_right hZ hdiff.le
  have hbZ : waterWeight (x / 2) + waterWeight (y / 2) -
      2 * waterWeight (x * y / (x + y)) <
      Z * (waterWeight x - waterWeight y) :=
    lt_of_lt_of_le hb hmul
  have hre : Z * (waterWeight y - waterWeight x) + waterWeight (x / 2) +
      waterWeight (y / 2) - 2 * waterWeight (x * y / (x + y)) =
      (waterWeight (x / 2) + waterWeight (y / 2) -
        2 * waterWeight (x * y / (x + y))) -
      Z * (waterWeight x - waterWeight y) := by
    ring
  rw [hre]
  exact sub_neg.mpr hbZ

/-! ### Pair force and the straight skeleton -/

/-- Separation-increasing force on charge `qi` at `ri` from charge `qj` at `rj`,
in units of `k e²`, with `ℓ = 1`. -/
def pairForce (qi qj : ℝ) (ri rj : Fin 3 → ℝ) (i : Fin 3) : ℝ :=
  qi * qj * (ri i - rj i) /
    (gammaSEqual (pairPhase (vnorm (vsub ri rj))) * vnorm (vsub ri rj) ^ 3)

/-- A point on the first coordinate axis. -/
def axisPoint (s : ℝ) : Fin 3 → ℝ :=
  ![s, 0, 0]

@[simp] theorem axisPoint_zero (s : ℝ) : axisPoint s 0 = s := rfl

@[simp] theorem axisPoint_one (s : ℝ) : axisPoint s 1 = 0 := rfl

@[simp] theorem axisPoint_two (s : ℝ) : axisPoint s 2 = 0 := rfl

private theorem vnorm_axis_sub (s t : ℝ) :
    vnorm (vsub (axisPoint s) (axisPoint t)) = |s - t| := by
  unfold vnorm vnorm2 vdot vsub
  simp only [axisPoint_zero, axisPoint_one, axisPoint_two]
  have hsq : (s - t) * (s - t) + (0 - 0) * (0 - 0) + (0 - 0) * (0 - 0) =
      (s - t) ^ 2 := by ring
  rw [hsq, sqrt_sq_eq_abs]

private theorem pairForce_axis_out {qi qj s t : ℝ} (hst : t < s)
    (_hγ : gammaSEqual (pairPhase (s - t)) ≠ 0) :
    pairForce qi qj (axisPoint s) (axisPoint t) 0 =
      qi * qj * pairAttraction (pairPhase (s - t)) := by
  have hpos : 0 < s - t := sub_pos.mpr hst
  unfold pairForce pairAttraction pairPhase
  have hv : vnorm (vsub (axisPoint s) (axisPoint t)) = s - t := by
    rw [vnorm_axis_sub, abs_of_pos hpos]
  rw [hv, axisPoint_zero, axisPoint_zero]
  have hne : s - t ≠ 0 := hpos.ne'
  field_simp [_hγ, hne]
  ring

private theorem pairForce_axis_in {qi qj s t : ℝ} (hst : s < t)
    (_hγ : gammaSEqual (pairPhase (t - s)) ≠ 0) :
    pairForce qi qj (axisPoint s) (axisPoint t) 0 =
      -(qi * qj * pairAttraction (pairPhase (t - s))) := by
  have hpos : 0 < t - s := sub_pos.mpr hst
  unfold pairForce pairAttraction pairPhase
  have hv : vnorm (vsub (axisPoint s) (axisPoint t)) = t - s := by
    rw [vnorm_axis_sub, abs_of_neg (sub_neg.mpr hst)]
    ring
  rw [hv, axisPoint_zero, axisPoint_zero]
  have hne : t - s ≠ 0 := hpos.ne'
  field_simp [_hγ, hne]
  ring

/-- Outward force on the electron of a straight water skeleton.
The nucleus is at the origin, the electron at `+r`, its proton at `+R`. -/
def waterStraightElectron (Z r R : ℝ) : ℝ :=
  pairForce (-1) Z (axisPoint r) (axisPoint 0) 0 +
    pairForce (-1) 1 (axisPoint r) (axisPoint R) 0 +
    pairForce (-1) (-1) (axisPoint r) (axisPoint (-r)) 0 +
    pairForce (-1) 1 (axisPoint r) (axisPoint (-R)) 0

/-- Outward force on the proton of a straight water skeleton. -/
def waterStraightProton (Z r R : ℝ) : ℝ :=
  pairForce 1 Z (axisPoint R) (axisPoint 0) 0 +
    pairForce 1 (-1) (axisPoint R) (axisPoint r) 0 +
    pairForce 1 1 (axisPoint R) (axisPoint (-R)) 0 +
    pairForce 1 (-1) (axisPoint R) (axisPoint (-r)) 0

private theorem phase_half_mem {d : ℝ} (hd : outerSep d) :
    pairPhase (2 * d) ∈ Ioo 0 resonanceRoot1 := by
  have hφ : 0 < pairPhase d := by
    unfold pairPhase
    exact div_pos (by norm_num) (by linarith [hd.1])
  have hlt : pairPhase (2 * d) < pairPhase d := by
    unfold pairPhase
    have h2 : 0 < 2 * d := by linarith [hd.1]
    have hd2 : 0 < 2 * (2 * d) := by linarith
    have hcmp : 2 * d < 2 * (2 * d) := by linarith
    exact div_lt_div_of_pos_left (by norm_num) h2 hcmp
  exact ⟨by
    unfold pairPhase
    exact div_pos (by norm_num) (by linarith [hd.1]), lt_trans hlt hd.2⟩

private theorem phase_sum_mem {r R : ℝ} (hr : outerSep r) (hR : 0 < R) :
    pairPhase (R + r) ∈ Ioo 0 resonanceRoot1 := by
  have hsum : 0 < R + r := by linarith [hr.1, hR]
  have hlt : pairPhase (R + r) < pairPhase r := by
    unfold pairPhase
    have hr2 : 0 < 2 * r := by linarith [hr.1]
    have hs2 : 0 < 2 * (R + r) := by linarith
    have hcmp : 2 * r < 2 * (R + r) := by linarith
    exact div_lt_div_of_pos_left (by norm_num) hr2 hcmp
  exact ⟨by
    unfold pairPhase
    exact div_pos (by norm_num) (by linarith), lt_trans hlt hr.2⟩

private theorem pairPhase_two {d : ℝ} (hd : d ≠ 0) :
    pairPhase (2 * d) = pairPhase d / 2 := by
  unfold pairPhase
  field_simp [hd]

private theorem pairPhase_add {r R : ℝ} (hr : r ≠ 0) (hR : R ≠ 0) (hsum : R + r ≠ 0) :
    pairPhase (R + r) = pairPhase r * pairPhase R / (pairPhase r + pairPhase R) := by
  unfold pairPhase
  field_simp [hr, hR, hsum]

/-- On the straight skeleton the sum of the outward forces is negative for
every nuclear charge at least `1/4`. -/
theorem water_straight_sum_neg {Z r R : ℝ}
    (hZ : (1 / 4 : ℝ) ≤ Z) (hr : outerSep r) (hR : outerSep R) (hrR : r < R)
    (hgap : gammaSEqual (pairPhase (R - r)) ≠ 0) :
    waterStraightElectron Z r R + waterStraightProton Z r R < 0 := by
  have hr0 : 0 < r := hr.1
  have hR0 : 0 < R := hR.1
  have hgap0 : 0 < R - r := sub_pos.mpr hrR
  have hγr : gammaSEqual (pairPhase r) ≠ 0 := (outer_gamma_pos hr).ne'
  have hγR : gammaSEqual (pairPhase R) ≠ 0 := (outer_gamma_pos hR).ne'
  have h2r : pairPhase (2 * r) ∈ Ioo 0 resonanceRoot1 := phase_half_mem hr
  have h2R : pairPhase (2 * R) ∈ Ioo 0 resonanceRoot1 := phase_half_mem hR
  have hsumφ : pairPhase (R + r) ∈ Ioo 0 resonanceRoot1 := phase_sum_mem hr hR0
  have hγ2r : gammaSEqual (pairPhase (2 * r)) ≠ 0 :=
    (gammaSEqual_pos_left_of_first_node h2r).ne'
  have hγ2R : gammaSEqual (pairPhase (2 * R)) ≠ 0 :=
    (gammaSEqual_pos_left_of_first_node h2R).ne'
  have hγsum : gammaSEqual (pairPhase (R + r)) ≠ 0 :=
    (gammaSEqual_pos_left_of_first_node hsumφ).ne'
  have hnr : -r < r := by linarith
  have hnR : -R < r := by linarith
  have hnRp : -R < R := by linarith
  have hnrR : -r < R := by linarith
  have hE : waterStraightElectron Z r R =
      -Z * pairAttraction (pairPhase r) + pairAttraction (pairPhase (R - r)) +
        pairAttraction (pairPhase (2 * r)) - pairAttraction (pairPhase (R + r)) := by
    unfold waterStraightElectron
    have hγ0 : gammaSEqual (pairPhase (r - 0)) ≠ 0 := by
      rw [sub_zero]; exact hγr
    have hγ2 : gammaSEqual (pairPhase (r - -r)) ≠ 0 := by
      rw [sub_neg_eq_add, ← two_mul]; exact hγ2r
    have hγc : gammaSEqual (pairPhase (r - -R)) ≠ 0 := by
      rw [sub_neg_eq_add, add_comm]; exact hγsum
    rw [pairForce_axis_out (by linarith : (0 : ℝ) < r) hγ0]
    rw [pairForce_axis_in hrR hgap]
    rw [pairForce_axis_out hnr hγ2]
    rw [pairForce_axis_out hnR hγc]
    simp only [sub_zero, sub_neg_eq_add]
    rw [← two_mul, add_comm r R]
    ring
  have hH : waterStraightProton Z r R =
      Z * pairAttraction (pairPhase R) - pairAttraction (pairPhase (R - r)) +
        pairAttraction (pairPhase (2 * R)) - pairAttraction (pairPhase (R + r)) := by
    unfold waterStraightProton
    have hγ0 : gammaSEqual (pairPhase (R - 0)) ≠ 0 := by
      rw [sub_zero]; exact hγR
    have hγ2 : gammaSEqual (pairPhase (R - -R)) ≠ 0 := by
      rw [sub_neg_eq_add, ← two_mul]; exact hγ2R
    have hγc : gammaSEqual (pairPhase (R - -r)) ≠ 0 := by
      rw [sub_neg_eq_add]; exact hγsum
    rw [pairForce_axis_out hR0 hγ0]
    rw [pairForce_axis_out hrR hgap]
    rw [pairForce_axis_out hnRp hγ2]
    rw [pairForce_axis_out hnrR hγc]
    simp only [sub_zero, sub_neg_eq_add]
    rw [← two_mul]
    ring
  have hcancel : waterStraightElectron Z r R + waterStraightProton Z r R =
      Z * (pairAttraction (pairPhase R) - pairAttraction (pairPhase r)) +
        pairAttraction (pairPhase (2 * r)) + pairAttraction (pairPhase (2 * R)) -
        2 * pairAttraction (pairPhase (R + r)) := by
    rw [hE, hH]
    ring
  rw [hcancel]
  have hx2 : pairPhase (2 * r) = pairPhase r / 2 := pairPhase_two hr0.ne'
  have hy2 : pairPhase (2 * R) = pairPhase R / 2 := pairPhase_two hR0.ne'
  have hh : pairPhase (R + r) =
      pairPhase r * pairPhase R / (pairPhase r + pairPhase R) :=
    pairPhase_add hr0.ne' hR0.ne' (by linarith)
  rw [pairAttraction_eq_four_waterWeight, pairAttraction_eq_four_waterWeight,
    pairAttraction_eq_four_waterWeight, pairAttraction_eq_four_waterWeight,
    pairAttraction_eq_four_waterWeight, hx2, hy2, hh]
  set x : ℝ := pairPhase r
  set y : ℝ := pairPhase R
  have hy : 0 < y := by
    unfold y pairPhase
    exact div_pos (by norm_num) (by linarith)
  have hxy : y < x := by
    unfold x y pairPhase
    have hr2 : 0 < 2 * r := by linarith
    have hR2 : 0 < 2 * R := by linarith
    have hcmp : 2 * r < 2 * R := by linarith
    exact div_lt_div_of_pos_left (by norm_num) hr2 hcmp
  have hx1 : x < resonanceRoot1 := by
    unfold x
    exact hr.2
  have hbrack := quarter_bracket_neg hZ hy hxy hx1
  have h4 : (4 : ℝ) *
      (Z * (waterWeight y - waterWeight x) + waterWeight (x / 2) +
        waterWeight (y / 2) - 2 * waterWeight (x * y / (x + y))) < 0 :=
    mul_neg_of_pos_of_neg (by norm_num) hbrack
  have heq : Z * (4 * waterWeight y - 4 * waterWeight x) + 4 * waterWeight (x / 2) +
      4 * waterWeight (y / 2) - 2 * (4 * waterWeight (x * y / (x + y))) =
      4 * (Z * (waterWeight y - waterWeight x) + waterWeight (x / 2) +
        waterWeight (y / 2) - 2 * waterWeight (x * y / (x + y))) := by
    ring
  rw [heq]
  exact h4

/-! ### Bent skeleton: tangential components -/

/-- Unit vector of a ray at half-angle `a` from the positive third axis. -/
def waterU (a : ℝ) : Fin 3 → ℝ :=
  ![sin a, 0, cos a]

/-- The reflected ray. -/
def waterV (a : ℝ) : Fin 3 → ℝ :=
  ![-sin a, 0, cos a]

/-- Unit tangent `d/da` of `waterU`. -/
def waterT (a : ℝ) : Fin 3 → ℝ :=
  ![cos a, 0, -sin a]

@[simp] theorem waterU_zero (a : ℝ) : waterU a 0 = sin a := rfl
@[simp] theorem waterU_one (a : ℝ) : waterU a 1 = 0 := rfl
@[simp] theorem waterU_two (a : ℝ) : waterU a 2 = cos a := rfl
@[simp] theorem waterV_zero (a : ℝ) : waterV a 0 = -sin a := rfl
@[simp] theorem waterV_one (a : ℝ) : waterV a 1 = 0 := rfl
@[simp] theorem waterV_two (a : ℝ) : waterV a 2 = cos a := rfl
@[simp] theorem waterT_zero (a : ℝ) : waterT a 0 = cos a := rfl
@[simp] theorem waterT_one (a : ℝ) : waterT a 1 = 0 := rfl
@[simp] theorem waterT_two (a : ℝ) : waterT a 2 = -sin a := rfl

private theorem vdot_add (t u w : Fin 3 → ℝ) :
    vdot t (fun i => u i + w i) = vdot t u + vdot t w := by
  unfold vdot
  ring

private theorem vdot_pairForce (qi qj : ℝ) (ri rj t : Fin 3 → ℝ)
    (_hden : gammaSEqual (pairPhase (vnorm (vsub ri rj))) * vnorm (vsub ri rj) ^ 3 ≠ 0) :
    vdot t (fun i => pairForce qi qj ri rj i) =
      qi * qj * vdot t (vsub ri rj) /
        (gammaSEqual (pairPhase (vnorm (vsub ri rj))) * vnorm (vsub ri rj) ^ 3) := by
  unfold vdot pairForce
  field_simp [_hden]
  unfold vsub
  ring

private theorem vdot_pairForce_ortho {qi qj : ℝ} {ri rj t : Fin 3 → ℝ}
    (hdot : vdot t (vsub ri rj) = 0) :
    vdot t (fun i => pairForce qi qj ri rj i) = 0 := by
  by_cases hden : gammaSEqual (pairPhase (vnorm (vsub ri rj))) * vnorm (vsub ri rj) ^ 3 = 0
  · have h0 (i : Fin 3) : pairForce qi qj ri rj i = 0 := by
      unfold pairForce
      rw [hden, div_zero]
    unfold vdot
    simp [h0]
  · rw [vdot_pairForce qi qj ri rj t hden, hdot, mul_zero, zero_div]

private theorem vdot_T_nucleus (c a : ℝ) :
    vdot (waterT a) (vsmul c (waterU a)) = 0 := by
  unfold vdot vsmul
  simp only [waterT_zero, waterT_one, waterT_two, waterU_zero, waterU_one, waterU_two]
  ring

private theorem vdot_T_partner (r R a : ℝ) :
    vdot (waterT a) (vsub (vsmul r (waterU a)) (vsmul R (waterU a))) = 0 := by
  unfold vdot vsub vsmul
  simp only [waterT_zero, waterT_one, waterT_two, waterU_zero, waterU_one, waterU_two]
  ring

private theorem vdot_T_ee (r a : ℝ) :
    vdot (waterT a) (vsub (vsmul r (waterU a)) (vsmul r (waterV a))) =
      r * sin (2 * a) := by
  unfold vdot vsub vsmul
  simp only [waterT_zero, waterT_one, waterT_two, waterU_zero, waterU_one, waterU_two,
    waterV_zero, waterV_one, waterV_two]
  rw [sin_two_mul]
  ring

private theorem vdot_T_cross (r R a : ℝ) :
    vdot (waterT a) (vsub (vsmul r (waterU a)) (vsmul R (waterV a))) =
      R * sin (2 * a) := by
  unfold vdot vsub vsmul
  simp only [waterT_zero, waterT_one, waterT_two, waterU_zero, waterU_one, waterU_two,
    waterV_zero, waterV_one, waterV_two]
  rw [sin_two_mul]
  ring

private theorem vdot_T_hh (R a : ℝ) :
    vdot (waterT a) (vsub (vsmul R (waterU a)) (vsmul R (waterV a))) =
      R * sin (2 * a) := by
  unfold vdot vsub vsmul
  simp only [waterT_zero, waterT_one, waterT_two, waterU_zero, waterU_one, waterU_two,
    waterV_zero, waterV_one, waterV_two]
  rw [sin_two_mul]
  ring

private theorem vdot_T_pe (r R a : ℝ) :
    vdot (waterT a) (vsub (vsmul R (waterU a)) (vsmul r (waterV a))) =
      r * sin (2 * a) := by
  unfold vdot vsub vsmul
  simp only [waterT_zero, waterT_one, waterT_two, waterU_zero, waterU_one, waterU_two,
    waterV_zero, waterV_one, waterV_two]
  rw [sin_two_mul]
  ring

private theorem vnorm_ee (r a : ℝ) (hr : 0 < r) (ha : 0 < sin a) :
    vnorm (vsub (vsmul r (waterU a)) (vsmul r (waterV a))) = 2 * r * sin a := by
  unfold vnorm vnorm2 vdot vsub vsmul
  simp only [waterU_zero, waterU_one, waterU_two, waterV_zero, waterV_one, waterV_two]
  have hsq : (r * sin a - r * -sin a) * (r * sin a - r * -sin a) +
      (r * 0 - r * 0) * (r * 0 - r * 0) +
      (r * cos a - r * cos a) * (r * cos a - r * cos a) = (2 * r * sin a) ^ 2 := by ring
  rw [hsq, sqrt_sq_eq_abs, abs_of_pos (by nlinarith)]

private theorem vnorm_hh (R a : ℝ) (hR : 0 < R) (ha : 0 < sin a) :
    vnorm (vsub (vsmul R (waterU a)) (vsmul R (waterV a))) = 2 * R * sin a := by
  unfold vnorm vnorm2 vdot vsub vsmul
  simp only [waterU_zero, waterU_one, waterU_two, waterV_zero, waterV_one, waterV_two]
  have hsq : (R * sin a - R * -sin a) * (R * sin a - R * -sin a) +
      (R * 0 - R * 0) * (R * 0 - R * 0) +
      (R * cos a - R * cos a) * (R * cos a - R * cos a) = (2 * R * sin a) ^ 2 := by ring
  rw [hsq, sqrt_sq_eq_abs, abs_of_pos (by nlinarith)]

private theorem vnorm2_cross (r R a : ℝ) :
    vnorm2 (vsub (vsmul r (waterU a)) (vsmul R (waterV a))) =
      r ^ 2 + R ^ 2 - 2 * r * R * (cos a ^ 2 - sin a ^ 2) := by
  unfold vnorm2 vdot vsub vsmul
  simp only [waterU_zero, waterU_one, waterU_two, waterV_zero, waterV_one, waterV_two]
  have h := sin_sq_add_cos_sq a
  calc
    (r * sin a - R * -sin a) * (r * sin a - R * -sin a) +
          (r * 0 - R * 0) * (r * 0 - R * 0) +
          (r * cos a - R * cos a) * (r * cos a - R * cos a)
        = (r + R) ^ 2 * sin a ^ 2 + (r - R) ^ 2 * cos a ^ 2 := by ring
    _ = (r ^ 2 + R ^ 2) * (sin a ^ 2 + cos a ^ 2) +
          2 * r * R * (sin a ^ 2 - cos a ^ 2) := by ring
    _ = r ^ 2 + R ^ 2 - 2 * r * R * (cos a ^ 2 - sin a ^ 2) := by
      rw [h]
      ring

private theorem vnorm_cross_sym (r R a : ℝ) :
    vnorm (vsub (vsmul R (waterU a)) (vsmul r (waterV a))) =
      vnorm (vsub (vsmul r (waterU a)) (vsmul R (waterV a))) := by
  unfold vnorm
  congr 1
  unfold vnorm2 vdot vsub vsmul
  simp only [waterU_zero, waterU_one, waterU_two, waterV_zero, waterV_one, waterV_two]
  ring

private theorem cos_sq_sub_sin_sq (a : ℝ) :
    cos a ^ 2 - sin a ^ 2 = cos (2 * a) := by
  rw [cos_two_mul, sin_sq]
  ring

private theorem cross_sep_pos {r R θ : ℝ}
    (hr : 0 < r) (hR : 0 < R) (hθ : θ ∈ Ioo 0 π) :
    0 < r ^ 2 + R ^ 2 - 2 * r * R * cos θ := by
  have hsin : 0 < sin θ := sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  have hcos : cos θ < 1 := by
    by_contra h
    push Not at h
    have heq : cos θ = 1 := le_antisymm (cos_le_one θ) h
    have hsq : sin θ ^ 2 + cos θ ^ 2 = 1 := sin_sq_add_cos_sq θ
    rw [heq] at hsq
    have : sin θ ^ 2 = 0 := by linarith
    have : sin θ = 0 := by nlinarith
    linarith
  have hrest : 0 < 2 * r * R * (1 - cos θ) := by
    have h1 : 0 < 1 - cos θ := sub_pos.mpr hcos
    exact mul_pos (by nlinarith) h1
  have hid : r ^ 2 + R ^ 2 - 2 * r * R * cos θ =
      (r - R) ^ 2 + 2 * r * R * (1 - cos θ) := by ring
  linarith [sq_nonneg (r - R), hid]

/-- Tangential component of the force on the electron at distance `r`
on the ray of half-angle `a`. -/
def waterBendElectron (Z r R a : ℝ) : ℝ :=
  vdot (waterT a) (fun i =>
    pairForce (-1) Z (vsmul r (waterU a)) (fun _ => 0) i +
      pairForce (-1) 1 (vsmul r (waterU a)) (vsmul R (waterU a)) i +
      pairForce (-1) (-1) (vsmul r (waterU a)) (vsmul r (waterV a)) i +
      pairForce (-1) 1 (vsmul r (waterU a)) (vsmul R (waterV a)) i)

/-- Tangential component of the force on the proton at distance `R`. -/
def waterBendProton (Z r R a : ℝ) : ℝ :=
  vdot (waterT a) (fun i =>
    pairForce 1 Z (vsmul R (waterU a)) (fun _ => 0) i +
      pairForce 1 (-1) (vsmul R (waterU a)) (vsmul r (waterU a)) i +
      pairForce 1 (-1) (vsmul R (waterU a)) (vsmul r (waterV a)) i +
      pairForce 1 1 (vsmul R (waterU a)) (vsmul R (waterV a)) i)

private theorem tangent_ratio {r R ee hh rc γe γh γc : ℝ}
    (hr : 0 < r) (hR : 0 < R) (hee : 0 < ee) (hhh : 0 < hh) (hrc : 0 < rc)
    (hγe : 0 < γe) (hγh : 0 < γh) (hγc : γc ≠ 0)
    (hscale : hh * r = ee * R)
    (hE : r / (γe * ee ^ 3) = R / (γc * rc ^ 3))
    (hH : R / (γh * hh ^ 3) = r / (γc * rc ^ 3)) :
    γe / γh = R / r := by
  have hE' : r * (γc * rc ^ 3) = R * (γe * ee ^ 3) := by
    rw [div_eq_div_iff (mul_ne_zero hγe.ne' (pow_ne_zero 3 hee.ne'))
      (mul_ne_zero hγc (pow_ne_zero 3 hrc.ne'))] at hE
    exact hE
  have hH' : R * (γc * rc ^ 3) = r * (γh * hh ^ 3) := by
    rw [div_eq_div_iff (mul_ne_zero hγh.ne' (pow_ne_zero 3 hhh.ne'))
      (mul_ne_zero hγc (pow_ne_zero 3 hrc.ne'))] at hH
    exact hH
  have hclear : R ^ 2 * γe * ee ^ 3 = r ^ 2 * γh * hh ^ 3 := by
    have h1 : R * (r * (γc * rc ^ 3)) = R * (R * (γe * ee ^ 3)) :=
      congrArg (fun t => R * t) hE'
    have h2 : r * (R * (γc * rc ^ 3)) = r * (r * (γh * hh ^ 3)) :=
      congrArg (fun t => r * t) hH'
    nlinarith [h1, h2]
  have hh_eq : hh = ee * R / r := by
    apply mul_left_cancel₀ hr.ne'
    calc
      r * hh = hh * r := by ring
      _ = ee * R := hscale
      _ = r * (ee * R / r) := by field_simp [hr.ne']
  rw [hh_eq] at hclear
  have hpow : (ee * R / r) ^ 3 = ee ^ 3 * R ^ 3 / r ^ 3 := by
    field_simp [hr.ne']
  rw [hpow] at hclear
  have hdiv : R ^ 2 * γe * r = γh * R ^ 3 := by
    have hee3 : ee ^ 3 ≠ 0 := pow_ne_zero 3 hee.ne'
    have hr3 : r ^ 3 ≠ 0 := pow_ne_zero 3 hr.ne'
    field_simp [hee3, hr3] at hclear
    nlinarith
  have hlin : γe * r = γh * R := by
    apply mul_left_cancel₀ (pow_ne_zero 2 hR.ne')
    calc
      R ^ 2 * (γe * r) = R ^ 2 * γe * r := by ring
      _ = γh * R ^ 3 := hdiv
      _ = R ^ 2 * (γh * R) := by ring
  rw [div_eq_div_iff hγh.ne' hr.ne']
  calc
    γe * r = γh * R := hlin
    _ = R * γh := by ring

/-- The tangential forces on the electron and on its proton do not vanish
together. `θ` is the angle between the rays. -/
theorem water_no_outer_tangent {Z r R θ : ℝ}
    (hθ : θ ∈ Ioo 0 π) (hr : 0 < r) (hR : 0 < R) (hne : r ≠ R)
    (hee : outerSep (2 * r * sin (θ / 2)))
    (hhh : outerSep (2 * R * sin (θ / 2)))
    (hc : gammaSEqual (pairPhase
      (sqrt (r ^ 2 + R ^ 2 - 2 * r * R * cos θ))) ≠ 0) :
    ¬ (waterBendElectron Z r R (θ / 2) = 0 ∧ waterBendProton Z r R (θ / 2) = 0) := by
  intro hzero
  set a : ℝ := θ / 2
  have h2 : 2 * a = θ := by
    unfold a
    ring
  have ha0 : 0 < a := by
    unfold a
    linarith [hθ.1]
  have haπ : a < π := by
    unfold a
    linarith [hθ.2, pi_pos]
  have hsin : 0 < sin a := sin_pos_of_pos_of_lt_pi ha0 haπ
  have hsinθ : 0 < sin θ := sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  have hee_pos : 0 < 2 * r * sin a := by
    unfold a at hee
    exact hee.1
  have hhh_pos : 0 < 2 * R * sin a := by
    unfold a at hhh
    exact hhh.1
  have hvee := vnorm_ee r a hr hsin
  have hvhh := vnorm_hh R a hR hsin
  have hrc2 := cross_sep_pos hr hR hθ
  have hpoly : vnorm2 (vsub (vsmul r (waterU a)) (vsmul R (waterV a))) =
      r ^ 2 + R ^ 2 - 2 * r * R * cos θ := by
    rw [vnorm2_cross, cos_sq_sub_sin_sq, h2]
  have hvrc : vnorm (vsub (vsmul r (waterU a)) (vsmul R (waterV a))) =
      sqrt (r ^ 2 + R ^ 2 - 2 * r * R * cos θ) := by
    unfold vnorm
    rw [hpoly]
  have hrc_pos : 0 < sqrt (r ^ 2 + R ^ 2 - 2 * r * R * cos θ) := sqrt_pos.mpr hrc2
  set ee : ℝ := 2 * r * sin a
  set hh : ℝ := 2 * R * sin a
  set rc : ℝ := sqrt (r ^ 2 + R ^ 2 - 2 * r * R * cos θ)
  have hγe : 0 < gammaSEqual (pairPhase ee) := by
    unfold ee a
    exact outer_gamma_pos hee
  have hγh : 0 < gammaSEqual (pairPhase hh) := by
    unfold hh a
    exact outer_gamma_pos hhh
  have hγc : gammaSEqual (pairPhase rc) ≠ 0 := by
    unfold rc
    exact hc
  have hden_e : gammaSEqual (pairPhase (vnorm (vsub (vsmul r (waterU a))
      (vsmul r (waterV a))))) *
      vnorm (vsub (vsmul r (waterU a)) (vsmul r (waterV a))) ^ 3 ≠ 0 := by
    rw [hvee]
    unfold ee at hγe
    exact mul_ne_zero hγe.ne' (pow_ne_zero 3 (by unfold ee at hee_pos; exact hee_pos.ne'))
  have hden_c : gammaSEqual (pairPhase (vnorm (vsub (vsmul r (waterU a))
      (vsmul R (waterV a))))) *
      vnorm (vsub (vsmul r (waterU a)) (vsmul R (waterV a))) ^ 3 ≠ 0 := by
    rw [hvrc]
    unfold rc at hγc hrc_pos
    exact mul_ne_zero hγc (pow_ne_zero 3 hrc_pos.ne')
  have hden_h : gammaSEqual (pairPhase (vnorm (vsub (vsmul R (waterU a))
      (vsmul R (waterV a))))) *
      vnorm (vsub (vsmul R (waterU a)) (vsmul R (waterV a))) ^ 3 ≠ 0 := by
    rw [hvhh]
    unfold hh at hγh
    exact mul_ne_zero hγh.ne' (pow_ne_zero 3 (by unfold hh at hhh_pos; exact hhh_pos.ne'))
  have hden_p : gammaSEqual (pairPhase (vnorm (vsub (vsmul R (waterU a))
      (vsmul r (waterV a))))) *
      vnorm (vsub (vsmul R (waterU a)) (vsmul r (waterV a))) ^ 3 ≠ 0 := by
    have hcomm : vnorm (vsub (vsmul R (waterU a)) (vsmul r (waterV a))) =
        vnorm (vsub (vsmul r (waterU a)) (vsmul R (waterV a))) :=
      vnorm_cross_sym r R a
    rw [hcomm]
    exact hden_c
  have hFe : waterBendElectron Z r R a =
      sin (2 * a) * (r / (gammaSEqual (pairPhase ee) * ee ^ 3) -
        R / (gammaSEqual (pairPhase rc) * rc ^ 3)) := by
    unfold waterBendElectron
    rw [vdot_add, vdot_add, vdot_add]
    have hnuc : vdot (waterT a) (fun i =>
        pairForce (-1) Z (vsmul r (waterU a)) (fun _ => 0) i) = 0 := by
      refine vdot_pairForce_ortho ?_
      have hsub : vsub (vsmul r (waterU a)) (fun _ => 0) = vsmul r (waterU a) := by
        funext i
        simp [vsub]
      rw [hsub, vdot_T_nucleus]
    have hown : vdot (waterT a) (fun i =>
        pairForce (-1) 1 (vsmul r (waterU a)) (vsmul R (waterU a)) i) = 0 :=
      vdot_pairForce_ortho (vdot_T_partner r R a)
    have hee_c := vdot_pairForce (-1) (-1)
      (vsmul r (waterU a)) (vsmul r (waterV a)) (waterT a) hden_e
    have hcross := vdot_pairForce (-1) 1
      (vsmul r (waterU a)) (vsmul R (waterV a)) (waterT a) hden_c
    rw [hnuc, hown, hee_c, hcross, vdot_T_ee, vdot_T_cross, hvee, hvrc]
    unfold ee rc
    ring
  have hFh : waterBendProton Z r R a =
      sin (2 * a) * (-r / (gammaSEqual (pairPhase rc) * rc ^ 3) +
        R / (gammaSEqual (pairPhase hh) * hh ^ 3)) := by
    unfold waterBendProton
    rw [vdot_add, vdot_add, vdot_add]
    have hnuc : vdot (waterT a) (fun i =>
        pairForce 1 Z (vsmul R (waterU a)) (fun _ => 0) i) = 0 := by
      refine vdot_pairForce_ortho ?_
      have hsub : vsub (vsmul R (waterU a)) (fun _ => 0) = vsmul R (waterU a) := by
        funext i
        simp [vsub]
      rw [hsub, vdot_T_nucleus]
    have hown : vdot (waterT a) (fun i =>
        pairForce 1 (-1) (vsmul R (waterU a)) (vsmul r (waterU a)) i) = 0 := by
      refine vdot_pairForce_ortho ?_
      have hswap : vdot (waterT a)
          (vsub (vsmul R (waterU a)) (vsmul r (waterU a))) = 0 := by
        simpa [show vsub (vsmul R (waterU a)) (vsmul r (waterU a)) =
          vsub (vsmul R (waterU a)) (vsmul r (waterU a)) from rfl] using
          vdot_T_partner R r a
      exact hswap
    have hpe := vdot_pairForce 1 (-1)
      (vsmul R (waterU a)) (vsmul r (waterV a)) (waterT a) hden_p
    have hhh_c := vdot_pairForce 1 1
      (vsmul R (waterU a)) (vsmul R (waterV a)) (waterT a) hden_h
    rw [hnuc, hown, hpe, hhh_c, vdot_T_pe, vdot_T_hh, hvhh]
    have hcomm : vnorm (vsub (vsmul R (waterU a)) (vsmul r (waterV a))) = rc :=
      (vnorm_cross_sym r R a).trans hvrc
    rw [hcomm]
    unfold hh rc
    have hden1 : gammaSEqual (pairPhase rc) * rc ^ 3 ≠ 0 :=
      mul_ne_zero hγc (pow_ne_zero 3 hrc_pos.ne')
    have hden2 : gammaSEqual (pairPhase hh) * hh ^ 3 ≠ 0 :=
      mul_ne_zero hγh.ne' (pow_ne_zero 3 hhh_pos.ne')
    field_simp [hden1, hden2]
    ring
  have hE0 : r / (gammaSEqual (pairPhase ee) * ee ^ 3) =
      R / (gammaSEqual (pairPhase rc) * rc ^ 3) := by
    have hmul : sin (2 * a) *
        (r / (gammaSEqual (pairPhase ee) * ee ^ 3) -
          R / (gammaSEqual (pairPhase rc) * rc ^ 3)) = 0 := by
      rw [← hFe]
      exact hzero.1
    have hdiff : r / (gammaSEqual (pairPhase ee) * ee ^ 3) -
        R / (gammaSEqual (pairPhase rc) * rc ^ 3) = 0 :=
      (mul_eq_zero.mp hmul).resolve_left (by rw [h2]; exact hsinθ.ne')
    linarith
  have hH0 : R / (gammaSEqual (pairPhase hh) * hh ^ 3) =
      r / (gammaSEqual (pairPhase rc) * rc ^ 3) := by
    have hmul : sin (2 * a) *
        (-r / (gammaSEqual (pairPhase rc) * rc ^ 3) +
          R / (gammaSEqual (pairPhase hh) * hh ^ 3)) = 0 := by
      rw [← hFh]
      exact hzero.2
    have hdiff : -r / (gammaSEqual (pairPhase rc) * rc ^ 3) +
        R / (gammaSEqual (pairPhase hh) * hh ^ 3) = 0 :=
      (mul_eq_zero.mp hmul).resolve_left (by rw [h2]; exact hsinθ.ne')
    rw [add_comm] at hdiff
    rw [neg_div] at hdiff
    rw [← sub_eq_add_neg] at hdiff
    exact sub_eq_zero.mp hdiff
  have hscale : hh * r = ee * R := by
    unfold hh ee
    ring
  have hratio := tangent_ratio hr hR hee_pos hhh_pos hrc_pos hγe hγh hγc hscale hE0 hH0
  have hcase : r < R ∨ R < r := lt_or_gt_of_ne hne
  rcases hcase with hlt | hgt
  · have hdist : ee < hh := by
      unfold ee hh
      nlinarith
    have hphase : pairPhase hh < pairPhase ee := by
      unfold pairPhase
      exact div_lt_div_of_pos_left (by norm_num) (by linarith : 0 < 2 * ee) (by linarith)
    have hγlt : gammaSEqual (pairPhase ee) < gammaSEqual (pairPhase hh) := by
      refine gamma_strictAnti_phase ?_ ?_ hphase
      · unfold pairPhase
        exact div_nonneg (by norm_num) (by linarith)
      · unfold ee a
        exact hee.2
    have hlt1 : gammaSEqual (pairPhase ee) / gammaSEqual (pairPhase hh) < 1 :=
      (div_lt_one hγh).mpr hγlt
    have hgt1 : 1 < R / r := (one_lt_div hr).mpr hlt
    linarith
  · have hdist : hh < ee := by
      unfold ee hh
      nlinarith
    have hphase : pairPhase ee < pairPhase hh := by
      unfold pairPhase
      exact div_lt_div_of_pos_left (by norm_num) (by linarith : 0 < 2 * hh) (by linarith)
    have hγlt : gammaSEqual (pairPhase hh) < gammaSEqual (pairPhase ee) := by
      refine gamma_strictAnti_phase ?_ ?_ hphase
      · unfold pairPhase
        exact div_nonneg (by norm_num) (by linarith)
      · unfold hh a
        exact hhh.2
    have hgt1 : 1 < gammaSEqual (pairPhase ee) / gammaSEqual (pairPhase hh) :=
      (one_lt_div hγh).mpr hγlt
    have hlt1 : R / r < 1 := (div_lt_one hr).mpr hgt
    linarith

end

end DstDiophantine.Gravity
