import DstDiophantine.Gravity.ElectronBoundary
import DstDiophantine.Gravity.ElectronForce
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Tactic.FieldSimp
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The water molecule

## Paper boundary (do **not** claim)

The length `ℓ` is not derived. Nothing here produces a bond angle in degrees,
a dissociation energy, a value of `a₀`, or a count of lone pairs. The molecule
is two bonds — one electron and one proton on each ray — together with any
further electrons off those rays. It is not a shell of eight and not the
cube. No equilibrium is claimed in the reversed shell. Oxygen is not the
dodecahedron. No degree of a bond angle is computed.

## What is proved

* While the bonding electron is closer than its proton and the two bonding
  electrons repel, the other bond drives that electron toward a wider angle.
  The nuclear charge does not enter. An electron on the same ray adds
  nothing. An electron that repels from the side toward the other bond adds
  a wider push; one that repels from the opposite side adds a narrower push.
  With every added electron contributing a nonnegative tangent, the total
  stays positive. Distances are in units of `ℓ`.
* On a straight line, while both distances from the nucleus lie in the outer
  well, the two bonds alone have no tangential force. An electron on the axis
  opposite the bonds then makes the bonding electron's tangent strictly
  negative.
* On that straight line, with each electron between the nucleus and its
  proton and with both nucleus distances in the outer well, the outward force
  on the electron plus the outward force on the proton is strictly negative
  whenever the nuclear charge is at least `1/4` and the factor on the segment
  between them is not a node.
* The older ratio statement remains: while the electron–electron and
  proton–proton separations lie in the outer well and the cross factor is
  not a node, the two tangential forces do not vanish together.
* The angle at which the protons are as far apart as each is from the other
  electron is strictly less than a third of a straight angle. While both
  separations lie in the outer well and the protons are no farther apart
  than that cross separation, the tangential force on each proton points
  toward the wider angle. The nuclear charge does not enter. When the
  electron lies at least a quarter as far from the nucleus as the proton
  and the equal separation still lies in the outer well, that force is
  positive at the equal separation, negative at some greater angle short of
  a straight line, and zero at an angle strictly between the two.
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

/-- Outward force on the electron of the straight water molecule.
The nucleus is at the origin, the electron at `+r`, its proton at `+R`. -/
def waterStraightElectron (Z r R : ℝ) : ℝ :=
  pairForce (-1) Z (axisPoint r) (axisPoint 0) 0 +
    pairForce (-1) 1 (axisPoint r) (axisPoint R) 0 +
    pairForce (-1) (-1) (axisPoint r) (axisPoint (-r)) 0 +
    pairForce (-1) 1 (axisPoint r) (axisPoint (-R)) 0

/-- Outward force on the proton of the straight water molecule. -/
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

/-! ### The molecule: opening, and electrons off the rays -/

private theorem vdot_sub (t u w : Fin 3 → ℝ) :
    vdot t (vsub u w) = vdot t u - vdot t w := by
  unfold vdot vsub
  ring

private theorem water_cross_expand (r R a : ℝ) :
    r ^ 2 + R ^ 2 - 2 * r * R * cos (2 * a) =
      (R - r) ^ 2 + 4 * r * R * sin a ^ 2 := by
  have hcos : cos (2 * a) = 1 - 2 * sin a ^ 2 := by
    rw [cos_two_mul]
    have hsc : cos a ^ 2 = 1 - sin a ^ 2 := by
      have h := sin_sq_add_cos_sq a
      linarith
    rw [hsc]
    ring
  rw [hcos]
  ring

private theorem outerSep_of_gt {d s : ℝ} (hd : outerSep d) (hlt : d < s) : outerSep s := by
  have hs : 0 < s := lt_trans hd.1 hlt
  refine ⟨hs, ?_⟩
  have hφ : pairPhase s < pairPhase d := by
    unfold pairPhase
    exact div_lt_div_of_pos_left (by norm_num) (mul_pos (by norm_num) hd.1)
      (by linarith : (2 : ℝ) * d < 2 * s)
  exact lt_trans hφ hd.2

/-- The electron tangent of the two bonds factors through `sin` of the angle.
`a` is the half-angle. The nuclear charge does not appear. -/
theorem waterBendElectron_factor {Z r R a : ℝ}
    (ha : a ∈ Ioo 0 π) (hr : 0 < r) (hR : 0 < R)
    (hee : outerSep (2 * r * sin a))
    (hc : gammaSEqual (pairPhase
      (sqrt (r ^ 2 + R ^ 2 - 2 * r * R * cos (2 * a)))) ≠ 0) :
    waterBendElectron Z r R a =
      sin (2 * a) * (r / (gammaSEqual (pairPhase (2 * r * sin a)) *
        (2 * r * sin a) ^ 3) -
        R / (gammaSEqual (pairPhase
          (sqrt (r ^ 2 + R ^ 2 - 2 * r * R * cos (2 * a)))) *
          (sqrt (r ^ 2 + R ^ 2 - 2 * r * R * cos (2 * a))) ^ 3)) := by
  have hsin : 0 < sin a := sin_pos_of_pos_of_lt_pi ha.1 ha.2
  have hee_pos : 0 < 2 * r * sin a := hee.1
  have hrc2 : 0 < r ^ 2 + R ^ 2 - 2 * r * R * cos (2 * a) := by
    rw [water_cross_expand]
    have hsin2 : 0 < sin a ^ 2 := sq_pos_of_pos hsin
    have h4 : 0 < 4 * r * R * sin a ^ 2 :=
      mul_pos (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 4) hr) hR) hsin2
    linarith [sq_nonneg (R - r)]
  have hrc_pos : 0 < sqrt (r ^ 2 + R ^ 2 - 2 * r * R * cos (2 * a)) :=
    sqrt_pos.mpr hrc2
  set ee : ℝ := 2 * r * sin a
  set rc : ℝ := sqrt (r ^ 2 + R ^ 2 - 2 * r * R * cos (2 * a))
  have hvee := vnorm_ee r a hr hsin
  have hpoly : vnorm2 (vsub (vsmul r (waterU a)) (vsmul R (waterV a))) =
      r ^ 2 + R ^ 2 - 2 * r * R * cos (2 * a) := by
    rw [vnorm2_cross, cos_sq_sub_sin_sq]
  have hvrc : vnorm (vsub (vsmul r (waterU a)) (vsmul R (waterV a))) = rc := by
    unfold vnorm rc
    rw [hpoly]
  have hγe : 0 < gammaSEqual (pairPhase ee) := outer_gamma_pos hee
  have hden_e : gammaSEqual (pairPhase (vnorm (vsub (vsmul r (waterU a))
      (vsmul r (waterV a))))) *
      vnorm (vsub (vsmul r (waterU a)) (vsmul r (waterV a))) ^ 3 ≠ 0 := by
    rw [hvee]
    exact mul_ne_zero hγe.ne' (pow_ne_zero 3 hee_pos.ne')
  have hden_c : gammaSEqual (pairPhase (vnorm (vsub (vsmul r (waterU a))
      (vsmul R (waterV a))))) *
      vnorm (vsub (vsmul r (waterU a)) (vsmul R (waterV a))) ^ 3 ≠ 0 := by
    rw [hvrc]
    exact mul_ne_zero hc (pow_ne_zero 3 hrc_pos.ne')
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
  ring

/-- Closer than its proton, and repelling the other bonding electron, the
electron is driven toward a wider angle. -/
theorem waterBendElectron_opening {Z r R a : ℝ}
    (ha : a ∈ Ioo 0 (π / 2)) (hr : 0 < r) (hrR : r < R)
    (hee : outerSep (2 * r * sin a)) :
    0 < waterBendElectron Z r R a := by
  have hR : 0 < R := lt_trans hr hrR
  have haπ : a ∈ Ioo 0 π := ⟨ha.1, lt_trans ha.2 (half_lt_self pi_pos)⟩
  have hsin : 0 < sin a := sin_pos_of_pos_of_lt_pi ha.1 haπ.2
  have hcos : 0 < cos a :=
    cos_pos_of_mem_Ioo ⟨lt_trans (neg_lt_zero.mpr pi_div_two_pos) ha.1, ha.2⟩
  have hsin2 : 0 < sin (2 * a) := by
    rw [sin_two_mul]
    exact mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2) hsin) hcos
  set ee : ℝ := 2 * r * sin a
  set rc : ℝ := sqrt (r ^ 2 + R ^ 2 - 2 * r * R * cos (2 * a))
  have hee_pos : 0 < ee := hee.1
  have hrc2_pos : 0 < r ^ 2 + R ^ 2 - 2 * r * R * cos (2 * a) := by
    rw [water_cross_expand]
    have hsinSq : 0 < sin a ^ 2 := sq_pos_of_pos hsin
    have h4 : 0 < 4 * r * R * sin a ^ 2 :=
      mul_pos (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 4) hr) hR) hsinSq
    linarith [sq_nonneg (R - r)]
  have hrc_pos : 0 < rc := by
    unfold rc
    exact sqrt_pos.mpr hrc2_pos
  have hrc_sq : rc ^ 2 = (R - r) ^ 2 + 4 * r * R * sin a ^ 2 := by
    have harg : rc ^ 2 = r ^ 2 + R ^ 2 - 2 * r * R * cos (2 * a) := by
      unfold rc
      exact sq_sqrt hrc2_pos.le
    rw [harg, water_cross_expand]
  have hee_sq : ee ^ 2 = 4 * r ^ 2 * sin a ^ 2 := by
    unfold ee
    ring
  have hsq : R * ee ^ 2 < r * rc ^ 2 := by
    have hdiff : r * rc ^ 2 - R * ee ^ 2 = r * (R - r) ^ 2 := by
      rw [hrc_sq, hee_sq]
      ring
    have hpos : 0 < r * (R - r) ^ 2 :=
      mul_pos hr (sq_pos_of_pos (sub_pos.mpr hrR))
    linarith
  have hrc_ee : ee < rc := by
    have h2 : ee ^ 2 < rc ^ 2 := by
      have hlt : r * ee ^ 2 < r * rc ^ 2 := by
        have hRR : r * ee ^ 2 < R * ee ^ 2 :=
          mul_lt_mul_of_pos_right hrR (sq_pos_of_pos hee_pos)
        linarith
      exact (mul_lt_mul_iff_of_pos_left hr).mp hlt
    have habs : |ee| < |rc| := (sq_lt_sq).mp h2
    rwa [abs_of_pos hee_pos, abs_of_pos hrc_pos] at habs
  have hcube : R * ee ^ 3 < r * rc ^ 3 := by
    have hmid : R * ee ^ 2 * ee < r * rc ^ 2 * rc := by
      have h1 : R * ee ^ 2 * ee < r * rc ^ 2 * ee :=
        mul_lt_mul_of_pos_right hsq hee_pos
      have h2 : r * rc ^ 2 * ee < r * rc ^ 2 * rc :=
        mul_lt_mul_of_pos_left hrc_ee (mul_pos hr (sq_pos_of_pos hrc_pos))
      linarith
    calc
      R * ee ^ 3 = R * ee ^ 2 * ee := by ring
      _ < r * rc ^ 2 * rc := hmid
      _ = r * rc ^ 3 := by ring
  have hphase : pairPhase rc < pairPhase ee := by
    unfold pairPhase
    exact div_lt_div_of_pos_left (by norm_num) (mul_pos (by norm_num) hee_pos)
      (by linarith : (2 : ℝ) * ee < 2 * rc)
  have hφee : pairPhase ee < resonanceRoot1 := hee.2
  have hγe : 0 < gammaSEqual (pairPhase ee) := outer_gamma_pos hee
  have hγc : 0 < gammaSEqual (pairPhase rc) := by
    refine outer_gamma_pos ?_
    exact ⟨hrc_pos, lt_trans hphase hφee⟩
  have hγlt : gammaSEqual (pairPhase ee) < gammaSEqual (pairPhase rc) := by
    refine gamma_strictAnti_phase ?_ hφee hphase
    unfold pairPhase
    exact div_nonneg (by norm_num) (mul_nonneg (by norm_num) hrc_pos.le)
  have hclear : R * gammaSEqual (pairPhase ee) * ee ^ 3 <
      r * gammaSEqual (pairPhase rc) * rc ^ 3 := by
    have h1 : gammaSEqual (pairPhase ee) * (R * ee ^ 3) <
        gammaSEqual (pairPhase ee) * (r * rc ^ 3) :=
      mul_lt_mul_of_pos_left hcube hγe
    have h2 : gammaSEqual (pairPhase ee) * (r * rc ^ 3) <
        gammaSEqual (pairPhase rc) * (r * rc ^ 3) :=
      mul_lt_mul_of_pos_right hγlt (mul_pos hr (pow_pos hrc_pos 3))
    have hord1 : gammaSEqual (pairPhase ee) * (R * ee ^ 3) =
        R * gammaSEqual (pairPhase ee) * ee ^ 3 := by ring
    have hord2 : gammaSEqual (pairPhase rc) * (r * rc ^ 3) =
        r * gammaSEqual (pairPhase rc) * rc ^ 3 := by ring
    linarith
  have hAe : 0 < r / (gammaSEqual (pairPhase ee) * ee ^ 3) -
      R / (gammaSEqual (pairPhase rc) * rc ^ 3) := by
    rw [sub_pos]
    rw [div_lt_div_iff₀ (mul_pos hγc (pow_pos hrc_pos 3))
      (mul_pos hγe (pow_pos hee_pos 3))]
    linarith
  have hfac := waterBendElectron_factor (Z := Z) haπ hr hR hee hγc.ne'
  rw [hfac]
  exact mul_pos hsin2 hAe

/-- On the straight line the two bonds exert no tangential force on the
bonding electron. Both distances from the nucleus lie in the outer well. -/
theorem waterBendElectron_straight {Z r R : ℝ}
    (hr : outerSep r) (hR : outerSep R) :
    waterBendElectron Z r R (π / 2) = 0 := by
  have ha : π / 2 ∈ Ioo 0 π := ⟨div_pos pi_pos (by norm_num), half_lt_self pi_pos⟩
  have hangle : 2 * (π / 2) = π := by ring
  have hee : outerSep (2 * r * sin (π / 2)) := by
    rw [sin_pi_div_two, mul_one]
    exact ⟨by linarith [hr.1], (phase_half_mem hr).2⟩
  have hc : gammaSEqual (pairPhase
      (sqrt (r ^ 2 + R ^ 2 - 2 * r * R * cos (2 * (π / 2))))) ≠ 0 := by
    rw [hangle, cos_pi]
    have hsq : r ^ 2 + R ^ 2 - 2 * r * R * (-1) = (R + r) ^ 2 := by ring
    rw [hsq, sqrt_sq_eq_abs, abs_of_pos (by linarith [hr.1, hR.1])]
    exact (outer_gamma_pos ⟨by linarith [hr.1, hR.1], (phase_sum_mem hr hR.1).2⟩).ne'
  rw [waterBendElectron_factor ha hr.1 hR.1 hee hc, hangle, sin_pi, zero_mul]

/-- A point on the axis between the two rays, or, for a negative coordinate,
on the opposite axis. -/
def bondAxis (z : ℝ) : Fin 3 → ℝ :=
  ![0, 0, z]

@[simp] theorem bondAxis_zero (z : ℝ) : bondAxis z 0 = 0 := rfl
@[simp] theorem bondAxis_one (z : ℝ) : bondAxis z 1 = 0 := rfl
@[simp] theorem bondAxis_two (z : ℝ) : bondAxis z 2 = z := rfl

private theorem vdot_T_bondAxis (a z : ℝ) :
    vdot (waterT a) (bondAxis z) = -z * sin a := by
  unfold vdot
  simp only [waterT_zero, waterT_one, waterT_two, bondAxis_zero, bondAxis_one,
    bondAxis_two]
  ring

/-- Tangential force on the bonding electron at distance `r` from an extra
charge `q` at `X`. -/
def waterExtraTangent (r a q : ℝ) (X : Fin 3 → ℝ) : ℝ :=
  vdot (waterT a) (fun i => pairForce (-1) q (vsmul r (waterU a)) X i)

/-- Sum of the tangential forces from finitely many extra charges. -/
def waterTangentSum {n : ℕ} (r a : ℝ) (q : Fin n → ℝ)
    (X : Fin n → Fin 3 → ℝ) : ℝ :=
  Finset.sum Finset.univ fun i => waterExtraTangent r a (q i) (X i)

private theorem waterExtraTangent_repel {r a q : ℝ} {X : Fin 3 → ℝ}
    (hsep : outerSep (vnorm (vsub (vsmul r (waterU a)) X))) :
    waterExtraTangent r a q X =
      q * vdot (waterT a) X /
        (gammaSEqual (pairPhase (vnorm (vsub (vsmul r (waterU a)) X))) *
          vnorm (vsub (vsmul r (waterU a)) X) ^ 3) := by
  unfold waterExtraTangent
  have hden : gammaSEqual (pairPhase (vnorm (vsub (vsmul r (waterU a)) X))) *
      vnorm (vsub (vsmul r (waterU a)) X) ^ 3 ≠ 0 :=
    mul_ne_zero (outer_gamma_pos hsep).ne' (pow_ne_zero 3 hsep.1.ne')
  rw [vdot_pairForce (-1) q (vsmul r (waterU a)) X (waterT a) hden]
  rw [vdot_sub, vdot_T_nucleus, zero_sub]
  have hnum : (-1) * q * (-vdot (waterT a) X) = q * vdot (waterT a) X := by ring
  rw [hnum]

/-- An electron that repels from the side toward the other bond pushes wider. -/
theorem waterExtraTangent_inner {r a q : ℝ} {X : Fin 3 → ℝ}
    (hq : q < 0) (hside : vdot (waterT a) X < 0)
    (hsep : outerSep (vnorm (vsub (vsmul r (waterU a)) X))) :
    0 < waterExtraTangent r a q X := by
  rw [waterExtraTangent_repel hsep]
  refine div_pos ?_ ?_
  · exact mul_pos_of_neg_of_neg hq hside
  · exact mul_pos (outer_gamma_pos hsep) (pow_pos hsep.1 3)

/-- An electron that repels from the opposite side pushes narrower. -/
theorem waterExtraTangent_outer {r a q : ℝ} {X : Fin 3 → ℝ}
    (hq : q < 0) (hside : 0 < vdot (waterT a) X)
    (hsep : outerSep (vnorm (vsub (vsmul r (waterU a)) X))) :
    waterExtraTangent r a q X < 0 := by
  rw [waterExtraTangent_repel hsep]
  refine div_neg_of_neg_of_pos ?_ ?_
  · exact mul_neg_of_neg_of_pos hq hside
  · exact mul_pos (outer_gamma_pos hsep) (pow_pos hsep.1 3)

/-- An electron on the same ray adds no tangential force. -/
theorem waterExtraTangent_same_ray (r a q s : ℝ) :
    waterExtraTangent r a q (vsmul s (waterU a)) = 0 := by
  unfold waterExtraTangent
  exact vdot_pairForce_ortho (vdot_T_partner r s a)

/-- An electron on the axis opposite the bonds, while it repels, pushes narrower. -/
theorem waterExtraTangent_far_neg {r a lam : ℝ}
    (ha : a ∈ Ioo 0 π) (hlam : 0 < lam)
    (hsep : outerSep (vnorm (vsub (vsmul r (waterU a)) (bondAxis (-lam))))) :
    waterExtraTangent r a (-1) (bondAxis (-lam)) < 0 := by
  refine waterExtraTangent_outer (by norm_num) ?_ hsep
  rw [vdot_T_bondAxis]
  have hsin : 0 < sin a := sin_pos_of_pos_of_lt_pi ha.1 ha.2
  nlinarith

/-- An electron on the axis between the bonds, while it repels, pushes wider. -/
theorem waterExtraTangent_bisector_pos {r a μ : ℝ}
    (ha : a ∈ Ioo 0 (π / 2)) (hμ : 0 < μ)
    (hsep : outerSep (vnorm (vsub (vsmul r (waterU a)) (bondAxis μ)))) :
    0 < waterExtraTangent r a (-1) (bondAxis μ) := by
  refine waterExtraTangent_inner (by norm_num) ?_ hsep
  rw [vdot_T_bondAxis]
  have hsin : 0 < sin a :=
    sin_pos_of_pos_of_lt_pi ha.1 (lt_trans ha.2 (half_lt_self pi_pos))
  nlinarith

/-- The bonding electron is still driven wider when every extra tangent is
nonnegative. -/
theorem waterMolecule_opening {n : ℕ} {Z r R a : ℝ}
    {q : Fin n → ℝ} {X : Fin n → Fin 3 → ℝ}
    (ha : a ∈ Ioo 0 (π / 2)) (hr : 0 < r) (hrR : r < R)
    (hee : outerSep (2 * r * sin a))
    (hnn : ∀ i, 0 ≤ waterExtraTangent r a (q i) (X i)) :
    0 < waterBendElectron Z r R a + waterTangentSum r a q X := by
  have hopen : 0 < waterBendElectron Z r R a :=
    waterBendElectron_opening ha hr hrR hee
  have hsum : 0 ≤ waterTangentSum r a q X := by
    unfold waterTangentSum
    exact Finset.sum_nonneg fun i _ => hnn i
  linarith

/-- On the straight line, an electron on the opposite axis drives the bonding
electron off the line. -/
theorem water_straight_far_neg {Z r R lam : ℝ}
    (hr : outerSep r) (hR : outerSep R) (hlam : 0 < lam) :
    waterBendElectron Z r R (π / 2) +
      waterExtraTangent r (π / 2) (-1) (bondAxis (-lam)) < 0 := by
  rw [waterBendElectron_straight hr hR]
  have ha : π / 2 ∈ Ioo 0 π := ⟨div_pos pi_pos (by norm_num), half_lt_self pi_pos⟩
  have hsep : outerSep (vnorm (vsub (vsmul r (waterU (π / 2))) (bondAxis (-lam)))) := by
    have hv : vnorm (vsub (vsmul r (waterU (π / 2))) (bondAxis (-lam))) =
        sqrt (r ^ 2 + lam ^ 2) := by
      unfold vnorm vnorm2 vdot vsub vsmul
      simp only [waterU_zero, waterU_one, waterU_two, bondAxis_zero, bondAxis_one,
        bondAxis_two, sin_pi_div_two, cos_pi_div_two]
      have hsq : (r * (1 : ℝ) - 0) * (r * (1 : ℝ) - 0) +
          (r * (0 : ℝ) - 0) * (r * (0 : ℝ) - 0) +
          (r * (0 : ℝ) - -lam) * (r * (0 : ℝ) - -lam) = r ^ 2 + lam ^ 2 := by ring
      rw [hsq]
    rw [hv]
    refine outerSep_of_gt hr ?_
    have hsq : r ^ 2 < r ^ 2 + lam ^ 2 := by
      linarith [sq_pos_of_pos hlam]
    have hsqrt : sqrt (r ^ 2) < sqrt (r ^ 2 + lam ^ 2) :=
      sqrt_lt_sqrt (sq_nonneg r) hsq
    rwa [sqrt_sq_eq_abs, abs_of_pos hr.1] at hsqrt
  have hfar := waterExtraTangent_far_neg ha hlam hsep
  linarith


/-! ### The angle held by the two protons -/

/-- Separation of the two protons. -/
noncomputable def protonSep (a R : ℝ) : ℝ :=
  2 * R * sin a

/-- Separation of a proton from the other bond's electron. -/
noncomputable def protonCross (a r R : ℝ) : ℝ :=
  sqrt ((R - r) ^ 2 + 4 * r * R * sin a ^ 2)

/-- Other-proton repulsion minus the other electron's pull, per unit sine. -/
noncomputable def protonParen (a r R : ℝ) : ℝ :=
  R / (gammaSEqual (pairPhase (protonSep a R)) * protonSep a R ^ 3) -
    r / (gammaSEqual (pairPhase (protonCross a r R)) * protonCross a r R ^ 3)

/-- Separation at which the protons are as far apart as each is from the other electron. -/
noncomputable def equalChord (r R : ℝ) : ℝ :=
  sqrt (R * (R - r))

/-- Half-angle of that equal separation. -/
noncomputable def equalHalf (r R : ℝ) : ℝ :=
  arcsin (equalChord r R / (2 * R))

private theorem equalChord_lt_half {r R : ℝ} (hr : 0 < r) (hR : r < R) :
    equalChord r R / (2 * R) < 1 / 2 := by
  have hRpos : 0 < R := lt_trans hr hR
  have hprod : 0 ≤ R * (R - r) := by nlinarith
  have hsq : equalChord r R ^ 2 = R * (R - r) := by
    unfold equalChord
    exact sq_sqrt hprod
  have hlt : equalChord r R ^ 2 < R ^ 2 := by
    rw [hsq]
    nlinarith
  have habs : |equalChord r R| < |R| := (sq_lt_sq).mp hlt
  have hpos : 0 < equalChord r R := by
    unfold equalChord
    exact sqrt_pos.mpr (by nlinarith)
  rw [abs_of_pos hpos, abs_of_pos hRpos] at habs
  rw [div_lt_div_iff₀ (by linarith) (by norm_num)]
  linarith

private theorem sin_equalHalf {r R : ℝ} (hr : 0 < r) (hR : r < R) :
    sin (equalHalf r R) = equalChord r R / (2 * R) := by
  unfold equalHalf
  have hRpos : 0 < R := lt_trans hr hR
  refine sin_arcsin ?_ ?_
  · have hnonneg : 0 ≤ equalChord r R / (2 * R) :=
      div_nonneg (sqrt_nonneg _) (by linarith)
    linarith
  · linarith [equalChord_lt_half hr hR]

theorem equalHalf_lt_pi_div_six {r R : ℝ} (hr : 0 < r) (hR : r < R) :
    equalHalf r R < π / 6 := by
  have hs : sin (equalHalf r R) < sin (π / 6) := by
    rw [sin_equalHalf hr hR, sin_pi_div_six]
    exact equalChord_lt_half hr hR
  have h1 : equalHalf r R ∈ Icc (-(π / 2)) (π / 2) := arcsin_mem_Icc _
  have h2 : (π / 6 : ℝ) ∈ Icc (-(π / 2)) (π / 2) := by
    constructor <;> linarith [pi_pos]
  exact (strictMonoOn_sin.lt_iff_lt h1 h2).mp hs

private theorem equalHalf_pos {r R : ℝ} (hr : 0 < r) (hR : r < R) :
    0 < equalHalf r R := by
  unfold equalHalf
  refine arcsin_pos.mpr ?_
  exact div_pos (by
    unfold equalChord
    exact sqrt_pos.mpr (by nlinarith)) (by linarith [lt_trans hr hR])

private theorem protonSep_equal {r R : ℝ} (hr : 0 < r) (hR : r < R) :
    protonSep (equalHalf r R) R = equalChord r R := by
  unfold protonSep
  rw [sin_equalHalf hr hR]
  have hRpos : 0 < R := lt_trans hr hR
  field_simp

private theorem protonCross_equal {r R : ℝ} (hr : 0 < r) (hR : r < R) :
    protonCross (equalHalf r R) r R = equalChord r R := by
  have hRpos : 0 < R := lt_trans hr hR
  have hsin := sin_equalHalf hr hR
  have hch : equalChord r R ^ 2 = R * (R - r) := by
    unfold equalChord
    exact sq_sqrt (by nlinarith)
  have hsqsin : sin (equalHalf r R) ^ 2 = (R - r) / (4 * R) := by
    calc
      sin (equalHalf r R) ^ 2 = (equalChord r R / (2 * R)) ^ 2 := by rw [hsin]
      _ = equalChord r R ^ 2 / (4 * R ^ 2) := by ring
      _ = (R * (R - r)) / (4 * R ^ 2) := by rw [hch]
      _ = (R - r) / (4 * R) := by field_simp
  unfold protonCross
  have harg : (R - r) ^ 2 + 4 * r * R * sin (equalHalf r R) ^ 2 =
      R * (R - r) := by
    rw [hsqsin]
    field_simp
    ring
  rw [harg]
  unfold equalChord
  rfl

private theorem protonSep_straight (R : ℝ) :
    protonSep (π / 2) R = 2 * R := by
  unfold protonSep
  rw [sin_pi_div_two]
  ring

private theorem protonCross_straight {r R : ℝ} (hr : 0 ≤ r) (hR : 0 ≤ R) :
    protonCross (π / 2) r R = R + r := by
  unfold protonCross
  have hsq : (R - r) ^ 2 + 4 * r * R * sin (π / 2) ^ 2 = (R + r) ^ 2 := by
    rw [sin_pi_div_two]
    ring
  rw [hsq, sqrt_sq (by linarith : 0 ≤ R + r)]

private theorem protonSep_mono {a b R : ℝ} (hR : 0 < R)
    (ha : -(π / 2) ≤ a) (hb : b ≤ π / 2) (hab : a ≤ b) :
    protonSep a R ≤ protonSep b R := by
  unfold protonSep
  have hsin : sin a ≤ sin b :=
    strictMonoOn_sin.monotoneOn ⟨ha, le_trans hab hb⟩ ⟨by linarith, hb⟩ hab
  have hmul : 0 ≤ 2 * R := by linarith
  exact mul_le_mul_of_nonneg_left hsin hmul

private theorem protonCross_mono {a b r R : ℝ} (hr : 0 ≤ r) (hR : 0 ≤ R)
    (ha : 0 ≤ a) (hb : b ≤ π / 2) (hab : a ≤ b) :
    protonCross a r R ≤ protonCross b r R := by
  unfold protonCross
  apply sqrt_le_sqrt
  have hsin : sin a ≤ sin b :=
    strictMonoOn_sin.monotoneOn
      ⟨by linarith [pi_pos, ha], le_trans hab hb⟩ ⟨by linarith [pi_pos, ha], hb⟩ hab
  have hsa : 0 ≤ sin a := sin_nonneg_of_nonneg_of_le_pi ha
    (le_trans hab (le_trans hb (le_of_lt (half_lt_self pi_pos))))
  have hsb : 0 ≤ sin b := sin_nonneg_of_nonneg_of_le_pi (le_trans ha hab)
    (le_trans hb (le_of_lt (half_lt_self pi_pos)))
  have hsq : sin a ^ 2 ≤ sin b ^ 2 := by
    calc
      sin a ^ 2 = sin a * sin a := by ring
      _ ≤ sin b * sin b := mul_le_mul hsin hsin hsa hsb
      _ = sin b ^ 2 := by ring
  have hcoef : 0 ≤ 4 * r * R := by positivity
  have hdiff : 4 * r * R * sin a ^ 2 ≤ 4 * r * R * sin b ^ 2 :=
    mul_le_mul_of_nonneg_left hsq hcoef
  linarith [sq_nonneg (R - r)]

private theorem outer_proton_between {a r R : ℝ}
    (hr : 0 < r) (hR : r < R) (hchord : outerSep (equalChord r R))
    (ha : equalHalf r R ≤ a) (ha2 : a ≤ π / 2) :
    outerSep (protonSep a R) ∧ outerSep (protonCross a r R) := by
  have hRpos : 0 < R := lt_trans hr hR
  have hsepeq := protonSep_equal hr hR
  have hcrosseq := protonCross_equal hr hR
  have hhalf_lo : -(π / 2) ≤ equalHalf r R := (arcsin_mem_Icc _).1
  have hsep_ge : equalChord r R ≤ protonSep a R := by
    rw [← hsepeq]
    exact protonSep_mono hRpos hhalf_lo ha2 ha
  have hcross_ge : equalChord r R ≤ protonCross a r R := by
    rw [← hcrosseq]
    exact protonCross_mono hr.le hRpos.le (equalHalf_pos hr hR).le ha2 ha
  refine ⟨?_, ?_⟩
  · rcases eq_or_lt_of_le hsep_ge with heq | hlt
    · rw [← heq]; exact hchord
    · exact outerSep_of_gt hchord hlt
  · rcases eq_or_lt_of_le hcross_ge with heq | hlt
    · rw [← heq]; exact hchord
    · exact outerSep_of_gt hchord hlt

private theorem eight_sep_gt {r R : ℝ} (hr : 0 < r) (hR : r < R) (hq : R ≤ 4 * r) :
    (R + r) ^ 3 < 8 * R ^ 2 * r := by
  have hRpos : 0 < R := lt_trans hr hR
  set t := r / R with ht
  have ht_lo : (1 / 4 : ℝ) ≤ t := by
    rw [ht, le_div_iff₀ hRpos]
    linarith
  have ht_hi : t < 1 := by
    rw [ht, div_lt_one hRpos]
    exact hR
  have hquad : (1 / 16 : ℝ) ≤ t ^ 2 + 4 * t - 1 := by
    have hdiff : t ^ 2 + 4 * t - 1 - (1 / 16) = (t - 1 / 4) * (t + 17 / 4) := by ring
    have hnn : 0 ≤ (t - 1 / 4) * (t + 17 / 4) :=
      mul_nonneg (by linarith) (by linarith)
    linarith
  have hpos : 0 < (1 - t) * (t ^ 2 + 4 * t - 1) :=
    mul_pos (by linarith) (by linarith)
  have hid : 8 * t - (1 + t) ^ 3 = (1 - t) * (t ^ 2 + 4 * t - 1) := by ring
  have h8 : (1 + t) ^ 3 < 8 * t := by linarith
  have hscale : (1 + t) ^ 3 * R ^ 3 < 8 * t * R ^ 3 :=
    mul_lt_mul_of_pos_right h8 (pow_pos hRpos 3)
  have hsum : (1 + t) * R = R + r := by
    rw [ht]
    field_simp
  have hrad : t * R = r := by
    rw [ht]
    field_simp
  calc
    (R + r) ^ 3 = ((1 + t) * R) ^ 3 := by rw [hsum]
    _ = (1 + t) ^ 3 * R ^ 3 := by ring
    _ < 8 * t * R ^ 3 := hscale
    _ = 8 * R ^ 2 * (t * R) := by ring
    _ = 8 * R ^ 2 * r := by rw [hrad]

/-- On the straight line the parenthesis is negative once the electron is at
least a quarter as far out as the proton and the straight cross separation
lies in the outer well. -/
theorem protonParen_neg_straight {r R : ℝ}
    (hr : 0 < r) (hR : r < R) (hq : R ≤ 4 * r) (hcross : outerSep (R + r)) :
    protonParen (π / 2) r R < 0 := by
  have hRpos : 0 < R := lt_trans hr hR
  have h2R : outerSep (2 * R) := outerSep_of_gt hcross (by linarith)
  have hγ : gammaSEqual (pairPhase (R + r)) < gammaSEqual (pairPhase (2 * R)) := by
    refine gamma_strictAnti_phase ?_ hcross.2 ?_
    · unfold pairPhase
      positivity
    · unfold pairPhase
      rw [div_lt_div_iff₀ (by positivity) (by positivity)]
      nlinarith
  have hγc : 0 < gammaSEqual (pairPhase (R + r)) := outer_gamma_pos hcross
  have hγh : 0 < gammaSEqual (pairPhase (2 * R)) := outer_gamma_pos h2R
  have hcube := eight_sep_gt hr hR hq
  have hcmp : gammaSEqual (pairPhase (R + r)) * (R + r) ^ 3 <
      gammaSEqual (pairPhase (2 * R)) * (8 * R ^ 2 * r) := by
    have h1 : gammaSEqual (pairPhase (R + r)) * (R + r) ^ 3 <
        gammaSEqual (pairPhase (R + r)) * (8 * R ^ 2 * r) :=
      mul_lt_mul_of_pos_left hcube hγc
    have h2 : gammaSEqual (pairPhase (R + r)) * (8 * R ^ 2 * r) <
        gammaSEqual (pairPhase (2 * R)) * (8 * R ^ 2 * r) :=
      mul_lt_mul_of_pos_right hγ (by positivity)
    linarith
  unfold protonParen
  rw [protonSep_straight, protonCross_straight hr.le hRpos.le, sub_neg]
  rw [div_lt_div_iff₀ (mul_pos hγh (by positivity)) (mul_pos hγc (by positivity))]
  have hpow : (2 * R) ^ 3 = 8 * R ^ 3 := by ring
  rw [hpow]
  have hmul : R * (gammaSEqual (pairPhase (R + r)) * (R + r) ^ 3) <
      R * (gammaSEqual (pairPhase (2 * R)) * (8 * R ^ 2 * r)) :=
    mul_lt_mul_of_pos_left hcmp hRpos
  rw [show r * (gammaSEqual (pairPhase (2 * R)) * (8 * R ^ 3)) =
      R * (gammaSEqual (pairPhase (2 * R)) * (8 * R ^ 2 * r)) by ring]
  exact hmul

/-- While the protons are no farther apart than each is from the other
electron, and both separations lie in the outer well, the parenthesis is
positive. -/
theorem protonParen_pos_of_le {a r R : ℝ}
    (hr : 0 < r) (hR : r < R)
    (hh : outerSep (protonSep a R)) (hc : outerSep (protonCross a r R))
    (hle : protonSep a R ≤ protonCross a r R) :
    0 < protonParen a r R := by
  have hRpos : 0 < R := lt_trans hr hR
  set H := protonSep a R with hH
  set C := protonCross a r R with hC
  have hHpos : 0 < H := hh.1
  have hCpos : 0 < C := hc.1
  unfold protonParen
  rw [← hH, ← hC, sub_pos]
  rcases lt_or_eq_of_le hle with hlt | heq
  · have hphase : pairPhase C < pairPhase H := by
      unfold pairPhase
      rw [div_lt_div_iff₀ (by positivity) (by positivity)]
      linarith
    have hγ : gammaSEqual (pairPhase H) < gammaSEqual (pairPhase C) :=
      gamma_strictAnti_phase (by unfold pairPhase; positivity) hh.2 hphase
    have hsq : H ^ 2 < C ^ 2 := by
      calc
        H ^ 2 = H * H := by ring
        _ < C * H := mul_lt_mul_of_pos_right hlt hHpos
        _ < C * C := mul_lt_mul_of_pos_left hlt hCpos
        _ = C ^ 2 := by ring
    have hcube : H ^ 3 < C ^ 3 := by
      calc
        H ^ 3 = H ^ 2 * H := by ring
        _ < C ^ 2 * H := mul_lt_mul_of_pos_right hsq hHpos
        _ < C ^ 2 * C := mul_lt_mul_of_pos_left hlt (sq_pos_of_pos hCpos)
        _ = C ^ 3 := by ring
    have hγC : 0 < gammaSEqual (pairPhase C) := outer_gamma_pos hc
    have hden : gammaSEqual (pairPhase H) * H ^ 3 <
        gammaSEqual (pairPhase C) * C ^ 3 := by
      have h1 : gammaSEqual (pairPhase H) * H ^ 3 <
          gammaSEqual (pairPhase C) * H ^ 3 :=
        mul_lt_mul_of_pos_right hγ (pow_pos hHpos 3)
      have h2 : gammaSEqual (pairPhase C) * H ^ 3 <
          gammaSEqual (pairPhase C) * C ^ 3 :=
        mul_lt_mul_of_pos_left hcube hγC
      linarith
    have hdenH : 0 < gammaSEqual (pairPhase H) * H ^ 3 :=
      mul_pos (outer_gamma_pos hh) (pow_pos hHpos 3)
    have hdenC : 0 < gammaSEqual (pairPhase C) * C ^ 3 :=
      mul_pos hγC (pow_pos hCpos 3)
    have hRden : R / (gammaSEqual (pairPhase C) * C ^ 3) <
        R / (gammaSEqual (pairPhase H) * H ^ 3) := by
      rw [div_lt_div_iff₀ hdenC hdenH]
      nlinarith [hden]
    have hrden : r / (gammaSEqual (pairPhase C) * C ^ 3) <
        R / (gammaSEqual (pairPhase C) * C ^ 3) := by
      rw [div_lt_div_iff₀ hdenC hdenC]
      nlinarith
    linarith
  · rw [heq]
    have hdenC' : 0 < gammaSEqual (pairPhase C) * C ^ 3 :=
      mul_pos (outer_gamma_pos hc) (pow_pos hCpos 3)
    rw [div_lt_div_iff₀ hdenC' hdenC']
    nlinarith

private theorem protonCross_eq (a r R : ℝ) :
    protonCross a r R = sqrt (r ^ 2 + R ^ 2 - 2 * r * R * cos (2 * a)) := by
  unfold protonCross
  rw [← water_cross_expand]

private theorem sin_two_pos {a : ℝ} (ha : a ∈ Ioo 0 (π / 2)) : 0 < sin (2 * a) := by
  rw [sin_two_mul]
  have hsin : 0 < sin a :=
    sin_pos_of_pos_of_lt_pi ha.1 (lt_trans ha.2 (half_lt_self pi_pos))
  have hcos : 0 < cos a :=
    cos_pos_of_mem_Ioo ⟨by linarith [pi_pos, ha.1], ha.2⟩
  positivity

/-- The tangential force on the proton is `sin` of the bond angle times the
parenthesis. The nuclear charge does not appear. -/
theorem waterBendProton_factor {Z r R a : ℝ}
    (ha : a ∈ Ioo 0 π) (_hr : 0 < r) (hR : 0 < R)
    (hhh : outerSep (protonSep a R)) (hc : outerSep (protonCross a r R)) :
    waterBendProton Z r R a = sin (2 * a) * protonParen a r R := by
  have hsin : 0 < sin a := sin_pos_of_pos_of_lt_pi ha.1 ha.2
  have hh_pos : 0 < protonSep a R := hhh.1
  have hc_pos : 0 < protonCross a r R := hc.1
  have hγh : 0 < gammaSEqual (pairPhase (protonSep a R)) := outer_gamma_pos hhh
  have hγc : 0 < gammaSEqual (pairPhase (protonCross a r R)) := outer_gamma_pos hc
  have hvhh : vnorm (vsub (vsmul R (waterU a)) (vsmul R (waterV a))) =
      protonSep a R := by
    rw [vnorm_hh R a hR hsin]
    rfl
  have hvrc : vnorm (vsub (vsmul r (waterU a)) (vsmul R (waterV a))) =
      protonCross a r R := by
    unfold vnorm
    rw [vnorm2_cross, cos_sq_sub_sin_sq, protonCross_eq]
  have hden_h : gammaSEqual (pairPhase (vnorm
      (vsub (vsmul R (waterU a)) (vsmul R (waterV a))))) *
      vnorm (vsub (vsmul R (waterU a)) (vsmul R (waterV a))) ^ 3 ≠ 0 := by
    rw [hvhh]
    exact mul_ne_zero hγh.ne' (pow_ne_zero 3 hh_pos.ne')
  have hden_p : gammaSEqual (pairPhase (vnorm
      (vsub (vsmul R (waterU a)) (vsmul r (waterV a))))) *
      vnorm (vsub (vsmul R (waterU a)) (vsmul r (waterV a))) ^ 3 ≠ 0 := by
    rw [vnorm_cross_sym, hvrc]
    exact mul_ne_zero hγc.ne' (pow_ne_zero 3 hc_pos.ne')
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
      pairForce 1 (-1) (vsmul R (waterU a)) (vsmul r (waterU a)) i) = 0 :=
    vdot_pairForce_ortho (vdot_T_partner R r a)
  have hpe := vdot_pairForce 1 (-1)
    (vsmul R (waterU a)) (vsmul r (waterV a)) (waterT a) hden_p
  have hhh_c := vdot_pairForce 1 1
    (vsmul R (waterU a)) (vsmul R (waterV a)) (waterT a) hden_h
  rw [hnuc, hown, hpe, hhh_c, vdot_T_pe, vdot_T_hh, hvhh]
  have hcomm : vnorm (vsub (vsmul R (waterU a)) (vsmul r (waterV a))) =
      protonCross a r R := (vnorm_cross_sym r R a).trans hvrc
  rw [hcomm]
  unfold protonParen
  have hden1 : gammaSEqual (pairPhase (protonCross a r R)) *
      protonCross a r R ^ 3 ≠ 0 :=
    mul_ne_zero hγc.ne' (pow_ne_zero 3 hc_pos.ne')
  have hden2 : gammaSEqual (pairPhase (protonSep a R)) *
      protonSep a R ^ 3 ≠ 0 :=
    mul_ne_zero hγh.ne' (pow_ne_zero 3 hh_pos.ne')
  field_simp [hden1, hden2]
  ring

private theorem continuousOn_invSep {s : Set ℝ} {f : ℝ → ℝ}
    (hf : ContinuousOn f s) (hpos : ∀ a ∈ s, 0 < f a)
    (hγ : ∀ a ∈ s, gammaSEqual (pairPhase (f a)) ≠ 0) :
    ContinuousOn (fun a => 1 / (gammaSEqual (pairPhase (f a)) * f a ^ 3)) s := by
  have hpair : ContinuousOn pairPhase (Ioi 0) := by
    unfold pairPhase
    refine ContinuousOn.div continuousOn_const
      (continuous_const.mul continuous_id).continuousOn ?_
    intro x hx
    exact mul_ne_zero (by norm_num) (ne_of_gt hx)
  have hphase : ContinuousOn (fun a => pairPhase (f a)) s :=
    hpair.comp hf fun a ha => hpos a ha
  have hden : ContinuousOn (fun a => gammaSEqual (pairPhase (f a)) * f a ^ 3) s :=
    (continuous_gammaSEqual.comp_continuousOn hphase).mul (hf.pow 3)
  refine ContinuousOn.div continuousOn_const hden ?_
  intro a ha
  exact mul_ne_zero (hγ a ha) (pow_ne_zero 3 (hpos a ha).ne')

private theorem continuousOn_protonParen {r R : ℝ}
    (hr : 0 < r) (hR : r < R) (hchord : outerSep (equalChord r R)) :
    ContinuousOn (fun a => protonParen a r R) (Icc (equalHalf r R) (π / 2)) := by
  have hRpos : 0 < R := lt_trans hr hR
  have hsep : ContinuousOn (fun a => protonSep a R) (Icc (equalHalf r R) (π / 2)) := by
    unfold protonSep
    exact (continuous_const.mul continuous_sin).continuousOn
  have hcross : ContinuousOn (fun a => protonCross a r R)
      (Icc (equalHalf r R) (π / 2)) := by
    unfold protonCross
    refine continuous_sqrt.comp_continuousOn ?_
    exact ((continuous_const.add
      (continuous_const.mul (continuous_sin.pow 2))).continuousOn)
  have houter : ∀ a ∈ Icc (equalHalf r R) (π / 2),
      outerSep (protonSep a R) ∧ outerSep (protonCross a r R) := by
    intro a ha
    exact outer_proton_between hr hR hchord ha.1 ha.2
  have hinvH := continuousOn_invSep hsep
    (fun a ha => (houter a ha).1.1)
    (fun a ha => (outer_gamma_pos (houter a ha).1).ne')
  have hinvC := continuousOn_invSep hcross
    (fun a ha => (houter a ha).2.1)
    (fun a ha => (outer_gamma_pos (houter a ha).2).ne')
  have hleft : ContinuousOn (fun a =>
      R * (1 / (gammaSEqual (pairPhase (protonSep a R)) * protonSep a R ^ 3)))
      (Icc (equalHalf r R) (π / 2)) :=
    continuousOn_const.mul hinvH
  have hright : ContinuousOn (fun a =>
      r * (1 / (gammaSEqual (pairPhase (protonCross a r R)) *
        protonCross a r R ^ 3)))
      (Icc (equalHalf r R) (π / 2)) :=
    continuousOn_const.mul hinvC
  have hpoint (a : ℝ) : protonParen a r R =
      R * (1 / (gammaSEqual (pairPhase (protonSep a R)) * protonSep a R ^ 3)) -
        r * (1 / (gammaSEqual (pairPhase (protonCross a r R)) *
          protonCross a r R ^ 3)) := by
    unfold protonParen
    have h1 : R / (gammaSEqual (pairPhase (protonSep a R)) * protonSep a R ^ 3) =
        R * (1 / (gammaSEqual (pairPhase (protonSep a R)) * protonSep a R ^ 3)) :=
      div_eq_mul_one_div _ _
    have h2 : r / (gammaSEqual (pairPhase (protonCross a r R)) *
        protonCross a r R ^ 3) =
        r * (1 / (gammaSEqual (pairPhase (protonCross a r R)) *
          protonCross a r R ^ 3)) :=
      div_eq_mul_one_div _ _
    rw [h1, h2]
  refine ContinuousOn.congr (hleft.sub hright) ?_
  intro a _ha
  rw [Pi.sub_apply]
  exact hpoint a

/-- The protons hold an angle strictly between the equal separation and the
straight line. That equal separation is strictly less than a third of a
straight angle. A smaller angle, down to the equal separation, is driven
wider whenever the parenthesis has not changed sign, and the parenthesis is
positive there and negative on the straight line. -/
theorem water_proton_angle {Z r R : ℝ}
    (hr : 0 < r) (hR : r < R) (hq : R ≤ 4 * r)
    (hchord : outerSep (equalChord r R)) :
    equalHalf r R < π / 6 ∧
      0 < protonParen (equalHalf r R) r R ∧
      protonParen (π / 2) r R < 0 ∧
      ∃ a, equalHalf r R < a ∧ a < π / 2 ∧ waterBendProton Z r R a = 0 := by
  have hRpos : 0 < R := lt_trans hr hR
  have hlt := equalHalf_lt_pi_div_six hr hR
  have hpos : 0 < protonParen (equalHalf r R) r R := by
    have houter := outer_proton_between hr hR hchord le_rfl
      (lt_trans hlt (by linarith [pi_pos])).le
    have heq : protonSep (equalHalf r R) R = protonCross (equalHalf r R) r R := by
      rw [protonSep_equal hr hR, protonCross_equal hr hR]
    exact protonParen_pos_of_le hr hR houter.1 houter.2 heq.le
  have hfar : outerSep (R + r) := by
    refine outerSep_of_gt hchord ?_
    have hchord_lt : equalChord r R < R := by
      have hsq : equalChord r R ^ 2 = R * (R - r) := by
        unfold equalChord
        exact sq_sqrt (by nlinarith)
      have hlt2 : equalChord r R ^ 2 < R ^ 2 := by
        rw [hsq]
        nlinarith
      have habs : |equalChord r R| < |R| := (sq_lt_sq).mp hlt2
      have hchpos : 0 < equalChord r R := hchord.1
      rw [abs_of_pos hchpos, abs_of_pos hRpos] at habs
      exact habs
    linarith
  have hneg := protonParen_neg_straight hr hR hq hfar
  have hcont := continuousOn_protonParen hr hR hchord
  have hhalf_le : equalHalf r R ≤ π / 2 :=
    (lt_trans hlt (by linarith [pi_pos])).le
  have hzero : (0 : ℝ) ∈ Ioo (protonParen (π / 2) r R)
      (protonParen (equalHalf r R) r R) :=
    ⟨hneg, hpos⟩
  obtain ⟨a, ha, hfa⟩ :=
    intermediate_value_Ioo' hhalf_le hcont hzero
  have ha_pi : a ∈ Ioo 0 π :=
    ⟨lt_trans (equalHalf_pos hr hR) ha.1, lt_trans ha.2 (half_lt_self pi_pos)⟩
  have houter := outer_proton_between hr hR hchord ha.1.le ha.2.le
  have hfac := waterBendProton_factor (Z := Z) ha_pi hr hRpos houter.1 houter.2
  refine ⟨hlt, hpos, hneg, a, ha.1, ha.2, ?_⟩
  rw [hfac]
  have hzero_paren : protonParen a r R = 0 := by simpa using hfa
  rw [hzero_paren, mul_zero]

/-- At the equal separation the tangential force on the proton points toward
the wider angle. -/
theorem waterBendProton_equal_pos {Z r R : ℝ}
    (hr : 0 < r) (hR : r < R) (hchord : outerSep (equalChord r R)) :
    0 < waterBendProton Z r R (equalHalf r R) := by
  have hRpos : 0 < R := lt_trans hr hR
  have hlt := equalHalf_lt_pi_div_six hr hR
  have houter := outer_proton_between hr hR hchord le_rfl
    (lt_trans hlt (by linarith [pi_pos])).le
  have heq : protonSep (equalHalf r R) R = protonCross (equalHalf r R) r R := by
    rw [protonSep_equal hr hR, protonCross_equal hr hR]
  have hp := protonParen_pos_of_le hr hR houter.1 houter.2 heq.le
  have ha : equalHalf r R ∈ Ioo 0 (π / 2) :=
    ⟨equalHalf_pos hr hR, lt_trans hlt (by linarith [pi_pos])⟩
  have haπ : equalHalf r R ∈ Ioo 0 π :=
    ⟨ha.1, lt_trans ha.2 (half_lt_self pi_pos)⟩
  rw [waterBendProton_factor haπ hr hRpos houter.1 houter.2]
  exact mul_pos (sin_two_pos ha) hp

/-- Somewhere short of the straight line the tangential force on the proton
points toward the narrower angle. -/
theorem waterBendProton_narrow {Z r R : ℝ}
    (hr : 0 < r) (hR : r < R) (hq : R ≤ 4 * r)
    (hchord : outerSep (equalChord r R)) :
    ∃ a, equalHalf r R < a ∧ a < π / 2 ∧ waterBendProton Z r R a < 0 := by
  have hRpos : 0 < R := lt_trans hr hR
  have hlt := equalHalf_lt_pi_div_six hr hR
  have hhalf_le : equalHalf r R ≤ π / 2 := (lt_trans hlt (by linarith [pi_pos])).le
  have hpos : 0 < protonParen (equalHalf r R) r R := by
    have houter := outer_proton_between hr hR hchord le_rfl hhalf_le
    have heq : protonSep (equalHalf r R) R = protonCross (equalHalf r R) r R := by
      rw [protonSep_equal hr hR, protonCross_equal hr hR]
    exact protonParen_pos_of_le hr hR houter.1 houter.2 heq.le
  have hfar : outerSep (R + r) := by
    refine outerSep_of_gt hchord ?_
    have hsq : equalChord r R ^ 2 = R * (R - r) := by
      unfold equalChord
      exact sq_sqrt (by nlinarith)
    have hlt2 : equalChord r R ^ 2 < R ^ 2 := by
      rw [hsq]
      nlinarith
    have habs : |equalChord r R| < |R| := (sq_lt_sq).mp hlt2
    rw [abs_of_pos hchord.1, abs_of_pos hRpos] at habs
    linarith
  have hneg := protonParen_neg_straight hr hR hq hfar
  have hmid : protonParen (π / 2) r R / 2 ∈
      Ioo (protonParen (π / 2) r R) (protonParen (equalHalf r R) r R) := by
    constructor <;> linarith
  obtain ⟨a, ha, hfa⟩ :=
    intermediate_value_Ioo' hhalf_le (continuousOn_protonParen hr hR hchord) hmid
  have hparen : protonParen a r R < 0 := by
    have hval : protonParen a r R = protonParen (π / 2) r R / 2 := by
      simpa using hfa
    linarith
  have haπ : a ∈ Ioo 0 π :=
    ⟨lt_trans (equalHalf_pos hr hR) ha.1, lt_trans ha.2 (half_lt_self pi_pos)⟩
  have houter := outer_proton_between hr hR hchord ha.1.le ha.2.le
  have hprod : waterBendProton Z r R a < 0 := by
    rw [waterBendProton_factor haπ hr hRpos houter.1 houter.2]
    exact mul_neg_of_pos_of_neg (sin_two_pos ⟨haπ.1, ha.2⟩) hparen
  exact ⟨a, ha.1, ha.2, hprod⟩

end

end DstDiophantine.Gravity
