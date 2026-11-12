import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import DstDiophantine.Gravity.Blackbody

/-!
# Longitudinal excitation of an outermost electron

## Paper boundary (do **not** claim)

A collision rate, a cross section, and a mean free path are not derived.
`h` and `k_B` stay external. The growth of cavity modes as `ν²` is not a
consequence of the collision. No theorem retunes the frequency of one root
by the temperature or by the size of the impulse, and none identifies a
particular root with the peak of the enclosure.

## What is proved

* Along the line of centres the electron of larger radius is the closer one.
  A radial impulse deposits energy `p²/(2m)`, with no stiffness in that
  energy. The subsequent frequency is `√(κ/m)`, with no impulse in that
  frequency. A stiffer root has a higher frequency and, for the same
  impulse, a smaller amplitude.
* Two positive weights on two distinct frequencies have positive variance.
* Equipartition weights the two roots in a ratio independent of temperature.
  The Larmor weight `ν³/(e^{aν/T}-1)` does not: if `0 < ν₁ < ν₂`, the ratio
  of the higher weight to the lower one is strictly increasing in `T`, and
  so is the weighted mean, which remains strictly between `ν₁` and `ν₂`.
* The shape `x³/(eˣ-1)` has positive integral on `(1,2)` and on `(4,5)`,
  hence on both sides of its maximum in `(5/2,3)`.
* The mean of that shape is strictly between `3` and `4`, so it lies above
  the maximum. The mean frequency of the enclosure is that mean times `T/a`
  and is strictly increasing in `T`.
-/

namespace DstDiophantine

namespace Gravity

open Real Set Filter MeasureTheory Asymptotics Topology intervalIntegral

/-! ### The outermost electron on the line of centres -/

/-- Distance from an electron at radius `r` to a partner nucleus at `d`. -/
def separationToPartner (d r : ℝ) : ℝ :=
  d - r

/-- On the segment toward the partner, the larger radius is the closer electron. -/
theorem outer_closer {rInner rOuter d : ℝ} (h0 : 0 ≤ rInner) (hlt : rInner < rOuter)
    (hd : rOuter < d) :
    0 ≤ rInner ∧ 0 < separationToPartner d rOuter ∧
      separationToPartner d rOuter < separationToPartner d rInner := by
  refine ⟨h0, ?_, ?_⟩
  · unfold separationToPartner
    linarith
  · unfold separationToPartner
    linarith

/-- The electron that meets the partner is the one of greater radius. -/
theorem contact_eq_outer {rInner rOuter : ℝ} (hlt : rInner ≤ rOuter) :
    max rInner rOuter = rOuter :=
  max_eq_right hlt

/-! ### Longitudinal frequency, impulse, and amplitude -/

/-- Frequency `√(κ/m)` of a longitudinal displacement about a restoring root. -/
noncomputable def longitudinalOmega (κ m : ℝ) : ℝ :=
  Real.sqrt (κ / m)

/-- Linearised radial acceleration. The angular velocity does not enter. -/
noncomputable def radialAccel (κ m ξ : ℝ) : ℝ :=
  -(κ / m) * ξ

/-- Energy of the radial oscillator. -/
noncomputable def radialEnergy (m κ x v : ℝ) : ℝ :=
  m * v ^ 2 / 2 + κ * x ^ 2 / 2

/-- Amplitude reached from the root by an impulse `p`. -/
noncomputable def impulseAmplitude (m κ p : ℝ) : ℝ :=
  Real.sqrt (p ^ 2 / (m * κ))

theorem longitudinalOmega_sq {κ m : ℝ} (hκ : 0 ≤ κ) (hm : 0 < m) :
    longitudinalOmega κ m ^ 2 = κ / m := by
  unfold longitudinalOmega
  exact sq_sqrt (div_nonneg hκ hm.le)

theorem longitudinalOmega_pos {κ m : ℝ} (hκ : 0 < κ) (hm : 0 < m) :
    0 < longitudinalOmega κ m := by
  unfold longitudinalOmega
  exact sqrt_pos.mpr (div_pos hκ hm)

/-- A stiffer root has a strictly higher longitudinal frequency. -/
theorem longitudinalOmega_strictMono {m κ1 κ2 : ℝ} (hm : 0 < m) (hκ1 : 0 < κ1)
    (hκ : κ1 < κ2) :
    longitudinalOmega κ1 m < longitudinalOmega κ2 m := by
  unfold longitudinalOmega
  refine sqrt_lt_sqrt (div_nonneg hκ1.le hm.le) ?_
  exact (div_lt_div_iff_of_pos_right hm).mpr hκ

theorem radialAccel_eq_omega {κ m ξ : ℝ} (hκ : 0 ≤ κ) (hm : 0 < m) :
    radialAccel κ m ξ = -(longitudinalOmega κ m ^ 2) * ξ := by
  unfold radialAccel
  rw [longitudinalOmega_sq hκ hm]

/-- From rest at the root, the deposited energy is `p²/(2m)`. The stiffness is absent. -/
theorem impulse_energy {m κ p : ℝ} (hm : m ≠ 0) :
    radialEnergy m κ 0 (p / m) = p ^ 2 / (2 * m) := by
  unfold radialEnergy
  field_simp [hm]
  ring

theorem impulseAmplitude_sq {m κ p : ℝ} (hm : 0 < m) (hκ : 0 < κ) :
    impulseAmplitude m κ p ^ 2 = p ^ 2 / (m * κ) := by
  unfold impulseAmplitude
  exact sq_sqrt (div_nonneg (sq_nonneg p) (mul_pos hm hκ).le)

/-- The same impulse reaches a smaller amplitude on a stiffer root. -/
theorem impulseAmplitude_strictAnti {m κ1 κ2 p : ℝ} (hm : 0 < m) (hp : p ≠ 0)
    (hκ1 : 0 < κ1) (hκ : κ1 < κ2) :
    impulseAmplitude m κ2 p < impulseAmplitude m κ1 p := by
  unfold impulseAmplitude
  refine sqrt_lt_sqrt (div_nonneg (sq_nonneg p) (mul_pos hm (hκ1.trans hκ)).le) ?_
  rw [div_lt_div_iff₀ (mul_pos hm (hκ1.trans hκ)) (mul_pos hm hκ1)]
  have hp2 : 0 < p ^ 2 := sq_pos_of_ne_zero hp
  exact mul_lt_mul_of_pos_left (mul_lt_mul_of_pos_left hκ hm) hp2

/-- At the turning point the deposited energy is again `p²/(2m)`. -/
theorem amplitude_energy {m κ p : ℝ} (hm : 0 < m) (hκ : 0 < κ) :
    radialEnergy m κ (impulseAmplitude m κ p) 0 = p ^ 2 / (2 * m) := by
  unfold radialEnergy
  rw [impulseAmplitude_sq hm hκ]
  field_simp
  ring

/-! ### A mixture of two frequencies is not one frequency -/

/-- Mean frequency of two weighted roots. -/
noncomputable def weightedMean (w1 w2 ν1 ν2 : ℝ) : ℝ :=
  (w1 * ν1 + w2 * ν2) / (w1 + w2)

theorem weightedMean_mem_Ioo {w1 w2 ν1 ν2 : ℝ} (hw1 : 0 < w1) (hw2 : 0 < w2)
    (hν : ν1 < ν2) :
    ν1 < weightedMean w1 w2 ν1 ν2 ∧ weightedMean w1 w2 ν1 ν2 < ν2 := by
  unfold weightedMean
  have hden : 0 < w1 + w2 := by linarith
  constructor
  · rw [lt_div_iff₀ hden]
    nlinarith
  · rw [div_lt_iff₀ hden]
    nlinarith

theorem mixtureVar_eq {w1 w2 ν1 ν2 : ℝ} (hw : w1 + w2 ≠ 0) :
    (w1 * (ν1 - weightedMean w1 w2 ν1 ν2) ^ 2 +
        w2 * (ν2 - weightedMean w1 w2 ν1 ν2) ^ 2) / (w1 + w2) =
      w1 * w2 * (ν1 - ν2) ^ 2 / (w1 + w2) ^ 2 := by
  unfold weightedMean
  field_simp [hw]
  ring

theorem mixtureVar_pos {w1 w2 ν1 ν2 : ℝ} (hw1 : 0 < w1) (hw2 : 0 < w2) (hν : ν1 ≠ ν2) :
    0 < w1 * w2 * (ν1 - ν2) ^ 2 / (w1 + w2) ^ 2 := by
  have hden : 0 < (w1 + w2) ^ 2 := by positivity
  exact div_pos (mul_pos (mul_pos hw1 hw2) (sq_pos_of_ne_zero (sub_ne_zero.mpr hν))) hden

/-- Raising the relative weight of the higher frequency raises the mean. -/
theorem weightedMean_lt_of_ratio_lt {w1 w2 w1' w2' ν1 ν2 : ℝ}
    (hw1 : 0 < w1) (hw2 : 0 < w2) (hw1' : 0 < w1') (hw2' : 0 < w2')
    (hν : ν1 < ν2) (hr : w2 / w1 < w2' / w1') :
    weightedMean w1 w2 ν1 ν2 < weightedMean w1' w2' ν1 ν2 := by
  unfold weightedMean
  have hden : 0 < w1 + w2 := by linarith
  have hden' : 0 < w1' + w2' := by linarith
  rw [div_lt_div_iff₀ hden hden']
  have hcross : w2 * w1' < w1 * w2' := by
    rw [div_lt_div_iff₀ hw1 hw1'] at hr
    linarith
  nlinarith

/-! ### Equipartition stands still; the Larmor weight shifts -/

/-- Classical power of one root, proportional to `T ν²`. -/
def classicalWeight (T ν : ℝ) : ℝ :=
  T * ν ^ 2

theorem classicalWeight_ratio_eq {T1 T2 ν1 ν2 : ℝ} (hT1 : T1 ≠ 0) (hT2 : T2 ≠ 0)
    (hν : ν1 ≠ 0) :
    classicalWeight T2 ν2 / classicalWeight T2 ν1 =
      classicalWeight T1 ν2 / classicalWeight T1 ν1 := by
  unfold classicalWeight
  field_simp [hT1, hT2, hν]

/-- Quantum Larmor weight of one longitudinal root, proportional to `ν³/(e^{aν/T}-1)`. -/
noncomputable def larmorWeight (a T ν : ℝ) : ℝ :=
  ν ^ 3 / (exp (a * ν / T) - 1)

theorem larmorWeight_pos {a T ν : ℝ} (ha : 0 < a) (hT : 0 < T) (hν : 0 < ν) :
    0 < larmorWeight a T ν := by
  unfold larmorWeight
  exact div_pos (by positivity) (sub_pos.mpr (one_lt_exp_iff.mpr (by positivity)))

private noncomputable def ratioDeficit (lam x : ℝ) : ℝ :=
  (1 - lam) + lam * exp (-x) - exp (-lam * x)

private theorem ratioDeficit_zero (lam : ℝ) : ratioDeficit lam 0 = 0 := by
  unfold ratioDeficit
  simp [exp_zero]

private theorem hasDerivAt_ratioDeficit (lam x : ℝ) :
    HasDerivAt (ratioDeficit lam) (lam * (exp (-lam * x) - exp (-x))) x := by
  unfold ratioDeficit
  have hconst : HasDerivAt (fun _ : ℝ => (1 : ℝ) - lam) 0 x := hasDerivAt_const x _
  have hneg : HasDerivAt (fun y : ℝ => -y) (-1) x := (hasDerivAt_id' x).neg
  have h1 : HasDerivAt (fun y : ℝ => exp (-y)) (exp (-x) * -1) x := by
    convert (hasDerivAt_exp (-x)).comp x hneg using 1
    funext y
    rfl
  have hlin : HasDerivAt (fun y : ℝ => -lam * y) (-lam * 1) x :=
    (hasDerivAt_id' x).const_mul (-lam)
  have h2 : HasDerivAt (fun y : ℝ => exp (-lam * y)) (exp (-lam * x) * (-lam * 1)) x := by
    convert (hasDerivAt_exp (-lam * x)).comp x hlin using 1
    funext y
    rfl
  convert ((hconst.add (h1.const_mul lam)).sub h2) using 1; ring_nf

private theorem ratioDeficit_neg {lam x : ℝ} (hlam : 1 < lam) (hx : 0 < x) :
    ratioDeficit lam x < 0 := by
  have hcont : ContinuousOn (ratioDeficit lam) (Ici 0) := by
    unfold ratioDeficit
    exact ((continuous_const.add (continuous_const.mul (continuous_exp.comp continuous_neg))).sub
      (continuous_exp.comp (continuous_const.mul continuous_id))).continuousOn
  have hanti : StrictAntiOn (ratioDeficit lam) (Ici 0) := by
    refine strictAntiOn_of_deriv_neg (convex_Ici 0) hcont ?_
    intro y hy
    rw [interior_Ici, mem_Ioi] at hy
    rw [(hasDerivAt_ratioDeficit lam y).deriv]
    have horder : exp (-lam * y) < exp (-y) := exp_lt_exp.mpr (by nlinarith)
    exact mul_neg_of_pos_of_neg (by linarith) (sub_neg.mpr horder)
  have hxI : x ∈ Ici (0 : ℝ) := mem_Ici.mpr hx.le
  have h0 : (0 : ℝ) ∈ Ici 0 := mem_Ici.mpr le_rfl
  simpa [ratioDeficit_zero lam] using hanti h0 hxI hx

private noncomputable def occupationRatio (lam x : ℝ) : ℝ :=
  (exp x - 1) / (exp (lam * x) - 1)

private theorem hasDerivAt_occupationRatio {lam x : ℝ} (hlam : 1 < lam) (hx : 0 < x) :
    HasDerivAt (occupationRatio lam)
      ((exp x * (exp (lam * x) - 1) - (exp x - 1) * (lam * exp (lam * x))) /
        (exp (lam * x) - 1) ^ 2) x := by
  unfold occupationRatio
  have hf : HasDerivAt (fun y : ℝ => exp y - 1) (exp x - 0) x :=
    (hasDerivAt_exp x).sub (hasDerivAt_const x (1 : ℝ))
  have hlin : HasDerivAt (fun y : ℝ => lam * y) (lam * 1) x :=
    (hasDerivAt_id' x).const_mul lam
  have hg : HasDerivAt (fun y : ℝ => exp (lam * y) - 1)
      (exp (lam * x) * (lam * 1) - 0) x := by
    convert ((hasDerivAt_exp (lam * x)).comp x hlin).sub (hasDerivAt_const x (1 : ℝ)) using 1
    funext y
    rfl
  have hden : exp (lam * x) - 1 ≠ 0 :=
    sub_ne_zero.mpr (one_lt_exp_iff.mpr (by positivity)).ne'
  convert hf.div hg hden using 1; ring_nf

private theorem occupationNumerator_eq {lam x : ℝ} :
    exp x * (exp (lam * x) - 1) - (exp x - 1) * (lam * exp (lam * x)) =
      exp ((1 + lam) * x) * ratioDeficit lam x := by
  unfold ratioDeficit
  have hsum : exp x * exp (lam * x) = exp ((1 + lam) * x) := by
    rw [← exp_add]
    ring_nf
  have hlam : exp ((1 + lam) * x) * exp (-x) = exp (lam * x) := by
    rw [← exp_add]
    ring_nf
  have hx' : exp ((1 + lam) * x) * exp (-lam * x) = exp x := by
    rw [← exp_add]
    ring_nf
  calc
    exp x * (exp (lam * x) - 1) - (exp x - 1) * (lam * exp (lam * x))
        = exp x * exp (lam * x) - exp x - lam * exp x * exp (lam * x) +
            lam * exp (lam * x) := by ring
    _ = (1 - lam) * exp ((1 + lam) * x) - exp x + lam * exp (lam * x) := by
          have hmul : lam * exp x * exp (lam * x) = lam * exp ((1 + lam) * x) := by
            rw [mul_assoc, hsum]
          rw [hsum, hmul]
          ring_nf
    _ = (1 - lam) * exp ((1 + lam) * x) + lam * (exp ((1 + lam) * x) * exp (-x)) -
          exp ((1 + lam) * x) * exp (-lam * x) := by
          rw [hlam, hx']
          ring_nf
    _ = exp ((1 + lam) * x) * ((1 - lam) + lam * exp (-x) - exp (-lam * x)) := by
          ring_nf

private theorem occupationRatio_deriv_neg {lam x : ℝ} (hlam : 1 < lam) (hx : 0 < x) :
    deriv (occupationRatio lam) x < 0 := by
  rw [(hasDerivAt_occupationRatio hlam hx).deriv]
  refine div_neg_of_neg_of_pos ?_ ?_
  · rw [occupationNumerator_eq]
    exact mul_neg_of_pos_of_neg (exp_pos _) (ratioDeficit_neg hlam hx)
  · exact sq_pos_of_pos (sub_pos.mpr (one_lt_exp_iff.mpr (by positivity)))

private theorem occupationRatio_strictAnti {lam : ℝ} (hlam : 1 < lam) :
    StrictAntiOn (occupationRatio lam) (Ioi 0) := by
  refine strictAntiOn_of_deriv_neg (convex_Ioi 0) ?_ ?_
  · unfold occupationRatio
    refine ContinuousOn.div (continuous_exp.sub continuous_const).continuousOn
      ((continuous_exp.comp (continuous_const.mul continuous_id)).sub
        continuous_const).continuousOn ?_
    intro x hx
    have hx0 : 0 < x := hx
    exact sub_ne_zero.mpr (one_lt_exp_iff.mpr (by nlinarith [hlam, hx0])).ne'
  · intro x hx
    rw [interior_Ioi] at hx
    exact occupationRatio_deriv_neg hlam hx

/-- For `0 < ν₁ < ν₂`, the ratio of the higher Larmor weight to the lower one
increases strictly with temperature. -/
theorem larmorWeight_ratio_strictMono {a ν1 ν2 T1 T2 : ℝ} (ha : 0 < a) (hν : 0 < ν1)
    (hlt : ν1 < ν2) (hT1 : 0 < T1) (hT : T1 < T2) :
    larmorWeight a T1 ν2 / larmorWeight a T1 ν1 <
      larmorWeight a T2 ν2 / larmorWeight a T2 ν1 := by
  have hν2 : 0 < ν2 := hν.trans hlt
  have hT2 : 0 < T2 := hT1.trans hT
  have hden1 : exp (a * ν1 / T1) - 1 ≠ 0 :=
    sub_ne_zero.mpr (one_lt_exp_iff.mpr (by positivity)).ne'
  have hden2 : exp (a * ν2 / T1) - 1 ≠ 0 :=
    sub_ne_zero.mpr (one_lt_exp_iff.mpr (by positivity)).ne'
  have hden1' : exp (a * ν1 / T2) - 1 ≠ 0 :=
    sub_ne_zero.mpr (one_lt_exp_iff.mpr (by positivity)).ne'
  have hden2' : exp (a * ν2 / T2) - 1 ≠ 0 :=
    sub_ne_zero.mpr (one_lt_exp_iff.mpr (by positivity)).ne'
  have hlam : 1 < ν2 / ν1 := (one_lt_div hν).mpr hlt
  have hx1 : 0 < a * ν1 / T1 := by positivity
  have hx2 : 0 < a * ν1 / T2 := by positivity
  have hxlt : a * ν1 / T2 < a * ν1 / T1 := by
    rw [div_lt_div_iff₀ hT2 hT1]
    exact mul_lt_mul_of_pos_left hT (mul_pos ha hν)
  have hanti := occupationRatio_strictAnti hlam
    (mem_Ioi.mpr hx2) (mem_Ioi.mpr hx1) hxlt
  have hscale1 : a * ν2 / T1 = (ν2 / ν1) * (a * ν1 / T1) := by field_simp
  have hscale2 : a * ν2 / T2 = (ν2 / ν1) * (a * ν1 / T2) := by field_simp
  unfold occupationRatio at hanti
  rw [← hscale1, ← hscale2] at hanti
  -- Both ratios equal `(ν2/ν1)³` times the occupation ratio.
  have hpow : 0 < (ν2 / ν1) ^ 3 := by positivity
  have hleft : larmorWeight a T1 ν2 / larmorWeight a T1 ν1 =
      (ν2 / ν1) ^ 3 * ((exp (a * ν1 / T1) - 1) / (exp (a * ν2 / T1) - 1)) := by
    unfold larmorWeight
    field_simp [hden1, hden2, hν.ne', hν2.ne']
  have hright : larmorWeight a T2 ν2 / larmorWeight a T2 ν1 =
      (ν2 / ν1) ^ 3 * ((exp (a * ν1 / T2) - 1) / (exp (a * ν2 / T2) - 1)) := by
    unfold larmorWeight
    field_simp [hden1', hden2', hν.ne', hν2.ne']
  rw [hleft, hright]
  exact mul_lt_mul_of_pos_left hanti hpow

/-- The weighted mean of two longitudinal frequencies increases with temperature. -/
theorem larmorMean_strictMono {a ν1 ν2 T1 T2 : ℝ} (ha : 0 < a) (hν : 0 < ν1)
    (hlt : ν1 < ν2) (hT1 : 0 < T1) (hT : T1 < T2) :
    weightedMean (larmorWeight a T1 ν1) (larmorWeight a T1 ν2) ν1 ν2 <
      weightedMean (larmorWeight a T2 ν1) (larmorWeight a T2 ν2) ν1 ν2 := by
  have hν2 : 0 < ν2 := hν.trans hlt
  have hT2 : 0 < T2 := hT1.trans hT
  exact weightedMean_lt_of_ratio_lt (larmorWeight_pos ha hT1 hν)
    (larmorWeight_pos ha hT1 hν2) (larmorWeight_pos ha hT2 hν)
    (larmorWeight_pos ha hT2 hν2) hlt
    (larmorWeight_ratio_strictMono ha hν hlt hT1 hT)

/-! ### Both sides of the maximum carry mass -/

theorem planckShape_pos {n : ℕ} {x : ℝ} (hx : 0 < x) : 0 < planckShape n x := by
  unfold planckShape
  exact div_pos (by positivity) (sub_pos.mpr (one_lt_exp_iff.mpr hx))

private theorem continuousOn_planckShape3 {a b : ℝ} (ha : 0 < a) (_hab : a ≤ b) :
    ContinuousOn (planckShape 3) (Icc a b) := by
  unfold planckShape
  refine ContinuousOn.div (continuous_pow 3).continuousOn
    ((continuous_exp.sub continuous_const).continuousOn) ?_
  intro x hx
  exact sub_ne_zero.mpr (one_lt_exp_iff.mpr (lt_of_lt_of_le ha hx.1)).ne'

theorem shape_interval_pos {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    0 < ∫ x in a..b, planckShape 3 x := by
  refine intervalIntegral.integral_pos hab (continuousOn_planckShape3 ha hab.le) ?_ ?_
  · intro x hx
    exact (planckShape_pos (lt_trans ha hx.1)).le
  · exact ⟨a, left_mem_Icc.mpr hab.le, planckShape_pos ha⟩

/-- The shape has positive mass on `(1,2)`, below the frequency maximum. -/
theorem shapeMass_below_peak : 0 < ∫ x in (1 : ℝ)..2, planckShape 3 x :=
  shape_interval_pos (by norm_num) (by norm_num)

/-- The shape has positive mass on `(4,5)`, above the frequency maximum. -/
theorem shapeMass_above_peak : 0 < ∫ x in (4 : ℝ)..5, planckShape 3 x :=
  shape_interval_pos (by norm_num) (by norm_num)

/-! ### The mean of the shape lies strictly between `3` and `4` -/

/-- `∑ n⁻⁵`, with the `n = 0` term read as zero. -/
noncomputable def zetaFive : ℝ :=
  ∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 5

theorem zetaFive_summable : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 5) := by
  refine hasSum_zeta_four.summable.of_nonneg_of_le ?_ ?_
  · intro n
    exact div_nonneg (by norm_num) (pow_nonneg (Nat.cast_nonneg n) 5)
  · intro n
    cases n with
    | zero => simp
    | succ n =>
      have ha : 0 < ((n + 1 : ℕ) : ℝ) ^ 5 := by positivity
      have hb : 0 < ((n + 1 : ℕ) : ℝ) ^ 4 := by positivity
      rw [div_le_div_iff₀ ha hb]
      have h1 : (1 : ℝ) ≤ (n + 1 : ℕ) := by
        exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
      have hpow : ((n + 1 : ℕ) : ℝ) ^ 4 * 1 ≤ ((n + 1 : ℕ) : ℝ) ^ 4 * (n + 1 : ℕ) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
      simpa [pow_succ, mul_comm] using hpow

theorem zetaFive_gt_one : (1 : ℝ) < zetaFive := by
  have hs := zetaFive_summable
  rw [zetaFive, hs.tsum_eq_zero_add]
  have h0 : (1 : ℝ) / ((0 : ℕ) : ℝ) ^ 5 = 0 := by norm_num
  rw [h0, zero_add]
  have hs1 : Summable (fun n : ℕ => (1 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 5) :=
    hs.comp_injective Nat.succ_injective
  rw [hs1.tsum_eq_zero_add]
  have h1 : (1 : ℝ) / ((0 + 1 : ℕ) : ℝ) ^ 5 = 1 := by norm_num
  rw [h1]
  have hrest : 0 < ∑' n : ℕ, (1 : ℝ) / (((n + 1) + 1 : ℕ) : ℝ) ^ 5 := by
    refine Summable.tsum_pos (hs1.comp_injective Nat.succ_injective) ?_ 0 ?_
    · intro n
      exact div_nonneg (by norm_num) (pow_nonneg (Nat.cast_nonneg _) _)
    · norm_num
  linarith

theorem zetaFive_lt_zetaFour : zetaFive < Real.pi ^ 4 / 90 := by
  rw [zetaFive, ← hasSum_zeta_four.tsum_eq]
  refine Summable.tsum_lt_tsum_of_nonneg (i := 2) ?_ ?_ ?_ hasSum_zeta_four.summable
  · intro n
    exact div_nonneg (by norm_num) (pow_nonneg (Nat.cast_nonneg n) 5)
  · intro n
    cases n with
    | zero => simp
    | succ n =>
      have ha : 0 < ((n + 1 : ℕ) : ℝ) ^ 5 := by positivity
      have hb : 0 < ((n + 1 : ℕ) : ℝ) ^ 4 := by positivity
      rw [div_le_div_iff₀ ha hb]
      have h1 : (1 : ℝ) ≤ (n + 1 : ℕ) := by
        exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
      have hpow : ((n + 1 : ℕ) : ℝ) ^ 4 * 1 ≤ ((n + 1 : ℕ) : ℝ) ^ 4 * (n + 1 : ℕ) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
      simpa [pow_succ, mul_comm] using hpow
  · norm_num

private theorem tendsto_pow_four_exp_half {m : ℝ} (hm : 0 < m) :
    Tendsto (fun x : ℝ => x ^ 4 * exp (-(m / 2) * x)) atTop (𝓝 0) := by
  have hz : Tendsto (fun x : ℝ => (m / 2) * x) atTop atTop :=
    Tendsto.const_mul_atTop (by positivity : 0 < m / 2) tendsto_id
  have hscaled := (tendsto_pow_mul_exp_neg_atTop_nhds_zero 4).comp hz |>.const_mul ((2 / m) ^ 4)
  rw [mul_zero] at hscaled
  refine hscaled.congr fun x => ?_
  have hmul : (2 / m) * ((m / 2) * x) = x := by field_simp
  have hexp : -((m / 2) * x) = -(m / 2) * x := by ring
  calc
    (2 / m) ^ 4 * (((m / 2) * x) ^ 4 * exp (-((m / 2) * x)))
        = ((2 / m) ^ 4 * ((m / 2) * x) ^ 4) * exp (-((m / 2) * x)) := by ring
    _ = ((2 / m) * ((m / 2) * x)) ^ 4 * exp (-((m / 2) * x)) := by rw [← mul_pow]
    _ = x ^ 4 * exp (-(m / 2) * x) := by rw [hmul, hexp]

private theorem integrableOn_pow_four_exp {m : ℝ} (hm : 0 < m) :
    IntegrableOn (fun x : ℝ => x ^ 4 * exp (-m * x)) (Ioi 0) := by
  refine integrable_of_isBigO_exp_neg (b := m / 2) (by positivity) (by fun_prop) ?_
  · rw [isBigO_iff]
    refine ⟨1, ?_⟩
    have hsmall :=
      (tendsto_pow_four_exp_half hm).eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
    filter_upwards [hsmall, eventually_ge_atTop (0 : ℝ)] with x hx hx0
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    have hsplit : x ^ 4 * exp (-m * x) =
        (x ^ 4 * exp (-(m / 2) * x)) * exp (-(m / 2) * x) := by
      have harg : -m * x = -(m / 2) * x + -(m / 2) * x := by ring
      rw [harg, exp_add, ← mul_assoc]
    have hpre : 0 ≤ x ^ 4 * exp (-(m / 2) * x) := by positivity
    rw [hsplit, abs_mul, abs_of_nonneg hpre, abs_of_pos (exp_pos _)]
    exact mul_le_mul_of_nonneg_right (le_of_lt hx) (exp_pos _).le

private theorem integral_pow_four_exp {m : ℝ} (hm : 0 < m) :
    ∫ x in Ioi (0 : ℝ), x ^ 4 * exp (-m * x) = 24 / m ^ 5 := by
  have hkey := integral_rpow_mul_exp_neg_mul_Ioi (a := 5) (r := m) (by norm_num) hm
  have hagree : EqOn (fun x : ℝ => x ^ ((5 : ℝ) - 1) * exp (-(m * x)))
      (fun x => x ^ 4 * exp (-m * x)) (Ioi 0) := by
    intro x _
    change x ^ ((5 : ℝ) - 1) * exp (-(m * x)) = x ^ 4 * exp (-m * x)
    rw [show (5 : ℝ) - 1 = ((4 : ℕ) : ℝ) by norm_num, rpow_natCast x 4]
    have harg : -(m * x) = -m * x := by ring
    rw [harg]
  have hsame : ∫ x in Ioi (0 : ℝ), x ^ 4 * exp (-m * x) =
      ∫ x in Ioi (0 : ℝ), x ^ ((5 : ℝ) - 1) * exp (-(m * x)) :=
    (setIntegral_congr_fun (μ := volume) measurableSet_Ioi hagree).symm
  have hΓ : Gamma 5 = 24 := by simp [Nat.factorial]
  rw [hsame, hkey, hΓ]
  conv_lhs =>
    arg 1
    rw [show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num]
    rw [rpow_natCast (1 / m) 5]
  rw [div_pow, one_pow, div_mul_eq_mul_div, one_mul]

private noncomputable def momentTerm (n : ℕ) (x : ℝ) : ℝ :=
  x ^ 4 * exp (-((n + 1 : ℕ) : ℝ) * x)

private theorem momentTerm_eq_pow {x : ℝ} (n : ℕ) :
    exp (-((n + 1 : ℕ) : ℝ) * x) = exp (-x) ^ (n + 1) := by
  rw [← exp_nat_mul (-x) (n + 1)]
  congr 1
  push_cast
  ring

private theorem geom_shift {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∑' n : ℕ, r ^ (n + 1) = r / (1 - r) := by
  have hgeom := tsum_geometric_of_lt_one hr0 hr1
  simp_rw [pow_succ]
  rw [tsum_mul_right, hgeom, mul_comm, ← div_eq_mul_inv]

private theorem exp_neg_div_sub {x : ℝ} (hx : 0 < x) :
    exp (-x) / (1 - exp (-x)) = 1 / (exp x - 1) := by
  have hex : exp x ≠ 0 := (exp_pos x).ne'
  have hlt : exp (-x) < 1 := exp_lt_one_iff.mpr (neg_lt_zero.mpr hx)
  calc
    exp (-x) / (1 - exp (-x))
        = (exp (-x) * exp x) / ((1 - exp (-x)) * exp x) := by
          field_simp [hex, sub_ne_zero.mpr hlt.ne]
    _ = 1 / (exp x - 1) := by
          rw [← exp_add, neg_add_cancel, exp_zero, sub_mul, one_mul, ← exp_add,
            neg_add_cancel, exp_zero]

private theorem momentTerm_tsum {x : ℝ} (hx : 0 < x) :
    ∑' n : ℕ, momentTerm n x = planckShape 4 x := by
  unfold momentTerm planckShape
  simp_rw [momentTerm_eq_pow]
  have hr0 : 0 ≤ exp (-x) := (exp_pos _).le
  have hr1 : exp (-x) < 1 := exp_lt_one_iff.mpr (neg_lt_zero.mpr hx)
  rw [tsum_mul_left, geom_shift hr0 hr1, exp_neg_div_sub hx, mul_div_assoc', mul_one]

private theorem integral_momentTerm (n : ℕ) :
    ∫ x in Ioi (0 : ℝ), momentTerm n x = 24 / ((n + 1 : ℕ) : ℝ) ^ 5 := by
  simpa [momentTerm] using integral_pow_four_exp (m := ((n + 1 : ℕ) : ℝ)) (by positivity)

private theorem momentTerm_integral_norm (n : ℕ) :
    ∫ x in Ioi (0 : ℝ), ‖momentTerm n x‖ = 24 / ((n + 1 : ℕ) : ℝ) ^ 5 := by
  have hnn : ∀ x ∈ Ioi (0 : ℝ), 0 ≤ momentTerm n x := by
    intro x hx
    unfold momentTerm
    exact mul_nonneg (pow_nonneg hx.le 4) (exp_pos _).le
  rw [setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_]
  · exact integral_momentTerm n
  · rw [Real.norm_eq_abs, abs_of_nonneg (hnn x hx)]

private theorem zetaFive_shift :
    ∑' n : ℕ, (1 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 5 = zetaFive := by
  have hs := zetaFive_summable
  rw [zetaFive, hs.tsum_eq_zero_add]
  have h0 : (1 : ℝ) / ((0 : ℕ) : ℝ) ^ 5 = 0 := by norm_num
  rw [h0, zero_add]

private theorem sum_moment_integrals :
    ∑' n : ℕ, ∫ x in Ioi (0 : ℝ), momentTerm n x = 24 * zetaFive := by
  simp_rw [integral_momentTerm]
  calc
    ∑' n : ℕ, (24 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 5
        = 24 * ∑' n : ℕ, (1 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 5 := by
          rw [← tsum_mul_left]
          congr
          ext n
          ring
    _ = 24 * zetaFive := by rw [zetaFive_shift]

/-- `∫₀^∞ x⁴/(eˣ-1) dx = 24 ∑ n⁻⁵`. -/
theorem momentIntegral : ∫ x in Ioi (0 : ℝ), planckShape 4 x = 24 * zetaFive := by
  have hint : ∀ n : ℕ, Integrable (momentTerm n) (volume.restrict (Ioi (0 : ℝ))) := by
    intro n
    refine Integrable.congr
      (integrableOn_pow_four_exp (m := ((n + 1 : ℕ) : ℝ)) (by positivity)).integrable ?_
    filter_upwards with x
    unfold momentTerm
    congr 1
  have hsum : Summable fun n => ∫ x, ‖momentTerm n x‖ ∂(volume.restrict (Ioi (0 : ℝ))) := by
    simp_rw [momentTerm_integral_norm]
    have hzeta : Summable fun n : ℕ => (1 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 5 :=
      zetaFive_summable.comp_injective Nat.succ_injective
    have hmul : (fun n : ℕ => (24 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 5) =
        fun n => 24 * ((1 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 5) := by
      funext n
      ring
    rw [hmul]
    exact hzeta.mul_left 24
  have hswap := integral_tsum_of_summable_integral_norm hint hsum
  have hseries : EqOn (fun x => ∑' n, momentTerm n x) (planckShape 4) (Ioi 0) :=
    fun x hx => momentTerm_tsum hx
  calc
    ∫ x in Ioi 0, planckShape 4 x
        = ∫ x in Ioi 0, ∑' n, momentTerm n x := by
          exact setIntegral_congr_fun measurableSet_Ioi fun _ hx => (hseries hx).symm
    _ = ∑' n, ∫ x in Ioi 0, momentTerm n x := by simpa using hswap.symm
    _ = 24 * zetaFive := sum_moment_integrals

/-- Mean of `x` under the normalized frequency shape `x³/(eˣ-1)`. -/
noncomputable def shapeMean : ℝ :=
  (∫ x in Ioi (0 : ℝ), planckShape 4 x) / (∫ x in Ioi (0 : ℝ), planckShape 3 x)

theorem shapeMean_eq : shapeMean = 24 * zetaFive / (Real.pi ^ 4 / 15) := by
  unfold shapeMean
  rw [momentIntegral, boseIntegral]

theorem shapeMean_bounds : (3 : ℝ) < shapeMean ∧ shapeMean < 4 := by
  rw [shapeMean_eq]
  have hden : 0 < Real.pi ^ 4 / 15 := by positivity
  have hlow : 3 * (Real.pi ^ 4 / 15) < 24 * zetaFive := by
    have hπ : Real.pi ^ 4 < (3.15 : ℝ) ^ 4 :=
      pow_lt_pow_left₀ pi_lt_d2 Real.pi_nonneg (by decide : (4 : ℕ) ≠ 0)
    have hnum : (3.15 : ℝ) ^ 4 < 120 := by norm_num
    have h120 : Real.pi ^ 4 < 120 := hπ.trans hnum
    have hζ : Real.pi ^ 4 / 120 < zetaFive := by
      have h1 : Real.pi ^ 4 / 120 < 1 := by
        rw [div_lt_one (by norm_num : (0 : ℝ) < 120)]
        exact h120
      exact h1.trans zetaFive_gt_one
    have heq : 3 * (Real.pi ^ 4 / 15) = 24 * (Real.pi ^ 4 / 120) := by ring
    exact heq.trans_lt (mul_lt_mul_of_pos_left hζ (by norm_num))
  have hhigh : 24 * zetaFive < 4 * (Real.pi ^ 4 / 15) := by
    have heq : 4 * (Real.pi ^ 4 / 15) = 24 * (Real.pi ^ 4 / 90) := by ring
    exact (mul_lt_mul_of_pos_left zetaFive_lt_zetaFour (by norm_num)).trans_eq heq.symm
  constructor
  · rw [lt_div_iff₀ hden]
    exact hlow
  · rw [div_lt_iff₀ hden]
    exact hhigh

/-- The mean of the shape lies strictly above the frequency maximum. -/
theorem peak_lt_shapeMean : planckPeak 3 < shapeMean :=
  frequencyPeak_bounds.2.trans shapeMean_bounds.1

/-- Mean frequency of the normalized enclosure spectrum. It equals `shapeMean · T / a`. -/
noncomputable def meanFrequency (a T : ℝ) : ℝ :=
  shapeMean * T / a

private theorem frequencyDensity_shape {a T ν : ℝ} (ha : 0 < a) (hT : 0 < T) (hν : 0 < ν) :
    frequencyDensity a T ν = (T / a) ^ 3 * planckShape 3 (a * ν / T) := by
  unfold frequencyDensity planckShape
  have hden : exp (a * ν / T) - 1 ≠ 0 :=
    sub_ne_zero.mpr (one_lt_exp_iff.mpr (by positivity)).ne'
  field_simp [ha.ne', hT.ne', hν.ne', hden]

/-- The mean of `ν` under the normalized enclosure density is `shapeMean · T / a`. -/
theorem meanFrequency_eq_ratio {a T : ℝ} (ha : 0 < a) (hT : 0 < T) :
    (∫ ν in Ioi 0, ν * frequencyDensity a T ν) /
        (∫ ν in Ioi 0, frequencyDensity a T ν) =
      meanFrequency a T := by
  have hb : 0 < a / T := by positivity
  have hlink : EqOn (fun ν : ℝ => ν * frequencyDensity a T ν)
      (fun ν => (T / a) ^ 4 * planckShape 4 ((a / T) * ν)) (Ioi 0) := by
    intro ν hν
    have hν0 : 0 < ν := hν
    change ν * frequencyDensity a T ν = (T / a) ^ 4 * planckShape 4 ((a / T) * ν)
    rw [frequencyDensity_shape ha hT hν0]
    have hbν : 0 < (a / T) * ν := by positivity
    unfold planckShape
    have hde : exp ((a / T) * ν) - 1 ≠ 0 :=
      sub_ne_zero.mpr (one_lt_exp_iff.mpr hbν).ne'
    field_simp [ha.ne', hT.ne', hb.ne', hde]
  have hint : ∫ ν in Ioi 0, ν * frequencyDensity a T ν =
      (T / a) ^ 5 * ∫ x in Ioi 0, planckShape 4 x := by
    rw [setIntegral_congr_fun measurableSet_Ioi hlink, MeasureTheory.integral_const_mul,
      integral_comp_mul_left_Ioi (planckShape 4) 0 hb]
    simp only [mul_zero, smul_eq_mul]
    field_simp [ha.ne', hT.ne']
  rw [hint, frequencyDensity_integral ha hT, meanFrequency, shapeMean, boseIntegral]
  field_simp [ha.ne', hT.ne']

theorem meanFrequency_pos {a T : ℝ} (ha : 0 < a) (hT : 0 < T) : 0 < meanFrequency a T := by
  unfold meanFrequency
  exact div_pos (mul_pos (lt_trans (by norm_num) shapeMean_bounds.1) hT) ha

theorem meanFrequency_strictMono {a T1 T2 : ℝ} (ha : 0 < a) (hT : T1 < T2) :
    meanFrequency a T1 < meanFrequency a T2 := by
  unfold meanFrequency
  refine div_lt_div_of_pos_right ?_ ha
  exact mul_lt_mul_of_pos_left hT (lt_trans (by norm_num) shapeMean_bounds.1)

/-- The mean frequency lies strictly above the frequency of the maximum. -/
theorem meanFrequency_gt_peak {a T : ℝ} (ha : 0 < a) (hT : 0 < T) :
    planckPeak 3 * T / a < meanFrequency a T := by
  unfold meanFrequency
  refine div_lt_div_of_pos_right ?_ ha
  exact mul_lt_mul_of_pos_right peak_lt_shapeMean hT

end Gravity

end DstDiophantine
