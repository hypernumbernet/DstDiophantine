import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Order.IntermediateValue

/-!
# Occupation of a harmonic ladder, and the thermal spectrum of an enclosure

## Paper boundary (do **not** claim)

`h`, `k_B`, and `c` are laboratory constants. The growth of the number of
modes as the square of the frequency is the geometry of a large enclosure.
Neither is a root of `γ_s`, and neither is derived from the signed force.
The zero-point energy of the ladder is not part of the mean computed here.
No theorem identifies a restoring root of the signed force with the peak of
the enclosure.

## What is proved

* On a harmonic ladder of spacing `x > 0`, measured in units of `k_B T`, the
  Boltzmann sum is geometric. The mean number of quanta is `1/(eˣ − 1)`.
  Once `x ≥ 1` that mean is less than `2 e^{−x}`.
  The mean energy above the ground state is strictly less than `k_B T`,
  and returns to `k_B T` as `x → 0`.
* The shape `xⁿ/(eˣ − 1)` for `n ≥ 2` has a single positive maximum, at the
  unique root of `(n − x) eˣ = n` in the interval `(n − 1, n)`.
* The frequency density, proportional to `x³/(eˣ − 1)`, therefore peaks in
  `(5/2, 3)`. The wavelength density, proportional to `x⁵/(eˣ − 1)`, peaks
  in `(9/2, 5)`. The wavelength peak lies at the larger multiple of `k_B T`.
  The maximizing ratio does not depend on `T`, so the product of the peak
  wavelength and the temperature is constant.
* The equipartition density `T ν²` is strictly increasing and has no peak.
* `∫₀^∞ x³/(eˣ − 1) dx = π⁴/15`. The frequency integral of an enclosure
  whose modes grow as `ν²` therefore scales as `T⁴`, while one classical
  root scales as `T`.
-/

namespace DstDiophantine

namespace Gravity

open Real Set Filter MeasureTheory Asymptotics Topology

/-! ### Geometric occupation -/

/-- Mean number of quanta on a harmonic ladder whose spacing is `x` units of
\(k_B T\). -/
noncomputable def meanQuantum (x : ℝ) : ℝ :=
  1 / (exp x - 1)

private theorem exp_neg_abs_lt_one {x : ℝ} (hx : 0 < x) : |exp (-x)| < 1 := by
  rw [abs_of_pos (exp_pos _)]
  exact exp_lt_one_iff.mpr (neg_lt_zero.mpr hx)

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

private theorem partition_tsum {x : ℝ} (hx : 0 < x) :
    ∑' n : ℕ, exp (-(n : ℝ) * x) = 1 / (1 - exp (-x)) := by
  have hpow : ∀ n : ℕ, exp (-(n : ℝ) * x) = exp (-x) ^ n := by
    intro n
    rw [← exp_nat_mul (-x) n]
    congr 1
    simp [neg_mul]
  simp_rw [hpow]
  rw [tsum_geometric_of_abs_lt_one (exp_neg_abs_lt_one hx), ← one_div]

private theorem ladder_tsum {x : ℝ} (hx : 0 < x) :
    ∑' n : ℕ, (n : ℝ) * exp (-(n : ℝ) * x) =
      exp (-x) / (1 - exp (-x)) ^ 2 := by
  have hr : ‖exp (-x)‖ < 1 := by
    simpa [Real.norm_eq_abs] using exp_neg_abs_lt_one hx
  have hpow : ∀ n : ℕ, (n : ℝ) * exp (-(n : ℝ) * x) = (n : ℝ) * exp (-x) ^ n := by
    intro n
    rw [show exp (-(n : ℝ) * x) = exp (-x) ^ n by
      rw [← exp_nat_mul (-x) n]; congr 1; simp [neg_mul]]
  simp_rw [hpow]
  simpa using tsum_coe_mul_geometric_of_norm_lt_one (r := exp (-x)) hr

/-- The ratio of the two geometric sums is the mean occupation. -/
theorem meanQuantum_eq_ladder {x : ℝ} (hx : 0 < x) :
    (∑' n : ℕ, (n : ℝ) * exp (-(n : ℝ) * x)) /
        (∑' n : ℕ, exp (-(n : ℝ) * x)) = meanQuantum x := by
  rw [ladder_tsum hx, partition_tsum hx, meanQuantum]
  have hden : 1 - exp (-x) ≠ 0 :=
    sub_ne_zero.mpr (exp_lt_one_iff.mpr (neg_lt_zero.mpr hx)).ne'
  calc
    (exp (-x) / (1 - exp (-x)) ^ 2) / (1 / (1 - exp (-x)))
        = exp (-x) / (1 - exp (-x)) := by field_simp [hden]
    _ = 1 / (exp x - 1) := exp_neg_div_sub hx

/-- The mean energy above the ground state is strictly below equipartition. -/
theorem quantumEnergy_lt_one {x : ℝ} (hx : 0 < x) : x * meanQuantum x < 1 := by
  unfold meanQuantum
  have hden : 0 < exp x - 1 := sub_pos.mpr (one_lt_exp_iff.mpr hx)
  rw [mul_div_assoc', mul_one, div_lt_one hden]
  linarith [add_one_lt_exp hx.ne']

/-- Once the quantum is at least \(k_B T\), the mean occupation is less than
\(2 e^{-x}\). -/
theorem meanQuantum_lt_two_exp {x : ℝ} (hx : 1 ≤ x) :
    meanQuantum x < 2 * exp (-x) := by
  have hlog : log 2 < x :=
    lt_of_lt_of_le ((log_lt_iff_lt_exp (by norm_num)).mpr exp_one_gt_two) hx
  have htwo : 2 < exp x := (log_lt_iff_lt_exp (by norm_num)).mp hlog
  unfold meanQuantum
  rw [exp_neg, ← div_eq_mul_inv]
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hx
  have hpos : 0 < exp x - 1 := sub_pos.mpr (one_lt_exp_iff.mpr hx0)
  rw [div_lt_div_iff₀ hpos (exp_pos x)]
  nlinarith [htwo]

/-- As the spacing tends to zero, the mean energy returns to \(k_B T\). -/
theorem tendsto_quantumEnergy_atZero :
    Tendsto (fun x : ℝ => x * meanQuantum x) (𝓝[>] 0) (𝓝 1) := by
  have hslope : Tendsto (slope exp 0) (𝓝[>] 0) (𝓝 1) := by
    simpa [exp_zero] using
      (hasDerivAt_iff_tendsto_slope_left_right.mp (hasDerivAt_exp 0)).2
  have hinv : Tendsto (fun y : ℝ => (slope exp 0 y)⁻¹) (𝓝[>] 0) (𝓝 1) := by
    simpa [inv_one] using hslope.inv₀ one_ne_zero
  refine hinv.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with y hy
  have hy0 : y ≠ 0 := ne_of_gt hy
  have hden : exp y - 1 ≠ 0 := sub_ne_zero.mpr (one_lt_exp_iff.mpr hy).ne'
  rw [slope_def_field, exp_zero, sub_zero, meanQuantum]
  field_simp [hy0, hden]

/-- The mean occupation tends to zero for a large quantum. -/
theorem tendsto_meanQuantum_atTop : Tendsto meanQuantum atTop (𝓝 0) := by
  have hexp : Tendsto (fun x : ℝ => 2 * exp (-x)) atTop (𝓝 0) := by
    simpa [Function.comp_def] using
      (tendsto_exp_atBot.comp tendsto_neg_atTop_atBot).const_mul 2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hexp ?_ ?_
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    unfold meanQuantum
    exact (div_pos one_pos (sub_pos.mpr (one_lt_exp_iff.mpr hx))).le
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    exact (meanQuantum_lt_two_exp hx).le

/-! ### The shape and its single maximum -/

/-- Spectral shape \(x^n/(e^x-1)\). -/
noncomputable def planckShape (n : ℕ) (x : ℝ) : ℝ :=
  x ^ n / (exp x - 1)

/-- Numerator of the logarithmic derivative, \((n-x)e^x-n\). -/
private noncomputable def planckSlope (n : ℕ) (x : ℝ) : ℝ :=
  ((n : ℝ) - x) * exp x - (n : ℝ)

private theorem hasDerivAt_planckSlope (n : ℕ) (x : ℝ) :
    HasDerivAt (planckSlope n) (((n : ℝ) - 1 - x) * exp x) x := by
  unfold planckSlope
  have hlin : HasDerivAt (fun y : ℝ => (n : ℝ) - y) (-1) x :=
    (hasDerivAt_id' x).const_sub _
  refine ((hlin.fun_mul (hasDerivAt_exp x)).fun_sub
    (hasDerivAt_const x ((n : ℝ)))).congr_deriv ?_
  ring

private theorem continuous_planckSlope (n : ℕ) : Continuous (planckSlope n) := by
  unfold planckSlope
  exact ((continuous_const.sub continuous_id).mul continuous_exp).sub continuous_const

private theorem planckSlope_zero (n : ℕ) : planckSlope n 0 = 0 := by
  unfold planckSlope
  simp [exp_zero]

private theorem planckSlope_at_n (n : ℕ) : planckSlope n (n : ℝ) = -(n : ℝ) := by
  unfold planckSlope
  simp

/-- \(\exp(n-1) > n\) for every integer \(n \ge 2\). -/
private theorem exp_pred_gt (n : ℕ) (hn : 2 ≤ n) : (n : ℝ) < exp ((n : ℝ) - 1) := by
  have hne : (n : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  linarith [add_one_lt_exp hne]

private theorem planckSlope_strictMono_initial {n : ℕ} (_hn : 2 ≤ n) :
    StrictMonoOn (planckSlope n) (Icc 0 ((n : ℝ) - 1)) := by
  refine strictMonoOn_of_deriv_pos (convex_Icc 0 _) (continuous_planckSlope n).continuousOn ?_
  intro x hx
  rw [interior_Icc] at hx
  rw [(hasDerivAt_planckSlope n x).deriv]
  exact mul_pos (by linarith [hx.1, hx.2]) (exp_pos _)

private theorem planckSlope_strictAnti_tail {n : ℕ} (_hn : 2 ≤ n) :
    StrictAntiOn (planckSlope n) (Ici ((n : ℝ) - 1)) := by
  refine strictAntiOn_of_deriv_neg (convex_Ici _) (continuous_planckSlope n).continuousOn ?_
  intro x hx
  have hx' : (n : ℝ) - 1 < x := by simpa [interior_Ici] using hx
  rw [(hasDerivAt_planckSlope n x).deriv]
  exact mul_neg_of_neg_of_pos (by linarith) (exp_pos _)

private theorem planckSlope_pred_pos {n : ℕ} (hn : 2 ≤ n) :
    0 < planckSlope n ((n : ℝ) - 1) := by
  have hgt := exp_pred_gt n hn
  have : planckSlope n ((n : ℝ) - 1) = exp ((n : ℝ) - 1) - (n : ℝ) := by
    unfold planckSlope
    ring
  linarith

private theorem exists_unique_planckPeak (n : ℕ) (hn : 2 ≤ n) :
    ∃! x : ℝ, x ∈ Ioo ((n : ℝ) - 1) (n : ℝ) ∧ planckSlope n x = 0 := by
  have hab : (n : ℝ) - 1 ≤ (n : ℝ) := by linarith
  have h0 : (0 : ℝ) ∈ Ioo (planckSlope n (n : ℝ)) (planckSlope n ((n : ℝ) - 1)) :=
    ⟨by rw [planckSlope_at_n]; exact neg_neg_of_pos (by exact_mod_cast (show 0 < n by omega)),
      planckSlope_pred_pos hn⟩
  obtain ⟨x, hx, hx0⟩ :=
    (intermediate_value_Ioo' hab (continuous_planckSlope n).continuousOn) h0
  refine ⟨x, ⟨hx, hx0⟩, ?_⟩
  intro y ⟨hy, hy0⟩
  have hanti := planckSlope_strictAnti_tail hn
  have hxIci : x ∈ Ici ((n : ℝ) - 1) := mem_Ici.mpr (mem_Ioo.mp hx).1.le
  have hyIci : y ∈ Ici ((n : ℝ) - 1) := mem_Ici.mpr (mem_Ioo.mp hy).1.le
  rcases lt_trichotomy x y with hlt | heq | hgt
  · exact (lt_irrefl (0 : ℝ) (by simpa [hx0, hy0] using hanti hxIci hyIci hlt)).elim
  · exact heq.symm
  · exact (lt_irrefl (0 : ℝ) (by simpa [hy0, hx0] using hanti hyIci hxIci hgt)).elim

/-- The unique positive stationary point of \(x^n/(e^x-1)\), for \(n \ge 2\). -/
noncomputable def planckPeak (n : ℕ) : ℝ :=
  if h : 2 ≤ n then
    Classical.choose (ExistsUnique.exists (exists_unique_planckPeak n h))
  else
    0

private theorem planckPeak_spec (n : ℕ) (hn : 2 ≤ n) :
    planckPeak n ∈ Ioo ((n : ℝ) - 1) (n : ℝ) ∧ planckSlope n (planckPeak n) = 0 := by
  unfold planckPeak
  rw [dite_eq_left hn]
  exact Classical.choose_spec (ExistsUnique.exists (exists_unique_planckPeak n hn))

private theorem planckPeak_mem_Ioo (n : ℕ) (hn : 2 ≤ n) :
    planckPeak n ∈ Ioo ((n : ℝ) - 1) (n : ℝ) :=
  (planckPeak_spec n hn).1

private theorem planckSlope_pos_before {n : ℕ} (hn : 2 ≤ n) {y : ℝ}
    (hy : 0 < y) (hy' : y < planckPeak n) : 0 < planckSlope n y := by
  have hpeak := planckPeak_spec n hn
  by_cases hyI : y ≤ (n : ℝ) - 1
  · have hmono := planckSlope_strictMono_initial hn
    have hlt := hmono ⟨le_rfl, by
      have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
      linarith⟩ ⟨hy.le, hyI⟩ hy
    simpa [planckSlope_zero] using hlt
  · push Not at hyI
    have hanti := planckSlope_strictAnti_tail hn
    have hlt := hanti (mem_Ici.mpr hyI.le)
      (mem_Ici.mpr (mem_Ioo.mp hpeak.1).1.le) hy'
    simpa [hpeak.2] using hlt

private theorem planckSlope_neg_after {n : ℕ} (hn : 2 ≤ n) {y : ℝ}
    (hy : planckPeak n < y) : planckSlope n y < 0 := by
  have hpeak := planckPeak_spec n hn
  have hanti := planckSlope_strictAnti_tail hn
  have hlt := hanti (mem_Ici.mpr (mem_Ioo.mp hpeak.1).1.le)
    (mem_Ici.mpr (le_of_lt (lt_trans (mem_Ioo.mp hpeak.1).1 hy))) hy
  simpa [hpeak.2] using hlt

private theorem hasDerivAt_planckShape (n : ℕ) {x : ℝ} (hx : exp x ≠ 1) :
    HasDerivAt (planckShape n)
      (((n : ℝ) * x ^ (n - 1) * (exp x - 1) - x ^ n * exp x) / (exp x - 1) ^ 2) x := by
  unfold planckShape
  have hd : HasDerivAt (fun y : ℝ => exp y - 1) (exp x) x := by
    refine ((hasDerivAt_exp x).fun_sub (hasDerivAt_const x (1 : ℝ))).congr_deriv ?_
    simp
  exact (hasDerivAt_pow n x).fun_div hd (sub_ne_zero.mpr hx)

private theorem planckShape_deriv_slope (n : ℕ) {x : ℝ} (hn : 1 ≤ n) (hx : 0 < x) :
    deriv (planckShape n) x =
      x ^ (n - 1) * planckSlope n x / (exp x - 1) ^ 2 := by
  have hex : exp x ≠ 1 := (one_lt_exp_iff.mpr hx).ne'
  rw [(hasDerivAt_planckShape n hex).deriv]
  cases n with
  | zero => omega
  | succ n =>
    simp only [Nat.succ_sub_one, pow_succ, planckSlope]
    field_simp [hex]
    ring

private theorem continuousOn_planckShape (n : ℕ) : ContinuousOn (planckShape n) (Ioi 0) := by
  unfold planckShape
  refine ContinuousOn.div (continuous_pow n).continuousOn
    (continuous_exp.continuousOn.sub continuousOn_const) ?_
  intro x hx
  exact sub_ne_zero.mpr (one_lt_exp_iff.mpr hx).ne'

private theorem planckPeak_pos {n : ℕ} (hn : 2 ≤ n) : 0 < planckPeak n := by
  have hmem := mem_Ioo.mp (planckPeak_mem_Ioo n hn)
  have : (0 : ℝ) < (n : ℝ) - 1 := by
    have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  exact lt_trans this hmem.1

private theorem planckShape_deriv_pos {n : ℕ} (hn : 2 ≤ n) {y : ℝ}
    (hy : 0 < y) (hy' : y < planckPeak n) : 0 < deriv (planckShape n) y := by
  rw [planckShape_deriv_slope n (le_trans (by decide : 1 ≤ 2) hn) hy]
  exact div_pos (mul_pos (pow_pos hy _) (planckSlope_pos_before hn hy hy'))
    (pow_pos (sub_pos.mpr (one_lt_exp_iff.mpr hy)) _)

private theorem planckShape_deriv_neg {n : ℕ} (hn : 2 ≤ n) {y : ℝ}
    (hy : planckPeak n < y) : deriv (planckShape n) y < 0 := by
  have hy0 : 0 < y := lt_trans (planckPeak_pos hn) hy
  rw [planckShape_deriv_slope n (le_trans (by decide : 1 ≤ 2) hn) hy0]
  exact div_neg_of_neg_of_pos
    (mul_neg_of_pos_of_neg (pow_pos hy0 _) (planckSlope_neg_after hn hy))
    (pow_pos (sub_pos.mpr (one_lt_exp_iff.mpr hy0)) _)

/-- For \(n \ge 2\) the shape has a unique positive maximum, at `planckPeak n`. -/
theorem planckShape_lt_peak {n : ℕ} (hn : 2 ≤ n) {x : ℝ} (hx : 0 < x)
    (hne : x ≠ planckPeak n) :
    planckShape n x < planckShape n (planckPeak n) := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hcont : ContinuousOn (planckShape n) (Icc x (planckPeak n)) :=
      (continuousOn_planckShape n).mono fun y hy => lt_of_lt_of_le hx hy.1
    have hmono : StrictMonoOn (planckShape n) (Icc x (planckPeak n)) :=
      strictMonoOn_of_deriv_pos (convex_Icc _ _) hcont fun y hy => by
        rw [interior_Icc] at hy
        exact planckShape_deriv_pos hn (lt_trans hx hy.1) hy.2
    exact hmono ⟨le_rfl, hlt.le⟩ ⟨hlt.le, le_rfl⟩ hlt
  · have hcont : ContinuousOn (planckShape n) (Icc (planckPeak n) x) :=
      (continuousOn_planckShape n).mono fun y hy =>
        lt_of_lt_of_le (planckPeak_pos hn) hy.1
    have hanti : StrictAntiOn (planckShape n) (Icc (planckPeak n) x) :=
      strictAntiOn_of_deriv_neg (convex_Icc _ _) hcont fun y hy => by
        rw [interior_Icc] at hy
        exact planckShape_deriv_neg hn hy.1
    exact hanti ⟨le_rfl, hgt.le⟩ ⟨hgt.le, le_rfl⟩ hgt

private theorem planckShape_le_peak {n : ℕ} (hn : 2 ≤ n) {x : ℝ} (hx : 0 < x) :
    planckShape n x ≤ planckShape n (planckPeak n) := by
  rcases eq_or_ne x (planckPeak n) with rfl | hne
  · exact le_rfl
  · exact (planckShape_lt_peak hn hx hne).le

private theorem planckPeak_gt_of_slope_pos {n : ℕ} (hn : 2 ≤ n) {y : ℝ}
    (hylo : (n : ℝ) - 1 ≤ y) (hyhi : y < (n : ℝ)) (hs : 0 < planckSlope n y) :
    y < planckPeak n := by
  by_contra hle
  push Not at hle
  have hpeak := planckPeak_spec n hn
  have hanti := planckSlope_strictAnti_tail hn
  rcases lt_or_eq_of_le hle with hlt | heq
  · have := hanti (mem_Ici.mpr (mem_Ioo.mp hpeak.1).1.le) (mem_Ici.mpr hylo) hlt
    rw [hpeak.2] at this
    linarith
  · subst heq
    rw [hpeak.2] at hs
    linarith

private theorem exp_two_gt_four : (4 : ℝ) < exp 2 := by
  have h : (2 : ℝ) < exp 1 := exp_one_gt_two
  have : exp 2 = exp 1 * exp 1 := by rw [← exp_add]; norm_num
  nlinarith

private theorem exp_half_gt_three_halves : (3 / 2 : ℝ) < exp (1 / 2) := by
  linarith [add_one_lt_exp (x := (1 / 2 : ℝ)) (by norm_num)]

private theorem exp_four_gt_sixteen : (16 : ℝ) < exp 4 := by
  have h := exp_two_gt_four
  have : exp 4 = exp 2 * exp 2 := by rw [← exp_add]; norm_num
  nlinarith

/-- The frequency shape \(x^3/(e^x-1)\) peaks strictly between \(5/2\) and \(3\). -/
theorem frequencyPeak_bounds : (5 / 2 : ℝ) < planckPeak 3 ∧ planckPeak 3 < 3 := by
  have hmem := planckPeak_mem_Ioo 3 (by norm_num)
  refine ⟨planckPeak_gt_of_slope_pos (by norm_num) (by norm_num) (by norm_num) ?_,
    (mem_Ioo.mp hmem).2⟩
  have hprod : (6 : ℝ) < exp (5 / 2) := by
    have h1 : (4 : ℝ) * (3 / 2) < exp 2 * (3 / 2) :=
      mul_lt_mul_of_pos_right exp_two_gt_four (by norm_num)
    have h2 : exp 2 * (3 / 2) < exp 2 * exp (1 / 2) :=
      mul_lt_mul_of_pos_left exp_half_gt_three_halves (exp_pos _)
    have : exp (5 / 2) = exp 2 * exp (1 / 2) := by rw [← exp_add]; norm_num
    linarith
  have hs : planckSlope 3 (5 / 2) = (1 / 2) * exp (5 / 2) - 3 := by
    unfold planckSlope
    ring
  linarith

/-- The wavelength shape \(x^5/(e^x-1)\) peaks strictly between \(9/2\) and \(5\). -/
theorem wavelengthPeak_bounds : (9 / 2 : ℝ) < planckPeak 5 ∧ planckPeak 5 < 5 := by
  have hmem := planckPeak_mem_Ioo 5 (by norm_num)
  refine ⟨planckPeak_gt_of_slope_pos (by norm_num) (by norm_num) (by norm_num) ?_,
    (mem_Ioo.mp hmem).2⟩
  have hprod : (24 : ℝ) < exp (9 / 2) := by
    have h1 : (16 : ℝ) * (3 / 2) < exp 4 * (3 / 2) :=
      mul_lt_mul_of_pos_right exp_four_gt_sixteen (by norm_num)
    have h2 : exp 4 * (3 / 2) < exp 4 * exp (1 / 2) :=
      mul_lt_mul_of_pos_left exp_half_gt_three_halves (exp_pos _)
    have : exp (9 / 2) = exp 4 * exp (1 / 2) := by rw [← exp_add]; norm_num
    linarith
  have hs : planckSlope 5 (9 / 2) = (1 / 2) * exp (9 / 2) - 5 := by
    unfold planckSlope
    ring
  linarith

/-! ### Enclosure densities -/

/-- Equipartition density of modes that grow as \(\nu^2\), each carrying \(T\). -/
noncomputable def rayleighJeans (T ν : ℝ) : ℝ :=
  T * ν ^ 2

/-- The classical density has no maximum: every frequency is dimmer than a higher one. -/
theorem rayleighJeans_no_maximum {T ν : ℝ} (hT : 0 < T) (hν : 0 < ν) :
    ∃ ν', ν < ν' ∧ rayleighJeans T ν < rayleighJeans T ν' := by
  refine ⟨ν + 1, by linarith, ?_⟩
  unfold rayleighJeans
  nlinarith [sq_nonneg ν, hT]

/-- Frequency density \(\nu^3/(e^{a\nu/T}-1)\), with \(a = h/k_B\). -/
noncomputable def frequencyDensity (a T ν : ℝ) : ℝ :=
  ν ^ 3 / (exp (a * ν / T) - 1)

private theorem frequencyDensity_eq_shape {a T ν : ℝ} (ha : 0 < a) (hT : 0 < T) (hν : 0 < ν) :
    frequencyDensity a T ν = (T / a) ^ 3 * planckShape 3 (a * ν / T) := by
  unfold frequencyDensity planckShape
  have hden : exp (a * ν / T) - 1 ≠ 0 :=
    sub_ne_zero.mpr (one_lt_exp_iff.mpr (by positivity)).ne'
  field_simp [ha.ne', hT.ne', hν.ne', hden]

/-- Wavelength density. The factor \(b\) is \(hc/k_B\). -/
noncomputable def wavelengthDensity (b T lam : ℝ) : ℝ :=
  1 / (lam ^ 5 * (exp (b / (lam * T)) - 1))

private theorem wavelengthDensity_eq_shape {b T lam : ℝ}
    (hb : 0 < b) (hT : 0 < T) (hlam : 0 < lam) :
    wavelengthDensity b T lam = (T / b) ^ 5 * planckShape 5 (b / (lam * T)) := by
  unfold wavelengthDensity planckShape
  have hx : 0 < b / (lam * T) := by positivity
  have hden : exp (b / (lam * T)) - 1 ≠ 0 :=
    sub_ne_zero.mpr (one_lt_exp_iff.mpr hx).ne'
  field_simp [hb.ne', hT.ne', hlam.ne', hden]

/-- Wien's displacement: the maximizing wavelength times \(T\) does not depend on \(T\). -/
theorem wien_product {b T : ℝ} (hT : T ≠ 0) :
    (b / (planckPeak 5 * T)) * T = b / planckPeak 5 := by
  have hp : planckPeak 5 ≠ 0 :=
    (lt_trans (by norm_num : (0 : ℝ) < 9 / 2) wavelengthPeak_bounds.1).ne'
  field_simp [hT, hp]

theorem wavelengthDensity_le {b T lam : ℝ} (hb : 0 < b) (hT : 0 < T) (hlam : 0 < lam) :
    wavelengthDensity b T lam ≤ wavelengthDensity b T (b / (planckPeak 5 * T)) := by
  have hp : 0 < planckPeak 5 :=
    lt_trans (by norm_num : (0 : ℝ) < 9 / 2) wavelengthPeak_bounds.1
  have hlamp : 0 < b / (planckPeak 5 * T) := by positivity
  rw [wavelengthDensity_eq_shape hb hT hlam, wavelengthDensity_eq_shape hb hT hlamp]
  have harg : b / ((b / (planckPeak 5 * T)) * T) = planckPeak 5 := by
    rw [wien_product hT.ne']
    field_simp [hb.ne', hp.ne']
  rw [harg]
  exact mul_le_mul_of_nonneg_left
    (planckShape_le_peak (by norm_num) (by positivity : 0 < b / (lam * T)))
    (by positivity)

theorem frequencyDensity_le {a T ν : ℝ} (ha : 0 < a) (hT : 0 < T) (hν : 0 < ν) :
    frequencyDensity a T ν ≤ frequencyDensity a T (planckPeak 3 * T / a) := by
  have hp : 0 < planckPeak 3 :=
    lt_trans (by norm_num : (0 : ℝ) < 5 / 2) frequencyPeak_bounds.1
  have hνp : 0 < planckPeak 3 * T / a := by positivity
  rw [frequencyDensity_eq_shape ha hT hν, frequencyDensity_eq_shape ha hT hνp]
  have harg : a * (planckPeak 3 * T / a) / T = planckPeak 3 := by
    field_simp [ha.ne', hT.ne', hp.ne']
  rw [harg]
  exact mul_le_mul_of_nonneg_left
    (planckShape_le_peak (by norm_num) (by positivity : 0 < a * ν / T))
    (by positivity)

/-! ### The Bose integral and the fourth power of temperature -/

private theorem tendsto_pow_three_exp_half {m : ℝ} (hm : 0 < m) :
    Tendsto (fun x : ℝ => x ^ 3 * exp (-(m / 2) * x)) atTop (𝓝 0) := by
  have hz : Tendsto (fun x : ℝ => (m / 2) * x) atTop atTop :=
    Tendsto.const_mul_atTop (by positivity : 0 < m / 2) tendsto_id
  have hscaled := (tendsto_pow_mul_exp_neg_atTop_nhds_zero 3).comp hz |>.const_mul ((2 / m) ^ 3)
  rw [mul_zero] at hscaled
  refine hscaled.congr fun x => ?_
  have hm0 : m ≠ 0 := hm.ne'
  have hmul : (2 / m) * ((m / 2) * x) = x := by
    field_simp
  have hexp : -((m / 2) * x) = -(m / 2) * x := by ring
  calc
    (2 / m) ^ 3 * (((m / 2) * x) ^ 3 * exp (-((m / 2) * x)))
        = ((2 / m) ^ 3 * ((m / 2) * x) ^ 3) * exp (-((m / 2) * x)) := by
          ring
    _ = ((2 / m) * ((m / 2) * x)) ^ 3 * exp (-((m / 2) * x)) := by
          rw [← mul_pow]
    _ = x ^ 3 * exp (-(m / 2) * x) := by
          rw [hmul, hexp]

private theorem integrableOn_pow_three_exp {m : ℝ} (hm : 0 < m) :
    IntegrableOn (fun x : ℝ => x ^ 3 * exp (-m * x)) (Ioi 0) := by
  refine integrable_of_isBigO_exp_neg (b := m / 2) (by positivity) (by fun_prop) ?_
  · rw [isBigO_iff]
    refine ⟨1, ?_⟩
    have hsmall :=
      (tendsto_pow_three_exp_half hm).eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
    filter_upwards [hsmall, eventually_ge_atTop (0 : ℝ)] with x hx hx0
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    have hsplit : x ^ 3 * exp (-m * x) =
        (x ^ 3 * exp (-(m / 2) * x)) * exp (-(m / 2) * x) := by
      have harg : -m * x = -(m / 2) * x + -(m / 2) * x := by ring
      rw [harg, exp_add, ← mul_assoc]
    have hnonneg : 0 ≤ x ^ 3 * exp (-m * x) := by positivity
    rw [hsplit, abs_mul]
    have hpre : 0 ≤ x ^ 3 * exp (-(m / 2) * x) := by positivity
    rw [abs_of_nonneg hpre, abs_of_pos (exp_pos _)]
    exact mul_le_mul_of_nonneg_right (le_of_lt hx) (exp_pos _).le

private theorem integral_pow_three_exp {m : ℝ} (hm : 0 < m) :
    ∫ x in Ioi (0 : ℝ), x ^ 3 * exp (-m * x) = 6 / m ^ 4 := by
  have hkey := integral_rpow_mul_exp_neg_mul_Ioi (a := 4) (r := m) (by norm_num) hm
  have hagree : EqOn (fun x : ℝ => x ^ ((4 : ℝ) - 1) * exp (-(m * x)))
      (fun x => x ^ 3 * exp (-m * x)) (Ioi 0) := by
    intro x _
    change x ^ ((4 : ℝ) - 1) * exp (-(m * x)) = x ^ 3 * exp (-m * x)
    rw [show (4 : ℝ) - 1 = ((3 : ℕ) : ℝ) by norm_num, rpow_natCast x 3]
    have harg : -(m * x) = -m * x := by ring
    rw [harg]
  have hsame : ∫ x in Ioi (0 : ℝ), x ^ 3 * exp (-m * x) =
      ∫ x in Ioi (0 : ℝ), x ^ ((4 : ℝ) - 1) * exp (-(m * x)) :=
    (setIntegral_congr_fun (μ := volume) measurableSet_Ioi hagree).symm
  have hΓ : Gamma 4 = 6 := by
    simp [Nat.factorial]
  rw [hsame, hkey, hΓ]
  conv_lhs =>
    arg 1
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num]
    rw [rpow_natCast (1 / m) 4]
  rw [div_pow, one_pow, div_mul_eq_mul_div, one_mul]

private noncomputable def boseTerm (n : ℕ) (x : ℝ) : ℝ :=
  x ^ 3 * exp (-((n + 1 : ℕ) : ℝ) * x)

private theorem boseTerm_eq_pow {x : ℝ} (n : ℕ) :
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

private theorem boseTerm_tsum {x : ℝ} (hx : 0 < x) :
    ∑' n : ℕ, boseTerm n x = planckShape 3 x := by
  unfold boseTerm planckShape
  simp_rw [boseTerm_eq_pow]
  have hr0 : 0 ≤ exp (-x) := (exp_pos _).le
  have hr1 : exp (-x) < 1 := exp_lt_one_iff.mpr (neg_lt_zero.mpr hx)
  rw [tsum_mul_left, geom_shift hr0 hr1, exp_neg_div_sub hx, mul_div_assoc', mul_one]

private theorem integral_boseTerm (n : ℕ) :
    ∫ x in Ioi (0 : ℝ), boseTerm n x = 6 / ((n + 1 : ℕ) : ℝ) ^ 4 := by
  simpa [boseTerm] using integral_pow_three_exp (m := ((n + 1 : ℕ) : ℝ)) (by positivity)

private theorem boseTerm_integral_norm (n : ℕ) :
    ∫ x in Ioi (0 : ℝ), ‖boseTerm n x‖ = 6 / ((n + 1 : ℕ) : ℝ) ^ 4 := by
  have hnn : ∀ x ∈ Ioi (0 : ℝ), 0 ≤ boseTerm n x := by
    intro x hx
    unfold boseTerm
    exact mul_nonneg (pow_nonneg hx.le 3) (exp_pos _).le
  rw [setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_]
  · exact integral_boseTerm n
  · rw [Real.norm_eq_abs, abs_of_nonneg (hnn x hx)]

private theorem sum_bose_integrals :
    ∑' n : ℕ, ∫ x in Ioi (0 : ℝ), boseTerm n x = Real.pi ^ 4 / 15 := by
  simp_rw [integral_boseTerm]
  have hzeta : ∑' n : ℕ, (1 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 4 = Real.pi ^ 4 / 90 := by
    have hz := hasSum_zeta_four.tsum_eq
    rw [(hasSum_zeta_four.summable).tsum_eq_zero_add] at hz
    simpa using hz
  calc
    ∑' n : ℕ, (6 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 4
        = 6 * ∑' n : ℕ, (1 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 4 := by
          rw [← tsum_mul_left]
          congr
          ext n
          ring
    _ = Real.pi ^ 4 / 15 := by
          rw [hzeta]
          ring

/-- \(\int_0^\infty x^3/(e^x-1)\,dx = \pi^4/15\). -/
theorem boseIntegral : ∫ x in Ioi (0 : ℝ), planckShape 3 x = Real.pi ^ 4 / 15 := by
  have hint : ∀ n : ℕ, Integrable (boseTerm n) (volume.restrict (Ioi (0 : ℝ))) := by
    intro n
    refine Integrable.congr
      (integrableOn_pow_three_exp (m := ((n + 1 : ℕ) : ℝ)) (by positivity)).integrable ?_
    filter_upwards with x
    unfold boseTerm
    congr 1
  have hsum : Summable fun n => ∫ x, ‖boseTerm n x‖ ∂(volume.restrict (Ioi (0 : ℝ))) := by
    have hnorm : ∀ n, ∫ x in Ioi (0 : ℝ), ‖boseTerm n x‖ =
        6 / ((n + 1 : ℕ) : ℝ) ^ 4 := boseTerm_integral_norm
    simp_rw [hnorm]
    have hzeta : Summable fun n : ℕ => (1 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 4 :=
      (hasSum_zeta_four.summable).comp_injective Nat.succ_injective
    have hmul : (fun n : ℕ => (6 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 4) =
        fun n => 6 * ((1 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 4) := by
      funext n
      ring
    rw [hmul]
    exact hzeta.mul_left 6
  have hswap := integral_tsum_of_summable_integral_norm hint hsum
  have hseries : EqOn (fun x => ∑' n, boseTerm n x) (planckShape 3) (Ioi 0) :=
    fun x hx => boseTerm_tsum hx
  calc
    ∫ x in Ioi 0, planckShape 3 x
        = ∫ x in Ioi 0, ∑' n, boseTerm n x := by
          exact setIntegral_congr_fun measurableSet_Ioi
            fun _ hx => (hseries hx).symm
    _ = ∑' n, ∫ x in Ioi 0, boseTerm n x := by
          simpa using hswap.symm
    _ = Real.pi ^ 4 / 15 := sum_bose_integrals

/-- The integrated frequency density of the enclosure scales as \(T^4\). -/
theorem frequencyDensity_integral {a T : ℝ} (ha : 0 < a) (hT : 0 < T) :
    ∫ ν in Ioi 0, frequencyDensity a T ν =
      (T / a) ^ 4 * (Real.pi ^ 4 / 15) := by
  have hc : 0 < a / T := by positivity
  have hpt : EqOn (frequencyDensity a T)
      (fun ν => (T / a) ^ 3 * planckShape 3 ((a / T) * ν)) (Ioi 0) := by
    intro ν hν
    rw [frequencyDensity_eq_shape ha hT hν]
    congr 1
    field_simp
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul,
    integral_comp_mul_left_Ioi (planckShape 3) 0 hc, smul_eq_mul]
  simp only [mul_zero]
  rw [boseIntegral]
  field_simp

end Gravity

end DstDiophantine
