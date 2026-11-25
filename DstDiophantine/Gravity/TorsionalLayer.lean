import DstDiophantine.Gravity.ElectronShell
import DstDiophantine.Algebra.Invariant
import DstDiophantine.Algebra.MismatchAngle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Closed-form structure of the equal-scale torsional layers

The length `ℓ` and the identification of the layered phase with the strong force are not derived. No
theorem asserts `dst_derives_lambda`, `dst_derives_alpha_s`, or `dst_derives_Amax`.
-/

namespace DstDiophantine

namespace Gravity

open Real Set Operations Invariant

/-! ### Equal-scale interference factor -/

/-- Legacy mixed overlap (`axisOverlapLegacy` balanced chart). -/
noncomputable def gammaSEqualLegacy (x : ℝ) : ℝ :=
  cosh x * cos x - sinh x * sin x

/-- Primary equal-scale overlap: grade-0 scalar `cosh x · cos x` (`x = ℓ/(2r)`). -/
noncomputable def gammaSEqual (x : ℝ) : ℝ :=
  cosh x * cos x

theorem gammaSEqual_eq_overlap_primary (x : ℝ) :
    gammaSEqual x = MismatchAngle.axisOverlapScalar (2 * x) (2 * x) := by
  unfold gammaSEqual MismatchAngle.axisOverlapScalar
  congr 1 <;> ring_nf

theorem gammaSEqualLegacy_eq_gammaS (x : ℝ) : gammaSEqualLegacy x = gammaS (2 * x) (2 * x) := by
  unfold gammaSEqualLegacy gammaS
  rw [show (2 * x) / 2 = x by ring]

theorem gammaSEqual_eq_gammaS (x : ℝ) : gammaSEqualLegacy x = gammaS (2 * x) (2 * x) :=
  gammaSEqualLegacy_eq_gammaS x

theorem gammaSEqual_zero : gammaSEqual 0 = 1 := by
  simp [gammaSEqual]

theorem continuous_gammaSEqual : Continuous gammaSEqual := by
  unfold gammaSEqual
  exact continuous_cosh.mul continuous_cos

/-! ### The exact derivative -/

theorem hasDerivAt_gammaSEqual (x : ℝ) :
    HasDerivAt gammaSEqual (sinh x * cos x - cosh x * sin x) x := by
  have h1 : HasDerivAt (fun y : ℝ => cosh y * cos y)
      (sinh x * cos x + cosh x * (-sin x)) x :=
    (Real.hasDerivAt_cosh x).mul (Real.hasDerivAt_cos x)
  unfold gammaSEqual
  convert h1 using 3 <;> ring

theorem deriv_gammaSEqual (x : ℝ) :
    deriv gammaSEqual x = sinh x * cos x - cosh x * sin x :=
  (hasDerivAt_gammaSEqual x).deriv

theorem gammaSEqual_eq_zero_iff (x : ℝ) : gammaSEqual x = 0 ↔ cos x = 0 := by
  unfold gammaSEqual
  constructor
  · intro h
    rcases mul_eq_zero.mp h with hcosh | hcos
    · exact absurd hcosh (cosh_pos x).ne'
    · exact hcos
  · intro h
    simp [h]

theorem gammaSEqual_eq_zero_iff_cos {x : ℝ} (hx : 0 < x) :
    gammaSEqual x = 0 ↔ cos x = 0 :=
  gammaSEqual_eq_zero_iff x

theorem resonanceRoot1_le_pi_div_two : resonanceRoot1 ≤ π / 2 := by
  rw [resonanceRoot1_eq_pi_div_two]

theorem deriv_gammaSEqual_eq_zero_iff (x : ℝ) :
    deriv gammaSEqual x = 0 ↔ sinh x * cos x = cosh x * sin x := by
  simp [deriv_gammaSEqual, sub_eq_zero]

private theorem tanh_lt_tan_of_mem_Ioo_quarter_half {x : ℝ} (hx : π / 4 < x) (hlt : x < π / 2) :
    tanh x < tan x := by
  have hx0 : 0 < x := lt_trans (by linarith [pi_pos]) hx
  have htan : 1 < tan x := by
    have hmem₁ : x ∈ Ioo (-(π / 2)) (π / 2) := ⟨by linarith [pi_pos], hlt⟩
    have hmem₂ : (π / 4) ∈ Ioo (-(π / 2)) (π / 2) :=
      ⟨by linarith [pi_pos], by linarith [pi_pos]⟩
    have hstep := strictMonoOn_tan hmem₂ hmem₁ hx
    rwa [tan_pi_div_four] at hstep
  have htanh : tanh x < 1 := tanh_lt_one x
  linarith

theorem deriv_gammaSEqual_ne_zero_of_mem_Ioo_quarter_half {x : ℝ}
    (hx : π / 4 < x) (hlt : x < π / 2) : deriv gammaSEqual x ≠ 0 := by
  intro h
  have hc : cos x ≠ 0 := (cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], hlt⟩).ne'
  have hmul : sinh x * cos x = cosh x * sin x := (deriv_gammaSEqual_eq_zero_iff x).1 h
  have htan : tan x = tanh x := by
    rw [tan_eq_sin_div_cos, tanh_eq_sinh_div_cosh]
    field_simp [hc, (cosh_pos x).ne']
    linarith [hmul.symm]
  exact (tanh_lt_tan_of_mem_Ioo_quarter_half hx hlt).ne' htan

alias gammaSEqual_deriv_ne_zero_of_mem_Ioo_pi :=
  deriv_gammaSEqual_ne_zero_of_mem_Ioo_quarter_half

/-! ### Legacy mixed-chart derivative -/

theorem hasDerivAt_gammaSEqualLegacy (x : ℝ) :
    HasDerivAt gammaSEqualLegacy (-2 * cosh x * sin x) x := by
  have h1 : HasDerivAt (fun y : ℝ => cosh y * cos y)
      (sinh x * cos x + cosh x * (-sin x)) x :=
    (Real.hasDerivAt_cosh x).mul (Real.hasDerivAt_cos x)
  have h2 : HasDerivAt (fun y : ℝ => sinh y * sin y)
      (cosh x * sin x + sinh x * cos x) x :=
    (Real.hasDerivAt_sinh x).mul (Real.hasDerivAt_sin x)
  have h3 := h1.sub h2
  have heq : (-2 * cosh x * sin x) =
      (sinh x * cos x + cosh x * (-sin x)) - (cosh x * sin x + sinh x * cos x) := by
    ring
  unfold gammaSEqualLegacy
  rw [heq]
  exact h3

theorem deriv_gammaSEqualLegacy (x : ℝ) :
    deriv gammaSEqualLegacy x = -2 * cosh x * sin x :=
  (hasDerivAt_gammaSEqualLegacy x).deriv

theorem continuous_gammaSEqualLegacy : Continuous gammaSEqualLegacy := by
  unfold gammaSEqualLegacy
  exact continuous_cosh.mul continuous_cos |>.sub (continuous_sinh.mul continuous_sin)

theorem deriv_gammaSEqualLegacy_eq_zero_iff (x : ℝ) :
    deriv gammaSEqualLegacy x = 0 ↔ sin x = 0 := by
  rw [deriv_gammaSEqualLegacy]
  have hc : cosh x ≠ 0 := (cosh_pos x).ne'
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h | h
    · rcases mul_eq_zero.mp h with h | h
      · norm_num at h
      · exact absurd h hc
    · exact h
  · intro h
    rw [h]
    ring

/-! ### Exact extremal values -/

private theorem neg_one_pow_mul_self (n : ℕ) : ((-1 : ℝ) ^ n) * ((-1 : ℝ) ^ n) = 1 := by
  rw [← pow_add, ← two_mul, pow_mul]
  norm_num

theorem gammaSEqual_nat_mul_pi (n : ℕ) :
    gammaSEqual ((n : ℝ) * π) = (-1) ^ n * cosh ((n : ℝ) * π) := by
  unfold gammaSEqual
  rw [cos_nat_mul_pi]
  ring

theorem abs_gammaSEqual_nat_mul_pi (n : ℕ) :
    |gammaSEqual ((n : ℝ) * π)| = cosh ((n : ℝ) * π) := by
  rw [gammaSEqual_nat_mul_pi, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_pos (cosh_pos _)]

theorem gammaSEqual_nat_mul_pi_ne_zero (n : ℕ) :
    gammaSEqual ((n : ℝ) * π) ≠ 0 := by
  intro h
  have := abs_gammaSEqual_nat_mul_pi n
  rw [h, abs_zero] at this
  exact absurd this.symm (cosh_pos _).ne'

/-! ### The plateau clock is not the force denominator -/

theorem gammaEff_equalScale_plateau (n : ℕ) :
    gammaEff (2 * ((n : ℝ) * π)) (2 * ((n : ℝ) * π)) =
      cosh (2 * ((n : ℝ) * π)) := by
  refine gammaEff_balanced_eq_cosh_of_sin_eq_zero ?_
  have harg : 2 * ((n : ℝ) * π) = ((2 * n : ℕ) : ℝ) * π := by
    push_cast
    ring
  rw [harg, sin_nat_mul_pi]

/-- The force denominator is not `γ_eff`. -/
theorem plateau_clock_gt_force_amplitude (n : ℕ) (hn : 0 < n) :
    |gammaSEqual ((n : ℝ) * π)| <
      gammaEff (2 * ((n : ℝ) * π)) (2 * ((n : ℝ) * π)) := by
  rw [abs_gammaSEqual_nat_mul_pi, gammaEff_equalScale_plateau]
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hlt : (n : ℝ) * π < 2 * ((n : ℝ) * π) := by nlinarith [pi_pos]
  refine cosh_lt_cosh.mpr ?_
  rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) * π),
    abs_of_pos (by positivity : (0 : ℝ) < 2 * ((n : ℝ) * π))]
  exact hlt

/-- The signed plateau value that divides the force is not the clock. -/
theorem plateau_gammaS_ne_gammaEff (n : ℕ) (hn : 0 < n) :
    gammaSEqual ((n : ℝ) * π) ≠
      gammaEff (2 * ((n : ℝ) * π)) (2 * ((n : ℝ) * π)) := by
  intro heq
  have hlt := plateau_clock_gt_force_amplitude n hn
  rw [heq, abs_of_pos (gammaEff_pos _ _)] at hlt
  exact lt_irrefl _ hlt

private theorem even_two_mul (k : ℕ) : Even (2 * k) :=
  even_iff_two_dvd.mpr ⟨k, rfl⟩

/-! ### Sign of `sin` on a branch -/

private theorem sin_nat_mul_pi_add (n : ℕ) (t : ℝ) :
    sin ((n : ℝ) * π + t) = (-1) ^ n * sin t := by
  rw [sin_add, sin_nat_mul_pi, cos_nat_mul_pi]
  ring

private theorem cos_nat_mul_pi_add (n : ℕ) (t : ℝ) :
    cos ((n : ℝ) * π + t) = (-1) ^ n * cos t := by
  rw [cos_add, cos_nat_mul_pi, sin_nat_mul_pi]
  ring

theorem signed_sin_pos_on_branch (n : ℕ) {x : ℝ}
    (hx : x ∈ Ioo ((n : ℝ) * π) ((n : ℝ) * π + π)) :
    0 < (-1 : ℝ) ^ n * sin x := by
  obtain ⟨h1, h2⟩ := hx
  have hxt : x = (n : ℝ) * π + (x - (n : ℝ) * π) := by ring
  have ht0 : 0 < x - (n : ℝ) * π := by linarith
  have htπ : x - (n : ℝ) * π < π := by linarith
  have hsin : 0 < sin (x - (n : ℝ) * π) := sin_pos_of_pos_of_lt_pi ht0 htπ
  rw [hxt, sin_nat_mul_pi_add, ← mul_assoc, neg_one_pow_mul_self, one_mul]
  exact hsin

/-! ### Strict monotonicity on each branch -/

/-- Sign-corrected interference factor: strictly decreasing on the `n`-th `π`-interval for every
`n`. -/
noncomputable def gammaSSigned (n : ℕ) (x : ℝ) : ℝ := (-1 : ℝ) ^ n * gammaSEqual x

theorem gammaSSigned_eq_zero_iff (n : ℕ) (x : ℝ) :
    gammaSSigned n x = 0 ↔ gammaSEqual x = 0 := by
  unfold gammaSSigned
  have hne : ((-1 : ℝ) ^ n) ≠ 0 := by positivity
  simp [mul_eq_zero, hne]

theorem hasDerivAt_gammaSSigned (n : ℕ) (x : ℝ) :
    HasDerivAt (gammaSSigned n) ((-1 : ℝ) ^ n * (sinh x * cos x - cosh x * sin x)) x :=
  (hasDerivAt_gammaSEqual x).const_mul _

theorem deriv_gammaSSigned (n : ℕ) (x : ℝ) :
    deriv (gammaSSigned n) x = (-1 : ℝ) ^ n * (sinh x * cos x - cosh x * sin x) :=
  (hasDerivAt_gammaSSigned n x).deriv

theorem continuous_gammaSSigned (n : ℕ) : Continuous (gammaSSigned n) := by
  unfold gammaSSigned
  exact continuous_const.mul continuous_gammaSEqual

/-! ### Legacy signed branches (mixed-chart monotonicity) -/

noncomputable def gammaSSignedLegacy (n : ℕ) (x : ℝ) : ℝ :=
  (-1 : ℝ) ^ n * gammaSEqualLegacy x

theorem hasDerivAt_gammaSSignedLegacy (n : ℕ) (x : ℝ) :
    HasDerivAt (gammaSSignedLegacy n) ((-1 : ℝ) ^ n * (-2 * cosh x * sin x)) x :=
  (hasDerivAt_gammaSEqualLegacy x).const_mul _

theorem deriv_gammaSSignedLegacy (n : ℕ) (x : ℝ) :
    deriv (gammaSSignedLegacy n) x = (-1 : ℝ) ^ n * (-2 * cosh x * sin x) :=
  (hasDerivAt_gammaSSignedLegacy n x).deriv

theorem continuous_gammaSSignedLegacy (n : ℕ) : Continuous (gammaSSignedLegacy n) := by
  unfold gammaSSignedLegacy
  exact continuous_const.mul continuous_gammaSEqualLegacy

private theorem sinh_cos_sub_lt {t : ℝ} (ht0 : 0 < t) (htπ : t < π) :
    sinh t * cos t < cosh t * sin t := by
  rcases lt_trichotomy t (π / 2) with h | h | h
  · exact sinh_mul_cos_lt_cosh_mul_sin ⟨ht0, h⟩
  · subst h
    simp [cos_pi_div_two, sin_pi_div_two]
    nlinarith [cosh_pos (π / 2), sinh_pos_iff.mpr ht0]
  · have hsin := sin_pos_of_pos_of_lt_pi ht0 htπ
    have hcos := cos_neg_of_pi_div_two_lt_of_lt h (lt_of_lt_of_le htπ (by linarith [pi_pos]))
    nlinarith [cosh_pos t, sinh_pos_iff.mpr ht0, hsin, hcos]

theorem strictAntiOn_gammaSSignedLegacy (n : ℕ) :
    StrictAntiOn (gammaSSignedLegacy n) (Icc ((n : ℝ) * π) ((n : ℝ) * π + π)) := by
  refine strictAntiOn_of_deriv_neg (convex_Icc _ _)
    (continuous_gammaSSignedLegacy n).continuousOn ?_
  intro x hx
  rw [interior_Icc] at hx
  have hs := signed_sin_pos_on_branch n hx
  have hc := cosh_pos x
  have hrw : ((-1 : ℝ) ^ n) * (-2 * cosh x * sin x)
      = -2 * cosh x * ((-1 : ℝ) ^ n * sin x) := by ring
  rw [deriv_gammaSSignedLegacy, hrw]
  nlinarith [hs, hc]

theorem legacy_strictAntiOn_gammaSEqual_even (k : ℕ) :
    StrictAntiOn gammaSEqualLegacy
      (Icc (((2 * k : ℕ) : ℝ) * π) (((2 * k : ℕ) : ℝ) * π + π)) := by
  have h := strictAntiOn_gammaSSignedLegacy (2 * k)
  intro a ha b hb hab
  have hlt := h ha hb hab
  unfold gammaSSignedLegacy at hlt
  rw [pow_mul] at hlt
  norm_num at hlt
  exact hlt

theorem legacy_strictMonoOn_gammaSEqual_odd (k : ℕ) :
    StrictMonoOn gammaSEqualLegacy
      (Icc (((2 * k + 1 : ℕ) : ℝ) * π) (((2 * k + 1 : ℕ) : ℝ) * π + π)) := by
  have h := strictAntiOn_gammaSSignedLegacy (2 * k + 1)
  intro a ha b hb hab
  have hlt := h ha hb hab
  unfold gammaSSignedLegacy at hlt
  rw [show (-1 : ℝ) ^ (2 * k + 1) = -1 by simp [pow_succ]] at hlt
  linarith

/-! ### Primary first-even-branch strict decrease -/

theorem strictAntiOn_gammaSSigned_zero :
    StrictAntiOn (gammaSSigned 0) (Icc (0 : ℝ) π) := by
  refine strictAntiOn_of_deriv_neg (convex_Icc _ _)
    (continuous_gammaSSigned 0).continuousOn ?_
  intro x hx
  simp only [interior_Icc] at hx
  simp only [deriv_gammaSSigned, deriv_gammaSEqual, pow_zero, one_mul]
  linarith [sinh_cos_sub_lt hx.1 hx.2]

theorem strictAntiOn_gammaSEqual_even (k : ℕ) (hk : k = 0 := by decide) :
    StrictAntiOn gammaSEqual
      (Icc (((2 * k : ℕ) : ℝ) * π) (((2 * k : ℕ) : ℝ) * π + π)) := by
  subst hk
  intro a ha b hb hab
  have ha' : a ∈ Icc (0 : ℝ) π := by simpa [Nat.cast_zero, zero_mul, zero_add] using ha
  have hb' : b ∈ Icc (0 : ℝ) π := by simpa [Nat.cast_zero, zero_mul, zero_add] using hb
  have hlt := strictAntiOn_gammaSSigned_zero ha' hb' hab
  simpa [gammaSSigned, pow_zero, one_mul, gammaSEqual] using hlt

theorem strictAntiOn_gammaSSigned (n : ℕ) (hn : n = 0 := by decide) :
    StrictAntiOn (gammaSSigned n) (Icc ((n : ℝ) * π) ((n : ℝ) * π + π)) := by
  subst hn
  simpa [gammaSSigned, pow_zero] using strictAntiOn_gammaSSigned_zero

private theorem sin_neg_of_signed_sin_pos_branch {n : ℕ} {x : ℝ}
    (hs : 0 < (-1 : ℝ) ^ n * sin x) (hn : Odd n) : sin x < 0 := by
  obtain ⟨k, rfl⟩ := hn
  have hpow : (-1 : ℝ) ^ (2 * k + 1) = -1 := by
    simp [pow_add, pow_mul, neg_one_sq]
  rw [hpow, neg_mul] at hs
  simpa using hs

private theorem eleven_lt_cosh_pi_aux : (11 : ℝ) < cosh π := by
  have he1 : (2.7182818283 : ℝ) < exp 1 := exp_one_gt_d9
  have he1pos : (0 : ℝ) < exp 1 := exp_pos 1
  have hexp3 : exp 1 * exp 1 * exp 1 = exp 3 := by rw [← exp_add, ← exp_add]; norm_num
  have h3 : (20 : ℝ) < exp 3 := by rw [← hexp3]; nlinarith [he1, he1pos]
  have hπ : (3.14 : ℝ) < π := pi_gt_d2
  have h2 : (1.14 : ℝ) < exp (π - 3) := by linarith [Real.add_one_le_exp (π - 3)]
  have hsplit : exp π = exp 3 * exp (π - 3) := by rw [← exp_add]; ring_nf
  have hexpπ : (22 : ℝ) < exp π := by rw [hsplit]; nlinarith [h3, h2, exp_pos (3 : ℝ), exp_pos (π - 3)]
  rw [cosh_eq]
  nlinarith [hexpπ, exp_pos (-π)]

private theorem cosh_pi_gt_ten : (10 : ℝ) < cosh π :=
  lt_trans (by norm_num : (10 : ℝ) < 11) eleven_lt_cosh_pi_aux

private lemma cosh_sub_sinh_eq_exp_neg (x : ℝ) : cosh x - sinh x = exp (-x) := by
  rw [cosh_eq, sinh_eq]; field_simp [exp_ne_zero]; ring

private lemma sinh_le_of_exp_le_local {x E : ℝ} (hE : exp x ≤ E) :
    sinh x ≤ (E - 1 / E) / 2 := by
  rw [sinh_eq]
  have hinv : 1 / E ≤ exp (-x) := by
    simpa [exp_neg] using one_div_le_one_div_of_le (exp_pos x) hE
  linarith [exp_pos x, exp_pos (-x)]

private lemma sinh_pi_gt_ten_point_nine : (109 / 10 : ℝ) < sinh π := by
  have hsq : (120 : ℝ) < sinh π ^ 2 :=
    by nlinarith [eleven_lt_cosh_pi_aux, cosh_sq_sub_sinh_sq π]
  nlinarith [sinh_pos_iff.mpr pi_pos, hsq, show (109 / 10) ^ 2 < (120 : ℝ) from by norm_num]

private lemma exp_between_torsional {x lo hi : ℝ} {n : ℕ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hn : 0 < n)
    (hlo : lo < (∑ m ∈ Finset.range n, x ^ m / m.factorial) -
      x ^ n * (n.succ / (n.factorial * n)))
    (hhi : (∑ m ∈ Finset.range n, x ^ m / m.factorial) +
      x ^ n * (n.succ / (n.factorial * n)) < hi) :
    lo < exp x ∧ exp x < hi := by
  have hx : |x| ≤ 1 := by rwa [abs_of_nonneg hx0]
  have h := Real.exp_bound hx hn
  rw [abs_of_nonneg hx0, abs_sub_le_iff] at h
  obtain ⟨hup, hdn⟩ := h
  constructor <;> linarith

private lemma exp_half_bounds_torsional :
    (164 / 100 : ℝ) < exp (1 / 2) ∧ exp (1 / 2) < 165 / 100 := by
  refine exp_between_torsional (x := 1 / 2) (n := 8) (by norm_num) (by norm_num) (by decide) ?_ ?_
  · norm_num [Finset.sum_range_succ, Nat.factorial]
  · norm_num [Finset.sum_range_succ, Nat.factorial]

private lemma exp_pi_lt_twenty_four : exp π < (24 : ℝ) := by
  have hsplit : exp π = exp 3 * exp (π - 3) := by rw [← exp_add]; ring_nf
  have hexp3 : exp 3 = exp 1 ^ 3 := by rw [← exp_nat_mul]; norm_num
  have h3 : exp 3 < (201 / 10 : ℝ) := by
    rw [hexp3]
    refine lt_trans (pow_lt_pow_left₀ Real.exp_one_lt_d9 (le_of_lt (exp_pos 1)) ?_) (by norm_num)
    decide
  have hπdiff : π - 3 < (15 / 100 : ℝ) := by linarith [pi_lt_d2]
  have hsmall : exp ((15 : ℝ) / 100) < (118 / 100 : ℝ) :=
    (exp_between_torsional (x := (15 : ℝ) / 100) (lo := 1) (hi := 118 / 100) (n := 8)
      (by norm_num) (by norm_num) (by decide)
      (by norm_num [Finset.sum_range_succ, Nat.factorial])
      (by norm_num [Finset.sum_range_succ, Nat.factorial])).2
  rw [hsplit]
  have hδ : exp (π - 3) < exp (15 / 100) := exp_strictMono hπdiff
  nlinarith [hδ, h3, hsmall, exp_pos 3]

private lemma cosh_pi_lt_fifteen : cosh π < (15 : ℝ) := by
  rw [cosh_eq]
  have hneg : exp (-π) < 1 := (exp_lt_one_iff).2 (by linarith [pi_pos])
  linarith [exp_pi_lt_twenty_four, hneg, exp_pos π]

private noncomputable def coshCosSubSinhSin (t : ℝ) : ℝ :=
  cosh t * cos t - sinh t * sin t

private theorem coshCosSubSinhSin_zero : coshCosSubSinhSin 0 = 1 := by
  simp [coshCosSubSinhSin]

private theorem coshCosSubSinhSin_two_fifths_min :
    (1219 / 6144 : ℝ) < coshCosSubSinhSin (2 / 5) := by
  dsimp [coshCosSubSinhSin]
  have htw : (2 : ℝ) / 5 < 1 / 2 := by norm_num
  have hcos : cos (1 / 2 : ℝ) < cos (2 / 5) :=
    cos_lt_cos_of_nonneg_of_le_pi_div_two (by positivity) (by nlinarith [pi_gt_three]) htw
  have hsin : sin (2 / 5) < sin (1 / 2 : ℝ) := by
    have ha : (2 / 5 : ℝ) ∈ Icc (-(π / 2)) (π / 2) := ⟨by nlinarith [pi_gt_three], by nlinarith [pi_gt_three]⟩
    have hb : (1 / 2 : ℝ) ∈ Icc (-(π / 2)) (π / 2) := ⟨by nlinarith [pi_gt_three], by nlinarith [pi_gt_three]⟩
    exact strictMonoOn_sin ha hb htw
  have hsinh : sinh (2 / 5) < sinh (1 / 2 : ℝ) := sinh_lt_sinh.mpr htw
  have hcosh : (1 : ℝ) < cosh (2 / 5) :=
    (one_lt_cosh.mpr (ne_of_gt (by norm_num : 0 < (2 : ℝ) / 5)))
  have hcos_lo : (1339 / 1536 : ℝ) ≤ cos (1 / 2) := by
    have hb := cos_bound (x := (1 / 2 : ℝ)) (by norm_num)
    obtain ⟨hlo, _⟩ := abs_sub_le_iff.mp hb
    have hpoly : (1 : ℝ) - (1 / 2) ^ 2 / 2 = 7 / 8 := by norm_num
    have herr : ((1 / 2 : ℝ) ^ 4) * (5 / 96) = 5 / 1536 := by norm_num
    have hsum : (7 / 8 : ℝ) - 5 / 1536 = 1339 / 1536 := by norm_num
    nlinarith [hlo, hpoly, herr, hsum]
  have hsin_hi : sin (1 / 2 : ℝ) < (11 / 20 : ℝ) := by
    obtain ⟨_, hup⟩ := abs_sub_le_iff.mp (sin_bound (x := (1 / 2 : ℝ)) (by norm_num))
    have hpoly : (1 / 2 : ℝ) - (1 / 2) ^ 3 / 6 = 23 / 48 := by norm_num
    have herr : ((1 / 2 : ℝ) ^ 5) / 100 = 1 / 3200 := by norm_num
    nlinarith [hup, hpoly, herr]
  have hsinh_hi : sinh (1 / 2 : ℝ) < (11 / 20 : ℝ) := by
    rcases exp_half_bounds_torsional with ⟨_, hu⟩
    have hle := sinh_le_of_exp_le_local hu.le
    have hub :
        sinh (1 / 2) ≤ (165 / 100 - 100 / 165) / 2 := by
      simpa [div_eq_mul_inv] using hle
    linarith [hub, show (165 / 100 - 100 / 165) / 2 < (11 / 20 : ℝ) from by norm_num]
  have hcos₂ : (1339 / 1536 : ℝ) < cos (2 / 5) := lt_of_le_of_lt hcos_lo hcos
  have hlhs : (1339 / 1536 : ℝ) < cosh (2 / 5) * cos (2 / 5) := by nlinarith [hcosh, hcos₂]
  have hrhs : sinh (2 / 5) * sin (2 / 5) < (121 / 400 : ℝ) := by
    have hsinh' : sinh (2 / 5) < 11 / 20 := lt_trans hsinh hsinh_hi
    have hsin' : sin (2 / 5) < 11 / 20 := lt_trans hsin hsin_hi
    have hsinpos : 0 < sin (2 / 5) := sin_pos_of_pos_of_lt_pi (by norm_num) (by nlinarith [pi_gt_three])
    have hsinhpos : 0 < sinh (2 / 5) := sinh_pos_iff.mpr (by norm_num)
    calc sinh (2 / 5) * sin (2 / 5)
        < (11 / 20 : ℝ) * (11 / 20) :=
          mul_lt_mul_of_pos hsinh' hsin' hsinhpos (by norm_num : 0 < (11 / 20 : ℝ))
      _ = 121 / 400 := by ring
  have hsep : (121 / 400 : ℝ) < 1339 / 1536 := by norm_num
  linarith [hlhs, hrhs, hsep]

private theorem coshCosSubSinhSin_two_fifths_pos :
    0 < coshCosSubSinhSin (2 / 5) :=
  lt_trans (by norm_num : (0 : ℝ) < 1219 / 6144) coshCosSubSinhSin_two_fifths_min

private noncomputable def coshSinSubSinhCos (t : ℝ) : ℝ :=
  cosh t * sin t - sinh t * cos t

private theorem hasDerivAt_coshSinSubSinhCos (t : ℝ) :
    HasDerivAt coshSinSubSinhCos (2 * sinh t * sin t) t := by
  unfold coshSinSubSinhCos
  have h1 := (Real.hasDerivAt_cosh t).mul (Real.hasDerivAt_sin t)
  have h2 := (Real.hasDerivAt_sinh t).mul (Real.hasDerivAt_cos t)
  convert HasDerivAt.sub h1 h2 using 1 <;> ring

private theorem deriv_coshSinSubSinhCos (t : ℝ) :
    deriv coshSinSubSinhCos t = 2 * sinh t * sin t :=
  (hasDerivAt_coshSinSubSinhCos t).deriv

private theorem continuousOn_coshSinSubSinhCos :
    ContinuousOn coshSinSubSinhCos (Icc (0 : ℝ) (2 / 5)) :=
  ContinuousOn.mono (((continuous_cosh.mul continuous_sin).sub
    (continuous_sinh.mul continuous_cos)).continuousOn) (by intro x _; exact mem_univ x)

private theorem strictMonoOn_coshSinSubSinhCos_zero_two_fifths :
    StrictMonoOn coshSinSubSinhCos (Icc (0 : ℝ) (2 / 5)) := by
  refine strictMonoOn_of_deriv_pos (convex_Icc _ _) continuousOn_coshSinSubSinhCos ?_
  intro t ht
  simp only [interior_Icc] at ht
  rw [deriv_coshSinSubSinhCos]
  have hsin : 0 < sin t :=
    sin_pos_of_pos_of_lt_pi (by linarith [ht.1]) (by nlinarith [ht.2, pi_gt_three])
  nlinarith [sinh_pos_iff.mpr ht.1, hsin]

private lemma exp_two_fifths_bounds_local :
    (149 / 100 : ℝ) < exp (2 / 5) ∧ exp (2 / 5) < 3 / 2 := by
  refine exp_between_torsional (x := 2 / 5) (n := 8) (by norm_num) (by norm_num) (by decide) ?_ ?_
  · norm_num [Finset.sum_range_succ, Nat.factorial]
  · norm_num [Finset.sum_range_succ, Nat.factorial]

private theorem coshSinSubSinhCos_two_fifths_lt_twelfth :
    coshSinSubSinhCos (2 / 5) < (1 / 12 : ℝ) := by
  dsimp [coshSinSubSinhCos]
  rcases exp_two_fifths_bounds_local with ⟨hexpL, hexpU⟩
  have hinv : exp (-(2 / 5)) < (100 / 149 : ℝ) := by
    rw [exp_neg]
    simpa [one_div] using
      one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 149 / 100) hexpL
  have hcosh : cosh (2 / 5) < (11 / 10 : ℝ) := by
    rw [cosh_eq]
    nlinarith [hexpU, hinv, exp_pos (2 / 5),
      show (3 / 2 + 100 / 149) / 2 < (11 / 10 : ℝ) from by norm_num]
  have hsinh : sinh (2 / 5) < (42 / 100 : ℝ) := by
    have hle := sinh_le_of_exp_le_local hexpU.le
    rw [sinh_eq] at hle ⊢
    linarith [hle, show ((3 / 2 - 2 / 3) / 2 : ℝ) = 5 / 12 from by ring,
      show (5 / 12 : ℝ) < 42 / 100 from by norm_num]
  obtain ⟨_, hcoslo⟩ := abs_sub_le_iff.mp (cos_bound (x := (2 / 5 : ℝ)) (by norm_num))
  obtain ⟨hsinup, _⟩ := abs_sub_le_iff.mp (sin_bound (x := (2 / 5 : ℝ)) (by norm_num))
  rw [abs_of_nonneg (show (0 : ℝ) ≤ 2 / 5 by norm_num)] at hcoslo hsinup
  have hcos : (689 / 750 : ℝ) ≤ cos (2 / 5) := by
    have hpoly : (1 : ℝ) - (2 / 5) ^ 2 / 2 = 23 / 25 := by norm_num
    have herr : ((2 / 5 : ℝ) ^ 4) * (5 / 96) = 1 / 750 := by norm_num
    have hsum : (23 / 25 : ℝ) - 1 / 750 = 689 / 750 := by norm_num
    nlinarith [hcoslo, hpoly, herr, hsum]
  have hsin : sin (2 / 5) < (2 / 5 : ℝ) := sin_lt (by norm_num : (0 : ℝ) < 2 / 5)
  have hsinhlo : (149 / 100 - 100 / 149) / 2 < sinh (2 / 5) := by
    rw [sinh_eq]
    nlinarith [hexpL, hinv, exp_pos (2 / 5)]
  have hsinpos : 0 < sin (2 / 5) := sin_pos_of_pos_of_lt_pi (by norm_num) (by nlinarith [pi_gt_three])
  have hcoshpos : 0 < cosh (2 / 5) := cosh_pos _
  have hprodup : cosh (2 / 5) * sin (2 / 5) < (11 / 10) * (2 / 5) :=
    mul_lt_mul_of_pos hcosh hsin hcoshpos (by norm_num : 0 < (2 / 5 : ℝ))
  nlinarith [hprodup, hsinhlo, hcos, hsinpos,
    show (11 / 10 : ℝ) * (2 / 5) - (149 / 100 - 100 / 149) / 2 * (689 / 750) < (1 / 12 : ℝ) from
      by norm_num]

private theorem cosh_sin_sub_sinh_cos_lt_twelfth_of_lt_two_fifths {t : ℝ}
    (ht0 : 0 < t) (ht : t < 2 / 5) :
    coshSinSubSinhCos t < (1 / 12 : ℝ) := by
  have htIcc : t ∈ Icc (0 : ℝ) (2 / 5) := ⟨le_of_lt ht0, le_of_lt ht⟩
  have h₂f : (2 / 5 : ℝ) ∈ Icc (0 : ℝ) (2 / 5) := ⟨by norm_num, by norm_num⟩
  have hmono := strictMonoOn_coshSinSubSinhCos_zero_two_fifths htIcc h₂f ht
  exact lt_trans hmono coshSinSubSinhCos_two_fifths_lt_twelfth

private theorem hasDerivAt_coshCosSubSinhSin (t : ℝ) :
    HasDerivAt coshCosSubSinhSin (-2 * cosh t * sin t) t := by
  have h1 : HasDerivAt (fun y : ℝ => cosh y * cos y) (sinh t * cos t - cosh t * sin t) t := by
    convert hasDerivAt_gammaSEqual t using 2 <;> simp [gammaSEqual]
  have h2 := (Real.hasDerivAt_sinh t).mul (Real.hasDerivAt_sin t)
  unfold coshCosSubSinhSin
  convert HasDerivAt.sub h1 h2 using 1 <;> ring

private theorem deriv_coshCosSubSinhSin (t : ℝ) :
    deriv coshCosSubSinhSin t = -2 * cosh t * sin t :=
  (hasDerivAt_coshCosSubSinhSin t).deriv

private theorem continuousOn_coshCosSubSinhSin :
    ContinuousOn coshCosSubSinhSin (Icc (0 : ℝ) (2 / 5)) :=
  ContinuousOn.mono (((continuous_cosh.mul continuous_cos).sub
    (continuous_sinh.mul continuous_sin)).continuousOn) (by intro x _; exact mem_univ x)

private theorem strictAntiOn_coshCosSubSinhSin_zero_two_fifths :
    StrictAntiOn coshCosSubSinhSin (Icc (0 : ℝ) (2 / 5)) := by
  refine strictAntiOn_of_deriv_neg (convex_Icc _ _)
    continuousOn_coshCosSubSinhSin ?_
  intro t ht
  simp only [interior_Icc] at ht
  rw [deriv_coshCosSubSinhSin]
  have hsin : 0 < sin t :=
    sin_pos_of_pos_of_lt_pi (by linarith [ht.1]) (by nlinarith [ht.2, pi_gt_three])
  nlinarith [cosh_pos t, hsin]

private theorem cosh_mul_cos_gt_sinh_mul_sin_of_lt_two_fifths {t : ℝ}
    (ht0 : 0 < t) (ht : t < 2 / 5) :
    sinh t * sin t < cosh t * cos t := by
  have htIcc : t ∈ Icc (0 : ℝ) (2 / 5) := ⟨le_of_lt ht0, le_of_lt ht⟩
  have h₂f : (2 / 5 : ℝ) ∈ Icc (0 : ℝ) (2 / 5) := ⟨by norm_num, by norm_num⟩
  have hgt := strictAntiOn_coshCosSubSinhSin_zero_two_fifths htIcc h₂f ht
  have hbase := coshCosSubSinhSin_two_fifths_pos
  have hpos : 0 < coshCosSubSinhSin t := lt_trans hbase hgt
  simpa [coshCosSubSinhSin] using sub_pos.mp hpos

private theorem sinh_pi_shift_mul_cos_lt_cosh_mul_sin_of_lt_two_fifths {t : ℝ}
    (ht0 : 0 < t) (ht : t < 2 / 5) :
    sinh (π + t) * cos (π + t) < cosh (π + t) * sin (π + t) := by
  have hcosx : cos (π + t) = -cos t := by
    rw [cos_add]; simp [cos_pi, sin_pi]
  have hsinx : sin (π + t) = -sin t := by
    rw [sin_add]; simp [cos_pi, sin_pi]
  have hsinhx : sinh (π + t) = sinh π * cosh t + cosh π * sinh t := by rw [sinh_add]
  have hcoshx : cosh (π + t) = cosh π * cosh t + sinh π * sinh t := by rw [cosh_add]
  have hpart1 := cosh_mul_cos_gt_sinh_mul_sin_of_lt_two_fifths ht0 ht
  have htioo : t ∈ Ioo (0 : ℝ) (π / 2) :=
    ⟨ht0, by nlinarith [ht, pi_gt_three]⟩
  have hpart2 := sinh_mul_cos_lt_cosh_mul_sin htioo
  have hshπ : 0 < sinh π := sinh_pos_iff.mpr pi_pos
  have hchπ : 0 < cosh π := cosh_pos π
  have hcomb : 0 <
      sinh π * (cosh t * cos t - sinh t * sin t) +
        cosh π * (sinh t * cos t - cosh t * sin t) := by
    have h₁ : 0 < cosh t * cos t - sinh t * sin t := sub_pos.mpr hpart1
    have h₂ : sinh t * cos t - cosh t * sin t < 0 := sub_neg.mpr hpart2
    have htIcc : t ∈ Icc (0 : ℝ) (2 / 5) := ⟨le_of_lt ht0, le_of_lt ht⟩
    have h₂f : (2 / 5 : ℝ) ∈ Icc (0 : ℝ) (2 / 5) := ⟨by norm_num, by norm_num⟩
    have hδlo : coshCosSubSinhSin (2 / 5) < coshCosSubSinhSin t :=
      strictAntiOn_coshCosSubSinhSin_zero_two_fifths htIcc h₂f ht
    have hδhi : cosh t * sin t - sinh t * cos t < (1 / 12 : ℝ) :=
      cosh_sin_sub_sinh_cos_lt_twelfth_of_lt_two_fifths ht0 ht
    have hδ1 : (1219 / 6144 : ℝ) < cosh t * cos t - sinh t * sin t :=
      lt_trans coshCosSubSinhSin_two_fifths_min (by simpa [coshCosSubSinhSin] using hδlo)
    nlinarith [hδ1, hδhi, sinh_pi_gt_ten_point_nine, cosh_pi_lt_fifteen, h₂, hchπ]
  suffices h : sinh (π + t) * cos (π + t) < cosh (π + t) * sin (π + t) by exact h
  have hΔ : sinh (π + t) * cos (π + t) = -(sinh π * cosh t + cosh π * sinh t) * cos t := by
    rw [hsinhx, hcosx]; ring
  have hΔ' : cosh (π + t) * sin (π + t) = -(cosh π * cosh t + sinh π * sinh t) * sin t := by
    rw [hcoshx, hsinx]; ring
  rw [hΔ, hΔ']
  nlinarith [hcomb]

private theorem sinh_cos_lt_cosh_sin_before_odd_node_zero {x : ℝ}
    (hx1 : π < x) (hx2 : x < π + (2 / 5 : ℝ)) :
    sinh x * cos x < cosh x * sin x := by
  set t := x - π with htdef
  have ht0 : 0 < t := by linarith [hx1, htdef]
  have ht : t < 2 / 5 := by linarith [hx2, htdef]
  simpa [htdef, add_assoc] using
    sinh_pi_shift_mul_cos_lt_cosh_mul_sin_of_lt_two_fifths ht0 ht

/-- Odd-branch monotonicity on the legacy mixed chart (balanced overlap; see `docs/mismatch-angle.md`). -/
theorem strictMonoOn_gammaSEqualLegacy_odd (k : ℕ) :
    StrictMonoOn gammaSEqualLegacy
      (Icc (((2 * k + 1 : ℕ) : ℝ) * π) (((2 * k + 1 : ℕ) : ℝ) * π + π)) :=
  legacy_strictMonoOn_gammaSEqual_odd k

/-! ### Exactly one node per `π`-interval -/

private theorem gammaSSigned_left (n : ℕ) :
    gammaSSigned n ((n : ℝ) * π) = cosh ((n : ℝ) * π) := by
  unfold gammaSSigned
  rw [gammaSEqual_nat_mul_pi, ← mul_assoc, neg_one_pow_mul_self, one_mul]

private theorem gammaSSigned_right (n : ℕ) :
    gammaSSigned n ((n : ℝ) * π + π) = -cosh (((n : ℝ) + 1) * π) := by
  have hcast : ((n : ℝ) + 1) * π = ((n + 1 : ℕ) : ℝ) * π := by push_cast; ring
  have harg : (n : ℝ) * π + π = ((n + 1 : ℕ) : ℝ) * π := by push_cast; ring
  unfold gammaSSigned
  rw [harg, gammaSEqual_nat_mul_pi, hcast, ← mul_assoc, pow_succ]
  rw [show ((-1 : ℝ) ^ n * ((-1 : ℝ) ^ n * (-1))) = -(((-1 : ℝ) ^ n) * ((-1 : ℝ) ^ n)) by ring,
    neg_one_pow_mul_self]
  ring

noncomputable def branchNode (n : ℕ) : ℝ :=
  π / 2 + (n : ℝ) * π

theorem branchNode_gammaSEqual_zero (n : ℕ) : gammaSEqual (branchNode n) = 0 := by
  unfold branchNode gammaSEqual
  simp [cos_add, cos_nat_mul_pi, sin_nat_mul_pi, cos_pi_div_two, mul_zero]

theorem branchNode_mem_branch (n : ℕ) :
    branchNode n ∈ Ioo ((n : ℝ) * π) ((n : ℝ) * π + π) := by
  unfold branchNode
  constructor <;> nlinarith [pi_pos, pi_gt_d2]

theorem branchNode_eq_of_gamma_zero (n : ℕ) {y : ℝ}
    (hy : y ∈ Ioo ((n : ℝ) * π) ((n : ℝ) * π + π)) (h0 : gammaSEqual y = 0) :
    y = branchNode n := by
  have hc := (gammaSEqual_eq_zero_iff y).1 h0
  unfold branchNode
  set t := y - (n : ℝ) * π with ht
  have ht0 : 0 < t := by simp [ht]; linarith [hy.1]
  have htπ : t < π := by simp [ht]; linarith [hy.2]
  have hxt : y = (n : ℝ) * π + t := by linarith [ht]
  rw [hxt, cos_add, cos_nat_mul_pi, sin_nat_mul_pi] at hc
  have hc' : cos t = 0 := by
    rw [zero_mul, sub_zero] at hc
    exact (mul_eq_zero.mp hc).resolve_left (pow_ne_zero _ (by norm_num : (-1 : ℝ) ≠ 0))
  have ht₂ : t = π / 2 :=
    (injOn_cos.eq_iff ⟨le_of_lt ht0, le_of_lt htπ⟩ ⟨by linarith [pi_pos], by linarith [pi_pos]⟩).mp
      (hc'.trans cos_pi_div_two.symm)
  linarith [hxt, ht₂]

private theorem cos_eq_zero_iff_eq_pi_div_two_add_nat_mul {x : ℝ} {n : ℕ}
    (hx : x ∈ Ioo ((n : ℝ) * π) ((n : ℝ) * π + π)) :
    cos x = 0 ↔ x = branchNode n := by
  unfold branchNode
  constructor
  · intro hc
    have h0 : gammaSEqual x = 0 := (gammaSEqual_eq_zero_iff x).mpr hc
    exact branchNode_eq_of_gamma_zero n hx h0
  · intro hEq
    simpa [hEq, branchNode, cos_add, cos_nat_mul_pi, sin_nat_mul_pi, cos_pi_div_two]

theorem exists_unique_node_branch (n : ℕ) :
    ∃! x : ℝ, x ∈ Ioo ((n : ℝ) * π) ((n : ℝ) * π + π) ∧ gammaSEqual x = 0 := by
  refine ⟨branchNode n, ⟨branchNode_mem_branch n, branchNode_gammaSEqual_zero n⟩, ?_⟩
  rintro y ⟨hy, hy0⟩
  exact (cos_eq_zero_iff_eq_pi_div_two_add_nat_mul hy).mp ((gammaSEqual_eq_zero_iff y).1 hy0)

theorem gammaSEqual_pos_before_branchNode (n : ℕ) (hn : Even n) {x : ℝ}
    (hxlo : (n : ℝ) * π ≤ x) (hxhi : x < branchNode n) : 0 < gammaSEqual x := by
  obtain ⟨k, rfl⟩ := hn
  unfold branchNode at hxhi
  set t := x - (2 * (k : ℕ) : ℝ) * π with htdef
  have ht2 : t < π / 2 := by simp [htdef] at hxhi ⊢; linarith [hxhi]
  have htnn : 0 ≤ t := by simp [htdef] at hxlo ⊢; linarith [hxlo]
  have hx' : x = (2 * (k : ℕ) : ℝ) * π + t := by linarith [htdef]
  rw [hx', gammaSEqual]
  have harg : 2 * (k : ℝ) * π + t = ((2 * k : ℕ) : ℝ) * π + t := by push_cast; ring
  rw [harg, cos_nat_mul_pi_add (2 * k) t]
  rw [show (-1 : ℝ) ^ (2 * k) = 1 from by simp [Nat.two_mul, pow_mul, neg_one_pow_two], one_mul]
  by_cases ht0 : t = 0
  · rw [ht0]; simp [cos_zero]; exact cosh_pos _
  · have htpos : 0 < t := lt_of_le_of_ne htnn (Ne.symm ht0)
    exact mul_pos (cosh_pos _) (cos_pos_of_mem_Ioo ⟨by linarith [htpos, pi_div_two_pos], ht2⟩)

theorem gammaSEqual_neg_after_branchNode (n : ℕ) (hn : Even n) {x : ℝ}
    (hxlo : branchNode n < x) (hxhi : x < (n : ℝ) * π + π) : gammaSEqual x < 0 := by
  obtain ⟨k, rfl⟩ := hn
  set t := x - (2 * (k : ℕ) : ℝ) * π with htdef
  have ht1 : π / 2 < t := by simp [htdef, branchNode] at hxlo ⊢; linarith [hxlo]
  have htπ : t < π := by simp [htdef] at hxhi ⊢; linarith [hxhi]
  have hx' : x = (2 * (k : ℕ) : ℝ) * π + t := by linarith [htdef]
  rw [hx', gammaSEqual]
  have harg : 2 * (k : ℝ) * π + t = ((2 * k : ℕ) : ℝ) * π + t := by push_cast; ring
  rw [harg, cos_nat_mul_pi_add (2 * k) t]
  rw [show (-1 : ℝ) ^ (2 * k) = 1 from by simp [Nat.two_mul, pow_mul, neg_one_pow_two], one_mul]
  have hcos : cos t < 0 :=
    Real.cos_neg_of_pi_div_two_lt_of_lt ht1 (lt_of_lt_of_le htπ (by linarith [Real.pi_pos]))
  exact mul_neg_of_pos_of_neg (cosh_pos _) hcos

theorem gammaSEqual_neg_before_branchNode (n : ℕ) (hn : Odd n) {x : ℝ}
    (hxlo : (n : ℝ) * π ≤ x) (hxhi : x < branchNode n) : gammaSEqual x < 0 := by
  obtain ⟨k, rfl⟩ := hn
  unfold branchNode at hxhi
  set t := x - ((2 * k + 1 : ℕ) : ℝ) * π with htdef
  have ht2 : t < π / 2 := by simp [htdef] at hxhi ⊢; linarith [hxhi]
  have ht0 : 0 ≤ t := by simp [htdef] at hxlo ⊢; linarith [hxlo]
  have hx' : x = ((2 * k + 1 : ℕ) : ℝ) * π + t := by linarith [htdef]
  rw [gammaSEqual, hx', cos_nat_mul_pi_add (2 * k + 1) t]
  have hpow : (-1 : ℝ) ^ (2 * k + 1) = -1 := by simp [pow_succ, pow_mul, neg_one_sq]
  simp only [hpow, neg_mul]
  by_cases ht : t = 0
  · rw [ht, cos_zero]
    simpa using mul_neg_of_pos_of_neg (cosh_pos _) (by norm_num : (-1 : ℝ) < 0)
  · have htpos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm ht)
    have hcos : 0 < cos t :=
      cos_pos_of_mem_Ioo ⟨by linarith [htpos, pi_div_two_pos], ht2⟩
    simpa [mul_assoc] using
      mul_neg_of_pos_of_neg (cosh_pos _) (neg_neg_of_pos hcos)

theorem gammaSEqual_pos_after_branchNode (n : ℕ) (hn : Odd n) {x : ℝ}
    (hxlo : branchNode n < x) (hxhi : x ≤ (n : ℝ) * π + π) : 0 < gammaSEqual x := by
  obtain ⟨k, rfl⟩ := hn
  unfold branchNode at hxlo
  set t := x - ((2 * k + 1 : ℕ) : ℝ) * π with htdef
  have ht1 : π / 2 < t := by simp [htdef, branchNode] at hxlo ⊢; linarith [hxlo]
  have htπ : t ≤ π := by simp [htdef] at hxhi ⊢; linarith [hxhi]
  have hx' : x = ((2 * k + 1 : ℕ) : ℝ) * π + t := by linarith [htdef]
  rw [gammaSEqual, hx', cos_nat_mul_pi_add (2 * k + 1) t]
  have hpow : (-1 : ℝ) ^ (2 * k + 1) = -1 := by simp [pow_succ, pow_mul, neg_one_sq]
  simp only [hpow, neg_mul]
  rcases le_iff_eq_or_lt.mp htπ with htp | htlt
  · rw [htp, cos_pi]
    simpa [mul_neg, neg_neg] using cosh_pos _
  · have hcos : cos t < 0 :=
      cos_neg_of_pi_div_two_lt_of_lt ht1 (lt_trans htlt (by linarith [pi_pos]))
    have hpos : 0 < -cos t := neg_pos.mpr hcos
    simpa [mul_assoc, neg_mul] using mul_pos (cosh_pos _) hpos

theorem gammaSEqual_neg_on_odd_left (k : ℕ) {x : ℝ}
    (hxlo : ((2 * k + 1 : ℕ) : ℝ) * π ≤ x)
    (hxhi : x < branchNode (2 * k + 1)) :
    gammaSEqual x < 0 :=
  gammaSEqual_neg_before_branchNode (2 * k + 1) ⟨k, rfl⟩ hxlo hxhi

theorem gammaSEqual_pos_on_odd_right (k : ℕ) {x : ℝ}
    (hxlo : branchNode (2 * k + 1) < x)
    (hxhi : x ≤ ((2 * k + 1 : ℕ) : ℝ) * π + π) :
    0 < gammaSEqual x :=
  gammaSEqual_pos_after_branchNode (2 * k + 1) ⟨k, rfl⟩ hxlo hxhi

theorem gammaSEqual_pos_on_even_left (k : ℕ) {x : ℝ}
    (hxlo : ((2 * k : ℕ) : ℝ) * π ≤ x)
    (hxhi : x < branchNode (2 * k)) :
    0 < gammaSEqual x :=
  gammaSEqual_pos_before_branchNode (2 * k) ⟨k, by simp [two_mul]⟩ hxlo hxhi

/-- Primary `cosh·cos` is strictly decreasing on `Icc π (π + 2/5)`
    (certified band where `γ' < 0` on the first odd branch). -/
theorem strictAntiOn_gammaSEqual_odd_branch (k : ℕ) (hk : k = 0 := by decide) :
    StrictAntiOn gammaSEqual (Icc π (π + (2 / 5 : ℝ))) := by
  subst hk
  refine strictAntiOn_of_deriv_neg (convex_Icc _ _)
    continuous_gammaSEqual.continuousOn ?_
  intro x hx
  simp only [interior_Icc] at hx
  obtain ⟨hx1, hx2⟩ := hx
  have hlt := sinh_cos_lt_cosh_sin_before_odd_node_zero (by simpa using hx1) hx2
  rw [deriv_gammaSEqual]
  linarith [hlt]

theorem node_is_simple_zero {x : ℝ} (hx : 0 < x) (h : gammaSEqual x = 0) :
    deriv gammaSEqual x ≠ 0 := by
  intro hderiv
  have hc : cos x = 0 := (gammaSEqual_eq_zero_iff x).1 h
  have hs : sin x ≠ 0 := by
    intro hs
    have := sin_sq_add_cos_sq x
    rw [hc, hs] at this
    norm_num at this
  have hcosh : cosh x * sin x ≠ 0 := mul_ne_zero (cosh_pos _).ne' hs
  have : deriv gammaSEqual x = -cosh x * sin x := by
    rw [deriv_gammaSEqual, hc]
    simp only [mul_zero, zero_mul]
    ring
  rw [this] at hderiv
  have hmul : cosh x * sin x = 0 := by linarith [hderiv]
  rcases mul_eq_zero.mp hmul with hc0 | hs0
  · exact absurd hc0 (cosh_pos x).ne'
  · exact hs hs0

/-! ### Legacy mixed-chart nodes (`tanh·tan = 1`, sharp `(π/4,π/2)` window) -/

theorem cos_ne_zero_of_gammaSEqualLegacy_eq_zero {x : ℝ} (hx : 0 < x)
    (h : gammaSEqualLegacy x = 0) : cos x ≠ 0 := by
  intro hc
  have hs : 0 < sinh x := sinh_pos_iff.mpr hx
  have hsin : sin x = 0 := by
    unfold gammaSEqualLegacy at h
    rw [hc, mul_zero, zero_sub, neg_eq_zero] at h
    rcases mul_eq_zero.mp h with h1 | h1
    · exact absurd h1 hs.ne'
    · exact h1
  have hpyth := sin_sq_add_cos_sq x
  rw [hsin, hc] at hpyth
  norm_num at hpyth

theorem tan_eq_of_gammaSEqualLegacy_eq_zero {x : ℝ} (hx : 0 < x)
    (h : gammaSEqualLegacy x = 0) : tan x = cosh x / sinh x := by
  have hs : 0 < sinh x := sinh_pos_iff.mpr hx
  have hc : cos x ≠ 0 := cos_ne_zero_of_gammaSEqualLegacy_eq_zero hx h
  have hbal : cosh x * cos x = sinh x * sin x := by
    unfold gammaSEqualLegacy at h; linarith
  rw [tan_eq_sin_div_cos, div_eq_div_iff hc hs.ne', mul_comm (sin x) (sinh x)]
  exact hbal.symm

theorem tan_eq_of_gammaSEqual_eq_zero {x : ℝ} (hx : 0 < x) (h : gammaSEqualLegacy x = 0) :
    tan x = cosh x / sinh x :=
  tan_eq_of_gammaSEqualLegacy_eq_zero hx h

theorem one_lt_tan_of_gammaSEqualLegacy_eq_zero {x : ℝ} (hx : 0 < x)
    (h : gammaSEqualLegacy x = 0) : 1 < tan x := by
  have hs : 0 < sinh x := sinh_pos_iff.mpr hx
  rw [tan_eq_of_gammaSEqualLegacy_eq_zero hx h, lt_div_iff₀ hs]
  have hsub := cosh_sub_sinh x
  have hp := exp_pos (-x)
  linarith

theorem node_is_simple_zeroLegacy {x : ℝ} (hx : 0 < x) (h : gammaSEqualLegacy x = 0) :
    deriv gammaSEqualLegacy x ≠ 0 := by
  intro hderiv
  have hsin : sin x = 0 := (deriv_gammaSEqualLegacy_eq_zero_iff x).1 hderiv
  have htan := one_lt_tan_of_gammaSEqualLegacy_eq_zero hx h
  rw [tan_eq_sin_div_cos, hsin, zero_div] at htan
  exact lt_irrefl (1 : ℝ) (lt_trans htan (by norm_num : (0 : ℝ) < 1))

theorem gammaEff_eq_gammaB_sq_at_nodeLegacy {x : ℝ} (h : gammaSEqualLegacy x = 0) :
    gammaEff (2 * x) (2 * x) = gammaB (2 * x) (2 * x) ^ 2 := by
  have hs : gammaS (2 * x) (2 * x) = 0 := by
    rw [← gammaSEqual_eq_gammaS]
    exact h
  unfold gammaEff
  rw [hs]
  ring

private theorem mem_quarter_half_of_one_lt_tan {t : ℝ}
    (ht0 : 0 < t) (htπ : t < π) (hcos : cos t ≠ 0) (htan : 1 < tan t) :
    π / 4 < t ∧ t < π / 2 := by
  have hπ := pi_pos
  have hne : t ≠ π / 2 := by
    intro hEq
    rw [hEq, cos_pi_div_two] at hcos
    exact hcos rfl
  have hlt : t < π / 2 := by
    rcases lt_or_gt_of_ne hne with hcase | hcase
    · exact hcase
    · exfalso
      have hcosneg : cos t < 0 := by
        have hstep := strictAntiOn_cos
          (a := π / 2) (b := t) ⟨by linarith, by linarith⟩
          ⟨by linarith, le_of_lt htπ⟩ hcase
        rwa [cos_pi_div_two] at hstep
      have hsinpos : 0 < sin t := sin_pos_of_pos_of_lt_pi ht0 htπ
      have htneg : tan t < 0 := by
        rw [tan_eq_sin_div_cos]
        exact div_neg_of_pos_of_neg hsinpos hcosneg
      linarith
  refine ⟨?_, hlt⟩
  by_contra hcon
  have hcon' : t ≤ π / 4 := not_lt.mp hcon
  have hmem₁ : t ∈ Ioo (-(π / 2)) (π / 2) := ⟨by linarith, hlt⟩
  have hmem₂ : π / 4 ∈ Ioo (-(π / 2)) (π / 2) := ⟨by linarith, by linarith⟩
  rcases eq_or_lt_of_le hcon' with hEq | hlt2
  · rw [hEq, tan_pi_div_four] at htan
    linarith
  · have hstep := strictMonoOn_tan hmem₁ hmem₂ hlt2
    rw [tan_pi_div_four] at hstep
    linarith

theorem node_mem_sharp_branchLegacy (n : ℕ) {x : ℝ}
    (hx : x ∈ Ioo ((n : ℝ) * π) ((n : ℝ) * π + π)) (h : gammaSEqualLegacy x = 0) :
    x ∈ Ioo ((n : ℝ) * π + π / 4) ((n : ℝ) * π + π / 2) := by
  obtain ⟨h1, h2⟩ := hx
  have hn0 : (0 : ℝ) ≤ (n : ℝ) * π := by positivity
  have hxpos : 0 < x := lt_of_le_of_lt hn0 h1
  set t := x - (n : ℝ) * π with ht
  have ht0 : 0 < t := by simp only [ht]; linarith
  have htπ : t < π := by simp only [ht]; linarith
  have hxt : x = (n : ℝ) * π + t := by simp only [ht]; ring
  have hcos : cos t ≠ 0 := by
    intro hc0
    have hcx := cos_ne_zero_of_gammaSEqualLegacy_eq_zero hxpos h
    rw [hxt, cos_nat_mul_pi_add, hc0, mul_zero] at hcx
    exact hcx rfl
  have htan : 1 < tan t := by
    have hper : tan (t + (n : ℝ) * π) = tan t :=
      (tan_periodic.nat_mul n) t
    have hcx := one_lt_tan_of_gammaSEqualLegacy_eq_zero hxpos h
    rw [hxt, add_comm ((n : ℝ) * π) t, hper] at hcx
    exact hcx
  obtain ⟨hlo, hhi⟩ := mem_quarter_half_of_one_lt_tan ht0 htπ hcos htan
  constructor
  · linarith [hlo]
  · linarith [hhi]

theorem gammaSEqualLegacy_eq_zero_iff_resonanceProd {x : ℝ} (hc : cos x ≠ 0) :
    gammaSEqualLegacy x = 0 ↔ resonanceProd x = 1 := by
  have hhalf : (2 * x) / 2 = x := by ring
  have hc' : cos ((2 * x) / 2) ≠ 0 := by rwa [hhalf]
  rw [gammaSEqual_eq_gammaS, gammaS_eq_zero_iff (2 * x) (2 * x) hc', hhalf]
  rfl

theorem resonanceRoot1_gammaSEqualLegacy_zero :
    gammaSEqualLegacy resonanceRootLegacy = 0 := by
  obtain ⟨_, hhi⟩ := resonanceRootLegacy_mem
  have hmem := resonanceRootLegacy_mem
  have hopen : resonanceRootLegacy ∈ Ioo (-(π / 2)) (π / 2) :=
    ⟨by linarith [hmem.1, pi_gt_three], by linarith [hmem.2, pi_gt_three]⟩
  have hcos : cos resonanceRootLegacy ≠ 0 := (cos_pos_of_mem_Ioo hopen).ne'
  exact (gammaSEqualLegacy_eq_zero_iff_resonanceProd hcos).mpr (resonanceRoot1_prod)

theorem resonanceRoot1_sharp_boundsLegacy :
    π / 4 < resonanceRootLegacy ∧ resonanceRootLegacy < 1 := by
  obtain ⟨hlo, hhi⟩ := resonanceRootLegacy_mem
  have hmem : resonanceRootLegacy ∈ Ioo (((0 : ℕ) : ℝ) * π) (((0 : ℕ) : ℝ) * π + π) := by
    simp only [Nat.cast_zero, zero_mul, zero_add, mem_Ioo]
    constructor <;> linarith [hlo, hhi, pi_gt_three]
  have hsharp := node_mem_sharp_branchLegacy 0 hmem resonanceRoot1_gammaSEqualLegacy_zero
  simp only [Nat.cast_zero, zero_mul, zero_add, mem_Ioo] at hsharp
  exact ⟨hsharp.1, hhi⟩

theorem branchNode_zero : branchNode 0 = π / 2 := by simp [branchNode]

theorem resonanceRoot1_sharp_bounds :
    π / 4 < resonanceRoot1 ∧ resonanceRoot1 < π := by
  rw [resonanceRoot1_eq_pi_div_two]
  constructor <;> linarith [pi_gt_three, pi_pos]

theorem resonanceRoot1_gammaSEqual_zero : gammaSEqual resonanceRoot1 = 0 := by
  simpa [resonanceRoot1, branchNode, cos_pi_div_two] using branchNode_gammaSEqual_zero 0

theorem node_mem_sharp_branch (n : ℕ) :
    branchNode n ∈ Ioo ((n : ℝ) * π + π / 4) ((n : ℝ) * π + π) := by
  unfold branchNode
  constructor <;> nlinarith [pi_pos, pi_gt_d2]

theorem exists_second_node_sharp :
    ∃ x₂ : ℝ, x₂ ∈ Ioo (π + π / 4) (π + π) ∧ gammaSEqual x₂ = 0 := by
  refine ⟨branchNode 1, ?_, branchNode_gammaSEqual_zero 1⟩
  simpa [branchNode] using node_mem_sharp_branch 1

/-! ### Layer radii -/

/-- Equal-scale layer radius `r = ℓ/(2x)`. -/
noncomputable def layerRadius (ℓ x : ℝ) : ℝ := ℓ / (2 * x)

theorem layerRadius_window {ℓ x : ℝ} (hℓ : 0 < ℓ) (n : ℕ)
    (hx : x ∈ Ioo ((n : ℝ) * π + π / 4) ((n : ℝ) * π + π / 2)) :
    ℓ / ((2 * (n : ℝ) + 1) * π) < layerRadius ℓ x ∧
      layerRadius ℓ x < 2 * ℓ / ((4 * (n : ℝ) + 1) * π) := by
  obtain ⟨h1, h2⟩ := hx
  have hπ := pi_pos
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hxpos : 0 < x := by nlinarith
  have hden1 : 0 < (2 * (n : ℝ) + 1) * π := by positivity
  have hden2 : 0 < (4 * (n : ℝ) + 1) * π := by positivity
  unfold layerRadius
  constructor
  · rw [div_lt_div_iff₀ hden1 (by positivity)]
    nlinarith [h2]
  · rw [div_lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * x) hden2]
    nlinarith [h1]

theorem layerRadius_window_zero {ℓ x : ℝ} (hℓ : 0 < ℓ)
    (hx : x ∈ Ioo (π / 4) (π / 2)) :
    ℓ / π < layerRadius ℓ x ∧ layerRadius ℓ x < 2 * ℓ / π := by
  have hx' : x ∈ Ioo (((0 : ℕ) : ℝ) * π + π / 4) (((0 : ℕ) : ℝ) * π + π / 2) := by
    simpa using hx
  have h := layerRadius_window hℓ 0 hx'
  simpa using h

theorem layerRadius_lt_two_ell_div_pi {ℓ x : ℝ} (hℓ : 0 < ℓ) (n : ℕ)
    (hx : x ∈ Ioo ((n : ℝ) * π + π / 4) ((n : ℝ) * π + π / 2)) :
    layerRadius ℓ x < 2 * ℓ / π := by
  have hπ := pi_pos
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hupper := (layerRadius_window hℓ n hx).2
  refine lt_of_lt_of_le hupper ?_
  rw [div_le_div_iff₀ (by positivity) hπ]
  nlinarith [mul_nonneg (mul_nonneg hℓ.le hπ.le) hn0]

/-! ### Amplitude growth of the plateau values -/

theorem cosh_pi_mul_cosh_le (a : ℝ) (ha : 0 ≤ a) :
    cosh π * cosh a ≤ cosh (a + π) := by
  rw [cosh_add]
  have hs : 0 ≤ sinh a := by
    rcases eq_or_lt_of_le ha with rfl | h
    · simp
    · exact (sinh_pos_iff.mpr h).le
  have hsπ : 0 < sinh π := sinh_pos_iff.mpr pi_pos
  nlinarith [hs, hsπ]

theorem cosh_pi_mul_growth (n : ℕ) :
    cosh π * cosh ((n : ℝ) * π) ≤ cosh (((n : ℝ) + 1) * π) := by
  have harg : ((n : ℝ) + 1) * π = (n : ℝ) * π + π := by ring
  rw [harg]
  exact cosh_pi_mul_cosh_le _ (by positivity)

theorem cosh_pi_pow_le_cosh_nat_mul_pi (n : ℕ) :
    cosh π ^ n ≤ cosh ((n : ℝ) * π) := by
  induction n with
  | zero => simp
  | succ k ih =>
    have hgrow := cosh_pi_mul_growth k
    have hcast : ((k : ℝ) + 1) * π = ((k + 1 : ℕ) : ℝ) * π := by push_cast; ring
    have hpos : 0 < cosh π := cosh_pos π
    calc cosh π ^ (k + 1)
        = cosh π * cosh π ^ k := by ring
      _ ≤ cosh π * cosh ((k : ℝ) * π) :=
          mul_le_mul_of_nonneg_left ih hpos.le
      _ ≤ cosh (((k : ℝ) + 1) * π) := hgrow
      _ = cosh (((k + 1 : ℕ) : ℝ) * π) := by rw [hcast]

theorem eleven_lt_cosh_pi : (11 : ℝ) < cosh π := by
  have he1 : (2.7182818283 : ℝ) < exp 1 := exp_one_gt_d9
  have he1pos : (0 : ℝ) < exp 1 := exp_pos 1
  have hexp3 : exp 1 * exp 1 * exp 1 = exp 3 := by
    rw [← exp_add, ← exp_add]
    norm_num
  have h3 : (20 : ℝ) < exp 3 := by
    rw [← hexp3]
    nlinarith [he1, he1pos]
  have hπ : (3.14 : ℝ) < π := pi_gt_d2
  have h2 : (1.14 : ℝ) < exp (π - 3) := by
    have hle := Real.add_one_le_exp (π - 3)
    linarith
  have hsplit : exp π = exp 3 * exp (π - 3) := by
    rw [← exp_add]
    ring_nf
  have hexpπ : (22 : ℝ) < exp π := by
    rw [hsplit]
    nlinarith [h3, h2, exp_pos (3 : ℝ), exp_pos (π - 3)]
  rw [cosh_eq]
  have := exp_pos (-π)
  linarith

theorem eleven_pow_le_cosh_nat_mul_pi (n : ℕ) :
    (11 : ℝ) ^ n ≤ cosh ((n : ℝ) * π) :=
  le_trans (pow_le_pow_left₀ (by norm_num) eleven_lt_cosh_pi.le n)
    (cosh_pi_pow_le_cosh_nat_mul_pi n)

theorem exp_pi_mul_cosh_sub_cosh_add_pi (a : ℝ) :
    exp π * cosh a - cosh (a + π) = sinh π * exp (-a) := by
  have h1 : exp π = cosh π + sinh π := (cosh_add_sinh π).symm
  have h2 : cosh a - sinh a = exp (-a) := cosh_sub_sinh a
  rw [cosh_add, h1]
  have hrw : sinh π * exp (-a) = sinh π * (cosh a - sinh a) := by rw [h2]
  rw [hrw]
  ring

theorem cosh_add_pi_lt_exp_pi_mul (a : ℝ) :
    cosh (a + π) < exp π * cosh a := by
  have hid := exp_pi_mul_cosh_sub_cosh_add_pi a
  have hpos : 0 < sinh π * exp (-a) :=
    mul_pos (sinh_pos_iff.mpr pi_pos) (exp_pos _)
  linarith

theorem cosh_add_pi_ratio_strictMono {a b : ℝ} (hab : a < b) :
    cosh (a + π) * cosh b < cosh (b + π) * cosh a := by
  have hid : cosh (a + π) * cosh b - cosh (b + π) * cosh a
      = sinh π * sinh (a - b) := by
    rw [cosh_add, cosh_add, sinh_sub]
    ring
  have hneg : sinh π * sinh (a - b) < 0 :=
    mul_neg_of_pos_of_neg (sinh_pos_iff.mpr pi_pos)
      (sinh_neg_iff.mpr (by linarith))
  linarith

theorem cosh_le_exp_of_nonneg {a : ℝ} (ha : 0 ≤ a) : cosh a ≤ exp a := by
  rw [cosh_eq]
  have hle : exp (-a) ≤ exp a := exp_le_exp.mpr (by linarith)
  linarith

theorem cosh_nat_mul_pi_le_exp (n : ℕ) :
    cosh ((n : ℝ) * π) ≤ exp ((n : ℝ) * π) :=
  cosh_le_exp_of_nonneg (by positivity)

/-! ### Inward screening of the mid-layer force -/

/-- Mid-layer (plateau) force factor: the force at the extremal radius `r = ℓ/(2nπ)` is
`k/(γ_s r²)`, i.e. `k/ℓ²` times this factor. -/
noncomputable def plateauForceFactor (n : ℕ) : ℝ :=
  4 * π ^ 2 * (n : ℝ) ^ 2 / cosh ((n : ℝ) * π)

theorem plateauForceFactor_nonneg (n : ℕ) : 0 ≤ plateauForceFactor n := by
  unfold plateauForceFactor
  positivity

theorem plateauForceFactor_strictAnti (n : ℕ) (hn : 1 ≤ n) :
    plateauForceFactor (n + 1) < plateauForceFactor n := by
  have hπ := pi_pos
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hcn : 0 < cosh ((n : ℝ) * π) := cosh_pos _
  have hcast : (((n + 1 : ℕ)) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
  have hgrow : cosh π * cosh ((n : ℝ) * π) ≤ cosh ((((n + 1 : ℕ)) : ℝ) * π) := by
    rw [hcast]
    exact cosh_pi_mul_growth n
  have hcn1 : 0 < cosh ((((n + 1 : ℕ)) : ℝ) * π) := cosh_pos _
  have hsq : 4 * π ^ 2 * ((((n + 1 : ℕ)) : ℝ)) ^ 2
      ≤ 4 * (4 * π ^ 2 * (n : ℝ) ^ 2) := by
    rw [hcast]
    nlinarith [hn1, sq_nonneg ((n : ℝ) - 1), pi_pos, sq_nonneg π]
  have hcosh11 : (11 : ℝ) < cosh π := eleven_lt_cosh_pi
  have hnum : 0 < 4 * π ^ 2 * (n : ℝ) ^ 2 :=
    mul_pos (by positivity) (pow_pos (by linarith : (0 : ℝ) < (n : ℝ)) 2)
  unfold plateauForceFactor
  rw [div_lt_div_iff₀ hcn1 hcn]
  calc 4 * π ^ 2 * (((n + 1 : ℕ)) : ℝ) ^ 2 * cosh ((n : ℝ) * π)
      ≤ 4 * (4 * π ^ 2 * (n : ℝ) ^ 2) * cosh ((n : ℝ) * π) :=
        mul_le_mul_of_nonneg_right hsq hcn.le
    _ < (4 * π ^ 2 * (n : ℝ) ^ 2) * (cosh π * cosh ((n : ℝ) * π)) := by
        have hACn : 0 < (4 * π ^ 2 * (n : ℝ) ^ 2) * cosh ((n : ℝ) * π) :=
          mul_pos hnum hcn
        nlinarith [hACn, hcosh11]
    _ ≤ (4 * π ^ 2 * (n : ℝ) ^ 2) * cosh ((((n + 1 : ℕ)) : ℝ) * π) :=
        mul_le_mul_of_nonneg_left hgrow hnum.le

theorem paper_amplitude_increase_inward_false :
    ¬ (∀ n : ℕ, 1 ≤ n → plateauForceFactor n < plateauForceFactor (n + 1)) := by
  intro h
  have h1 := h 1 le_rfl
  have h2 := plateauForceFactor_strictAnti 1 le_rfl
  linarith

/-! ### The equal-scale locus is the balanced locus `J = 0` -/

/-- Equal-scale torsion parameters `α = β`. -/
def equalScaleParams (α : Fin 3 → ℝ) : TorsionParams where
  alpha := α
  beta := α

theorem J_equalScaleParams (α : Fin 3 → ℝ) : J (equalScaleParams α) = 0 := by
  rw [J_coef]
  simp [equalScaleParams]

theorem mass_equalScaleParams (α : Fin 3 → ℝ) :
    mass (equalScaleParams α) = ∑ a : Fin 3, (α a) ^ 2 := by
  rw [mass_coef]
  simp only [equalScaleParams, Fin.sum_univ_three]
  ring

theorem mass_equalScaleParams_pos {α : Fin 3 → ℝ} (h : ∃ a, α a ≠ 0) :
    0 < mass (equalScaleParams α) := by
  obtain ⟨a, ha⟩ := h
  rw [mass_equalScaleParams]
  refine Finset.sum_pos' (fun i _ => sq_nonneg (α i)) ⟨a, Finset.mem_univ a, ?_⟩
  exact pow_pos (abs_pos.mpr ha) 2 |>.trans_le (by rw [sq_abs])

/-- The layer order parameter is `gammaS`, not `J`. -/
theorem layer_order_parameter_is_gammaS :
    (∀ α : Fin 3 → ℝ, J (equalScaleParams α) = 0) ∧
      ∃ x y : ℝ, 0 < gammaSEqual x ∧ gammaSEqual y < 0 := by
  refine ⟨J_equalScaleParams, 0, π, ?_, ?_⟩
  · rw [gammaSEqual_zero]; norm_num
  · have h := gammaSEqual_nat_mul_pi 1
    norm_num at h
    rw [h]
    have := cosh_pos π
    linarith

end Gravity

end DstDiophantine
