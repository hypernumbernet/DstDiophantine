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

theorem strictAntiOn_gammaSSigned {n : ℕ} (hn : Even n) :
    StrictAntiOn (gammaSSigned n) (Icc ((n : ℝ) * π) ((n : ℝ) * π + π)) := by
  rcases even_iff_two_dvd.mp hn with ⟨k, rfl⟩
  refine strictAntiOn_of_deriv_neg (convex_Icc _ _)
    (continuous_gammaSSigned (2 * k)).continuousOn ?_
  intro x hx
  simp only [interior_Icc] at hx
  obtain ⟨hx1, hx2⟩ := hx
  have hs := signed_sin_pos_on_branch (2 * k) ⟨hx1, hx2⟩
  have hc := cosh_pos x
  have ht0 : 0 < x - (2 * k : ℝ) * π := sub_pos.mpr (by simpa using hx1)
  have htπ : x - (2 * k : ℝ) * π < π := by linarith [hx2]
  have hsinh := sinh_cos_sub_lt ht0 htπ
  suffices hderiv : sinh x * cos x - cosh x * sin x < 0 by
    simpa [deriv_gammaSSigned, deriv_gammaSEqual, pow_mul, Nat.even_mul] using hderiv
  exact hsinh

private theorem sin_neg_of_signed_sin_pos_branch {n : ℕ} {x : ℝ}
    (hs : 0 < (-1 : ℝ) ^ n * sin x) (hn : Odd n) : sin x < 0 := by
  obtain ⟨k, rfl⟩ := hn
  have hpow : (-1 : ℝ) ^ (2 * k + 1) = -1 := by
    simp [pow_add, pow_mul, neg_one_sq, one_mul]
  rw [hpow, neg_mul] at hs
  simpa using hs

private theorem cosh_sin_lt_sinh_cos_of_sin_neg {x : ℝ}
    (hsin : sin x < 0) (hx0 : 0 < x) :
    cosh x * sin x < sinh x * cos x := by
  have hc := cosh_pos x
  have hs := sinh_pos_iff.mpr hx0
  nlinarith [hsin, hc, hs, sinh_add_cosh, Real.sin_sq_add_cos_sq x]

theorem strictAntiOn_gammaSSigned_odd (k : ℕ) :
    StrictAntiOn (gammaSSigned (2 * k + 1))
      (Icc (((2 * k + 1 : ℕ) : ℝ) * π) ((2 * k + 1 : ℕ) * π + π)) := by
  refine strictAntiOn_of_deriv_neg (convex_Icc _ _)
    (continuous_gammaSSigned (2 * k + 1)).continuousOn ?_
  intro x hx
  simp only [interior_Icc] at hx
  obtain ⟨hx1, hx2⟩ := hx
  have hs := signed_sin_pos_on_branch (2 * k + 1) ⟨hx1, hx2⟩
  have hsin := sin_neg_of_signed_sin_pos_branch hs ⟨k, rfl⟩
  have hx0 : 0 < x := lt_trans (by linarith [pi_pos]) hx1
  have hlt := cosh_sin_lt_sinh_cos_of_sin_neg hsin hx0
  suffices hderiv : deriv (gammaSSigned (2 * k + 1)) x < 0 by exact hderiv
  rw [deriv_gammaSSigned, deriv_gammaSEqual]
  simp [pow_succ, pow_mul]
  linarith [hlt]

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
  simp [deriv_gammaSSigned, deriv_gammaSEqual, pow_zero, one_mul]
  exact sinh_cos_sub_lt hx.1 hx.2

theorem strictAntiOn_gammaSEqual_even (k : ℕ) :
    StrictAntiOn gammaSEqual
      (Icc (((2 * k : ℕ) : ℝ) * π) (((2 * k : ℕ) : ℝ) * π + π)) := by
  have h := strictAntiOn_gammaSSigned (even_two_mul k)
  intro a ha b hb hab
  have hlt := h ha hb hab
  unfold gammaSSigned at hlt
  rw [pow_mul] at hlt
  norm_num at hlt
  exact hlt

theorem strictMonoOn_gammaSEqual_odd (k : ℕ) :
    StrictMonoOn gammaSEqual
      (Icc (((2 * k + 1 : ℕ) : ℝ) * π) (((2 * k + 1 : ℕ) : ℝ) * π + π)) := by
  have h := strictAntiOn_gammaSSigned_odd k
  intro a ha b hb hab
  have hlt := h ha hb hab
  unfold gammaSSigned at hlt
  rw [show (-1 : ℝ) ^ (2 * k + 1) = -1 by simp [pow_succ, pow_mul]] at hlt
  linarith

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
