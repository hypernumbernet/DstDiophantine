import DstDiophantine.Algebra.Admissible
import DstDiophantine.Gravity.DualRotorVacuum
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The written mismatch is the product of the free lag and the common rapidity

On the written flow `J = δ σ / 2`. For positive stiffness that product is
constant only when the lag vanishes, and then it is zero. Any other lag sends
it to `-∞` at both ends of the time axis. The same flow remains in the
admissible cone for every time only at a resting aligned rapidity in
`[0, π/2]`. The cone's ceiling is not a bound kept by these angles.
-/

namespace DstDiophantine

namespace Gravity

open RelativeRotor Invariant Admissible Filter Polynomial

/-- Mismatch of the written angles, `δ(t) σ(t) / 2`. -/
noncomputable def writtenLagProduct (σ₀ σd₀ m δ₀ ν t : ℝ) : ℝ :=
  writtenDelta δ₀ ν t * writtenSigma σ₀ σd₀ m δ₀ ν t / 2

theorem writtenLagProduct_poly (σ₀ σd₀ m δ₀ ν t : ℝ) :
    writtenLagProduct σ₀ σd₀ m δ₀ ν t =
      δ₀ * σ₀ / 2 +
        (δ₀ * σd₀ + ν * σ₀) / 2 * t +
        (ν * σd₀ / 2 - m * δ₀ ^ 2 / 2) * t ^ 2 +
        (-(2 / 3) * m * ν * δ₀) * t ^ 3 +
        (-(m * ν ^ 2 / 6)) * t ^ 4 := by
  unfold writtenLagProduct writtenDelta writtenSigma affineMismatch cubicRapidity
  ring

theorem writtenLagProduct_frozen (σ₀ σd₀ m δ₀ t : ℝ) :
    writtenLagProduct σ₀ σd₀ m δ₀ 0 t =
      -(m * δ₀ ^ 2 / 2) * t ^ 2 + (δ₀ * σd₀ / 2) * t + δ₀ * σ₀ / 2 := by
  rw [writtenLagProduct_poly]
  ring

theorem written_flow_J (σ₀ σd₀ m δ₀ ν t : ℝ) :
    J (axisParams (writtenUsual σ₀ σd₀ m δ₀ ν t) (writtenDual σ₀ σd₀ m δ₀ ν t)) =
      writtenLagProduct σ₀ σd₀ m δ₀ ν t := by
  simp only [writtenUsual, writtenDual, usualFrom, dualFrom, writtenLagProduct]
  rw [axis_J_sum_diff]

theorem written_flow_mass (σ₀ σd₀ m δ₀ ν t : ℝ) :
    mass (axisParams (writtenUsual σ₀ σd₀ m δ₀ ν t) (writtenDual σ₀ σd₀ m δ₀ ν t)) =
      (writtenSigma σ₀ σd₀ m δ₀ ν t ^ 2 + writtenDelta δ₀ ν t ^ 2) / 4 := by
  simp only [writtenUsual, writtenDual, usualFrom, dualFrom]
  rw [axis_mass_sum_diff]

/-! ### The product as a polynomial -/

noncomputable def lagPoly (σ₀ σd₀ m δ₀ ν : ℝ) : ℝ[X] :=
  C (δ₀ * σ₀ / 2) +
    C ((δ₀ * σd₀ + ν * σ₀) / 2) * X +
    C (ν * σd₀ / 2 - m * δ₀ ^ 2 / 2) * X ^ 2 +
    C (-(2 / 3) * m * ν * δ₀) * X ^ 3 +
    C (-(m * ν ^ 2 / 6)) * X ^ 4

theorem lagPoly_coeff_four (σ₀ σd₀ m δ₀ ν : ℝ) :
    (lagPoly σ₀ σd₀ m δ₀ ν).coeff 4 = -(m * ν ^ 2 / 6) := by
  simp only [lagPoly, coeff_add, coeff_C, coeff_C_mul, coeff_X]
  norm_num

theorem lagPoly_coeff_three (σ₀ σd₀ m δ₀ ν : ℝ) :
    (lagPoly σ₀ σd₀ m δ₀ ν).coeff 3 = -(2 / 3) * m * ν * δ₀ := by
  simp only [lagPoly, coeff_add, coeff_C, coeff_C_mul, coeff_X]
  norm_num

theorem lagPoly_coeff_two (σ₀ σd₀ m δ₀ ν : ℝ) :
    (lagPoly σ₀ σd₀ m δ₀ ν).coeff 2 = ν * σd₀ / 2 - m * δ₀ ^ 2 / 2 := by
  simp only [lagPoly, coeff_add, coeff_C, coeff_C_mul, coeff_X]
  norm_num

theorem lagPoly_eval (σ₀ σd₀ m δ₀ ν t : ℝ) :
    (lagPoly σ₀ σd₀ m δ₀ ν).eval t = writtenLagProduct σ₀ σd₀ m δ₀ ν t := by
  simp only [lagPoly, eval_add, eval_mul, eval_pow, eval_C, eval_X, writtenLagProduct_poly]

/-- `-(m a² / c) = 0` with `m` and `c` positive forces `a = 0`. -/
private theorem eq_zero_of_neg_div_square {m a c : ℝ} (hm : 0 < m) (hc : 0 < c)
    (h : -(m * a ^ 2 / c) = 0) : a = 0 := by
  have hmul : m * a ^ 2 = 0 := by
    have h0 : m * a ^ 2 / c = 0 := by linarith
    field_simp [hc.ne'] at h0
    linarith
  exact sq_eq_zero_iff.mp ((mul_eq_zero.mp hmul).resolve_left hm.ne')

theorem writtenLagProduct_const_iff {σ₀ σd₀ m δ₀ ν : ℝ} (hm : 0 < m) :
    (∀ t, writtenLagProduct σ₀ σd₀ m δ₀ ν t = writtenLagProduct σ₀ σd₀ m δ₀ ν 0) ↔
      δ₀ = 0 ∧ ν = 0 := by
  constructor
  · intro h
    have hpoly : lagPoly σ₀ σd₀ m δ₀ ν = C ((lagPoly σ₀ σd₀ m δ₀ ν).eval 0) := by
      apply Polynomial.funext
      intro t
      rw [eval_C, lagPoly_eval, lagPoly_eval, h t, h 0]
    have h4 : (lagPoly σ₀ σd₀ m δ₀ ν).coeff 4 = 0 := by
      rw [hpoly]
      simp
    have h2 : (lagPoly σ₀ σd₀ m δ₀ ν).coeff 2 = 0 := by
      rw [hpoly]
      simp
    rw [lagPoly_coeff_four] at h4
    rw [lagPoly_coeff_two] at h2
    have hν : ν = 0 := eq_zero_of_neg_div_square hm (by norm_num) h4
    rw [hν, zero_mul, zero_div, zero_sub] at h2
    exact ⟨eq_zero_of_neg_div_square hm (by norm_num) h2, hν⟩
  · intro ⟨hδ, hν⟩ t
    simp [writtenLagProduct, writtenDelta, writtenSigma, affineMismatch, cubicRapidity, hδ, hν]

private theorem lagPoly_natDegree_le (σ₀ σd₀ m δ₀ ν : ℝ) :
    (lagPoly σ₀ σd₀ m δ₀ ν).natDegree ≤ 4 := by
  unfold lagPoly
  have hC {a : ℝ} : (C a).natDegree ≤ 4 := by
    rw [natDegree_C]
    decide
  have hX {a : ℝ} : (C a * X).natDegree ≤ 4 := by
    rw [← pow_one X]
    exact (natDegree_C_mul_X_pow_le a 1).trans (by decide)
  have hpow {a : ℝ} {n : ℕ} (hn : n ≤ 4) : (C a * X ^ n).natDegree ≤ 4 :=
    (natDegree_C_mul_X_pow_le a n).trans hn
  refine (natDegree_add_le _ _).trans (max_le ?_ (hpow (by decide)))
  refine (natDegree_add_le _ _).trans (max_le ?_ (hpow (by decide)))
  refine (natDegree_add_le _ _).trans (max_le ?_ (hpow (by decide)))
  exact (natDegree_add_le _ _).trans (max_le hC hX)

private theorem tendsto_eval_of_natDegree {p : ℝ[X]} {n : ℕ}
    (hn : p.natDegree = n) (hdeg : 0 < n) (hlead : p.leadingCoeff ≤ 0) :
    Tendsto (fun t => p.eval t) atTop atBot := by
  have hne : p ≠ 0 := by
    intro hp
    have : n = 0 := by simpa [hp, natDegree_zero] using hn.symm
    rw [this] at hdeg
    exact Nat.lt_irrefl _ hdeg
  have hp : 0 < p.degree := by
    rw [degree_eq_natDegree hne, hn]
    exact WithBot.coe_lt_coe.mpr hdeg
  exact p.tendsto_atBot_of_leadingCoeff_nonpos hp hlead

private theorem natDegree_eq_two_of_tail {p : ℝ[X]} (hle : p.natDegree ≤ 4)
    (h3 : p.coeff 3 = 0) (h4 : p.coeff 4 = 0) (h2 : p.coeff 2 ≠ 0) : p.natDegree = 2 := by
  refine le_antisymm ?_ (le_natDegree_of_ne_zero h2)
  rw [natDegree_le_iff_coeff_eq_zero]
  intro n hn
  by_cases hhi : 4 < n
  · exact coeff_eq_zero_of_natDegree_lt (Nat.lt_of_le_of_lt hle hhi)
  · rcases Nat.eq_or_lt_of_le (Nat.succ_le_of_lt hn) with rfl | hn3
    · exact h3
    · rcases Nat.eq_or_lt_of_le (Nat.succ_le_of_lt hn3) with rfl | hn4
      · exact h4
      · exact absurd hn4 hhi

/-- A nonzero rate makes the degree-four term the leading term, and it is negative. -/
private theorem lagPoly_tendsto_of_rate {σ₀ σd₀ m δ₀ ν : ℝ} (hm : 0 < m) (hν : ν ≠ 0) :
    Tendsto (fun t => (lagPoly σ₀ σd₀ m δ₀ ν).eval t) atTop atBot := by
  have hc4 : (lagPoly σ₀ σd₀ m δ₀ ν).coeff 4 = -(m * ν ^ 2 / 6) :=
    lagPoly_coeff_four σ₀ σd₀ m δ₀ ν
  have hc4ne : (lagPoly σ₀ σd₀ m δ₀ ν).coeff 4 ≠ 0 := by
    intro h0
    exact hν <| eq_zero_of_neg_div_square hm (by norm_num) (hc4.symm.trans h0)
  have hnat : (lagPoly σ₀ σd₀ m δ₀ ν).natDegree = 4 :=
    le_antisymm (lagPoly_natDegree_le σ₀ σd₀ m δ₀ ν) (le_natDegree_of_ne_zero hc4ne)
  have hlead : (lagPoly σ₀ σd₀ m δ₀ ν).leadingCoeff ≤ 0 := by
    rw [leadingCoeff, hnat, hc4]
    have : 0 ≤ m * ν ^ 2 / 6 := by positivity
    linarith
  exact tendsto_eval_of_natDegree hnat (by decide) hlead

private theorem lagPoly_tendsto_atTop_of_lag {σ₀ σd₀ m δ₀ ν : ℝ}
    (hm : 0 < m) (h : δ₀ ≠ 0 ∨ ν ≠ 0) :
    Tendsto (fun t => (lagPoly σ₀ σd₀ m δ₀ ν).eval t) atTop atBot := by
  by_cases hν : ν = 0
  · have hδ : δ₀ ≠ 0 := by
      rcases h with hδ | hν'
      · exact hδ
      · exact absurd hν hν'
    have hc2 : (lagPoly σ₀ σd₀ m δ₀ ν).coeff 2 = -(m * δ₀ ^ 2 / 2) := by
      rw [lagPoly_coeff_two, hν]
      ring
    have hc2ne : (lagPoly σ₀ σd₀ m δ₀ ν).coeff 2 ≠ 0 := by
      intro h0
      exact hδ <| eq_zero_of_neg_div_square hm (by norm_num) (hc2.symm.trans h0)
    have hc3 : (lagPoly σ₀ σd₀ m δ₀ ν).coeff 3 = 0 := by
      rw [lagPoly_coeff_three, hν]
      ring
    have hc4 : (lagPoly σ₀ σd₀ m δ₀ ν).coeff 4 = 0 := by
      rw [lagPoly_coeff_four, hν]
      ring
    have hnat := natDegree_eq_two_of_tail (lagPoly_natDegree_le σ₀ σd₀ m δ₀ ν) hc3 hc4 hc2ne
    have hlead : (lagPoly σ₀ σd₀ m δ₀ ν).leadingCoeff ≤ 0 := by
      rw [leadingCoeff, hnat, hc2]
      have : 0 ≤ m * δ₀ ^ 2 / 2 := by positivity
      linarith
    exact tendsto_eval_of_natDegree hnat (by decide) hlead
  · exact lagPoly_tendsto_of_rate hm hν

theorem writtenLagProduct_timeFlip (σ₀ σd₀ m δ₀ ν t : ℝ) :
    writtenLagProduct σ₀ (-σd₀) m δ₀ (-ν) (-t) =
      writtenLagProduct σ₀ σd₀ m δ₀ ν t := by
  rw [writtenLagProduct_poly, writtenLagProduct_poly]
  ring

theorem writtenLagProduct_tendsto_atTop {σ₀ σd₀ m δ₀ ν : ℝ}
    (hm : 0 < m) (h : δ₀ ≠ 0 ∨ ν ≠ 0) :
    Tendsto (writtenLagProduct σ₀ σd₀ m δ₀ ν) atTop atBot := by
  have hpoly := lagPoly_tendsto_atTop_of_lag (σ₀ := σ₀) (σd₀ := σd₀) (m := m)
    (δ₀ := δ₀) (ν := ν) hm h
  refine hpoly.congr fun t => ?_
  exact lagPoly_eval σ₀ σd₀ m δ₀ ν t

theorem writtenLagProduct_tendsto_atBot {σ₀ σd₀ m δ₀ ν : ℝ}
    (hm : 0 < m) (h : δ₀ ≠ 0 ∨ ν ≠ 0) :
    Tendsto (writtenLagProduct σ₀ σd₀ m δ₀ ν) atBot atBot := by
  have hflipLag : δ₀ ≠ 0 ∨ -ν ≠ 0 := by
    rcases h with hδ | hν
    · exact Or.inl hδ
    · exact Or.inr (neg_ne_zero.mpr hν)
  have htop := writtenLagProduct_tendsto_atTop (σ₀ := σ₀) (σd₀ := -σd₀) (m := m)
    (δ₀ := δ₀) (ν := -ν) hm hflipLag
  have hcomp : Tendsto (fun t => writtenLagProduct σ₀ (-σd₀) m δ₀ (-ν) (-t)) atBot atBot :=
    htop.comp tendsto_neg_atBot_atTop
  refine hcomp.congr fun t => ?_
  exact writtenLagProduct_timeFlip σ₀ σd₀ m δ₀ ν t

/-! ### Cone -/

theorem axisParams_admissible_iff (α β : ℝ) :
    IsAdmissibleContinuous (axisParams α β) ↔
      0 ≤ α ∧ 0 ≤ β ∧ α + β ≤ Real.pi / 2 := by
  constructor
  · intro h
    simpa [axisParams] using h 0
  · intro h a
    have hpi : (0 : ℝ) ≤ Real.pi / 2 := div_nonneg Real.pi_nonneg (by norm_num)
    fin_cases a
    · simpa [axisParams] using h
    · simp [axisParams, hpi]
    · simp [axisParams, hpi]

theorem sumDiff_admissible_iff (σ δ : ℝ) :
    IsAdmissibleContinuous (axisParams ((σ + δ) / 2) ((σ - δ) / 2)) ↔
      |δ| ≤ σ ∧ σ ≤ Real.pi / 2 := by
  rw [axisParams_admissible_iff]
  constructor
  · intro ⟨hφ, hθ, hσ⟩
    refine ⟨?_, by linarith⟩
    rw [abs_le]
    constructor <;> linarith
  · intro ⟨habs, hσ⟩
    rw [abs_le] at habs
    refine ⟨by linarith, by linarith, by linarith⟩

theorem written_flow_admissible_iff (σ₀ σd₀ m δ₀ ν t : ℝ) :
    IsAdmissibleContinuous (axisParams (writtenUsual σ₀ σd₀ m δ₀ ν t)
      (writtenDual σ₀ σd₀ m δ₀ ν t)) ↔
      |writtenDelta δ₀ ν t| ≤ writtenSigma σ₀ σd₀ m δ₀ ν t ∧
        writtenSigma σ₀ σd₀ m δ₀ ν t ≤ Real.pi / 2 := by
  simp only [writtenUsual, writtenDual, usualFrom, dualFrom]
  exact sumDiff_admissible_iff _ _

noncomputable def sigmaPoly (σ₀ σd₀ m δ₀ ν : ℝ) : ℝ[X] :=
  C σ₀ + C σd₀ * X + C (-(m * δ₀)) * X ^ 2 + C (-(m * ν / 3)) * X ^ 3

private theorem sigmaPoly_coeff_one (σ₀ σd₀ m δ₀ ν : ℝ) :
    (sigmaPoly σ₀ σd₀ m δ₀ ν).coeff 1 = σd₀ := by
  simp only [sigmaPoly, coeff_add, coeff_C, coeff_C_mul, coeff_X]
  norm_num

private theorem sigmaPoly_coeff_two (σ₀ σd₀ m δ₀ ν : ℝ) :
    (sigmaPoly σ₀ σd₀ m δ₀ ν).coeff 2 = -(m * δ₀) := by
  simp only [sigmaPoly, coeff_add, coeff_C, coeff_C_mul, coeff_X]
  norm_num

private theorem sigmaPoly_coeff_three (σ₀ σd₀ m δ₀ ν : ℝ) :
    (sigmaPoly σ₀ σd₀ m δ₀ ν).coeff 3 = -(m * ν / 3) := by
  simp only [sigmaPoly, coeff_add, coeff_C, coeff_C_mul, coeff_X]
  norm_num

theorem sigmaPoly_eval (σ₀ σd₀ m δ₀ ν t : ℝ) :
    (sigmaPoly σ₀ σd₀ m δ₀ ν).eval t = writtenSigma σ₀ σd₀ m δ₀ ν t := by
  simp only [sigmaPoly, eval_add, eval_mul, eval_pow, eval_C, eval_X, writtenSigma, cubicRapidity]
  ring

theorem written_flow_forever_admissible_iff {σ₀ σd₀ m δ₀ ν : ℝ} (hm : 0 < m) :
    (∀ t, IsAdmissibleContinuous (axisParams (writtenUsual σ₀ σd₀ m δ₀ ν t)
      (writtenDual σ₀ σd₀ m δ₀ ν t))) ↔
      δ₀ = 0 ∧ ν = 0 ∧ σd₀ = 0 ∧ 0 ≤ σ₀ ∧ σ₀ ≤ Real.pi / 2 := by
  constructor
  · intro h
    have hcone : ∀ t, |writtenDelta δ₀ ν t| ≤ writtenSigma σ₀ σd₀ m δ₀ ν t ∧
        writtenSigma σ₀ σd₀ m δ₀ ν t ≤ Real.pi / 2 :=
      fun t => (written_flow_admissible_iff σ₀ σd₀ m δ₀ ν t).mp (h t)
    have hbound : IsBoundedUnder (· ≤ ·) atTop fun t => |(sigmaPoly σ₀ σd₀ m δ₀ ν).eval t| := by
      refine ⟨Real.pi / 2, eventually_map.mpr <| Eventually.of_forall ?_⟩
      intro t
      rw [sigmaPoly_eval]
      have hpair := hcone t
      have hnn : 0 ≤ writtenSigma σ₀ σd₀ m δ₀ ν t := le_trans (abs_nonneg _) hpair.1
      rw [abs_of_nonneg hnn]
      exact hpair.2
    have hdeg : (sigmaPoly σ₀ σd₀ m δ₀ ν).degree ≤ 0 :=
      (isBoundedUnder_abs_atTop_iff _).mp hbound
    have hnat : (sigmaPoly σ₀ σd₀ m δ₀ ν).natDegree ≤ 0 := natDegree_le_of_degree_le hdeg
    have hcoeff (k : ℕ) (hk : 0 < k) : (sigmaPoly σ₀ σd₀ m δ₀ ν).coeff k = 0 :=
      coeff_eq_zero_of_natDegree_lt (Nat.lt_of_le_of_lt hnat hk)
    have hc1 := hcoeff 1 (by decide)
    have hc2 := hcoeff 2 (by decide)
    have hc3 := hcoeff 3 (by decide)
    rw [sigmaPoly_coeff_three] at hc3
    rw [sigmaPoly_coeff_two] at hc2
    rw [sigmaPoly_coeff_one] at hc1
    have hν : ν = 0 := by
      have hmul : m * ν = 0 := by
        field_simp at hc3
        linarith
      exact (mul_eq_zero.mp hmul).resolve_left hm.ne'
    have hδ : δ₀ = 0 := (mul_eq_zero.mp (neg_eq_zero.mp hc2)).resolve_left hm.ne'
    have hσd : σd₀ = 0 := hc1
    have h0 := hcone 0
    have hσ : writtenSigma σ₀ σd₀ m δ₀ ν 0 = σ₀ := by
      unfold writtenSigma cubicRapidity
      ring
    have hδ0 : writtenDelta δ₀ ν 0 = 0 := by
      unfold writtenDelta affineMismatch
      simp [hδ, hν]
    rw [hσ, hδ0] at h0
    exact ⟨hδ, hν, hσd, by simpa using h0.1, h0.2⟩
  · intro ⟨hδ, hν, hσd, h0, hpi⟩ t
    rw [written_flow_admissible_iff]
    constructor
    · simpa [writtenDelta, affineMismatch, writtenSigma, cubicRapidity, hδ, hν, hσd] using h0
    · simpa [writtenDelta, affineMismatch, writtenSigma, cubicRapidity, hδ, hν, hσd] using hpi

end Gravity

end DstDiophantine
