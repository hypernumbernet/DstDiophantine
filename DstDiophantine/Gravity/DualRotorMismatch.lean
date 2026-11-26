import DstDiophantine.Algebra.Admissible
import DstDiophantine.Gravity.DualRotorVacuum
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Roots
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

private theorem coeff_scaled_pow (a : ℝ) (n k : ℕ) :
    (C a * X ^ n).coeff k = if k = n then a else 0 := by
  simp only [coeff_C_mul, coeff_X_pow]
  split_ifs <;> simp

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
    have hν : ν = 0 := by
      have hmul : m * ν ^ 2 = 0 := by
        field_simp at h4
        linarith
      exact sq_eq_zero_iff.mp ((mul_eq_zero.mp hmul).resolve_left hm.ne')
    rw [hν] at h2
    have hδ : δ₀ = 0 := by
      have hmul : m * δ₀ ^ 2 = 0 := by
        field_simp at h2
        linarith
      exact sq_eq_zero_iff.mp ((mul_eq_zero.mp hmul).resolve_left hm.ne')
    exact ⟨hδ, hν⟩
  · intro ⟨hδ, hν⟩ t
    simp [writtenLagProduct, writtenDelta, writtenSigma, affineMismatch, cubicRapidity, hδ, hν]

private theorem ne_of_gt {n k : ℕ} (hn : k < n) : n ≠ k := by
  intro h
  subst h
  exact Nat.lt_irrefl _ hn

private theorem lagPoly_coeff_high {σ₀ σd₀ m δ₀ ν : ℝ} {n : ℕ} (hn : 4 < n) :
    (lagPoly σ₀ σd₀ m δ₀ ν).coeff n = 0 := by
  simp only [lagPoly, coeff_add, coeff_C, coeff_C_mul, coeff_X]
  have h0 : n ≠ 0 := ne_of_gt (Nat.lt_trans (by decide : 0 < 4) hn)
  have h1 : n ≠ 1 := ne_of_gt (Nat.lt_trans (by decide : 1 < 4) hn)
  have h2 : n ≠ 2 := ne_of_gt (Nat.lt_trans (by decide : 2 < 4) hn)
  have h3 : n ≠ 3 := ne_of_gt (Nat.lt_trans (by decide : 3 < 4) hn)
  have h4 : n ≠ 4 := ne_of_gt hn
  simp [h0, h2, h3, h4, Ne.symm h1]

private theorem lagPoly_natDegree_le (σ₀ σd₀ m δ₀ ν : ℝ) :
    (lagPoly σ₀ σd₀ m δ₀ ν).natDegree ≤ 4 := by
  rw [natDegree_le_iff_degree_le, degree_le_iff_coeff_zero]
  intro n hn
  exact lagPoly_coeff_high (WithBot.coe_lt_coe.mp hn)

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

private theorem lagPoly_tendsto_atTop_of_lag {σ₀ σd₀ m δ₀ ν : ℝ}
    (hm : 0 < m) (h : δ₀ ≠ 0 ∨ ν ≠ 0) :
    Tendsto (fun t => (lagPoly σ₀ σd₀ m δ₀ ν).eval t) atTop atBot := by
  rcases h with hδ | hν
  · by_cases hrate : ν = 0
    · have hc2 : (lagPoly σ₀ σd₀ m δ₀ ν).coeff 2 = -(m * δ₀ ^ 2 / 2) := by
        rw [lagPoly_coeff_two, hrate]
        ring
      have hc2ne : (lagPoly σ₀ σd₀ m δ₀ ν).coeff 2 ≠ 0 := by
        intro h0
        rw [hc2] at h0
        have : m * δ₀ ^ 2 = 0 := by
          field_simp at h0
          linarith
        exact hδ (sq_eq_zero_iff.mp ((mul_eq_zero.mp this).resolve_left hm.ne'))
      have hc3 : (lagPoly σ₀ σd₀ m δ₀ ν).coeff 3 = 0 := by
        rw [lagPoly_coeff_three, hrate]
        ring
      have hc4 : (lagPoly σ₀ σd₀ m δ₀ ν).coeff 4 = 0 := by
        rw [lagPoly_coeff_four, hrate]
        ring
      have hnat : (lagPoly σ₀ σd₀ m δ₀ ν).natDegree = 2 := by
        apply le_antisymm
        · rw [natDegree_le_iff_degree_le, degree_le_iff_coeff_zero]
          intro n hn
          have hn2 : 2 < n := WithBot.coe_lt_coe.mp hn
          by_cases h3 : n = 3
          · simpa [h3] using hc3
          · by_cases h4 : n = 4
            · simpa [h4] using hc4
            · have hgt : 4 < n := by
                have hge3 : 3 ≤ n := Nat.succ_le_of_lt hn2
                have hgt3 : 3 < n := Nat.lt_of_le_of_ne hge3 (Ne.symm h3)
                have hge4 : 4 ≤ n := Nat.succ_le_of_lt hgt3
                exact Nat.lt_of_le_of_ne hge4 (Ne.symm h4)
              exact lagPoly_coeff_high hgt
        · exact le_natDegree_of_ne_zero hc2ne
      have hlead : (lagPoly σ₀ σd₀ m δ₀ ν).leadingCoeff ≤ 0 := by
        rw [leadingCoeff, hnat, hc2]
        have : 0 ≤ m * δ₀ ^ 2 / 2 := by positivity
        linarith
      exact tendsto_eval_of_natDegree hnat (by decide) hlead
    · have hc4 : (lagPoly σ₀ σd₀ m δ₀ ν).coeff 4 = -(m * ν ^ 2 / 6) :=
        lagPoly_coeff_four σ₀ σd₀ m δ₀ ν
      have hc4ne : (lagPoly σ₀ σd₀ m δ₀ ν).coeff 4 ≠ 0 := by
        intro h0
        rw [hc4] at h0
        have : m * ν ^ 2 = 0 := by
          field_simp at h0
          linarith
        exact hrate (sq_eq_zero_iff.mp ((mul_eq_zero.mp this).resolve_left hm.ne'))
      have hnat : (lagPoly σ₀ σd₀ m δ₀ ν).natDegree = 4 :=
        le_antisymm (lagPoly_natDegree_le σ₀ σd₀ m δ₀ ν) (le_natDegree_of_ne_zero hc4ne)
      have hlead : (lagPoly σ₀ σd₀ m δ₀ ν).leadingCoeff ≤ 0 := by
        rw [leadingCoeff, hnat, hc4]
        have : 0 ≤ m * ν ^ 2 / 6 := by positivity
        linarith
      exact tendsto_eval_of_natDegree hnat (by decide) hlead
  · have hc4 : (lagPoly σ₀ σd₀ m δ₀ ν).coeff 4 = -(m * ν ^ 2 / 6) :=
      lagPoly_coeff_four σ₀ σd₀ m δ₀ ν
    have hc4ne : (lagPoly σ₀ σd₀ m δ₀ ν).coeff 4 ≠ 0 := by
      intro h0
      rw [hc4] at h0
      have : m * ν ^ 2 = 0 := by
        field_simp at h0
        linarith
      exact hν (sq_eq_zero_iff.mp ((mul_eq_zero.mp this).resolve_left hm.ne'))
    have hnat : (lagPoly σ₀ σd₀ m δ₀ ν).natDegree = 4 :=
      le_antisymm (lagPoly_natDegree_le σ₀ σd₀ m δ₀ ν) (le_natDegree_of_ne_zero hc4ne)
    have hlead : (lagPoly σ₀ σd₀ m δ₀ ν).leadingCoeff ≤ 0 := by
      rw [leadingCoeff, hnat, hc4]
      have : 0 ≤ m * ν ^ 2 / 6 := by positivity
      linarith
    exact tendsto_eval_of_natDegree hnat (by decide) hlead

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
    have hc1 : (sigmaPoly σ₀ σd₀ m δ₀ ν).coeff 1 = 0 :=
      coeff_eq_zero_of_natDegree_lt (Nat.lt_of_le_of_lt hnat (by decide))
    have hc2 : (sigmaPoly σ₀ σd₀ m δ₀ ν).coeff 2 = 0 :=
      coeff_eq_zero_of_natDegree_lt (Nat.lt_of_le_of_lt hnat (by decide))
    have hc3 : (sigmaPoly σ₀ σd₀ m δ₀ ν).coeff 3 = 0 :=
      coeff_eq_zero_of_natDegree_lt (Nat.lt_of_le_of_lt hnat (by decide))
    rw [sigmaPoly_coeff_three] at hc3
    rw [sigmaPoly_coeff_two] at hc2
    rw [sigmaPoly_coeff_one] at hc1
    have hν : ν = 0 := by
      have hmul : m * ν = 0 := by
        field_simp at hc3
        linarith
      exact (mul_eq_zero.mp hmul).resolve_left hm.ne'
    have hδ : δ₀ = 0 := by
      exact (mul_eq_zero.mp (neg_eq_zero.mp hc2)).resolve_left hm.ne'
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
