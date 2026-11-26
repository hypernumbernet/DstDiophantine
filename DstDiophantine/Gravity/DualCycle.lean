import DstDiophantine.Algebra.Admissible
import DstDiophantine.Algebra.Invariant
import DstDiophantine.Algebra.Generators
import DstDiophantine.Algebra.RelativeRotor
import DstDiophantine.Gravity.DualRotorFlow
import DstDiophantine.Logic.Quantum.DualRodrigues
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The expressed dual rotor does not complete a cycle

On an admissible configuration the dual half-angle is at most `π √3 / 4`, strictly below `π/2`.
The dual rotor therefore has positive scalar part: it is the identity only when every dual
rapidity vanishes, and it is never `-1`. Negating the dual rapidities reverses the rotor and
leaves `J` unchanged, and it leaves the cone whenever a dual rapidity was positive. A unit lag
rate of the written action, at vanishing stiffness, puts the dual coordinate at `-t/2` and
leaves the cone before that coordinate can reach the antipodal rapidity `2π`. No acceleration
ceiling is read off a `4π` wrap.
-/

namespace DstDiophantine

namespace Gravity

open Operations Admissible Invariant RelativeRotor Logic Generators Motor
open CliffordAlgebra NormedSpace Real

/-! ### Half-angle bound -/

theorem toDual_coord (p : TorsionParams) (a : Fin 3) : toDual p a = p.beta a := by
  simp [toDual]

theorem toDual_norm_sq (p : TorsionParams) :
    ‖toDual p‖ ^ 2 = (p.beta 0) ^ 2 + (p.beta 1) ^ 2 + (p.beta 2) ^ 2 := by
  have h1 := (real_inner_self_eq_norm_sq (F := DualRapidity) (toDual p)).symm
  have h2 : inner ℝ (toDual p) (toDual p) =
      (toDual p 0) ^ 2 + (toDual p 1) ^ 2 + (toDual p 2) ^ 2 := by
    simp [inner, Fin.sum_univ_three, sq]
  rw [h1, h2, toDual_coord, toDual_coord, toDual_coord]

theorem admissible_beta_sq_le (p : TorsionParams) (h : IsAdmissibleContinuous p) (a : Fin 3) :
    (p.beta a) ^ 2 ≤ (Real.pi / 2) ^ 2 := by
  exact pow_le_pow_left₀ (admissibleContinuous_beta_nonneg p h a)
    (admissibleContinuous_beta_le_half_pi p h a) 2

theorem admissible_dual_norm_sq_le (p : TorsionParams) (h : IsAdmissibleContinuous p) :
    ‖toDual p‖ ^ 2 ≤ 3 * (Real.pi / 2) ^ 2 := by
  rw [toDual_norm_sq]
  have h0 := admissible_beta_sq_le p h 0
  have h1 := admissible_beta_sq_le p h 1
  have h2 := admissible_beta_sq_le p h 2
  linarith

/-- Ceiling `π √3 / 4` on the dual half-angle. It lies strictly below `π/2`. -/
theorem dualHalfAngle_ceiling_lt_half_pi :
    Real.pi * Real.sqrt 3 / 4 < Real.pi / 2 := by
  have hsq : (Real.sqrt 3) ^ 2 < (2 : ℝ) ^ 2 := by
    rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 3)]
    norm_num
  have hsqrt : Real.sqrt 3 < 2 := by
    have hne : |Real.sqrt 3| < |(2 : ℝ)| := (sq_lt_sq).mp hsq
    simpa [abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] using hne
  nlinarith [Real.pi_pos, hsqrt]

theorem admissible_dual_halfAngle_le (p : TorsionParams) (h : IsAdmissibleContinuous p) :
    ‖toDual p‖ / 2 ≤ Real.pi * Real.sqrt 3 / 4 := by
  have hnn : 0 ≤ Real.sqrt 3 * (Real.pi / 2) := by positivity
  have hsq : ‖toDual p‖ ^ 2 ≤ (Real.sqrt 3 * (Real.pi / 2)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 3)]
    exact admissible_dual_norm_sq_le p h
  have hle : ‖toDual p‖ ≤ Real.sqrt 3 * (Real.pi / 2) := by
    have hdiff :
        0 ≤ (Real.sqrt 3 * (Real.pi / 2) - ‖toDual p‖) *
          (Real.sqrt 3 * (Real.pi / 2) + ‖toDual p‖) := by
      have : 0 ≤ (Real.sqrt 3 * (Real.pi / 2)) ^ 2 - ‖toDual p‖ ^ 2 := by linarith
      convert this using 1
      ring
    have hsum : 0 < Real.sqrt 3 * (Real.pi / 2) + ‖toDual p‖ := by
      have : 0 < Real.sqrt 3 * (Real.pi / 2) := by positivity
      linarith [norm_nonneg (toDual p)]
    have hsub : 0 ≤ Real.sqrt 3 * (Real.pi / 2) - ‖toDual p‖ :=
      (mul_nonneg_iff_of_pos_right hsum).mp hdiff
    linarith
  have hdiv : ‖toDual p‖ / 2 ≤ (Real.sqrt 3 * (Real.pi / 2)) / 2 := by
    gcongr
  have hform : (Real.sqrt 3 * (Real.pi / 2)) / 2 = Real.pi * Real.sqrt 3 / 4 := by ring
  rw [hform] at hdiv
  exact hdiv

theorem admissible_dual_halfAngle_lt_half_pi (p : TorsionParams) (h : IsAdmissibleContinuous p) :
    ‖toDual p‖ / 2 < Real.pi / 2 :=
  lt_of_le_of_lt (admissible_dual_halfAngle_le p h) dualHalfAngle_ceiling_lt_half_pi

theorem admissible_dual_cos_pos (p : TorsionParams) (h : IsAdmissibleContinuous p) :
    0 < Real.cos (‖toDual p‖ / 2) := by
  have hr0 : -(Real.pi / 2) < ‖toDual p‖ / 2 := by
    have : 0 ≤ ‖toDual p‖ / 2 := by positivity
    linarith [Real.pi_pos]
  exact Real.cos_pos_of_mem_Ioo ⟨hr0, admissible_dual_halfAngle_lt_half_pi p h⟩

/-! ### Scalar part of the dual rotor -/

theorem omegaUsual_ofDual (β : DualRapidity) : omegaUsual (ofDual β) = 0 := by
  simp [omegaUsual, ofDual]

theorem omegaDual_of_toDual (p : TorsionParams) :
    omegaDual (ofDual (toDual p)) = omegaDual p := by
  unfold omegaDual
  congr 1

theorem rotorDual_eq_rotorTorsion_ofDual (p : TorsionParams) :
    rotorDual p = rotorTorsion (ofDual (toDual p)) := by
  rw [rotorDual, rotorTorsion, omegaTorsion_eq_add, omegaUsual_ofDual, zero_add,
    omegaDual_of_toDual]

theorem reverse_cyclicComb (β : DualRapidity) :
    reverse (cyclicComb β) = -cyclicComb β := by
  simp only [cyclicComb, map_sum, map_smul, cyclic_reverse, smul_neg]
  rw [← Finset.sum_neg_distrib]

theorem rotorDual_add_reverse (p : TorsionParams) :
    rotorDual p + reverse (rotorDual p) =
      (2 * Real.cos (‖toDual p‖ / 2)) • (1 : PGA) := by
  rw [rotorDual_eq_rotorTorsion_ofDual, rotorTorsion_ofDual_comb]
  set β : DualRapidity := toDual p
  by_cases hβ : ‖β‖ = 0
  · simp [hβ, zero_div, Real.cos_zero, reverse.map_one, two_smul]
  · have hrev :
        reverse ((Real.sin (‖β‖ / 2) / ‖β‖) • cyclicComb β) =
          -((Real.sin (‖β‖ / 2) / ‖β‖) • cyclicComb β) := by
      rw [map_smul, reverse_cyclicComb, smul_neg]
    simp only [hβ, ↓reduceIte]
    rw [map_add, map_smul, reverse.map_one, hrev]
    module

private theorem scalar_smul_eq {c d : ℝ}
    (h : c • (1 : PGA) = d • (1 : PGA)) : c = d := by
  have hmap : algebraMap ℝ PGA c = algebraMap ℝ PGA d := by
    simpa [Algebra.algebraMap_eq_smul_one] using h
  exact FaithfulSMul.algebraMap_injective (R := ℝ) (A := PGA) hmap

theorem admissible_rotorDual_ne_neg_one (p : TorsionParams) (h : IsAdmissibleContinuous p) :
    rotorDual p ≠ -1 := by
  intro hR
  have hsum := rotorDual_add_reverse p
  rw [hR, map_neg, reverse.map_one] at hsum
  have hsc : (-2 : ℝ) = 2 * Real.cos (‖toDual p‖ / 2) := by
    apply scalar_smul_eq
    convert hsum using 1
    module
  linarith [admissible_dual_cos_pos p h]

theorem admissible_rotorDual_eq_one_iff (p : TorsionParams) (h : IsAdmissibleContinuous p) :
    rotorDual p = 1 ↔ ∀ a, p.beta a = 0 := by
  constructor
  · intro hR
    have hsum := rotorDual_add_reverse p
    rw [hR, reverse.map_one] at hsum
    have hsc : (2 : ℝ) = 2 * Real.cos (‖toDual p‖ / 2) := by
      apply scalar_smul_eq
      convert hsum using 1
      all_goals module
    have hcos : Real.cos (‖toDual p‖ / 2) = 1 := by linarith
    have hr0 : 0 ≤ ‖toDual p‖ / 2 := by positivity
    have hr : ‖toDual p‖ / 2 < Real.pi / 2 := admissible_dual_halfAngle_lt_half_pi p h
    have hzero : ‖toDual p‖ / 2 = 0 :=
      (Real.cos_eq_one_iff_of_lt_of_lt (by linarith [hr0, Real.pi_pos]) (by linarith)).mp hcos
    have hnorm : ‖toDual p‖ = 0 := by linarith
    have hzero : toDual p = 0 := norm_eq_zero.mp hnorm
    intro a
    have : toDual p a = 0 := by simp [hzero]
    simpa [toDual_coord] using this
  · intro hβ
    have hω : omegaDual p = 0 := by
      unfold omegaDual
      simp [hβ]
    simp [rotorDual, hω]

/-! ### Negating the dual rapidities reverses the rotor and preserves `J` -/

/-- Dual rapidities reversed, usual rapidities held. -/
def negDual (p : TorsionParams) : TorsionParams where
  alpha := p.alpha
  beta := fun a => -p.beta a

theorem omegaDual_negDual (p : TorsionParams) :
    omegaDual (negDual p) = -omegaDual p := by
  have hcoeff (c : ℝ) : (-c) / 2 = -(c / 2) := by ring
  unfold omegaDual negDual
  simp only [Fin.sum_univ_three, hcoeff, neg_smul]
  abel

theorem rotorDual_negDual (p : TorsionParams) :
    rotorDual (negDual p) = reverse (rotorDual p) := by
  rw [rotorDual, rotorDual, reverse_exp_of_reverse_neg (omegaDual_reverse p), omegaDual_negDual]

theorem J_negDual (p : TorsionParams) : J (negDual p) = J p := by
  rw [J_coef, J_coef]
  simp [negDual]

theorem negDual_not_admissible_of_pos {p : TorsionParams} {a : Fin 3}
    (h : IsAdmissibleContinuous p) (hβ : 0 < p.beta a) :
    ¬ IsAdmissibleContinuous (negDual p) := by
  intro h'
  have hle : 0 ≤ (negDual p).beta a := admissibleContinuous_beta_nonneg _ h' a
  have hneg : (negDual p).beta a = -p.beta a := rfl
  have h0 : 0 ≤ p.beta a := admissibleContinuous_beta_nonneg p h a
  linarith

/-! ### A positive lag rate leaves the cone short of the antipode -/

theorem written_free_dual (t : ℝ) : writtenDual 0 0 0 0 1 t = -t / 2 := by
  simp [writtenDual, dualFrom, writtenSigma, writtenDelta, cubicRapidity, affineMismatch]

theorem written_free_rate_leaves {t : ℝ} (ht : 0 < t) :
    ¬ IsAdmissibleContinuous
        (axisParams (writtenUsual 0 0 0 0 1 t) (writtenDual 0 0 0 0 1 t)) := by
  intro h
  have hβ := admissibleContinuous_beta_nonneg _ h 0
  have hcoord :
      (axisParams (writtenUsual 0 0 0 0 1 t) (writtenDual 0 0 0 0 1 t)).beta 0 =
        writtenDual 0 0 0 0 1 t := by
    simp [axisParams]
  rw [hcoord, written_free_dual] at hβ
  linarith

/-- The exit at `t = 1` is still short of the rapidity `2π` where the one-axis rotor is `-1`. -/
theorem written_free_rate_exits_short_of_antipode :
    ∃ t : ℝ, 0 < t ∧ |writtenDual 0 0 0 0 1 t| < 2 * Real.pi ∧
      ¬ IsAdmissibleContinuous
          (axisParams (writtenUsual 0 0 0 0 1 t) (writtenDual 0 0 0 0 1 t)) := by
  refine ⟨1, by norm_num, ?_, written_free_rate_leaves (by norm_num)⟩
  rw [written_free_dual]
  have hπ : (2 : ℝ) ≤ Real.pi := Real.two_le_pi
  norm_num
  linarith

end Gravity

end DstDiophantine
