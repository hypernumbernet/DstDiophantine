import DstDiophantine.Logic.Quantum.Quaternion
import DstDiophantine.Algebra.PGA.Normed
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

/-!
# Dual-sector Rodrigues formula in \(G(3,1,1)\)

For a pure dual rapidity \(\beta\), the torsion bivector is the cyclic
combination \(\Gamma(\beta)=\sum\beta_a\Gamma_a\). The quaternion table
gives \(\Gamma(\beta)^2=-\lVert\beta\rVert^2\), so the Banach exponential
collapses to the Rodrigues formula. Mixed usual/dual generators are not
identified with a matrix exponential here.
-/

namespace DstDiophantine

namespace Logic

open PGA Generators Motor CliffordAlgebra NormedSpace

/-- Cyclic combination \(\Gamma(\beta)=\sum_a\beta_a\Gamma_a\). -/
noncomputable def cyclicComb (β : DualRapidity) : PGA :=
  ∑ a : Fin 3, (β a) • cyclic a

theorem cyclicComb_zero : cyclicComb 0 = 0 := by
  simp [cyclicComb]

private theorem smul_mul_smul (c d : ℝ) (u v : PGA) :
    (c • u) * (d • v) = (c * d) • (u * v) := by
  rw [mul_smul_comm, smul_mul_assoc, smul_smul, mul_comm d c]

/-- Distinct cyclic generators anticommute. -/
theorem cyclic_anticomm {a b : Fin 3} (h : a ≠ b) :
    cyclic a * cyclic b + cyclic b * cyclic a = 0 := by
  fin_cases a <;> fin_cases b <;> try contradiction
  · simp [cyclic_zero_mul_one, cyclic_one_mul_zero]
  · simp [cyclic_zero_mul_two, cyclic_two_mul_zero]
  · simp [cyclic_one_mul_zero, cyclic_zero_mul_one]
  · simp [cyclic_one_mul_two, cyclic_two_mul_one]
  · simp [cyclic_two_mul_zero, cyclic_zero_mul_two]
  · simp [cyclic_two_mul_one, cyclic_one_mul_two]

private theorem cyclicComb_sq_expand (β : DualRapidity) :
    cyclicComb β * cyclicComb β =
      (β 0 * β 0) • (cyclic 0 * cyclic 0) +
        (β 1 * β 1) • (cyclic 1 * cyclic 1) +
          (β 2 * β 2) • (cyclic 2 * cyclic 2) +
            (β 0 * β 1) • (cyclic 0 * cyclic 1) +
              (β 1 * β 0) • (cyclic 1 * cyclic 0) +
                (β 0 * β 2) • (cyclic 0 * cyclic 2) +
                  (β 2 * β 0) • (cyclic 2 * cyclic 0) +
                    (β 1 * β 2) • (cyclic 1 * cyclic 2) +
                      (β 2 * β 1) • (cyclic 2 * cyclic 1) := by
  simp only [cyclicComb, Fin.sum_univ_three, mul_add, add_mul, smul_mul_smul]
  abel

/-- \(\Gamma(\beta)^2 = -\lVert\beta\rVert^2\). -/
theorem cyclicComb_sq (β : DualRapidity) :
    cyclicComb β * cyclicComb β = (-(‖β‖ ^ 2)) • (1 : PGA) := by
  have hnorm : ‖β‖ ^ 2 = (β 0) ^ 2 + (β 1) ^ 2 + (β 2) ^ 2 := by
    have h1 := (real_inner_self_eq_norm_sq (F := DualRapidity) β).symm
    have h2 : inner ℝ β β = (β 0) ^ 2 + (β 1) ^ 2 + (β 2) ^ 2 := by
      simp [inner, Fin.sum_univ_three, sq]
    exact h1.trans h2
  have hcross01 :
      (β 0 * β 1) • (cyclic 0 * cyclic 1) + (β 1 * β 0) • (cyclic 1 * cyclic 0) = 0 := by
    have : cyclic 1 * cyclic 0 = -(cyclic 0 * cyclic 1) :=
      eq_neg_of_add_eq_zero_right (cyclic_anticomm (by decide : (0 : Fin 3) ≠ 1))
    rw [this, smul_neg, mul_comm (β 1) (β 0)]
    abel
  have hcross02 :
      (β 0 * β 2) • (cyclic 0 * cyclic 2) + (β 2 * β 0) • (cyclic 2 * cyclic 0) = 0 := by
    have : cyclic 2 * cyclic 0 = -(cyclic 0 * cyclic 2) :=
      eq_neg_of_add_eq_zero_right (cyclic_anticomm (by decide : (0 : Fin 3) ≠ 2))
    rw [this, smul_neg, mul_comm (β 2) (β 0)]
    abel
  have hcross12 :
      (β 1 * β 2) • (cyclic 1 * cyclic 2) + (β 2 * β 1) • (cyclic 2 * cyclic 1) = 0 := by
    have : cyclic 2 * cyclic 1 = -(cyclic 1 * cyclic 2) :=
      eq_neg_of_add_eq_zero_right (cyclic_anticomm (by decide : (1 : Fin 3) ≠ 2))
    rw [this, smul_neg, mul_comm (β 2) (β 1)]
    abel
  have hdiag :
      (β 0 * β 0) • (cyclic 0 * cyclic 0) +
        (β 1 * β 1) • (cyclic 1 * cyclic 1) +
          (β 2 * β 2) • (cyclic 2 * cyclic 2) =
        (-((β 0) ^ 2 + (β 1) ^ 2 + (β 2) ^ 2)) • (1 : PGA) := by
    simp only [cyclic_sq, sq]
    simp [smul_neg, add_smul, neg_smul]
    abel
  have hsum := cyclicComb_sq_expand β
  have hgroup :
      cyclicComb β * cyclicComb β =
        ((β 0 * β 0) • (cyclic 0 * cyclic 0) +
            (β 1 * β 1) • (cyclic 1 * cyclic 1) +
              (β 2 * β 2) • (cyclic 2 * cyclic 2)) +
          (((β 0 * β 1) • (cyclic 0 * cyclic 1) +
              (β 1 * β 0) • (cyclic 1 * cyclic 0)) +
            ((β 0 * β 2) • (cyclic 0 * cyclic 2) +
                (β 2 * β 0) • (cyclic 2 * cyclic 0)) +
              ((β 1 * β 2) • (cyclic 1 * cyclic 2) +
                (β 2 * β 1) • (cyclic 2 * cyclic 1))) := by
    rw [hsum]
    abel
  rw [hgroup, hcross01, hcross02, hcross12, add_zero, add_zero, add_zero, hdiag, hnorm]

theorem omegaTorsion_ofDual_cyclicComb (β : DualRapidity) :
    omegaTorsion (ofDual β) = (1 / 2 : ℝ) • cyclicComb β := by
  rw [omegaTorsion_ofDual]
  simp only [cyclicComb, Fin.sum_univ_three, smul_add, smul_smul]
  ring_nf

/-- Unit cyclic combination of a nonzero dual rapidity. Squares to \(-1\). -/
noncomputable def cyclicUnit (β : DualRapidity) (_h : β ≠ 0) : PGA :=
  (1 / ‖β‖) • cyclicComb β

theorem cyclicUnit_sq {β : DualRapidity} (h : β ≠ 0) :
    cyclicUnit β h * cyclicUnit β h = -1 := by
  have hr : ‖β‖ ≠ 0 := norm_ne_zero_iff.mpr h
  unfold cyclicUnit
  rw [smul_mul_smul, cyclicComb_sq, smul_smul]
  have : (1 / ‖β‖ * (1 / ‖β‖) * (-(‖β‖ ^ 2))) = (-1 : ℝ) := by
    field_simp [hr]
  rw [this, neg_smul, one_smul]

theorem omegaTorsion_ofDual_unit {β : DualRapidity} (h : β ≠ 0) :
    omegaTorsion (ofDual β) = (‖β‖ / 2) • cyclicUnit β h := by
  have hr : ‖β‖ ≠ 0 := norm_ne_zero_iff.mpr h
  rw [omegaTorsion_ofDual_cyclicComb]
  unfold cyclicUnit
  simp [smul_smul]
  field_simp [hr]

/-- Dual-sector Banach exponential is the Rodrigues formula. -/
theorem rotorTorsion_ofDual (β : DualRapidity) :
    rotorTorsion (ofDual β) =
      Real.cos (‖β‖ / 2) • (1 : PGA) +
        (if h : β = 0 then (0 : PGA)
          else Real.sin (‖β‖ / 2) • cyclicUnit β h) := by
  by_cases h : β = 0
  · subst h
    simp [rotorTorsion, omegaTorsion_ofDual, Real.cos_zero]
  · rw [rotorTorsion, omegaTorsion_ofDual_unit h]
    simp [h]
    exact exp_of_sq_neg_one (cyclicUnit_sq h) (‖β‖ / 2)

/-- Closed form along the (possibly zero) cyclic combination. -/
theorem rotorTorsion_ofDual_comb (β : DualRapidity) :
    rotorTorsion (ofDual β) =
      Real.cos (‖β‖ / 2) • (1 : PGA) +
        (if ‖β‖ = 0 then (0 : PGA)
          else (Real.sin (‖β‖ / 2) / ‖β‖) • cyclicComb β) := by
  rw [rotorTorsion_ofDual]
  by_cases h : β = 0
  · subst h
    simp
  · have hr : ‖β‖ ≠ 0 := norm_ne_zero_iff.mpr h
    have hnorm : ‖β‖ = 0 ↔ False := iff_false_intro hr
    simp only [h, ↓reduceDIte, hr, ↓reduceIte, cyclicUnit, smul_smul]
    field_simp [hr]

end Logic

end DstDiophantine
