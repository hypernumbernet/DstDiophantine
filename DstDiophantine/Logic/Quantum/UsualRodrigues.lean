import DstDiophantine.Logic.Quantum.DualSector
import DstDiophantine.Algebra.PGA.Normed
import DstDiophantine.Algebra.Motor
import DstDiophantine.Algebra.Generators
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

/-!
# Usual-sector Rodrigues formula in \(G(3,1,1)\)

For a pure usual rapidity \(\alpha\), the torsion bivector is the hyperbolic
combination \(\Gamma^+(\alpha)=\sum\alpha_a B^+_a\). Distinct hyperbolic
generators anticommute and each squares to \(+1\), so
\(\Gamma^+(\alpha)^2=\lVert\alpha\rVert^2\) and the Banach exponential
collapses to the hyperbolic Rodrigues formula. Mixed usual/dual generators
are not identified with a matrix exponential here.
-/

namespace DstDiophantine

namespace Logic

open PGA Generators Motor CliffordAlgebra NormedSpace

/-- Hyperbolic combination \(\Gamma^+(\alpha)=\sum_a\alpha_a B^+_a\). -/
noncomputable def hyperbolicComb (α : UsualRapidity) : PGA :=
  ∑ a : Fin 3, (α a) • hyperbolic a

theorem hyperbolicComb_zero : hyperbolicComb 0 = 0 := by
  simp [hyperbolicComb]

private theorem smul_mul_smul (c d : ℝ) (u v : PGA) :
    (c • u) * (d • v) = (c * d) • (u * v) := by
  rw [mul_smul_comm, smul_mul_assoc, smul_smul, mul_comm d c]

private theorem e0_sq_neg_one : ι 0 * ι 0 = (-1 : PGA) := by
  rw [e0_sq, map_neg, map_one]

/-- `B⁺₀ B⁺₁ = e₁ e₂`. -/
private theorem mul_hyperbolic0_hyperbolic1 :
    hyperbolic 0 * hyperbolic 1 = ι 1 * ι 2 := by
  dsimp [hyperbolic]
  have h10 : ι 1 * ι 0 = -(ι 0 * ι 1) := e_mul_anticomm (by decide)
  calc (ι 0 * ι 1) * (ι 0 * ι 2)
      = ι 0 * (ι 1 * ι 0) * ι 2 := by simp [mul_assoc]
    _ = ι 0 * (-(ι 0 * ι 1)) * ι 2 := by rw [h10]
    _ = -(ι 0 * ι 0) * (ι 1 * ι 2) := by simp [mul_neg, mul_assoc]
    _ = -(-1) * (ι 1 * ι 2) := by rw [e0_sq_neg_one]
    _ = ι 1 * ι 2 := by simp

/-- `B⁺₁ B⁺₀ = e₂ e₁`. -/
private theorem mul_hyperbolic1_hyperbolic0 :
    hyperbolic 1 * hyperbolic 0 = ι 2 * ι 1 := by
  dsimp [hyperbolic]
  have h20 : ι 2 * ι 0 = -(ι 0 * ι 2) := e_mul_anticomm (by decide)
  calc (ι 0 * ι 2) * (ι 0 * ι 1)
      = ι 0 * (ι 2 * ι 0) * ι 1 := by simp [mul_assoc]
    _ = ι 0 * (-(ι 0 * ι 2)) * ι 1 := by rw [h20]
    _ = -(ι 0 * ι 0) * (ι 2 * ι 1) := by simp [mul_neg, mul_assoc]
    _ = -(-1) * (ι 2 * ι 1) := by rw [e0_sq_neg_one]
    _ = ι 2 * ι 1 := by simp

/-- `B⁺₀ B⁺₂ = e₁ e₃`. -/
private theorem mul_hyperbolic0_hyperbolic2 :
    hyperbolic 0 * hyperbolic 2 = ι 1 * ι 3 := by
  dsimp [hyperbolic]
  have h10 : ι 1 * ι 0 = -(ι 0 * ι 1) := e_mul_anticomm (by decide)
  calc (ι 0 * ι 1) * (ι 0 * ι 3)
      = ι 0 * (ι 1 * ι 0) * ι 3 := by simp [mul_assoc]
    _ = ι 0 * (-(ι 0 * ι 1)) * ι 3 := by rw [h10]
    _ = -(ι 0 * ι 0) * (ι 1 * ι 3) := by simp [mul_neg, mul_assoc]
    _ = -(-1) * (ι 1 * ι 3) := by rw [e0_sq_neg_one]
    _ = ι 1 * ι 3 := by simp

/-- `B⁺₂ B⁺₀ = e₃ e₁`. -/
private theorem mul_hyperbolic2_hyperbolic0 :
    hyperbolic 2 * hyperbolic 0 = ι 3 * ι 1 := by
  dsimp [hyperbolic]
  have h30 : ι 3 * ι 0 = -(ι 0 * ι 3) := e_mul_anticomm (by decide)
  calc (ι 0 * ι 3) * (ι 0 * ι 1)
      = ι 0 * (ι 3 * ι 0) * ι 1 := by simp [mul_assoc]
    _ = ι 0 * (-(ι 0 * ι 3)) * ι 1 := by rw [h30]
    _ = -(ι 0 * ι 0) * (ι 3 * ι 1) := by simp [mul_neg, mul_assoc]
    _ = -(-1) * (ι 3 * ι 1) := by rw [e0_sq_neg_one]
    _ = ι 3 * ι 1 := by simp

/-- `B⁺₁ B⁺₂ = e₂ e₃`. -/
private theorem mul_hyperbolic1_hyperbolic2 :
    hyperbolic 1 * hyperbolic 2 = ι 2 * ι 3 := by
  dsimp [hyperbolic]
  have h20 : ι 2 * ι 0 = -(ι 0 * ι 2) := e_mul_anticomm (by decide)
  calc (ι 0 * ι 2) * (ι 0 * ι 3)
      = ι 0 * (ι 2 * ι 0) * ι 3 := by simp [mul_assoc]
    _ = ι 0 * (-(ι 0 * ι 2)) * ι 3 := by rw [h20]
    _ = -(ι 0 * ι 0) * (ι 2 * ι 3) := by simp [mul_neg, mul_assoc]
    _ = -(-1) * (ι 2 * ι 3) := by rw [e0_sq_neg_one]
    _ = ι 2 * ι 3 := by simp

/-- `B⁺₂ B⁺₁ = e₃ e₂`. -/
private theorem mul_hyperbolic2_hyperbolic1 :
    hyperbolic 2 * hyperbolic 1 = ι 3 * ι 2 := by
  dsimp [hyperbolic]
  have h30 : ι 3 * ι 0 = -(ι 0 * ι 3) := e_mul_anticomm (by decide)
  calc (ι 0 * ι 3) * (ι 0 * ι 2)
      = ι 0 * (ι 3 * ι 0) * ι 2 := by simp [mul_assoc]
    _ = ι 0 * (-(ι 0 * ι 3)) * ι 2 := by rw [h30]
    _ = -(ι 0 * ι 0) * (ι 3 * ι 2) := by simp [mul_neg, mul_assoc]
    _ = -(-1) * (ι 3 * ι 2) := by rw [e0_sq_neg_one]
    _ = ι 3 * ι 2 := by simp

/-- Distinct hyperbolic generators anticommute. -/
theorem hyperbolic_anticomm {a b : Fin 3} (h : a ≠ b) :
    hyperbolic a * hyperbolic b + hyperbolic b * hyperbolic a = 0 := by
  fin_cases a <;> fin_cases b <;> try contradiction
  · simp [mul_hyperbolic0_hyperbolic1, mul_hyperbolic1_hyperbolic0]
    exact e_anticomm (by decide : (1 : Fin 5) ≠ 2)
  · simp [mul_hyperbolic0_hyperbolic2, mul_hyperbolic2_hyperbolic0]
    exact e_anticomm (by decide : (1 : Fin 5) ≠ 3)
  · simp [mul_hyperbolic1_hyperbolic0, mul_hyperbolic0_hyperbolic1]
    exact e_anticomm (by decide : (2 : Fin 5) ≠ 1)
  · simp [mul_hyperbolic1_hyperbolic2, mul_hyperbolic2_hyperbolic1]
    exact e_anticomm (by decide : (2 : Fin 5) ≠ 3)
  · simp [mul_hyperbolic2_hyperbolic0, mul_hyperbolic0_hyperbolic2]
    exact e_anticomm (by decide : (3 : Fin 5) ≠ 1)
  · simp [mul_hyperbolic2_hyperbolic1, mul_hyperbolic1_hyperbolic2]
    exact e_anticomm (by decide : (3 : Fin 5) ≠ 2)

private theorem hyperbolicComb_sq_expand (α : UsualRapidity) :
    hyperbolicComb α * hyperbolicComb α =
      (α 0 * α 0) • (hyperbolic 0 * hyperbolic 0) +
        (α 1 * α 1) • (hyperbolic 1 * hyperbolic 1) +
          (α 2 * α 2) • (hyperbolic 2 * hyperbolic 2) +
            (α 0 * α 1) • (hyperbolic 0 * hyperbolic 1) +
              (α 1 * α 0) • (hyperbolic 1 * hyperbolic 0) +
                (α 0 * α 2) • (hyperbolic 0 * hyperbolic 2) +
                  (α 2 * α 0) • (hyperbolic 2 * hyperbolic 0) +
                    (α 1 * α 2) • (hyperbolic 1 * hyperbolic 2) +
                      (α 2 * α 1) • (hyperbolic 2 * hyperbolic 1) := by
  simp only [hyperbolicComb, Fin.sum_univ_three, mul_add, add_mul, smul_mul_smul]
  abel

/-- \(\Gamma^+(\alpha)^2 = \lVert\alpha\rVert^2\). -/
theorem hyperbolicComb_sq (α : UsualRapidity) :
    hyperbolicComb α * hyperbolicComb α = (‖α‖ ^ 2) • (1 : PGA) := by
  have hnorm : ‖α‖ ^ 2 = (α 0) ^ 2 + (α 1) ^ 2 + (α 2) ^ 2 := by
    have h1 := (real_inner_self_eq_norm_sq (F := UsualRapidity) α).symm
    have h2 : inner ℝ α α = (α 0) ^ 2 + (α 1) ^ 2 + (α 2) ^ 2 := by
      simp [inner, Fin.sum_univ_three, sq]
    exact h1.trans h2
  have hcross01 :
      (α 0 * α 1) • (hyperbolic 0 * hyperbolic 1) +
        (α 1 * α 0) • (hyperbolic 1 * hyperbolic 0) = 0 := by
    have : hyperbolic 1 * hyperbolic 0 = -(hyperbolic 0 * hyperbolic 1) :=
      eq_neg_of_add_eq_zero_right (hyperbolic_anticomm (by decide : (0 : Fin 3) ≠ 1))
    rw [this, smul_neg, mul_comm (α 1) (α 0)]
    abel
  have hcross02 :
      (α 0 * α 2) • (hyperbolic 0 * hyperbolic 2) +
        (α 2 * α 0) • (hyperbolic 2 * hyperbolic 0) = 0 := by
    have : hyperbolic 2 * hyperbolic 0 = -(hyperbolic 0 * hyperbolic 2) :=
      eq_neg_of_add_eq_zero_right (hyperbolic_anticomm (by decide : (0 : Fin 3) ≠ 2))
    rw [this, smul_neg, mul_comm (α 2) (α 0)]
    abel
  have hcross12 :
      (α 1 * α 2) • (hyperbolic 1 * hyperbolic 2) +
        (α 2 * α 1) • (hyperbolic 2 * hyperbolic 1) = 0 := by
    have : hyperbolic 2 * hyperbolic 1 = -(hyperbolic 1 * hyperbolic 2) :=
      eq_neg_of_add_eq_zero_right (hyperbolic_anticomm (by decide : (1 : Fin 3) ≠ 2))
    rw [this, smul_neg, mul_comm (α 2) (α 1)]
    abel
  have hdiag :
      (α 0 * α 0) • (hyperbolic 0 * hyperbolic 0) +
        (α 1 * α 1) • (hyperbolic 1 * hyperbolic 1) +
          (α 2 * α 2) • (hyperbolic 2 * hyperbolic 2) =
        ((α 0) ^ 2 + (α 1) ^ 2 + (α 2) ^ 2) • (1 : PGA) := by
    simp only [hyperbolic_sq, sq]
    simp [add_smul]
  have hsum := hyperbolicComb_sq_expand α
  have hgroup :
      hyperbolicComb α * hyperbolicComb α =
        ((α 0 * α 0) • (hyperbolic 0 * hyperbolic 0) +
            (α 1 * α 1) • (hyperbolic 1 * hyperbolic 1) +
              (α 2 * α 2) • (hyperbolic 2 * hyperbolic 2)) +
          (((α 0 * α 1) • (hyperbolic 0 * hyperbolic 1) +
              (α 1 * α 0) • (hyperbolic 1 * hyperbolic 0)) +
            ((α 0 * α 2) • (hyperbolic 0 * hyperbolic 2) +
                (α 2 * α 0) • (hyperbolic 2 * hyperbolic 0)) +
              ((α 1 * α 2) • (hyperbolic 1 * hyperbolic 2) +
                (α 2 * α 1) • (hyperbolic 2 * hyperbolic 1))) := by
    rw [hsum]
    abel
  rw [hgroup, hcross01, hcross02, hcross12, add_zero, add_zero, add_zero, hdiag, hnorm]

/-- Pure usual torsion bivector is the hyperbolic combination of the usual rapidity. -/
theorem omegaTorsion_ofUsual (α : UsualRapidity) :
    omegaTorsion (ofUsual α) = ∑ a : Fin 3, (α a / 2) • hyperbolic a := by
  simp [omegaTorsion, ofUsual]

theorem omegaTorsion_ofUsual_hyperbolicComb (α : UsualRapidity) :
    omegaTorsion (ofUsual α) = (1 / 2 : ℝ) • hyperbolicComb α := by
  rw [omegaTorsion_ofUsual]
  simp only [hyperbolicComb, Fin.sum_univ_three, smul_add, smul_smul]
  ring_nf

theorem omegaTorsion_ofUsual_axis0 (θ : ℝ) :
    omegaTorsion (ofUsual (EuclideanSpace.single 0 θ)) = (θ / 2) • hyperbolic 0 := by
  rw [omegaTorsion_ofUsual]
  simp [PiLp.single_apply, Fin.sum_univ_three]

/-- Unit hyperbolic combination of a nonzero usual rapidity. Squares to \(+1\). -/
noncomputable def hyperbolicUnit (α : UsualRapidity) (_h : α ≠ 0) : PGA :=
  (1 / ‖α‖) • hyperbolicComb α

theorem hyperbolicUnit_sq {α : UsualRapidity} (h : α ≠ 0) :
    hyperbolicUnit α h * hyperbolicUnit α h = 1 := by
  have hr : ‖α‖ ≠ 0 := norm_ne_zero_iff.mpr h
  unfold hyperbolicUnit
  rw [smul_mul_smul, hyperbolicComb_sq, smul_smul]
  have : (1 / ‖α‖ * (1 / ‖α‖) * (‖α‖ ^ 2)) = (1 : ℝ) := by
    field_simp [hr]
  rw [this, one_smul]

theorem omegaTorsion_ofUsual_unit {α : UsualRapidity} (h : α ≠ 0) :
    omegaTorsion (ofUsual α) = (‖α‖ / 2) • hyperbolicUnit α h := by
  have hr : ‖α‖ ≠ 0 := norm_ne_zero_iff.mpr h
  rw [omegaTorsion_ofUsual_hyperbolicComb]
  unfold hyperbolicUnit
  simp [smul_smul]
  field_simp [hr]

/-- Usual-sector Banach exponential is the hyperbolic Rodrigues formula. -/
theorem rotorTorsion_ofUsual (α : UsualRapidity) :
    rotorTorsion (ofUsual α) =
      Real.cosh (‖α‖ / 2) • (1 : PGA) +
        (if h : α = 0 then (0 : PGA)
          else Real.sinh (‖α‖ / 2) • hyperbolicUnit α h) := by
  by_cases h : α = 0
  · subst h
    simp [rotorTorsion, omegaTorsion_ofUsual, Real.cosh_zero]
  · rw [rotorTorsion, omegaTorsion_ofUsual_unit h]
    simp only [h, ↓reduceDIte]
    exact exp_of_sq_one (hyperbolicUnit_sq h) (‖α‖ / 2)

/-- Axis-0 usual rotor: \(\cosh(\theta/2)\,I+\sinh(\theta/2)\,B^+_0\). -/
theorem rotorTorsion_ofUsual_axis0 (θ : ℝ) :
    rotorTorsion (ofUsual (EuclideanSpace.single 0 θ)) =
      Real.cosh (θ / 2) • (1 : PGA) + Real.sinh (θ / 2) • hyperbolic 0 := by
  rw [rotorTorsion, omegaTorsion_ofUsual_axis0]
  exact exp_of_sq_one (hyperbolic_sq 0) (θ / 2)

/-- Closed form along the (possibly zero) hyperbolic combination. -/
theorem rotorTorsion_ofUsual_comb (α : UsualRapidity) :
    rotorTorsion (ofUsual α) =
      Real.cosh (‖α‖ / 2) • (1 : PGA) +
        (if ‖α‖ = 0 then (0 : PGA)
          else (Real.sinh (‖α‖ / 2) / ‖α‖) • hyperbolicComb α) := by
  rw [rotorTorsion_ofUsual]
  by_cases h : α = 0
  · subst h
    simp
  · have hr : ‖α‖ ≠ 0 := norm_ne_zero_iff.mpr h
    simp only [h, ↓reduceDIte, hr, ↓reduceIte, hyperbolicUnit, smul_smul]
    field_simp [hr]

end Logic

end DstDiophantine
