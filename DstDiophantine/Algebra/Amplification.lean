import DstDiophantine.Algebra.Invariant
import DstDiophantine.Algebra.Motor
import DstDiophantine.Algebra.Generators
import Mathlib.Analysis.Normed.Algebra.Exponential

/-!
# Torsional amplification under scaling and rotor powers
-/

namespace DstDiophantine

open Operations Motor Invariant Generators NormedSpace

namespace Amplification

def scaleTorsion (c : ℝ) (p : TorsionParams) : TorsionParams where
  alpha := fun a => c * p.alpha a
  beta := fun a => c * p.beta a

theorem J_scale (c : ℝ) (p : TorsionParams) :
    J (scaleTorsion c p) = c ^ 2 * J p := by
  rw [J_coef, J_coef]
  simp only [scaleTorsion, Fin.sum_univ_three, mul_pow]
  ring_nf

theorem JNormalized_scale (c : ℝ) (p : TorsionParams) :
    JNormalized (scaleTorsion c p) = c ^ 2 * JNormalized p := by
  unfold JNormalized
  rw [J_scale]
  ring_nf

def pureBoost (θ : ℝ) : TorsionParams where
  alpha := fun a => match a with | 0 => θ | _ => 0
  beta := fun _ => 0

theorem omegaTorsion_pureBoost (θ : ℝ) :
    omegaTorsion (pureBoost θ) = (θ / 2) • hyperbolic 0 := by
  simp only [omegaTorsion, pureBoost, Fin.sum_univ_three, div_eq_mul_inv, zero_mul, zero_smul,
    add_zero]

theorem rotorTorsion_pureBoost (θ : ℝ) :
    rotorTorsion (pureBoost θ) = exp ((θ / 2) • hyperbolic 0) := by
  rw [rotorTorsion, omegaTorsion_pureBoost]

theorem pureBoost_scale (θ : ℝ) (p : ℕ) :
    pureBoost (p * θ) = scaleTorsion (p : ℝ) (pureBoost θ) := by
  dsimp [pureBoost, scaleTorsion]
  congr <;> funext a <;> fin_cases a <;> simp

theorem rotorTorsion_pureBoost_pow (θ : ℝ) (p : ℕ) :
    rotorTorsion (pureBoost (p * θ)) = rotorTorsion (pureBoost θ) ^ p := by
  rw [pureBoost_scale, rotorTorsion]
  have hω : omegaTorsion (scaleTorsion (p : ℝ) (pureBoost θ)) =
      (p : ℝ) • ((θ / 2) • hyperbolic 0) := by
    simp only [omegaTorsion, scaleTorsion, pureBoost, Fin.sum_univ_three, zero_smul,
      div_eq_mul_inv, ← smul_smul]
    simp only [add_zero, smul_zero]
  rw [hω, rotorTorsion_pureBoost (θ := θ), ← exp_nsmul (n := p)]
  congr 1

theorem J_pureBoost (θ : ℝ) :
    J (pureBoost θ) = (1 / 2) * θ ^ 2 := by
  rw [J_coef]
  simp only [pureBoost, Fin.sum_univ_three, zero_pow two_ne_zero, sub_zero, mul_zero, add_zero,
    pow_two]

theorem J_pow_amplify (θ : ℝ) (p : ℕ) :
    J (pureBoost (p * θ)) = (p : ℝ) ^ 2 * J (pureBoost θ) := by
  rw [pureBoost_scale, J_scale]

theorem JNormalized_pow_amplify (θ : ℝ) (p : ℕ) :
    JNormalized (pureBoost (p * θ)) = (p : ℝ) ^ 2 * JNormalized (pureBoost θ) := by
  rw [pureBoost_scale, JNormalized_scale]

end Amplification

end DstDiophantine
