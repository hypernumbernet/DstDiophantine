import DstDiophantine.Algebra.Operations
import DstDiophantine.Algebra.PGA.Normed
import Mathlib.Analysis.Normed.Algebra.Exponential

/-!
# Motors, Ω decomposition, and null exponential truncation

The translational exponential truncates at first order because the null sector is
strongly nilpotent (`N_μ N_ν = 0`). Torsion rotors use the Banach-algebra exponential.
-/

namespace DstDiophantine

open CliffordAlgebra PGA Generators Operations NormedSpace

namespace Motor

structure TransParams where
  lambda : Fin 4 → ℝ

structure OmegaParams where
  torsion : TorsionParams
  trans : TransParams

/-- Torsion part `Ω_torsion = ∑ (αₐ/2) B⁺ₐ + (βₐ/2) B⁻ₐ`. -/
noncomputable def omegaTorsion (p : TorsionParams) : PGA :=
  ∑ a : Fin 3, ((p.alpha a / 2) • hyperbolic a + (p.beta a / 2) • cyclic a)

/-- Translational part `Ω_trans = ∑ (λ^μ/2) N_μ`. -/
noncomputable def omegaTrans (p : TransParams) : PGA :=
  ∑ μ : Fin 4, (p.lambda μ / 2) • null μ

/-- Full five-dimensional bivector generator `Ω_biv⁽⁵⁾`. -/
noncomputable def omegaBiv (p : OmegaParams) : PGA :=
  omegaTorsion p.torsion + omegaTrans p.trans

theorem omegaTorsion_reverse (p : TorsionParams) :
    reverse (omegaTorsion p) = -omegaTorsion p := by
  simp only [omegaTorsion, map_sum, map_smul, map_add, hyperbolic_reverse, cyclic_reverse]
  rw [← Finset.sum_neg_distrib]
  congr 1
  ext a
  simp [neg_add_rev, add_comm]

/-- Helper for the deferred `reverse_exp_of_reverse_neg` proof. -/
theorem reverse_pow (x : PGA) (n : ℕ) : reverse (x ^ n) = (reverse x) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, CliffordAlgebra.reverse.map_mul, ih, pow_succ (reverse x)]
    exact (Commute.pow_right (Commute.refl (reverse x)) n).eq

theorem reverse_pow_of_reverse_neg (x : PGA) (hx : reverse x = -x) (n : ℕ) :
    reverse (x ^ n) = (-x) ^ n := by
  rw [reverse_pow, hx]

theorem omegaTrans_sq (p : TransParams) : omegaTrans p * omegaTrans p = 0 := by
  simp [omegaTrans, Finset.sum_mul_sum, null_mul_null]

theorem omegaTrans_mul (p q : TransParams) : omegaTrans p * omegaTrans q = 0 := by
  simp [omegaTrans, Finset.sum_mul_sum, null_mul_null]

theorem omegaTrans_add (p q : TransParams) :
    omegaTrans p + omegaTrans q = omegaTrans ⟨fun μ => p.lambda μ + q.lambda μ⟩ := by
  simp only [omegaTrans, Finset.sum_add_distrib, add_smul, add_div]

/-- First-order null exponential: `exp(Ω_trans) = 1 + Ω_trans`. -/
noncomputable def expTrans (p : TransParams) : PGA :=
  1 + omegaTrans p

theorem expTrans_eq (p : TransParams) :
    expTrans p = 1 + omegaTrans p := rfl

/-- Torsion rotor `R = exp(Ω_torsion)`. -/
noncomputable def rotorTorsion (p : TorsionParams) : PGA :=
  exp (omegaTorsion p)

/-- `reverse(exp x) = exp(-x)` when `reverse x = -x`. -/
theorem reverse_exp_of_reverse_neg {x : PGA} (hx : reverse x = -x) :
    reverse (exp x) = exp (-x) := by
  set revOp := CliffordAlgebra.reverseOp (Q := Q311)
  have hcont : Continuous revOp := revOp.toLinearMap.continuous_of_finiteDimensional
  calc
    reverse (exp x) = (revOp (exp x)).unop :=
      (CliffordAlgebra.unop_reverseOp (Q := Q311) (exp x)).symm
    _ = (exp (revOp x)).unop := by rw [map_exp revOp hcont]
    _ = (exp (MulOpposite.op (reverse x))).unop := by rw [CliffordAlgebra.op_reverse (Q := Q311)]
    _ = (exp (MulOpposite.op (-x))).unop := by rw [hx]
    _ = exp (-x) := by rw [← MulOpposite.unop_op (exp (-x)), ← exp_op (-x)]

theorem rotor_unitary (p : TorsionParams) :
    rotorTorsion p * reverse (rotorTorsion p) = 1 := by
  dsimp [rotorTorsion]
  rw [reverse_exp_of_reverse_neg (omegaTorsion_reverse p)]
  rw [← exp_add_of_commute (Commute.neg_right (Commute.refl (omegaTorsion p)))]
  simp

/-- Motor split `M = R · T` at the definition level. -/
noncomputable def motor (p : OmegaParams) : PGA :=
  rotorTorsion p.torsion * expTrans p.trans

/-- Null translator is unitary: `(1+Ω_trans)(1+Ω_trans)˜ = 1`. -/
theorem expTrans_unitary (p : TransParams) :
    expTrans p * reverse (expTrans p) = 1 := by
  have hrev : reverse (omegaTrans p) = -omegaTrans p := by
    simp only [omegaTrans, map_sum, map_smul, null_reverse]
    rw [← Finset.sum_neg_distrib]
    congr 1
    ext μ
    rw [smul_neg]
  simp [expTrans, CliffordAlgebra.reverse.map_add, CliffordAlgebra.reverse.map_one, hrev,
    mul_add, add_mul, omegaTrans_sq, mul_neg]

theorem motor_unitary (p : OmegaParams) :
    motor p * reverse (motor p) = 1 := by
  simp only [motor, CliffordAlgebra.reverse.map_mul]
  calc
    rotorTorsion p.torsion * expTrans p.trans *
        (reverse (expTrans p.trans) * reverse (rotorTorsion p.torsion))
        = rotorTorsion p.torsion * (expTrans p.trans * reverse (expTrans p.trans)) *
            reverse (rotorTorsion p.torsion) := by
              rw [← mul_assoc, mul_assoc (rotorTorsion p.torsion) (expTrans p.trans)
                (reverse (expTrans p.trans))]
    _ = rotorTorsion p.torsion * reverse (rotorTorsion p.torsion) := by
              rw [expTrans_unitary, mul_one]
    _ = 1 := rotor_unitary p.torsion

theorem motor_factorization (p : OmegaParams) :
    motor p = rotorTorsion p.torsion * expTrans p.trans := rfl

end Motor

end DstDiophantine
