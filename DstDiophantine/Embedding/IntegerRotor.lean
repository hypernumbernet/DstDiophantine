import DstDiophantine.Algebra.Amplification
import DstDiophantine.Algebra.Motor
import DstDiophantine.Algebra.PGA.Normed
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Canonical integer rotors `R(n) = exp(log|n| · iI)`

Multiplicative embedding of nonzero integers into the hyperbolic rotor sector.
-/

namespace DstDiophantine

open CliffordAlgebra PGA Generators Motor Amplification Operations Real NormedSpace

namespace Embedding

/-- Canonical rotor for a nonzero integer: `R(n) = exp(log|n| · B⁺₀)`. -/
noncomputable def integerRotor (n : ℤ) (_hn : n ≠ 0) : PGA :=
  exp ((Real.log (Int.natAbs n)) • hyperbolic 0)

theorem integerRotor_eq_exp (n : ℤ) (hn : n ≠ 0) :
    integerRotor n hn = exp ((Real.log (Int.natAbs n)) • hyperbolic 0) := rfl

theorem integerRotor_eq_of_arg_eq {m k : ℤ} (hm : m ≠ 0) (hk : k ≠ 0) (h : m = k) :
    integerRotor m hm = integerRotor k hk := by subst h; rfl

theorem integerRotor_neg (n : ℤ) (hn : n ≠ 0) :
    integerRotor (-n) (neg_ne_zero.mpr hn) = integerRotor n hn := by
  simp only [integerRotor, Int.natAbs_neg]

theorem integerRotor_one (n : ℤ) (hn : n ≠ 0) (habs : Int.natAbs n = 1) :
    integerRotor n hn = 1 := by
  rw [integerRotor]
  simp [habs, Real.log_one, zero_smul]

theorem integerRotor_pos (n : ℕ) (hn : n ≠ 0) :
    integerRotor n (Int.natCast_ne_zero.mpr hn) =
      exp ((Real.log n) • hyperbolic 0) := by
  simp only [integerRotor, Int.natAbs_natCast]

theorem integerRotor_mul {m n : ℤ} (hm : m ≠ 0) (hn : n ≠ 0) :
    integerRotor (m * n) (mul_ne_zero hm hn) =
      integerRotor m hm * integerRotor n hn := by
  simp only [integerRotor, Int.natAbs_mul]
  have hmpos : 0 < (Int.natAbs m : ℝ) := by positivity
  have hnpos : 0 < (Int.natAbs n : ℝ) := by positivity
  rw [show Real.log ((Int.natAbs m * Int.natAbs n : ℕ) : ℝ) =
      Real.log (Int.natAbs m : ℝ) + Real.log (Int.natAbs n : ℝ) from by
    rw [Nat.cast_mul]; exact Real.log_mul (ne_of_gt hmpos) (ne_of_gt hnpos)]
  have hcomm :
      Commute (Real.log (Int.natAbs m) • hyperbolic 0)
        (Real.log (Int.natAbs n) • hyperbolic 0) :=
    Generators.hyperbolic_smul_mul _ _
  rw [add_smul, exp_add_of_commute hcomm]

theorem integerRotor_eq_rotorTorsion (n : ℤ) (hn : n ≠ 0) :
    integerRotor n hn = rotorTorsion (pureBoost (2 * Real.log (Int.natAbs n))) := by
  rw [integerRotor, rotorTorsion_pureBoost]
  congr 1
  field_simp [two_mul, mul_assoc, mul_comm (Real.log (Int.natAbs n))]

theorem integerRotor_unitary (n : ℤ) (hn : n ≠ 0) :
    integerRotor n hn * reverse (integerRotor n hn) = 1 := by
  rw [integerRotor_eq_rotorTorsion]
  exact rotor_unitary (pureBoost (2 * Real.log (Int.natAbs n)))

end Embedding

end DstDiophantine
