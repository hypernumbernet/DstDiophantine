import DstDiophantine.Embedding.IntegerRotor
import DstDiophantine.Algebra.Amplification
import DstDiophantine.Algebra.Invariant

/-!
# Rotor powers and torsional amplification for integer embeddings
-/

namespace DstDiophantine

namespace Embedding

open Amplification Invariant Operations Real CliffordAlgebra PGA

theorem integerRotor_pow {n : ℤ} (hn : n ≠ 0) (p : ℕ) :
    integerRotor (n ^ p) (pow_ne_zero p hn) = (integerRotor n hn) ^ p := by
  induction p with
  | zero =>
    calc integerRotor (n ^ 0) (pow_ne_zero 0 hn)
        = integerRotor 1 (by norm_num) :=
            integerRotor_eq_of_arg_eq _ _ (pow_zero n)
      _ = 1 := integerRotor_one 1 (by norm_num) rfl
      _ = (integerRotor n hn) ^ 0 := by rw [pow_zero]
  | succ p ih =>
    have hn' : n ^ p ≠ 0 := pow_ne_zero p hn
    have hpow : n ^ (p + 1) = n ^ p * n := pow_succ n p
    have hmul : n ^ p * n = n * n ^ p := mul_comm (n ^ p) n
    have hnm : n ^ (p + 1) = n * n ^ p := hpow.trans hmul
    have hne' : n ^ (p + 1) ≠ 0 := pow_ne_zero (p + 1) hn
    have hne : n * n ^ p ≠ 0 := by rw [← hnm]; exact hne'
    set R : PGA := integerRotor n hn
    calc integerRotor (n ^ (p + 1)) hne'
        = integerRotor (n * n ^ p) hne := integerRotor_eq_of_arg_eq _ _ hnm
      _ = R * integerRotor (n ^ p) hn' := integerRotor_mul hn hn'
      _ = R * R ^ p := by rw [ih]
      _ = R ^ (p + 1) := by
          rw [(Commute.pow_right (Commute.refl R) p).eq, pow_succ]

/-- Log mismatch on axis `0` between two integers (model for `R(a)† R(c)`). -/
noncomputable def logMismatch (a c : ℤ) (_ha : a ≠ 0) (_hc : c ≠ 0) : TorsionParams :=
  pureBoost (Real.log (Int.natAbs c) - Real.log (Int.natAbs a))

theorem J_logMismatch (a c : ℤ) (ha : a ≠ 0) (hc : c ≠ 0) :
    J (logMismatch a c ha hc) =
      (1 / 2) * (Real.log (Int.natAbs c) - Real.log (Int.natAbs a)) ^ 2 := by
  dsimp [logMismatch]
  exact J_pureBoost _

/-- Leading `p²` amplification on the pure-boost mismatch model. -/
theorem J_pow_amplify_int {a c : ℤ} (ha : a ≠ 0) (hc : c ≠ 0) (p : ℕ) :
    J (pureBoost (p * (Real.log (Int.natAbs c) - Real.log (Int.natAbs a)))) =
      (p : ℝ) ^ 2 * J (logMismatch a c ha hc) := by
  rw [J_pow_amplify, logMismatch]

theorem JNormalized_pow_amplify_int {a c : ℤ} (ha : a ≠ 0) (hc : c ≠ 0) (p : ℕ) :
    JNormalized (pureBoost (p * (Real.log (Int.natAbs c) - Real.log (Int.natAbs a)))) =
      (p : ℝ) ^ 2 * JNormalized (logMismatch a c ha hc) := by
  rw [JNormalized_pow_amplify, logMismatch]

end Embedding

end DstDiophantine
