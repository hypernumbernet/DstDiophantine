import DstDiophantine.Embedding.NullTranslator
import DstDiophantine.Embedding.IntegerRotor
import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation

/-!
# Power-sum Diophantine representation

Phase 4 restricts the paper's informal “arbitrary polynomial” embedding to
**integer linear combinations of pure powers**
`∑ᵢ cᵢ · bᵢ^{eᵢ} = 0`, which covers the additive skeletons of FLT, Beal,
Goldbach, and abc. The null-translator motor is faithful for this class.
-/

namespace DstDiophantine

namespace Framework

open _root_.DstDiophantine.Embedding CliffordAlgebra PGA
/-- A single powered monomial `coeff · base ^ exp`. -/
structure PowerSumTerm where
  coeff : ℤ
  base : ℤ
  exp : ℕ

/-- Evaluate one term as an integer. -/
def evalTerm (t : PowerSumTerm) : ℤ :=
  t.coeff * t.base ^ t.exp

/-- Finite power-sum equation `∑ terms = 0`. -/
structure PowerSumEquation where
  terms : List PowerSumTerm

/-- Integer evaluation of a power-sum expression. -/
def evalPowerSum (e : PowerSumEquation) : ℤ :=
  (e.terms.map evalTerm).sum

/-- Additive null-sector motor: `T(eval e)`. Equals `1` precisely when `e` vanishes. -/
noncomputable def powerSumMotor (e : PowerSumEquation) : PGA :=
  Embedding.nullTranslator (evalPowerSum e)

theorem powerSumMotor_eq (e : PowerSumEquation) :
    powerSumMotor e = Embedding.nullTranslator (evalPowerSum e) := rfl

theorem powerSumMotor_one_iff (e : PowerSumEquation) :
    powerSumMotor e = 1 ↔ evalPowerSum e = 0 := by
  rw [powerSumMotor, Embedding.nullTranslator_faithful]

/-- Convenience: equation `a^p + b^p - c^p = 0`. -/
def fermatEquation (a b c : ℤ) (p : ℕ) : PowerSumEquation where
  terms := [
    ⟨1, a, p⟩,
    ⟨1, b, p⟩,
    ⟨-1, c, p⟩
  ]

theorem eval_fermat (a b c : ℤ) (p : ℕ) :
    evalPowerSum (fermatEquation a b c p) = a ^ p + b ^ p - c ^ p := by
  simp [evalPowerSum, fermatEquation, evalTerm]
  ring

theorem fermatMotor_one_iff (a b c : ℤ) (p : ℕ) :
    powerSumMotor (fermatEquation a b c p) = 1 ↔ a ^ p + b ^ p = c ^ p := by
  rw [powerSumMotor_one_iff, eval_fermat, sub_eq_zero]

/-- Additive relation `a + b - c = 0` as a power-sum (exponents `1`). -/
def additivePowerSum (a b c : ℤ) : PowerSumEquation where
  terms := [
    ⟨1, a, 1⟩,
    ⟨1, b, 1⟩,
    ⟨-1, c, 1⟩
  ]

theorem eval_additivePowerSum (a b c : ℤ) :
    evalPowerSum (additivePowerSum a b c) = a + b - c := by
  simp [evalPowerSum, additivePowerSum, evalTerm, pow_one]
  ring
theorem additivePowerSum_one_iff (a b c : ℤ) :
    powerSumMotor (additivePowerSum a b c) = 1 ↔ a + b = c := by
  rw [powerSumMotor_one_iff, eval_additivePowerSum, sub_eq_zero]

/--
Paper shape `R(f) · exp(∑ T) = 1` specialised to the null sector:
vanishing of `eval` is equivalent to the translator motor being the identity.
The rotor factor is supplied separately via `mismatchRotor` for amplification
arguments (Phase 5).
-/
theorem paperForm_null_sector (e : PowerSumEquation) :
    powerSumMotor e = 1 ↔ evalPowerSum e = 0 :=
  powerSumMotor_one_iff e

/-- Mismatch rotor between two nonzero integers (usual-sector amplification seed). -/
noncomputable def mismatchRotor (a c : ℤ) (ha : a ≠ 0) (hc : c ≠ 0) : PGA :=
  reverse (integerRotor a ha) * integerRotor c hc

/-- Powered mismatch for Fermat-type amplification. -/
noncomputable def poweredMismatch (a c : ℤ) (ha : a ≠ 0) (hc : c ≠ 0) (p : ℕ) : PGA :=
  (mismatchRotor a c ha hc) ^ p

end Framework

end DstDiophantine
