import DstDiophantine.Algebra.Motor
import DstDiophantine.Algebra.QuadraticForm
import DstDiophantine.Algebra.PGA
import DstDiophantine.Algebra.Generators
import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation

/-!
# Null translators `T(a) = exp(½ a^μ N_μ)`
-/

namespace DstDiophantine

open CliffordAlgebra PGA Generators Motor QuadraticForm

namespace Embedding

def minkowskiOfInt (a : ℤ) : Fin 4 → ℝ
  | 0 => 0
  | 1 => a
  | 2 => 0
  | 3 => 0

@[simp] theorem minkowskiOfInt_zero : minkowskiOfInt 0 = fun _ => 0 := by
  funext μ
  fin_cases μ <;> simp [minkowskiOfInt]

@[simp] theorem minkowskiOfInt_add (a b : ℤ) :
    minkowskiOfInt (a + b) = fun μ => minkowskiOfInt a μ + minkowskiOfInt b μ := by
  funext μ
  fin_cases μ <;> simp [minkowskiOfInt]

noncomputable def nullTranslator (a : ℤ) : PGA :=
  expTrans ⟨minkowskiOfInt a⟩

theorem nullTranslator_zero : nullTranslator 0 = 1 := by
  simp [nullTranslator, expTrans, omegaTrans, minkowskiOfInt_zero, Finset.sum_const_zero]

theorem nullTranslator_add (a b : ℤ) :
    nullTranslator (a + b) = nullTranslator a * nullTranslator b := by
  simp only [nullTranslator, expTrans]
  have hω :
      omegaTrans ⟨minkowskiOfInt (a + b)⟩ =
        omegaTrans ⟨minkowskiOfInt a⟩ + omegaTrans ⟨minkowskiOfInt b⟩ := by
    rw [minkowskiOfInt_add, omegaTrans_add]
  rw [hω]
  set A := omegaTrans ⟨minkowskiOfInt a⟩
  set B := omegaTrans ⟨minkowskiOfInt b⟩
  calc 1 + (A + B)
      = 1 + A + B := by rw [add_assoc]
    _ = 1 + B + A := by ac_rfl
    _ = 1 + B + A + A * B := by rw [add_assoc, omegaTrans_mul, add_zero]
    _ = (1 + A) * (1 + B) := by noncomm_ring

theorem nullTranslator_unitary (a : ℤ) :
    nullTranslator a * reverse (nullTranslator a) = 1 :=
  expTrans_unitary ⟨minkowskiOfInt a⟩

noncomputable def translateBy (R : PGA) (a : ℤ) : PGA :=
  R * nullTranslator a * reverse R

private theorem castAdd_one_eq_one : Fin.castAdd 1 (1 : Fin 4) = (1 : Fin 5) := by decide

private theorem omegaTrans_minkowski_eq (a : ℤ) :
    omegaTrans ⟨minkowskiOfInt a⟩ = (a / 2 : ℝ) • null 1 := by
  simp only [omegaTrans, minkowskiOfInt, Fin.sum_univ_four, null, div_eq_mul_inv, Fin.isValue,
    castAdd_one_eq_one]
  ring_nf
  simp [zero_smul, add_zero]

theorem nullTranslator_faithful (a : ℤ) :
    nullTranslator a = 1 ↔ a = 0 := by
  constructor
  · intro h
    have hω : omegaTrans ⟨minkowskiOfInt a⟩ = 0 := by
      rw [nullTranslator, expTrans] at h
      exact add_left_cancel (h.trans (add_zero 1).symm)
    rw [omegaTrans_minkowski_eq] at hω
    rcases smul_eq_zero.mp hω with hc | hn
    · have ha : (a : ℝ) = 0 := by linarith [hc]
      exact Int.cast_eq_zero.mp ha
    · exact absurd hn null_one_ne_zero
  · intro h
    simp [h, nullTranslator_zero]

end Embedding

end DstDiophantine
