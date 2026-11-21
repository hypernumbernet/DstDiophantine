import DstDiophantine.Algebra.Admissible
import DstDiophantine.Theorems.Abc
import DstDiophantine.Theorems.Beal
import DstDiophantine.Theorems.Collatz
import DstDiophantine.Theorems.FermatLast
import DstDiophantine.Theorems.Goldbach
import DstDiophantine.Theorems.Polignac
import DstDiophantine.Theorems.Riemann
import Mathlib.NumberTheory.FLT.Basic

open DstDiophantine.Admissible
open DstDiophantine.Theorems

/-!
# Headline Diophantine conjectures (target proofs)

Unconditional classical statements. Assembly lemmas in the main library
(e.g. `beal_conjecture_pos_of_fine_residuals`) show how residuals imply
these goals once the listed leaves in `Goals.Diophantine.Residuals` are proved.
-/

namespace Goals.Diophantine

/-- **Claim (EN):** Positive Beal solutions with exponents ≥ 3 share a prime factor.

    **Claim (JA):** 指数がすべて 3 以上の正のベール解は共通の素因数を持つ。

    **Paper:** `papers/dst-diophantine.tex`.

    **Status:** open — see residuals; assembly in `beal_conjecture_pos_of_fine_residuals`.
-/
theorem classical_beal_conjecture :
    ∀ {A B C : ℤ} {x y z : ℕ},
      3 ≤ x → 3 ≤ y → 3 ≤ z →
      0 < A → 0 < B → 0 < C →
      A ^ x + B ^ y = C ^ z →
      1 < bealGcd A B C := by sorry

/-- **Claim (EN):** Fermat's Last Theorem.

    **Claim (JA):** フェルマーの最終定理。

    **Paper:** `papers/dst-diophantine.tex`.

    **Status:** open — `FermatMixedMotorResidual`.
-/
theorem fermat_last_theorem_unconditional : FermatLastTheorem := by sorry

/-- **Claim (EN):** The abc conjecture.

    **Claim (JA):** abc 予想。

    **Paper:** `papers/dst-diophantine.tex`.

    **Status:** open — `AbcModularBridge`.
-/
theorem abc_conjecture_unconditional :
    ∀ (ε : ℝ), 0 < ε →
      ∃ C : ℝ, 0 < C ∧
        ∀ (a b c : ℕ), IsAbcTriple a b c →
          (c : ℝ) ≤ C * (abcRadical (a * b * c) : ℝ) ^ (1 + ε) := by sorry

theorem collatz_conjecture_unconditional :
    ∀ n : ℕ, 0 < n → ReachesOne n := by sorry

theorem goldbach_conjecture_unconditional :
    ∀ n : ℕ, Even n → 4 ≤ n → ∃ p q : ℕ, IsGoldbachPair p q n := by sorry

theorem polignac_conjecture_unconditional :
    ∀ k : ℕ, 0 < k → ∀ B : ℕ, ∃ p : ℕ, B < p ∧ IsPolignacPair p k := by sorry

theorem twin_prime_conjecture_unconditional :
    ∀ B : ℕ, ∃ p : ℕ, B < p ∧ IsTwinPrimePair p := by sorry

theorem riemann_hypothesis_unconditional :
    ∀ ρ_re : ℝ, ρ_re ≠ 1 / 2 →
      ∃ θ : ℝ, 0 < θ ∧
        IsAdmissibleContinuous (criticalMismatchParams θ ρ_re) ∧
          0 < criticalHeight θ ρ_re ∧
            ¬ IsCriticalZeroEnsemble θ ρ_re := by sorry

end Goals.Diophantine