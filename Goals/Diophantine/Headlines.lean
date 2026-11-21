import DstDiophantine.Algebra.Admissible
import Goals.Diophantine.Bridges
import Goals.Diophantine.Residuals

open DstDiophantine.Admissible
open DstDiophantine.Theorems

/-!
# Headline Diophantine conjectures

Each statement below is the classical (or, for the critical line, the DST)
claim. The proof is the assembly already in the main library, applied to the
open leaves in `Residuals.lean` and `Bridges.lean`. None of these proofs is
unconditional: the `sorry` sits on that leaf or bridge. Positive Beal also
uses the FLT axiom `fermatLastTheorem` inside the main-library assembly.
-/

namespace Goals.Diophantine

/-- **Claim (EN):** Positive Beal solutions with exponents ≥ 3 share a prime
    factor.

    **Claim (JA):** 指数がすべて 3 以上の正のベール解は共通の素因数を持つ。

    **Paper:** `papers/dst-diophantine.tex`.

    **Status:** assembled from the six live leaves by
    `beal_conjecture_pos_of_fine_residuals_even_split`. The `d ≥ 3` slice uses
    the FLT axiom in the main library.
-/
theorem classical_beal_conjecture :
    ∀ {A B C : ℤ} {x y z : ℕ},
      3 ≤ x → 3 ≤ y → 3 ≤ z →
      0 < A → 0 < B → 0 < C →
      A ^ x + B ^ y = C ^ z →
      1 < bealGcd A B C :=
  beal_conjecture_pos_of_fine_residuals_even_split
    (BealTwoEqualEvenSumResidual_of_ge_seven_outside_fourth_fifth
      bealTwoEqualEvenSumExpGeSevenOutsideFourthFifthResidual)
    (BealTwoEqualEvenDiffResidual_of_outside_fifth
      bealTwoEqualEvenDiffOutsideFifthPairResidual)
    (BealTwoEqualOddResidual_of_outside_fifth_pair
      bealTwoEqualOddOutsideFifthPairResidual)
    (BealAllDistinctExpResidual_of_outside_fifth_pair
      bealAllDistinctOutsideFifthPairResidual)
    (BealEqualOddTwoFactorResidual_of_ge_five
      bealEqualOddTwoFactorExpGeFiveResidual)
    (BealPythagoreanUnequalOddResidual_of_outside_fifth_pair
      bealPythagoreanUnequalOddOutsideFifthPairResidual)

/-- **Claim (EN):** Fermat's Last Theorem.

    **Claim (JA):** フェルマーの最終定理。

    **Paper:** `papers/dst-diophantine.tex`.

    **Status:** assembled by `FermatLastTheorem_of_mixed_motor_residual`.
    The open leaf is `fermatMixedMotorResidual`.
-/
theorem fermat_last_theorem_unconditional : FermatLastTheorem :=
  FermatLastTheorem_of_mixed_motor_residual fermatMixedMotorResidual

/-- **Claim (EN):** The abc conjecture.

    **Claim (JA):** abc 予想。

    **Paper:** `papers/dst-diophantine.tex`.

    **Status:** assembled by `abc_conjecture_of_modular_bridge`.
    The open leaf is `abcModularBridge`.
-/
theorem abc_conjecture_unconditional :
    ∀ (ε : ℝ), 0 < ε →
      ∃ C : ℝ, 0 < C ∧
        ∀ (a b c : ℕ), IsAbcTriple a b c →
          (c : ℝ) ≤ C * (abcRadical (a * b * c) : ℝ) ^ (1 + ε) :=
  abc_conjecture_of_modular_bridge abcModularBridge

/-- **Claim (EN):** The Collatz conjecture.

    **Claim (JA):** コラッツ予想。

    **Paper:** `papers/dst-diophantine.tex`.

    **Status:** assembled by `collatz_conjecture_of_bridge`.
    Equivalent to `collatzAdmissibleBridge`.
-/
theorem collatz_conjecture_unconditional :
    ∀ n : ℕ, 0 < n → ReachesOne n :=
  collatz_conjecture_of_bridge collatzAdmissibleBridge

/-- **Claim (EN):** The Goldbach conjecture.

    **Claim (JA):** ゴールドバッハ予想。

    **Paper:** `papers/dst-diophantine.tex`.

    **Status:** assembled by `goldbach_conjecture_of_bridge`.
    Equivalent to `goldbachAdmissibleBridge`.
-/
theorem goldbach_conjecture_unconditional :
    ∀ n : ℕ, Even n → 4 ≤ n → ∃ p q : ℕ, IsGoldbachPair p q n :=
  goldbach_conjecture_of_bridge goldbachAdmissibleBridge

/-- **Claim (EN):** Polignac's conjecture.

    **Claim (JA):** ポリニャック予想。

    **Paper:** `papers/dst-diophantine.tex`.

    **Status:** assembled by `polignac_conjecture_of_bridge`.
    Equivalent to `polignacAdmissibleBridge`.
-/
theorem polignac_conjecture_unconditional :
    ∀ k : ℕ, 0 < k → ∀ B : ℕ, ∃ p : ℕ, B < p ∧ IsPolignacPair p k :=
  polignac_conjecture_of_bridge polignacAdmissibleBridge

/-- **Claim (EN):** The twin-prime conjecture.

    **Claim (JA):** 双子素数予想。

    **Paper:** `papers/dst-diophantine.tex`.

    **Status:** assembled by `twin_prime_conjecture_of_bridge`.
    This is Polignac at `k = 1`, not a separate open leaf.
-/
theorem twin_prime_conjecture_unconditional :
    ∀ B : ℕ, ∃ p : ℕ, B < p ∧ IsTwinPrimePair p :=
  twin_prime_conjecture_of_bridge polignacAdmissibleBridge

/-- **Claim (EN):** Off the critical line, some positive-height admissible
    ensemble is not a zero ensemble.

    **Claim (JA):** 臨界線の外では、正の高さを持つ許容アンサンブルで、零
    アンサンブルでないものがある。

    **Paper:** `papers/dst-diophantine.tex`, Chapter 8.

    **Status:** assembled by `riemann_hypothesis_of_bridge`.
    Not mathlib's `riemannZeta`. The open leaf is `riemannAdmissibleBridge`.
-/
theorem riemann_hypothesis_unconditional :
    ∀ ρ_re : ℝ, ρ_re ≠ 1 / 2 →
      ∃ θ : ℝ, 0 < θ ∧
        IsAdmissibleContinuous (criticalMismatchParams θ ρ_re) ∧
          0 < criticalHeight θ ρ_re ∧
            ¬ IsCriticalZeroEnsemble θ ρ_re :=
  riemann_hypothesis_of_bridge riemannAdmissibleBridge

end Goals.Diophantine
