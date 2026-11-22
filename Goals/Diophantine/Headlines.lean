import DstDiophantine.Algebra.Admissible
import Goals.Diophantine.Bridges
import Goals.Diophantine.Residuals

open DstDiophantine.Admissible
open DstDiophantine.Theorems

/-!
# Headline Diophantine conjectures

Each proof assembles an open leaf or bridge and is not unconditional. Positive Beal also uses the
FLT axiom `fermatLastTheorem`.
-/

namespace Goals.Diophantine

/-- Not a proof: assembled from the six live leaves; the `d ≥ 3` slice uses the FLT axiom. -/
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

/-- Not a proof: assembled from the open leaf `fermatMixedMotorResidual`. -/
theorem fermat_last_theorem_unconditional : FermatLastTheorem :=
  FermatLastTheorem_of_mixed_motor_residual fermatMixedMotorResidual

/-- Not a proof: assembled from the open bridge `abcModularBridge`. -/
theorem abc_conjecture_unconditional :
    ∀ (ε : ℝ), 0 < ε →
      ∃ C : ℝ, 0 < C ∧
        ∀ (a b c : ℕ), IsAbcTriple a b c →
          (c : ℝ) ≤ C * (abcRadical (a * b * c) : ℝ) ^ (1 + ε) :=
  abc_conjecture_of_modular_bridge abcModularBridge

/-- Not a proof: equivalent to `collatzAdmissibleBridge`. -/
theorem collatz_conjecture_unconditional :
    ∀ n : ℕ, 0 < n → ReachesOne n :=
  collatz_conjecture_of_bridge collatzAdmissibleBridge

/-- Not a proof: equivalent to `goldbachAdmissibleBridge`. -/
theorem goldbach_conjecture_unconditional :
    ∀ n : ℕ, Even n → 4 ≤ n → ∃ p q : ℕ, IsGoldbachPair p q n :=
  goldbach_conjecture_of_bridge goldbachAdmissibleBridge

/-- Not a proof: equivalent to `polignacAdmissibleBridge`. -/
theorem polignac_conjecture_unconditional :
    ∀ k : ℕ, 0 < k → ∀ B : ℕ, ∃ p : ℕ, B < p ∧ IsPolignacPair p k :=
  polignac_conjecture_of_bridge polignacAdmissibleBridge

/-- Not a proof: Polignac at `k = 1`, not a separate open leaf. -/
theorem twin_prime_conjecture_unconditional :
    ∀ B : ℕ, ∃ p : ℕ, B < p ∧ IsTwinPrimePair p :=
  twin_prime_conjecture_of_bridge polignacAdmissibleBridge

/-- Not a proof: not mathlib's `riemannZeta`; the open leaf is `riemannAdmissibleBridge`. -/
theorem riemann_hypothesis_unconditional :
    ∀ ρ_re : ℝ, ρ_re ≠ 1 / 2 →
      ∃ θ : ℝ, 0 < θ ∧
        IsAdmissibleContinuous (criticalMismatchParams θ ρ_re) ∧
          0 < criticalHeight θ ρ_re ∧
            ¬ IsCriticalZeroEnsemble θ ρ_re :=
  riemann_hypothesis_of_bridge riemannAdmissibleBridge

end Goals.Diophantine
