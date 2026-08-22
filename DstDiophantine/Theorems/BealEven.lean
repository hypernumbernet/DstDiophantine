import DstDiophantine.Theorems.BealGaussian
import DstDiophantine.Theorems.BealMixed
import DstDiophantine.Theorems.DarmonMerel
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.Tactic.Linarith

/-!
# Phase 7k: even two-equal residual split (sum vs difference)

Splits `BealTwoEqualEvenResidual` into:

* **sum form** `x = y` even — Gaussian hypotenuse power
  `(A^{x/2})² + (B^{x/2})² = C^z`;
* **difference form** `y = z` or `x = z` with even common exponent —
  `C^n − B^n = A^x` (does **not** lift to a Gaussian hypotenuse power).

The sum form with `z = 3` is closed by Darmon–Merel. Classical Beal is **not**
claimed unconditionally.
-/

namespace DstDiophantine

namespace Theorems

open GaussianInt

local notation "ℤ[i]" => GaussianInt

/-! ### Residual types -/

/--
**Residual** (phase 7k, unproved): no three-way-coprime Beal solution with
`bealExpGcd = 1`, `x = y`, and even common exponent (Gaussian sum form).
-/
def BealTwoEqualEvenSumResidual : Prop :=
  ∀ (A B C : ℤ) (x y z : ℕ) (_hx : 3 ≤ x) (_hy : 3 ≤ y) (_hz : 3 ≤ z)
    (_hA : A ≠ 0) (_hB : B ≠ 0) (_hC : C ≠ 0),
    bealGcd A B C = 1 →
    bealExpGcd x y z = 1 →
    x = y → Even x →
      ¬ A ^ x + B ^ y = C ^ z

/--
**Residual** (phase 7k, unproved): no three-way-coprime Beal solution with
`bealExpGcd = 1` and even common exponent on `y = z` or `x = z`
(difference form `C^n − B^n = A^x`).
-/
def BealTwoEqualEvenDiffResidual : Prop :=
  ∀ (A B C : ℤ) (x y z : ℕ) (_hx : 3 ≤ x) (_hy : 3 ≤ y) (_hz : 3 ≤ z)
    (_hA : A ≠ 0) (_hB : B ≠ 0) (_hC : C ≠ 0),
    bealGcd A B C = 1 →
    bealExpGcd x y z = 1 →
    ((y = z ∧ Even y) ∨ (x = z ∧ Even x)) →
      ¬ A ^ x + B ^ y = C ^ z

/--
Phase 7k assembly: sum + difference residuals imply `BealTwoEqualEvenResidual`.
-/
theorem beal_two_equal_even_of_sum_diff
    (hSum : BealTwoEqualEvenSumResidual)
    (hDiff : BealTwoEqualEvenDiffResidual) :
    BealTwoEqualEvenResidual := by
  intro A B C x y z hx hy hz hA hB hC hgcd hd hpair hsol
  rcases hpair with ⟨hxy, hxe⟩ | ⟨hyz, hye⟩ | ⟨hxz, hxe⟩
  · exact hSum A B C x y z hx hy hz hA hB hC hgcd hd hxy hxe hsol
  · exact hDiff A B C x y z hx hy hz hA hB hC hgcd hd (Or.inl ⟨hyz, hye⟩) hsol
  · exact hDiff A B C x y z hx hy hz hA hB hC hgcd hd (Or.inr ⟨hxz, hxe⟩) hsol

/-! ### Sum form: Gaussian package + Darmon–Merel cube slice -/

/--
Sum form lifts to a Gaussian hypotenuse `z`-th power with both coordinates
pure `(x/2)`-th powers (`x/2 ≥ 2`).
-/
theorem beal_two_equal_even_sum_gaussian
    {A B C : ℤ} {x y z : ℕ}
    (hx : 3 ≤ x) (hz : 3 ≤ z) (hxy : x = y) (hd : bealExpGcd x y z = 1)
    (hxeven : Even x)
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hgcd : bealGcd A B C = 1)
    (hsol : A ^ x + B ^ y = C ^ z) :
    Odd z ∧
      2 ≤ x / 2 ∧
        IsGaussianHypotenusePower (A ^ (x / 2)) (B ^ (x / 2)) z ∧
          ∃ g : ℤ[i], Associated (g ^ z) (⟨A ^ (x / 2), B ^ (x / 2)⟩ : ℤ[i]) := by
  obtain ⟨hzodd, _, hIs, hG⟩ :=
    exists_gaussian_hyp_pow_of_two_equal_xy_even hx hz hxy hd hxeven hA hB hC hgcd hsol
  have hx4 : 4 ≤ x := by
    have : x ≠ 3 := by
      intro h; subst h
      exact Nat.not_even_iff_odd.mpr (by decide : Odd 3) hxeven
    omega
  exact ⟨hzodd, by omega, hIs, hG⟩

/--
If the sum residual holds outside the Darmon–Merel cube slice `z = 3`,
then together with that slice the full sum residual follows.
-/
theorem BealTwoEqualEvenSumResidual_of_outside_cube
    (hOut :
      ∀ (A B C : ℤ) (x y z : ℕ) (_hx : 3 ≤ x) (_hy : 3 ≤ y) (_hz : 3 ≤ z)
        (_hA : A ≠ 0) (_hB : B ≠ 0) (_hC : C ≠ 0),
        bealGcd A B C = 1 →
        bealExpGcd x y z = 1 →
        x = y → Even x → z ≠ 3 →
          ¬ A ^ x + B ^ y = C ^ z) :
    BealTwoEqualEvenSumResidual := by
  intro A B C x y z hx hy hz hA hB hC hgcd hd hxy hxeven hsol
  by_cases hz3 : z = 3
  · exact not_beal_two_equal_third_three hx hy hz hA hB hC hgcd hd hxy hz3 hsol
  · exact hOut A B C x y z hx hy hz hA hB hC hgcd hd hxy hxeven hz3 hsol

/-! ### Difference form: rewrite identity -/

theorem beal_two_equal_even_diff_yz_form
    {A B C : ℤ} {x y z : ℕ}
    (hyz : y = z) (hsol : A ^ x + B ^ y = C ^ z) :
    C ^ y - B ^ y = A ^ x := by
  subst hyz; linarith [hsol]

theorem beal_two_equal_even_diff_xz_form
    {A B C : ℤ} {x y z : ℕ}
    (hxz : x = z) (hsol : A ^ x + B ^ y = C ^ z) :
    C ^ x - A ^ x = B ^ y := by
  subst hxz; linarith [hsol]

/--
Phase 7k: five fine residuals with even residual replaced by sum+diff still
recover positive classical Beal (under the FLT axiom via the existing assembly).
-/
theorem beal_conjecture_pos_of_fine_residuals_even_split
    (hSum : BealTwoEqualEvenSumResidual)
    (hDiff : BealTwoEqualEvenDiffResidual)
    (hOdd : BealTwoEqualOddResidual)
    (hDist : BealAllDistinctExpResidual)
    (hEq : BealEqualOddTwoFactorResidual)
    (hUneq : BealPythagoreanUnequalOddResidual) :
    ∀ {A B C : ℤ} {x y z : ℕ},
      3 ≤ x → 3 ≤ y → 3 ≤ z →
      0 < A → 0 < B → 0 < C →
      A ^ x + B ^ y = C ^ z →
      1 < bealGcd A B C :=
  beal_conjecture_pos_of_fine_residuals
    (beal_two_equal_even_of_sum_diff hSum hDiff) hOdd hDist hEq hUneq

end Theorems

end DstDiophantine
