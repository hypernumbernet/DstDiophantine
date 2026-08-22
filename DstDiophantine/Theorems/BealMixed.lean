import DstDiophantine.Theorems.Beal
import DstDiophantine.Theorems.BealGaussian
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.Tactic.Positivity

/-!
# Phase 7j: Beal residual splits and sub-assemblies

Refines `BealMixedExpResidual` / `BealPythagoreanResidual` into smaller residual
types, assembles them (sorry-free), and lifts the even two-equal `d = 1` shape
`x = y` to a Gaussian hypotenuse power.

The `(n,n,3)` cube slice lives in `DarmonMerel`. Classical Beal is **not**
claimed unconditionally.
-/

namespace DstDiophantine

namespace Theorems

open GaussianInt

local notation "ℤ[i]" => GaussianInt

/-! ### `d = 1` sub-residuals -/

/--
**Residual** (phase 7j, unproved): no three-way-coprime Beal solution with
`bealExpGcd = 1` where two exponents agree and that common value is odd.
-/
def BealTwoEqualOddResidual : Prop :=
  ∀ (A B C : ℤ) (x y z : ℕ) (_hx : 3 ≤ x) (_hy : 3 ≤ y) (_hz : 3 ≤ z)
    (_hA : A ≠ 0) (_hB : B ≠ 0) (_hC : C ≠ 0),
    bealGcd A B C = 1 →
    bealExpGcd x y z = 1 →
    ((x = y ∧ Odd x) ∨ (y = z ∧ Odd y) ∨ (x = z ∧ Odd x)) →
      ¬ A ^ x + B ^ y = C ^ z

/--
**Residual** (phase 7j, unproved): no three-way-coprime Beal solution with
`bealExpGcd = 1` and pairwise-distinct exponents.
-/
def BealAllDistinctExpResidual : Prop :=
  ∀ (A B C : ℤ) (x y z : ℕ) (_hx : 3 ≤ x) (_hy : 3 ≤ y) (_hz : 3 ≤ z)
    (_hA : A ≠ 0) (_hB : B ≠ 0) (_hC : C ≠ 0),
    bealGcd A B C = 1 →
    bealExpGcd x y z = 1 →
    x ≠ y → y ≠ z → x ≠ z →
      ¬ A ^ x + B ^ y = C ^ z

/--
Phase 7j assembly: the three `d = 1` sub-residuals imply `BealMixedExpResidual`.
-/
theorem beal_mixed_exp_of_subresiduals
    (hEven : BealTwoEqualEvenResidual)
    (hOdd : BealTwoEqualOddResidual)
    (hDist : BealAllDistinctExpResidual) :
    BealMixedExpResidual := by
  intro A B C x y z hx hy hz hA hB hC hgcd hd hsol
  rcases beal_expGcd_eq_one_two_equal_or_all_distinct hd with hxy | hyz | hxz | hdist
  · by_cases hxe : Even x
    · exact hEven A B C x y z hx hy hz hA hB hC hgcd hd (Or.inl ⟨hxy, hxe⟩) hsol
    · exact hOdd A B C x y z hx hy hz hA hB hC hgcd hd
        (Or.inl ⟨hxy, Nat.not_even_iff_odd.mp hxe⟩) hsol
  · by_cases hye : Even y
    · exact hEven A B C x y z hx hy hz hA hB hC hgcd hd (Or.inr (Or.inl ⟨hyz, hye⟩)) hsol
    · exact hOdd A B C x y z hx hy hz hA hB hC hgcd hd
        (Or.inr (Or.inl ⟨hyz, Nat.not_even_iff_odd.mp hye⟩)) hsol
  · by_cases hxe : Even x
    · exact hEven A B C x y z hx hy hz hA hB hC hgcd hd (Or.inr (Or.inr ⟨hxz, hxe⟩)) hsol
    · exact hOdd A B C x y z hx hy hz hA hB hC hgcd hd
        (Or.inr (Or.inr ⟨hxz, Nat.not_even_iff_odd.mp hxe⟩)) hsol
  · exact hDist A B C x y z hx hy hz hA hB hC hgcd hd hdist.1 hdist.2.1 hdist.2.2 hsol

/-! ### `d = 2` unequal-odd residual -/

/--
**Residual** (phase 7j, unproved): no three-way-coprime Beal solution with
`bealExpGcd = 2` outside fourth-divisibility and outside equal-odd slices
(even leg shares the hypotenuse's odd reduced exponent).
-/
def BealPythagoreanUnequalOddResidual : Prop :=
  ∀ (A B C : ℤ) (x y z : ℕ) (_hx : 3 ≤ x) (_hy : 3 ≤ y) (_hz : 3 ≤ z)
    (_hA : A ≠ 0) (_hB : B ≠ 0) (_hC : C ≠ 0),
    bealGcd A B C = 1 →
    bealExpGcd x y z = 2 →
    ¬ (4 ∣ x ∧ 4 ∣ y) →
    ¬ (4 ∣ x ∧ 4 ∣ z) →
    ¬ (4 ∣ y ∧ 4 ∣ z) →
    ¬ (y = z ∧ Odd (y / 2) ∧ Even B) →
    ¬ (x = z ∧ Odd (x / 2) ∧ Even A) →
      ¬ A ^ x + B ^ y = C ^ z

private theorem odd_sq_diff_of_opposite_parity {m n : ℤ}
    (hpar : m % 2 = 0 ∧ n % 2 = 1 ∨ m % 2 = 1 ∧ n % 2 = 0) :
    Odd (m ^ 2 - n ^ 2) := by
  have hm2 : m ^ 2 % 2 = m % 2 := by
    have : m % 2 = 0 ∨ m % 2 = 1 := by omega
    rcases this with h | h <;> simp [pow_two, Int.mul_emod, h]
  have hn2 : n ^ 2 % 2 = n % 2 := by
    have : n % 2 = 0 ∨ n % 2 = 1 := by omega
    rcases this with h | h <;> simp [pow_two, Int.mul_emod, h]
  have hdiff : (m ^ 2 - n ^ 2) % 2 = 1 := by
    rcases hpar with ⟨hm, hn⟩ | ⟨hm, hn⟩
    · have : (m ^ 2 - n ^ 2) % 2 = (0 - 1) % 2 := by
        rw [Int.sub_emod, hm2, hn2, hm, hn]
      simpa using this
    · have : (m ^ 2 - n ^ 2) % 2 = (1 - 0) % 2 := by
        rw [Int.sub_emod, hm2, hn2, hm, hn]
      simpa using this
  exact Int.odd_iff.mpr hdiff

private theorem even_pow_ne_odd_sq_diff {K m n : ℤ} {e : ℕ}
    (hKeven : Even K) (he : e ≠ 0)
    (hpar : m % 2 = 0 ∧ n % 2 = 1 ∨ m % 2 = 1 ∧ n % 2 = 0)
    (heq : K ^ e = m ^ 2 - n ^ 2) : False := by
  have hpow : Even (K ^ e) := by
    rw [even_iff_two_dvd] at hKeven ⊢
    exact dvd_pow hKeven he
  have hodd : Odd (K ^ e) := by
    simpa [heq] using odd_sq_diff_of_opposite_parity hpar
  exact Int.not_odd_iff_even.mpr hpow hodd

/--
Classification of a coprime `d = 2` solution with even base `B` forces the
even Pythagorean leg to be `B^{y/2}`.
-/
theorem beal_pythagorean_even_leg_B_of_even_B
    {A B C : ℤ} {x y z : ℕ}
    (hx : 3 ≤ x) (hy : 3 ≤ y) (hz : 3 ≤ z)
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hgcd : bealGcd A B C = 1)
    (hd : bealExpGcd x y z = 2)
    (hBeven : Even B)
    (hsol : A ^ x + B ^ y = C ^ z) :
    ∃ m n : ℤ,
      A ^ (x / 2) = m ^ 2 - n ^ 2 ∧
        B ^ (y / 2) = 2 * m * n ∧
          (C ^ (z / 2) = m ^ 2 + n ^ 2 ∨ C ^ (z / 2) = -(m ^ 2 + n ^ 2)) ∧
            Int.gcd m n = 1 ∧
              (m % 2 = 0 ∧ n % 2 = 1 ∨ m % 2 = 1 ∧ n % 2 = 0) := by
  obtain ⟨m, n, hleg, hhyp, hmn, hpar⟩ :=
    beal_pythagorean_classification_of_expGcd_eq_two hx hy hz hA hB hC hgcd hd hsol
  rcases hleg with h | h
  · exact ⟨m, n, h.1, h.2, hhyp, hmn, hpar⟩
  · have hy0 : y / 2 ≠ 0 := by
      have := (beal_pythagorean_of_expGcd_eq_two hx hy hz hd hsol).2.1
      omega
    exact False.elim (even_pow_ne_odd_sq_diff hBeven hy0 hpar h.2)

theorem beal_pythagorean_even_leg_A_of_even_A
    {A B C : ℤ} {x y z : ℕ}
    (hx : 3 ≤ x) (hy : 3 ≤ y) (hz : 3 ≤ z)
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hgcd : bealGcd A B C = 1)
    (hd : bealExpGcd x y z = 2)
    (hAeven : Even A)
    (hsol : A ^ x + B ^ y = C ^ z) :
    ∃ m n : ℤ,
      A ^ (x / 2) = 2 * m * n ∧
        B ^ (y / 2) = m ^ 2 - n ^ 2 ∧
          (C ^ (z / 2) = m ^ 2 + n ^ 2 ∨ C ^ (z / 2) = -(m ^ 2 + n ^ 2)) ∧
            Int.gcd m n = 1 ∧
              (m % 2 = 0 ∧ n % 2 = 1 ∨ m % 2 = 1 ∧ n % 2 = 0) := by
  obtain ⟨m, n, hleg, hhyp, hmn, hpar⟩ :=
    beal_pythagorean_classification_of_expGcd_eq_two hx hy hz hA hB hC hgcd hd hsol
  rcases hleg with h | h
  · have hx0 : x / 2 ≠ 0 := by
      have := (beal_pythagorean_of_expGcd_eq_two hx hy hz hd hsol).1
      omega
    exact False.elim (even_pow_ne_odd_sq_diff hAeven hx0 hpar h.1)
  · exact ⟨m, n, h.1, h.2, hhyp, hmn, hpar⟩

theorem not_beal_sol_eq_odd_yz_of_two_factor
    (hRes : BealEqualOddTwoFactorResidual)
    {A B C : ℤ} {x y z : ℕ}
    (hx : 3 ≤ x) (hy : 3 ≤ y) (hz : 3 ≤ z)
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hgcd : bealGcd A B C = 1)
    (hd : bealExpGcd x y z = 2)
    (hyz : y = z)
    (hodd : Odd (y / 2))
    (hBeven : Even B)
    (hsol : A ^ x + B ^ y = C ^ z) : False :=
  not_beal_sol_of_expGcd_eq_two_of_eq_odd_yz hRes hx hy hz hA hB hC hgcd hd hyz hodd hsol
    (beal_pythagorean_even_leg_B_of_even_B hx hy hz hA hB hC hgcd hd hBeven hsol)

theorem not_beal_sol_eq_odd_xz_of_two_factor
    (hRes : BealEqualOddTwoFactorResidual)
    {A B C : ℤ} {x y z : ℕ}
    (hx : 3 ≤ x) (hy : 3 ≤ y) (hz : 3 ≤ z)
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hgcd : bealGcd A B C = 1)
    (hd : bealExpGcd x y z = 2)
    (hxz : x = z)
    (hodd : Odd (x / 2))
    (hAeven : Even A)
    (hsol : A ^ x + B ^ y = C ^ z) : False :=
  not_beal_sol_of_expGcd_eq_two_of_eq_odd_xz hRes hx hy hz hA hB hC hgcd hd hxz hodd hsol
    (beal_pythagorean_even_leg_A_of_even_A hx hy hz hA hB hC hgcd hd hAeven hsol)

/--
Phase 7j assembly: equal-odd two-factor residual + unequal-odd residual imply
`BealPythagoreanResidual`.
-/
theorem beal_pythagorean_of_subresiduals
    (hEq : BealEqualOddTwoFactorResidual)
    (hUneq : BealPythagoreanUnequalOddResidual) :
    BealPythagoreanResidual := by
  intro A B C x y z hx hy hz hA hB hC hgcd hd hxy hxz hyz hsol
  by_cases h1 : y = z ∧ Odd (y / 2) ∧ Even B
  · exact not_beal_sol_eq_odd_yz_of_two_factor hEq hx hy hz hA hB hC hgcd hd h1.1 h1.2.1
      h1.2.2 hsol
  · by_cases h2 : x = z ∧ Odd (x / 2) ∧ Even A
    · exact not_beal_sol_eq_odd_xz_of_two_factor hEq hx hy hz hA hB hC hgcd hd h2.1 h2.2.1
        h2.2.2 hsol
    · exact hUneq A B C x y z hx hy hz hA hB hC hgcd hd hxy hxz hyz h1 h2 hsol

/--
Phase 7j: positive classical Beal from the five fine residuals (under the FLT
axiom, via the existing two-residual assembly).
-/
theorem beal_conjecture_pos_of_fine_residuals
    (hEven : BealTwoEqualEvenResidual)
    (hOdd : BealTwoEqualOddResidual)
    (hDist : BealAllDistinctExpResidual)
    (hEq : BealEqualOddTwoFactorResidual)
    (hUneq : BealPythagoreanUnequalOddResidual) :
    ∀ {A B C : ℤ} {x y z : ℕ},
      3 ≤ x → 3 ≤ y → 3 ≤ z →
      0 < A → 0 < B → 0 < C →
      A ^ x + B ^ y = C ^ z →
      1 < bealGcd A B C :=
  beal_conjecture_pos_of_residuals
    (beal_mixed_exp_of_subresiduals hEven hOdd hDist)
    (beal_pythagorean_of_subresiduals hEq hUneq)

/-! ### Even two-equal `x = y` → Gaussian hypotenuse power -/

/--
Even two-equal `x = y` with `d = 1`: the progress identity
`(A^{x/2})² + (B^{x/2})² = C^z` yields a Gaussian hypotenuse `z`-th power
(`z` is odd by coprimality with even `x`).
-/
theorem exists_gaussian_hyp_pow_of_two_equal_xy_even
    {A B C : ℤ} {x y z : ℕ}
    (hx : 3 ≤ x) (hz : 3 ≤ z) (hxy : x = y) (hd : bealExpGcd x y z = 1)
    (hxeven : Even x)
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hgcd : bealGcd A B C = 1)
    (hsol : A ^ x + B ^ y = C ^ z) :
    Odd z ∧
      ((Even A ∧ Odd B) ∨ (Odd A ∧ Even B)) ∧
        IsGaussianHypotenusePower (A ^ (x / 2)) (B ^ (x / 2)) z ∧
          ∃ g : ℤ[i], Associated (g ^ z) (⟨A ^ (x / 2), B ^ (x / 2)⟩ : ℤ[i]) := by
  obtain ⟨_hCodd, hparAB, hsq⟩ :=
    beal_two_equal_xy_even_progress hx hz hxy hd hxeven hA hB hC hgcd hsol
  obtain ⟨hgcdxz, _⟩ := beal_two_equal_exp_of_expGcd_eq_one hx hxy hd
  have hzodd : Odd z := odd_of_even_coprime hxeven hgcdxz
  have hx2pos : 0 < x / 2 := by omega
  have hparLegs :
      (Even (A ^ (x / 2)) ∧ Odd (B ^ (x / 2))) ∨
        (Odd (A ^ (x / 2)) ∧ Even (B ^ (x / 2))) := by
    rcases hparAB with ⟨hAe, hBo⟩ | ⟨hAo, hBe⟩
    · exact Or.inl ⟨Even.pow_of_ne_zero hAe (ne_of_gt hx2pos), Odd.pow hBo⟩
    · exact Or.inr ⟨Odd.pow hAo, Even.pow_of_ne_zero hBe (ne_of_gt hx2pos)⟩
  have hx0 : 0 < x := Nat.lt_of_lt_of_le (by decide : 0 < 3) hx
  have hy0 : 0 < y := by simpa [hxy] using hx0
  have hz0 : 0 < z := Nat.lt_of_lt_of_le (by decide : 0 < 3) hz
  have hab := beal_coprime_ab hA hB hC hx0 hy0 hz0 hgcd hsol
  have hlegGcd : Int.gcd (A ^ (x / 2)) (B ^ (x / 2)) = 1 := by
    have hpow : Nat.Coprime (A.natAbs ^ (x / 2)) (B.natAbs ^ (x / 2)) := by
      rw [Nat.coprime_pow_left_iff hx2pos, Nat.coprime_comm,
        Nat.coprime_pow_left_iff hx2pos, Nat.coprime_comm]
      exact hab
    simpa [Int.gcd, Int.natAbs_pow] using Nat.coprime_iff_gcd_eq_one.mp hpow
  have heq : (A ^ (x / 2)) ^ 2 + (B ^ (x / 2)) ^ 2 = (C.natAbs : ℤ) ^ z := by
    have hnn : 0 ≤ (A ^ (x / 2)) ^ 2 + (B ^ (x / 2)) ^ 2 := by positivity
    have hAbs : (C ^ z).natAbs = C.natAbs ^ z := Int.natAbs_pow _ _
    have hkey : (C ^ z).natAbs =
        ((A ^ (x / 2)) ^ 2 + (B ^ (x / 2)) ^ 2).natAbs := by
      rw [← hsq]
    calc (A ^ (x / 2)) ^ 2 + (B ^ (x / 2)) ^ 2
        = ↑((A ^ (x / 2)) ^ 2 + (B ^ (x / 2)) ^ 2).natAbs :=
          (Int.natAbs_of_nonneg hnn).symm
      _ = ↑(C ^ z).natAbs := by rw [hkey]
      _ = ↑(C.natAbs ^ z) := by rw [hAbs]
      _ = (C.natAbs : ℤ) ^ z := by norm_cast
  refine ⟨hzodd, hparAB,
    isGaussianHypotenusePower_of_hyp_eq_pow hz0 hlegGcd hparLegs heq, ?_⟩
  exact exists_associated_pow_of_hyp_eq_pow hz0 hlegGcd hparLegs heq

end Theorems

end DstDiophantine
