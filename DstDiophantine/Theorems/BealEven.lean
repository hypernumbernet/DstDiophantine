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

/-! ### Difference form: rewrite identity and factorization progress -/

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

/-- Even common exponent and `gcd(x,y)=1` force the distinct exponent odd. -/
theorem beal_two_equal_even_diff_yz_x_odd
    {x y z : ℕ} (hy : 3 ≤ y) (hyz : y = z) (hd : bealExpGcd x y z = 1)
    (hyeven : Even y) : Odd x := by
  obtain ⟨hgcdxy, _⟩ := beal_two_equal_exp_yz_of_expGcd_eq_one hy hyz hd
  have : Nat.gcd y x = 1 := by rw [Nat.gcd_comm]; exact hgcdxy
  exact odd_of_even_coprime hyeven this

theorem beal_two_equal_even_diff_xz_y_odd
    {x y z : ℕ} (hx : 3 ≤ x) (hxz : x = z) (hd : bealExpGcd x y z = 1)
    (hxeven : Even x) : Odd y := by
  obtain ⟨hgcdxy, _⟩ := beal_two_equal_exp_xz_of_expGcd_eq_one hx hxz hd
  exact odd_of_even_coprime hxeven hgcdxy

theorem even_pow_sub_eq_mul {C B : ℤ} {y : ℕ} (hyeven : Even y) :
    C ^ y - B ^ y =
      (C ^ (y / 2) - B ^ (y / 2)) * (C ^ (y / 2) + B ^ (y / 2)) := by
  obtain ⟨k, hk⟩ := even_iff_exists_two_mul.mp hyeven
  have hy2 : y / 2 = k := by omega
  have hC : C ^ y = (C ^ k) ^ 2 := by
    rw [hk, show 2 * k = k * 2 by ring, pow_mul]
  have hB : B ^ y = (B ^ k) ^ 2 := by
    rw [hk, show 2 * k = k * 2 by ring, pow_mul]
  calc C ^ y - B ^ y
      = (C ^ k) ^ 2 - (B ^ k) ^ 2 := by rw [hC, hB]
    _ = (C ^ k - B ^ k) * (C ^ k + B ^ k) := by ring
    _ = (C ^ (y / 2) - B ^ (y / 2)) * (C ^ (y / 2) + B ^ (y / 2)) := by
        rw [hy2]

/--
Progress package for the even difference form `y = z`: rewrite, odd distinct
exponent, and factorization into conjugate factors whose product is `A^x`.
-/
theorem beal_two_equal_even_diff_yz_progress
    {A B C : ℤ} {x y z : ℕ}
    (hx : 3 ≤ x) (hy : 3 ≤ y) (hz : 3 ≤ z)
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hgcd : bealGcd A B C = 1)
    (hd : bealExpGcd x y z = 1)
    (hyz : y = z) (hyeven : Even y)
    (hsol : A ^ x + B ^ y = C ^ z) :
    Odd x ∧
      C ^ y - B ^ y = A ^ x ∧
        (C ^ (y / 2) - B ^ (y / 2)) * (C ^ (y / 2) + B ^ (y / 2)) = A ^ x ∧
          Nat.Coprime B.natAbs C.natAbs := by
  have hxodd := beal_two_equal_even_diff_yz_x_odd hy hyz hd hyeven
  have hdiff := beal_two_equal_even_diff_yz_form hyz hsol
  have hfac : (C ^ (y / 2) - B ^ (y / 2)) * (C ^ (y / 2) + B ^ (y / 2)) = A ^ x := by
    rw [← even_pow_sub_eq_mul hyeven, hdiff]
  have hx0 : 0 < x := Nat.lt_of_lt_of_le (by decide : 0 < 3) hx
  have hy0 : 0 < y := Nat.lt_of_lt_of_le (by decide : 0 < 3) hy
  have hz0 : 0 < z := Nat.lt_of_lt_of_le (by decide : 0 < 3) hz
  have hbc := beal_coprime_bc hA hB hC hx0 hy0 hz0 hgcd hsol
  exact ⟨hxodd, hdiff, hfac, hbc⟩

theorem beal_two_equal_even_diff_xz_progress
    {A B C : ℤ} {x y z : ℕ}
    (hx : 3 ≤ x) (hy : 3 ≤ y) (hz : 3 ≤ z)
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hgcd : bealGcd A B C = 1)
    (hd : bealExpGcd x y z = 1)
    (hxz : x = z) (hxeven : Even x)
    (hsol : A ^ x + B ^ y = C ^ z) :
    Odd y ∧
      C ^ x - A ^ x = B ^ y ∧
        (C ^ (x / 2) - A ^ (x / 2)) * (C ^ (x / 2) + A ^ (x / 2)) = B ^ y ∧
          Nat.Coprime A.natAbs C.natAbs := by
  have hyodd := beal_two_equal_even_diff_xz_y_odd hx hxz hd hxeven
  have hdiff := beal_two_equal_even_diff_xz_form hxz hsol
  have hfac : (C ^ (x / 2) - A ^ (x / 2)) * (C ^ (x / 2) + A ^ (x / 2)) = B ^ y := by
    rw [← even_pow_sub_eq_mul hxeven, hdiff]
  have hx0 : 0 < x := Nat.lt_of_lt_of_le (by decide : 0 < 3) hx
  have hy0 : 0 < y := Nat.lt_of_lt_of_le (by decide : 0 < 3) hy
  have hz0 : 0 < z := Nat.lt_of_lt_of_le (by decide : 0 < 3) hz
  have hac := beal_coprime_ac hA hB hC hx0 hy0 hz0 hgcd hsol
  exact ⟨hyodd, hdiff, hfac, hac⟩

/--
**Residual** (phase 7l): the even-difference factorization kernel —
no coprime solution of `D * E = A^x` arising from
`D = C^{n/2} - B^{n/2}`, `E = C^{n/2} + B^{n/2}` with even `n ≥ 4`, odd `x ≥ 3`,
and `Nat.Coprime B.natAbs C.natAbs`.
-/
def BealTwoEqualEvenDiffFactorResidual : Prop :=
  ∀ (A B C : ℤ) (x n : ℕ),
    3 ≤ x → 4 ≤ n → Even n → Odd x →
    A ≠ 0 → B ≠ 0 → C ≠ 0 →
    Nat.Coprime B.natAbs C.natAbs →
    (C ^ (n / 2) - B ^ (n / 2)) * (C ^ (n / 2) + B ^ (n / 2)) = A ^ x →
      False

/--
The factorization residual implies the full even-difference Beal residual
(both `y = z` and `x = z` orientations).
-/
theorem BealTwoEqualEvenDiffResidual_of_factor
    (hFac : BealTwoEqualEvenDiffFactorResidual) :
    BealTwoEqualEvenDiffResidual := by
  intro A B C x y z hx hy hz hA hB hC hgcd hd hpair hsol
  rcases hpair with ⟨hyz, hye⟩ | ⟨hxz, hxe⟩
  · obtain ⟨hxodd, _, hfac, hbc⟩ :=
      beal_two_equal_even_diff_yz_progress hx hy hz hA hB hC hgcd hd hyz hye hsol
    have hn4 : 4 ≤ y := by
      have : y ≠ 3 := fun h => by
        subst h; exact Nat.not_even_iff_odd.mpr (by decide : Odd 3) hye
      omega
    exact hFac A B C x y hx hn4 hye hxodd hA hB hC hbc hfac
  · obtain ⟨hyodd, _, hfac, hac⟩ :=
      beal_two_equal_even_diff_xz_progress hx hy hz hA hB hC hgcd hd hxz hxe hsol
    have hn4 : 4 ≤ x := by
      have : x ≠ 3 := fun h => by
        subst h; exact Nat.not_even_iff_odd.mpr (by decide : Odd 3) hxe
      omega
    -- Factor residual expects `Nat.Coprime B.natAbs C.natAbs`; here bases are A,C
    -- after swapping roles to `D*E = B^y` with legs A,C.
    have hac' : Nat.Coprime A.natAbs C.natAbs := hac
    exact hFac B A C y x hy hn4 hxe hyodd hB hA hC hac' hfac

/-! ### Sum form splits (`z = 5` / `z ≥ 7`) and odd two-equal splits -/

/-- Sum residual outside Darmon–Merel, further split at hypotenuse exponent 5. -/
def BealTwoEqualEvenSumOutsideCubeResidual : Prop :=
  ∀ (A B C : ℤ) (x y z : ℕ) (_hx : 3 ≤ x) (_hy : 3 ≤ y) (_hz : 3 ≤ z)
    (_hA : A ≠ 0) (_hB : B ≠ 0) (_hC : C ≠ 0),
    bealGcd A B C = 1 →
    bealExpGcd x y z = 1 →
    x = y → Even x → z ≠ 3 →
      ¬ A ^ x + B ^ y = C ^ z

def BealTwoEqualEvenSumExpFiveResidual : Prop :=
  ∀ (A B C : ℤ) (x y z : ℕ) (_hx : 3 ≤ x) (_hy : 3 ≤ y) (_hz : 3 ≤ z)
    (_hA : A ≠ 0) (_hB : B ≠ 0) (_hC : C ≠ 0),
    bealGcd A B C = 1 →
    bealExpGcd x y z = 1 →
    x = y → Even x → z = 5 →
      ¬ A ^ x + B ^ y = C ^ z

def BealTwoEqualEvenSumExpGeSevenResidual : Prop :=
  ∀ (A B C : ℤ) (x y z : ℕ) (_hx : 3 ≤ x) (_hy : 3 ≤ y) (_hz : 3 ≤ z)
    (_hA : A ≠ 0) (_hB : B ≠ 0) (_hC : C ≠ 0),
    bealGcd A B C = 1 →
    bealExpGcd x y z = 1 →
    x = y → Even x → 7 ≤ z →
      ¬ A ^ x + B ^ y = C ^ z

theorem BealTwoEqualEvenSumOutsideCubeResidual_of_five_ge_seven
    (h5 : BealTwoEqualEvenSumExpFiveResidual)
    (h7 : BealTwoEqualEvenSumExpGeSevenResidual) :
    BealTwoEqualEvenSumOutsideCubeResidual := by
  intro A B C x y z hx hy hz hA hB hC hgcd hd hxy hxeven hz3 hsol
  have hzodd : Odd z :=
    (beal_two_equal_even_sum_gaussian hx hz hxy hd hxeven hA hB hC hgcd hsol).1
  have hzge4 : 4 ≤ z := by omega
  have : z = 5 ∨ 7 ≤ z := by
    have hne4 : z ≠ 4 := fun h => by
      subst h; exact Nat.not_odd_iff_even.mpr (by decide : Even 4) hzodd
    have hne6 : z ≠ 6 := fun h => by
      subst h; exact Nat.not_odd_iff_even.mpr (by decide : Even 6) hzodd
    omega
  rcases this with hz5 | hz7
  · exact h5 A B C x y z hx hy hz hA hB hC hgcd hd hxy hxeven hz5 hsol
  · exact h7 A B C x y z hx hy hz hA hB hC hgcd hd hxy hxeven hz7 hsol

theorem BealTwoEqualEvenSumResidual_of_five_ge_seven
    (h5 : BealTwoEqualEvenSumExpFiveResidual)
    (h7 : BealTwoEqualEvenSumExpGeSevenResidual) :
    BealTwoEqualEvenSumResidual :=
  BealTwoEqualEvenSumResidual_of_outside_cube
    (BealTwoEqualEvenSumOutsideCubeResidual_of_five_ge_seven h5 h7)

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
