import DstDiophantine.Theorems.BealGaussian
import DstDiophantine.Theorems.BealMixed
import DstDiophantine.Theorems.DarmonMerel
import DstDiophantine.Logic.Geometric
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.Tactic.Linarith

/-!
# Phase 7k / 7m / 7o / 7r: even two-equal residual split (sum vs difference)

Splits `BealTwoEqualEvenResidual` into:

* **sum form** `x = y` even — Gaussian hypotenuse power
  `(A^{x/2})² + (B^{x/2})² = C^z`;
* **difference form** `y = z` or `x = z` with even common exponent —
  `C^n − B^n = A^x` (does **not** lift to a Gaussian hypotenuse power).

The sum form with `z = 3` is closed by Darmon–Merel. Phase 7o extracts signed
/`2`-stripped perfect powers from the difference factor kernel and packages the
live body as `BealTwoEqualEvenDiffPerfectPowerResidual`. Phase 7r records that
sum (Gaussian / cyclic) and diff (hyperbolic factor) interfere and must not
share a CGA dilation no-go. Classical Beal is **not** claimed unconditionally.
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

/-! ### Even-difference factor kernel: `gcd ∣ 2` and 2-adic packaging -/

/--
`Int.gcd (C^k − B^k) (C^k + B^k)` divides `2` when `B, C` are coprime in absolute
value. Odd common prime factors would divide both `B` and `C`.
-/
theorem int_gcd_pow_diff_sum_dvd_two {B C : ℤ} {k : ℕ}
    (hcop : Nat.Coprime B.natAbs C.natAbs) :
    Int.gcd (C ^ k - B ^ k) (C ^ k + B ^ k) ∣ 2 := by
  set D := C ^ k - B ^ k
  set E := C ^ k + B ^ k
  have hED : E - D = 2 * B ^ k := by ring
  have hDE : D + E = 2 * C ^ k := by ring
  have hgcdD : Int.gcd D E = Int.gcd D (2 * B ^ k) := by
    rw [← hED, Int.gcd_sub_self_right]
  have hgcdE : Int.gcd D E = Int.gcd (2 * C ^ k) E := by
    rw [← hDE, ← Int.gcd_add_self_left]
  have hdB : (Int.gcd D E : ℤ) ∣ 2 * B ^ k := by
    rw [hgcdD]; exact Int.gcd_dvd_right _ _
  have hdC : (Int.gcd D E : ℤ) ∣ 2 * C ^ k := by
    rw [hgcdE]; exact Int.gcd_dvd_left _ _
  have hgB : Int.gcd D E ∣ (2 * B ^ k).natAbs := Int.natCast_dvd.mp hdB
  have hgC : Int.gcd D E ∣ (2 * C ^ k).natAbs := Int.natCast_dvd.mp hdC
  have h2B : (2 * B ^ k).natAbs = 2 * B.natAbs ^ k := by
    rw [Int.natAbs_mul, Int.natAbs_pow]; rfl
  have h2C : (2 * C ^ k).natAbs = 2 * C.natAbs ^ k := by
    rw [Int.natAbs_mul, Int.natAbs_pow]; rfl
  rw [h2B] at hgB; rw [h2C] at hgC
  have hdiv : Int.gcd D E ∣ Nat.gcd (2 * B.natAbs ^ k) (2 * C.natAbs ^ k) :=
    Nat.dvd_gcd hgB hgC
  have hgcd2 : Nat.gcd (2 * B.natAbs ^ k) (2 * C.natAbs ^ k) = 2 := by
    have hpow : Nat.gcd (B.natAbs ^ k) (C.natAbs ^ k) = 1 :=
      Nat.pow_gcd_pow_of_gcd_eq_one (Nat.coprime_iff_gcd_eq_one.mp hcop)
    calc Nat.gcd (2 * B.natAbs ^ k) (2 * C.natAbs ^ k)
        = 2 * Nat.gcd (B.natAbs ^ k) (C.natAbs ^ k) := Nat.gcd_mul_left _ _ _
      _ = 2 := by rw [hpow]
  rwa [hgcd2] at hdiv

/-- Absolute-value form of the gcd bound. -/
theorem nat_gcd_pow_diff_sum_dvd_two {B C : ℤ} {k : ℕ}
    (hcop : Nat.Coprime B.natAbs C.natAbs) :
    Nat.gcd (C ^ k - B ^ k).natAbs (C ^ k + B ^ k).natAbs ∣ 2 := by
  simpa [Int.gcd] using int_gcd_pow_diff_sum_dvd_two (B := B) (C := C) (k := k) hcop

/-- Opposite parity of `B, C` with `k > 0` forces both conjugate factors odd. -/
theorem odd_pow_diff_sum_of_opposite_parity {B C : ℤ} {k : ℕ}
    (hk : 0 < k)
    (hpar : (Even B ∧ Odd C) ∨ (Odd B ∧ Even C)) :
    Odd (C ^ k - B ^ k) ∧ Odd (C ^ k + B ^ k) := by
  have hk0 : k ≠ 0 := Nat.pos_iff_ne_zero.mp hk
  rcases hpar with ⟨hBe, hCo⟩ | ⟨hBo, hCe⟩
  · have hBk : Even (B ^ k) := hBe.pow_of_ne_zero hk0
    have hCk : Odd (C ^ k) := Odd.pow (n := k) hCo
    exact ⟨hCk.sub_even hBk, hCk.add_even hBk⟩
  · have hBk : Odd (B ^ k) := Odd.pow (n := k) hBo
    have hCk : Even (C ^ k) := hCe.pow_of_ne_zero hk0
    exact ⟨hCk.sub_odd hBk, hCk.add_odd hBk⟩

/-- Opposite parity of `B, C` forces gcd of absolute values to be `1`. -/
theorem nat_gcd_pow_diff_sum_eq_one_of_opposite_parity {B C : ℤ} {k : ℕ}
    (hk : 0 < k)
    (hpar : (Even B ∧ Odd C) ∨ (Odd B ∧ Even C))
    (hcop : Nat.Coprime B.natAbs C.natAbs) :
    Nat.gcd (C ^ k - B ^ k).natAbs (C ^ k + B ^ k).natAbs = 1 := by
  obtain ⟨hDo, _hEo⟩ := odd_pow_diff_sum_of_opposite_parity hk hpar
  have hdiv := nat_gcd_pow_diff_sum_dvd_two (B := B) (C := C) (k := k) hcop
  have hoddg : Odd (Nat.gcd (C ^ k - B ^ k).natAbs (C ^ k + B ^ k).natAbs) := by
    refine Nat.not_even_iff_odd.mp ?_
    intro he
    have h2 : 2 ∣ Nat.gcd (C ^ k - B ^ k).natAbs (C ^ k + B ^ k).natAbs :=
      even_iff_two_dvd.mp he
    have : 2 ∣ (C ^ k - B ^ k).natAbs :=
      dvd_trans h2 (Nat.gcd_dvd_left _ _)
    exact Nat.not_odd_iff_even.mpr (even_iff_two_dvd.mpr this) (Int.natAbs_odd.mpr hDo)
  rcases (Nat.dvd_prime Nat.prime_two).1 hdiv with h1 | h2
  · exact h1
  · exact False.elim (Nat.not_odd_iff_even.mpr (by rw [h2]; decide) hoddg)

/-- Both `B, C` odd forces both conjugate factors even and gcd exactly `2`. -/
theorem nat_gcd_pow_diff_sum_eq_two_of_both_odd {B C : ℤ} {k : ℕ}
    (hB : Odd B) (hC : Odd C)
    (hcop : Nat.Coprime B.natAbs C.natAbs) :
    Even (C ^ k - B ^ k) ∧ Even (C ^ k + B ^ k) ∧
      Nat.gcd (C ^ k - B ^ k).natAbs (C ^ k + B ^ k).natAbs = 2 := by
  have hDe : Even (C ^ k - B ^ k) :=
    (Odd.pow (n := k) hC).sub_odd (Odd.pow (n := k) hB)
  have hEe : Even (C ^ k + B ^ k) :=
    (Odd.pow (n := k) hC).add_odd (Odd.pow (n := k) hB)
  refine ⟨hDe, hEe, ?_⟩
  have hdiv := nat_gcd_pow_diff_sum_dvd_two (B := B) (C := C) (k := k) hcop
  have h2D : 2 ∣ (C ^ k - B ^ k).natAbs :=
    Int.natCast_dvd.mp (even_iff_two_dvd.mp hDe)
  have h2E : 2 ∣ (C ^ k + B ^ k).natAbs :=
    Int.natCast_dvd.mp (even_iff_two_dvd.mp hEe)
  have h2g : 2 ∣ Nat.gcd (C ^ k - B ^ k).natAbs (C ^ k + B ^ k).natAbs :=
    Nat.dvd_gcd h2D h2E
  rcases (Nat.dvd_prime Nat.prime_two).1 hdiv with h1 | h2
  · exact False.elim ((by decide : ¬ 2 ∣ (1 : ℕ)) (by rwa [h1] at h2g))
  · exact h2

/--
When both bases are odd, the conjugate factors cannot both be divisible by `4`,
so at least one has 2-adic valuation exactly `1`.
-/
theorem exists_padicValNat_two_eq_one_of_both_odd {B C : ℤ} {k : ℕ}
    (hB : Odd B) (hC : Odd C) (hk : 0 < k)
    (hD0 : C ^ k - B ^ k ≠ 0) (hE0 : C ^ k + B ^ k ≠ 0) :
    padicValNat 2 (C ^ k - B ^ k).natAbs = 1 ∨
      padicValNat 2 (C ^ k + B ^ k).natAbs = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hDe : Even (C ^ k - B ^ k) :=
    (Odd.pow (n := k) hC).sub_odd (Odd.pow (n := k) hB)
  have hEe : Even (C ^ k + B ^ k) :=
    (Odd.pow (n := k) hC).add_odd (Odd.pow (n := k) hB)
  have h2D : 2 ∣ (C ^ k - B ^ k).natAbs :=
    Int.natCast_dvd.mp (even_iff_two_dvd.mp hDe)
  have h2E : 2 ∣ (C ^ k + B ^ k).natAbs :=
    Int.natCast_dvd.mp (even_iff_two_dvd.mp hEe)
  have hDne : (C ^ k - B ^ k).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hD0
  have hEne : (C ^ k + B ^ k).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hE0
  have hgeD : 1 ≤ padicValNat 2 (C ^ k - B ^ k).natAbs :=
    (padicValNat_dvd_iff_le hDne (n := 1)).mp h2D
  have hgeE : 1 ≤ padicValNat 2 (C ^ k + B ^ k).natAbs :=
    (padicValNat_dvd_iff_le hEne (n := 1)).mp h2E
  have hnot4 : ¬ (4 ∣ (C ^ k - B ^ k).natAbs ∧ 4 ∣ (C ^ k + B ^ k).natAbs) := by
    intro ⟨h4D, h4E⟩
    have h4Dz : (4 : ℤ) ∣ C ^ k - B ^ k := Int.natCast_dvd.mpr h4D
    have h4Ez : (4 : ℤ) ∣ C ^ k + B ^ k := Int.natCast_dvd.mpr h4E
    have h4diff : (4 : ℤ) ∣ (C ^ k + B ^ k) - (C ^ k - B ^ k) := dvd_sub h4Ez h4Dz
    have hED : (C ^ k + B ^ k) - (C ^ k - B ^ k) = 2 * B ^ k := by ring
    rw [hED] at h4diff
    have h2Bk : (2 : ℤ) ∣ B ^ k := by
      obtain ⟨t, ht⟩ := h4diff
      refine ⟨t, mul_left_cancel₀ (by decide : (2 : ℤ) ≠ 0) ?_⟩
      calc (2 : ℤ) * B ^ k = 4 * t := ht
        _ = 2 * (2 * t) := by ring
    have h2B : (2 : ℤ) ∣ B :=
      (Int.prime_two.dvd_pow_iff_dvd (Nat.pos_iff_ne_zero.mp hk)).mp h2Bk
    exact Int.not_odd_iff_even.mpr (even_iff_two_dvd.mpr h2B) hB
  by_cases h4D : 4 ∣ (C ^ k - B ^ k).natAbs
  · have h4E : ¬ 4 ∣ (C ^ k + B ^ k).natAbs := fun h => hnot4 ⟨h4D, h⟩
    refine Or.inr ?_
    have hlt : padicValNat 2 (C ^ k + B ^ k).natAbs < 2 := by
      rw [← not_le]
      intro hle
      exact h4E ((padicValNat_dvd_iff_le hEne (n := 2)).mpr hle)
    omega
  · refine Or.inl ?_
    have hlt : padicValNat 2 (C ^ k - B ^ k).natAbs < 2 := by
      rw [← not_le]
      intro hle
      exact h4D ((padicValNat_dvd_iff_le hDne (n := 2)).mpr hle)
    omega

/-! ### Phase 7o: perfect-power extraction from the factor kernel -/

/--
If absolute values are coprime and their product is an `x`-th power, each is an
`x`-th power (ℕ UFD).
-/
theorem exists_natAbs_pow_of_mul_eq_pow_of_coprime_abs {D E A : ℤ} {x : ℕ}
    (hcop : Nat.Coprime D.natAbs E.natAbs)
    (heq : D * E = A ^ x) :
    ∃ u v : ℕ, D.natAbs = u ^ x ∧ E.natAbs = v ^ x := by
  have hprod : D.natAbs * E.natAbs = A.natAbs ^ x := by
    have := congrArg Int.natAbs heq
    simpa [Int.natAbs_mul, Int.natAbs_pow] using this
  obtain ⟨u, hu⟩ := nat_eq_pow_of_mul_eq_pow_of_coprime hcop hprod
  obtain ⟨v, hv⟩ := nat_eq_pow_of_mul_eq_pow_of_coprime_right hcop hprod
  exact ⟨u, v, hu, hv⟩

/--
Signed form: `n.natAbs = u^e` yields `n = ± (u : ℤ)^e`.
-/
theorem exists_signed_pow_of_natAbs_eq_pow {n : ℤ} {u e : ℕ}
    (h : n.natAbs = u ^ e) :
    n = (u : ℤ) ^ e ∨ n = -((u : ℤ) ^ e) := by
  have : n.natAbs = ((u : ℤ) ^ e).natAbs := by
    rw [h, Int.natAbs_pow, Int.natAbs_natCast]
  exact (Int.natAbs_eq_natAbs_iff).1 this

/--
Opposite-parity conjugate factors with product an `x`-th power are each
absolute `x`-th powers (`gcd` of absolute values is 1).
-/
theorem exists_signed_pow_of_diff_sum_mul_eq_pow_opposite_parity
    {B C A : ℤ} {k x : ℕ}
    (hk : 0 < k)
    (hpar : (Even B ∧ Odd C) ∨ (Odd B ∧ Even C))
    (hcop : Nat.Coprime B.natAbs C.natAbs)
    (heq : (C ^ k - B ^ k) * (C ^ k + B ^ k) = A ^ x) :
    ∃ u v : ℕ,
      (C ^ k - B ^ k).natAbs = u ^ x ∧
        (C ^ k + B ^ k).natAbs = v ^ x := by
  have hgcd1 :=
    nat_gcd_pow_diff_sum_eq_one_of_opposite_parity hk hpar hcop
  exact exists_natAbs_pow_of_mul_eq_pow_of_coprime_abs
    (Nat.coprime_iff_gcd_eq_one.mpr hgcd1) heq

/--
Both-odd conjugate factors: absolute gcd is exactly 2, and at least one factor
has 2-adic valuation exactly 1.
-/
theorem diff_sum_mul_eq_pow_both_odd_gcd_padic
    {B C : ℤ} {k : ℕ}
    (hk : 0 < k)
    (hB : Odd B) (hC : Odd C)
    (hcop : Nat.Coprime B.natAbs C.natAbs)
    (hD0 : C ^ k - B ^ k ≠ 0) (hE0 : C ^ k + B ^ k ≠ 0) :
    Nat.gcd (C ^ k - B ^ k).natAbs (C ^ k + B ^ k).natAbs = 2 ∧
      (padicValNat 2 (C ^ k - B ^ k).natAbs = 1 ∨
        padicValNat 2 (C ^ k + B ^ k).natAbs = 1) := by
  exact ⟨(nat_gcd_pow_diff_sum_eq_two_of_both_odd hB hC hcop).2.2,
    exists_padicValNat_two_eq_one_of_both_odd hB hC hk hD0 hE0⟩

/--
If `D * E = A^x` with `Nat.gcd D E = 2` and both nonzero, the 2-free parts of
`D` and `E` are each `x`-th powers.
-/
theorem exists_odd_parts_pow_of_mul_eq_pow_gcd_two
    {D E A x : ℕ} (_hx : 0 < x)
    (hgcd : Nat.gcd D E = 2)
    (hD0 : D ≠ 0) (hE0 : E ≠ 0)
    (hprod : D * E = A ^ x) :
    ∃ u v : ℕ,
      D / 2 ^ padicValNat 2 D = u ^ x ∧
        E / 2 ^ padicValNat 2 E = v ^ x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set a := padicValNat 2 D
  set b := padicValNat 2 E
  set d' := D / 2 ^ a
  set e' := E / 2 ^ b
  have hDa : 2 ^ a * d' = D := Nat.ordProj_mul_ordCompl_eq_self D 2
  have hEb : 2 ^ b * e' = E := Nat.ordProj_mul_ordCompl_eq_self E 2
  have hd'odd : ¬ 2 ∣ d' := by
    intro h2
    have hpow : 2 ^ (a + 1) = 2 ^ a * 2 := by rw [pow_succ]
    have : 2 ^ (a + 1) ∣ D := by
      rw [← hDa, hpow]
      exact mul_dvd_mul_left _ h2
    have : a + 1 ≤ padicValNat 2 D :=
      (padicValNat_dvd_iff_le hD0 (n := a + 1)).mp this
    omega
  have he'odd : ¬ 2 ∣ e' := by
    intro h2
    have hpow : 2 ^ (b + 1) = 2 ^ b * 2 := by rw [pow_succ]
    have : 2 ^ (b + 1) ∣ E := by
      rw [← hEb, hpow]
      exact mul_dvd_mul_left _ h2
    have : b + 1 ≤ padicValNat 2 E :=
      (padicValNat_dvd_iff_le hE0 (n := b + 1)).mp this
    omega
  have hcopde : Nat.Coprime d' e' := by
    -- Any common prime dividing d' and e' divides gcd(D,E)=2, but d',e' are odd.
    refine Nat.coprime_iff_gcd_eq_one.mpr ?_
    have hdiv : Nat.gcd d' e' ∣ Nat.gcd D E := by
      have hdD : Nat.gcd d' e' ∣ D := by
        have : Nat.gcd d' e' ∣ d' := Nat.gcd_dvd_left _ _
        have : Nat.gcd d' e' ∣ 2 ^ a * d' := dvd_mul_of_dvd_right this _
        rwa [hDa] at this
      have heE : Nat.gcd d' e' ∣ E := by
        have : Nat.gcd d' e' ∣ e' := Nat.gcd_dvd_right _ _
        have : Nat.gcd d' e' ∣ 2 ^ b * e' := dvd_mul_of_dvd_right this _
        rwa [hEb] at this
      exact Nat.dvd_gcd hdD heE
    have hdiv2 : Nat.gcd d' e' ∣ 2 := by rwa [hgcd] at hdiv
    have hodd : ¬ 2 ∣ Nat.gcd d' e' := by
      intro h2
      exact hd'odd (dvd_trans h2 (Nat.gcd_dvd_left _ _))
    rcases (Nat.dvd_prime Nat.prime_two).1 hdiv2 with h1 | h2
    · exact h1
    · exact False.elim (hodd (by rw [h2]))
  have h2copd : Nat.Coprime (2 ^ (a + b)) d' :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hd'odd |>.pow_left _
  have h2cope : Nat.Coprime (2 ^ (a + b)) e' :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 he'odd |>.pow_left _
  have hcop2de : Nat.Coprime (2 ^ (a + b)) (d' * e') :=
    Nat.Coprime.mul_right h2copd h2cope
  have hprod' : 2 ^ (a + b) * (d' * e') = A ^ x := by
    calc 2 ^ (a + b) * (d' * e')
        = (2 ^ a * d') * (2 ^ b * e') := by
            rw [pow_add]; ring
      _ = D * E := by rw [hDa, hEb]
      _ = A ^ x := hprod
  obtain ⟨t, ht⟩ :=
    nat_eq_pow_of_mul_eq_pow_of_coprime_right hcop2de hprod'
  obtain ⟨u, hu⟩ := nat_eq_pow_of_mul_eq_pow_of_coprime hcopde ht
  obtain ⟨v, hv⟩ := nat_eq_pow_of_mul_eq_pow_of_coprime_right hcopde ht
  exact ⟨u, v, hu, hv⟩

/--
Both-odd conjugate factors with product an `x`-th power: gcd = 2, one
valuation is exactly 1, and the 2-free parts are `x`-th powers.
-/
theorem exists_odd_pow_parts_of_diff_sum_mul_eq_pow_both_odd
    {B C A : ℤ} {k x : ℕ}
    (hk : 0 < k) (hx : 0 < x)
    (hB : Odd B) (hC : Odd C)
    (hcop : Nat.Coprime B.natAbs C.natAbs)
    (hD0 : C ^ k - B ^ k ≠ 0) (hE0 : C ^ k + B ^ k ≠ 0)
    (heq : (C ^ k - B ^ k) * (C ^ k + B ^ k) = A ^ x) :
    Nat.gcd (C ^ k - B ^ k).natAbs (C ^ k + B ^ k).natAbs = 2 ∧
      (padicValNat 2 (C ^ k - B ^ k).natAbs = 1 ∨
        padicValNat 2 (C ^ k + B ^ k).natAbs = 1) ∧
        ∃ u v : ℕ,
          (C ^ k - B ^ k).natAbs /
              2 ^ padicValNat 2 (C ^ k - B ^ k).natAbs = u ^ x ∧
            (C ^ k + B ^ k).natAbs /
                2 ^ padicValNat 2 (C ^ k + B ^ k).natAbs = v ^ x := by
  obtain ⟨hgcd2, hv2⟩ :=
    diff_sum_mul_eq_pow_both_odd_gcd_padic hk hB hC hcop hD0 hE0
  refine ⟨hgcd2, hv2, ?_⟩
  have hprod : (C ^ k - B ^ k).natAbs * (C ^ k + B ^ k).natAbs =
      A.natAbs ^ x := by
    have := congrArg Int.natAbs heq
    simpa [Int.natAbs_mul, Int.natAbs_pow] using this
  exact exists_odd_parts_pow_of_mul_eq_pow_gcd_two hx hgcd2
    (Int.natAbs_ne_zero.mpr hD0) (Int.natAbs_ne_zero.mpr hE0) hprod

/--
**Residual** (phase 7o): no even-difference conjugate configuration in the
opposite-parity or both-odd branches (the only branches compatible with
`Nat.Coprime B.natAbs C.natAbs`). Extraction shows those branches yield signed
/`2`-stripped perfect `x`-th powers; this residual packages that live body.
It does **not** close the descent to a smaller Fermat equation.
-/
def BealTwoEqualEvenDiffPerfectPowerResidual : Prop :=
  ∀ (A B C : ℤ) (x n : ℕ),
    3 ≤ x → 4 ≤ n → Even n → Odd x →
    A ≠ 0 → B ≠ 0 → C ≠ 0 →
    Nat.Coprime B.natAbs C.natAbs →
    (C ^ (n / 2) - B ^ (n / 2)) * (C ^ (n / 2) + B ^ (n / 2)) = A ^ x →
      ¬ (((Even B ∧ Odd C) ∨ (Odd B ∧ Even C)) ∨ (Odd B ∧ Odd C))

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
Phase 7o assembly: perfect-power residual (opposite-parity / both-odd) implies
the factorization residual. Both-even bases contradict
`Nat.Coprime B.natAbs C.natAbs`.
-/
theorem BealTwoEqualEvenDiffFactorResidual_of_perfect_power
    (hPow : BealTwoEqualEvenDiffPerfectPowerResidual) :
    BealTwoEqualEvenDiffFactorResidual := by
  intro A B C x n hx hn hne hxodd hA hB hC hcop heq
  have hpar :
      ((Even B ∧ Odd C) ∨ (Odd B ∧ Even C)) ∨ (Odd B ∧ Odd C) ∨
        (Even B ∧ Even C) := by
    cases Nat.even_or_odd B.natAbs with
    | inl hBe =>
      cases Nat.even_or_odd C.natAbs with
      | inl hCe =>
        exact Or.inr (Or.inr ⟨Int.natAbs_even.mp hBe, Int.natAbs_even.mp hCe⟩)
      | inr hCo =>
        exact Or.inl (Or.inl ⟨Int.natAbs_even.mp hBe, Int.natAbs_odd.mp hCo⟩)
    | inr hBo =>
      cases Nat.even_or_odd C.natAbs with
      | inl hCe =>
        exact Or.inl (Or.inr ⟨Int.natAbs_odd.mp hBo, Int.natAbs_even.mp hCe⟩)
      | inr hCo =>
        exact Or.inr (Or.inl ⟨Int.natAbs_odd.mp hBo, Int.natAbs_odd.mp hCo⟩)
  rcases hpar with h | h | ⟨hBe, hCe⟩
  · exact hPow A B C x n hx hn hne hxodd hA hB hC hcop heq (Or.inl h)
  · exact hPow A B C x n hx hn hne hxodd hA hB hC hcop heq (Or.inr h)
  · have h2B : 2 ∣ B.natAbs := even_iff_two_dvd.mp (Int.natAbs_even.mpr hBe)
    have h2C : 2 ∣ C.natAbs := even_iff_two_dvd.mp (Int.natAbs_even.mpr hCe)
    have : 2 ∣ Nat.gcd B.natAbs C.natAbs := Nat.dvd_gcd h2B h2C
    have h1 : Nat.gcd B.natAbs C.natAbs = 1 :=
      Nat.coprime_iff_gcd_eq_one.mp hcop
    exact absurd (by rwa [h1] at this) (by decide : ¬ 2 ∣ (1 : ℕ))

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

/-! ### Phase 7r: sector diagnostics (sum = cyclic, diff = hyperbolic) -/

/-
Even-sum already packages as Gaussian hypotenuse
(`beal_two_equal_even_sum_gaussian` — cyclic / rotation sector).
Even-diff packages as hyperbolic factors
(`beal_two_equal_even_diff_yz_progress`). Distinct axes interfere, so the
two forms must not share a single CGA dilation no-go.
-/

/-- Hyperbolic and cyclic generators on distinct axes do not commute. -/
theorem beal_even_sum_diff_sectors_interfere :
    Logic.interfere Logic.axis0Boost Logic.axis1Rotation ≠ 0 :=
  Logic.interfere_axis0_axis1_ne_zero

end Theorems

end DstDiophantine
