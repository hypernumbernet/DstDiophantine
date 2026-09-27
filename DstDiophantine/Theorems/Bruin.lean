import DstDiophantine.Theorems.BealMixed
import Mathlib.Data.Int.Basic
import Mathlib.Tactic.Linarith

/-!
# Sums of two cubes as perfect powers (phase 7v / 7w)

mathlib (v4.34) does not contain the theorems that a coprime sum of two cubes
is never an `n`-th power for `3 ≤ n ≤ 10^9`, nor for every even `n ≥ 4`.
We take that classical statement as an `axiom` (same contract as
`darmonMerelCube` / `fermatSignatureNN5`).

* The bound `3 ≤ n ≤ 10^9` is the compilation of Bruin, Chen–Siksek, Dahmen,
  Freitas and Kraus recorded by Bennett–Bruni–Freitas.
* The even family `n = 2k` with `k ≥ 2` is Bennett–Chen–Dahmen–Yazdani:
  `a³ + b³ = c^{2k}` has no nonzero coprime solution.

Bruin's fourth and fifth powers are the first two cases (`bruinSumTwoCubes`
is derived, not a separate axiom). The exponent `3` is odd, so each placement
of the repeated exponent rewrites, by moving one cube across the equation,
into `a³ + b³ = cⁿ`.

Phase 7x: divisibility by `3` returns to the same equation. If two Beal
exponents are multiples of `3`, those powers are cubes of powers of the
original bases. Carrying either cube across the equation absorbs only a sign.
Whenever the remaining exponent is a `TwoCubeExponent`, the solution is
impossible. This cuts across the exponent-gcd stratification: it does not
require `d = 1`. Classical Beal is **not** claimed unconditionally.
-/

namespace DstDiophantine

namespace Theorems

/--
Two exponents equal `3` and the third equals `4` or `5`, in any position.
-/
def IsBruinTwoCubeShape (x y z : ℕ) : Prop :=
  (x = 3 ∧ y = 3 ∧ (z = 4 ∨ z = 5)) ∨
    (y = 3 ∧ z = 3 ∧ (x = 4 ∨ x = 5)) ∨
      (x = 3 ∧ z = 3 ∧ (y = 4 ∨ y = 5))

instance {x y z : ℕ} : Decidable (IsBruinTwoCubeShape x y z) := by
  unfold IsBruinTwoCubeShape
  infer_instance

/--
Companion exponents for which a coprime sum of two cubes is not an `n`-th power:
the range `3 ≤ n ≤ 10^9`, or any even `n ≥ 4`.
-/
def TwoCubeExponent (n : ℕ) : Prop :=
  (3 ≤ n ∧ n ≤ 1000000000) ∨ (4 ≤ n ∧ 2 ∣ n)

instance : DecidablePred TwoCubeExponent := by
  intro n
  unfold TwoCubeExponent
  infer_instance

/--
Two exponents equal `3` and the third is a `TwoCubeExponent`, in any position.
Bruin's shapes `(3,3,4)` and `(3,3,5)` are the first cases.
-/
def IsTwoCubePowerShape (x y z : ℕ) : Prop :=
  (x = 3 ∧ y = 3 ∧ TwoCubeExponent z) ∨
    (y = 3 ∧ z = 3 ∧ TwoCubeExponent x) ∨
      (x = 3 ∧ z = 3 ∧ TwoCubeExponent y)

instance {x y z : ℕ} : Decidable (IsTwoCubePowerShape x y z) := by
  unfold IsTwoCubePowerShape
  infer_instance

theorem TwoCubeExponent_of_four_or_five {n : ℕ} (h : n = 4 ∨ n = 5) :
    TwoCubeExponent n := by
  rcases h with rfl | rfl
  · exact Or.inl ⟨by decide, by decide⟩
  · exact Or.inl ⟨by decide, by decide⟩

theorem IsTwoCubePowerShape_of_bruin {x y z : ℕ} (h : IsBruinTwoCubeShape x y z) :
    IsTwoCubePowerShape x y z := by
  rcases h with ⟨hx, hy, hz⟩ | ⟨hy, hz, hx⟩ | ⟨hx, hz, hy⟩
  · exact Or.inl ⟨hx, hy, TwoCubeExponent_of_four_or_five hz⟩
  · exact Or.inr (Or.inl ⟨hy, hz, TwoCubeExponent_of_four_or_five hx⟩)
  · exact Or.inr (Or.inr ⟨hx, hz, TwoCubeExponent_of_four_or_five hy⟩)

/--
No nonzero coprime solution of `a³ + b³ = cⁿ` when `3 ≤ n ≤ 10^9`, and none
when `n` is even and `n ≥ 4`.

Not present in mathlib at the pin used by this project; recorded explicitly as
an axiom rather than smuggled into a `sorry`. This is **not** a Lean proof of
the cited theorems. On this equation a three-way gcd of `1` is the coprimality
hypothesis of the classical statements (a prime dividing two bases divides the
third).
-/
axiom sumTwoCubesNotPerfectPower :
    ∀ (a b c : ℤ) (n : ℕ),
      ((3 ≤ n ∧ n ≤ 1000000000) ∨ (4 ≤ n ∧ 2 ∣ n)) →
      a ≠ 0 → b ≠ 0 → c ≠ 0 →
      Nat.gcd a.natAbs (Nat.gcd b.natAbs c.natAbs) = 1 →
      ¬ a ^ 3 + b ^ 3 = c ^ n

/--
Bruin (2000), recovered from `sumTwoCubesNotPerfectPower`: no nonzero coprime
solution of `a³ + b³ = cⁿ` for `n = 4` or `n = 5`.
-/
theorem bruinSumTwoCubes :
    ∀ (a b c : ℤ) (n : ℕ),
      (n = 4 ∨ n = 5) →
      a ≠ 0 → b ≠ 0 → c ≠ 0 →
      Nat.gcd a.natAbs (Nat.gcd b.natAbs c.natAbs) = 1 →
      ¬ a ^ 3 + b ^ 3 = c ^ n := by
  intro a b c n hn hA hB hC hgcd hsol
  apply sumTwoCubesNotPerfectPower a b c n ?_ hA hB hC hgcd hsol
  rcases hn with rfl | rfl
  · exact Or.inl ⟨by decide, by decide⟩
  · exact Or.inl ⟨by decide, by decide⟩

/-- Abbreviation for the two-cube fourth/fifth-power hypothesis. -/
abbrev BruinSumTwoCubesHyp : Prop :=
  ∀ (a b c : ℤ) (n : ℕ),
    (n = 4 ∨ n = 5) → a ≠ 0 → b ≠ 0 → c ≠ 0 →
      Nat.gcd a.natAbs (Nat.gcd b.natAbs c.natAbs) = 1 →
      ¬ a ^ 3 + b ^ 3 = c ^ n

private theorem bealGcd_neg_permute (A B C : ℤ) :
    bealGcd C (-B) A = bealGcd A B C ∧ bealGcd C (-A) B = bealGcd A B C := by
  constructor <;> simp [bealGcd, Nat.gcd_comm, Nat.gcd_left_comm]

private theorem odd_pow_add_neg {X Y : ℤ} {n : ℕ} (hodd : Odd n) :
    X ^ n + (-Y) ^ n = X ^ n - Y ^ n := by
  rw [Odd.neg_pow hodd Y]; ring

/--
Phase 7v: a coprime Beal solution whose exponents are a two-cube fourth or
fifth power is impossible.
-/
theorem not_beal_bruin_two_cube_shape_of
    (hBr : BruinSumTwoCubesHyp)
    {A B C : ℤ} {x y z : ℕ}
    (_hx : 3 ≤ x) (_hy : 3 ≤ y) (_hz : 3 ≤ z)
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hgcd : bealGcd A B C = 1)
    (_hd : bealExpGcd x y z = 1)
    (hshape : IsBruinTwoCubeShape x y z)
    (hsol : A ^ x + B ^ y = C ^ z) : False := by
  rcases hshape with ⟨hx3, hy3, hz45⟩ | ⟨hy3, hz3, hx45⟩ | ⟨hx3, hz3, hy45⟩
  · subst hx3; subst hy3
    exact hBr A B C z hz45 hA hB hC hgcd hsol
  · subst hy3; subst hz3
    have hrew : C ^ 3 + (-B) ^ 3 = A ^ x := by
      rw [odd_pow_add_neg (by decide : Odd 3)]
      linarith [hsol]
    have hgcd' : bealGcd C (-B) A = 1 := by
      rw [(bealGcd_neg_permute A B C).1]; exact hgcd
    exact hBr C (-B) A x hx45 hC (neg_ne_zero.mpr hB) hA hgcd' hrew
  · subst hx3; subst hz3
    have hrew : C ^ 3 + (-A) ^ 3 = B ^ y := by
      rw [odd_pow_add_neg (by decide : Odd 3)]
      linarith [hsol]
    have hgcd' : bealGcd C (-A) B = 1 := by
      rw [(bealGcd_neg_permute A B C).2]; exact hgcd
    exact hBr C (-A) B y hy45 hC (neg_ne_zero.mpr hA) hB hgcd' hrew

/--
Two of the three exponents are divisible by `3`, and the remaining exponent
is a `TwoCubeExponent` (the range in which a coprime sum of two cubes is never
a perfect power). The repeated exponent need not equal `3`.
-/
def IsCubePairPowerShape (x y z : ℕ) : Prop :=
  (3 ∣ x ∧ 3 ∣ y ∧ TwoCubeExponent z) ∨
    (3 ∣ y ∧ 3 ∣ z ∧ TwoCubeExponent x) ∨
      (3 ∣ x ∧ 3 ∣ z ∧ TwoCubeExponent y)

instance {x y z : ℕ} : Decidable (IsCubePairPowerShape x y z) := by
  unfold IsCubePairPowerShape
  infer_instance

theorem IsCubePairPowerShape_of_twoCube {x y z : ℕ}
    (h : IsTwoCubePowerShape x y z) : IsCubePairPowerShape x y z := by
  rcases h with ⟨hx, hy, hz⟩ | ⟨hy, hz, hx⟩ | ⟨hx, hz, hy⟩
  · subst hx; subst hy
    exact Or.inl ⟨Nat.dvd_refl 3, Nat.dvd_refl 3, hz⟩
  · subst hy; subst hz
    exact Or.inr (Or.inl ⟨Nat.dvd_refl 3, Nat.dvd_refl 3, hx⟩)
  · subst hx; subst hz
    exact Or.inr (Or.inr ⟨Nat.dvd_refl 3, Nat.dvd_refl 3, hy⟩)

private theorem zpow_mul_div_three {A : ℤ} {n : ℕ} (h : 3 ∣ n) :
    (A ^ (n / 3)) ^ 3 = A ^ n := by
  rw [← pow_mul, Nat.div_mul_cancel h]

private theorem pos_div_three_of_dvd {n : ℕ} (hn : 3 ≤ n) (h : 3 ∣ n) :
    0 < n / 3 := by
  have hmul : 3 * (n / 3) = n := Nat.mul_div_cancel' h
  have hne : n / 3 ≠ 0 := by
    intro hz
    simp [hz] at hmul
    omega
  exact Nat.pos_of_ne_zero hne

private theorem bealGcd_pow_pow_eq_one {A B C : ℤ} {r s : ℕ}
    (_hr : 0 < r) (_hs : 0 < s) (hA : A ≠ 0)
    (hgcd : bealGcd A B C = 1) :
    bealGcd (A ^ r) (B ^ s) C = 1 := by
  by_contra hne
  have hgt : 1 < bealGcd (A ^ r) (B ^ s) C := by
    have hpos : 0 < bealGcd (A ^ r) (B ^ s) C :=
      bealGcd_pos (pow_ne_zero r hA)
    omega
  obtain ⟨p, hp, hpA, hpB, hpC⟩ := exists_common_prime_of_bealGcd_gt_one hgt
  have hpA' : p ∣ A.natAbs :=
    hp.dvd_of_dvd_pow (by simpa [Int.natAbs_pow] using hpA)
  have hpB' : p ∣ B.natAbs :=
    hp.dvd_of_dvd_pow (by simpa [Int.natAbs_pow] using hpB)
  have : p ∣ bealGcd A B C := Nat.dvd_gcd hpA' (Nat.dvd_gcd hpB' hpC)
  rw [hgcd] at this
  exact hp.not_dvd_one this

private theorem bealGcd_pow_cross_eq_one {A B C : ℤ} {r s : ℕ}
    (_hr : 0 < r) (_hs : 0 < s) (hC : C ≠ 0)
    (hgcd : bealGcd A B C = 1) :
    bealGcd (C ^ r) (B ^ s) A = 1 := by
  by_contra hne
  have hgt : 1 < bealGcd (C ^ r) (B ^ s) A := by
    have hpos : 0 < bealGcd (C ^ r) (B ^ s) A :=
      bealGcd_pos (pow_ne_zero r hC)
    omega
  obtain ⟨p, hp, hpC, hpB, hpA⟩ := exists_common_prime_of_bealGcd_gt_one hgt
  have hpC' : p ∣ C.natAbs :=
    hp.dvd_of_dvd_pow (by simpa [Int.natAbs_pow] using hpC)
  have hpB' : p ∣ B.natAbs :=
    hp.dvd_of_dvd_pow (by simpa [Int.natAbs_pow] using hpB)
  have : p ∣ bealGcd A B C := Nat.dvd_gcd hpA (Nat.dvd_gcd hpB' hpC')
  rw [hgcd] at this
  exact hp.not_dvd_one this

private theorem bealGcd_neg_pow_cross_eq_one {A B C : ℤ} {r s : ℕ}
    (hr : 0 < r) (hs : 0 < s) (hC : C ≠ 0)
    (hgcd : bealGcd A B C = 1) :
    bealGcd (C ^ r) (-(B ^ s)) A = 1 := by
  simpa [bealGcd, Int.natAbs_neg] using bealGcd_pow_cross_eq_one hr hs hC hgcd

/--
Phase 7x: if two exponents are divisible by `3` and the third is a
`TwoCubeExponent`, a three-way-coprime solution is impossible.

The two powers divisible by `3` are cubes. The exponent `3` is odd, so moving
either cube across the equation changes only a sign, and the resulting
equation is a coprime sum of two cubes equal to a perfect power.
-/
theorem not_beal_cube_pair_power_shape
    {A B C : ℤ} {x y z : ℕ}
    (hx : 3 ≤ x) (hy : 3 ≤ y) (hz : 3 ≤ z)
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hgcd : bealGcd A B C = 1)
    (hshape : IsCubePairPowerShape x y z)
    (hsol : A ^ x + B ^ y = C ^ z) : False := by
  rcases hshape with ⟨hx3, hy3, hzN⟩ | ⟨hy3, hz3, hxN⟩ | ⟨hx3, hz3, hyN⟩
  · have hxr : 0 < x / 3 := pos_div_three_of_dvd hx hx3
    have hyr : 0 < y / 3 := pos_div_three_of_dvd hy hy3
    have hgcd' := bealGcd_pow_pow_eq_one hxr hyr hA hgcd
    have hsol' :
        (A ^ (x / 3)) ^ 3 + (B ^ (y / 3)) ^ 3 = C ^ z := by
      rw [zpow_mul_div_three hx3, zpow_mul_div_three hy3]
      exact hsol
    exact sumTwoCubesNotPerfectPower (A ^ (x / 3)) (B ^ (y / 3)) C z hzN
      (pow_ne_zero _ hA) (pow_ne_zero _ hB) hC hgcd' hsol'
  · have hzr : 0 < z / 3 := pos_div_three_of_dvd hz hz3
    have hyr : 0 < y / 3 := pos_div_three_of_dvd hy hy3
    have hrew :
        (C ^ (z / 3)) ^ 3 + (-(B ^ (y / 3))) ^ 3 = A ^ x := by
      have hcub := odd_pow_add_neg (X := C ^ (z / 3)) (Y := B ^ (y / 3))
        (by decide : Odd 3)
      rw [hcub, zpow_mul_div_three hz3, zpow_mul_div_three hy3]
      linarith [hsol]
    have hgcd' := bealGcd_neg_pow_cross_eq_one hzr hyr hC hgcd
    exact sumTwoCubesNotPerfectPower (C ^ (z / 3)) (-(B ^ (y / 3))) A x hxN
      (pow_ne_zero _ hC) (neg_ne_zero.mpr (pow_ne_zero _ hB)) hA hgcd' hrew
  · have hzr : 0 < z / 3 := pos_div_three_of_dvd hz hz3
    have hxr : 0 < x / 3 := pos_div_three_of_dvd hx hx3
    have hrew :
        (C ^ (z / 3)) ^ 3 + (-(A ^ (x / 3))) ^ 3 = B ^ y := by
      have hcub := odd_pow_add_neg (X := C ^ (z / 3)) (Y := A ^ (x / 3))
        (by decide : Odd 3)
      rw [hcub, zpow_mul_div_three hz3, zpow_mul_div_three hx3]
      linarith [hsol]
    have hgcd' :=
      bealGcd_neg_pow_cross_eq_one (A := B) (B := A) hzr hxr hC
        (by simpa [bealGcd, Nat.gcd_left_comm] using hgcd)
    exact sumTwoCubesNotPerfectPower (C ^ (z / 3)) (-(A ^ (x / 3))) B y hyN
      (pow_ne_zero _ hC) (neg_ne_zero.mpr (pow_ne_zero _ hA)) hB hgcd' hrew

/--
Phase 7w: a coprime Beal solution whose exponents are a repeated cube beside a
`TwoCubeExponent` is impossible, in every position.
-/
theorem not_beal_two_cube_power_shape
    {A B C : ℤ} {x y z : ℕ}
    (_hx : 3 ≤ x) (_hy : 3 ≤ y) (_hz : 3 ≤ z)
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hgcd : bealGcd A B C = 1)
    (_hd : bealExpGcd x y z = 1)
    (hshape : IsTwoCubePowerShape x y z)
    (hsol : A ^ x + B ^ y = C ^ z) : False := by
  rcases hshape with ⟨hx3, hy3, hzN⟩ | ⟨hy3, hz3, hxN⟩ | ⟨hx3, hz3, hyN⟩
  · subst hx3; subst hy3
    exact sumTwoCubesNotPerfectPower A B C z hzN hA hB hC hgcd hsol
  · subst hy3; subst hz3
    have hrew : C ^ 3 + (-B) ^ 3 = A ^ x := by
      rw [odd_pow_add_neg (by decide : Odd 3)]
      linarith [hsol]
    have hgcd' : bealGcd C (-B) A = 1 := by
      rw [(bealGcd_neg_permute A B C).1]; exact hgcd
    exact sumTwoCubesNotPerfectPower C (-B) A x hxN hC (neg_ne_zero.mpr hB) hA hgcd' hrew
  · subst hx3; subst hz3
    have hrew : C ^ 3 + (-A) ^ 3 = B ^ y := by
      rw [odd_pow_add_neg (by decide : Odd 3)]
      linarith [hsol]
    have hgcd' : bealGcd C (-A) B = 1 := by
      rw [(bealGcd_neg_permute A B C).2]; exact hgcd
    exact sumTwoCubesNotPerfectPower C (-A) B y hyN hC (neg_ne_zero.mpr hA) hB hgcd' hrew

/-- Phase 7v axiom form of the two-cube fourth/fifth-power slice. -/
theorem not_beal_bruin_two_cube_shape
    {A B C : ℤ} {x y z : ℕ}
    (hx : 3 ≤ x) (hy : 3 ≤ y) (hz : 3 ≤ z)
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hgcd : bealGcd A B C = 1)
    (hd : bealExpGcd x y z = 1)
    (hshape : IsBruinTwoCubeShape x y z)
    (hsol : A ^ x + B ^ y = C ^ z) : False :=
  not_beal_bruin_two_cube_shape_of bruinSumTwoCubes
    hx hy hz hA hB hC hgcd hd hshape hsol

/--
**Residual** (phase 7w, unproved): odd two-equal Beal outside the two-cube
power shapes. The removed shapes are `IsTwoCubePowerShape` (Bruin's fourth
and fifth powers, every companion through `10^9`, and every even companion
at least `4`).
-/
def BealTwoEqualOddOutsideBruinResidual : Prop :=
  ∀ (A B C : ℤ) (x y z : ℕ) (_hx : 3 ≤ x) (_hy : 3 ≤ y) (_hz : 3 ≤ z)
    (_hA : A ≠ 0) (_hB : B ≠ 0) (_hC : C ≠ 0),
    bealGcd A B C = 1 →
    bealExpGcd x y z = 1 →
    ((x = y ∧ Odd x) ∨ (y = z ∧ Odd y) ∨ (x = z ∧ Odd x)) →
    ¬ IsTwoCubePowerShape x y z →
      ¬ A ^ x + B ^ y = C ^ z

/--
Phase 7w: the odd two-equal residual follows from its body outside the
two-cube power shapes.
-/
theorem BealTwoEqualOddResidual_of_outside_bruin
    (hOut : BealTwoEqualOddOutsideBruinResidual) :
    BealTwoEqualOddResidual := by
  intro A B C x y z hx hy hz hA hB hC hgcd hd hpair hsol
  by_cases hshape : IsTwoCubePowerShape x y z
  · exact not_beal_two_cube_power_shape hx hy hz hA hB hC hgcd hd hshape hsol
  · exact hOut A B C x y z hx hy hz hA hB hC hgcd hd hpair hshape hsol

/--
**Residual** (phase 7x, unproved): odd two-equal Beal outside every cube-pair
shape. Repeated exponent `3` is the special case `IsTwoCubePowerShape`; a
repeated odd multiple of `3`, such as `9`, is removed by the same prohibition
whenever the companion is a `TwoCubeExponent`.
-/
def BealTwoEqualOddOutsideCubePairResidual : Prop :=
  ∀ (A B C : ℤ) (x y z : ℕ) (_hx : 3 ≤ x) (_hy : 3 ≤ y) (_hz : 3 ≤ z)
    (_hA : A ≠ 0) (_hB : B ≠ 0) (_hC : C ≠ 0),
    bealGcd A B C = 1 →
    bealExpGcd x y z = 1 →
    ((x = y ∧ Odd x) ∨ (y = z ∧ Odd y) ∨ (x = z ∧ Odd x)) →
    ¬ IsCubePairPowerShape x y z →
      ¬ A ^ x + B ^ y = C ^ z

/--
Phase 7x: the odd two-equal residual follows from its body outside cube-pair
shapes. Those shapes are a coprime sum of two cubes.
-/
theorem BealTwoEqualOddResidual_of_outside_cube_pair
    (hOut : BealTwoEqualOddOutsideCubePairResidual) :
    BealTwoEqualOddResidual := by
  intro A B C x y z hx hy hz hA hB hC hgcd hd hpair hsol
  by_cases hshape : IsCubePairPowerShape x y z
  · exact not_beal_cube_pair_power_shape hx hy hz hA hB hC hgcd hshape hsol
  · exact hOut A B C x y z hx hy hz hA hB hC hgcd hd hpair hshape hsol

/--
**Residual** (phase 7x, unproved): pairwise distinct exponents outside
cube-pair shapes. Signature `(3,4,5)` is removed separately.
-/
def BealAllDistinctOutsideCubePairResidual : Prop :=
  ∀ (A B C : ℤ) (x y z : ℕ) (_hx : 3 ≤ x) (_hy : 3 ≤ y) (_hz : 3 ≤ z)
    (_hA : A ≠ 0) (_hB : B ≠ 0) (_hC : C ≠ 0),
    bealGcd A B C = 1 →
    bealExpGcd x y z = 1 →
    x ≠ y → y ≠ z → x ≠ z →
    ¬ IsCubePairPowerShape x y z →
      ¬ A ^ x + B ^ y = C ^ z

theorem BealAllDistinctExpResidual_of_outside_cube_pair
    (hOut : BealAllDistinctOutsideCubePairResidual) :
    BealAllDistinctExpResidual := by
  intro A B C x y z hx hy hz hA hB hC hgcd hd hxy hyz hxz hsol
  by_cases hshape : IsCubePairPowerShape x y z
  · exact not_beal_cube_pair_power_shape hx hy hz hA hB hC hgcd hshape hsol
  · exact hOut A B C x y z hx hy hz hA hB hC hgcd hd hxy hyz hxz hshape hsol

/--
**Residual** (phase 7x, unproved): unequal-odd Pythagorean body outside
cube-pair shapes. A signature such as `(6,12,10)` is a sum of two cubes and
is no longer part of this body.
-/
def BealPythagoreanUnequalOddOutsideCubePairResidual : Prop :=
  ∀ (A B C : ℤ) (x y z : ℕ) (_hx : 3 ≤ x) (_hy : 3 ≤ y) (_hz : 3 ≤ z)
    (_hA : A ≠ 0) (_hB : B ≠ 0) (_hC : C ≠ 0),
    bealGcd A B C = 1 →
    bealExpGcd x y z = 2 →
    ¬ (4 ∣ x ∧ 4 ∣ y) →
    ¬ (4 ∣ x ∧ 4 ∣ z) →
    ¬ (4 ∣ y ∧ 4 ∣ z) →
    ¬ (y = z ∧ Odd (y / 2) ∧ Even B) →
    ¬ (x = z ∧ Odd (x / 2) ∧ Even A) →
    ¬ IsCubePairPowerShape x y z →
      ¬ A ^ x + B ^ y = C ^ z

theorem BealPythagoreanUnequalOddResidual_of_outside_cube_pair
    (hOut : BealPythagoreanUnequalOddOutsideCubePairResidual) :
    BealPythagoreanUnequalOddResidual := by
  intro A B C x y z hx hy hz hA hB hC hgcd hd hxy hxz hyz hyzOdd hxzOdd hsol
  by_cases hshape : IsCubePairPowerShape x y z
  · exact not_beal_cube_pair_power_shape hx hy hz hA hB hC hgcd hshape hsol
  · exact hOut A B C x y z hx hy hz hA hB hC hgcd hd hxy hxz hyz hyzOdd hxzOdd
      hshape hsol

/-- `(6,6,7)` is a coprime sum of two cubes equal to a seventh power. -/
theorem not_beal_six_six_seven {A B C : ℤ}
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hgcd : bealGcd A B C = 1)
    (hsol : A ^ 6 + B ^ 6 = C ^ 7) : False :=
  not_beal_cube_pair_power_shape (by decide) (by decide) (by decide)
    hA hB hC hgcd (by decide) hsol

/-- `(9,9,4)` is a coprime sum of two cubes equal to a fourth power. -/
theorem not_beal_nine_nine_four {A B C : ℤ}
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hgcd : bealGcd A B C = 1)
    (hsol : A ^ 9 + B ^ 9 = C ^ 4) : False :=
  not_beal_cube_pair_power_shape (by decide) (by decide) (by decide)
    hA hB hC hgcd (by decide) hsol

/-- `(5,6,6)` is an even permutation of `(n,n,5)` and a coprime sum of two cubes. -/
theorem not_beal_five_six_six {A B C : ℤ}
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hgcd : bealGcd A B C = 1)
    (hsol : A ^ 5 + B ^ 6 = C ^ 6) : False :=
  not_beal_cube_pair_power_shape (by decide) (by decide) (by decide)
    hA hB hC hgcd (by decide) hsol

/-- `(3,6,5)` is a coprime sum of two cubes equal to a fifth power. -/
theorem not_beal_three_six_five {A B C : ℤ}
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hgcd : bealGcd A B C = 1)
    (hsol : A ^ 3 + B ^ 6 = C ^ 5) : False :=
  not_beal_cube_pair_power_shape (by decide) (by decide) (by decide)
    hA hB hC hgcd (by decide) hsol

end Theorems

end DstDiophantine
