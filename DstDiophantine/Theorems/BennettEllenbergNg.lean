import DstDiophantine.Theorems.BealEven
import Mathlib.Tactic.Linarith

/-!
# Fourth power plus a square (phase 7z)

mathlib (v4.34) does not contain Bennett–Ellenberg–Ng's theorem that
`A⁴ + B² = Cⁿ` has no nonzero coprime solution for `n ≥ 4`. We take that
statement as an `axiom` (same contract as `sumTwoFifthsNotSeventhOrNineteenth`)
and close every even two-equal sum whose common exponent is divisible by `4`
and whose hypotenuse exponent is at least `4`.

The rewrite is `A^{4k} + B^{4k} = (A^k)⁴ + (B^{2k})²`. A prime dividing two of
the new bases divides the third, so three-way coprimality survives. `(4,4,7)`
is the first case inside the `z ≥ 7` leaf; `(8,8,7)` and `(4,4,9)` close with
it. The common exponent `10` is twice an odd integer, so `(10,10,7)` does not
rewrite to this equation; phase 8a closes it as a sum of two fifth powers.
An even difference with `d = 1` does not become this equation: the distinct
exponent is odd. Classical Beal is **not** claimed unconditionally.
-/

namespace DstDiophantine

namespace Theorems

/--
Bennett–Ellenberg–Ng (2010): no nonzero coprime solution of `A⁴ + B² = Cⁿ`
for an integer `n ≥ 4`.

Not present in mathlib at the pin used by this project; recorded explicitly as
an axiom rather than smuggled into a `sorry`. This is **not** a Lean proof of
Bennett–Ellenberg–Ng. A vanishing coordinate satisfies the equation
(`0⁴ + 1² = 1ⁿ`) and is excluded here: it is not a Beal solution. Signs on
`A` and `B` are absorbed by the even powers, and a negative `C` with odd `n`
makes the right side negative.
-/
axiom bennettEllenbergNg :
    ∀ (A B C : ℤ) (n : ℕ),
      4 ≤ n →
      A ≠ 0 → B ≠ 0 → C ≠ 0 →
      Nat.gcd A.natAbs (Nat.gcd B.natAbs C.natAbs) = 1 →
      ¬ A ^ 4 + B ^ 2 = C ^ n

/--
Two equal exponents divisible by `4`, and a third exponent at least `4`.
The Beal sum `A^x + B^x = C^z` then rewrites as a fourth power plus a square.
-/
def IsFourthSumShape (x y z : ℕ) : Prop :=
  x = y ∧ 4 ∣ x ∧ 4 ≤ z

instance {x y z : ℕ} : Decidable (IsFourthSumShape x y z) := by
  unfold IsFourthSumShape
  infer_instance

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

/--
No coprime nonzero Beal sum `A^x + B^x = C^z` with `4 ∣ x` and `z ≥ 4`.
-/
theorem not_beal_fourth_sum
    {A B C : ℤ} {x z : ℕ}
    (hx : 3 ≤ x) (hz : 4 ≤ z)
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hgcd : bealGcd A B C = 1)
    (h4 : 4 ∣ x)
    (hsol : A ^ x + B ^ x = C ^ z) : False := by
  obtain ⟨k, hk⟩ := h4
  have hk0 : 0 < k := by
    have : 3 ≤ 4 * k := by simpa [hk] using hx
    omega
  have hA4 : (A ^ k) ^ 4 = A ^ x := by
    rw [← pow_mul, mul_comm, hk]
  have hB2 : (B ^ (2 * k)) ^ 2 = B ^ x := by
    have hmul : (2 * k) * 2 = x := by
      rw [hk]
      omega
    rw [← pow_mul, hmul]
  have hsol' : (A ^ k) ^ 4 + (B ^ (2 * k)) ^ 2 = C ^ z := by
    rw [hA4, hB2]
    exact hsol
  have hgcd' : bealGcd (A ^ k) (B ^ (2 * k)) C = 1 :=
    bealGcd_pow_pow_eq_one hk0 (by omega : 0 < 2 * k) hA hgcd
  exact bennettEllenbergNg (A ^ k) (B ^ (2 * k)) C z hz
    (pow_ne_zero k hA) (pow_ne_zero (2 * k) hB) hC
    (by simpa [bealGcd] using hgcd') hsol'

/--
No coprime nonzero Beal solution whose exponents are a fourth-power sum shape.
-/
theorem not_beal_fourth_sum_shape
    {A B C : ℤ} {x y z : ℕ}
    (hx : 3 ≤ x) (_hy : 3 ≤ y) (_hz : 3 ≤ z)
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hgcd : bealGcd A B C = 1)
    (hshape : IsFourthSumShape x y z)
    (hsol : A ^ x + B ^ y = C ^ z) : False := by
  obtain ⟨hxy, h4, hz4⟩ := hshape
  subst hxy
  exact not_beal_fourth_sum hx hz4 hA hB hC hgcd h4 hsol

/--
**Residual** (phase 7z, unproved): even-sum body at hypotenuse exponent
`z ≥ 7`, outside cube-pair shapes and outside a common exponent divisible
by `4`. `(4,4,7)` is removed. `(10,10,7)` is not this shape; phase 8a
removes it as a fifth-power pair. The live body is the further narrowing
`BealTwoEqualEvenSumExpGeSevenOutsideFourthFifthResidual`.
-/
def BealTwoEqualEvenSumExpGeSevenOutsideFourthResidual : Prop :=
  ∀ (A B C : ℤ) (x y z : ℕ) (_hx : 3 ≤ x) (_hy : 3 ≤ y) (_hz : 3 ≤ z)
    (_hA : A ≠ 0) (_hB : B ≠ 0) (_hC : C ≠ 0),
    bealGcd A B C = 1 →
    bealExpGcd x y z = 1 →
    x = y → Even x → 7 ≤ z →
    ¬ IsCubePairPowerShape x y z →
    ¬ 4 ∣ x →
      ¬ A ^ x + B ^ y = C ^ z

/--
The even-sum body outside cube pairs follows once a common exponent divisible
by `4` has also been removed.
-/
theorem BealTwoEqualEvenSumExpGeSevenOutsideCubePairResidual_of_outside_fourth
    (hOut : BealTwoEqualEvenSumExpGeSevenOutsideFourthResidual) :
    BealTwoEqualEvenSumExpGeSevenOutsideCubePairResidual := by
  intro A B C x y z hx hy hz hA hB hC hgcd hd hxy hxeven hz7 hshape hsol
  by_cases h4 : 4 ∣ x
  · subst hxy
    exact not_beal_fourth_sum hx (by omega) hA hB hC hgcd h4 hsol
  · exact hOut A B C x y z hx hy hz hA hB hC hgcd hd hxy hxeven hz7 hshape h4 hsol

/--
Phase 7z: the even-sum residual follows from the `z ≥ 7` body outside cube
pairs and outside a common exponent divisible by `4`.
-/
theorem BealTwoEqualEvenSumResidual_of_ge_seven_outside_fourth
    (h7 : BealTwoEqualEvenSumExpGeSevenOutsideFourthResidual) :
    BealTwoEqualEvenSumResidual :=
  BealTwoEqualEvenSumResidual_of_ge_seven_outside_cube_pair
    (BealTwoEqualEvenSumExpGeSevenOutsideCubePairResidual_of_outside_fourth h7)

end Theorems

end DstDiophantine
