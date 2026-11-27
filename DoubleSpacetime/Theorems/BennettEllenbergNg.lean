import DoubleSpacetime.Theorems.BealEven
import Mathlib.Tactic.Linarith

/-!
# Fourth power plus a square

`bennettEllenbergNg` assumes no nonzero coprime `A⁴ + B² = Cⁿ` for `n ≥ 4`. It is an axiom, not a
Lean proof; classical Beal is not claimed and `BealTwoEqualEvenSumExpGeSevenOutsideFourthResidual`
stays open.
-/

namespace DoubleSpacetime

namespace Theorems

/-- No nonzero coprime `A⁴ + B² = Cⁿ` for `n ≥ 4`. An axiom, not a Lean proof. -/
axiom bennettEllenbergNg :
    ∀ (A B C : ℤ) (n : ℕ),
      4 ≤ n →
      A ≠ 0 → B ≠ 0 → C ≠ 0 →
      Nat.gcd A.natAbs (Nat.gcd B.natAbs C.natAbs) = 1 →
      ¬ A ^ 4 + B ^ 2 = C ^ n

/-- Equal exponents divisible by `4`: the sum is a fourth power plus a square. -/
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

/-- Open: even sum `z ≥ 7` outside cube pairs and `4 ∣ x`. Not `(10,10,7)`. -/
def BealTwoEqualEvenSumExpGeSevenOutsideFourthResidual : Prop :=
  ∀ (A B C : ℤ) (x y z : ℕ) (_hx : 3 ≤ x) (_hy : 3 ≤ y) (_hz : 3 ≤ z)
    (_hA : A ≠ 0) (_hB : B ≠ 0) (_hC : C ≠ 0),
    bealGcd A B C = 1 →
    bealExpGcd x y z = 1 →
    x = y → Even x → 7 ≤ z →
    ¬ IsCubePairPowerShape x y z →
    ¬ 4 ∣ x →
      ¬ A ^ x + B ^ y = C ^ z

theorem BealTwoEqualEvenSumExpGeSevenOutsideCubePairResidual_of_outside_fourth
    (hOut : BealTwoEqualEvenSumExpGeSevenOutsideFourthResidual) :
    BealTwoEqualEvenSumExpGeSevenOutsideCubePairResidual := by
  intro A B C x y z hx hy hz hA hB hC hgcd hd hxy hxeven hz7 hshape hsol
  by_cases h4 : 4 ∣ x
  · subst hxy
    exact not_beal_fourth_sum hx (by omega) hA hB hC hgcd h4 hsol
  · exact hOut A B C x y z hx hy hz hA hB hC hgcd hd hxy hxeven hz7 hshape h4 hsol

theorem BealTwoEqualEvenSumResidual_of_ge_seven_outside_fourth
    (h7 : BealTwoEqualEvenSumExpGeSevenOutsideFourthResidual) :
    BealTwoEqualEvenSumResidual :=
  BealTwoEqualEvenSumResidual_of_ge_seven_outside_cube_pair
    (BealTwoEqualEvenSumExpGeSevenOutsideCubePairResidual_of_outside_fourth h7)

end Theorems

end DoubleSpacetime
