import DstDiophantine.Theorems.DahmenSiksek
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Prime.Basic

/-!
# Even sums of two double-prime powers

`anniSiksekDoublePrimeSum` is Anni–Siksek, Theorem 1.1, for hypotenuse primes `7` and `11`,
together with Billerey–Chen–Dembélé–Dieulefait–Freitas, Corollary 8.2, which removes the
`ℓ, m ≠ 7` exception at hypotenuse `13`. `michaudJacobsPrimeSeventeenth` is the equal-exponent
case of Michaud-Jacobs, Theorem 3: primes other than `5`, hypotenuse `17`.
Each axiom is the cited statement, not a Lean proof of it. Classical Beal is not claimed.
`(10,10,23)` and `(14,14,19)` stay outside both statements.
-/

namespace DstDiophantine

namespace Theorems

/-- No nonzero coprime `a^{2ℓ} + b^{2m} = c^p` for primes `ℓ, m ≥ 5` and `p ∈ {7,11,13}`.
An axiom, not a proof of Anni–Siksek or of the Billerey–Chen–Dembélé–Dieulefait–Freitas
completion at `p = 13`. -/
axiom anniSiksekDoublePrimeSum :
    ∀ (a b c : ℤ) (ℓ m p : ℕ),
      Nat.Prime ℓ → Nat.Prime m → 5 ≤ ℓ → 5 ≤ m →
      (p = 7 ∨ p = 11 ∨ p = 13) →
      a ≠ 0 → b ≠ 0 → c ≠ 0 →
      Nat.gcd a.natAbs (Nat.gcd b.natAbs c.natAbs) = 1 →
      ¬ a ^ (2 * ℓ) + b ^ (2 * m) = c ^ p

/-- No nonzero coprime `a^{2ℓ} + b^{2m} = c^17` for primes `ℓ, m ≠ 5`.
An axiom, not a proof of Michaud-Jacobs, Theorem 3. The case `ℓ = m = 5` is Stoll's
`sumTwoFifthsNotStollPrime`, not this statement. -/
axiom michaudJacobsPrimeSeventeenth :
    ∀ (a b c : ℤ) (ℓ m : ℕ),
      Nat.Prime ℓ → Nat.Prime m → ℓ ≠ 5 → m ≠ 5 →
      a ≠ 0 → b ≠ 0 → c ≠ 0 →
      Nat.gcd a.natAbs (Nat.gcd b.natAbs c.natAbs) = 1 →
      ¬ a ^ (2 * ℓ) + b ^ (2 * m) = c ^ 17

/-- Equal exponents, one of them twice a prime at least `5`, hypotenuse divisible by `7`, `11`,
or `13`. `(22,22,7)` and `(14,14,13)` are this shape. -/
def IsAnniSiksekEvenSumShape (x y z : ℕ) : Prop :=
  x = y ∧
    (∃ ℓ, ℓ ≤ x ∧ Nat.Prime ℓ ∧ 5 ≤ ℓ ∧ 2 * ℓ ∣ x) ∧
    (7 ∣ z ∨ 11 ∣ z ∨ 13 ∣ z)

/-- Equal exponents, twice a prime other than `5`, hypotenuse divisible by `17`.
`(14,14,17)` is this shape. `(10,10,17)` is a fifth-power pair, not this shape. -/
def IsEqualEvenSeventeenthShape (x y z : ℕ) : Prop :=
  x = y ∧
    (∃ ℓ, ℓ ≤ x ∧ Nat.Prime ℓ ∧ ℓ ≠ 5 ∧ 2 * ℓ ∣ x) ∧
    17 ∣ z

private def hasAnniPrimeFactor (n : ℕ) : Bool :=
  (List.range (n + 1)).any fun ℓ => decide (Nat.Prime ℓ ∧ 5 ≤ ℓ ∧ 2 * ℓ ∣ n)

private theorem hasAnniPrimeFactor_iff {n : ℕ} :
    hasAnniPrimeFactor n = true ↔
      ∃ ℓ, ℓ ≤ n ∧ Nat.Prime ℓ ∧ 5 ≤ ℓ ∧ 2 * ℓ ∣ n := by
  unfold hasAnniPrimeFactor
  simp only [List.any_eq_true, List.mem_range, decide_eq_true_eq]
  constructor
  · rintro ⟨ℓ, hlt, hp, h5, hdiv⟩
    exact ⟨ℓ, Nat.lt_succ_iff.mp hlt, hp, h5, hdiv⟩
  · rintro ⟨ℓ, hle, hp, h5, hdiv⟩
    exact ⟨ℓ, Nat.lt_succ_iff.mpr hle, hp, h5, hdiv⟩

private def hasSeventeenthPrimeFactor (n : ℕ) : Bool :=
  (List.range (n + 1)).any fun ℓ => decide (Nat.Prime ℓ ∧ ℓ ≠ 5 ∧ 2 * ℓ ∣ n)

private theorem hasSeventeenthPrimeFactor_iff {n : ℕ} :
    hasSeventeenthPrimeFactor n = true ↔
      ∃ ℓ, ℓ ≤ n ∧ Nat.Prime ℓ ∧ ℓ ≠ 5 ∧ 2 * ℓ ∣ n := by
  unfold hasSeventeenthPrimeFactor
  simp only [List.any_eq_true, List.mem_range, decide_eq_true_eq]
  constructor
  · rintro ⟨ℓ, hlt, hp, hne, hdiv⟩
    exact ⟨ℓ, Nat.lt_succ_iff.mp hlt, hp, hne, hdiv⟩
  · rintro ⟨ℓ, hle, hp, hne, hdiv⟩
    exact ⟨ℓ, Nat.lt_succ_iff.mpr hle, hp, hne, hdiv⟩

instance {x y z : ℕ} : Decidable (IsAnniSiksekEvenSumShape x y z) :=
  decidable_of_iff
      (decide (x = y) && hasAnniPrimeFactor x &&
        decide (7 ∣ z ∨ 11 ∣ z ∨ 13 ∣ z) = true) <| by
    simp only [Bool.and_eq_true, decide_eq_true_eq, hasAnniPrimeFactor_iff,
      IsAnniSiksekEvenSumShape]
    constructor
    · rintro ⟨⟨hxy, hℓ⟩, hp⟩
      exact ⟨hxy, hℓ, hp⟩
    · rintro ⟨hxy, hℓ, hp⟩
      exact ⟨⟨hxy, hℓ⟩, hp⟩

instance {x y z : ℕ} : Decidable (IsEqualEvenSeventeenthShape x y z) :=
  decidable_of_iff
      (decide (x = y) && hasSeventeenthPrimeFactor x && decide (17 ∣ z) = true) <| by
    simp only [Bool.and_eq_true, decide_eq_true_eq, hasSeventeenthPrimeFactor_iff,
      IsEqualEvenSeventeenthShape]
    constructor
    · rintro ⟨⟨hxy, hℓ⟩, hp⟩
      exact ⟨hxy, hℓ, hp⟩
    · rintro ⟨hxy, hℓ, hp⟩
      exact ⟨⟨hxy, hℓ⟩, hp⟩

private theorem zpow_mul_div {A : ℤ} {n k : ℕ} (h : k ∣ n) :
    (A ^ (n / k)) ^ k = A ^ n := by
  rw [← pow_mul, Nat.div_mul_cancel h]

private theorem pos_div_of_dvd {n k : ℕ} (hn : 0 < n) (h : k ∣ n) :
    0 < n / k := by
  have hmul : k * (n / k) = n := Nat.mul_div_cancel' h
  have hne : n / k ≠ 0 := by
    intro hz
    simp [hz] at hmul
    omega
  exact Nat.pos_of_ne_zero hne

private theorem bealGcd_three_pow_eq_one {A B C : ℤ} {r s t : ℕ}
    (_hr : 0 < r) (_hs : 0 < s) (_ht : 0 < t) (hA : A ≠ 0)
    (hgcd : bealGcd A B C = 1) :
    bealGcd (A ^ r) (B ^ s) (C ^ t) = 1 := by
  by_contra hne
  have hgt : 1 < bealGcd (A ^ r) (B ^ s) (C ^ t) := by
    have hpos : 0 < bealGcd (A ^ r) (B ^ s) (C ^ t) :=
      bealGcd_pos (pow_ne_zero r hA)
    omega
  obtain ⟨p, hp, hpA, hpB, hpC⟩ := exists_common_prime_of_bealGcd_gt_one hgt
  have hpA' : p ∣ A.natAbs :=
    hp.dvd_of_dvd_pow (by simpa [Int.natAbs_pow] using hpA)
  have hpB' : p ∣ B.natAbs :=
    hp.dvd_of_dvd_pow (by simpa [Int.natAbs_pow] using hpB)
  have hpC' : p ∣ C.natAbs :=
    hp.dvd_of_dvd_pow (by simpa [Int.natAbs_pow] using hpC)
  have : p ∣ bealGcd A B C := Nat.dvd_gcd hpA' (Nat.dvd_gcd hpB' hpC')
  rw [hgcd] at this
  exact hp.not_dvd_one this

theorem not_beal_anni_siksek_even_sum
    {A B C : ℤ} {x y z : ℕ}
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hz : 0 < z)
    (hgcd : bealGcd A B C = 1)
    (hshape : IsAnniSiksekEvenSumShape x y z)
    (hsol : A ^ x + B ^ y = C ^ z) : False := by
  obtain ⟨rfl, ⟨ℓ, hℓle, hprime, hℓ5, hdiv⟩, hpz⟩ := hshape
  obtain ⟨p, hp, hdivp⟩ : ∃ p, (p = 7 ∨ p = 11 ∨ p = 13) ∧ p ∣ z := by
    rcases hpz with h7 | h11 | h13
    · exact ⟨7, Or.inl rfl, h7⟩
    · exact ⟨11, Or.inr (Or.inl rfl), h11⟩
    · exact ⟨13, Or.inr (Or.inr rfl), h13⟩
  have hx : 0 < x := lt_of_lt_of_le (by decide : (0 : ℕ) < 5) (hℓ5.trans hℓle)
  have hxt : 0 < x / (2 * ℓ) := pos_div_of_dvd hx hdiv
  have hzt : 0 < z / p := pos_div_of_dvd hz hdivp
  have hgcd' := bealGcd_three_pow_eq_one hxt hxt hzt hA hgcd
  have hsol' :
      (A ^ (x / (2 * ℓ))) ^ (2 * ℓ) + (B ^ (x / (2 * ℓ))) ^ (2 * ℓ) =
        (C ^ (z / p)) ^ p := by
    rw [zpow_mul_div hdiv, zpow_mul_div hdiv, zpow_mul_div hdivp]
    exact hsol
  exact anniSiksekDoublePrimeSum
    (A ^ (x / (2 * ℓ))) (B ^ (x / (2 * ℓ))) (C ^ (z / p))
    ℓ ℓ p hprime hprime hℓ5 hℓ5 hp
    (pow_ne_zero _ hA) (pow_ne_zero _ hB) (pow_ne_zero _ hC)
    (by simpa [bealGcd] using hgcd') hsol'

theorem not_beal_equal_even_seventeenth
    {A B C : ℤ} {x y z : ℕ}
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hz : 0 < z)
    (hgcd : bealGcd A B C = 1)
    (hshape : IsEqualEvenSeventeenthShape x y z)
    (hsol : A ^ x + B ^ y = C ^ z) : False := by
  obtain ⟨rfl, ⟨ℓ, hℓle, hprime, hne, hdiv⟩, hdiv17⟩ := hshape
  have hx : 0 < x := lt_of_lt_of_le (Nat.Prime.pos hprime) hℓle
  have hxt : 0 < x / (2 * ℓ) := pos_div_of_dvd hx hdiv
  have hzt : 0 < z / 17 := pos_div_of_dvd hz hdiv17
  have hgcd' := bealGcd_three_pow_eq_one hxt hxt hzt hA hgcd
  have hsol' :
      (A ^ (x / (2 * ℓ))) ^ (2 * ℓ) + (B ^ (x / (2 * ℓ))) ^ (2 * ℓ) =
        (C ^ (z / 17)) ^ 17 := by
    rw [zpow_mul_div hdiv, zpow_mul_div hdiv, zpow_mul_div hdiv17]
    exact hsol
  exact michaudJacobsPrimeSeventeenth
    (A ^ (x / (2 * ℓ))) (B ^ (x / (2 * ℓ))) (C ^ (z / 17))
    ℓ ℓ hprime hprime hne hne
    (pow_ne_zero _ hA) (pow_ne_zero _ hB) (pow_ne_zero _ hC)
    (by simpa [bealGcd] using hgcd') hsol'

theorem not_beal_twenty_two_twenty_two_seven {A B C : ℤ}
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hgcd : bealGcd A B C = 1)
    (hsol : A ^ 22 + B ^ 22 = C ^ 7) : False :=
  not_beal_anni_siksek_even_sum hA hB hC (by decide) hgcd (by decide) hsol

theorem not_beal_fourteen_fourteen_eleven {A B C : ℤ}
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hgcd : bealGcd A B C = 1)
    (hsol : A ^ 14 + B ^ 14 = C ^ 11) : False :=
  not_beal_anni_siksek_even_sum hA hB hC (by decide) hgcd (by decide) hsol

theorem not_beal_fourteen_fourteen_thirteen {A B C : ℤ}
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hgcd : bealGcd A B C = 1)
    (hsol : A ^ 14 + B ^ 14 = C ^ 13) : False :=
  not_beal_anni_siksek_even_sum hA hB hC (by decide) hgcd (by decide) hsol

theorem not_beal_fourteen_fourteen_seventeen {A B C : ℤ}
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hgcd : bealGcd A B C = 1)
    (hsol : A ^ 14 + B ^ 14 = C ^ 17) : False :=
  not_beal_equal_even_seventeenth hA hB hC (by decide) hgcd (by decide) hsol

/-- Open: even sum `z ≥ 7` outside the double-prime cuts.
`(22,22,7)` is `IsAnniSiksekEvenSumShape`. `(14,14,17)` is `IsEqualEvenSeventeenthShape`.
`(10,10,23)` and `(14,14,19)` remain. -/
def BealTwoEqualEvenSumExpGeSevenOutsideAnniSeventeenthResidual : Prop :=
  ∀ (A B C : ℤ) (x y z : ℕ) (_hx : 3 ≤ x) (_hy : 3 ≤ y) (_hz : 3 ≤ z)
    (_hA : A ≠ 0) (_hB : B ≠ 0) (_hC : C ≠ 0),
    bealGcd A B C = 1 →
    bealExpGcd x y z = 1 →
    x = y → Even x → 7 ≤ z →
    ¬ IsCubePairPowerShape x y z →
    ¬ 4 ∣ x →
    ¬ IsFifthPairPowerShape x y z →
    ¬ IsSharedExpCubeOrFifth x y z →
    ¬ IsAnniSiksekEvenSumShape x y z →
    ¬ IsEqualEvenSeventeenthShape x y z →
      ¬ A ^ x + B ^ y = C ^ z

theorem BealTwoEqualEvenSumExpGeSevenOutsideFourthFifthResidual_of_outside_anni
    (hOut : BealTwoEqualEvenSumExpGeSevenOutsideAnniSeventeenthResidual) :
    BealTwoEqualEvenSumExpGeSevenOutsideFourthFifthResidual := by
  intro A B C x y z hx hy hz hA hB hC hgcd hd hxy hxeven hz7 hshape h4 hfifth hshared hsol
  by_cases hanni : IsAnniSiksekEvenSumShape x y z
  · exact not_beal_anni_siksek_even_sum hA hB hC (by omega) hgcd hanni hsol
  · by_cases h17 : IsEqualEvenSeventeenthShape x y z
    · exact not_beal_equal_even_seventeenth hA hB hC (by omega) hgcd h17 hsol
    · exact hOut A B C x y z hx hy hz hA hB hC hgcd hd hxy hxeven hz7 hshape h4 hfifth
        hshared hanni h17 hsol

theorem BealTwoEqualEvenSumResidual_of_ge_seven_outside_anni
    (h7 : BealTwoEqualEvenSumExpGeSevenOutsideAnniSeventeenthResidual) :
    BealTwoEqualEvenSumResidual :=
  BealTwoEqualEvenSumResidual_of_ge_seven_outside_fourth_fifth
    (BealTwoEqualEvenSumExpGeSevenOutsideFourthFifthResidual_of_outside_anni h7)

/-- Open: unequal-odd body outside the double-prime cuts. `(22,22,14)` has left. -/
def BealPythagoreanUnequalOddOutsideAnniSeventeenthResidual : Prop :=
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
    ¬ IsFifthPairPowerShape x y z →
    ¬ IsSharedExpCubeOrFifth x y z →
    ¬ IsAnniSiksekEvenSumShape x y z →
    ¬ IsEqualEvenSeventeenthShape x y z →
      ¬ A ^ x + B ^ y = C ^ z

theorem BealPythagoreanUnequalOddOutsideFifthPairResidual_of_outside_anni
    (hOut : BealPythagoreanUnequalOddOutsideAnniSeventeenthResidual) :
    BealPythagoreanUnequalOddOutsideFifthPairResidual := by
  intro A B C x y z hx hy hz hA hB hC hgcd hd hxy hxz hyz hyzOdd hxzOdd hshape hfifth
    hshared hsol
  by_cases hanni : IsAnniSiksekEvenSumShape x y z
  · exact not_beal_anni_siksek_even_sum hA hB hC (by omega) hgcd hanni hsol
  · by_cases h17 : IsEqualEvenSeventeenthShape x y z
    · exact not_beal_equal_even_seventeenth hA hB hC (by omega) hgcd h17 hsol
    · exact hOut A B C x y z hx hy hz hA hB hC hgcd hd hxy hxz hyz hyzOdd hxzOdd
        hshape hfifth hshared hanni h17 hsol

theorem BealPythagoreanUnequalOddResidual_of_outside_anni
    (hOut : BealPythagoreanUnequalOddOutsideAnniSeventeenthResidual) :
    BealPythagoreanUnequalOddResidual :=
  BealPythagoreanUnequalOddResidual_of_outside_fifth_pair
    (BealPythagoreanUnequalOddOutsideFifthPairResidual_of_outside_anni hOut)

end Theorems

end DstDiophantine
