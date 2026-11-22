import DstDiophantine.Theorems.BennettEllenbergNg
import DstDiophantine.Theorems.Bruin
import Mathlib.Data.Int.Basic
import Mathlib.Tactic.Linarith

/-!
# Repeated fifth powers

`sumTwoFifthsNotSeventhOrNineteenth` assumes no nonzero coprime `a⁵ + b⁵ = cˡ` for `l = 7` or `19`.
It is an axiom, not a Lean proof of Dahmen–Siksek, and classical Beal is not claimed.
-/

namespace DstDiophantine

namespace Theorems

/-- Two of the exponents equal `5` and the third equals `l`, in any order. -/
def IsRepeatedFifthTo (l x y z : ℕ) : Prop :=
  (x = 5 ∧ y = 5 ∧ z = l) ∨
    (y = 5 ∧ z = 5 ∧ x = l) ∨
      (x = 5 ∧ z = 5 ∧ y = l)

instance {l x y z : ℕ} : Decidable (IsRepeatedFifthTo l x y z) := by
  unfold IsRepeatedFifthTo
  infer_instance

/-- Repeated `5` beside `7` or `19`. `(7,7,5)` is `(n,n,5)`, not this. -/
def IsRepeatedFifthShape (x y z : ℕ) : Prop :=
  IsRepeatedFifthTo 7 x y z ∨ IsRepeatedFifthTo 19 x y z

instance {x y z : ℕ} : Decidable (IsRepeatedFifthShape x y z) := by
  unfold IsRepeatedFifthShape
  infer_instance

/-- No nonzero coprime `a⁵ + b⁵ = cˡ` for `l ∈ {7,19}`. An axiom, not a proof. -/
axiom sumTwoFifthsNotSeventhOrNineteenth :
    ∀ (a b c : ℤ) (l : ℕ),
      (l = 7 ∨ l = 19) →
      a ≠ 0 → b ≠ 0 → c ≠ 0 →
      Nat.gcd a.natAbs (Nat.gcd b.natAbs c.natAbs) = 1 →
      ¬ a ^ 5 + b ^ 5 = c ^ l

private theorem odd_pow_neg {X : ℤ} {n : ℕ} (hodd : Odd n) : (-X) ^ n = - X ^ n :=
  Odd.neg_pow hodd X

private theorem bealGcd_fifth_perm (A B C : ℤ) :
    bealGcd C (-B) A = bealGcd A B C ∧
      bealGcd C (-A) B = bealGcd A B C := by
  constructor <;> simp [bealGcd, Nat.gcd_comm, Nat.gcd_left_comm]

theorem not_beal_repeated_fifth_to
    {A B C : ℤ} {x y z l : ℕ}
    (hl : l = 7 ∨ l = 19)
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hgcd : bealGcd A B C = 1)
    (hshape : IsRepeatedFifthTo l x y z)
    (hsol : A ^ x + B ^ y = C ^ z) : False := by
  rcases hshape with ⟨hx, hy, hz⟩ | ⟨hy, hz, hx⟩ | ⟨hx, hz, hy⟩
  · subst hx; subst hy
    rw [hz] at hsol
    exact sumTwoFifthsNotSeventhOrNineteenth A B C l hl hA hB hC hgcd hsol
  · subst hy; subst hz
    rw [hx] at hsol
    have hrew : C ^ 5 + (-B) ^ 5 = A ^ l := by
      rw [odd_pow_neg (by decide : Odd 5)]
      linarith [hsol]
    exact sumTwoFifthsNotSeventhOrNineteenth C (-B) A l hl hC
      (neg_ne_zero.mpr hB) hA ((bealGcd_fifth_perm A B C).1.trans hgcd) hrew
  · subst hx; subst hz
    rw [hy] at hsol
    have hrew : C ^ 5 + (-A) ^ 5 = B ^ l := by
      rw [odd_pow_neg (by decide : Odd 5)]
      linarith [hsol]
    exact sumTwoFifthsNotSeventhOrNineteenth C (-A) B l hl hC
      (neg_ne_zero.mpr hA) hB ((bealGcd_fifth_perm A B C).2.trans hgcd) hrew

theorem not_beal_repeated_fifth_shape
    {A B C : ℤ} {x y z : ℕ}
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hgcd : bealGcd A B C = 1)
    (hshape : IsRepeatedFifthShape x y z)
    (hsol : A ^ x + B ^ y = C ^ z) : False := by
  rcases hshape with h | h
  · exact not_beal_repeated_fifth_to (Or.inl rfl) hA hB hC hgcd h hsol
  · exact not_beal_repeated_fifth_to (Or.inr rfl) hA hB hC hgcd h hsol

/-- Open: odd two-equal outside cube pairs and a repeated five beside `7` or `19`. -/
def BealTwoEqualOddOutsideRepeatedFifthResidual : Prop :=
  ∀ (A B C : ℤ) (x y z : ℕ) (_hx : 3 ≤ x) (_hy : 3 ≤ y) (_hz : 3 ≤ z)
    (_hA : A ≠ 0) (_hB : B ≠ 0) (_hC : C ≠ 0),
    bealGcd A B C = 1 →
    bealExpGcd x y z = 1 →
    ((x = y ∧ Odd x) ∨ (y = z ∧ Odd y) ∨ (x = z ∧ Odd x)) →
    ¬ IsCubePairPowerShape x y z →
    ¬ IsRepeatedFifthShape x y z →
      ¬ A ^ x + B ^ y = C ^ z

theorem BealTwoEqualOddOutsideCubePairResidual_of_outside_repeated_fifth
    (hOut : BealTwoEqualOddOutsideRepeatedFifthResidual) :
    BealTwoEqualOddOutsideCubePairResidual := by
  intro A B C x y z hx hy hz hA hB hC hgcd hd hpair hcube hsol
  by_cases hfifth : IsRepeatedFifthShape x y z
  · exact not_beal_repeated_fifth_shape hA hB hC hgcd hfifth hsol
  · exact hOut A B C x y z hx hy hz hA hB hC hgcd hd hpair hcube hfifth hsol

theorem BealTwoEqualOddResidual_of_outside_repeated_fifth
    (hOut : BealTwoEqualOddOutsideRepeatedFifthResidual) :
    BealTwoEqualOddResidual :=
  BealTwoEqualOddResidual_of_outside_cube_pair
    (BealTwoEqualOddOutsideCubePairResidual_of_outside_repeated_fifth hOut)

/-! ### Phase 8a: fifth-power pairs beside a multiple of `7` or `19` -/

/-- The remaining exponent is a seventh or a nineteenth power. -/
abbrev IsDahmenSiksekMultiple (n : ℕ) : Prop :=
  7 ∣ n ∨ 19 ∣ n

/-- Two exponents divisible by `5`, the third by `7` or `19`. -/
def IsFifthPairPowerShape (x y z : ℕ) : Prop :=
  (5 ∣ x ∧ 5 ∣ y ∧ IsDahmenSiksekMultiple z) ∨
    (5 ∣ y ∧ 5 ∣ z ∧ IsDahmenSiksekMultiple x) ∨
      (5 ∣ x ∧ 5 ∣ z ∧ IsDahmenSiksekMultiple y)

instance {x y z : ℕ} : Decidable (IsFifthPairPowerShape x y z) := by
  unfold IsFifthPairPowerShape
  infer_instance

theorem IsFifthPairPowerShape_of_repeated {x y z : ℕ}
    (h : IsRepeatedFifthShape x y z) : IsFifthPairPowerShape x y z := by
  rcases h with h7 | h19
  · rcases h7 with ⟨hx, hy, hz⟩ | ⟨hy, hz, hx⟩ | ⟨hx, hz, hy⟩
    · subst hx; subst hy; subst hz
      exact Or.inl ⟨Nat.dvd_refl 5, Nat.dvd_refl 5, Or.inl (Nat.dvd_refl 7)⟩
    · subst hy; subst hz; subst hx
      exact Or.inr (Or.inl ⟨Nat.dvd_refl 5, Nat.dvd_refl 5, Or.inl (Nat.dvd_refl 7)⟩)
    · subst hx; subst hz; subst hy
      exact Or.inr (Or.inr ⟨Nat.dvd_refl 5, Nat.dvd_refl 5, Or.inl (Nat.dvd_refl 7)⟩)
  · rcases h19 with ⟨hx, hy, hz⟩ | ⟨hy, hz, hx⟩ | ⟨hx, hz, hy⟩
    · subst hx; subst hy; subst hz
      exact Or.inl ⟨Nat.dvd_refl 5, Nat.dvd_refl 5, Or.inr (Nat.dvd_refl 19)⟩
    · subst hy; subst hz; subst hx
      exact Or.inr (Or.inl ⟨Nat.dvd_refl 5, Nat.dvd_refl 5, Or.inr (Nat.dvd_refl 19)⟩)
    · subst hx; subst hz; subst hy
      exact Or.inr (Or.inr ⟨Nat.dvd_refl 5, Nat.dvd_refl 5, Or.inr (Nat.dvd_refl 19)⟩)

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

private theorem bealGcd_eq_cba {A B C : ℤ} : bealGcd C B A = bealGcd A B C := by
  simp [bealGcd, Nat.gcd_comm, Nat.gcd_left_comm]

private theorem bealGcd_eq_cab {A B C : ℤ} : bealGcd C A B = bealGcd A B C := by
  simp [bealGcd, Nat.gcd_comm, Nat.gcd_left_comm]

private theorem exists_dahmen_divisor {n : ℕ} (h : IsDahmenSiksekMultiple n) :
    ∃ l, (l = 7 ∨ l = 19) ∧ l ∣ n := by
  rcases h with h7 | h19
  · exact ⟨7, Or.inl rfl, h7⟩
  · exact ⟨19, Or.inr rfl, h19⟩

theorem not_beal_fifth_pair_power_shape
    {A B C : ℤ} {x y z : ℕ}
    (hx : 3 ≤ x) (hy : 3 ≤ y) (hz : 3 ≤ z)
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hgcd : bealGcd A B C = 1)
    (hshape : IsFifthPairPowerShape x y z)
    (hsol : A ^ x + B ^ y = C ^ z) : False := by
  rcases hshape with ⟨hx5, hy5, hzD⟩ | ⟨hy5, hz5, hxD⟩ | ⟨hx5, hz5, hyD⟩
  · obtain ⟨l, hl, hdiv⟩ := exists_dahmen_divisor hzD
    have hxr : 0 < x / 5 := pos_div_of_dvd (by omega) hx5
    have hyr : 0 < y / 5 := pos_div_of_dvd (by omega) hy5
    have hzt : 0 < z / l := pos_div_of_dvd (by omega) hdiv
    have hgcd' := bealGcd_three_pow_eq_one hxr hyr hzt hA hgcd
    have hsol' :
        (A ^ (x / 5)) ^ 5 + (B ^ (y / 5)) ^ 5 = (C ^ (z / l)) ^ l := by
      rw [zpow_mul_div hx5, zpow_mul_div hy5, zpow_mul_div hdiv]
      exact hsol
    exact sumTwoFifthsNotSeventhOrNineteenth (A ^ (x / 5)) (B ^ (y / 5))
      (C ^ (z / l)) l hl (pow_ne_zero _ hA) (pow_ne_zero _ hB) (pow_ne_zero _ hC)
      hgcd' hsol'
  · obtain ⟨l, hl, hdiv⟩ := exists_dahmen_divisor hxD
    have hyr : 0 < y / 5 := pos_div_of_dvd (by omega) hy5
    have hzr : 0 < z / 5 := pos_div_of_dvd (by omega) hz5
    have hxt : 0 < x / l := pos_div_of_dvd (by omega) hdiv
    have hrew :
        (C ^ (z / 5)) ^ 5 + (-(B ^ (y / 5))) ^ 5 = (A ^ (x / l)) ^ l := by
      rw [odd_pow_neg (by decide : Odd 5), zpow_mul_div hz5, zpow_mul_div hy5,
        zpow_mul_div hdiv]
      linarith [hsol]
    have hgcd' :
        bealGcd (C ^ (z / 5)) (-(B ^ (y / 5))) (A ^ (x / l)) = 1 := by
      have hplain := bealGcd_three_pow_eq_one (A := C) (B := B) (C := A)
        hzr hyr hxt hC (bealGcd_eq_cba.trans hgcd)
      simpa [bealGcd, Int.natAbs_neg] using hplain
    exact sumTwoFifthsNotSeventhOrNineteenth (C ^ (z / 5)) (-(B ^ (y / 5)))
      (A ^ (x / l)) l hl (pow_ne_zero _ hC) (neg_ne_zero.mpr (pow_ne_zero _ hB))
      (pow_ne_zero _ hA) hgcd' hrew
  · obtain ⟨l, hl, hdiv⟩ := exists_dahmen_divisor hyD
    have hxr : 0 < x / 5 := pos_div_of_dvd (by omega) hx5
    have hzr : 0 < z / 5 := pos_div_of_dvd (by omega) hz5
    have hyt : 0 < y / l := pos_div_of_dvd (by omega) hdiv
    have hrew :
        (C ^ (z / 5)) ^ 5 + (-(A ^ (x / 5))) ^ 5 = (B ^ (y / l)) ^ l := by
      rw [odd_pow_neg (by decide : Odd 5), zpow_mul_div hz5, zpow_mul_div hx5,
        zpow_mul_div hdiv]
      linarith [hsol]
    have hgcd' :
        bealGcd (C ^ (z / 5)) (-(A ^ (x / 5))) (B ^ (y / l)) = 1 := by
      have hplain := bealGcd_three_pow_eq_one (A := C) (B := A) (C := B)
        hzr hxr hyt hC (bealGcd_eq_cab.trans hgcd)
      simpa [bealGcd, Int.natAbs_neg] using hplain
    exact sumTwoFifthsNotSeventhOrNineteenth (C ^ (z / 5)) (-(A ^ (x / 5)))
      (B ^ (y / l)) l hl (pow_ne_zero _ hC) (neg_ne_zero.mpr (pow_ne_zero _ hA))
      (pow_ne_zero _ hB) hgcd' hrew

theorem not_beal_ten_ten_seven {A B C : ℤ}
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hgcd : bealGcd A B C = 1)
    (hsol : A ^ 10 + B ^ 10 = C ^ 7) : False :=
  not_beal_fifth_pair_power_shape (by decide) (by decide) (by decide)
    hA hB hC hgcd (by decide) hsol

theorem not_beal_seven_ten_ten {A B C : ℤ}
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hgcd : bealGcd A B C = 1)
    (hsol : A ^ 7 + B ^ 10 = C ^ 10) : False :=
  not_beal_fifth_pair_power_shape (by decide) (by decide) (by decide)
    hA hB hC hgcd (by decide) hsol

theorem not_beal_five_ten_seven {A B C : ℤ}
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hgcd : bealGcd A B C = 1)
    (hsol : A ^ 5 + B ^ 10 = C ^ 7) : False :=
  not_beal_fifth_pair_power_shape (by decide) (by decide) (by decide)
    hA hB hC hgcd (by decide) hsol

theorem not_beal_five_five_twenty_one {A B C : ℤ}
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hgcd : bealGcd A B C = 1)
    (hsol : A ^ 5 + B ^ 5 = C ^ 21) : False :=
  not_beal_fifth_pair_power_shape (by decide) (by decide) (by decide)
    hA hB hC hgcd (by decide) hsol

/-- Open: even sum `z ≥ 7` outside fourth- and fifth-power cuts. `(10,10,9)` remains. -/
def BealTwoEqualEvenSumExpGeSevenOutsideFourthFifthResidual : Prop :=
  ∀ (A B C : ℤ) (x y z : ℕ) (_hx : 3 ≤ x) (_hy : 3 ≤ y) (_hz : 3 ≤ z)
    (_hA : A ≠ 0) (_hB : B ≠ 0) (_hC : C ≠ 0),
    bealGcd A B C = 1 →
    bealExpGcd x y z = 1 →
    x = y → Even x → 7 ≤ z →
    ¬ IsCubePairPowerShape x y z →
    ¬ 4 ∣ x →
    ¬ IsFifthPairPowerShape x y z →
      ¬ A ^ x + B ^ y = C ^ z

theorem BealTwoEqualEvenSumExpGeSevenOutsideFourthResidual_of_outside_fifth
    (hOut : BealTwoEqualEvenSumExpGeSevenOutsideFourthFifthResidual) :
    BealTwoEqualEvenSumExpGeSevenOutsideFourthResidual := by
  intro A B C x y z hx hy hz hA hB hC hgcd hd hxy hxeven hz7 hshape h4 hsol
  by_cases hfifth : IsFifthPairPowerShape x y z
  · exact not_beal_fifth_pair_power_shape hx hy hz hA hB hC hgcd hfifth hsol
  · exact hOut A B C x y z hx hy hz hA hB hC hgcd hd hxy hxeven hz7 hshape h4
      hfifth hsol

theorem BealTwoEqualEvenSumResidual_of_ge_seven_outside_fourth_fifth
    (h7 : BealTwoEqualEvenSumExpGeSevenOutsideFourthFifthResidual) :
    BealTwoEqualEvenSumResidual :=
  BealTwoEqualEvenSumResidual_of_ge_seven_outside_fourth
    (BealTwoEqualEvenSumExpGeSevenOutsideFourthResidual_of_outside_fifth h7)

/-- Open: even difference outside cube pairs and fifth-power pairs. -/
def BealTwoEqualEvenDiffOutsideFifthPairResidual : Prop :=
  ∀ (A B C : ℤ) (x y z : ℕ) (_hx : 3 ≤ x) (_hy : 3 ≤ y) (_hz : 3 ≤ z)
    (_hA : A ≠ 0) (_hB : B ≠ 0) (_hC : C ≠ 0),
    bealGcd A B C = 1 →
    bealExpGcd x y z = 1 →
    ((y = z ∧ Even y) ∨ (x = z ∧ Even x)) →
    ¬ IsCubePairPowerShape x y z →
    ¬ IsFifthPairPowerShape x y z →
      ¬ A ^ x + B ^ y = C ^ z

theorem BealTwoEqualEvenDiffOutsideCubePairResidual_of_outside_fifth
    (hOut : BealTwoEqualEvenDiffOutsideFifthPairResidual) :
    BealTwoEqualEvenDiffOutsideCubePairResidual := by
  intro A B C x y z hx hy hz hA hB hC hgcd hd hpair hshape hsol
  by_cases hfifth : IsFifthPairPowerShape x y z
  · exact not_beal_fifth_pair_power_shape hx hy hz hA hB hC hgcd hfifth hsol
  · exact hOut A B C x y z hx hy hz hA hB hC hgcd hd hpair hshape hfifth hsol

theorem BealTwoEqualEvenDiffResidual_of_outside_fifth
    (hOut : BealTwoEqualEvenDiffOutsideFifthPairResidual) :
    BealTwoEqualEvenDiffResidual :=
  BealTwoEqualEvenDiffResidual_of_outside_cube_pair
    (BealTwoEqualEvenDiffOutsideCubePairResidual_of_outside_fifth hOut)

/-- Open: odd two-equal outside those cuts. `(5,5,11)` remains. -/
def BealTwoEqualOddOutsideFifthPairResidual : Prop :=
  ∀ (A B C : ℤ) (x y z : ℕ) (_hx : 3 ≤ x) (_hy : 3 ≤ y) (_hz : 3 ≤ z)
    (_hA : A ≠ 0) (_hB : B ≠ 0) (_hC : C ≠ 0),
    bealGcd A B C = 1 →
    bealExpGcd x y z = 1 →
    ((x = y ∧ Odd x) ∨ (y = z ∧ Odd y) ∨ (x = z ∧ Odd x)) →
    ¬ IsCubePairPowerShape x y z →
    ¬ IsRepeatedFifthShape x y z →
    ¬ IsFifthPairPowerShape x y z →
      ¬ A ^ x + B ^ y = C ^ z

theorem BealTwoEqualOddOutsideRepeatedFifthResidual_of_outside_fifth
    (hOut : BealTwoEqualOddOutsideFifthPairResidual) :
    BealTwoEqualOddOutsideRepeatedFifthResidual := by
  intro A B C x y z hx hy hz hA hB hC hgcd hd hpair hcube hrep hsol
  by_cases hfifth : IsFifthPairPowerShape x y z
  · exact not_beal_fifth_pair_power_shape hx hy hz hA hB hC hgcd hfifth hsol
  · exact hOut A B C x y z hx hy hz hA hB hC hgcd hd hpair hcube hrep hfifth hsol

theorem BealTwoEqualOddResidual_of_outside_fifth_pair
    (hOut : BealTwoEqualOddOutsideFifthPairResidual) :
    BealTwoEqualOddResidual :=
  BealTwoEqualOddResidual_of_outside_repeated_fifth
    (BealTwoEqualOddOutsideRepeatedFifthResidual_of_outside_fifth hOut)

/-- Open: distinct exponents outside those cuts. `(3,5,7)` remains. -/
def BealAllDistinctOutsideFifthPairResidual : Prop :=
  ∀ (A B C : ℤ) (x y z : ℕ) (_hx : 3 ≤ x) (_hy : 3 ≤ y) (_hz : 3 ≤ z)
    (_hA : A ≠ 0) (_hB : B ≠ 0) (_hC : C ≠ 0),
    bealGcd A B C = 1 →
    bealExpGcd x y z = 1 →
    x ≠ y → y ≠ z → x ≠ z →
    ¬ IsCubePairPowerShape x y z →
    ¬ IsFifthPairPowerShape x y z →
      ¬ A ^ x + B ^ y = C ^ z

theorem BealAllDistinctOutsideCubePairResidual_of_outside_fifth
    (hOut : BealAllDistinctOutsideFifthPairResidual) :
    BealAllDistinctOutsideCubePairResidual := by
  intro A B C x y z hx hy hz hA hB hC hgcd hd hxy hyz hxz hshape hsol
  by_cases hfifth : IsFifthPairPowerShape x y z
  · exact not_beal_fifth_pair_power_shape hx hy hz hA hB hC hgcd hfifth hsol
  · exact hOut A B C x y z hx hy hz hA hB hC hgcd hd hxy hyz hxz hshape hfifth hsol

theorem BealAllDistinctExpResidual_of_outside_fifth_pair
    (hOut : BealAllDistinctOutsideFifthPairResidual) :
    BealAllDistinctExpResidual :=
  BealAllDistinctExpResidual_of_outside_cube_pair
    (BealAllDistinctOutsideCubePairResidual_of_outside_fifth hOut)

/-- Open: unequal-odd body outside those cuts. `(10,10,14)` is removed. -/
def BealPythagoreanUnequalOddOutsideFifthPairResidual : Prop :=
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
      ¬ A ^ x + B ^ y = C ^ z

theorem BealPythagoreanUnequalOddOutsideCubePairResidual_of_outside_fifth
    (hOut : BealPythagoreanUnequalOddOutsideFifthPairResidual) :
    BealPythagoreanUnequalOddOutsideCubePairResidual := by
  intro A B C x y z hx hy hz hA hB hC hgcd hd hxy hxz hyz hyzOdd hxzOdd hshape hsol
  by_cases hfifth : IsFifthPairPowerShape x y z
  · exact not_beal_fifth_pair_power_shape hx hy hz hA hB hC hgcd hfifth hsol
  · exact hOut A B C x y z hx hy hz hA hB hC hgcd hd hxy hxz hyz hyzOdd hxzOdd
      hshape hfifth hsol

theorem BealPythagoreanUnequalOddResidual_of_outside_fifth_pair
    (hOut : BealPythagoreanUnequalOddOutsideFifthPairResidual) :
    BealPythagoreanUnequalOddResidual :=
  BealPythagoreanUnequalOddResidual_of_outside_cube_pair
    (BealPythagoreanUnequalOddOutsideCubePairResidual_of_outside_fifth hOut)

end Theorems

end DstDiophantine
