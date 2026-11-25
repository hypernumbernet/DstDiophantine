import DstDiophantine.Theorems.BennettEllenbergNg
import DstDiophantine.Theorems.Bruin
import Mathlib.Data.Int.Basic
import Mathlib.Tactic.Linarith

/-!
# Repeated fifth powers

`sumTwoFifthsNotSeventhOrNineteenth` assumes no nonzero coprime `a⁵ + b⁵ = cˡ` for `l = 7` or `19`.
`sumTwoFifthsNotStollPrime` assumes the same for `l = 11`, `13`, or `17`.
Each is an axiom, not a Lean proof of the cited theorem, and classical Beal is not claimed.
Primes `p ≥ 23` stay under GRH in Stoll's chapter and are not axioms.
`(7,7,11)` is not either statement.
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

/-- No nonzero coprime `a⁵ + b⁵ = cˡ` for `l ∈ {11,13,17}`.
An axiom, not a proof of Stoll's Theorem 8.7
(*Chabauty without the Mordell–Weil group*, Springer, 2017).
That chapter assumes GRH for primes `p ≥ 23`; those primes are not included. -/
axiom sumTwoFifthsNotStollPrime :
    ∀ (a b c : ℤ) (l : ℕ),
      (l = 11 ∨ l = 13 ∨ l = 17) →
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

/-! ### Phase 8a: fifth-power pairs beside a multiple of `7`, `11`, `13`, `17`, or `19` -/

/-- The remaining exponent is a seventh or a nineteenth power. -/
abbrev IsDahmenSiksekMultiple (n : ℕ) : Prop :=
  7 ∣ n ∨ 19 ∣ n

/-- The remaining exponent is an eleventh, thirteenth, or seventeenth power.
Unconditional range of Stoll's theorem on `x⁵ + y⁵ = zᵖ`. -/
abbrev IsStollFifthMultiple (n : ℕ) : Prop :=
  11 ∣ n ∨ 13 ∣ n ∨ 17 ∣ n

/-- Dahmen–Siksek or the unconditional Stoll range. -/
abbrev IsFifthCompanionMultiple (n : ℕ) : Prop :=
  IsDahmenSiksekMultiple n ∨ IsStollFifthMultiple n

/-- Two exponents divisible by `5`, the third by `7`, `11`, `13`, `17`, or `19`. -/
def IsFifthPairPowerShape (x y z : ℕ) : Prop :=
  (5 ∣ x ∧ 5 ∣ y ∧ IsFifthCompanionMultiple z) ∨
    (5 ∣ y ∧ 5 ∣ z ∧ IsFifthCompanionMultiple x) ∨
      (5 ∣ x ∧ 5 ∣ z ∧ IsFifthCompanionMultiple y)

instance {x y z : ℕ} : Decidable (IsFifthPairPowerShape x y z) := by
  unfold IsFifthPairPowerShape
  infer_instance

theorem IsFifthPairPowerShape_of_repeated {x y z : ℕ}
    (h : IsRepeatedFifthShape x y z) : IsFifthPairPowerShape x y z := by
  rcases h with h7 | h19
  · rcases h7 with ⟨hx, hy, hz⟩ | ⟨hy, hz, hx⟩ | ⟨hx, hz, hy⟩
    · subst hx; subst hy; subst hz
      exact Or.inl ⟨Nat.dvd_refl 5, Nat.dvd_refl 5, Or.inl (Or.inl (Nat.dvd_refl 7))⟩
    · subst hy; subst hz; subst hx
      exact Or.inr (Or.inl ⟨Nat.dvd_refl 5, Nat.dvd_refl 5, Or.inl (Or.inl (Nat.dvd_refl 7))⟩)
    · subst hx; subst hz; subst hy
      exact Or.inr (Or.inr ⟨Nat.dvd_refl 5, Nat.dvd_refl 5, Or.inl (Or.inl (Nat.dvd_refl 7))⟩)
  · rcases h19 with ⟨hx, hy, hz⟩ | ⟨hy, hz, hx⟩ | ⟨hx, hz, hy⟩
    · subst hx; subst hy; subst hz
      exact Or.inl ⟨Nat.dvd_refl 5, Nat.dvd_refl 5, Or.inl (Or.inr (Nat.dvd_refl 19))⟩
    · subst hy; subst hz; subst hx
      exact Or.inr (Or.inl ⟨Nat.dvd_refl 5, Nat.dvd_refl 5, Or.inl (Or.inr (Nat.dvd_refl 19))⟩)
    · subst hx; subst hz; subst hy
      exact Or.inr (Or.inr ⟨Nat.dvd_refl 5, Nat.dvd_refl 5, Or.inl (Or.inr (Nat.dvd_refl 19))⟩)

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

private theorem exists_fifth_companion {n : ℕ} (h : IsFifthCompanionMultiple n) :
    ∃ l, ((l = 7 ∨ l = 19) ∨ (l = 11 ∨ l = 13 ∨ l = 17)) ∧ l ∣ n := by
  rcases h with hDS | hSt
  · obtain ⟨l, hl, hdiv⟩ := exists_dahmen_divisor hDS
    exact ⟨l, Or.inl hl, hdiv⟩
  · rcases hSt with h11 | h13 | h17
    · exact ⟨11, Or.inr (Or.inl rfl), h11⟩
    · exact ⟨13, Or.inr (Or.inr (Or.inl rfl)), h13⟩
    · exact ⟨17, Or.inr (Or.inr (Or.inr rfl)), h17⟩

private theorem not_sum_two_fifths_of_companion
    {a b c : ℤ} {l : ℕ}
    (hl : (l = 7 ∨ l = 19) ∨ (l = 11 ∨ l = 13 ∨ l = 17))
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hgcd : Nat.gcd a.natAbs (Nat.gcd b.natAbs c.natAbs) = 1)
    (hsol : a ^ 5 + b ^ 5 = c ^ l) : False := by
  rcases hl with hDS | hSt
  · exact sumTwoFifthsNotSeventhOrNineteenth a b c l hDS ha hb hc hgcd hsol
  · exact sumTwoFifthsNotStollPrime a b c l hSt ha hb hc hgcd hsol

theorem not_beal_fifth_pair_power_shape
    {A B C : ℤ} {x y z : ℕ}
    (hx : 3 ≤ x) (hy : 3 ≤ y) (hz : 3 ≤ z)
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hgcd : bealGcd A B C = 1)
    (hshape : IsFifthPairPowerShape x y z)
    (hsol : A ^ x + B ^ y = C ^ z) : False := by
  rcases hshape with ⟨hx5, hy5, hzD⟩ | ⟨hy5, hz5, hxD⟩ | ⟨hx5, hz5, hyD⟩
  · obtain ⟨l, hl, hdiv⟩ := exists_fifth_companion hzD
    have hxr : 0 < x / 5 := pos_div_of_dvd (by omega) hx5
    have hyr : 0 < y / 5 := pos_div_of_dvd (by omega) hy5
    have hzt : 0 < z / l := pos_div_of_dvd (by omega) hdiv
    have hgcd' := bealGcd_three_pow_eq_one hxr hyr hzt hA hgcd
    have hsol' :
        (A ^ (x / 5)) ^ 5 + (B ^ (y / 5)) ^ 5 = (C ^ (z / l)) ^ l := by
      rw [zpow_mul_div hx5, zpow_mul_div hy5, zpow_mul_div hdiv]
      exact hsol
    exact not_sum_two_fifths_of_companion hl (pow_ne_zero _ hA) (pow_ne_zero _ hB)
      (pow_ne_zero _ hC) hgcd' hsol'
  · obtain ⟨l, hl, hdiv⟩ := exists_fifth_companion hxD
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
    exact not_sum_two_fifths_of_companion hl (pow_ne_zero _ hC)
      (neg_ne_zero.mpr (pow_ne_zero _ hB)) (pow_ne_zero _ hA) hgcd' hrew
  · obtain ⟨l, hl, hdiv⟩ := exists_fifth_companion hyD
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
    exact not_sum_two_fifths_of_companion hl (pow_ne_zero _ hC)
      (neg_ne_zero.mpr (pow_ne_zero _ hA)) (pow_ne_zero _ hB) hgcd' hrew

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

theorem not_beal_five_five_eleven {A B C : ℤ}
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hgcd : bealGcd A B C = 1)
    (hsol : A ^ 5 + B ^ 5 = C ^ 11) : False :=
  not_beal_fifth_pair_power_shape (by decide) (by decide) (by decide)
    hA hB hC hgcd (by decide) hsol

theorem not_beal_five_five_thirteen {A B C : ℤ}
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hgcd : bealGcd A B C = 1)
    (hsol : A ^ 5 + B ^ 5 = C ^ 13) : False :=
  not_beal_fifth_pair_power_shape (by decide) (by decide) (by decide)
    hA hB hC hgcd (by decide) hsol

theorem not_beal_five_five_seventeen {A B C : ℤ}
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hgcd : bealGcd A B C = 1)
    (hsol : A ^ 5 + B ^ 5 = C ^ 17) : False :=
  not_beal_fifth_pair_power_shape (by decide) (by decide) (by decide)
    hA hB hC hgcd (by decide) hsol

theorem not_beal_ten_ten_eleven {A B C : ℤ}
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hgcd : bealGcd A B C = 1)
    (hsol : A ^ 10 + B ^ 10 = C ^ 11) : False :=
  not_beal_fifth_pair_power_shape (by decide) (by decide) (by decide)
    hA hB hC hgcd (by decide) hsol

/-! ### Shared exponent beside a multiple of `3` or `5` -/

/-- Two exponents share a divisor at least `4`, and the third is divisible by `3` or by `5`.
A difference seat requires that shared divisor to be odd, so the sign rewrite stays a sum. -/
def IsSharedExpCubeOrFifth (x y z : ℕ) : Prop :=
  (4 ≤ Nat.gcd x y ∧ (3 ∣ z ∨ 5 ∣ z)) ∨
    (4 ≤ Nat.gcd y z ∧ Nat.gcd y z % 2 = 1 ∧ (3 ∣ x ∨ 5 ∣ x)) ∨
      (4 ≤ Nat.gcd x z ∧ Nat.gcd x z % 2 = 1 ∧ (3 ∣ y ∨ 5 ∣ y))

instance {x y z : ℕ} : Decidable (IsSharedExpCubeOrFifth x y z) := by
  unfold IsSharedExpCubeOrFifth
  infer_instance

private theorem not_beal_shared_sum
    {A B C : ℤ} {x y z : ℕ}
    (hx : 3 ≤ x) (hy : 3 ≤ y) (hz : 3 ≤ z)
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hgcd : bealGcd A B C = 1)
    (hn : 4 ≤ Nat.gcd x y) (hdiv : 3 ∣ z ∨ 5 ∣ z)
    (hsol : A ^ x + B ^ y = C ^ z) : False := by
  set n := Nat.gcd x y
  have hnx : n ∣ x := Nat.gcd_dvd_left _ _
  have hny : n ∣ y := Nat.gcd_dvd_right _ _
  have hxn : 0 < x / n := pos_div_of_dvd (by omega) hnx
  have hyn : 0 < y / n := pos_div_of_dvd (by omega) hny
  rcases hdiv with hz3 | hz5
  · have hzt : 0 < z / 3 := pos_div_of_dvd (by omega) hz3
    have hgcd' := bealGcd_three_pow_eq_one hxn hyn hzt hA hgcd
    have hsol' :
        (A ^ (x / n)) ^ n + (B ^ (y / n)) ^ n = (C ^ (z / 3)) ^ 3 := by
      rw [zpow_mul_div hnx, zpow_mul_div hny, zpow_mul_div hz3]
      exact hsol
    exact darmonMerelCube (A ^ (x / n)) (B ^ (y / n)) (C ^ (z / 3)) n hn
      (pow_ne_zero _ hA) (pow_ne_zero _ hB) (pow_ne_zero _ hC) hgcd' hsol'
  · have hzt : 0 < z / 5 := pos_div_of_dvd (by omega) hz5
    have hgcd' := bealGcd_three_pow_eq_one hxn hyn hzt hA hgcd
    have hsol' :
        (A ^ (x / n)) ^ n + (B ^ (y / n)) ^ n = (C ^ (z / 5)) ^ 5 := by
      rw [zpow_mul_div hnx, zpow_mul_div hny, zpow_mul_div hz5]
      exact hsol
    exact fermatSignatureNN5 (A ^ (x / n)) (B ^ (y / n)) (C ^ (z / 5)) n hn
      (pow_ne_zero _ hA) (pow_ne_zero _ hB) (pow_ne_zero _ hC) hgcd' hsol'

private theorem not_beal_shared_diff_yz
    {A B C : ℤ} {x y z : ℕ}
    (hx : 3 ≤ x) (hy : 3 ≤ y) (hz : 3 ≤ z)
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hgcd : bealGcd A B C = 1)
    (hn : 4 ≤ Nat.gcd y z) (hodd : Nat.gcd y z % 2 = 1)
    (hdiv : 3 ∣ x ∨ 5 ∣ x)
    (hsol : A ^ x + B ^ y = C ^ z) : False := by
  set n := Nat.gcd y z
  have hny : n ∣ y := Nat.gcd_dvd_left _ _
  have hnz : n ∣ z := Nat.gcd_dvd_right _ _
  have hodd' : Odd n := Nat.odd_iff.mpr hodd
  have hyn : 0 < y / n := pos_div_of_dvd (by omega) hny
  have hzn : 0 < z / n := pos_div_of_dvd (by omega) hnz
  rcases hdiv with hx3 | hx5
  · have hxt : 0 < x / 3 := pos_div_of_dvd (by omega) hx3
    have hrew :
        (C ^ (z / n)) ^ n + (-(B ^ (y / n))) ^ n = (A ^ (x / 3)) ^ 3 := by
      rw [odd_pow_neg hodd', zpow_mul_div hnz, zpow_mul_div hny, zpow_mul_div hx3]
      linarith [hsol]
    have hgcd' :
        bealGcd (C ^ (z / n)) (-(B ^ (y / n))) (A ^ (x / 3)) = 1 := by
      have hplain := bealGcd_three_pow_eq_one (A := C) (B := B) (C := A)
        hzn hyn hxt hC (bealGcd_eq_cba.trans hgcd)
      simpa [bealGcd, Int.natAbs_neg] using hplain
    exact darmonMerelCube (C ^ (z / n)) (-(B ^ (y / n))) (A ^ (x / 3)) n hn
      (pow_ne_zero _ hC) (neg_ne_zero.mpr (pow_ne_zero _ hB)) (pow_ne_zero _ hA)
      hgcd' hrew
  · have hxt : 0 < x / 5 := pos_div_of_dvd (by omega) hx5
    have hrew :
        (C ^ (z / n)) ^ n + (-(B ^ (y / n))) ^ n = (A ^ (x / 5)) ^ 5 := by
      rw [odd_pow_neg hodd', zpow_mul_div hnz, zpow_mul_div hny, zpow_mul_div hx5]
      linarith [hsol]
    have hgcd' :
        bealGcd (C ^ (z / n)) (-(B ^ (y / n))) (A ^ (x / 5)) = 1 := by
      have hplain := bealGcd_three_pow_eq_one (A := C) (B := B) (C := A)
        hzn hyn hxt hC (bealGcd_eq_cba.trans hgcd)
      simpa [bealGcd, Int.natAbs_neg] using hplain
    exact fermatSignatureNN5 (C ^ (z / n)) (-(B ^ (y / n))) (A ^ (x / 5)) n hn
      (pow_ne_zero _ hC) (neg_ne_zero.mpr (pow_ne_zero _ hB)) (pow_ne_zero _ hA)
      hgcd' hrew

private theorem not_beal_shared_diff_xz
    {A B C : ℤ} {x y z : ℕ}
    (hx : 3 ≤ x) (hy : 3 ≤ y) (hz : 3 ≤ z)
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hgcd : bealGcd A B C = 1)
    (hn : 4 ≤ Nat.gcd x z) (hodd : Nat.gcd x z % 2 = 1)
    (hdiv : 3 ∣ y ∨ 5 ∣ y)
    (hsol : A ^ x + B ^ y = C ^ z) : False := by
  set n := Nat.gcd x z
  have hnx : n ∣ x := Nat.gcd_dvd_left _ _
  have hnz : n ∣ z := Nat.gcd_dvd_right _ _
  have hodd' : Odd n := Nat.odd_iff.mpr hodd
  have hxn : 0 < x / n := pos_div_of_dvd (by omega) hnx
  have hzn : 0 < z / n := pos_div_of_dvd (by omega) hnz
  rcases hdiv with hy3 | hy5
  · have hyt : 0 < y / 3 := pos_div_of_dvd (by omega) hy3
    have hrew :
        (C ^ (z / n)) ^ n + (-(A ^ (x / n))) ^ n = (B ^ (y / 3)) ^ 3 := by
      rw [odd_pow_neg hodd', zpow_mul_div hnz, zpow_mul_div hnx, zpow_mul_div hy3]
      linarith [hsol]
    have hgcd' :
        bealGcd (C ^ (z / n)) (-(A ^ (x / n))) (B ^ (y / 3)) = 1 := by
      have hplain := bealGcd_three_pow_eq_one (A := C) (B := A) (C := B)
        hzn hxn hyt hC (bealGcd_eq_cab.trans hgcd)
      simpa [bealGcd, Int.natAbs_neg] using hplain
    exact darmonMerelCube (C ^ (z / n)) (-(A ^ (x / n))) (B ^ (y / 3)) n hn
      (pow_ne_zero _ hC) (neg_ne_zero.mpr (pow_ne_zero _ hA)) (pow_ne_zero _ hB)
      hgcd' hrew
  · have hyt : 0 < y / 5 := pos_div_of_dvd (by omega) hy5
    have hrew :
        (C ^ (z / n)) ^ n + (-(A ^ (x / n))) ^ n = (B ^ (y / 5)) ^ 5 := by
      rw [odd_pow_neg hodd', zpow_mul_div hnz, zpow_mul_div hnx, zpow_mul_div hy5]
      linarith [hsol]
    have hgcd' :
        bealGcd (C ^ (z / n)) (-(A ^ (x / n))) (B ^ (y / 5)) = 1 := by
      have hplain := bealGcd_three_pow_eq_one (A := C) (B := A) (C := B)
        hzn hxn hyt hC (bealGcd_eq_cab.trans hgcd)
      simpa [bealGcd, Int.natAbs_neg] using hplain
    exact fermatSignatureNN5 (C ^ (z / n)) (-(A ^ (x / n))) (B ^ (y / 5)) n hn
      (pow_ne_zero _ hC) (neg_ne_zero.mpr (pow_ne_zero _ hA)) (pow_ne_zero _ hB)
      hgcd' hrew

/-- No coprime nonzero solution whose exponents share a divisor at least `4` beside a multiple of
`3` or of `5`. The cube case is `darmonMerelCube`; the fifth-power case is `fermatSignatureNN5`. -/
theorem not_beal_shared_exp_cube_or_fifth
    {A B C : ℤ} {x y z : ℕ}
    (hx : 3 ≤ x) (hy : 3 ≤ y) (hz : 3 ≤ z)
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hgcd : bealGcd A B C = 1)
    (hshape : IsSharedExpCubeOrFifth x y z)
    (hsol : A ^ x + B ^ y = C ^ z) : False := by
  rcases hshape with hsum | hdiff | hdiff
  · exact not_beal_shared_sum hx hy hz hA hB hC hgcd hsum.1 hsum.2 hsol
  · exact not_beal_shared_diff_yz hx hy hz hA hB hC hgcd hdiff.1 hdiff.2.1 hdiff.2.2 hsol
  · exact not_beal_shared_diff_xz hx hy hz hA hB hC hgcd hdiff.1 hdiff.2.1 hdiff.2.2 hsol

theorem not_beal_ten_ten_nine {A B C : ℤ}
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hgcd : bealGcd A B C = 1)
    (hsol : A ^ 10 + B ^ 10 = C ^ 9) : False :=
  not_beal_shared_exp_cube_or_fifth (by decide) (by decide) (by decide)
    hA hB hC hgcd (by decide) hsol

/-- Even sum `z ≥ 7` outside fourth-, fifth-, and shared-exponent cuts.
Follows from `BealTwoEqualEvenSumExpGeSevenOutsideAnniSeventeenthResidual`.
`(22,22,7)` is an Anni–Siksek shape. `(10,10,11)` is a fifth-power pair. -/
def BealTwoEqualEvenSumExpGeSevenOutsideFourthFifthResidual : Prop :=
  ∀ (A B C : ℤ) (x y z : ℕ) (_hx : 3 ≤ x) (_hy : 3 ≤ y) (_hz : 3 ≤ z)
    (_hA : A ≠ 0) (_hB : B ≠ 0) (_hC : C ≠ 0),
    bealGcd A B C = 1 →
    bealExpGcd x y z = 1 →
    x = y → Even x → 7 ≤ z →
    ¬ IsCubePairPowerShape x y z →
    ¬ 4 ∣ x →
    ¬ IsFifthPairPowerShape x y z →
    ¬ IsSharedExpCubeOrFifth x y z →
      ¬ A ^ x + B ^ y = C ^ z

theorem BealTwoEqualEvenSumExpGeSevenOutsideFourthResidual_of_outside_fifth
    (hOut : BealTwoEqualEvenSumExpGeSevenOutsideFourthFifthResidual) :
    BealTwoEqualEvenSumExpGeSevenOutsideFourthResidual := by
  intro A B C x y z hx hy hz hA hB hC hgcd hd hxy hxeven hz7 hshape h4 hsol
  by_cases hshared : IsSharedExpCubeOrFifth x y z
  · exact not_beal_shared_exp_cube_or_fifth hx hy hz hA hB hC hgcd hshared hsol
  · by_cases hfifth : IsFifthPairPowerShape x y z
    · exact not_beal_fifth_pair_power_shape hx hy hz hA hB hC hgcd hfifth hsol
    · exact hOut A B C x y z hx hy hz hA hB hC hgcd hd hxy hxeven hz7 hshape h4
        hfifth hshared hsol

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
    ¬ IsSharedExpCubeOrFifth x y z →
      ¬ A ^ x + B ^ y = C ^ z

theorem BealTwoEqualEvenDiffOutsideCubePairResidual_of_outside_fifth
    (hOut : BealTwoEqualEvenDiffOutsideFifthPairResidual) :
    BealTwoEqualEvenDiffOutsideCubePairResidual := by
  intro A B C x y z hx hy hz hA hB hC hgcd hd hpair hshape hsol
  by_cases hshared : IsSharedExpCubeOrFifth x y z
  · exact not_beal_shared_exp_cube_or_fifth hx hy hz hA hB hC hgcd hshared hsol
  · by_cases hfifth : IsFifthPairPowerShape x y z
    · exact not_beal_fifth_pair_power_shape hx hy hz hA hB hC hgcd hfifth hsol
    · exact hOut A B C x y z hx hy hz hA hB hC hgcd hd hpair hshape hfifth
        hshared hsol

theorem BealTwoEqualEvenDiffResidual_of_outside_fifth
    (hOut : BealTwoEqualEvenDiffOutsideFifthPairResidual) :
    BealTwoEqualEvenDiffResidual :=
  BealTwoEqualEvenDiffResidual_of_outside_cube_pair
    (BealTwoEqualEvenDiffOutsideCubePairResidual_of_outside_fifth hOut)

/-- Open: odd two-equal outside those cuts.
`(5,5,23)` and `(7,7,11)` remain. `(5,5,11)`, `(5,5,13)`, and `(5,5,17)` are fifth-power pairs.
A prime hypotenuse past `10^9` with `p ≡ 2 (mod 3)` is a Freitas cube companion.
`p ≡ 1 (mod 3)` stays in this leaf. -/
def BealTwoEqualOddOutsideFifthPairResidual : Prop :=
  ∀ (A B C : ℤ) (x y z : ℕ) (_hx : 3 ≤ x) (_hy : 3 ≤ y) (_hz : 3 ≤ z)
    (_hA : A ≠ 0) (_hB : B ≠ 0) (_hC : C ≠ 0),
    bealGcd A B C = 1 →
    bealExpGcd x y z = 1 →
    ((x = y ∧ Odd x) ∨ (y = z ∧ Odd y) ∨ (x = z ∧ Odd x)) →
    ¬ IsCubePairPowerShape x y z →
    ¬ IsRepeatedFifthShape x y z →
    ¬ IsFifthPairPowerShape x y z →
    ¬ IsSharedExpCubeOrFifth x y z →
      ¬ A ^ x + B ^ y = C ^ z

theorem BealTwoEqualOddOutsideRepeatedFifthResidual_of_outside_fifth
    (hOut : BealTwoEqualOddOutsideFifthPairResidual) :
    BealTwoEqualOddOutsideRepeatedFifthResidual := by
  intro A B C x y z hx hy hz hA hB hC hgcd hd hpair hcube hrep hsol
  by_cases hshared : IsSharedExpCubeOrFifth x y z
  · exact not_beal_shared_exp_cube_or_fifth hx hy hz hA hB hC hgcd hshared hsol
  · by_cases hfifth : IsFifthPairPowerShape x y z
    · exact not_beal_fifth_pair_power_shape hx hy hz hA hB hC hgcd hfifth hsol
    · exact hOut A B C x y z hx hy hz hA hB hC hgcd hd hpair hcube hrep hfifth
        hshared hsol

theorem BealTwoEqualOddResidual_of_outside_fifth_pair
    (hOut : BealTwoEqualOddOutsideFifthPairResidual) :
    BealTwoEqualOddResidual :=
  BealTwoEqualOddResidual_of_outside_repeated_fifth
    (BealTwoEqualOddOutsideRepeatedFifthResidual_of_outside_fifth hOut)

/-- Open: distinct exponents outside those cuts.
`(3,5,7)` remains. `(5,10,11)` is a fifth-power pair. -/
def BealAllDistinctOutsideFifthPairResidual : Prop :=
  ∀ (A B C : ℤ) (x y z : ℕ) (_hx : 3 ≤ x) (_hy : 3 ≤ y) (_hz : 3 ≤ z)
    (_hA : A ≠ 0) (_hB : B ≠ 0) (_hC : C ≠ 0),
    bealGcd A B C = 1 →
    bealExpGcd x y z = 1 →
    x ≠ y → y ≠ z → x ≠ z →
    ¬ IsCubePairPowerShape x y z →
    ¬ IsFifthPairPowerShape x y z →
    ¬ IsSharedExpCubeOrFifth x y z →
      ¬ A ^ x + B ^ y = C ^ z

theorem BealAllDistinctOutsideCubePairResidual_of_outside_fifth
    (hOut : BealAllDistinctOutsideFifthPairResidual) :
    BealAllDistinctOutsideCubePairResidual := by
  intro A B C x y z hx hy hz hA hB hC hgcd hd hxy hyz hxz hshape hsol
  by_cases hshared : IsSharedExpCubeOrFifth x y z
  · exact not_beal_shared_exp_cube_or_fifth hx hy hz hA hB hC hgcd hshared hsol
  · by_cases hfifth : IsFifthPairPowerShape x y z
    · exact not_beal_fifth_pair_power_shape hx hy hz hA hB hC hgcd hfifth hsol
    · exact hOut A B C x y z hx hy hz hA hB hC hgcd hd hxy hyz hxz hshape hfifth
        hshared hsol

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
    ¬ IsSharedExpCubeOrFifth x y z →
      ¬ A ^ x + B ^ y = C ^ z

theorem BealPythagoreanUnequalOddOutsideCubePairResidual_of_outside_fifth
    (hOut : BealPythagoreanUnequalOddOutsideFifthPairResidual) :
    BealPythagoreanUnequalOddOutsideCubePairResidual := by
  intro A B C x y z hx hy hz hA hB hC hgcd hd hxy hxz hyz hyzOdd hxzOdd hshape hsol
  by_cases hshared : IsSharedExpCubeOrFifth x y z
  · exact not_beal_shared_exp_cube_or_fifth hx hy hz hA hB hC hgcd hshared hsol
  · by_cases hfifth : IsFifthPairPowerShape x y z
    · exact not_beal_fifth_pair_power_shape hx hy hz hA hB hC hgcd hfifth hsol
    · exact hOut A B C x y z hx hy hz hA hB hC hgcd hd hxy hxz hyz hyzOdd hxzOdd
        hshape hfifth hshared hsol

theorem BealPythagoreanUnequalOddResidual_of_outside_fifth_pair
    (hOut : BealPythagoreanUnequalOddOutsideFifthPairResidual) :
    BealPythagoreanUnequalOddResidual :=
  BealPythagoreanUnequalOddResidual_of_outside_cube_pair
    (BealPythagoreanUnequalOddOutsideCubePairResidual_of_outside_fifth hOut)

end Theorems

end DstDiophantine
