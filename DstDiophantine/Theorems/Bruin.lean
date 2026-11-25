import DstDiophantine.Theorems.BealMixed
import Mathlib.Data.Int.Basic
import Mathlib.Tactic.Linarith

/-!
# Sums of two cubes

`sumTwoCubesNotPerfectPower` assumes no nonzero coprime `a³ + b³ = cⁿ` for a `TwoCubeExponent` `n`.
A proper multiple of such an `n` reduces to that axiom. It is not a Lean proof of the cited range,
and classical Beal is not claimed. A prime exponent past `10^9` stays outside the closure.
-/

namespace DstDiophantine

namespace Theorems

/-- Two exponents equal `3` and the third equals `4` or `5`, in any position. -/
def IsBruinTwoCubeShape (x y z : ℕ) : Prop :=
  (x = 3 ∧ y = 3 ∧ (z = 4 ∨ z = 5)) ∨
    (y = 3 ∧ z = 3 ∧ (x = 4 ∨ x = 5)) ∨
      (x = 3 ∧ z = 3 ∧ (y = 4 ∨ y = 5))

instance {x y z : ℕ} : Decidable (IsBruinTwoCubeShape x y z) := by
  unfold IsBruinTwoCubeShape
  infer_instance

/-- Companion exponents for which a coprime sum of two cubes is not an `n`-th power: the range
`3 ≤ n ≤ 10^9`, or any even `n ≥ 4`. -/
def TwoCubeExponent (n : ℕ) : Prop :=
  (3 ≤ n ∧ n ≤ 1000000000) ∨ (4 ≤ n ∧ 2 ∣ n)

instance : DecidablePred TwoCubeExponent := by
  intro n
  unfold TwoCubeExponent
  infer_instance

/-- `n` is a `TwoCubeExponent`, or a proper multiple of one. -/
def TwoCubeMultiple (n : ℕ) : Prop :=
  TwoCubeExponent n ∨ ∃ d, d < n ∧ TwoCubeExponent d ∧ d ∣ n

private def findTwoCubeFactor.go (n d : ℕ) : ℕ → Option ℕ
  | 0 => none
  | fuel + 1 =>
    if n ≤ d then none
    else if TwoCubeExponent d ∧ d ∣ n then some d
    else findTwoCubeFactor.go n (d + 1) fuel

/-- Least `TwoCubeExponent` divisor in `3, …, min(n - 1, 10^9)`, if any. -/
private def findTwoCubeFactor (n : ℕ) : Option ℕ :=
  findTwoCubeFactor.go n 3 (min (n - 3) 1000000000)

private theorem findTwoCubeFactor.go_spec {n d fuel m : ℕ}
    (h : findTwoCubeFactor.go n d fuel = some m) :
    d ≤ m ∧ m < n ∧ TwoCubeExponent m ∧ m ∣ n := by
  induction fuel generalizing d with
  | zero => simp [findTwoCubeFactor.go] at h
  | succ fuel ih =>
    simp only [findTwoCubeFactor.go] at h
    split_ifs at h with hle hex
    · have hdm : d = m := by injection h
      subst hdm
      exact ⟨le_rfl, Nat.lt_of_not_le hle, hex.1, hex.2⟩
    · obtain ⟨hle', hlt, hExp, hdiv⟩ := ih h
      exact ⟨Nat.le_trans (Nat.le_succ d) hle', hlt, hExp, hdiv⟩

private theorem findTwoCubeFactor.go_of_witness {n d fuel k : ℕ}
    (hkd : d ≤ k) (hkn : k < n) (hfuel : k < d + fuel)
    (hExp : TwoCubeExponent k) (hdiv : k ∣ n) :
    ∃ m, findTwoCubeFactor.go n d fuel = some m := by
  induction fuel generalizing d with
  | zero => omega
  | succ fuel ih =>
    by_cases hle : n ≤ d
    · omega
    · by_cases hex : TwoCubeExponent d ∧ d ∣ n
      · exact ⟨d, by simp [findTwoCubeFactor.go, hle, hex]⟩
      · have hkd' : d + 1 ≤ k := by
          have hne : d ≠ k := by
            intro heq
            apply hex
            subst heq
            exact ⟨hExp, hdiv⟩
          omega
        have hfuel' : k < (d + 1) + fuel := by omega
        obtain ⟨m, hm⟩ := ih hkd' hfuel'
        refine ⟨m, ?_⟩
        simp [findTwoCubeFactor.go, hle, hex, hm]

private theorem findTwoCubeFactor_of_witness {n k : ℕ}
    (hk3 : 3 ≤ k) (hkn : k < n) (hkB : k ≤ 1000000000)
    (hExp : TwoCubeExponent k) (hdiv : k ∣ n) :
    ∃ m, findTwoCubeFactor n = some m := by
  have hn : 3 ≤ n := le_trans hk3 (Nat.le_of_lt hkn)
  have hsum : 3 + (n - 3) = n := Nat.add_sub_of_le hn
  have hfuel : k < 3 + min (n - 3) 1000000000 := by
    have hkn' : k < 3 + (n - 3) := by rw [hsum]; exact hkn
    have hkB' : k < 3 + 1000000000 := by omega
    have hmin : k < 3 + min (n - 3) 1000000000 := by
      by_cases hcmp : n - 3 ≤ 1000000000
      · rw [min_eq_left hcmp]; exact hkn'
      · rw [min_eq_right (Nat.le_of_not_le hcmp)]; exact hkB'
    exact hmin
  simpa [findTwoCubeFactor] using
    findTwoCubeFactor.go_of_witness hk3 hkn hfuel hExp hdiv

private def twoCubeMultipleBool (n : ℕ) : Bool :=
  decide (TwoCubeExponent n) || (findTwoCubeFactor n).isSome

private theorem twoCubeMultipleBool_iff {n : ℕ} :
    twoCubeMultipleBool n = true ↔ TwoCubeMultiple n := by
  unfold twoCubeMultipleBool TwoCubeMultiple
  constructor
  · intro h
    simp only [Bool.or_eq_true, decide_eq_true_eq, Option.isSome_iff_exists] at h
    rcases h with h | ⟨m, hm⟩
    · exact Or.inl h
    · obtain ⟨_, hlt, hExp, hdiv⟩ :=
        findTwoCubeFactor.go_spec (by simpa [findTwoCubeFactor] using hm)
      exact Or.inr ⟨m, hlt, hExp, hdiv⟩
  · intro h
    rcases h with h | ⟨d, hdlt, hExp, hdiv⟩
    · simp [h]
    · by_cases hdir : TwoCubeExponent n
      · simp [hdir]
      · have hd3 : 3 ≤ d := by
          rcases hExp with ⟨h3, _⟩ | ⟨h4, _⟩
          · exact h3
          · exact le_trans (by decide : (3 : ℕ) ≤ 4) h4
        have hdB : d ≤ 1000000000 := by
          rcases hExp with ⟨_, hle⟩ | ⟨h4, heven⟩
          · exact hle
          · have h2n : 2 ∣ n := dvd_trans heven hdiv
            have h4n : 4 ≤ n := by omega
            exact absurd (Or.inr ⟨h4n, h2n⟩) hdir
        obtain ⟨m, hm⟩ := findTwoCubeFactor_of_witness hd3 hdlt hdB hExp hdiv
        simp [hdir, hm]

instance : DecidablePred TwoCubeMultiple := fun n =>
  decidable_of_iff (twoCubeMultipleBool n = true) twoCubeMultipleBool_iff

theorem TwoCubeMultiple.of_twoCube {n : ℕ} (h : TwoCubeExponent n) :
    TwoCubeMultiple n := Or.inl h

/-- A prime past `10^9` is not a multiple of a `TwoCubeExponent`. -/
theorem not_twoCubeMultiple_of_large_prime {p : ℕ}
    (hp : Nat.Prime p) (hgt : 1000000000 < p) : ¬ TwoCubeMultiple p := by
  intro h
  rcases h with h | ⟨d, hdlt, hExp, hdiv⟩
  · rcases h with ⟨_, hle⟩ | ⟨_, heven⟩
    · omega
    · have hp2 : 2 = p := (Nat.prime_dvd_prime_iff_eq (by decide : Nat.Prime 2) hp).mp heven
      omega
  · have hd : d = 1 ∨ d = p := hp.eq_one_or_self_of_dvd d hdiv
    rcases hd with hd1 | hdp
    · subst hd1
      rcases hExp with ⟨h3, _⟩ | ⟨h4, _⟩ <;> omega
    · exact ne_of_lt hdlt hdp

/-- Two exponents equal `3` and the third is a `TwoCubeExponent`. -/
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

/-- No nonzero coprime `a³ + b³ = cⁿ` on `TwoCubeExponent`. An axiom, not a proof. -/
axiom sumTwoCubesNotPerfectPower :
    ∀ (a b c : ℤ) (n : ℕ),
      ((3 ≤ n ∧ n ≤ 1000000000) ∨ (4 ≤ n ∧ 2 ∣ n)) →
      a ≠ 0 → b ≠ 0 → c ≠ 0 →
      Nat.gcd a.natAbs (Nat.gcd b.natAbs c.natAbs) = 1 →
      ¬ a ^ 3 + b ^ 3 = c ^ n

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

/-- Two exponents divisible by `3`, the other a `TwoCubeMultiple`. -/
def IsCubePairPowerShape (x y z : ℕ) : Prop :=
  (3 ∣ x ∧ 3 ∣ y ∧ TwoCubeMultiple z) ∨
    (3 ∣ y ∧ 3 ∣ z ∧ TwoCubeMultiple x) ∨
      (3 ∣ x ∧ 3 ∣ z ∧ TwoCubeMultiple y)

instance {x y z : ℕ} : Decidable (IsCubePairPowerShape x y z) := by
  unfold IsCubePairPowerShape
  infer_instance

theorem IsCubePairPowerShape_of_twoCube {x y z : ℕ}
    (h : IsTwoCubePowerShape x y z) : IsCubePairPowerShape x y z := by
  rcases h with ⟨hx, hy, hz⟩ | ⟨hy, hz, hx⟩ | ⟨hx, hz, hy⟩
  · subst hx; subst hy
    exact Or.inl ⟨Nat.dvd_refl 3, Nat.dvd_refl 3, TwoCubeMultiple.of_twoCube hz⟩
  · subst hy; subst hz
    exact Or.inr (Or.inl ⟨Nat.dvd_refl 3, Nat.dvd_refl 3, TwoCubeMultiple.of_twoCube hx⟩)
  · subst hx; subst hz
    exact Or.inr (Or.inr ⟨Nat.dvd_refl 3, Nat.dvd_refl 3, TwoCubeMultiple.of_twoCube hy⟩)

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

private theorem bealGcd_pow_right {A B C : ℤ} {k : ℕ}
    (_hk : 0 < k) (hA : A ≠ 0)
    (hgcd : bealGcd A B C = 1) :
    bealGcd A B (C ^ k) = 1 := by
  by_contra hne
  have hgt : 1 < bealGcd A B (C ^ k) := by
    have hpos : 0 < bealGcd A B (C ^ k) := bealGcd_pos hA
    omega
  obtain ⟨p, hp, hpA, hpB, hpC⟩ := exists_common_prime_of_bealGcd_gt_one hgt
  have hpC' : p ∣ C.natAbs :=
    hp.dvd_of_dvd_pow (by simpa [Int.natAbs_pow] using hpC)
  have : p ∣ bealGcd A B C := Nat.dvd_gcd hpA (Nat.dvd_gcd hpB hpC')
  rw [hgcd] at this
  exact hp.not_dvd_one this

/-- A coprime sum of two cubes is not an `n`th power when `n` is a `TwoCubeMultiple`. -/
theorem not_sum_two_cubes_of_twoCubeMultiple
    {a b c : ℤ} {n : ℕ}
    (hn : TwoCubeMultiple n)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hgcd : bealGcd a b c = 1)
    (hsol : a ^ 3 + b ^ 3 = c ^ n) : False := by
  rcases hn with h | ⟨d, hdlt, hExp, hdiv⟩
  · exact sumTwoCubesNotPerfectPower a b c n h ha hb hc hgcd hsol
  · have hquot : 0 < n / d := by
      have hmul : d * (n / d) = n := Nat.mul_div_cancel' hdiv
      have hne : n / d ≠ 0 := by
        intro hz
        simp [hz] at hmul
        omega
      exact Nat.pos_of_ne_zero hne
    have hsol' : a ^ 3 + b ^ 3 = (c ^ (n / d)) ^ d := by
      rw [← pow_mul, Nat.div_mul_cancel hdiv]
      exact hsol
    have hgcd' : bealGcd a b (c ^ (n / d)) = 1 :=
      bealGcd_pow_right hquot ha hgcd
    exact sumTwoCubesNotPerfectPower a b (c ^ (n / d)) d hExp ha hb
      (pow_ne_zero _ hc) (by simpa [bealGcd] using hgcd') hsol'

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
    exact not_sum_two_cubes_of_twoCubeMultiple hzN
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
    exact not_sum_two_cubes_of_twoCubeMultiple hxN
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
    exact not_sum_two_cubes_of_twoCubeMultiple hyN
      (pow_ne_zero _ hC) (neg_ne_zero.mpr (pow_ne_zero _ hA)) hB hgcd' hrew

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

/-- Open residual: odd two-equal Beal outside `IsTwoCubePowerShape`. -/
def BealTwoEqualOddOutsideBruinResidual : Prop :=
  ∀ (A B C : ℤ) (x y z : ℕ) (_hx : 3 ≤ x) (_hy : 3 ≤ y) (_hz : 3 ≤ z)
    (_hA : A ≠ 0) (_hB : B ≠ 0) (_hC : C ≠ 0),
    bealGcd A B C = 1 →
    bealExpGcd x y z = 1 →
    ((x = y ∧ Odd x) ∨ (y = z ∧ Odd y) ∨ (x = z ∧ Odd x)) →
    ¬ IsTwoCubePowerShape x y z →
      ¬ A ^ x + B ^ y = C ^ z

theorem BealTwoEqualOddResidual_of_outside_bruin
    (hOut : BealTwoEqualOddOutsideBruinResidual) :
    BealTwoEqualOddResidual := by
  intro A B C x y z hx hy hz hA hB hC hgcd hd hpair hsol
  by_cases hshape : IsTwoCubePowerShape x y z
  · exact not_beal_two_cube_power_shape hx hy hz hA hB hC hgcd hd hshape hsol
  · exact hOut A B C x y z hx hy hz hA hB hC hgcd hd hpair hshape hsol

/-- Open residual: odd two-equal Beal outside every cube-pair shape. -/
def BealTwoEqualOddOutsideCubePairResidual : Prop :=
  ∀ (A B C : ℤ) (x y z : ℕ) (_hx : 3 ≤ x) (_hy : 3 ≤ y) (_hz : 3 ≤ z)
    (_hA : A ≠ 0) (_hB : B ≠ 0) (_hC : C ≠ 0),
    bealGcd A B C = 1 →
    bealExpGcd x y z = 1 →
    ((x = y ∧ Odd x) ∨ (y = z ∧ Odd y) ∨ (x = z ∧ Odd x)) →
    ¬ IsCubePairPowerShape x y z →
      ¬ A ^ x + B ^ y = C ^ z

theorem BealTwoEqualOddResidual_of_outside_cube_pair
    (hOut : BealTwoEqualOddOutsideCubePairResidual) :
    BealTwoEqualOddResidual := by
  intro A B C x y z hx hy hz hA hB hC hgcd hd hpair hsol
  by_cases hshape : IsCubePairPowerShape x y z
  · exact not_beal_cube_pair_power_shape hx hy hz hA hB hC hgcd hshape hsol
  · exact hOut A B C x y z hx hy hz hA hB hC hgcd hd hpair hshape hsol

/-- Open residual: distinct exponents outside cube pairs. `(3,4,5)` is removed. -/
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

/-- Open residual: unequal-odd `d = 2` outside cube pairs. -/
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

theorem not_beal_six_six_seven {A B C : ℤ}
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hgcd : bealGcd A B C = 1)
    (hsol : A ^ 6 + B ^ 6 = C ^ 7) : False :=
  not_beal_cube_pair_power_shape (by decide) (by decide) (by decide)
    hA hB hC hgcd (by decide) hsol

theorem not_beal_nine_nine_four {A B C : ℤ}
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hgcd : bealGcd A B C = 1)
    (hsol : A ^ 9 + B ^ 9 = C ^ 4) : False :=
  not_beal_cube_pair_power_shape (by decide) (by decide) (by decide)
    hA hB hC hgcd (by decide) hsol

theorem not_beal_five_six_six {A B C : ℤ}
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hgcd : bealGcd A B C = 1)
    (hsol : A ^ 5 + B ^ 6 = C ^ 6) : False :=
  not_beal_cube_pair_power_shape (by decide) (by decide) (by decide)
    hA hB hC hgcd (by decide) hsol

theorem not_beal_three_six_five {A B C : ℤ}
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hgcd : bealGcd A B C = 1)
    (hsol : A ^ 3 + B ^ 6 = C ^ 5) : False :=
  not_beal_cube_pair_power_shape (by decide) (by decide) (by decide)
    hA hB hC hgcd (by decide) hsol

/-- `7 ∣ 10^9 + 1`, and `7` is a `TwoCubeExponent`. -/
theorem twoCubeMultiple_billion_plus_one : TwoCubeMultiple 1000000001 :=
  Or.inr ⟨7, by decide, by decide, by decide⟩

/-- No coprime `A³ + B³ = C^(10^9+1)`. The hypotenuse is a multiple of `7`. -/
theorem not_beal_three_three_billion_plus_one {A B C : ℤ}
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hgcd : bealGcd A B C = 1)
    (hsol : A ^ 3 + B ^ 3 = C ^ 1000000001) : False :=
  not_beal_cube_pair_power_shape (by decide) (by decide) (by decide)
    hA hB hC hgcd
    (Or.inl ⟨Nat.dvd_refl 3, Nat.dvd_refl 3, twoCubeMultiple_billion_plus_one⟩) hsol

/-- No coprime `A⁹ + B⁹ = C^(10^9+1)`. Both exponents are divisible by `3`. -/
theorem not_beal_nine_nine_billion_plus_one {A B C : ℤ}
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hgcd : bealGcd A B C = 1)
    (hsol : A ^ 9 + B ^ 9 = C ^ 1000000001) : False :=
  not_beal_cube_pair_power_shape (by decide) (by decide) (by decide)
    hA hB hC hgcd
    (Or.inl ⟨by decide, by decide, twoCubeMultiple_billion_plus_one⟩) hsol

/-- A prime hypotenuse past `10^9` is not a cube-pair shape. -/
theorem not_cubePair_three_three_large_prime {p : ℕ}
    (hp : Nat.Prime p) (hgt : 1000000000 < p) :
    ¬ IsCubePairPowerShape 3 3 p := by
  intro h
  rcases h with ⟨_, _, hpM⟩ | ⟨_, hpdiv, _⟩ | ⟨_, hpdiv, _⟩
  · exact not_twoCubeMultiple_of_large_prime hp hgt hpM
  · have hp3 : p = 3 := (hp.dvd_iff_eq (by decide : (3 : ℕ) ≠ 1)).mp hpdiv
    omega
  · have hp3 : p = 3 := (hp.dvd_iff_eq (by decide : (3 : ℕ) ≠ 1)).mp hpdiv
    omega

end Theorems

end DstDiophantine
