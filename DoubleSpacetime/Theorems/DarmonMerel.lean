import DoubleSpacetime.Theorems.Beal
import Mathlib.Data.Int.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Darmon–Merel as an axiom

`darmonMerelCube` assumes no coprime nonzero `a^n + b^n = c³` for `n ≥ 4`. A shared exponent
`n ≥ 4` rewrites to that form when the remaining exponent is a multiple of `3`
(`IsSharedExpCubeOrFifth`). The axiom is not a Lean proof of Darmon–Merel.
-/

namespace DoubleSpacetime

namespace Theorems

/-- No coprime nonzero `a^n + b^n = c³` for `n ≥ 4`. An axiom, not a proof. -/
axiom darmonMerelCube :
    ∀ (a b c : ℤ) (n : ℕ),
      4 ≤ n →
      a ≠ 0 → b ≠ 0 → c ≠ 0 →
      Nat.gcd a.natAbs (Nat.gcd b.natAbs c.natAbs) = 1 →
      ¬ a ^ n + b ^ n = c ^ 3

abbrev DarmonMerelCubeHyp : Prop :=
  ∀ (a b c : ℤ) (n : ℕ),
    4 ≤ n → a ≠ 0 → b ≠ 0 → c ≠ 0 →
      Nat.gcd a.natAbs (Nat.gcd b.natAbs c.natAbs) = 1 →
      ¬ a ^ n + b ^ n = c ^ 3

private theorem bealGcd_neg_permute (A B C : ℤ) :
    bealGcd C (-B) A = bealGcd A B C ∧ bealGcd C (-A) B = bealGcd A B C := by
  constructor <;> simp [bealGcd, Nat.gcd_comm, Nat.gcd_left_comm]

private theorem odd_pow_add_neg {X Y : ℤ} {n : ℕ} (hodd : Odd n) :
    X ^ n + (-Y) ^ n = X ^ n - Y ^ n := by
  rw [Odd.neg_pow hodd Y]; ring

theorem not_beal_two_equal_third_three_of_DM
    (hDM : DarmonMerelCubeHyp)
    {A B C : ℤ} {x y z : ℕ}
    (hx : 3 ≤ x) (_hy : 3 ≤ y) (_hz : 3 ≤ z)
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hgcd : bealGcd A B C = 1)
    (hd : bealExpGcd x y z = 1)
    (hxy : x = y) (hz3 : z = 3)
    (hsol : A ^ x + B ^ y = C ^ z) : False := by
  subst hxy; subst hz3
  obtain ⟨_, hne⟩ := beal_two_equal_exp_of_expGcd_eq_one hx rfl hd
  have hx4 : 4 ≤ x := by omega
  exact hDM A B C x hx4 hA hB hC hgcd hsol

theorem not_beal_two_equal_third_three {A B C : ℤ} {x y z : ℕ}
    (hx : 3 ≤ x) (hy : 3 ≤ y) (hz : 3 ≤ z)
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hgcd : bealGcd A B C = 1)
    (hd : bealExpGcd x y z = 1)
    (hxy : x = y) (hz3 : z = 3)
    (hsol : A ^ x + B ^ y = C ^ z) : False :=
  not_beal_two_equal_third_three_of_DM darmonMerelCube
    hx hy hz hA hB hC hgcd hd hxy hz3 hsol

theorem not_beal_two_equal_first_three_odd_of_DM
    (hDM : DarmonMerelCubeHyp)
    {A B C : ℤ} {x y z : ℕ}
    (_hx : 3 ≤ x) (hy : 3 ≤ y) (_hz : 3 ≤ z)
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hgcd : bealGcd A B C = 1)
    (hd : bealExpGcd x y z = 1)
    (hyz : y = z) (hx3 : x = 3) (hyodd : Odd y)
    (hsol : A ^ x + B ^ y = C ^ z) : False := by
  subst hyz; subst hx3
  obtain ⟨_, hne⟩ := beal_two_equal_exp_yz_of_expGcd_eq_one hy rfl hd
  have hy4 : 4 ≤ y := by omega
  have hrew : C ^ y + (-B) ^ y = A ^ 3 := by
    rw [odd_pow_add_neg hyodd]; linarith [hsol]
  have hgcd' : bealGcd C (-B) A = 1 := by
    rw [(bealGcd_neg_permute A B C).1]; exact hgcd
  exact hDM C (-B) A y hy4 hC (neg_ne_zero.mpr hB) hA hgcd' hrew

theorem not_beal_two_equal_first_three_odd {A B C : ℤ} {x y z : ℕ}
    (hx : 3 ≤ x) (hy : 3 ≤ y) (hz : 3 ≤ z)
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hgcd : bealGcd A B C = 1)
    (hd : bealExpGcd x y z = 1)
    (hyz : y = z) (hx3 : x = 3) (hyodd : Odd y)
    (hsol : A ^ x + B ^ y = C ^ z) : False :=
  not_beal_two_equal_first_three_odd_of_DM darmonMerelCube
    hx hy hz hA hB hC hgcd hd hyz hx3 hyodd hsol

theorem not_beal_two_equal_second_three_odd_of_DM
    (hDM : DarmonMerelCubeHyp)
    {A B C : ℤ} {x y z : ℕ}
    (hx : 3 ≤ x) (_hy : 3 ≤ y) (_hz : 3 ≤ z)
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hgcd : bealGcd A B C = 1)
    (hd : bealExpGcd x y z = 1)
    (hxz : x = z) (hy3 : y = 3) (hxodd : Odd x)
    (hsol : A ^ x + B ^ y = C ^ z) : False := by
  subst hxz; subst hy3
  obtain ⟨_, hne⟩ := beal_two_equal_exp_xz_of_expGcd_eq_one hx rfl hd
  have hx4 : 4 ≤ x := by omega
  have hrew : C ^ x + (-A) ^ x = B ^ 3 := by
    rw [odd_pow_add_neg hxodd]; linarith [hsol]
  have hgcd' : bealGcd C (-A) B = 1 := by
    rw [(bealGcd_neg_permute A B C).2]; exact hgcd
  exact hDM C (-A) B x hx4 hC (neg_ne_zero.mpr hA) hB hgcd' hrew

theorem not_beal_two_equal_second_three_odd {A B C : ℤ} {x y z : ℕ}
    (hx : 3 ≤ x) (hy : 3 ≤ y) (hz : 3 ≤ z)
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hgcd : bealGcd A B C = 1)
    (hd : bealExpGcd x y z = 1)
    (hxz : x = z) (hy3 : y = 3) (hxodd : Odd x)
    (hsol : A ^ x + B ^ y = C ^ z) : False :=
  not_beal_two_equal_second_three_odd_of_DM darmonMerelCube
    hx hy hz hA hB hC hgcd hd hxz hy3 hxodd hsol

theorem not_beal_two_equal_cube_slice {A B C : ℤ} {x y z : ℕ}
    (hx : 3 ≤ x) (hy : 3 ≤ y) (hz : 3 ≤ z)
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hgcd : bealGcd A B C = 1)
    (hd : bealExpGcd x y z = 1)
    (hpair :
      (x = y ∧ z = 3) ∨
        (y = z ∧ x = 3 ∧ Odd y) ∨
          (x = z ∧ y = 3 ∧ Odd x))
    (hsol : A ^ x + B ^ y = C ^ z) : False := by
  rcases hpair with h | h | h
  · exact not_beal_two_equal_third_three hx hy hz hA hB hC hgcd hd h.1 h.2 hsol
  · exact not_beal_two_equal_first_three_odd hx hy hz hA hB hC hgcd hd h.1 h.2.1
      h.2.2 hsol
  · exact not_beal_two_equal_second_three_odd hx hy hz hA hB hC hgcd hd h.1 h.2.1
      h.2.2 hsol

end Theorems

end DoubleSpacetime
