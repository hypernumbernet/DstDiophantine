import DstDiophantine.Theorems.Beal
import Mathlib.Data.Int.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Signature `(n,n,5)` as an axiom

`fermatSignatureNN5` assumes no coprime nonzero `a^n + b^n = c⁵` for `n ≥ 4`. It is not Darmon–Merel
and not a Lean proof of that theorem; `(3,3,5)` is not this axiom.
-/

namespace DstDiophantine

namespace Theorems

/-- No coprime nonzero `a^n + b^n = c⁵` for `n ≥ 4`. An axiom, not a proof. -/
axiom fermatSignatureNN5 :
    ∀ (a b c : ℤ) (n : ℕ),
      4 ≤ n →
      a ≠ 0 → b ≠ 0 → c ≠ 0 →
      Nat.gcd a.natAbs (Nat.gcd b.natAbs c.natAbs) = 1 →
      ¬ a ^ n + b ^ n = c ^ 5

abbrev FermatSignatureNN5Hyp : Prop :=
  ∀ (a b c : ℤ) (n : ℕ),
    4 ≤ n → a ≠ 0 → b ≠ 0 → c ≠ 0 →
      Nat.gcd a.natAbs (Nat.gcd b.natAbs c.natAbs) = 1 →
      ¬ a ^ n + b ^ n = c ^ 5

private theorem bealGcd_neg_permute (A B C : ℤ) :
    bealGcd C (-B) A = bealGcd A B C ∧ bealGcd C (-A) B = bealGcd A B C := by
  constructor <;> simp [bealGcd, Nat.gcd_comm, Nat.gcd_left_comm]

private theorem odd_pow_add_neg {X Y : ℤ} {n : ℕ} (hodd : Odd n) :
    X ^ n + (-Y) ^ n = X ^ n - Y ^ n := by
  rw [Odd.neg_pow hodd Y]; ring

theorem not_beal_two_equal_third_five_of_NN5
    (hNN5 : FermatSignatureNN5Hyp)
    {A B C : ℤ} {x y z : ℕ}
    (_hx : 3 ≤ x) (_hy : 3 ≤ y) (_hz : 3 ≤ z)
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hgcd : bealGcd A B C = 1)
    (_hd : bealExpGcd x y z = 1)
    (hxy : x = y) (hz5 : z = 5) (hx4 : 4 ≤ x)
    (hsol : A ^ x + B ^ y = C ^ z) : False := by
  subst hxy; subst hz5
  exact hNN5 A B C x hx4 hA hB hC hgcd hsol

theorem not_beal_two_equal_third_five {A B C : ℤ} {x y z : ℕ}
    (hx : 3 ≤ x) (hy : 3 ≤ y) (hz : 3 ≤ z)
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hgcd : bealGcd A B C = 1)
    (hd : bealExpGcd x y z = 1)
    (hxy : x = y) (hz5 : z = 5) (hx4 : 4 ≤ x)
    (hsol : A ^ x + B ^ y = C ^ z) : False :=
  not_beal_two_equal_third_five_of_NN5 fermatSignatureNN5
    hx hy hz hA hB hC hgcd hd hxy hz5 hx4 hsol

theorem not_beal_two_equal_third_five_even {A B C : ℤ} {x y z : ℕ}
    (hx : 3 ≤ x) (hy : 3 ≤ y) (hz : 3 ≤ z)
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hgcd : bealGcd A B C = 1)
    (hd : bealExpGcd x y z = 1)
    (hxy : x = y) (hz5 : z = 5) (hxeven : Even x)
    (hsol : A ^ x + B ^ y = C ^ z) : False := by
  have hx4 : 4 ≤ x := by
    have : x ≠ 3 := fun h => by
      subst h; exact Nat.not_even_iff_odd.mpr (by decide : Odd 3) hxeven
    omega
  exact not_beal_two_equal_third_five hx hy hz hA hB hC hgcd hd hxy hz5 hx4 hsol

theorem not_beal_two_equal_first_five_odd_of_NN5
    (hNN5 : FermatSignatureNN5Hyp)
    {A B C : ℤ} {x y z : ℕ}
    (_hx : 3 ≤ x) (_hy : 3 ≤ y) (_hz : 3 ≤ z)
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hgcd : bealGcd A B C = 1)
    (_hd : bealExpGcd x y z = 1)
    (hyz : y = z) (hx5 : x = 5) (hyodd : Odd y) (hy4 : 4 ≤ y)
    (hsol : A ^ x + B ^ y = C ^ z) : False := by
  subst hyz; subst hx5
  have hrew : C ^ y + (-B) ^ y = A ^ 5 := by
    rw [odd_pow_add_neg hyodd]; linarith [hsol]
  have hgcd' : bealGcd C (-B) A = 1 := by
    rw [(bealGcd_neg_permute A B C).1]; exact hgcd
  exact hNN5 C (-B) A y hy4 hC (neg_ne_zero.mpr hB) hA hgcd' hrew

theorem not_beal_two_equal_first_five_odd {A B C : ℤ} {x y z : ℕ}
    (hx : 3 ≤ x) (hy : 3 ≤ y) (hz : 3 ≤ z)
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hgcd : bealGcd A B C = 1)
    (hd : bealExpGcd x y z = 1)
    (hyz : y = z) (hx5 : x = 5) (hyodd : Odd y) (hy4 : 4 ≤ y)
    (hsol : A ^ x + B ^ y = C ^ z) : False :=
  not_beal_two_equal_first_five_odd_of_NN5 fermatSignatureNN5
    hx hy hz hA hB hC hgcd hd hyz hx5 hyodd hy4 hsol

theorem not_beal_two_equal_second_five_odd_of_NN5
    (hNN5 : FermatSignatureNN5Hyp)
    {A B C : ℤ} {x y z : ℕ}
    (_hx : 3 ≤ x) (_hy : 3 ≤ y) (_hz : 3 ≤ z)
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hgcd : bealGcd A B C = 1)
    (_hd : bealExpGcd x y z = 1)
    (hxz : x = z) (hy5 : y = 5) (hxodd : Odd x) (hx4 : 4 ≤ x)
    (hsol : A ^ x + B ^ y = C ^ z) : False := by
  subst hxz; subst hy5
  have hrew : C ^ x + (-A) ^ x = B ^ 5 := by
    rw [odd_pow_add_neg hxodd]; linarith [hsol]
  have hgcd' : bealGcd C (-A) B = 1 := by
    rw [(bealGcd_neg_permute A B C).2]; exact hgcd
  exact hNN5 C (-A) B x hx4 hC (neg_ne_zero.mpr hA) hB hgcd' hrew

theorem not_beal_two_equal_second_five_odd {A B C : ℤ} {x y z : ℕ}
    (hx : 3 ≤ x) (hy : 3 ≤ y) (hz : 3 ≤ z)
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hgcd : bealGcd A B C = 1)
    (hd : bealExpGcd x y z = 1)
    (hxz : x = z) (hy5 : y = 5) (hxodd : Odd x) (hx4 : 4 ≤ x)
    (hsol : A ^ x + B ^ y = C ^ z) : False :=
  not_beal_two_equal_second_five_odd_of_NN5 fermatSignatureNN5
    hx hy hz hA hB hC hgcd hd hxz hy5 hxodd hx4 hsol

theorem not_beal_two_equal_fifth_slice {A B C : ℤ} {x y z : ℕ}
    (hx : 3 ≤ x) (hy : 3 ≤ y) (hz : 3 ≤ z)
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hgcd : bealGcd A B C = 1)
    (hd : bealExpGcd x y z = 1)
    (hpair :
      (x = y ∧ z = 5 ∧ 4 ≤ x) ∨
        (y = z ∧ x = 5 ∧ Odd y ∧ 4 ≤ y) ∨
          (x = z ∧ y = 5 ∧ Odd x ∧ 4 ≤ x))
    (hsol : A ^ x + B ^ y = C ^ z) : False := by
  rcases hpair with h | h | h
  · exact not_beal_two_equal_third_five hx hy hz hA hB hC hgcd hd h.1 h.2.1 h.2.2
      hsol
  · exact not_beal_two_equal_first_five_odd hx hy hz hA hB hC hgcd hd h.1 h.2.1
      h.2.2.1 h.2.2.2 hsol
  · exact not_beal_two_equal_second_five_odd hx hy hz hA hB hC hgcd hd h.1 h.2.1
      h.2.2.1 h.2.2.2 hsol

end Theorems

end DstDiophantine
