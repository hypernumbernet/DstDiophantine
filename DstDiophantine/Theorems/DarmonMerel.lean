import DstDiophantine.Theorems.Beal
import Mathlib.Data.Int.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Darmon–Merel theorem as an axiom (phase 7j / 7k)

mathlib (v4.34) does not contain the Darmon–Merel theorem on the generalised
Fermat equation of signature `(n,n,3)`. We take the classical statement as an
`axiom` (same contract as `fermatLastTheorem` / `mihailescu`) and derive the
Beal two-equal cube slices from it.

Phase 7k extends the `(n,n,3)` slice to the odd permutations
`(3,n,n)` and `(n,3,n)` via sign rewriting (`(-B)^n = -B^n` when `n` is odd).
Even common exponents do **not** rewrite to Darmon–Merel form.

This is **not** a Lean proof of Darmon–Merel.
-/

namespace DstDiophantine

namespace Theorems

/--
Darmon–Merel (1997): there are no nonzero integer solutions of
`a^n + b^n = c^3` with `n ≥ 4` and `gcd(|a|,|b|,|c|) = 1`.

Not present in mathlib at the pin used by this project; recorded explicitly as
an axiom rather than smuggled into a `sorry`. This is **not** an unconditional
Lean proof of Darmon–Merel.
-/
axiom darmonMerelCube :
    ∀ (a b c : ℤ) (n : ℕ),
      4 ≤ n →
      a ≠ 0 → b ≠ 0 → c ≠ 0 →
      Nat.gcd a.natAbs (Nat.gcd b.natAbs c.natAbs) = 1 →
      ¬ a ^ n + b ^ n = c ^ 3

/-- Abbreviation for the Darmon–Merel hypothesis shape. -/
abbrev DarmonMerelCubeHyp : Prop :=
  ∀ (a b c : ℤ) (n : ℕ),
    4 ≤ n → a ≠ 0 → b ≠ 0 → c ≠ 0 →
      Nat.gcd a.natAbs (Nat.gcd b.natAbs c.natAbs) = 1 →
      ¬ a ^ n + b ^ n = c ^ 3

private theorem bealGcd_neg_permute (A B C : ℤ) :
    bealGcd C (-B) A = bealGcd A B C ∧ bealGcd C (-A) B = bealGcd A B C := by
  constructor <;> simp [bealGcd, Nat.gcd_comm, Nat.gcd_left_comm]

/-- Odd power: `X^n + (-Y)^n = X^n - Y^n`. -/
private theorem odd_pow_add_neg {X Y : ℤ} {n : ℕ} (hodd : Odd n) :
    X ^ n + (-Y) ^ n = X ^ n - Y ^ n := by
  rw [Odd.neg_pow hodd Y]; ring

/--
Hypothesis form: Darmon–Merel forbids `A^n + B^n = C^3` for `n ≥ 4` with
three-way gcd 1 (Beal `d = 1`, first-pair equal, third exponent 3).
-/
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

/-- Phase 7j: axiom form of the `(n,n,3)` two-equal Beal slice. -/
theorem not_beal_two_equal_third_three {A B C : ℤ} {x y z : ℕ}
    (hx : 3 ≤ x) (hy : 3 ≤ y) (hz : 3 ≤ z)
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hgcd : bealGcd A B C = 1)
    (hd : bealExpGcd x y z = 1)
    (hxy : x = y) (hz3 : z = 3)
    (hsol : A ^ x + B ^ y = C ^ z) : False :=
  not_beal_two_equal_third_three_of_DM darmonMerelCube
    hx hy hz hA hB hC hgcd hd hxy hz3 hsol

/--
Phase 7k: `(3,n,n)` with odd `n ≥ 5` and `d = 1`.

From `A^3 + B^n = C^n` and odd `n`, rewrite to `C^n + (-B)^n = A^3`.
-/
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

/-- Phase 7k axiom form: `(3,n,n)` with odd common exponent. -/
theorem not_beal_two_equal_first_three_odd {A B C : ℤ} {x y z : ℕ}
    (hx : 3 ≤ x) (hy : 3 ≤ y) (hz : 3 ≤ z)
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hgcd : bealGcd A B C = 1)
    (hd : bealExpGcd x y z = 1)
    (hyz : y = z) (hx3 : x = 3) (hyodd : Odd y)
    (hsol : A ^ x + B ^ y = C ^ z) : False :=
  not_beal_two_equal_first_three_odd_of_DM darmonMerelCube
    hx hy hz hA hB hC hgcd hd hyz hx3 hyodd hsol

/--
Phase 7k: `(n,3,n)` with odd `n ≥ 5` and `d = 1`.

From `A^n + B^3 = C^n` and odd `n`, rewrite to `C^n + (-A)^n = B^3`.
-/
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

/-- Phase 7k axiom form: `(n,3,n)` with odd common exponent. -/
theorem not_beal_two_equal_second_three_odd {A B C : ℤ} {x y z : ℕ}
    (hx : 3 ≤ x) (hy : 3 ≤ y) (hz : 3 ≤ z)
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hgcd : bealGcd A B C = 1)
    (hd : bealExpGcd x y z = 1)
    (hxz : x = z) (hy3 : y = 3) (hxodd : Odd x)
    (hsol : A ^ x + B ^ y = C ^ z) : False :=
  not_beal_two_equal_second_three_odd_of_DM darmonMerelCube
    hx hy hz hA hB hC hgcd hd hxz hy3 hxodd hsol

/--
Phase 7k: any two-equal Beal solution with the distinct exponent equal to 3,
and with the common exponent odd whenever the cube is not in third position,
is forbidden by Darmon–Merel.
-/
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

end DstDiophantine
