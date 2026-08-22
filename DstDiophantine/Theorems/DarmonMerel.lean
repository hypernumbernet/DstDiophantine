import DstDiophantine.Theorems.Beal
import Mathlib.Data.Int.Basic
import Mathlib.Data.Nat.Basic

/-!
# Darmon–Merel theorem as an axiom (phase 7j)

mathlib (v4.34) does not contain the Darmon–Merel theorem on the generalised
Fermat equation of signature `(n,n,3)`. We take the classical statement as an
`axiom` (same contract as `fermatLastTheorem` / `mihailescu`) and derive the
Beal two-equal cube slice from it.

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

/--
Hypothesis form: Darmon–Merel forbids `A^n + B^n = C^3` for `n ≥ 4` with
three-way gcd 1 (Beal `d = 1`, first-pair equal, third exponent 3).
-/
theorem not_beal_two_equal_third_three_of_DM
    (hDM :
      ∀ (a b c : ℤ) (n : ℕ),
        4 ≤ n → a ≠ 0 → b ≠ 0 → c ≠ 0 →
          Nat.gcd a.natAbs (Nat.gcd b.natAbs c.natAbs) = 1 →
          ¬ a ^ n + b ^ n = c ^ 3)
    {A B C : ℤ} {x y z : ℕ}
    (hx : 3 ≤ x) (_hy : 3 ≤ y) (_hz : 3 ≤ z)
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hgcd : bealGcd A B C = 1)
    (hd : bealExpGcd x y z = 1)
    (hxy : x = y) (hz3 : z = 3)
    (hsol : A ^ x + B ^ y = C ^ z) : False := by
  subst hxy; subst hz3
  obtain ⟨_, hne⟩ := beal_two_equal_exp_of_expGcd_eq_one hx rfl hd
  have hx4 : 4 ≤ x := by
    have : x ≠ 3 := hne
    omega
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

end Theorems

end DstDiophantine
