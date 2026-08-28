import DstDiophantine.Theorems.Beal
import Mathlib.Data.Int.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Generalised Fermat signature `(n,n,5)` as an axiom (phase 7s)

mathlib (v4.34) does not contain a formalisation of the generalised Fermat
equation of signature `(n,n,5)`. We take the classical statement as an
`axiom` (same contract as `fermatLastTheorem` / `mihailescu` / `darmonMerelCube`)
and derive the Beal two-equal fifth-power slices from it.

This is **not** Darmon–Merel (1997), which treats signatures `(n,n,2)` and
`(n,n,3)`. It is **not** a Lean proof of the `(n,n,5)` theorem; the equal-
exponent case `n = 5` overlaps FLT and is recorded separately for uniformity.
Even common exponents do **not** rewrite via the odd-permutation form.

Phase 7s uses this to close the even-sum residual at `z = 5` (even common
exponent forces `n ≥ 4`). The configuration `(3,3,5)` lies outside `n ≥ 4`
and is not claimed here.
-/

namespace DstDiophantine

namespace Theorems

/--
Generalised Fermat equation of signature `(n,n,5)`: there are no nonzero
integer solutions of `a^n + b^n = c^5` with `n ≥ 4` and
`gcd(|a|,|b|,|c|) = 1`.

Not present in mathlib at the pin used by this project; recorded explicitly as
an axiom rather than smuggled into a `sorry`. This is **not** an unconditional
Lean proof of the `(n,n,5)` theorem.
-/
axiom fermatSignatureNN5 :
    ∀ (a b c : ℤ) (n : ℕ),
      4 ≤ n →
      a ≠ 0 → b ≠ 0 → c ≠ 0 →
      Nat.gcd a.natAbs (Nat.gcd b.natAbs c.natAbs) = 1 →
      ¬ a ^ n + b ^ n = c ^ 5

/-- Abbreviation for the `(n,n,5)` hypothesis shape. -/
abbrev FermatSignatureNN5Hyp : Prop :=
  ∀ (a b c : ℤ) (n : ℕ),
    4 ≤ n → a ≠ 0 → b ≠ 0 → c ≠ 0 →
      Nat.gcd a.natAbs (Nat.gcd b.natAbs c.natAbs) = 1 →
      ¬ a ^ n + b ^ n = c ^ 5

private theorem bealGcd_neg_permute (A B C : ℤ) :
    bealGcd C (-B) A = bealGcd A B C ∧ bealGcd C (-A) B = bealGcd A B C := by
  constructor <;> simp [bealGcd, Nat.gcd_comm, Nat.gcd_left_comm]

/-- Odd power: `X^n + (-Y)^n = X^n - Y^n`. -/
private theorem odd_pow_add_neg {X Y : ℤ} {n : ℕ} (hodd : Odd n) :
    X ^ n + (-Y) ^ n = X ^ n - Y ^ n := by
  rw [Odd.neg_pow hodd Y]; ring

/--
Hypothesis form: `(n,n,5)` forbids `A^n + B^n = C^5` for `n ≥ 4` with
three-way gcd 1 (Beal `d = 1`, first-pair equal, third exponent 5).

Unlike Darmon–Merel `(n,n,3)`, the inequality `x ≠ 5` alone does not force
`4 ≤ x` (the `(3,3,5)` case is out of scope). Callers must supply `4 ≤ x`
(e.g. from `Even x` in the even-sum residual).
-/
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

/-- Phase 7s: axiom form of the `(n,n,5)` two-equal Beal slice (`n ≥ 4`). -/
theorem not_beal_two_equal_third_five {A B C : ℤ} {x y z : ℕ}
    (hx : 3 ≤ x) (hy : 3 ≤ y) (hz : 3 ≤ z)
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hgcd : bealGcd A B C = 1)
    (hd : bealExpGcd x y z = 1)
    (hxy : x = y) (hz5 : z = 5) (hx4 : 4 ≤ x)
    (hsol : A ^ x + B ^ y = C ^ z) : False :=
  not_beal_two_equal_third_five_of_NN5 fermatSignatureNN5
    hx hy hz hA hB hC hgcd hd hxy hz5 hx4 hsol

/--
Even common exponent forces `4 ≤ x`, so the even-sum residual at `z = 5` is
closed by the axiom with no extra hypothesis.
-/
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

/--
Phase 7s: `(5,n,n)` with odd `n ≥ 4` and `d = 1`.

From `A^5 + B^n = C^n` and odd `n`, rewrite to `C^n + (-B)^n = A^5`.
The case `n = 3` rewrites to signature `(3,3,5)` and is **not** claimed.
-/
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

/-- Phase 7s axiom form: `(5,n,n)` with odd common exponent `n ≥ 4`. -/
theorem not_beal_two_equal_first_five_odd {A B C : ℤ} {x y z : ℕ}
    (hx : 3 ≤ x) (hy : 3 ≤ y) (hz : 3 ≤ z)
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hgcd : bealGcd A B C = 1)
    (hd : bealExpGcd x y z = 1)
    (hyz : y = z) (hx5 : x = 5) (hyodd : Odd y) (hy4 : 4 ≤ y)
    (hsol : A ^ x + B ^ y = C ^ z) : False :=
  not_beal_two_equal_first_five_odd_of_NN5 fermatSignatureNN5
    hx hy hz hA hB hC hgcd hd hyz hx5 hyodd hy4 hsol

/--
Phase 7s: `(n,5,n)` with odd `n ≥ 4` and `d = 1`.

From `A^n + B^5 = C^n` and odd `n`, rewrite to `C^n + (-A)^n = B^5`.
The case `n = 3` is **not** claimed.
-/
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

/-- Phase 7s axiom form: `(n,5,n)` with odd common exponent `n ≥ 4`. -/
theorem not_beal_two_equal_second_five_odd {A B C : ℤ} {x y z : ℕ}
    (hx : 3 ≤ x) (hy : 3 ≤ y) (hz : 3 ≤ z)
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hgcd : bealGcd A B C = 1)
    (hd : bealExpGcd x y z = 1)
    (hxz : x = z) (hy5 : y = 5) (hxodd : Odd x) (hx4 : 4 ≤ x)
    (hsol : A ^ x + B ^ y = C ^ z) : False :=
  not_beal_two_equal_second_five_odd_of_NN5 fermatSignatureNN5
    hx hy hz hA hB hC hgcd hd hxz hy5 hxodd hx4 hsol

/--
Phase 7s: two-equal Beal with distinct exponent 5, when the common exponent is
at least 4 (and odd when the fifth power is not in third position).
-/
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
