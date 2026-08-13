import Mathlib.Data.Nat.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Mihăilescu's theorem (Catalan's conjecture) as an axiom

mathlib (v4.34) does not contain Mihăilescu's theorem.  We take the classical
statement as an `axiom` and derive Beal unit-base fragments from it.

The only solution in the natural numbers of `a^x − b^y = 1` with
`a, b > 0` and `x, y > 1` is `3² − 2³ = 1`.
-/

namespace DstDiophantine

namespace Theorems

/--
Mihăilescu's theorem (Catalan's conjecture), 2002.

Not present in mathlib at the pin used by this project; recorded explicitly as
an axiom rather than smuggled into a `sorry`.
-/
axiom mihailescu :
    ∀ (a b x y : ℕ),
      1 < x → 1 < y → 0 < a → 0 < b →
      a ^ x = b ^ y + 1 →
        a = 3 ∧ x = 2 ∧ b = 2 ∧ y = 3

/-- No perfect-power difference of 1 when both exponents are at least 3. -/
theorem not_nat_pow_sub_one_of_exponents_ge_three {a b x y : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hx : 3 ≤ x) (hy : 3 ≤ y) :
    ¬ a ^ x = b ^ y + 1 := by
  intro heq
  have hx1 : 1 < x := Nat.lt_of_lt_of_le (by decide : 1 < 3) hx
  have hy1 : 1 < y := Nat.lt_of_lt_of_le (by decide : 1 < 3) hy
  obtain ⟨_, hx2, _, _⟩ := mihailescu a b x y hx1 hy1 ha hb heq
  exact absurd hx2 (by omega : x ≠ 2)

/-- Integer form: positive bases, exponents ≥ 3. -/
theorem not_int_pow_sub_one_of_exponents_ge_three {a b : ℤ} {x y : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hx : 3 ≤ x) (hy : 3 ≤ y) :
    ¬ a ^ x - b ^ y = 1 := by
  intro h
  have haN : 0 < a.natAbs := Int.natAbs_pos.mpr ha.ne'
  have hbN : 0 < b.natAbs := Int.natAbs_pos.mpr hb.ne'
  have ha' : (a.natAbs : ℤ) = a := Int.natAbs_of_nonneg ha.le
  have hb' : (b.natAbs : ℤ) = b := Int.natAbs_of_nonneg hb.le
  have heqN : a.natAbs ^ x = b.natAbs ^ y + 1 := by
    have : (a.natAbs : ℤ) ^ x = (b.natAbs : ℤ) ^ y + 1 := by
      rw [ha', hb']; linarith [h]
    exact_mod_cast this
  exact not_nat_pow_sub_one_of_exponents_ge_three haN hbN hx hy heqN

/--
Positive unit base: `1^x + B^y = C^z` is impossible for `B, C > 0` and
exponents ≥ 3.
-/
theorem not_one_pow_add_pos_pow_eq_pos_pow {B C : ℤ} {x y z : ℕ}
    (hB : 0 < B) (hC : 0 < C) (_hx : 3 ≤ x) (hy : 3 ≤ y) (hz : 3 ≤ z) :
    ¬ ((1 : ℤ) ^ x + B ^ y = C ^ z) := by
  intro hsol
  have h1 : (1 : ℤ) ^ x = 1 := one_pow x
  have hdiff : C ^ z - B ^ y = 1 := by linarith [hsol, h1]
  exact not_int_pow_sub_one_of_exponents_ge_three hC hB hz hy hdiff

/--
Positive bases with `|A| = 1`: forbids the Beal equation via Mihăilescu.
Classical Beal is usually stated for positive integers; this is the live residual.
-/
theorem not_unitAbs_pow_add_pow_eq_pow_pos {A B C : ℤ} {x y z : ℕ}
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (hA1 : A.natAbs = 1) (hx : 3 ≤ x) (hy : 3 ≤ y) (hz : 3 ≤ z) :
    ¬ A ^ x + B ^ y = C ^ z := by
  have hAeq : A = 1 := by
    have : (A.natAbs : ℤ) = A := Int.natAbs_of_nonneg hA.le
    rw [hA1] at this
    exact_mod_cast this.symm
  rw [hAeq]
  exact not_one_pow_add_pos_pow_eq_pos_pow hB hC hx hy hz

end Theorems

end DstDiophantine
