import DstDiophantine.Theorems.Beal
import Mathlib.Data.Int.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Signature `(3,4,5)` (phase 7w)

mathlib (v4.34) does not contain Siksek–Stoll's determination of the primitive
integer solutions of `x³ + y⁴ + z⁵ = 0`. We take that statement as an `axiom`
(same contract as `darmonMerelCube`) and close every ordering of the Beal
signature `(3,4,5)`.

The only primitive solutions have a vanishing coordinate. A Beal solution has
three nonzero bases, so the signature is empty in the coprime range. The
exponent `4` is even and the exponents `3` and `5` are odd, so each ordering
rewrites to the same equation by moving one term and absorbing the sign of an
odd power into its base. Classical Beal is **not** claimed unconditionally.
-/

namespace DstDiophantine

namespace Theorems

/-- The three exponents are `3`, `4` and `5`, in any order. -/
def IsSignature345 (x y z : ℕ) : Prop :=
  (x = 3 ∧ y = 4 ∧ z = 5) ∨
    (x = 3 ∧ y = 5 ∧ z = 4) ∨
      (x = 4 ∧ y = 3 ∧ z = 5) ∨
        (x = 4 ∧ y = 5 ∧ z = 3) ∨
          (x = 5 ∧ y = 3 ∧ z = 4) ∨
            (x = 5 ∧ y = 4 ∧ z = 3)

instance {x y z : ℕ} : Decidable (IsSignature345 x y z) := by
  unfold IsSignature345
  infer_instance

/--
Siksek–Stoll (2012): the only integer solutions of `x³ + y⁴ + z⁵ = 0` with
`gcd(|x|,|y|,|z|) = 1` have a vanishing coordinate.

Not present in mathlib at the pin used by this project; recorded explicitly as
an axiom rather than smuggled into a `sorry`. This is **not** a Lean proof of
Siksek–Stoll. The classical list of primitive solutions is contained in this
vanishing statement, which is all the Beal application uses.
-/
axiom siksekStoll345 :
    ∀ x y z : ℤ,
      Nat.gcd x.natAbs (Nat.gcd y.natAbs z.natAbs) = 1 →
      x ^ 3 + y ^ 4 + z ^ 5 = 0 →
      x = 0 ∨ y = 0 ∨ z = 0

private theorem odd_pow_neg {X : ℤ} {n : ℕ} (hodd : Odd n) : (-X) ^ n = - X ^ n :=
  Odd.neg_pow hodd X

private theorem bealGcd_abs_perm (A B C : ℤ) :
    bealGcd (-A) C (-B) = bealGcd A B C ∧
      bealGcd B A (-C) = bealGcd A B C ∧
        bealGcd (-C) A B = bealGcd A B C ∧
          bealGcd (-B) C (-A) = bealGcd A B C ∧
            bealGcd (-C) B A = bealGcd A B C := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [bealGcd, Nat.gcd_comm, Nat.gcd_left_comm]

/--
Phase 7w: no coprime nonzero Beal solution of signature `(3,4,5)`, in any order.
-/
theorem not_beal_signature_345
    {A B C : ℤ} {x y z : ℕ}
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hgcd : bealGcd A B C = 1)
    (hshape : IsSignature345 x y z)
    (hsol : A ^ x + B ^ y = C ^ z) : False := by
  rcases hshape with ⟨hx, hy, hz⟩ | ⟨hx, hy, hz⟩ | ⟨hx, hy, hz⟩ |
      ⟨hx, hy, hz⟩ | ⟨hx, hy, hz⟩ | ⟨hx, hy, hz⟩
  · subst hx; subst hy; subst hz
    -- A³ + B⁴ = C⁵
    have hrew : A ^ 3 + B ^ 4 + (-C) ^ 5 = 0 := by
      rw [odd_pow_neg (by decide : Odd 5)]
      linarith [hsol]
    have hzero := siksekStoll345 A B (-C) (by simpa [bealGcd] using hgcd) hrew
    rcases hzero with h | h | h
    · exact hA h
    · exact hB h
    · exact hC (neg_eq_zero.mp h)
  · subst hx; subst hy; subst hz
    -- A³ + B⁵ = C⁴
    have hrew : (-A) ^ 3 + C ^ 4 + (-B) ^ 5 = 0 := by
      rw [odd_pow_neg (by decide : Odd 3), odd_pow_neg (by decide : Odd 5)]
      linarith [hsol]
    have hgcd' : bealGcd (-A) C (-B) = 1 := (bealGcd_abs_perm A B C).1.trans hgcd
    have hzero := siksekStoll345 (-A) C (-B) (by simpa [bealGcd] using hgcd') hrew
    rcases hzero with h | h | h
    · exact hA (neg_eq_zero.mp h)
    · exact hC h
    · exact hB (neg_eq_zero.mp h)
  · subst hx; subst hy; subst hz
    -- A⁴ + B³ = C⁵
    have hrew : B ^ 3 + A ^ 4 + (-C) ^ 5 = 0 := by
      rw [odd_pow_neg (by decide : Odd 5)]
      linarith [hsol]
    have hgcd' : bealGcd B A (-C) = 1 := (bealGcd_abs_perm A B C).2.1.trans hgcd
    have hzero := siksekStoll345 B A (-C) (by simpa [bealGcd] using hgcd') hrew
    rcases hzero with h | h | h
    · exact hB h
    · exact hA h
    · exact hC (neg_eq_zero.mp h)
  · subst hx; subst hy; subst hz
    -- A⁴ + B⁵ = C³
    have hrew : (-C) ^ 3 + A ^ 4 + B ^ 5 = 0 := by
      rw [odd_pow_neg (by decide : Odd 3)]
      linarith [hsol]
    have hgcd' : bealGcd (-C) A B = 1 := (bealGcd_abs_perm A B C).2.2.1.trans hgcd
    have hzero := siksekStoll345 (-C) A B (by simpa [bealGcd] using hgcd') hrew
    rcases hzero with h | h | h
    · exact hC (neg_eq_zero.mp h)
    · exact hA h
    · exact hB h
  · subst hx; subst hy; subst hz
    -- A⁵ + B³ = C⁴
    have hrew : (-B) ^ 3 + C ^ 4 + (-A) ^ 5 = 0 := by
      rw [odd_pow_neg (by decide : Odd 3), odd_pow_neg (by decide : Odd 5)]
      linarith [hsol]
    have hgcd' : bealGcd (-B) C (-A) = 1 := (bealGcd_abs_perm A B C).2.2.2.1.trans hgcd
    have hzero := siksekStoll345 (-B) C (-A) (by simpa [bealGcd] using hgcd') hrew
    rcases hzero with h | h | h
    · exact hB (neg_eq_zero.mp h)
    · exact hC h
    · exact hA (neg_eq_zero.mp h)
  · subst hx; subst hy; subst hz
    -- A⁵ + B⁴ = C³
    have hrew : (-C) ^ 3 + B ^ 4 + A ^ 5 = 0 := by
      rw [odd_pow_neg (by decide : Odd 3)]
      linarith [hsol]
    have hgcd' : bealGcd (-C) B A = 1 := (bealGcd_abs_perm A B C).2.2.2.2.trans hgcd
    have hzero := siksekStoll345 (-C) B A (by simpa [bealGcd] using hgcd') hrew
    rcases hzero with h | h | h
    · exact hC (neg_eq_zero.mp h)
    · exact hB h
    · exact hA h

end Theorems

end DstDiophantine
