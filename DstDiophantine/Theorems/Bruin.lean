import DstDiophantine.Theorems.BealMixed
import Mathlib.Data.Int.Basic
import Mathlib.Tactic.Linarith

/-!
# Sums of two cubes as fourth and fifth powers (phase 7v)

mathlib (v4.34) does not contain Bruin's theorem that a sum of two cubes is
never a fourth or a fifth power. We take that classical statement as an
`axiom` (same contract as `darmonMerelCube` / `fermatSignatureNN5`) and close
the odd two-equal Beal shapes in which the repeated exponent is `3` and the
remaining exponent is `4` or `5`.

The exponent `3` is odd, so each placement of the repeated exponent rewrites,
by moving one cube across the equation, into `a³ + b³ = cⁿ`. Signature
`(n,n,5)` with `n ≥ 4` stays with `fermatSignatureNN5`; the case `n = 3` is
this theorem, not that one. Classical Beal is **not** claimed unconditionally.
-/

namespace DstDiophantine

namespace Theorems

/--
Two exponents equal `3` and the third equals `4` or `5`, in any position.
-/
def IsBruinTwoCubeShape (x y z : ℕ) : Prop :=
  (x = 3 ∧ y = 3 ∧ (z = 4 ∨ z = 5)) ∨
    (y = 3 ∧ z = 3 ∧ (x = 4 ∨ x = 5)) ∨
      (x = 3 ∧ z = 3 ∧ (y = 4 ∨ y = 5))

instance {x y z : ℕ} : Decidable (IsBruinTwoCubeShape x y z) := by
  unfold IsBruinTwoCubeShape
  infer_instance

/--
Bruin (2000): there are no nonzero integer solutions of `a³ + b³ = cⁿ` for
`n = 4` or `n = 5` with `gcd(|a|,|b|,|c|) = 1`.

Not present in mathlib at the pin used by this project; recorded explicitly as
an axiom rather than smuggled into a `sorry`. This is **not** a Lean proof of
Bruin's theorem. On this equation a three-way gcd of `1` is the coprimality
hypothesis of the classical statement.
-/
axiom bruinSumTwoCubes :
    ∀ (a b c : ℤ) (n : ℕ),
      (n = 4 ∨ n = 5) →
      a ≠ 0 → b ≠ 0 → c ≠ 0 →
      Nat.gcd a.natAbs (Nat.gcd b.natAbs c.natAbs) = 1 →
      ¬ a ^ 3 + b ^ 3 = c ^ n

/-- Abbreviation for the two-cube fourth/fifth-power hypothesis. -/
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

/--
Phase 7v: a coprime Beal solution whose exponents are a two-cube fourth or
fifth power is impossible.
-/
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

/-- Phase 7v axiom form of the two-cube fourth/fifth-power slice. -/
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

/--
**Residual** (phase 7v, unproved): odd two-equal Beal outside the two-cube
fourth and fifth powers. The removed shapes are `IsBruinTwoCubeShape`.
-/
def BealTwoEqualOddOutsideBruinResidual : Prop :=
  ∀ (A B C : ℤ) (x y z : ℕ) (_hx : 3 ≤ x) (_hy : 3 ≤ y) (_hz : 3 ≤ z)
    (_hA : A ≠ 0) (_hB : B ≠ 0) (_hC : C ≠ 0),
    bealGcd A B C = 1 →
    bealExpGcd x y z = 1 →
    ((x = y ∧ Odd x) ∨ (y = z ∧ Odd y) ∨ (x = z ∧ Odd x)) →
    ¬ IsBruinTwoCubeShape x y z →
      ¬ A ^ x + B ^ y = C ^ z

/--
Phase 7v: the odd two-equal residual follows from its body outside the
two-cube fourth and fifth powers.
-/
theorem BealTwoEqualOddResidual_of_outside_bruin
    (hOut : BealTwoEqualOddOutsideBruinResidual) :
    BealTwoEqualOddResidual := by
  intro A B C x y z hx hy hz hA hB hC hgcd hd hpair hsol
  by_cases hshape : IsBruinTwoCubeShape x y z
  · exact not_beal_bruin_two_cube_shape hx hy hz hA hB hC hgcd hd hshape hsol
  · exact hOut A B C x y z hx hy hz hA hB hC hgcd hd hpair hshape hsol

end Theorems

end DstDiophantine
