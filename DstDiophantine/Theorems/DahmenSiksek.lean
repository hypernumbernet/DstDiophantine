import DstDiophantine.Theorems.Bruin
import Mathlib.Data.Int.Basic
import Mathlib.Tactic.Linarith

/-!
# Repeated fifth powers (phase 7y)

mathlib (v4.34) does not contain Dahmen–Siksek's determination of the
coprime solutions of `x⁵ + y⁵ = zˡ` for `l = 7` and `l = 19`. We take that
statement as an `axiom` (same contract as `siksekStoll345`) and close every
ordering of the Beal signatures `(5,5,7)` and `(5,5,19)`.

Every exponent is odd, so each ordering rewrites to a sum of two fifth powers
by carrying one term and absorbing its sign into the base. The only coprime
solutions have a vanishing coordinate, hence none is a Beal solution.

The signature `(7,7,5)` is not a new case: it is the position `(n,n,5)` with
odd common exponent, already closed by `not_beal_two_equal_fifth_slice`,
including the odd permutations `(5,7,7)` and `(7,5,7)`. The companions `11`
and `13` are conditional on the generalised Riemann hypothesis in the same
source and are **not** closed here. Classical Beal is **not** claimed
unconditionally.
-/

namespace DstDiophantine

namespace Theorems

/--
Two of the exponents equal `5` and the third equals `l`, in any order.
-/
def IsRepeatedFifthTo (l x y z : ℕ) : Prop :=
  (x = 5 ∧ y = 5 ∧ z = l) ∨
    (y = 5 ∧ z = 5 ∧ x = l) ∨
      (x = 5 ∧ z = 5 ∧ y = l)

instance {l x y z : ℕ} : Decidable (IsRepeatedFifthTo l x y z) := by
  unfold IsRepeatedFifthTo
  infer_instance

/--
Repeated fifth power beside an unmatched exponent `7` or `19`, every order.
These are the unconditional Dahmen–Siksek signatures inside the odd two-equal
family. `(7,7,5)` is excluded: it is already signature `(n,n,5)`.
-/
def IsRepeatedFifthShape (x y z : ℕ) : Prop :=
  IsRepeatedFifthTo 7 x y z ∨ IsRepeatedFifthTo 19 x y z

instance {x y z : ℕ} : Decidable (IsRepeatedFifthShape x y z) := by
  unfold IsRepeatedFifthShape
  infer_instance

/--
Dahmen–Siksek: there is no nonzero coprime solution of `a⁵ + b⁵ = cˡ`
for `l = 7` or `l = 19`.

Not present in mathlib at the pin used by this project; recorded explicitly as
an axiom rather than smuggled into a `sorry`. This is **not** a Lean proof of
Dahmen–Siksek. The published list of coprime solutions consists entirely of
triples with a vanishing coordinate, which is all the Beal application uses.
The companions `11` and `13` are not included.
-/
axiom sumTwoFifthsNotSeventhOrNineteenth :
    ∀ (a b c : ℤ) (l : ℕ),
      (l = 7 ∨ l = 19) →
      a ≠ 0 → b ≠ 0 → c ≠ 0 →
      Nat.gcd a.natAbs (Nat.gcd b.natAbs c.natAbs) = 1 →
      ¬ a ^ 5 + b ^ 5 = c ^ l

private theorem odd_pow_neg {X : ℤ} {n : ℕ} (hodd : Odd n) : (-X) ^ n = - X ^ n :=
  Odd.neg_pow hodd X

private theorem bealGcd_fifth_perm (A B C : ℤ) :
    bealGcd C (-B) A = bealGcd A B C ∧
      bealGcd C (-A) B = bealGcd A B C := by
  constructor <;> simp [bealGcd, Nat.gcd_comm, Nat.gcd_left_comm]

/--
No coprime nonzero Beal solution whose exponents are a repeated five beside
`7` or `19`, in any order.
-/
theorem not_beal_repeated_fifth_to
    {A B C : ℤ} {x y z l : ℕ}
    (hl : l = 7 ∨ l = 19)
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hgcd : bealGcd A B C = 1)
    (hshape : IsRepeatedFifthTo l x y z)
    (hsol : A ^ x + B ^ y = C ^ z) : False := by
  have hgcdB : bealGcd C (-B) A = 1 := (bealGcd_fifth_perm A B C).1.trans hgcd
  have hgcdA : bealGcd C (-A) B = 1 := (bealGcd_fifth_perm A B C).2.trans hgcd
  rcases hl with rfl | rfl
  · rcases hshape with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact sumTwoFifthsNotSeventhOrNineteenth A B C 7 (Or.inl rfl) hA hB hC hgcd hsol
    · have hrew : C ^ 5 + (-B) ^ 5 = A ^ 7 := by
        rw [odd_pow_neg (by decide : Odd 5)]
        linarith [hsol]
      exact sumTwoFifthsNotSeventhOrNineteenth C (-B) A 7 (Or.inl rfl) hC
        (neg_ne_zero.mpr hB) hA hgcdB hrew
    · have hrew : C ^ 5 + (-A) ^ 5 = B ^ 7 := by
        rw [odd_pow_neg (by decide : Odd 5)]
        linarith [hsol]
      exact sumTwoFifthsNotSeventhOrNineteenth C (-A) B 7 (Or.inl rfl) hC
        (neg_ne_zero.mpr hA) hB hgcdA hrew
  · rcases hshape with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact sumTwoFifthsNotSeventhOrNineteenth A B C 19 (Or.inr rfl) hA hB hC hgcd hsol
    · have hrew : C ^ 5 + (-B) ^ 5 = A ^ 19 := by
        rw [odd_pow_neg (by decide : Odd 5)]
        linarith [hsol]
      exact sumTwoFifthsNotSeventhOrNineteenth C (-B) A 19 (Or.inr rfl) hC
        (neg_ne_zero.mpr hB) hA hgcdB hrew
    · have hrew : C ^ 5 + (-A) ^ 5 = B ^ 19 := by
        rw [odd_pow_neg (by decide : Odd 5)]
        linarith [hsol]
      exact sumTwoFifthsNotSeventhOrNineteenth C (-A) B 19 (Or.inr rfl) hC
        (neg_ne_zero.mpr hA) hB hgcdA hrew

theorem not_beal_repeated_fifth_shape
    {A B C : ℤ} {x y z : ℕ}
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hgcd : bealGcd A B C = 1)
    (hshape : IsRepeatedFifthShape x y z)
    (hsol : A ^ x + B ^ y = C ^ z) : False := by
  rcases hshape with h | h
  · exact not_beal_repeated_fifth_to (Or.inl rfl) hA hB hC hgcd h hsol
  · exact not_beal_repeated_fifth_to (Or.inr rfl) hA hB hC hgcd h hsol

/--
**Residual** (phase 7y, unproved): odd two-equal Beal outside cube-pair shapes
and outside a repeated five beside `7` or `19`.
-/
def BealTwoEqualOddOutsideRepeatedFifthResidual : Prop :=
  ∀ (A B C : ℤ) (x y z : ℕ) (_hx : 3 ≤ x) (_hy : 3 ≤ y) (_hz : 3 ≤ z)
    (_hA : A ≠ 0) (_hB : B ≠ 0) (_hC : C ≠ 0),
    bealGcd A B C = 1 →
    bealExpGcd x y z = 1 →
    ((x = y ∧ Odd x) ∨ (y = z ∧ Odd y) ∨ (x = z ∧ Odd x)) →
    ¬ IsCubePairPowerShape x y z →
    ¬ IsRepeatedFifthShape x y z →
      ¬ A ^ x + B ^ y = C ^ z

/--
Phase 7y: the odd two-equal residual follows from its body outside cube pairs
and outside the repeated-fifth signatures `(5,5,7)` and `(5,5,19)`.
-/
theorem BealTwoEqualOddResidual_of_outside_repeated_fifth
    (hOut : BealTwoEqualOddOutsideRepeatedFifthResidual) :
    BealTwoEqualOddResidual := by
  intro A B C x y z hx hy hz hA hB hC hgcd hd hpair hsol
  by_cases hcube : IsCubePairPowerShape x y z
  · exact not_beal_cube_pair_power_shape hx hy hz hA hB hC hgcd hcube hsol
  · by_cases hfifth : IsRepeatedFifthShape x y z
    · exact not_beal_repeated_fifth_shape hA hB hC hgcd hfifth hsol
    · exact hOut A B C x y z hx hy hz hA hB hC hgcd hd hpair hcube hfifth hsol

theorem BealTwoEqualOddOutsideCubePairResidual_of_outside_repeated_fifth
    (hOut : BealTwoEqualOddOutsideRepeatedFifthResidual) :
    BealTwoEqualOddOutsideCubePairResidual := by
  intro A B C x y z hx hy hz hA hB hC hgcd hd hpair hcube hsol
  by_cases hfifth : IsRepeatedFifthShape x y z
  · exact not_beal_repeated_fifth_shape hA hB hC hgcd hfifth hsol
  · exact hOut A B C x y z hx hy hz hA hB hC hgcd hd hpair hcube hfifth hsol

end Theorems

end DstDiophantine
