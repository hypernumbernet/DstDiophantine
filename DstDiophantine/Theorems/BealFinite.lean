import DstDiophantine.Theorems.Beal
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic.NormNum

set_option linter.style.nativeDecide false

/-!
# Phase 7j: finite Beal certificate (no coprime solutions in a box)

Exhaustive `native_decide` search in the style of Goldbach / abc finite
certificates. Records that there is no three-way-coprime positive Beal solution
with bases `≤ Amax` and exponents in `3…Emax`. Known **non-coprime** solutions
are kept as regression witnesses (they are not Beal counterexamples).

Classical Beal is **not** claimed unconditionally.
-/

namespace DstDiophantine

namespace Theorems

/-! ### Bool search -/

/--
True when `(A,B,C,x,y,z)` is a positive coprime Beal solution (exponents ≥ 3).
-/
def isCoprimeBeal (A B C x y z : ℕ) : Bool :=
  decide
    (3 ≤ x ∧ 3 ≤ y ∧ 3 ≤ z ∧
      0 < A ∧ 0 < B ∧ 0 < C ∧
      A ^ x + B ^ y = C ^ z ∧
      Nat.gcd A (Nat.gcd B C) = 1)

/--
Bases `1…Amax` and exponents `3…Emax` (empty when `Emax < 3`).
-/
def hasCoprimeBealUpTo (Amax Emax : ℕ) : Bool :=
  (List.range' 1 Amax).any fun A =>
    (List.range' 1 Amax).any fun B =>
      (List.range' 1 Amax).any fun C =>
        (List.range' 3 (Emax + 1 - 3)).any fun x =>
          (List.range' 3 (Emax + 1 - 3)).any fun y =>
            (List.range' 3 (Emax + 1 - 3)).any fun z =>
              isCoprimeBeal A B C x y z

/-- Negation of `hasCoprimeBealUpTo` (certificate Bool). -/
def noCoprimeBealUpTo (Amax Emax : ℕ) : Bool :=
  !(hasCoprimeBealUpTo Amax Emax)

private theorem mem_bases {A Amax : ℕ} (hA : 0 < A) (hAmax : A ≤ Amax) :
    A ∈ List.range' 1 Amax :=
  List.mem_range'_1.mpr ⟨Nat.succ_le_of_lt hA, by omega⟩

private theorem mem_exps {x Emax : ℕ} (hx : 3 ≤ x) (hxE : x ≤ Emax) :
    x ∈ List.range' 3 (Emax + 1 - 3) :=
  List.mem_range'_1.mpr ⟨hx, by omega⟩

theorem isCoprimeBeal_sound {A B C x y z : ℕ}
    (h : isCoprimeBeal A B C x y z = true) :
    3 ≤ x ∧ 3 ≤ y ∧ 3 ≤ z ∧
      0 < A ∧ 0 < B ∧ 0 < C ∧
      A ^ x + B ^ y = C ^ z ∧
      Nat.gcd A (Nat.gcd B C) = 1 := by
  simpa [isCoprimeBeal, decide_eq_true_eq] using h

theorem noCoprimeBealUpTo_sound {Amax Emax : ℕ}
    (h : noCoprimeBealUpTo Amax Emax = true)
    {A B C x y z : ℕ}
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (hAmax : A ≤ Amax) (hBmax : B ≤ Amax) (hCmax : C ≤ Amax)
    (hx : 3 ≤ x) (hy : 3 ≤ y) (hz : 3 ≤ z)
    (hxE : x ≤ Emax) (hyE : y ≤ Emax) (hzE : z ≤ Emax)
    (hsol : A ^ x + B ^ y = C ^ z)
    (hgcd : Nat.gcd A (Nat.gcd B C) = 1) : False := by
  have hany : hasCoprimeBealUpTo Amax Emax = true := by
    refine (List.any_eq_true).mpr ⟨A, mem_bases hA hAmax, ?_⟩
    refine (List.any_eq_true).mpr ⟨B, mem_bases hB hBmax, ?_⟩
    refine (List.any_eq_true).mpr ⟨C, mem_bases hC hCmax, ?_⟩
    refine (List.any_eq_true).mpr ⟨x, mem_exps hx hxE, ?_⟩
    refine (List.any_eq_true).mpr ⟨y, mem_exps hy hyE, ?_⟩
    refine (List.any_eq_true).mpr ⟨z, mem_exps hz hzE, ?_⟩
    simp [isCoprimeBeal, hx, hy, hz, hA, hB, hC, hsol, hgcd]
  have : hasCoprimeBealUpTo Amax Emax = false := by
    simpa [noCoprimeBealUpTo, Bool.not_eq_true'] using h
  exact absurd hany (by simp [this])

/--
Finite-exploration certificate: no positive coprime Beal solution with bases
`≤ 8` and exponents in `3…5`.
-/
theorem beal_no_coprime_of_le_eight_five
    {A B C x y z : ℕ}
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (hAmax : A ≤ 8) (hBmax : B ≤ 8) (hCmax : C ≤ 8)
    (hx : 3 ≤ x) (hy : 3 ≤ y) (hz : 3 ≤ z)
    (hxE : x ≤ 5) (hyE : y ≤ 5) (hzE : z ≤ 5)
    (hsol : A ^ x + B ^ y = C ^ z)
    (hgcd : Nat.gcd A (Nat.gcd B C) = 1) : False :=
  noCoprimeBealUpTo_sound
    (by native_decide : noCoprimeBealUpTo 8 5 = true)
    hA hB hC hAmax hBmax hCmax hx hy hz hxE hyE hzE hsol hgcd

/-! ### Known non-coprime solutions (not counterexamples) -/

/-- Classic non-coprime identity `3³ + 6³ = 3⁵` (gcd 3). -/
theorem beal_known_noncoprime_three_six :
    (3 : ℤ) ^ 3 + 6 ^ 3 = 3 ^ 5 ∧ bealGcd 3 6 3 = 3 := by
  constructor
  · norm_num
  · native_decide

/-- Classic non-coprime identity `2³ + 2³ = 2⁴` (gcd 2). -/
theorem beal_known_noncoprime_two_two :
    (2 : ℤ) ^ 3 + 2 ^ 3 = 2 ^ 4 ∧ bealGcd 2 2 2 = 2 := by
  constructor
  · norm_num
  · native_decide

end Theorems

end DstDiophantine
