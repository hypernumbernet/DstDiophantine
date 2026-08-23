import DstDiophantine.Theorems.Beal
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic.NormNum

set_option linter.style.nativeDecide false

/-!
# Phase 7j / 7k / 7m: finite Beal certificates

* **Box search** (phase 7j): bases and `C` all `≤ Amax`, exponents in `3…Emax`.
* **Perfect-power search** (phase 7k–7m): bases `≤ Amax`, exponents in `3…Emax`,
  but `C` is recovered as a positive `z`-th root of `A^x + B^y` (unbounded).
  Phase 7m raises the certificate to bases `≤ 14` (exponents `3…6`).

Known **non-coprime** solutions are kept as regression witnesses (they are not
Beal counterexamples). Classical Beal is **not** claimed unconditionally.
-/

namespace DstDiophantine

namespace Theorems

/-! ### Bool search (bounded box) -/

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

/-! ### Perfect-power search (phase 7k; `C` unbounded) -/

/--
Search for a positive `z`-th root of `s`, starting at `c`, with fuel bound.
Returns `some C` when `C ^ z = s`.
-/
def findNthRootGO (s z c fuel : ℕ) : Option ℕ :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    if c ^ z = s then some c
    else if s < c ^ z then none
    else findNthRootGO s z (c + 1) fuel

/-- Positive `z`-th root of `s`, if any (`z = 0` yields `none`). -/
def findNthRoot (s z : ℕ) : Option ℕ :=
  if z = 0 then none
  else findNthRootGO s z 1 (s + 1)

/-- True when `s` is a positive perfect `z`-th power. -/
def isNthPower (s z : ℕ) : Bool :=
  (findNthRoot s z).isSome

theorem findNthRootGO_sound {s z c fuel C : ℕ}
    (h : findNthRootGO s z c fuel = some C) : C ^ z = s ∧ c ≤ C := by
  induction fuel generalizing c with
  | zero =>
    simp [findNthRootGO] at h
  | succ fuel ih =>
    by_cases hEq : c ^ z = s
    · have h' : some c = some C := by
        simpa [findNthRootGO, hEq] using h
      obtain rfl := Option.some_inj.mp h'
      exact ⟨hEq, le_rfl⟩
    · by_cases hGt : s < c ^ z
      · have : findNthRootGO s z c (fuel + 1) = none := by
          simp [findNthRootGO, hEq, hGt]
        simp [this] at h
      · have h' : findNthRootGO s z (c + 1) fuel = some C := by
          simpa [findNthRootGO, hEq, hGt] using h
        obtain ⟨heq, hle⟩ := ih h'
        exact ⟨heq, Nat.le_trans (Nat.le_succ c) hle⟩

theorem findNthRoot_sound {s z C : ℕ}
    (h : findNthRoot s z = some C) : 0 < C ∧ C ^ z = s := by
  by_cases hz : z = 0
  · simp [findNthRoot, hz] at h
  · have h' : findNthRootGO s z 1 (s + 1) = some C := by
      simpa [findNthRoot, hz] using h
    obtain ⟨heq, hle⟩ := findNthRootGO_sound h'
    exact ⟨Nat.lt_of_lt_of_le (by decide : 0 < 1) hle, heq⟩

theorem findNthRootGO_complete {s z c fuel : ℕ}
    (_hz : 0 < z) (_hc : 0 < c)
    (hfuel : ∃ C, c ≤ C ∧ C ^ z = s ∧ C < c + fuel) :
    (findNthRootGO s z c fuel).isSome := by
  induction fuel generalizing c with
  | zero =>
    obtain ⟨C, hle, _, hlt⟩ := hfuel
    omega
  | succ fuel ih =>
    obtain ⟨C, hle, heq, hlt⟩ := hfuel
    by_cases hEq : c ^ z = s
    · simp [findNthRootGO, hEq]
    · by_cases hGt : s < c ^ z
      · have : c ^ z ≤ s := by
          have := Nat.pow_le_pow_left hle z
          simpa [heq] using this
        exact False.elim (Nat.lt_le_asymm hGt this)
      · have hcC : c < C := by
          by_contra hnot
          have heqC : c = C := Nat.le_antisymm hle (Nat.not_lt.mp hnot)
          exact hEq (heqC ▸ heq)
        have hrec :
            (findNthRootGO s z (c + 1) fuel).isSome :=
          ih (by omega) ⟨C, Nat.succ_le_of_lt hcC, heq, by omega⟩
        simpa [findNthRootGO, hEq, hGt] using hrec

theorem findNthRoot_complete {s z C : ℕ}
    (hz : 0 < z) (hC : 0 < C) (heq : C ^ z = s) :
    (findNthRoot s z).isSome := by
  have hzne : z ≠ 0 := Nat.pos_iff_ne_zero.mp hz
  simp only [findNthRoot, hzne, ↓reduceIte]
  refine findNthRootGO_complete hz (by decide : 0 < 1) ⟨C, Nat.succ_le_of_lt hC, heq, ?_⟩
  have : C ≤ C ^ z := Nat.le_self_pow hzne C
  omega

/--
True when `A^x + B^y` is a positive perfect `z`-th power `C^z` with
three-way gcd 1 and exponents / bases positive as in Beal.
-/
def isCoprimeBealPerfectPower (A B x y z : ℕ) : Bool :=
  decide (3 ≤ x ∧ 3 ≤ y ∧ 3 ≤ z ∧ 0 < A ∧ 0 < B) &&
    match findNthRoot (A ^ x + B ^ y) z with
    | some C => decide (Nat.gcd A (Nat.gcd B C) = 1)
    | none => false

/--
Bases `1…Amax`, exponents `3…Emax`: whether a coprime perfect-power Beal
solution exists (`C` recovered as a root, not bounded by `Amax`).
-/
def hasCoprimeBealPerfectPowerUpTo (Amax Emax : ℕ) : Bool :=
  (List.range' 1 Amax).any fun A =>
    (List.range' 1 Amax).any fun B =>
      (List.range' 3 (Emax + 1 - 3)).any fun x =>
        (List.range' 3 (Emax + 1 - 3)).any fun y =>
          (List.range' 3 (Emax + 1 - 3)).any fun z =>
            isCoprimeBealPerfectPower A B x y z

def noCoprimeBealPerfectPowerUpTo (Amax Emax : ℕ) : Bool :=
  !(hasCoprimeBealPerfectPowerUpTo Amax Emax)

theorem isCoprimeBealPerfectPower_sound {A B x y z : ℕ}
    (h : isCoprimeBealPerfectPower A B x y z = true) :
    ∃ C : ℕ,
      3 ≤ x ∧ 3 ≤ y ∧ 3 ≤ z ∧
        0 < A ∧ 0 < B ∧ 0 < C ∧
          A ^ x + B ^ y = C ^ z ∧
            Nat.gcd A (Nat.gcd B C) = 1 := by
  simp only [isCoprimeBealPerfectPower, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hx, hy, hz, hA, hB⟩, hroot⟩ := h
  match hC : findNthRoot (A ^ x + B ^ y) z with
  | none => simp [hC] at hroot
  | some C =>
    simp only [hC, decide_eq_true_eq] at hroot
    obtain ⟨hCpos, heq⟩ := findNthRoot_sound hC
    exact ⟨C, hx, hy, hz, hA, hB, hCpos, heq.symm, hroot⟩

theorem noCoprimeBealPerfectPowerUpTo_sound {Amax Emax : ℕ}
    (h : noCoprimeBealPerfectPowerUpTo Amax Emax = true)
    {A B C x y z : ℕ}
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (hAmax : A ≤ Amax) (hBmax : B ≤ Amax)
    (hx : 3 ≤ x) (hy : 3 ≤ y) (hz : 3 ≤ z)
    (hxE : x ≤ Emax) (hyE : y ≤ Emax) (hzE : z ≤ Emax)
    (hsol : A ^ x + B ^ y = C ^ z)
    (hgcd : Nat.gcd A (Nat.gcd B C) = 1) : False := by
  have hz0 : 0 < z := Nat.lt_of_lt_of_le (by decide : 0 < 3) hz
  have hfind : findNthRoot (A ^ x + B ^ y) z = some C := by
    have hsome := findNthRoot_complete hz0 hC hsol.symm
    match hC' : findNthRoot (A ^ x + B ^ y) z with
    | none => simp [hC'] at hsome
    | some C' =>
      obtain ⟨_, heq'⟩ := findNthRoot_sound hC'
      have hpow : C' ^ z = C ^ z := by
        calc
          C' ^ z = A ^ x + B ^ y := heq'
          _ = C ^ z := hsol
      have hCC : C' = C :=
        Nat.pow_left_injective (Nat.pos_iff_ne_zero.mp hz0) hpow
      exact congrArg some hCC
  have hpp : isCoprimeBealPerfectPower A B x y z = true := by
    simp [isCoprimeBealPerfectPower, hx, hy, hz, hA, hB, hfind, hgcd]
  have hany : hasCoprimeBealPerfectPowerUpTo Amax Emax = true := by
    refine (List.any_eq_true).mpr ⟨A, mem_bases hA hAmax, ?_⟩
    refine (List.any_eq_true).mpr ⟨B, mem_bases hB hBmax, ?_⟩
    refine (List.any_eq_true).mpr ⟨x, mem_exps hx hxE, ?_⟩
    refine (List.any_eq_true).mpr ⟨y, mem_exps hy hyE, ?_⟩
    refine (List.any_eq_true).mpr ⟨z, mem_exps hz hzE, ?_⟩
    exact hpp
  have : hasCoprimeBealPerfectPowerUpTo Amax Emax = false := by
    simpa [noCoprimeBealPerfectPowerUpTo, Bool.not_eq_true'] using h
  exact absurd hany (by simp [this])

/--
Phase 7k: no positive coprime Beal solution with bases `≤ 12` and exponents in
`3…6`, allowing unbounded `C` recovered as a perfect power.
-/
theorem beal_no_coprime_perfect_power_of_le_twelve_six
    {A B C x y z : ℕ}
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (hAmax : A ≤ 12) (hBmax : B ≤ 12)
    (hx : 3 ≤ x) (hy : 3 ≤ y) (hz : 3 ≤ z)
    (hxE : x ≤ 6) (hyE : y ≤ 6) (hzE : z ≤ 6)
    (hsol : A ^ x + B ^ y = C ^ z)
    (hgcd : Nat.gcd A (Nat.gcd B C) = 1) : False :=
  noCoprimeBealPerfectPowerUpTo_sound
    (by native_decide : noCoprimeBealPerfectPowerUpTo 12 6 = true)
    hA hB hC hAmax hBmax hx hy hz hxE hyE hzE hsol hgcd

/--
Phase 7l probe: no positive coprime Beal solution with bases `≤ 13` and
exponents in `3…6`, allowing unbounded `C` recovered as a perfect power.
-/
theorem beal_no_coprime_perfect_power_of_le_thirteen_six
    {A B C x y z : ℕ}
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (hAmax : A ≤ 13) (hBmax : B ≤ 13)
    (hx : 3 ≤ x) (hy : 3 ≤ y) (hz : 3 ≤ z)
    (hxE : x ≤ 6) (hyE : y ≤ 6) (hzE : z ≤ 6)
    (hsol : A ^ x + B ^ y = C ^ z)
    (hgcd : Nat.gcd A (Nat.gcd B C) = 1) : False :=
  noCoprimeBealPerfectPowerUpTo_sound
    (by native_decide : noCoprimeBealPerfectPowerUpTo 13 6 = true)
    hA hB hC hAmax hBmax hx hy hz hxE hyE hzE hsol hgcd

/--
Phase 7m: no positive coprime Beal solution with bases `≤ 14` and exponents in
`3…6`, allowing unbounded `C` recovered as a perfect power.
-/
theorem beal_no_coprime_perfect_power_of_le_fourteen_six
    {A B C x y z : ℕ}
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (hAmax : A ≤ 14) (hBmax : B ≤ 14)
    (hx : 3 ≤ x) (hy : 3 ≤ y) (hz : 3 ≤ z)
    (hxE : x ≤ 6) (hyE : y ≤ 6) (hzE : z ≤ 6)
    (hsol : A ^ x + B ^ y = C ^ z)
    (hgcd : Nat.gcd A (Nat.gcd B C) = 1) : False :=
  noCoprimeBealPerfectPowerUpTo_sound
    (by native_decide : noCoprimeBealPerfectPowerUpTo 14 6 = true)
    hA hB hC hAmax hBmax hx hy hz hxE hyE hzE hsol hgcd

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

/-- Perfect-power witness: `3³ + 6³` is a 5th power (non-coprime). -/
theorem beal_known_noncoprime_is_perfect_power :
    isNthPower (3 ^ 3 + 6 ^ 3) 5 = true := by
  native_decide

end Theorems

end DstDiophantine
