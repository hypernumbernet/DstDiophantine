import DstDiophantine.Theorems.BealFinite

set_option linter.style.nativeDecide false

/-!
# Phase 7n–7q: residual-shaped Beal finite search

Finite certificates aimed at residual shapes where a classical Beal
counterexample could still hide. This module is diagnostic / computational;
it does **not** close residual bodies (`BealPosCubeAddTwoCubeResidual`, etc.).

* **Positive cube kernel** `α³ + 2β³ = γ³`: current certificate bases `≤ 120`
  (weaker named bounds follow by monotonicity).
* **Open-residual filter** on classical coprime `A^x+B^y=C^z` (skips closed
  slices `d ≥ 3`, two exponents divisible by 4, Darmon–Merel cube positions,
  and signature-`(n,n,5)` with common exponent `≥ 4`):
  current certificate bases `≤ 60`, exponents `3…6`.

Classical Beal is **not** claimed unconditionally.
-/

namespace DstDiophantine

namespace Theorems

/-! ### Positive cube kernel `α³ + 2β³ = γ³` -/

/--
True when `α³ + 2β³` is a positive perfect cube `γ³` with
`gcd(α,β,γ) = 1` and `α` odd (primitive positive slice; both-even is 2-adically
reducible, even-α/odd-β is impossible).
-/
def isPosCubeAddTwoPrimitive (α β : ℕ) : Bool :=
  decide (0 < α ∧ 0 < β ∧ α % 2 = 1) &&
    match findNthRoot (α ^ 3 + 2 * β ^ 3) 3 with
    | some γ => decide (Nat.gcd α (Nat.gcd β γ) = 1 ∧ γ % 2 = 1)
    | none => false

/-- Existence of a primitive positive cube hit with `α,β ≤ N`. -/
def hasPosCubeAddTwoPrimitiveUpTo (N : ℕ) : Bool :=
  (List.range' 1 N).any fun α =>
    (List.range' 1 N).any fun β =>
      isPosCubeAddTwoPrimitive α β

def noPosCubeAddTwoPrimitiveUpTo (N : ℕ) : Bool :=
  !(hasPosCubeAddTwoPrimitiveUpTo N)

/-- First primitive positive cube hit with `α,β ≤ N`, if any. -/
def findPosCubeAddTwoPrimitiveUpTo (N : ℕ) : Option (ℕ × ℕ × ℕ) :=
  (List.range' 1 N).findSome? fun α =>
    (List.range' 1 N).findSome? fun β =>
      if isPosCubeAddTwoPrimitive α β then
        (findNthRoot (α ^ 3 + 2 * β ^ 3) 3).map fun γ => (α, β, γ)
      else none

theorem isPosCubeAddTwoPrimitive_sound {α β : ℕ}
    (h : isPosCubeAddTwoPrimitive α β = true) :
    ∃ γ : ℕ,
      0 < α ∧ 0 < β ∧ 0 < γ ∧
        α % 2 = 1 ∧ γ % 2 = 1 ∧
          Nat.gcd α (Nat.gcd β γ) = 1 ∧
            α ^ 3 + 2 * β ^ 3 = γ ^ 3 := by
  simp only [isPosCubeAddTwoPrimitive, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hα, hβ, hαodd⟩, hroot⟩ := h
  match hγ : findNthRoot (α ^ 3 + 2 * β ^ 3) 3 with
  | none => simp [hγ] at hroot
  | some γ =>
    simp only [hγ, decide_eq_true_eq] at hroot
    obtain ⟨hγpos, heq⟩ := findNthRoot_sound hγ
    exact ⟨γ, hα, hβ, hγpos, hαodd, hroot.2, hroot.1, heq.symm⟩

theorem findPosCubeAddTwoPrimitiveUpTo_sound {N α β γ : ℕ}
    (h : findPosCubeAddTwoPrimitiveUpTo N = some (α, β, γ)) :
    isPosCubeAddTwoPrimitive α β = true ∧
      findNthRoot (α ^ 3 + 2 * β ^ 3) 3 = some γ := by
  obtain ⟨_, α', _, _, h1, _⟩ := (List.findSome?_eq_some_iff).1 h
  obtain ⟨_, β', _, _, hf, _⟩ := (List.findSome?_eq_some_iff).1 h1
  by_cases htrue : isPosCubeAddTwoPrimitive α' β' = true
  · simp only [htrue, ↓reduceIte, Option.map_eq_some_iff] at hf
    obtain ⟨γ', hγ, hEq⟩ := hf
    obtain ⟨rfl, rfl, rfl⟩ := hEq
    exact ⟨htrue, hγ⟩
  · simp [htrue] at hf

theorem noPosCubeAddTwoPrimitiveUpTo_sound {N : ℕ}
    (h : noPosCubeAddTwoPrimitiveUpTo N = true)
    {α β γ : ℕ}
    (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ)
    (hαN : α ≤ N) (hβN : β ≤ N)
    (hαodd : α % 2 = 1) (hγodd : γ % 2 = 1)
    (hgcd : Nat.gcd α (Nat.gcd β γ) = 1)
    (heq : α ^ 3 + 2 * β ^ 3 = γ ^ 3) : False := by
  have hfind : findNthRoot (α ^ 3 + 2 * β ^ 3) 3 = some γ :=
    findNthRoot_eq_some_of (by decide : 0 < 3) hγ heq.symm
  have hpp : isPosCubeAddTwoPrimitive α β = true := by
    simp [isPosCubeAddTwoPrimitive, hα, hβ, hαodd, hfind, hgcd, hγodd]
  have hany : hasPosCubeAddTwoPrimitiveUpTo N = true := by
    refine (List.any_eq_true).mpr ⟨α, mem_beal_bases hα hαN, ?_⟩
    refine (List.any_eq_true).mpr ⟨β, mem_beal_bases hβ hβN, ?_⟩
    exact hpp
  have : hasPosCubeAddTwoPrimitiveUpTo N = false := by
    simpa [noPosCubeAddTwoPrimitiveUpTo, Bool.not_eq_true'] using h
  exact absurd hany (by simp [this])

/--
Phase 7s: no primitive positive solution of `α³ + 2β³ = γ³` with
`α,β ≤ 120` (odd `α`, three-way gcd 1). Finite slice only.
-/
theorem no_pos_cube_add_two_primitive_of_le_hundredtwenty
    {α β γ : ℕ}
    (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ)
    (hαN : α ≤ 120) (hβN : β ≤ 120)
    (hαodd : α % 2 = 1) (hγodd : γ % 2 = 1)
    (hgcd : Nat.gcd α (Nat.gcd β γ) = 1)
    (heq : α ^ 3 + 2 * β ^ 3 = γ ^ 3) : False :=
  noPosCubeAddTwoPrimitiveUpTo_sound
    (by native_decide : noPosCubeAddTwoPrimitiveUpTo 120 = true)
    hα hβ hγ hαN hβN hαodd hγodd hgcd heq

/-- Phase 7r certificate; follows from ≤ 120. -/
theorem no_pos_cube_add_two_primitive_of_le_hundred
    {α β γ : ℕ}
    (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ)
    (hαN : α ≤ 100) (hβN : β ≤ 100)
    (hαodd : α % 2 = 1) (hγodd : γ % 2 = 1)
    (hgcd : Nat.gcd α (Nat.gcd β γ) = 1)
    (heq : α ^ 3 + 2 * β ^ 3 = γ ^ 3) : False :=
  no_pos_cube_add_two_primitive_of_le_hundredtwenty
    hα hβ hγ (by omega) (by omega) hαodd hγodd hgcd heq

/-- Phase 7q certificate; follows from ≤ 120. -/
theorem no_pos_cube_add_two_primitive_of_le_eighty
    {α β γ : ℕ}
    (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ)
    (hαN : α ≤ 80) (hβN : β ≤ 80)
    (hαodd : α % 2 = 1) (hγodd : γ % 2 = 1)
    (hgcd : Nat.gcd α (Nat.gcd β γ) = 1)
    (heq : α ^ 3 + 2 * β ^ 3 = γ ^ 3) : False :=
  no_pos_cube_add_two_primitive_of_le_hundredtwenty
    hα hβ hγ (by omega) (by omega) hαodd hγodd hgcd heq

/-- Weaker cube-kernel certificates (phases 7n–7p); follow from ≤ 120. -/
theorem no_pos_cube_add_two_primitive_of_le_forty
    {α β γ : ℕ}
    (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ)
    (hαN : α ≤ 40) (hβN : β ≤ 40)
    (hαodd : α % 2 = 1) (hγodd : γ % 2 = 1)
    (hgcd : Nat.gcd α (Nat.gcd β γ) = 1)
    (heq : α ^ 3 + 2 * β ^ 3 = γ ^ 3) : False :=
  no_pos_cube_add_two_primitive_of_le_hundredtwenty
    hα hβ hγ (by omega) (by omega) hαodd hγodd hgcd heq

theorem no_pos_cube_add_two_primitive_of_le_fifty
    {α β γ : ℕ}
    (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ)
    (hαN : α ≤ 50) (hβN : β ≤ 50)
    (hαodd : α % 2 = 1) (hγodd : γ % 2 = 1)
    (hgcd : Nat.gcd α (Nat.gcd β γ) = 1)
    (heq : α ^ 3 + 2 * β ^ 3 = γ ^ 3) : False :=
  no_pos_cube_add_two_primitive_of_le_hundredtwenty
    hα hβ hγ (by omega) (by omega) hαodd hγodd hgcd heq

theorem no_pos_cube_add_two_primitive_of_le_sixty
    {α β γ : ℕ}
    (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ)
    (hαN : α ≤ 60) (hβN : β ≤ 60)
    (hαodd : α % 2 = 1) (hγodd : γ % 2 = 1)
    (hgcd : Nat.gcd α (Nat.gcd β γ) = 1)
    (heq : α ^ 3 + 2 * β ^ 3 = γ ^ 3) : False :=
  no_pos_cube_add_two_primitive_of_le_hundredtwenty
    hα hβ hγ (by omega) (by omega) hαodd hγodd hgcd heq

/-! ### Open-residual filter on classical Beal -/

/--
Exponents that still sit in an **open** residual after skipping closed slices:

* `d = gcd(x,y,z) ∈ {1,2}` (skip `d ≥ 3` / FLT),
* not two of `{x,y,z}` divisible by 4 when `d = 2`,
* not a Darmon–Merel cube position `(n,n,3)` / `(3,n,n)` / `(n,3,n)`,
* not a signature-`(n,n,5)` position with common exponent `≥ 4`:
  `(n,n,5)` / `(5,n,n)` / `(n,5,n)` (phase 7s; `(3,3,5)` stays open).
-/
def isOpenResidualExponents (x y z : ℕ) : Bool :=
  let d := Nat.gcd x (Nat.gcd y z)
  decide
    (3 ≤ x ∧ 3 ≤ y ∧ 3 ≤ z ∧
      (d = 1 ∨ d = 2) ∧
      ¬(d = 2 ∧ ((4 ∣ x ∧ 4 ∣ y) ∨ (4 ∣ y ∧ 4 ∣ z) ∨ (4 ∣ x ∧ 4 ∣ z))) ∧
      ¬((x = y ∧ z = 3) ∨ (y = z ∧ x = 3) ∨ (x = z ∧ y = 3)) ∧
      ¬((x = y ∧ z = 5 ∧ 4 ≤ x) ∨ (y = z ∧ x = 5 ∧ 4 ≤ y) ∨
          (x = z ∧ y = 5 ∧ 4 ≤ x)))

/-- Coprime perfect-power Beal hit whose exponents pass the open-residual filter. -/
def isOpenResidualBealPerfectPower (A B x y z : ℕ) : Bool :=
  isOpenResidualExponents x y z && isCoprimeBealPerfectPower A B x y z

def hasOpenResidualBealPerfectPowerUpTo (Amax Emax : ℕ) : Bool :=
  (List.range' 1 Amax).any fun A =>
    (List.range' 1 Amax).any fun B =>
      (List.range' 3 (Emax + 1 - 3)).any fun x =>
        (List.range' 3 (Emax + 1 - 3)).any fun y =>
          (List.range' 3 (Emax + 1 - 3)).any fun z =>
            isOpenResidualBealPerfectPower A B x y z

def noOpenResidualBealPerfectPowerUpTo (Amax Emax : ℕ) : Bool :=
  !(hasOpenResidualBealPerfectPowerUpTo Amax Emax)

/-- First open-residual coprime perfect-power hit, if any. -/
def findOpenResidualBealPerfectPowerUpTo (Amax Emax : ℕ) :
    Option (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) :=
  (List.range' 1 Amax).findSome? fun A =>
    (List.range' 1 Amax).findSome? fun B =>
      (List.range' 3 (Emax + 1 - 3)).findSome? fun x =>
        (List.range' 3 (Emax + 1 - 3)).findSome? fun y =>
          (List.range' 3 (Emax + 1 - 3)).findSome? fun z =>
            if isOpenResidualBealPerfectPower A B x y z then
              (findNthRoot (A ^ x + B ^ y) z).map fun C => (A, B, C, x, y, z)
            else none

theorem isOpenResidualBealPerfectPower_sound {A B x y z : ℕ}
    (h : isOpenResidualBealPerfectPower A B x y z = true) :
    isOpenResidualExponents x y z = true ∧
      ∃ C : ℕ,
        3 ≤ x ∧ 3 ≤ y ∧ 3 ≤ z ∧
          0 < A ∧ 0 < B ∧ 0 < C ∧
            A ^ x + B ^ y = C ^ z ∧
              Nat.gcd A (Nat.gcd B C) = 1 := by
  simp only [isOpenResidualBealPerfectPower, Bool.and_eq_true] at h
  exact ⟨h.1, isCoprimeBealPerfectPower_sound h.2⟩

theorem noOpenResidualBealPerfectPowerUpTo_sound {Amax Emax : ℕ}
    (h : noOpenResidualBealPerfectPowerUpTo Amax Emax = true)
    {A B C x y z : ℕ}
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (hAmax : A ≤ Amax) (hBmax : B ≤ Amax)
    (hx : 3 ≤ x) (hy : 3 ≤ y) (hz : 3 ≤ z)
    (hxE : x ≤ Emax) (hyE : y ≤ Emax) (hzE : z ≤ Emax)
    (hopen : isOpenResidualExponents x y z = true)
    (hsol : A ^ x + B ^ y = C ^ z)
    (hgcd : Nat.gcd A (Nat.gcd B C) = 1) : False := by
  have hz0 : 0 < z := Nat.lt_of_lt_of_le (by decide : 0 < 3) hz
  have hfind : findNthRoot (A ^ x + B ^ y) z = some C :=
    findNthRoot_eq_some_of hz0 hC hsol.symm
  have hpp : isOpenResidualBealPerfectPower A B x y z = true := by
    simp [isOpenResidualBealPerfectPower, hopen, isCoprimeBealPerfectPower,
      hx, hy, hz, hA, hB, hfind, hgcd]
  have hany : hasOpenResidualBealPerfectPowerUpTo Amax Emax = true := by
    refine (List.any_eq_true).mpr ⟨A, mem_beal_bases hA hAmax, ?_⟩
    refine (List.any_eq_true).mpr ⟨B, mem_beal_bases hB hBmax, ?_⟩
    refine (List.any_eq_true).mpr ⟨x, mem_beal_exps hx hxE, ?_⟩
    refine (List.any_eq_true).mpr ⟨y, mem_beal_exps hy hyE, ?_⟩
    refine (List.any_eq_true).mpr ⟨z, mem_beal_exps hz hzE, ?_⟩
    exact hpp
  have : hasOpenResidualBealPerfectPowerUpTo Amax Emax = false := by
    simpa [noOpenResidualBealPerfectPowerUpTo, Bool.not_eq_true'] using h
  exact absurd hany (by simp [this])

/--
Phase 7s: no open-residual coprime perfect-power Beal solution with bases
`≤ 60` and exponents in `3…6` (`C` unbounded).
-/
theorem beal_no_open_residual_perfect_power_of_le_sixty_six
    {A B C x y z : ℕ}
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (hAmax : A ≤ 60) (hBmax : B ≤ 60)
    (hx : 3 ≤ x) (hy : 3 ≤ y) (hz : 3 ≤ z)
    (hxE : x ≤ 6) (hyE : y ≤ 6) (hzE : z ≤ 6)
    (hopen : isOpenResidualExponents x y z = true)
    (hsol : A ^ x + B ^ y = C ^ z)
    (hgcd : Nat.gcd A (Nat.gcd B C) = 1) : False :=
  noOpenResidualBealPerfectPowerUpTo_sound
    (by native_decide : noOpenResidualBealPerfectPowerUpTo 60 6 = true)
    hA hB hC hAmax hBmax hx hy hz hxE hyE hzE hopen hsol hgcd

/-- Phase 7r certificate; follows from ≤ 60. -/
theorem beal_no_open_residual_perfect_power_of_le_fifty_six
    {A B C x y z : ℕ}
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (hAmax : A ≤ 50) (hBmax : B ≤ 50)
    (hx : 3 ≤ x) (hy : 3 ≤ y) (hz : 3 ≤ z)
    (hxE : x ≤ 6) (hyE : y ≤ 6) (hzE : z ≤ 6)
    (hopen : isOpenResidualExponents x y z = true)
    (hsol : A ^ x + B ^ y = C ^ z)
    (hgcd : Nat.gcd A (Nat.gcd B C) = 1) : False :=
  beal_no_open_residual_perfect_power_of_le_sixty_six
    hA hB hC (by omega) (by omega) hx hy hz hxE hyE hzE hopen hsol hgcd

/-- Phase 7q certificate; follows from ≤ 60. -/
theorem beal_no_open_residual_perfect_power_of_le_forty_six
    {A B C x y z : ℕ}
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (hAmax : A ≤ 40) (hBmax : B ≤ 40)
    (hx : 3 ≤ x) (hy : 3 ≤ y) (hz : 3 ≤ z)
    (hxE : x ≤ 6) (hyE : y ≤ 6) (hzE : z ≤ 6)
    (hopen : isOpenResidualExponents x y z = true)
    (hsol : A ^ x + B ^ y = C ^ z)
    (hgcd : Nat.gcd A (Nat.gcd B C) = 1) : False :=
  beal_no_open_residual_perfect_power_of_le_sixty_six
    hA hB hC (by omega) (by omega) hx hy hz hxE hyE hzE hopen hsol hgcd

/-- Weaker open-residual certificates (phases 7n–7p); follow from ≤ 60. -/
theorem beal_no_open_residual_perfect_power_of_le_twenty_six
    {A B C x y z : ℕ}
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (hAmax : A ≤ 20) (hBmax : B ≤ 20)
    (hx : 3 ≤ x) (hy : 3 ≤ y) (hz : 3 ≤ z)
    (hxE : x ≤ 6) (hyE : y ≤ 6) (hzE : z ≤ 6)
    (hopen : isOpenResidualExponents x y z = true)
    (hsol : A ^ x + B ^ y = C ^ z)
    (hgcd : Nat.gcd A (Nat.gcd B C) = 1) : False :=
  beal_no_open_residual_perfect_power_of_le_sixty_six
    hA hB hC (by omega) (by omega) hx hy hz hxE hyE hzE hopen hsol hgcd

theorem beal_no_open_residual_perfect_power_of_le_twentyfive_six
    {A B C x y z : ℕ}
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (hAmax : A ≤ 25) (hBmax : B ≤ 25)
    (hx : 3 ≤ x) (hy : 3 ≤ y) (hz : 3 ≤ z)
    (hxE : x ≤ 6) (hyE : y ≤ 6) (hzE : z ≤ 6)
    (hopen : isOpenResidualExponents x y z = true)
    (hsol : A ^ x + B ^ y = C ^ z)
    (hgcd : Nat.gcd A (Nat.gcd B C) = 1) : False :=
  beal_no_open_residual_perfect_power_of_le_sixty_six
    hA hB hC (by omega) (by omega) hx hy hz hxE hyE hzE hopen hsol hgcd

theorem beal_no_open_residual_perfect_power_of_le_thirty_six
    {A B C x y z : ℕ}
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (hAmax : A ≤ 30) (hBmax : B ≤ 30)
    (hx : 3 ≤ x) (hy : 3 ≤ y) (hz : 3 ≤ z)
    (hxE : x ≤ 6) (hyE : y ≤ 6) (hzE : z ≤ 6)
    (hopen : isOpenResidualExponents x y z = true)
    (hsol : A ^ x + B ^ y = C ^ z)
    (hgcd : Nat.gcd A (Nat.gcd B C) = 1) : False :=
  beal_no_open_residual_perfect_power_of_le_sixty_six
    hA hB hC (by omega) (by omega) hx hy hz hxE hyE hzE hopen hsol hgcd

end Theorems

end DstDiophantine
