import DstDiophantine.Theorems.BealFinite

set_option linter.style.nativeDecide false

/-!
# Residual-shaped Beal finite search

Finite certificates aimed at residual shapes where a classical Beal
counterexample could still hide. This module is diagnostic / computational;
it does **not** close residual bodies (`BealPosCubeAddTwoCubeResidual`, etc.).

* **Positive cube kernel** `α³ + 2β³ = γ³`: closed under the Euler axiom
  (`BealPosCubeAddTwoCubeResidual_of_euler`); the finite certificate bases
  `≤ 400` remain as a complementary diagnostic.
* **Open-residual filter** on classical coprime `A^x+B^y=C^z` (skips closed
  slices `d ≥ 3`, two exponents divisible by 4, Darmon–Merel cube positions,
  and signature-`(n,n,5)` with common exponent `≥ 4`):
  current certificate bases `≤ 80`, exponents `3…7`.

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
Phase 7t: no primitive positive solution of `α³ + 2β³ = γ³` with
`α,β ≤ 400` (odd `α`, three-way gcd 1). Finite slice only.
-/
theorem no_pos_cube_add_two_primitive_of_le_fourhundred
    {α β γ : ℕ}
    (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ)
    (hαN : α ≤ 400) (hβN : β ≤ 400)
    (hαodd : α % 2 = 1) (hγodd : γ % 2 = 1)
    (hgcd : Nat.gcd α (Nat.gcd β γ) = 1)
    (heq : α ^ 3 + 2 * β ^ 3 = γ ^ 3) : False :=
  noPosCubeAddTwoPrimitiveUpTo_sound
    (by native_decide : noPosCubeAddTwoPrimitiveUpTo 400 = true)
    hα hβ hγ hαN hβN hαodd hγodd hgcd heq

/-- Phase 7s certificate; follows from ≤ 400. -/
theorem no_pos_cube_add_two_primitive_of_le_hundredtwenty
    {α β γ : ℕ}
    (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ)
    (hαN : α ≤ 120) (hβN : β ≤ 120)
    (hαodd : α % 2 = 1) (hγodd : γ % 2 = 1)
    (hgcd : Nat.gcd α (Nat.gcd β γ) = 1)
    (heq : α ^ 3 + 2 * β ^ 3 = γ ^ 3) : False :=
  no_pos_cube_add_two_primitive_of_le_fourhundred
    hα hβ hγ (by omega) (by omega) hαodd hγodd hgcd heq

/-- Phase 7r certificate; follows from ≤ 400. -/
theorem no_pos_cube_add_two_primitive_of_le_hundred
    {α β γ : ℕ}
    (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ)
    (hαN : α ≤ 100) (hβN : β ≤ 100)
    (hαodd : α % 2 = 1) (hγodd : γ % 2 = 1)
    (hgcd : Nat.gcd α (Nat.gcd β γ) = 1)
    (heq : α ^ 3 + 2 * β ^ 3 = γ ^ 3) : False :=
  no_pos_cube_add_two_primitive_of_le_hundredtwenty
    hα hβ hγ (by omega) (by omega) hαodd hγodd hgcd heq

/-- Phase 7q certificate; follows from ≤ 400. -/
theorem no_pos_cube_add_two_primitive_of_le_eighty
    {α β γ : ℕ}
    (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ)
    (hαN : α ≤ 80) (hβN : β ≤ 80)
    (hαodd : α % 2 = 1) (hγodd : γ % 2 = 1)
    (hgcd : Nat.gcd α (Nat.gcd β γ) = 1)
    (heq : α ^ 3 + 2 * β ^ 3 = γ ^ 3) : False :=
  no_pos_cube_add_two_primitive_of_le_hundredtwenty
    hα hβ hγ (by omega) (by omega) hαodd hγodd hgcd heq

/-- Weaker cube-kernel certificates (phases 7n–7p); follow from ≤ 400. -/
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
Beal-range exponent triples whose *shape* is closed by a named slice:

* `d ≥ 3` (FLT axiom);
* `d = 2` with at least two of `{x,y,z}` divisible by 4;
* Darmon–Merel cube positions, matching `not_beal_two_equal_cube_slice`
  (the even permutations `(3,n,n)` / `(n,3,n)` with even `n` stay live);
* signature `(n,n,5)` positions, matching `not_beal_two_equal_fifth_slice`
  (even permutations likewise stay live; `(3,3,5)` stays open).

This is strictly coarser than the residual atlas: Mihăilescu's `|u| = 1`
slice is a coefficient condition, not an exponent shape.
-/
def IsClosedShapeExponents (x y z : ℕ) : Prop :=
  3 ≤ x ∧ 3 ≤ y ∧ 3 ≤ z ∧
    (3 ≤ bealExpGcd x y z ∨
      (bealExpGcd x y z = 2 ∧
        ((4 ∣ x ∧ 4 ∣ y) ∨ (4 ∣ y ∧ 4 ∣ z) ∨ (4 ∣ x ∧ 4 ∣ z))) ∨
      (bealExpGcd x y z = 1 ∧
        ((x = y ∧ z = 3) ∨ (y = z ∧ x = 3 ∧ y % 2 = 1) ∨
          (x = z ∧ y = 3 ∧ x % 2 = 1))) ∨
      (bealExpGcd x y z = 1 ∧
        ((x = y ∧ z = 5 ∧ 4 ≤ x) ∨
          (y = z ∧ x = 5 ∧ y % 2 = 1 ∧ 4 ≤ y) ∨
          (x = z ∧ y = 5 ∧ x % 2 = 1 ∧ 4 ≤ x))))

instance {x y z : ℕ} : Decidable (IsClosedShapeExponents x y z) := by
  unfold IsClosedShapeExponents
  infer_instance

/--
Exponents that still sit in an **open** residual after skipping closed
*shapes* (`IsClosedShapeExponents`). Even permutations of the cube and
`(n,n,5)` signatures are kept open: they belong to the even two-equal
difference residual, because an even common exponent does not rewrite to
Darmon–Merel or `(n,n,5)` form.
-/
def isOpenResidualExponents (x y z : ℕ) : Bool :=
  let d := bealExpGcd x y z
  decide
    (3 ≤ x ∧ 3 ≤ y ∧ 3 ≤ z ∧
      (d = 1 ∨ d = 2) ∧
      ¬(d = 2 ∧ ((4 ∣ x ∧ 4 ∣ y) ∨ (4 ∣ y ∧ 4 ∣ z) ∨ (4 ∣ x ∧ 4 ∣ z))) ∧
      ¬(d = 1 ∧ ((x = y ∧ z = 3) ∨ (y = z ∧ x = 3 ∧ y % 2 = 1) ∨
          (x = z ∧ y = 3 ∧ x % 2 = 1))) ∧
      ¬(d = 1 ∧ ((x = y ∧ z = 5 ∧ 4 ≤ x) ∨
          (y = z ∧ x = 5 ∧ y % 2 = 1 ∧ 4 ≤ y) ∨
          (x = z ∧ y = 5 ∧ x % 2 = 1 ∧ 4 ≤ x))))

theorem isOpenResidualExponents_iff {x y z : ℕ} :
    isOpenResidualExponents x y z = true ↔
      3 ≤ x ∧ 3 ≤ y ∧ 3 ≤ z ∧ ¬ IsClosedShapeExponents x y z := by
  unfold isOpenResidualExponents
  simp only [decide_eq_true_eq]
  constructor
  · intro ⟨hx, hy, hz, hd, hfourth, hDM, hNN5⟩
    refine ⟨hx, hy, hz, ?_⟩
    intro hcl
    obtain ⟨_, _, _, hdisj⟩ := hcl
    rcases hdisj with hge | h2 | hdm | hnn
    · rcases hd with hd | hd <;> omega
    · exact hfourth h2
    · exact hDM hdm
    · exact hNN5 hnn
  · intro ⟨hx, hy, hz, hnot⟩
    refine ⟨hx, hy, hz, ?_, ?_, ?_, ?_⟩
    · have htri := bealExpGcd_eq_one_or_eq_two_or_ge_three (y := y) (z := z) hx
      have hnge : ¬ 3 ≤ bealExpGcd x y z := fun hd =>
        hnot ⟨hx, hy, hz, Or.inl hd⟩
      rcases htri with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact (hnge h).elim
    · exact fun hf => hnot ⟨hx, hy, hz, Or.inr (Or.inl hf)⟩
    · exact fun hDM => hnot ⟨hx, hy, hz, Or.inr (Or.inr (Or.inl hDM))⟩
    · exact fun hNN5 => hnot ⟨hx, hy, hz, Or.inr (Or.inr (Or.inr hNN5))⟩

theorem isOpenResidualExponents_eq_false_of_closed {x y z : ℕ}
    (h : IsClosedShapeExponents x y z) :
    isOpenResidualExponents x y z = false := by
  rw [Bool.eq_false_iff]
  intro htrue
  exact (isOpenResidualExponents_iff.mp htrue).2.2.2 h

theorem isClosedShapeExponents_of_range_not_open {x y z : ℕ}
    (hx : 3 ≤ x) (hy : 3 ≤ y) (hz : 3 ≤ z)
    (hopen : isOpenResidualExponents x y z = false) :
    IsClosedShapeExponents x y z := by
  have hne : isOpenResidualExponents x y z ≠ true := by
    simpa [Bool.not_eq_true] using hopen
  have : ¬ (3 ≤ x ∧ 3 ≤ y ∧ 3 ≤ z ∧ ¬ IsClosedShapeExponents x y z) := by
    simpa [isOpenResidualExponents_iff] using hne
  exact Decidable.not_not.mp fun hnot => this ⟨hx, hy, hz, hnot⟩

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
Phase 7t: no open-residual coprime perfect-power Beal solution with bases
`≤ 80` and exponents in `3…7` (`C` unbounded).
-/
theorem beal_no_open_residual_perfect_power_of_le_eighty_seven
    {A B C x y z : ℕ}
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (hAmax : A ≤ 80) (hBmax : B ≤ 80)
    (hx : 3 ≤ x) (hy : 3 ≤ y) (hz : 3 ≤ z)
    (hxE : x ≤ 7) (hyE : y ≤ 7) (hzE : z ≤ 7)
    (hopen : isOpenResidualExponents x y z = true)
    (hsol : A ^ x + B ^ y = C ^ z)
    (hgcd : Nat.gcd A (Nat.gcd B C) = 1) : False :=
  noOpenResidualBealPerfectPowerUpTo_sound
    (by native_decide : noOpenResidualBealPerfectPowerUpTo 80 7 = true)
    hA hB hC hAmax hBmax hx hy hz hxE hyE hzE hopen hsol hgcd

/-- Phase 7s certificate; follows from ≤ 80 · 7. -/
theorem beal_no_open_residual_perfect_power_of_le_sixty_six
    {A B C x y z : ℕ}
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (hAmax : A ≤ 60) (hBmax : B ≤ 60)
    (hx : 3 ≤ x) (hy : 3 ≤ y) (hz : 3 ≤ z)
    (hxE : x ≤ 6) (hyE : y ≤ 6) (hzE : z ≤ 6)
    (hopen : isOpenResidualExponents x y z = true)
    (hsol : A ^ x + B ^ y = C ^ z)
    (hgcd : Nat.gcd A (Nat.gcd B C) = 1) : False :=
  beal_no_open_residual_perfect_power_of_le_eighty_seven
    hA hB hC (by omega) (by omega) hx hy hz (by omega) (by omega) (by omega)
    hopen hsol hgcd

/-- Phase 7t certificate; follows from ≤ 80 · 7. -/
theorem beal_no_open_residual_perfect_power_of_le_eighty_six
    {A B C x y z : ℕ}
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (hAmax : A ≤ 80) (hBmax : B ≤ 80)
    (hx : 3 ≤ x) (hy : 3 ≤ y) (hz : 3 ≤ z)
    (hxE : x ≤ 6) (hyE : y ≤ 6) (hzE : z ≤ 6)
    (hopen : isOpenResidualExponents x y z = true)
    (hsol : A ^ x + B ^ y = C ^ z)
    (hgcd : Nat.gcd A (Nat.gcd B C) = 1) : False :=
  beal_no_open_residual_perfect_power_of_le_eighty_seven
    hA hB hC hAmax hBmax hx hy hz (by omega) (by omega) (by omega)
    hopen hsol hgcd

/-- Phase 7t certificate; follows from ≤ 80 · 7. -/
theorem beal_no_open_residual_perfect_power_of_le_sixty_seven
    {A B C x y z : ℕ}
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (hAmax : A ≤ 60) (hBmax : B ≤ 60)
    (hx : 3 ≤ x) (hy : 3 ≤ y) (hz : 3 ≤ z)
    (hxE : x ≤ 7) (hyE : y ≤ 7) (hzE : z ≤ 7)
    (hopen : isOpenResidualExponents x y z = true)
    (hsol : A ^ x + B ^ y = C ^ z)
    (hgcd : Nat.gcd A (Nat.gcd B C) = 1) : False :=
  beal_no_open_residual_perfect_power_of_le_eighty_seven
    hA hB hC (by omega) (by omega) hx hy hz hxE hyE hzE
    hopen hsol hgcd

/-- Phase 7r certificate; follows from ≤ 80 · 7. -/
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

/-- Phase 7q certificate; follows from ≤ 80 · 7. -/
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

/-- Weaker open-residual certificates (phases 7n–7p); follow from ≤ 80 · 7. -/
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
