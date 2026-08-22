import DstDiophantine.Theorems.BealGaussian
import DstDiophantine.Theorems.Mihailescu
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Phase 7k / 7l: equal-odd two-factor cube slice (`e = 3`)

Infrastructure and closed branches for `BealEqualOddTwoFactorResidual` at
exponent 3:

* Gaussian cube expansion `(a+bi)³`;
* mod-8 obstruction when the factor `2` sits on an odd coordinate;
* Mihăilescu when the pure-cube coordinate has absolute value `1`;
* reduction of the `|u| ≥ 1` body to the positive equation `α³ + 2β³ = γ³`;
* mod-7 / mod-9 diagnostic slices for that equation;
* split assembly `e = 3` vs `e ≥ 5`.

The positive cube equation `α³ + 2β³ = γ³` is the live residual for `e = 3`
(no new axiom; classical Beal is **not** claimed unconditionally).
-/

namespace DstDiophantine

namespace Theorems

open GaussianInt
open Zsqrtd (re_mul im_mul)

local notation "ℤ[i]" => GaussianInt

/-! ### Cube expansion -/

/-- `(a + bi)³ = (a³ − 3ab²) + (3a²b − b³)i`. -/
theorem gaussian_cube_eq (a b : ℤ) :
    (⟨a, b⟩ : ℤ[i]) ^ 3 = ⟨a ^ 3 - 3 * a * b ^ 2, 3 * a ^ 2 * b - b ^ 3⟩ := by
  ext <;> simp [pow_three, re_mul, im_mul] <;> ring

/-! ### Mod-8 obstruction -/

/--
Cubes modulo 8 are `0, 1,` or `7`. Hence `2 * (odd)` cannot be a cube
(for any `v`, including `0`: then `m = 0` is even).
-/
theorem not_two_mul_odd_eq_cube {m v : ℕ} (hm : Odd m) :
    ¬ 2 * m = v ^ 3 := by
  intro heq
  have hvod : Even v :=
    (Nat.even_pow.mp (by rw [← heq]; exact even_two_mul _)).1
  obtain ⟨k, hk⟩ := even_iff_exists_two_mul.mp hvod
  have hv8 : (v ^ 3) % 8 = 0 := by
    rw [hk, show (2 * k) ^ 3 = 8 * k ^ 3 by ring]
    exact Nat.mul_mod_right _ _
  have hLHS : (2 * m) % 8 = 2 ∨ (2 * m) % 8 = 6 := by
    have : m % 2 = 1 := Nat.odd_iff.mp hm
    have hm8 : m % 8 = 1 ∨ m % 8 = 3 ∨ m % 8 = 5 ∨ m % 8 = 7 := by omega
    rcases hm8 with h | h | h | h <;> simp [Nat.mul_mod, h]
  omega

theorem not_two_mul_odd_natAbs_eq_cube {m : ℤ} {v : ℕ}
    (hm : Odd m) : ¬ 2 * m.natAbs = v ^ 3 :=
  not_two_mul_odd_eq_cube (Int.natAbs_odd.mpr hm)

/--
For `e = 3`, the two-factor form must place `2 * ·.natAbs = cube` on the
**even** coordinate (otherwise mod 8 forbids it).
-/
theorem eq_odd_two_factor_cube_even_slot
    {m n : ℤ} {u v : ℕ}
    (hpar : (Even m ∧ Odd n) ∨ (Odd m ∧ Even n))
    (hform :
      (n.natAbs = u ^ 3 ∧ 2 * m.natAbs = v ^ 3) ∨
        (m.natAbs = u ^ 3 ∧ 2 * n.natAbs = v ^ 3)) :
    (Even m ∧ Odd n ∧ n.natAbs = u ^ 3 ∧ 2 * m.natAbs = v ^ 3) ∨
      (Odd m ∧ Even n ∧ m.natAbs = u ^ 3 ∧ 2 * n.natAbs = v ^ 3) := by
  rcases hpar with ⟨hme, hno⟩ | ⟨hmo, hne⟩ <;> rcases hform with ⟨hn, hm⟩ | ⟨hm, hn⟩
  · exact Or.inl ⟨hme, hno, hn, hm⟩
  · exact False.elim (not_two_mul_odd_natAbs_eq_cube hno hn)
  · exact False.elim (not_two_mul_odd_natAbs_eq_cube hmo hm)
  · exact Or.inr ⟨hmo, hne, hm, hn⟩

/-! ### Mihăilescu slice: pure-cube coordinate of absolute value 1 -/

/-- `c³ − t² = 1` with positive integers is impossible (Mihăilescu). -/
theorem not_nat_cube_sub_sq_eq_one {c t : ℕ}
    (hc : 0 < c) (ht : 0 < t) : ¬ c ^ 3 = t ^ 2 + 1 := by
  intro heq
  obtain ⟨_, hx2, _, _⟩ := mihailescu c t 3 2 (by decide) (by decide) hc ht heq
  exact absurd hx2 (by decide : (3 : ℕ) ≠ 2)

/--
If `m² + n² = c³` (natural `c`) and `|n| = 1` with `m ≠ 0`, contradiction via
Mihăilescu.
-/
theorem not_sum_sq_eq_cube_of_natAbs_one {m n : ℤ} {c : ℕ}
    (hm0 : m ≠ 0) (hn1 : n.natAbs = 1)
    (heq : m ^ 2 + n ^ 2 = (c : ℤ) ^ 3) : False := by
  have hn2 : n ^ 2 = 1 := by
    have : (n.natAbs : ℤ) = 1 := by exact_mod_cast hn1
    rw [← Int.natAbs_sq n, this]; norm_num
  have hc0 : 0 < c := by
    by_contra h
    have : c = 0 := Nat.eq_zero_of_not_pos h
    subst this
    have : m ^ 2 + n ^ 2 = 0 := by simpa using heq
    exact hm0 (by nlinarith [sq_nonneg m, sq_nonneg n, this])
  have hform : c ^ 3 = m.natAbs ^ 2 + 1 := by
    have : (c : ℤ) ^ 3 = (m.natAbs : ℤ) ^ 2 + 1 := by
      calc (c : ℤ) ^ 3
          = m ^ 2 + n ^ 2 := heq.symm
        _ = (m.natAbs : ℤ) ^ 2 + 1 := by rw [← Int.natAbs_sq m, hn2]
    exact_mod_cast this
  exact not_nat_cube_sub_sq_eq_one hc0 (Int.natAbs_pos.mpr hm0) hform

theorem not_sum_sq_eq_cube_of_natAbs_one_left {m n : ℤ} {c : ℕ}
    (hn0 : n ≠ 0) (hm1 : m.natAbs = 1)
    (heq : m ^ 2 + n ^ 2 = (c : ℤ) ^ 3) : False :=
  not_sum_sq_eq_cube_of_natAbs_one hn0 hm1 (by rw [add_comm]; exact heq)

/--
Phase 7k cube slice: two-factor data at `e = 3` with pure-cube absolute value
`1` contradicts a sum-of-squares cube identity (Mihăilescu).
-/
theorem not_eq_odd_two_factor_of_exp_three_abs_one
    {m n : ℤ} {c : ℕ}
    (hm0 : m ≠ 0) (hn0 : n ≠ 0)
    (heq : m ^ 2 + n ^ 2 = (c : ℤ) ^ 3)
    (hform :
      (∃ v : ℕ, n.natAbs = 1 ∧ 2 * m.natAbs = v ^ 3) ∨
        (∃ v : ℕ, m.natAbs = 1 ∧ 2 * n.natAbs = v ^ 3)) :
    False := by
  rcases hform with ⟨_, hn1, _⟩ | ⟨_, hm1, _⟩
  · exact not_sum_sq_eq_cube_of_natAbs_one hm0 hn1 heq
  · exact not_sum_sq_eq_cube_of_natAbs_one_left hn0 hm1 heq

/--
From `IsGaussianHypotenusePower m n 3` recover `m² + n² = (|Norm g|)³`.
-/
theorem sum_sq_eq_natAbs_norm_cube_of_gaussian_hyp
    {m n : ℤ} (hIs : IsGaussianHypotenusePower m n 3) :
    ∃ c : ℕ, m ^ 2 + n ^ 2 = (c : ℤ) ^ 3 := by
  obtain ⟨g, hn⟩ := hIs
  refine ⟨(Zsqrtd.norm g).natAbs, ?_⟩
  have hnn : 0 ≤ Zsqrtd.norm g := GaussianInt.norm_nonneg g
  have hpow : Zsqrtd.norm (g ^ 3) = (Zsqrtd.norm g) ^ 3 := by
    calc Zsqrtd.norm (g ^ 3)
        = Zsqrtd.norm (g * g * g) := by ring_nf
      _ = Zsqrtd.norm g * Zsqrtd.norm g * Zsqrtd.norm g := by
          rw [Zsqrtd.norm_mul, Zsqrtd.norm_mul]
      _ = (Zsqrtd.norm g) ^ 3 := by ring
  calc m ^ 2 + n ^ 2
      = Zsqrtd.norm (g ^ 3) := by simpa [Zsqrtd.norm, sq] using hn.symm
    _ = (Zsqrtd.norm g) ^ 3 := hpow
    _ = ((Zsqrtd.norm g).natAbs : ℤ) ^ 3 := by rw [Int.natAbs_of_nonneg hnn]

/--
Phase 7k: Gaussian hypotenuse cube + two-factor form with pure-cube `|·|=1`
is impossible (both coordinates nonzero).
-/
theorem not_eq_odd_two_factor_of_exp_three
    {m n : ℤ}
    (hm0 : m ≠ 0) (hn0 : n ≠ 0)
    (hIs : IsGaussianHypotenusePower m n 3)
    (hform :
      (∃ v : ℕ, n.natAbs = 1 ∧ 2 * m.natAbs = v ^ 3) ∨
        (∃ v : ℕ, m.natAbs = 1 ∧ 2 * n.natAbs = v ^ 3)) :
    False := by
  obtain ⟨c, heq⟩ := sum_sq_eq_natAbs_norm_cube_of_gaussian_hyp hIs
  exact not_eq_odd_two_factor_of_exp_three_abs_one hm0 hn0 heq hform

/-! ### Reduction of two-factor data to `α³ + 2β³ = γ³` -/

theorem even_of_two_mul_eq_cube {m v : ℕ} (heq : 2 * m = v ^ 3) : Even v :=
  (Nat.even_pow.mp (by rw [← heq]; exact even_two_mul _)).1

theorem exists_t_of_two_mul_eq_cube {m v : ℕ} (heq : 2 * m = v ^ 3) :
    ∃ t : ℕ, v = 2 * t ∧ m = 4 * t ^ 3 := by
  obtain ⟨t, ht⟩ := even_iff_exists_two_mul.mp (even_of_two_mul_eq_cube heq)
  refine ⟨t, ht, ?_⟩
  have h8 : 2 * m = 8 * t ^ 3 := by
    calc 2 * m = (2 * t) ^ 3 := by rw [← ht, heq]
      _ = 8 * t ^ 3 := by ring
  omega

/--
Two-factor cube data plus `m² + n² = c³` yields a positive solution of
`α³ + 2β³ = γ³` (`α = u²`, `β = 2 t²`).
-/
theorem exists_pos_cube_add_two_cube_of_two_factor
    {m n : ℤ} {u v c : ℕ}
    (hu0 : 0 < u) (hv0 : 0 < v) (hc0 : 0 < c)
    (hn : n.natAbs = u ^ 3)
    (hm : 2 * m.natAbs = v ^ 3)
    (heq : m ^ 2 + n ^ 2 = (c : ℤ) ^ 3) :
    ∃ α β γ : ℕ, 0 < α ∧ 0 < β ∧ 0 < γ ∧ α ^ 3 + 2 * β ^ 3 = γ ^ 3 := by
  obtain ⟨t, hv2, hm4⟩ := exists_t_of_two_mul_eq_cube hm
  have ht0 : 0 < t := by
    by_contra h
    have : t = 0 := Nat.eq_zero_of_not_pos h
    subst this
    simp [hv2] at hv0
  have hNat : (4 * t ^ 3) ^ 2 + (u ^ 3) ^ 2 = c ^ 3 := by
    -- Work in ℤ: (↑m.natAbs)² + (↑n.natAbs)² = ↑c³
    have heqZ : (m.natAbs : ℤ) ^ 2 + (n.natAbs : ℤ) ^ 2 = (c : ℤ) ^ 3 := by
      calc (m.natAbs : ℤ) ^ 2 + (n.natAbs : ℤ) ^ 2
          = m ^ 2 + n ^ 2 := by rw [Int.natAbs_sq, Int.natAbs_sq]
        _ = (c : ℤ) ^ 3 := heq
    have hmZ : (m.natAbs : ℤ) = (4 * t ^ 3 : ℕ) := by exact_mod_cast hm4
    have hnZ : (n.natAbs : ℤ) = (u ^ 3 : ℕ) := by exact_mod_cast hn
    have : ((4 * t ^ 3 : ℕ) : ℤ) ^ 2 + ((u ^ 3 : ℕ) : ℤ) ^ 2 = (c : ℤ) ^ 3 := by
      rwa [← hmZ, ← hnZ]
    exact_mod_cast this
  refine ⟨u ^ 2, 2 * t ^ 2, c, pow_pos hu0 2,
    Nat.mul_pos (by decide : 0 < 2) (pow_pos ht0 2), hc0, ?_⟩
  calc (u ^ 2) ^ 3 + 2 * (2 * t ^ 2) ^ 3
      = u ^ 6 + 16 * t ^ 6 := by ring
    _ = (4 * t ^ 3) ^ 2 + (u ^ 3) ^ 2 := by ring
    _ = c ^ 3 := hNat

theorem exists_pos_cube_add_two_cube_of_two_factor_symm
    {m n : ℤ} {u v c : ℕ}
    (hu0 : 0 < u) (hv0 : 0 < v) (hc0 : 0 < c)
    (hm : m.natAbs = u ^ 3)
    (hn : 2 * n.natAbs = v ^ 3)
    (heq : m ^ 2 + n ^ 2 = (c : ℤ) ^ 3) :
    ∃ α β γ : ℕ, 0 < α ∧ 0 < β ∧ 0 < γ ∧ α ^ 3 + 2 * β ^ 3 = γ ^ 3 :=
  exists_pos_cube_add_two_cube_of_two_factor hu0 hv0 hc0 hm hn (by rw [add_comm]; exact heq)

/-! ### Residual: no positive solutions of `α³ + 2β³ = γ³` -/

/--
**Residual** (phase 7l, unproved): no positive integers satisfy
`α³ + 2β³ = γ³`. (Signed solutions exist, e.g. `(-1)³ + 2·1³ = 1³`; the Beal
two-factor reduction only produces positive `α = u²`.)
-/
def BealPosCubeAddTwoCubeResidual : Prop :=
  ∀ (α β γ : ℕ), 0 < α → 0 < β → 0 < γ → ¬ α ^ 3 + 2 * β ^ 3 = γ ^ 3

/-! ### Mod-7 / mod-9 diagnostic slices -/

theorem nat_cube_mod_seven (v : ℕ) :
    v ^ 3 % 7 = 0 ∨ v ^ 3 % 7 = 1 ∨ v ^ 3 % 7 = 6 := by
  have h : v % 7 = 0 ∨ v % 7 = 1 ∨ v % 7 = 2 ∨ v % 7 = 3 ∨
      v % 7 = 4 ∨ v % 7 = 5 ∨ v % 7 = 6 := by omega
  have hv : v ^ 3 % 7 = (v % 7) ^ 3 % 7 := by rw [← Nat.pow_mod]
  rcases h with h | h | h | h | h | h | h <;> simp [hv, h]

theorem nat_cube_mod_nine (v : ℕ) :
    v ^ 3 % 9 = 0 ∨ v ^ 3 % 9 = 1 ∨ v ^ 3 % 9 = 8 := by
  have h : v % 9 = 0 ∨ v % 9 = 1 ∨ v % 9 = 2 ∨ v % 9 = 3 ∨ v % 9 = 4 ∨
      v % 9 = 5 ∨ v % 9 = 6 ∨ v % 9 = 7 ∨ v % 9 = 8 := by omega
  have hv : v ^ 3 % 9 = (v % 9) ^ 3 % 9 := by rw [← Nat.pow_mod]
  rcases h with h | h | h | h | h | h | h | h | h <;> simp [hv, h]

theorem not_pos_cube_add_two_cube_mod_seven_of_alpha0_beta1
    {α β γ : ℕ} (hα : α ^ 3 % 7 = 0) (hβ : β ^ 3 % 7 = 1)
    (heq : α ^ 3 + 2 * β ^ 3 = γ ^ 3) : False := by
  have hLHS : (α ^ 3 + 2 * β ^ 3) % 7 = 2 := by
    have h2 : (2 * β ^ 3) % 7 = 2 := by
      calc (2 * β ^ 3) % 7 = (2 % 7 * (β ^ 3 % 7)) % 7 := Nat.mul_mod _ _ _
        _ = (2 * 1) % 7 := by rw [hβ]
        _ = 2 := by decide
    calc (α ^ 3 + 2 * β ^ 3) % 7
        = (α ^ 3 % 7 + (2 * β ^ 3) % 7) % 7 := Nat.add_mod _ _ _
      _ = (0 + 2) % 7 := by rw [hα, h2]
      _ = 2 := by decide
  have hγ := nat_cube_mod_seven γ
  have : γ ^ 3 % 7 = 2 := by rw [← heq]; exact hLHS
  omega

theorem not_pos_cube_add_two_cube_mod_seven_of_alpha0_beta6
    {α β γ : ℕ} (hα : α ^ 3 % 7 = 0) (hβ : β ^ 3 % 7 = 6)
    (heq : α ^ 3 + 2 * β ^ 3 = γ ^ 3) : False := by
  have hLHS : (α ^ 3 + 2 * β ^ 3) % 7 = 5 := by
    have h2 : (2 * β ^ 3) % 7 = 5 := by
      calc (2 * β ^ 3) % 7 = (2 % 7 * (β ^ 3 % 7)) % 7 := Nat.mul_mod _ _ _
        _ = (2 * 6) % 7 := by rw [hβ]
        _ = 5 := by decide
    calc (α ^ 3 + 2 * β ^ 3) % 7
        = (α ^ 3 % 7 + (2 * β ^ 3) % 7) % 7 := Nat.add_mod _ _ _
      _ = (0 + 5) % 7 := by rw [hα, h2]
      _ = 5 := by decide
  have hγ := nat_cube_mod_seven γ
  have : γ ^ 3 % 7 = 5 := by rw [← heq]; exact hLHS
  omega

theorem not_pos_cube_add_two_cube_mod_nine_of_alpha1_beta1
    {α β γ : ℕ} (hα : α ^ 3 % 9 = 1) (hβ : β ^ 3 % 9 = 1)
    (heq : α ^ 3 + 2 * β ^ 3 = γ ^ 3) : False := by
  have hLHS : (α ^ 3 + 2 * β ^ 3) % 9 = 3 := by
    have h2 : (2 * β ^ 3) % 9 = 2 := by
      calc (2 * β ^ 3) % 9 = (2 % 9 * (β ^ 3 % 9)) % 9 := Nat.mul_mod _ _ _
        _ = (2 * 1) % 9 := by rw [hβ]
        _ = 2 := by decide
    calc (α ^ 3 + 2 * β ^ 3) % 9
        = (α ^ 3 % 9 + (2 * β ^ 3) % 9) % 9 := Nat.add_mod _ _ _
      _ = (1 + 2) % 9 := by rw [hα, h2]
      _ = 3 := by decide
  have hγ := nat_cube_mod_nine γ
  have : γ ^ 3 % 9 = 3 := by rw [← heq]; exact hLHS
  omega

theorem not_pos_cube_add_two_cube_mod_nine_of_alpha8_beta8
    {α β γ : ℕ} (hα : α ^ 3 % 9 = 8) (hβ : β ^ 3 % 9 = 8)
    (heq : α ^ 3 + 2 * β ^ 3 = γ ^ 3) : False := by
  have hLHS : (α ^ 3 + 2 * β ^ 3) % 9 = 6 := by
    have h2 : (2 * β ^ 3) % 9 = 7 := by
      calc (2 * β ^ 3) % 9 = (2 % 9 * (β ^ 3 % 9)) % 9 := Nat.mul_mod _ _ _
        _ = (2 * 8) % 9 := by rw [hβ]
        _ = 7 := by decide
    calc (α ^ 3 + 2 * β ^ 3) % 9
        = (α ^ 3 % 9 + (2 * β ^ 3) % 9) % 9 := Nat.add_mod _ _ _
      _ = (8 + 7) % 9 := by rw [hα, h2]
      _ = 6 := by decide
  have hγ := nat_cube_mod_nine γ
  have : γ ^ 3 % 9 = 6 := by rw [← heq]; exact hLHS
  omega

/-! ### Bridge from residual to two-factor `e = 3` -/

theorem not_eq_odd_two_factor_of_exp_three_of_pos_cube
    (hRes : BealPosCubeAddTwoCubeResidual)
    {m n : ℤ} {u v c : ℕ}
    (hu0 : 0 < u) (hv0 : 0 < v) (hc0 : 0 < c)
    (heq : m ^ 2 + n ^ 2 = (c : ℤ) ^ 3)
    (hform :
      (n.natAbs = u ^ 3 ∧ 2 * m.natAbs = v ^ 3) ∨
        (m.natAbs = u ^ 3 ∧ 2 * n.natAbs = v ^ 3)) :
    False := by
  rcases hform with ⟨hn, hm⟩ | ⟨hm, hn⟩
  · obtain ⟨α, β, γ, hα, hβ, hγ, he⟩ :=
      exists_pos_cube_add_two_cube_of_two_factor hu0 hv0 hc0 hn hm heq
    exact hRes α β γ hα hβ hγ he
  · obtain ⟨α, β, γ, hα, hβ, hγ, he⟩ :=
      exists_pos_cube_add_two_cube_of_two_factor_symm hu0 hv0 hc0 hm hn heq
    exact hRes α β γ hα hβ hγ he

theorem isGaussianHypotenusePower_of_associated_pow
    {m n : ℤ} {e : ℕ} {g : ℤ[i]}
    (h : Associated (g ^ e) (⟨m, n⟩ : ℤ[i])) :
    IsGaussianHypotenusePower m n e := by
  refine ⟨g, ?_⟩
  have hn := Zsqrtd.norm_eq_of_associated (by simp : (-1 : ℤ) ≤ 0) h
  -- hn : norm (g^e) = norm ⟨m,n⟩
  simpa [Zsqrtd.norm, sq, gaussian_norm_mk] using hn

theorem not_eq_odd_two_factor_exp_three_full_of_pos_cube
    (hRes : BealPosCubeAddTwoCubeResidual)
    {m n : ℤ} {u v : ℕ}
    (hm0 : m ≠ 0) (_hn0 : n ≠ 0)
    (hu0 : 0 < u) (hv0 : 0 < v)
    (hIs : IsGaussianHypotenusePower m n 3)
    (hform :
      (n.natAbs = u ^ 3 ∧ 2 * m.natAbs = v ^ 3) ∨
        (m.natAbs = u ^ 3 ∧ 2 * n.natAbs = v ^ 3)) :
    False := by
  obtain ⟨c, heq⟩ := sum_sq_eq_natAbs_norm_cube_of_gaussian_hyp hIs
  have hc0 : 0 < c := by
    by_contra h
    have : c = 0 := Nat.eq_zero_of_not_pos h
    subst this
    have : m ^ 2 + n ^ 2 = 0 := by simpa using heq
    exact hm0 (by nlinarith [sq_nonneg m, sq_nonneg n, this])
  exact not_eq_odd_two_factor_of_exp_three_of_pos_cube hRes hu0 hv0 hc0 heq hform

theorem not_eq_odd_two_factor_exp_three_of_pos_cube_associated
    (hRes : BealPosCubeAddTwoCubeResidual)
    {m n : ℤ} {u v : ℕ}
    (hu0 : 0 < u) (hv0 : 0 < v)
    (hAssoc : ∃ g : ℤ[i], Associated (g ^ 3) (⟨m, n⟩ : ℤ[i]))
    (hform :
      (n.natAbs = u ^ 3 ∧ 2 * m.natAbs = v ^ 3) ∨
        (m.natAbs = u ^ 3 ∧ 2 * n.natAbs = v ^ 3)) :
    False := by
  obtain ⟨g, hg⟩ := hAssoc
  have hIs := isGaussianHypotenusePower_of_associated_pow hg
  have hm0 : m ≠ 0 := by
    intro hm; subst hm
    rcases hform with ⟨_, hm2⟩ | ⟨hm3, _⟩
    · have : v ^ 3 = 0 := by simpa using hm2.symm
      exact Nat.pos_iff_ne_zero.mp hv0 (Nat.pow_eq_zero.mp this).1
    · have : u ^ 3 = 0 := by simpa using hm3.symm
      exact Nat.pos_iff_ne_zero.mp hu0 (Nat.pow_eq_zero.mp this).1
  have hn0 : n ≠ 0 := by
    intro hn; subst hn
    rcases hform with ⟨hn3, _⟩ | ⟨_, hn2⟩
    · have : u ^ 3 = 0 := by simpa using hn3.symm
      exact Nat.pos_iff_ne_zero.mp hu0 (Nat.pow_eq_zero.mp this).1
    · have : v ^ 3 = 0 := by simpa using hn2.symm
      exact Nat.pos_iff_ne_zero.mp hv0 (Nat.pow_eq_zero.mp this).1
  exact not_eq_odd_two_factor_exp_three_full_of_pos_cube hRes hm0 hn0 hu0 hv0 hIs hform

/-! ### Split `e = 3` / `e ≥ 5` -/

/--
**Residual** (phase 7l): equal-odd two-factor body for odd exponents `e ≥ 5`.
-/
def BealEqualOddTwoFactorExpGeFiveResidual : Prop :=
  ∀ (m n : ℤ) (e : ℕ),
    5 ≤ e → Odd e →
    Int.gcd m n = 1 →
    ((Even m ∧ Odd n) ∨ (Odd m ∧ Even n)) →
    (∃ g : ℤ[i], Associated (g ^ e) (⟨m, n⟩ : ℤ[i])) →
    ((∃ u v : ℕ, 0 < u ∧ 0 < v ∧ n.natAbs = u ^ e ∧ 2 * m.natAbs = v ^ e) ∨
      (∃ u v : ℕ, 0 < u ∧ 0 < v ∧ m.natAbs = u ^ e ∧ 2 * n.natAbs = v ^ e)) →
    False

/--
Phase 7l assembly: positive-cube residual + `e ≥ 5` residual imply the full
`BealEqualOddTwoFactorResidual`.
-/
theorem BealEqualOddTwoFactorResidual_of_pos_cube_and_ge_five
    (hCube : BealPosCubeAddTwoCubeResidual)
    (hGe5 : BealEqualOddTwoFactorExpGeFiveResidual) :
    BealEqualOddTwoFactorResidual := by
  intro m n e he hodd hcop hpar hAssoc hform
  have he_cases : e = 3 ∨ 5 ≤ e := by
    have : e = 3 ∨ 4 ≤ e := by omega
    rcases this with h | h
    · exact Or.inl h
    · have : e ≠ 4 := fun h4 => by
        subst h4
        exact Nat.not_odd_iff_even.mpr (by decide : Even 4) hodd
      omega
  rcases he_cases with he3 | he5
  · subst he3
    rcases hform with ⟨u, v, hu0, hv0, hn, hm⟩ | ⟨u, v, hu0, hv0, hm, hn⟩
    · exact not_eq_odd_two_factor_exp_three_of_pos_cube_associated hCube hu0 hv0
        hAssoc (Or.inl ⟨hn, hm⟩)
    · exact not_eq_odd_two_factor_exp_three_of_pos_cube_associated hCube hu0 hv0
        hAssoc (Or.inr ⟨hm, hn⟩)
  · exact hGe5 m n e he5 hodd hcop hpar hAssoc hform

end Theorems

end DstDiophantine
