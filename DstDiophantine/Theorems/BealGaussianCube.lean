import DstDiophantine.Theorems.BealGaussian
import DstDiophantine.Theorems.EulerCube
import DstDiophantine.Theorems.Mihailescu
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.MaxPowDiv
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Phase 7k / 7l / 7m: equal-odd two-factor cube slice (`e = 3`)

Infrastructure and closed branches for `BealEqualOddTwoFactorResidual` at
exponent 3:

* Gaussian cube expansion `(a+bi)³`;
* mod-8 obstruction when the factor `2` sits on an odd coordinate;
* Mihăilescu when the pure-cube coordinate has absolute value `1`;
* reduction of the `|u| ≥ 1` body to the positive equation `α³ + 2β³ = γ³`;
* 2-adic/gcd reduction of any positive solution to a primitive odd-`α,γ` slice;
* mod-7 / mod-9 / mod-13 / mod-19 cube-residue tables and allowed classes;
* split assembly `e = 3` vs `e ≥ 5`;
* phase 7m: primitivity / parity / difference-factor / 2-adic packaging for
  `α³ + 2β³ = γ³`, and assembly from the affine residual `X³ + 2Y³ = 1`;
* phase 7q: 3-descent of the difference factors (`gcd ∈ {1,3}`), almost-cube
  assignment, and reduction to `s³ = t⁶ + 3τ²` or `s³ = τ² + (3^{2k-1} t²)³`;
* phase 7o: birational packaging of that Affine curve onto the Mordell model
  `y² = x³ - 1728`, with assembly `BealMordellCubeAddTwoResidual → Affine`;
* phase 7u: Euler axiom `eulerAffineCubeAddTwo` closes the affine residual and
  therefore the positive-cube residual (the `e = 3` leaf).

The live residual for equal-odd two-factor is now the odd-exponent body
`e ≥ 5`. Classical Beal is **not** claimed unconditionally. The Mordell rank
is not in mathlib; phase 7o does **not** close the Weierstrass model by itself.
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

/-! ### Mihăilescu slice: pure-power coordinate of absolute value 1 -/

/-- `c^e − t² = 1` with positive integers and `e ≥ 3` is impossible (Mihăilescu). -/
theorem not_nat_pow_sub_sq_eq_one {c t e : ℕ}
    (hc : 0 < c) (ht : 0 < t) (he : 3 ≤ e) : ¬ c ^ e = t ^ 2 + 1 := by
  intro heq
  have he1 : 1 < e := Nat.lt_of_lt_of_le (by decide : 1 < 3) he
  obtain ⟨_, hx2, _, _⟩ := mihailescu c t e 2 he1 (by decide) hc ht heq
  exact absurd hx2 (by omega : e ≠ 2)

/-- Specialization of `not_nat_pow_sub_sq_eq_one` at `e = 3`. -/
theorem not_nat_cube_sub_sq_eq_one {c t : ℕ}
    (hc : 0 < c) (ht : 0 < t) : ¬ c ^ 3 = t ^ 2 + 1 :=
  not_nat_pow_sub_sq_eq_one hc ht (by decide : 3 ≤ 3)

/--
If `m² + n² = c^e` (natural `c`, `e ≥ 3`) and `|n| = 1` with `m ≠ 0`, contradiction via
Mihăilescu.
-/
theorem not_sum_sq_eq_pow_of_natAbs_one {m n : ℤ} {c e : ℕ}
    (hm0 : m ≠ 0) (hn1 : n.natAbs = 1) (he : 3 ≤ e)
    (heq : m ^ 2 + n ^ 2 = (c : ℤ) ^ e) : False := by
  have hn2 : n ^ 2 = 1 := by
    have : (n.natAbs : ℤ) = 1 := by exact_mod_cast hn1
    rw [← Int.natAbs_sq n, this]; norm_num
  have hc0 : 0 < c := by
    by_contra h
    have : c = 0 := Nat.eq_zero_of_not_pos h
    subst this
    have : m ^ 2 + n ^ 2 = 0 := by
      simpa [zero_pow (Nat.pos_iff_ne_zero.mp (Nat.lt_of_lt_of_le (by decide : 0 < 3) he))]
        using heq
    exact hm0 (by nlinarith [sq_nonneg m, sq_nonneg n, this])
  have hform : c ^ e = m.natAbs ^ 2 + 1 := by
    have : (c : ℤ) ^ e = (m.natAbs : ℤ) ^ 2 + 1 := by
      calc (c : ℤ) ^ e
          = m ^ 2 + n ^ 2 := heq.symm
        _ = (m.natAbs : ℤ) ^ 2 + 1 := by rw [← Int.natAbs_sq m, hn2]
    exact_mod_cast this
  exact not_nat_pow_sub_sq_eq_one hc0 (Int.natAbs_pos.mpr hm0) he hform

theorem not_sum_sq_eq_pow_of_natAbs_one_left {m n : ℤ} {c e : ℕ}
    (hn0 : n ≠ 0) (hm1 : m.natAbs = 1) (he : 3 ≤ e)
    (heq : m ^ 2 + n ^ 2 = (c : ℤ) ^ e) : False :=
  not_sum_sq_eq_pow_of_natAbs_one hn0 hm1 he (by rw [add_comm]; exact heq)

/-- Cube specialization retained for Phase 7k call sites. -/
theorem not_sum_sq_eq_cube_of_natAbs_one {m n : ℤ} {c : ℕ}
    (hm0 : m ≠ 0) (hn1 : n.natAbs = 1)
    (heq : m ^ 2 + n ^ 2 = (c : ℤ) ^ 3) : False :=
  not_sum_sq_eq_pow_of_natAbs_one hm0 hn1 (by decide : 3 ≤ 3) heq

theorem not_sum_sq_eq_cube_of_natAbs_one_left {m n : ℤ} {c : ℕ}
    (hn0 : n ≠ 0) (hm1 : m.natAbs = 1)
    (heq : m ^ 2 + n ^ 2 = (c : ℤ) ^ 3) : False :=
  not_sum_sq_eq_pow_of_natAbs_one_left hn0 hm1 (by decide : 3 ≤ 3) heq

/--
Phase 7m: two-factor data at odd `e ≥ 3` with pure-power absolute value `1`
contradicts a sum-of-squares power identity (Mihăilescu).
-/
theorem not_eq_odd_two_factor_of_exp_ge_three_abs_one
    {m n : ℤ} {c e : ℕ}
    (hm0 : m ≠ 0) (hn0 : n ≠ 0) (he : 3 ≤ e)
    (heq : m ^ 2 + n ^ 2 = (c : ℤ) ^ e)
    (hform :
      (∃ v : ℕ, n.natAbs = 1 ∧ 2 * m.natAbs = v ^ e) ∨
        (∃ v : ℕ, m.natAbs = 1 ∧ 2 * n.natAbs = v ^ e)) :
    False := by
  rcases hform with ⟨_, hn1, _⟩ | ⟨_, hm1, _⟩
  · exact not_sum_sq_eq_pow_of_natAbs_one hm0 hn1 he heq
  · exact not_sum_sq_eq_pow_of_natAbs_one_left hn0 hm1 he heq

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
    False :=
  not_eq_odd_two_factor_of_exp_ge_three_abs_one hm0 hn0 (by decide : 3 ≤ 3) heq hform

/--
From `IsGaussianHypotenusePower m n e` recover `m² + n² = (|Norm g|)^e`.
-/
theorem sum_sq_eq_natAbs_norm_pow_of_gaussian_hyp
    {m n : ℤ} {e : ℕ} (hIs : IsGaussianHypotenusePower m n e) :
    ∃ c : ℕ, m ^ 2 + n ^ 2 = (c : ℤ) ^ e := by
  obtain ⟨g, hn⟩ := hIs
  refine ⟨(Zsqrtd.norm g).natAbs, ?_⟩
  have hnn : 0 ≤ Zsqrtd.norm g := GaussianInt.norm_nonneg g
  have hpow : ∀ k : ℕ, Zsqrtd.norm (g ^ k) = (Zsqrtd.norm g) ^ k := by
    intro k
    induction k with
    | zero => simp [Zsqrtd.norm_one]
    | succ k ih => rw [pow_succ, Zsqrtd.norm_mul, ih, pow_succ]
  calc m ^ 2 + n ^ 2
      = Zsqrtd.norm (g ^ e) := hn.symm
    _ = (Zsqrtd.norm g) ^ e := hpow e
    _ = ((Zsqrtd.norm g).natAbs : ℤ) ^ e := by rw [Int.natAbs_of_nonneg hnn]

/--
From `IsGaussianHypotenusePower m n 3` recover `m² + n² = (|Norm g|)³`.
-/
theorem sum_sq_eq_natAbs_norm_cube_of_gaussian_hyp
    {m n : ℤ} (hIs : IsGaussianHypotenusePower m n 3) :
    ∃ c : ℕ, m ^ 2 + n ^ 2 = (c : ℤ) ^ 3 :=
  sum_sq_eq_natAbs_norm_pow_of_gaussian_hyp hIs

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
**Cube leaf** (phase 7l / 7u): no positive integers satisfy `α³ + 2β³ = γ³`.
Signed solutions exist (e.g. `(-1)³ + 2·1³ = 1³`); the Beal two-factor
reduction only produces positive `α = u²`. Closed under the Euler axiom via
`BealPosCubeAddTwoCubeResidual_of_euler` below.
-/
def BealPosCubeAddTwoCubeResidual : Prop :=
  ∀ (α β γ : ℕ), 0 < α → 0 < β → 0 < γ → ¬ α ^ 3 + 2 * β ^ 3 = γ ^ 3

/-! ### Phase 7m: packaging for `α³ + 2β³ = γ³` -/

/--
If `α` and `β` are both even in a positive solution of `α³ + 2β³ = γ³`, then
`γ` is even and the halved triple is again a positive solution (the only place
a 2-adic descent step applies).
-/
theorem pos_cube_add_two_cube_halve_of_even
    {α β γ : ℕ} (hα0 : 0 < α) (hβ0 : 0 < β) (hγ0 : 0 < γ)
    (hαe : Even α) (hβe : Even β)
    (heq : α ^ 3 + 2 * β ^ 3 = γ ^ 3) :
    ∃ α' β' γ' : ℕ,
      0 < α' ∧ 0 < β' ∧ 0 < γ' ∧
        α = 2 * α' ∧ β = 2 * β' ∧ γ = 2 * γ' ∧
          α' ^ 3 + 2 * β' ^ 3 = γ' ^ 3 := by
  obtain ⟨α', hα⟩ := even_iff_exists_two_mul.mp hαe
  obtain ⟨β', hβ⟩ := even_iff_exists_two_mul.mp hβe
  have hα'0 : 0 < α' := by
    by_contra h; have : α' = 0 := Nat.eq_zero_of_not_pos h
    subst this; simp [hα] at hα0
  have hβ'0 : 0 < β' := by
    by_contra h; have : β' = 0 := Nat.eq_zero_of_not_pos h
    subst this; simp [hβ] at hβ0
  have hγe : Even γ := by
    have : Even (γ ^ 3) := by
      rw [← heq, hα, hβ]
      refine Even.add ?_ ?_
      · exact even_iff_two_dvd.mpr ⟨4 * α' ^ 3, by ring⟩
      · exact even_iff_two_dvd.mpr ⟨8 * β' ^ 3, by ring⟩
    exact (Nat.even_pow.mp this).1
  obtain ⟨γ', hγ⟩ := even_iff_exists_two_mul.mp hγe
  have hγ'0 : 0 < γ' := by
    by_contra h; have : γ' = 0 := Nat.eq_zero_of_not_pos h
    subst this; simp [hγ] at hγ0
  refine ⟨α', β', γ', hα'0, hβ'0, hγ'0, hα, hβ, hγ, ?_⟩
  have : (2 * α') ^ 3 + 2 * (2 * β') ^ 3 = (2 * γ') ^ 3 := by
    simpa [hα, hβ, hγ] using heq
  have h8 : 8 * (α' ^ 3 + 2 * β' ^ 3) = 8 * γ' ^ 3 := by
    calc 8 * (α' ^ 3 + 2 * β' ^ 3)
        = (2 * α') ^ 3 + 2 * (2 * β') ^ 3 := by ring
      _ = (2 * γ') ^ 3 := this
      _ = 8 * γ' ^ 3 := by ring
  exact Nat.mul_left_cancel (by decide : 0 < 8) h8

/-- Cubes are never `2` or `6` modulo 8. -/
theorem not_nat_cube_mod_eight_eq_two_or_six (v : ℕ) :
    v ^ 3 % 8 ≠ 2 ∧ v ^ 3 % 8 ≠ 6 := by
  have h : v % 8 = 0 ∨ v % 8 = 1 ∨ v % 8 = 2 ∨ v % 8 = 3 ∨
      v % 8 = 4 ∨ v % 8 = 5 ∨ v % 8 = 6 ∨ v % 8 = 7 := by omega
  have hv : v ^ 3 % 8 = (v % 8) ^ 3 % 8 := by rw [← Nat.pow_mod]
  rcases h with h | h | h | h | h | h | h | h <;> simp [hv, h]

/-- Even cubes are `0` modulo 8. -/
theorem even_nat_cube_mod_eight_eq_zero {v : ℕ} (hv : Even v) :
    v ^ 3 % 8 = 0 := by
  obtain ⟨k, hk⟩ := even_iff_exists_two_mul.mp hv
  rw [hk, show (2 * k) ^ 3 = 8 * k ^ 3 by ring]
  exact Nat.mul_mod_right _ _

/-- If `α` is odd in a positive solution, then `γ` is odd (parity). -/
theorem odd_gamma_of_odd_alpha_pos_cube
    {α β γ : ℕ} (hαo : Odd α) (heq : α ^ 3 + 2 * β ^ 3 = γ ^ 3) :
    Odd γ := by
  have hα3 : Odd (α ^ 3) := Odd.pow hαo
  have h2 : Even (2 * β ^ 3) := even_two_mul _
  have hsum : Odd (α ^ 3 + 2 * β ^ 3) := hα3.add_even h2
  have : Odd (γ ^ 3) := by simpa [heq] using hsum
  exact Nat.Odd.of_mul_right this

/-- `α` even and `β` odd cannot occur for `α³ + 2β³ = γ³`. -/
theorem not_even_alpha_odd_beta_pos_cube
    {α β γ : ℕ} (hαe : Even α) (hβo : Odd β)
    (heq : α ^ 3 + 2 * β ^ 3 = γ ^ 3) : False := by
  have hα3 : α ^ 3 % 8 = 0 := even_nat_cube_mod_eight_eq_zero hαe
  have hβ3 : β ^ 3 % 8 = 1 ∨ β ^ 3 % 8 = 3 ∨ β ^ 3 % 8 = 5 ∨ β ^ 3 % 8 = 7 := by
    have h : β % 8 = 1 ∨ β % 8 = 3 ∨ β % 8 = 5 ∨ β % 8 = 7 := by
      have : β % 2 = 1 := Nat.odd_iff.mp hβo
      have hb : β % 8 = 0 ∨ β % 8 = 1 ∨ β % 8 = 2 ∨ β % 8 = 3 ∨
          β % 8 = 4 ∨ β % 8 = 5 ∨ β % 8 = 6 ∨ β % 8 = 7 := by omega
      omega
    have hv : β ^ 3 % 8 = (β % 8) ^ 3 % 8 := by rw [← Nat.pow_mod]
    rcases h with h | h | h | h <;> simp [hv, h]
  have h2β : (2 * β ^ 3) % 8 = 2 ∨ (2 * β ^ 3) % 8 = 6 := by
    rcases hβ3 with hb | hb | hb | hb
    · exact Or.inl (by
        calc (2 * β ^ 3) % 8 = (2 % 8 * (β ^ 3 % 8)) % 8 := Nat.mul_mod _ _ _
          _ = 2 := by rw [hb])
    · exact Or.inr (by
        calc (2 * β ^ 3) % 8 = (2 % 8 * (β ^ 3 % 8)) % 8 := Nat.mul_mod _ _ _
          _ = 6 := by rw [hb])
    · exact Or.inl (by
        calc (2 * β ^ 3) % 8 = (2 % 8 * (β ^ 3 % 8)) % 8 := Nat.mul_mod _ _ _
          _ = 2 := by rw [hb])
    · exact Or.inr (by
        calc (2 * β ^ 3) % 8 = (2 % 8 * (β ^ 3 % 8)) % 8 := Nat.mul_mod _ _ _
          _ = 6 := by rw [hb])
  have hLHS : (α ^ 3 + 2 * β ^ 3) % 8 = 2 ∨ (α ^ 3 + 2 * β ^ 3) % 8 = 6 := by
    rcases h2β with h | h
    · exact Or.inl (by
        calc (α ^ 3 + 2 * β ^ 3) % 8
            = (α ^ 3 % 8 + (2 * β ^ 3) % 8) % 8 := Nat.add_mod _ _ _
          _ = 2 := by rw [hα3, h])
    · exact Or.inr (by
        calc (α ^ 3 + 2 * β ^ 3) % 8
            = (α ^ 3 % 8 + (2 * β ^ 3) % 8) % 8 := Nat.add_mod _ _ _
          _ = 6 := by rw [hα3, h])
  have hγ := not_nat_cube_mod_eight_eq_two_or_six γ
  have : γ ^ 3 % 8 = 2 ∨ γ ^ 3 % 8 = 6 := by
    have hγeq : γ ^ 3 % 8 = (α ^ 3 + 2 * β ^ 3) % 8 := by rw [← heq]
    rcases hLHS with h | h
    · exact Or.inl (by rw [hγeq, h])
    · exact Or.inr (by rw [hγeq, h])
  omega

/--
Primitive positive solutions (`gcd(α,β,γ) = 1`) of `α³ + 2β³ = γ³` have
both `α` and `γ` odd.
-/
theorem odd_alpha_gamma_of_pos_cube_primitive
    {α β γ : ℕ} (hα0 : 0 < α) (hβ0 : 0 < β) (hγ0 : 0 < γ)
    (hgcd : Nat.gcd α (Nat.gcd β γ) = 1)
    (heq : α ^ 3 + 2 * β ^ 3 = γ ^ 3) :
    Odd α ∧ Odd γ := by
  by_cases hαe : Even α
  · by_cases hβe : Even β
    · obtain ⟨α', β', γ', _, _, _, hα, hβ, hγ, _⟩ :=
        pos_cube_add_two_cube_halve_of_even hα0 hβ0 hγ0 hαe hβe heq
      have h2 : 2 ∣ Nat.gcd α (Nat.gcd β γ) :=
        Nat.dvd_gcd ⟨α', hα⟩ (Nat.dvd_gcd ⟨β', hβ⟩ ⟨γ', hγ⟩)
      have : 2 ∣ (1 : ℕ) := by rwa [hgcd] at h2
      omega
    · exact False.elim
        (not_even_alpha_odd_beta_pos_cube hαe (Nat.not_even_iff_odd.mp hβe) heq)
  · have hαo : Odd α := Nat.not_even_iff_odd.mp hαe
    exact ⟨hαo, odd_gamma_of_odd_alpha_pos_cube hαo heq⟩

/--
Any positive solution of `α³ + 2β³ = γ³` yields a primitive solution with both
`α` and `γ` odd (divide out `gcd(α,β,γ)`; the surviving triple cannot be even).
-/
theorem exists_primitive_odd_pos_cube_of_pos
    {α β γ : ℕ} (hα0 : 0 < α) (hβ0 : 0 < β) (hγ0 : 0 < γ)
    (heq : α ^ 3 + 2 * β ^ 3 = γ ^ 3) :
    ∃ α' β' γ' : ℕ,
      0 < α' ∧ 0 < β' ∧ 0 < γ' ∧
        Nat.gcd α' (Nat.gcd β' γ') = 1 ∧ Odd α' ∧ Odd γ' ∧
          α' ^ 3 + 2 * β' ^ 3 = γ' ^ 3 := by
  set d := Nat.gcd α (Nat.gcd β γ)
  have hdpos : 0 < d := Nat.gcd_pos_of_pos_left _ hα0
  obtain ⟨α', hα⟩ := (Nat.gcd_dvd_left α (Nat.gcd β γ) : d ∣ α)
  obtain ⟨β', hβ⟩ :=
    ((Nat.gcd_dvd_right α (Nat.gcd β γ)).trans (Nat.gcd_dvd_left β γ) : d ∣ β)
  obtain ⟨γ', hγ⟩ :=
    ((Nat.gcd_dvd_right α (Nat.gcd β γ)).trans (Nat.gcd_dvd_right β γ) : d ∣ γ)
  have hα'0 : 0 < α' := Nat.pos_of_mul_pos_left (hα ▸ hα0)
  have hβ'0 : 0 < β' := Nat.pos_of_mul_pos_left (hβ ▸ hβ0)
  have hγ'0 : 0 < γ' := Nat.pos_of_mul_pos_left (hγ ▸ hγ0)
  have heq' : α' ^ 3 + 2 * β' ^ 3 = γ' ^ 3 := by
    have hmul : d ^ 3 * (α' ^ 3 + 2 * β' ^ 3) = d ^ 3 * γ' ^ 3 := by
      calc d ^ 3 * (α' ^ 3 + 2 * β' ^ 3)
          = (d * α') ^ 3 + 2 * (d * β') ^ 3 := by ring
        _ = α ^ 3 + 2 * β ^ 3 := by rw [← hα, ← hβ]
        _ = γ ^ 3 := heq
        _ = (d * γ') ^ 3 := by rw [hγ]
        _ = d ^ 3 * γ' ^ 3 := by ring
    exact Nat.mul_left_cancel (pow_pos hdpos 3) hmul
  have hg : Nat.gcd α' (Nat.gcd β' γ') = 1 := by
    have hmul :
        d * Nat.gcd α' (Nat.gcd β' γ') =
          Nat.gcd (d * α') (Nat.gcd (d * β') (d * γ')) := by
      rw [Nat.gcd_mul_left, Nat.gcd_mul_left]
    have : d * Nat.gcd α' (Nat.gcd β' γ') = d := by
      rw [hmul, ← hα, ← hβ, ← hγ]
    have : d * Nat.gcd α' (Nat.gcd β' γ') = d * 1 := by
      simpa [mul_one] using this
    exact Nat.mul_left_cancel hdpos this
  have hodd := odd_alpha_gamma_of_pos_cube_primitive hα'0 hβ'0 hγ'0 hg heq'
  exact ⟨α', β', γ', hα'0, hβ'0, hγ'0, hg, hodd.1, hodd.2, heq'⟩

/--
The positive-cube residual is equivalent to the absence of primitive solutions
with both `α` and `γ` odd.
-/
theorem BealPosCubeAddTwoCubeResidual_iff_no_primitive_odd :
    BealPosCubeAddTwoCubeResidual ↔
      ∀ (α β γ : ℕ), 0 < α → 0 < β → 0 < γ →
        Nat.gcd α (Nat.gcd β γ) = 1 → Odd α → Odd γ →
          ¬ α ^ 3 + 2 * β ^ 3 = γ ^ 3 := by
  constructor
  · intro h α β γ hα hβ hγ _ _ _ heq
    exact h α β γ hα hβ hγ heq
  · intro h α β γ hα hβ hγ heq
    obtain ⟨α', β', γ', hα', hβ', hγ', hg, hoα, hoγ, heq'⟩ :=
      exists_primitive_odd_pos_cube_of_pos hα hβ hγ heq
    exact h α' β' γ' hα' hβ' hγ' hg hoα hoγ heq'

/-- Positive solutions satisfy `α < γ`. -/
theorem alpha_lt_gamma_of_pos_cube
    {α β γ : ℕ} (hβ0 : 0 < β) (heq : α ^ 3 + 2 * β ^ 3 = γ ^ 3) :
    α < γ := by
  have hlt : α ^ 3 < γ ^ 3 := by
    have : 0 < 2 * β ^ 3 := Nat.mul_pos (by decide : 0 < 2) (pow_pos hβ0 3)
    have : α ^ 3 < α ^ 3 + 2 * β ^ 3 := Nat.lt_add_of_pos_right this
    rwa [heq] at this
  exact lt_of_pow_lt_pow_left₀ 3 (Nat.zero_le _) hlt

/-- Convenience: `γ³ − α³ = 2β³`. -/
theorem gamma_cube_sub_alpha_cube_eq_two_beta
    {α β γ : ℕ} (hβ0 : 0 < β) (heq : α ^ 3 + 2 * β ^ 3 = γ ^ 3) :
    γ ^ 3 - α ^ 3 = 2 * β ^ 3 := by
  have hle : α ≤ γ := Nat.le_of_lt (alpha_lt_gamma_of_pos_cube hβ0 heq)
  have : α ^ 3 ≤ γ ^ 3 := Nat.pow_le_pow_left hle 3
  omega

/-- Difference-of-cubes identity on `ℕ` when `α ≤ γ`. -/
theorem cube_sub_eq_mul_of_le {γ α : ℕ} (hle : α ≤ γ) :
    γ ^ 3 - α ^ 3 = (γ - α) * (γ ^ 2 + γ * α + α ^ 2) := by
  have hγ3 : α ^ 3 ≤ γ ^ 3 := Nat.pow_le_pow_left hle 3
  apply Int.ofNat_inj.mp
  have hγa : ((γ - α : ℕ) : ℤ) = (γ : ℤ) - α := Nat.cast_sub hle
  calc ((γ ^ 3 - α ^ 3 : ℕ) : ℤ)
      = (γ : ℤ) ^ 3 - (α : ℤ) ^ 3 := by
          rw [Nat.cast_sub hγ3]; simp
    _ = ((γ : ℤ) - α) * ((γ : ℤ) ^ 2 + γ * α + α ^ 2) := by ring
    _ = ((γ - α : ℕ) : ℤ) * ((γ ^ 2 + γ * α + α ^ 2 : ℕ) : ℤ) := by
          rw [hγa]; push_cast; ring
    _ = ((γ - α) * (γ ^ 2 + γ * α + α ^ 2) : ℕ) := by simp

/-- Quadratic factor of a difference of cubes, as a polynomial identity on `ℕ`. -/
theorem quad_factor_eq_of_le {γ α : ℕ} (hle : α ≤ γ) :
    γ ^ 2 + γ * α + α ^ 2 = (γ - α) * (γ + 2 * α) + 3 * α ^ 2 := by
  apply Int.ofNat_inj.mp
  have hγa : ((γ - α : ℕ) : ℤ) = (γ : ℤ) - α := Nat.cast_sub hle
  calc ((γ ^ 2 + γ * α + α ^ 2 : ℕ) : ℤ)
      = (γ : ℤ) ^ 2 + γ * α + α ^ 2 := by push_cast; ring
    _ = ((γ : ℤ) - α) * ((γ : ℤ) + 2 * α) + 3 * α ^ 2 := by ring
    _ = (((γ - α : ℕ) : ℤ) * ((γ + 2 * α : ℕ) : ℤ) + (3 * α ^ 2 : ℕ)) := by
          rw [hγa]; push_cast; ring
    _ = ((γ - α) * (γ + 2 * α) + 3 * α ^ 2 : ℕ) := by simp

/-- Under `Nat.Coprime α γ` and `α ≤ γ`, the difference-factor gcd divides 3. -/
theorem gcd_cube_diff_factors_dvd_three_of_coprime
    {γ α : ℕ} (hle : α ≤ γ) (hcop : Nat.Coprime α γ) :
    Nat.gcd (γ - α) (γ ^ 2 + γ * α + α ^ 2) ∣ 3 := by
  have hga : Nat.Coprime (γ - α) α := by
    refine (Nat.coprime_iff_gcd_eq_one.2 ?_).symm
    -- gcd α (γ - α) = gcd α γ = 1
    have : Nat.gcd α (γ - α) = Nat.gcd α γ := by
      have h := Nat.gcd_add_self_right α (γ - α)
      -- h : gcd α ((γ - α) + α) = gcd α (γ - α)
      rw [Nat.add_comm] at h
      rw [← h, Nat.add_sub_of_le hle]
    rwa [this, ← Nat.coprime_iff_gcd_eq_one]
  have hrew : Nat.gcd (γ - α) (γ ^ 2 + γ * α + α ^ 2) =
      Nat.gcd (γ - α) (3 * α ^ 2) := by
    rw [quad_factor_eq_of_le hle, Nat.gcd_mul_left_add_right]
  rw [hrew]
  have hga2 : Nat.Coprime (γ - α) (α ^ 2) := hga.pow_right 2
  rw [hga2.symm.gcd_mul_right_cancel_right 3]
  exact Nat.gcd_dvd_right _ _

/-- Primitive solutions are pairwise coprime in `(α, γ)`. -/
theorem coprime_alpha_gamma_of_pos_cube_primitive
    {α β γ : ℕ} (hα0 : 0 < α) (hβ0 : 0 < β) (hγ0 : 0 < γ)
    (hgcd : Nat.gcd α (Nat.gcd β γ) = 1)
    (heq : α ^ 3 + 2 * β ^ 3 = γ ^ 3) :
    Nat.Coprime α γ := by
  refine Nat.coprime_iff_gcd_eq_one.2 ?_
  set d := Nat.gcd α γ
  have hdα : d ∣ α := Nat.gcd_dvd_left _ _
  have hdγ : d ∣ γ := Nat.gcd_dvd_right _ _
  have hα3 : d ^ 3 ∣ α ^ 3 := pow_dvd_pow_of_dvd hdα 3
  have hγ3 : d ^ 3 ∣ γ ^ 3 := pow_dvd_pow_of_dvd hdγ 3
  have hsub := gamma_cube_sub_alpha_cube_eq_two_beta hβ0 heq
  have h2β : d ^ 3 ∣ 2 * β ^ 3 := by
    have : d ^ 3 ∣ γ ^ 3 - α ^ 3 := Nat.dvd_sub hγ3 hα3
    rwa [hsub] at this
  have hodd := odd_alpha_gamma_of_pos_cube_primitive hα0 hβ0 hγ0 hgcd heq
  have hd_ne_two : ¬ 2 ∣ d := by
    intro h2
    exact Nat.not_odd_iff_even.mpr
      (even_iff_two_dvd.mpr (dvd_trans h2 hdα)) hodd.1
  have hcop2 : Nat.Coprime d 2 :=
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hd_ne_two).symm
  have hcop2pow : Nat.Coprime (d ^ 3) 2 := hcop2.pow_left 3
  have hdβ3 : d ^ 3 ∣ β ^ 3 :=
    Nat.Coprime.dvd_of_dvd_mul_left hcop2pow (by simpa [mul_comm] using h2β)
  have hdβ : d ∣ β := (Nat.pow_dvd_pow_iff (by decide : (3 : ℕ) ≠ 0)).mp hdβ3
  have : d ∣ Nat.gcd α (Nat.gcd β γ) :=
    Nat.dvd_gcd hdα (Nat.dvd_gcd hdβ hdγ)
  have : d ∣ 1 := by simpa [hgcd] using this
  exact Nat.eq_one_of_dvd_one this

/-- Factorisation package for a positive primitive solution. -/
theorem pos_cube_diff_factor_package
    {α β γ : ℕ} (hα0 : 0 < α) (hβ0 : 0 < β) (hγ0 : 0 < γ)
    (hgcd : Nat.gcd α (Nat.gcd β γ) = 1)
    (heq : α ^ 3 + 2 * β ^ 3 = γ ^ 3) :
    α < γ ∧
      Odd α ∧ Odd γ ∧
        Nat.Coprime α γ ∧
          γ ^ 3 - α ^ 3 = 2 * β ^ 3 ∧
            (γ - α) * (γ ^ 2 + γ * α + α ^ 2) = 2 * β ^ 3 ∧
              Nat.gcd (γ - α) (γ ^ 2 + γ * α + α ^ 2) ∣ 3 := by
  have hlt := alpha_lt_gamma_of_pos_cube hβ0 heq
  have hle := Nat.le_of_lt hlt
  have hodd := odd_alpha_gamma_of_pos_cube_primitive hα0 hβ0 hγ0 hgcd heq
  have hcop := coprime_alpha_gamma_of_pos_cube_primitive hα0 hβ0 hγ0 hgcd heq
  have hsub := gamma_cube_sub_alpha_cube_eq_two_beta hβ0 heq
  have hfac := cube_sub_eq_mul_of_le hle
  exact ⟨hlt, hodd.1, hodd.2, hcop, hsub, by rw [← hfac]; exact hsub,
    gcd_cube_diff_factors_dvd_three_of_coprime hle hcop⟩

/--
For a positive solution with both `α` and `γ` odd, the second difference factor
is odd, so `padicValNat 2 (γ - α) = 1 + 3 * padicValNat 2 β`.
-/
theorem padicValNat_two_gamma_sub_alpha_of_odd
    {α β γ : ℕ} (hβ0 : 0 < β) (hαo : Odd α) (hγo : Odd γ)
    (heq : α ^ 3 + 2 * β ^ 3 = γ ^ 3) :
    padicValNat 2 (γ - α) = 1 + 3 * padicValNat 2 β := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle : α ≤ γ := Nat.le_of_lt (alpha_lt_gamma_of_pos_cube hβ0 heq)
  have hfac : (γ - α) * (γ ^ 2 + γ * α + α ^ 2) = 2 * β ^ 3 := by
    rw [← cube_sub_eq_mul_of_le hle, gamma_cube_sub_alpha_cube_eq_two_beta hβ0 heq]
  have hsec_odd : Odd (γ ^ 2 + γ * α + α ^ 2) :=
    ((Odd.pow hγo).add_odd (hγo.mul hαo)).add_odd (Odd.pow hαo)
  have hsec_ne : ¬ 2 ∣ (γ ^ 2 + γ * α + α ^ 2) := Odd.not_two_dvd_nat hsec_odd
  have hβne : β ≠ 0 := Nat.pos_iff_ne_zero.mp hβ0
  have hdiff_ne : γ - α ≠ 0 :=
    Nat.sub_ne_zero_of_lt (alpha_lt_gamma_of_pos_cube hβ0 heq)
  have hsec_ne0 : γ ^ 2 + γ * α + α ^ 2 ≠ 0 := fun h => by
    have : α ^ 2 ≤ γ ^ 2 + γ * α + α ^ 2 := Nat.le_add_left _ _
    have : α = 0 := by omega
    subst this
    exact Nat.not_odd_iff_even.mpr (by decide : Even 0) hαo
  have hprod := padicValNat.mul (p := 2) hdiff_ne hsec_ne0
  have hsec0 : padicValNat 2 (γ ^ 2 + γ * α + α ^ 2) = 0 :=
    padicValNat.eq_zero_of_not_dvd hsec_ne
  have hrhs : padicValNat 2 (2 * β ^ 3) = 1 + 3 * padicValNat 2 β := by
    have h2 : padicValNat 2 2 = 1 := padicValNat_self (p := 2)
    have hb : padicValNat 2 (β ^ 3) = 3 * padicValNat 2 β :=
      padicValNat.pow (p := 2) β 3
    have hm := padicValNat.mul (p := 2) (by decide : (2 : ℕ) ≠ 0) (pow_ne_zero 3 hβne)
    simpa [h2, hb] using hm
  calc padicValNat 2 (γ - α)
      = padicValNat 2 ((γ - α) * (γ ^ 2 + γ * α + α ^ 2)) := by
          simp [hprod, hsec0]
    _ = padicValNat 2 (2 * β ^ 3) := by rw [hfac]
    _ = 1 + 3 * padicValNat 2 β := hrhs

/-! ### Phase 7q: 3-descent of the difference factors -/

theorem eq_of_nat_cube_eq {a b : ℕ} (h : a ^ 3 = b ^ 3) : a = b :=
  le_antisymm
    (le_of_pow_le_pow_left₀ (by decide : (3 : ℕ) ≠ 0) (Nat.zero_le _) (le_of_eq h))
    (le_of_pow_le_pow_left₀ (by decide : (3 : ℕ) ≠ 0) (Nat.zero_le _) (le_of_eq h.symm))

/--
Odd coordinates yield an integer half-sum and half-difference.
-/
theorem exists_half_sum_diff_of_odd {α γ : ℕ}
    (hαo : Odd α) (hγo : Odd γ) (hle : α ≤ γ) :
    ∃ τ δ : ℕ, γ + α = 2 * τ ∧ γ - α = 2 * δ ∧
      γ = τ + δ ∧ α = τ - δ ∧ δ ≤ τ := by
  have hsum2 : (γ + α) % 2 = 0 := by
    have := Nat.odd_iff.mp hγo
    have := Nat.odd_iff.mp hαo
    omega
  have hdiff2 : (γ - α) % 2 = 0 := by
    have := Nat.odd_iff.mp hγo
    have := Nat.odd_iff.mp hαo
    omega
  obtain ⟨τ, hτ⟩ := (Nat.dvd_iff_mod_eq_zero.mpr hsum2 : 2 ∣ γ + α)
  obtain ⟨δ, hδ⟩ := (Nat.dvd_iff_mod_eq_zero.mpr hdiff2 : 2 ∣ γ - α)
  have hδτ : δ ≤ τ := by
    have : 2 * δ ≤ 2 * τ := by
      rw [← hδ, ← hτ]
      omega
    omega
  refine ⟨τ, δ, hτ, hδ, ?_, ?_, hδτ⟩
  · have : 2 * γ = 2 * (τ + δ) := by omega
    exact Nat.mul_left_cancel (by decide : 0 < 2) this
  · have : 2 * α = 2 * (τ - δ) := by
      have : 2 * τ - 2 * δ = 2 * (τ - δ) := (Nat.mul_sub_left_distrib 2 τ δ).symm
      omega
    exact Nat.mul_left_cancel (by decide : 0 < 2) this

/--
On a half-sum / half-difference splitting, the quadratic factor is
`3 τ² + δ²`.
-/
theorem quad_factor_of_half_sum_diff {γ α τ δ : ℕ}
    (hle : α ≤ γ) (hsum : γ + α = 2 * τ) (hdiff : γ - α = 2 * δ) :
    γ ^ 2 + γ * α + α ^ 2 = 3 * τ ^ 2 + δ ^ 2 := by
  have h4 : 4 * (γ ^ 2 + γ * α + α ^ 2) =
      3 * (γ + α) ^ 2 + (γ - α) ^ 2 := by
    apply Int.ofNat_inj.mp
    have hγa : ((γ - α : ℕ) : ℤ) = (γ : ℤ) - α := Nat.cast_sub hle
    calc ((4 * (γ ^ 2 + γ * α + α ^ 2) : ℕ) : ℤ)
        = 4 * ((γ : ℤ) ^ 2 + γ * α + α ^ 2) := by push_cast; ring
      _ = 3 * ((γ : ℤ) + α) ^ 2 + ((γ : ℤ) - α) ^ 2 := by ring
      _ = 3 * ((γ + α : ℕ) : ℤ) ^ 2 + ((γ - α : ℕ) : ℤ) ^ 2 := by
            rw [hγa]; push_cast; ring
      _ = ((3 * (γ + α) ^ 2 + (γ - α) ^ 2 : ℕ) : ℤ) := by simp
  have : 4 * (γ ^ 2 + γ * α + α ^ 2) = 4 * (3 * τ ^ 2 + δ ^ 2) := by
    calc 4 * (γ ^ 2 + γ * α + α ^ 2)
        = 3 * (γ + α) ^ 2 + (γ - α) ^ 2 := h4
      _ = 3 * (2 * τ) ^ 2 + (2 * δ) ^ 2 := by rw [hsum, hdiff]
      _ = 4 * (3 * τ ^ 2 + δ ^ 2) := by ring
  exact Nat.mul_left_cancel (by decide : 0 < 4) this

/--
Elementary reconstruction identity:
`(τ+δ)³ − (τ−δ)³ = 2δ(3τ²+δ²)`.
-/
theorem cube_sub_of_half_sum_diff {τ δ : ℕ} (h : δ ≤ τ) :
    (τ + δ) ^ 3 - (τ - δ) ^ 3 = 2 * δ * (3 * τ ^ 2 + δ ^ 2) := by
  have hle : τ - δ ≤ τ + δ :=
    Nat.le_trans (Nat.sub_le _ _) (Nat.le_add_right _ _)
  have hpow : (τ - δ) ^ 3 ≤ (τ + δ) ^ 3 := Nat.pow_le_pow_left hle 3
  apply Int.ofNat_inj.mp
  have hτδ : ((τ - δ : ℕ) : ℤ) = (τ : ℤ) - δ := Nat.cast_sub h
  calc ((((τ + δ) ^ 3 - (τ - δ) ^ 3 : ℕ) : ℤ))
      = ((τ : ℤ) + δ) ^ 3 - ((τ : ℤ) - δ) ^ 3 := by
          rw [Nat.cast_sub hpow]; push_cast; rw [hτδ]
    _ = 2 * (δ : ℤ) * (3 * (τ : ℤ) ^ 2 + (δ : ℤ) ^ 2) := by ring
    _ = ((2 * δ * (3 * τ ^ 2 + δ ^ 2) : ℕ) : ℤ) := by rfl

theorem pos_cube_eq_of_half_sum_diff {τ δ β : ℕ} (hδ : δ ≤ τ)
    (hβ : β ^ 3 = δ * (3 * τ ^ 2 + δ ^ 2)) :
    (τ - δ) ^ 3 + 2 * β ^ 3 = (τ + δ) ^ 3 := by
  have hsub := cube_sub_of_half_sum_diff hδ
  have hle : (τ - δ) ^ 3 ≤ (τ + δ) ^ 3 :=
    Nat.pow_le_pow_left (Nat.le_trans (Nat.sub_le _ _) (Nat.le_add_right _ _)) 3
  calc (τ - δ) ^ 3 + 2 * β ^ 3
      = (τ - δ) ^ 3 + 2 * (δ * (3 * τ ^ 2 + δ ^ 2)) := by rw [hβ]
    _ = (τ - δ) ^ 3 + 2 * δ * (3 * τ ^ 2 + δ ^ 2) := by ring
    _ = (τ - δ) ^ 3 + ((τ + δ) ^ 3 - (τ - δ) ^ 3) := by rw [hsub]
    _ = (τ + δ) ^ 3 := Nat.add_sub_of_le hle

/-- Coprime difference factors have gcd `1` or `3`. -/
theorem gcd_cube_diff_eq_one_or_three {γ α : ℕ}
    (hlt : α < γ) (hcop : Nat.Coprime α γ) :
    Nat.gcd (γ - α) (γ ^ 2 + γ * α + α ^ 2) = 1 ∨
      Nat.gcd (γ - α) (γ ^ 2 + γ * α + α ^ 2) = 3 :=
  (Nat.dvd_prime Nat.prime_three).1
    (gcd_cube_diff_factors_dvd_three_of_coprime (Nat.le_of_lt hlt) hcop)

theorem three_dvd_quad_factor_of_three_dvd_diff {γ α : ℕ}
    (hle : α ≤ γ) (h3 : 3 ∣ γ - α) :
    3 ∣ γ ^ 2 + γ * α + α ^ 2 := by
  rw [quad_factor_eq_of_le hle]
  exact dvd_add (dvd_mul_of_dvd_left h3 _) ⟨α ^ 2, rfl⟩

/-- The gcd is `3` if and only if `3` divides the difference. -/
theorem three_dvd_gamma_sub_alpha_iff_gcd_eq_three {α γ : ℕ}
    (hlt : α < γ) (hcop : Nat.Coprime α γ) :
    3 ∣ γ - α ↔
      Nat.gcd (γ - α) (γ ^ 2 + γ * α + α ^ 2) = 3 := by
  constructor
  · intro h3
    have h3Q := three_dvd_quad_factor_of_three_dvd_diff (Nat.le_of_lt hlt) h3
    have hg3 : 3 ∣ Nat.gcd (γ - α) (γ ^ 2 + γ * α + α ^ 2) :=
      Nat.dvd_gcd h3 h3Q
    rcases gcd_cube_diff_eq_one_or_three hlt hcop with h1 | h3eq
    · exact False.elim ((by decide : ¬ 3 ∣ (1 : ℕ)) (h1 ▸ hg3))
    · exact h3eq
  · intro hg
    exact hg ▸ Nat.gcd_dvd_left _ _

theorem not_three_dvd_alpha_of_three_dvd_diff {α γ : ℕ}
    (hle : α ≤ γ) (hcop : Nat.Coprime α γ) (h3 : 3 ∣ γ - α) :
    ¬ 3 ∣ α := by
  intro hα
  have hγ : 3 ∣ γ := by
    have hγeq : γ = α + (γ - α) := (Nat.add_sub_of_le hle).symm
    rw [hγeq]
    exact dvd_add hα h3
  have : 3 ∣ Nat.gcd α γ := Nat.dvd_gcd hα hγ
  exact (by decide : ¬ 3 ∣ (1 : ℕ))
    ((Nat.coprime_iff_gcd_eq_one.mp hcop) ▸ this)

/--
If the difference factors are coprime, each is a cube up to the explicit
factor of `2` on the even difference: `γ − α = 2 t³` and
`γ² + γα + α² = s³`.
-/
theorem exists_pos_cube_gcd_one_almost_cubes
    {α β γ : ℕ} (hα0 : 0 < α) (hβ0 : 0 < β) (hγ0 : 0 < γ)
    (hgcd : Nat.gcd α (Nat.gcd β γ) = 1)
    (heq : α ^ 3 + 2 * β ^ 3 = γ ^ 3)
    (hg1 : Nat.gcd (γ - α) (γ ^ 2 + γ * α + α ^ 2) = 1) :
    ∃ t s : ℕ, 0 < t ∧ 0 < s ∧
      Nat.Coprime t s ∧ Odd s ∧ ¬ 3 ∣ t ∧
        γ - α = 2 * t ^ 3 ∧
          γ ^ 2 + γ * α + α ^ 2 = s ^ 3 ∧
            β = t * s := by
  obtain ⟨hlt, hαo, hγo, hcop, _, hfac, _⟩ :=
    pos_cube_diff_factor_package hα0 hβ0 hγ0 hgcd heq
  set D := γ - α
  set Q := γ ^ 2 + γ * α + α ^ 2
  have hDe : Even D :=
    (Nat.even_sub (Nat.le_of_lt hlt)).2
      (iff_of_false (Nat.not_even_iff_odd.2 hγo) (Nat.not_even_iff_odd.2 hαo))
  obtain ⟨D2, hD2⟩ := even_iff_exists_two_mul.mp hDe
  have hprod : D2 * Q = β ^ 3 := by
    have : 2 * (D2 * Q) = 2 * β ^ 3 := by
      calc 2 * (D2 * Q) = (2 * D2) * Q := by ring
        _ = D * Q := by rw [hD2]
        _ = 2 * β ^ 3 := hfac
    exact Nat.mul_left_cancel (by decide : 0 < 2) this
  have hcopDQ2 : Nat.Coprime D2 Q := by
    have hdiv : Nat.gcd D2 Q ∣ Nat.gcd D Q := by
      refine Nat.dvd_gcd ?_ (Nat.gcd_dvd_right _ _)
      have : Nat.gcd D2 Q ∣ D2 := Nat.gcd_dvd_left _ _
      have : Nat.gcd D2 Q ∣ 2 * D2 := dvd_mul_of_dvd_right this 2
      rwa [← hD2] at this
    have : Nat.gcd D2 Q ∣ 1 := by rwa [hg1] at hdiv
    exact Nat.coprime_iff_gcd_eq_one.2 (Nat.eq_one_of_dvd_one this)
  obtain ⟨t, ht⟩ := nat_eq_pow_of_mul_eq_pow_of_coprime hcopDQ2 hprod
  obtain ⟨s, hs⟩ := nat_eq_pow_of_mul_eq_pow_of_coprime_right hcopDQ2 hprod
  have ht0 : 0 < t := by
    have hDpos : 0 < D := Nat.sub_pos_of_lt hlt
    have hD20 : 0 < D2 := by
      by_contra h
      have : D2 = 0 := Nat.eq_zero_of_not_pos h
      subst this
      simp [hD2] at hDpos
    have ht0' : t ≠ 0 := by
      intro ht0
      subst ht0
      exact hD20.ne' (by simpa using ht)
    exact Nat.pos_iff_ne_zero.mpr ht0'
  have hs0 : 0 < s := by
    have hQpos : 0 < Q := lt_of_lt_of_le (pow_pos hα0 2) (Nat.le_add_left _ _)
    have hs0' : s ≠ 0 := by
      intro hs0
      subst hs0
      exact hQpos.ne' (by simpa using hs)
    exact Nat.pos_iff_ne_zero.mpr hs0'
  have hcopts : Nat.Coprime t s := by
    refine Nat.coprime_iff_gcd_eq_one.2 ?_
    set d := Nat.gcd t s
    have hdD : d ∣ D2 := by
      have : d ∣ t := Nat.gcd_dvd_left _ _
      have : d ∣ t ^ 3 := dvd_trans this (dvd_pow (dvd_refl t) (by decide : 3 ≠ 0))
      rwa [← ht] at this
    have hdQ : d ∣ Q := by
      have : d ∣ s := Nat.gcd_dvd_right _ _
      have : d ∣ s ^ 3 := dvd_trans this (dvd_pow (dvd_refl s) (by decide : 3 ≠ 0))
      rwa [← hs] at this
    have : d ∣ Nat.gcd D2 Q := Nat.dvd_gcd hdD hdQ
    have : d ∣ 1 := by rwa [Nat.coprime_iff_gcd_eq_one.mp hcopDQ2] at this
    exact Nat.eq_one_of_dvd_one this
  have hsodd : Odd s := by
    have hQodd : Odd Q :=
      ((Odd.pow hγo).add_odd (hγo.mul hαo)).add_odd (Odd.pow hαo)
    have : Odd (s ^ 3) := by simpa [hs] using hQodd
    simpa [pow_three] using Nat.Odd.of_mul_right this
  have ht3 : ¬ 3 ∣ t := by
    intro ht3'
    have h3D2 : 3 ∣ D2 := by
      have : 3 ∣ t ^ 3 := dvd_trans ht3' (dvd_pow (dvd_refl t) (by decide : 3 ≠ 0))
      rwa [← ht] at this
    have h3D : 3 ∣ D := by
      rw [hD2]
      exact dvd_mul_of_dvd_right h3D2 2
    have hg3 : Nat.gcd D Q = 3 :=
      (three_dvd_gamma_sub_alpha_iff_gcd_eq_three hlt hcop).1 h3D
    exact (by decide : (3 : ℕ) ≠ 1) (hg3.symm.trans hg1)
  refine ⟨t, s, ht0, hs0, hcopts, hsodd, ht3, ?_, hs, ?_⟩
  · rw [hD2, ht]
  · exact eq_of_nat_cube_eq (by rw [← hprod, ht, hs, mul_pow])

/--
Cubes modulo 9 of an integer not divisible by 3 are `1` or `8`.
-/
theorem nat_cube_mod_nine_of_not_three_dvd {v : ℕ} (h : ¬ 3 ∣ v) :
    v ^ 3 % 9 = 1 ∨ v ^ 3 % 9 = 8 := by
  have h9 : v % 9 = 1 ∨ v % 9 = 2 ∨ v % 9 = 4 ∨ v % 9 = 5 ∨
      v % 9 = 7 ∨ v % 9 = 8 := by
    have : v % 3 ≠ 0 := fun hv => h (Nat.dvd_iff_mod_eq_zero.mpr hv)
    omega
  have hv : v ^ 3 % 9 = (v % 9) ^ 3 % 9 := by rw [← Nat.pow_mod]
  rcases h9 with h | h | h | h | h | h <;> simp [hv, h]

/--
On `s³ = t⁶ + 3 τ²` with `3 ∤ t`, the half-sum is divisible by `3`.
(Otherwise the left-hand side would be `4` modulo `9`, which is not a cube.)
-/
theorem three_dvd_tau_of_cube_sixth {t s τ : ℕ}
    (ht3 : ¬ 3 ∣ t) (heq : s ^ 3 = t ^ 6 + 3 * τ ^ 2) : 3 ∣ τ := by
  have ht6 : t ^ 6 % 9 = 1 := by
    have ht3m := nat_cube_mod_nine_of_not_three_dvd ht3
    have h6 : t ^ 6 % 9 = (t ^ 3 % 9) ^ 2 % 9 := by
      have : t ^ 6 = (t ^ 3) ^ 2 := by ring
      rw [this, ← Nat.pow_mod]
    rcases ht3m with h | h <;> simp [h6, h]
  by_contra hτ
  have hτ2 : (3 * τ ^ 2) % 9 = 3 := by
    have h9 : τ % 9 = 1 ∨ τ % 9 = 2 ∨ τ % 9 = 4 ∨ τ % 9 = 5 ∨
        τ % 9 = 7 ∨ τ % 9 = 8 := by
      have : τ % 3 ≠ 0 := by
        intro h
        exact hτ (Nat.dvd_iff_mod_eq_zero.mpr h)
      omega
    have hsq : τ ^ 2 % 9 = (τ % 9) ^ 2 % 9 := by rw [← Nat.pow_mod]
    have hmul : (3 * τ ^ 2) % 9 = (3 * (τ ^ 2 % 9)) % 9 := by
      rw [Nat.mul_mod, Nat.mod_eq_of_lt (by decide : 3 < 9)]
    rcases h9 with h | h | h | h | h | h <;> simp [hmul, hsq, h]
  have hLHS : s ^ 3 % 9 = (t ^ 6 % 9 + (3 * τ ^ 2) % 9) % 9 := by
    rw [heq, Nat.add_mod]
  have : s ^ 3 % 9 = 4 := by rw [hLHS, ht6, hτ2]
  have hc : s ^ 3 % 9 = 0 ∨ s ^ 3 % 9 = 1 ∨ s ^ 3 % 9 = 8 := by
    have h : s % 9 = 0 ∨ s % 9 = 1 ∨ s % 9 = 2 ∨ s % 9 = 3 ∨ s % 9 = 4 ∨
        s % 9 = 5 ∨ s % 9 = 6 ∨ s % 9 = 7 ∨ s % 9 = 8 := by omega
    have hv : s ^ 3 % 9 = (s % 9) ^ 3 % 9 := by rw [← Nat.pow_mod]
    rcases h with h | h | h | h | h | h | h | h | h <;> simp [hv, h]
  omega

/--
Coprime difference factors collapse to the single equation
`s³ = t⁶ + 3 τ²` with `α = τ − t³`, `γ = τ + t³`, `β = t s`, and `3 ∣ τ`.
-/
theorem exists_pos_cube_gcd_one_half_sum
    {α β γ : ℕ} (hα0 : 0 < α) (hβ0 : 0 < β) (hγ0 : 0 < γ)
    (hgcd : Nat.gcd α (Nat.gcd β γ) = 1)
    (heq : α ^ 3 + 2 * β ^ 3 = γ ^ 3)
    (hg1 : Nat.gcd (γ - α) (γ ^ 2 + γ * α + α ^ 2) = 1) :
    ∃ t s τ : ℕ, 0 < t ∧ 0 < s ∧ t ^ 3 < τ ∧
      Nat.Coprime t s ∧ Odd s ∧ ¬ 3 ∣ t ∧ ¬ 3 ∣ s ∧ 3 ∣ τ ∧
        α = τ - t ^ 3 ∧ γ = τ + t ^ 3 ∧ β = t * s ∧
          s ^ 3 = t ^ 6 + 3 * τ ^ 2 := by
  obtain ⟨t, s, ht0, hs0, hcop, hsodd, ht3, hD, hQ, hβ⟩ :=
    exists_pos_cube_gcd_one_almost_cubes hα0 hβ0 hγ0 hgcd heq hg1
  obtain ⟨hlt, hαo, hγo, _, _, _, _⟩ :=
    pos_cube_diff_factor_package hα0 hβ0 hγ0 hgcd heq
  obtain ⟨τ, δ, hsum, hdiff, hγeq, hαeq, hδτ⟩ :=
    exists_half_sum_diff_of_odd hαo hγo (Nat.le_of_lt hlt)
  have hδ : δ = t ^ 3 :=
    Nat.mul_left_cancel (by decide : 0 < 2) (hdiff.symm.trans hD)
  subst hδ
  have hQτ : s ^ 3 = 3 * τ ^ 2 + (t ^ 3) ^ 2 := by
    have := quad_factor_of_half_sum_diff (Nat.le_of_lt hlt) hsum hdiff
    rwa [hQ] at this
  have hs3 : s ^ 3 = t ^ 6 + 3 * τ ^ 2 := by
    rw [hQτ, show (t ^ 3) ^ 2 = t ^ 6 by ring]
    ring
  have hτt : t ^ 3 < τ := by
    have : α = τ - t ^ 3 := hαeq
    omega
  have hτ3 : 3 ∣ τ := three_dvd_tau_of_cube_sixth ht3 hs3
  have hs3n : ¬ 3 ∣ s := by
    intro h3s
    have : 3 ∣ s ^ 3 := dvd_trans h3s (dvd_pow (dvd_refl s) (by decide : 3 ≠ 0))
    have hsum : 3 ∣ t ^ 6 + 3 * τ ^ 2 := by rwa [← hs3]
    have h3τ : 3 ∣ 3 * τ ^ 2 := ⟨τ ^ 2, rfl⟩
    have : 3 ∣ t ^ 6 := (Nat.dvd_add_iff_left h3τ).mpr hsum
    exact ht3 (Nat.Prime.dvd_of_dvd_pow Nat.prime_three this)
  exact ⟨t, s, τ, ht0, hs0, hτt, hcop, hsodd, ht3, hs3n, hτ3, hαeq, hγeq, hβ, hs3⟩

/--
The coprime parametrisation reconstructs a positive solution of
`α³ + 2β³ = γ³`.
-/
theorem pos_cube_eq_of_gcd_one_params {t s τ : ℕ}
    (h : t ^ 3 ≤ τ) (heq : s ^ 3 = t ^ 6 + 3 * τ ^ 2) :
    (τ - t ^ 3) ^ 3 + 2 * (t * s) ^ 3 = (τ + t ^ 3) ^ 3 := by
  have hβ : (t * s) ^ 3 = t ^ 3 * (3 * τ ^ 2 + (t ^ 3) ^ 2) := by
    rw [mul_pow, heq, show (t ^ 3) ^ 2 = t ^ 6 by ring]
    ring
  exact pos_cube_eq_of_half_sum_diff h hβ

theorem three_pow_pred_mul_three {k : ℕ} (hk : 0 < k) :
    3 ^ (3 * k - 1) * 3 = 3 ^ (3 * k) := by
  have hle : 1 ≤ 3 * k := by omega
  calc 3 ^ (3 * k - 1) * 3
      = 3 ^ (3 * k - 1) * 3 ^ 1 := by rw [pow_one]
    _ = 3 ^ ((3 * k - 1) + 1) := (pow_add _ _ _).symm
    _ = 3 ^ (3 * k) := by rw [Nat.sub_add_cancel hle]

theorem three_pow_sixth_pred_mul_three {k : ℕ} (hk : 0 < k) :
    3 ^ (6 * k - 3) * 3 = 3 ^ (6 * k - 2) := by
  have hex : 6 * k - 3 + 1 = 6 * k - 2 := by omega
  calc 3 ^ (6 * k - 3) * 3
      = 3 ^ (6 * k - 3) * 3 ^ 1 := by rw [pow_one]
    _ = 3 ^ (6 * k - 3 + 1) := (pow_add _ _ _).symm
    _ = 3 ^ (6 * k - 2) := by rw [hex]

theorem sq_of_three_pow_mul_t_cube {k t : ℕ} (_hk : 0 < k) :
    (3 ^ (3 * k - 1) * t ^ 3) ^ 2 = 3 ^ (6 * k - 2) * t ^ 6 := by
  have h2 : (3 * k - 1) * 2 = 6 * k - 2 := by omega
  calc (3 ^ (3 * k - 1) * t ^ 3) ^ 2
      = (3 ^ (3 * k - 1)) ^ 2 * (t ^ 3) ^ 2 := mul_pow _ _ 2
    _ = 3 ^ ((3 * k - 1) * 2) * t ^ 6 := by
          rw [← pow_mul, show (t ^ 3) ^ 2 = t ^ 6 by ring]
    _ = 3 ^ (6 * k - 2) * t ^ 6 := by rw [h2]

theorem three_pow_t_sixth_eq_cube {k t : ℕ} (_hk : 0 < k) :
    3 ^ (6 * k - 3) * t ^ 6 = (3 ^ (2 * k - 1) * t ^ 2) ^ 3 := by
  have h3 : 6 * k - 3 = (2 * k - 1) * 3 := by omega
  calc 3 ^ (6 * k - 3) * t ^ 6
      = 3 ^ ((2 * k - 1) * 3) * (t ^ 2) ^ 3 := by
          rw [h3, show t ^ 6 = (t ^ 2) ^ 3 by ring]
    _ = (3 ^ (2 * k - 1)) ^ 3 * (t ^ 2) ^ 3 := by rw [pow_mul]
    _ = (3 ^ (2 * k - 1) * t ^ 2) ^ 3 := (mul_pow _ _ 3).symm

/--
If `3` divides the difference of a primitive positive solution, then
`v₃(γ−α) = 3 v₃(β) − 1` and `v₃(γ²+γα+α²) = 1`.
-/
theorem padicValNat_three_of_pos_cube_three_dvd
    {α β γ : ℕ} (hα0 : 0 < α) (hβ0 : 0 < β) (hγ0 : 0 < γ)
    (hgcd : Nat.gcd α (Nat.gcd β γ) = 1)
    (heq : α ^ 3 + 2 * β ^ 3 = γ ^ 3)
    (h3 : 3 ∣ γ - α) :
    padicValNat 3 (γ - α) = 3 * padicValNat 3 β - 1 ∧
      padicValNat 3 (γ ^ 2 + γ * α + α ^ 2) = 1 ∧
        1 ≤ padicValNat 3 β := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hlt, _, _, hcop, _, hfac, _⟩ :=
    pos_cube_diff_factor_package hα0 hβ0 hγ0 hgcd heq
  set D := γ - α
  set Q := γ ^ 2 + γ * α + α ^ 2
  have hα3 : ¬ 3 ∣ α :=
    not_three_dvd_alpha_of_three_dvd_diff (Nat.le_of_lt hlt) hcop h3
  have hDne : D ≠ 0 := Nat.pos_iff_ne_zero.mp (Nat.sub_pos_of_lt hlt)
  have hQne : Q ≠ 0 :=
    Nat.pos_iff_ne_zero.mp (lt_of_lt_of_le (pow_pos hα0 2) (Nat.le_add_left _ _))
  have hAeq : D * (γ + 2 * α) + 3 * α ^ 2 = Q :=
    (quad_factor_eq_of_le (Nat.le_of_lt hlt)).symm
  set A := D * (γ + 2 * α)
  set B := 3 * α ^ 2
  have hAne : A ≠ 0 := by
    have : 0 < γ + 2 * α := Nat.add_pos_left hγ0 _
    exact Nat.mul_ne_zero hDne (Nat.pos_iff_ne_zero.mp this)
  have hBne : B ≠ 0 :=
    Nat.mul_ne_zero (by decide : (3 : ℕ) ≠ 0)
      (pow_ne_zero 2 (Nat.pos_iff_ne_zero.mp hα0))
  have hvB : padicValNat 3 B = 1 := by
    have hα0v : padicValNat 3 α = 0 := padicValNat.eq_zero_of_not_dvd hα3
    have hm := padicValNat.mul (p := 3) (by decide : (3 : ℕ) ≠ 0)
      (pow_ne_zero 2 (Nat.pos_iff_ne_zero.mp hα0))
    have h3self : padicValNat 3 3 = 1 := padicValNat_self (p := 3)
    have hα2 : padicValNat 3 (α ^ 2) = 2 * padicValNat 3 α :=
      padicValNat.pow (p := 3) α 2
    simpa [h3self, hα2, hα0v] using hm
  have h3sum : 3 ∣ γ + 2 * α := by
    have hγ : γ = α + D := (Nat.add_sub_of_le (Nat.le_of_lt hlt)).symm
    have : γ + 2 * α = D + 3 * α := by
      rw [hγ]; ring
    rw [this]
    exact dvd_add h3 ⟨α, rfl⟩
  have h9A : 9 ∣ A := by
    have : 3 * 3 ∣ D * (γ + 2 * α) := Nat.mul_dvd_mul h3 h3sum
    simpa [show (9 : ℕ) = 3 * 3 by decide] using this
  have hQeq : A + B = Q := hAeq
  have hn9Q : ¬ 9 ∣ Q := by
    intro h9
    have h9AB : 9 ∣ A + B := by simpa [hQeq] using h9
    have h9B : 9 ∣ B := (Nat.dvd_add_iff_right h9A).mpr h9AB
    have : 2 ≤ padicValNat 3 B := (padicValNat_dvd_iff_le hBne (n := 2)).mp h9B
    omega
  have hvQ : padicValNat 3 Q = 1 := by
    have h3Q : 3 ∣ Q := by
      rw [← hQeq]
      exact dvd_add (dvd_trans (by decide : 3 ∣ 9) h9A) ⟨α ^ 2, rfl⟩
    have hge : 1 ≤ padicValNat 3 Q :=
      (padicValNat_dvd_iff_le hQne (n := 1)).mp h3Q
    have hlt2 : padicValNat 3 Q < 2 := by
      by_contra h
      have : 2 ≤ padicValNat 3 Q := Nat.le_of_not_lt h
      exact hn9Q ((padicValNat_dvd_iff_le hQne (n := 2)).mpr this)
    omega
  have hkpos : 1 ≤ padicValNat 3 β := by
    have h3β3 : 3 ∣ β ^ 3 := by
      have : 3 ∣ D * Q := dvd_mul_of_dvd_left h3 _
      have : 3 ∣ 2 * β ^ 3 := by rwa [hfac] at this
      exact Nat.Coprime.dvd_of_dvd_mul_left (by decide : Nat.Coprime 3 2)
        (by simpa [mul_comm] using this)
    have h3β : 3 ∣ β := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3β3
    exact (padicValNat_dvd_iff_le (Nat.pos_iff_ne_zero.mp hβ0) (n := 1)).mp h3β
  have hvprod : padicValNat 3 (D * Q) = padicValNat 3 D + padicValNat 3 Q :=
    padicValNat.mul (p := 3) hDne hQne
  have hrhs : padicValNat 3 (2 * β ^ 3) = 3 * padicValNat 3 β := by
    have h2 : padicValNat 3 2 = 0 :=
      padicValNat.eq_zero_of_not_dvd (by decide : ¬ 3 ∣ 2)
    have hb : padicValNat 3 (β ^ 3) = 3 * padicValNat 3 β :=
      padicValNat.pow (p := 3) β 3
    have hm := padicValNat.mul (p := 3) (by decide : (2 : ℕ) ≠ 0)
      (pow_ne_zero 3 (Nat.pos_iff_ne_zero.mp hβ0))
    simpa [h2, hb] using hm
  have hvD : padicValNat 3 D = 3 * padicValNat 3 β - 1 := by
    have : padicValNat 3 D + 1 = 3 * padicValNat 3 β := by
      have : padicValNat 3 (D * Q) = padicValNat 3 (2 * β ^ 3) := by rw [hfac]
      simpa [hvprod, hvQ, hrhs] using this
    omega
  exact ⟨hvD, hvQ, hkpos⟩

/--
If the difference-factor gcd is `3`, stripping the 3-primary part yields
`γ − α = 2 · 3^{3k−1} t³` and `γ² + γα + α² = 3 s³` with `k = v₃(β) ≥ 1`.
-/
theorem exists_pos_cube_gcd_three_almost_cubes
    {α β γ : ℕ} (hα0 : 0 < α) (hβ0 : 0 < β) (hγ0 : 0 < γ)
    (hgcd : Nat.gcd α (Nat.gcd β γ) = 1)
    (heq : α ^ 3 + 2 * β ^ 3 = γ ^ 3)
    (hg3 : Nat.gcd (γ - α) (γ ^ 2 + γ * α + α ^ 2) = 3) :
    ∃ k t s : ℕ, 0 < k ∧ 0 < t ∧ 0 < s ∧
      Nat.Coprime t s ∧ Odd s ∧ ¬ 3 ∣ t ∧ ¬ 3 ∣ s ∧
        k = padicValNat 3 β ∧
          γ - α = 2 * (3 ^ (3 * k - 1) * t ^ 3) ∧
            γ ^ 2 + γ * α + α ^ 2 = 3 * s ^ 3 ∧
              β = 3 ^ k * t * s := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hlt, hαo, hγo, hcop, _, hfac, _⟩ :=
    pos_cube_diff_factor_package hα0 hβ0 hγ0 hgcd heq
  have h3D : 3 ∣ γ - α :=
    (three_dvd_gamma_sub_alpha_iff_gcd_eq_three hlt hcop).2 hg3
  obtain ⟨hvD, hvQ, hkpos⟩ :=
    padicValNat_three_of_pos_cube_three_dvd hα0 hβ0 hγ0 hgcd heq h3D
  set k := padicValNat 3 β
  set D := γ - α
  set Q := γ ^ 2 + γ * α + α ^ 2
  have hDne : D ≠ 0 := Nat.pos_iff_ne_zero.mp (Nat.sub_pos_of_lt hlt)
  have hQne : Q ≠ 0 :=
    Nat.pos_iff_ne_zero.mp (lt_of_lt_of_le (pow_pos hα0 2) (Nat.le_add_left _ _))
  have hβne : β ≠ 0 := Nat.pos_iff_ne_zero.mp hβ0
  have hvDeq : padicValNat 3 D = 3 * k - 1 := hvD
  have hDsplit : 3 ^ (3 * k - 1) * (D / 3 ^ (3 * k - 1)) = D := by
    have hdiv : 3 ^ (3 * k - 1) ∣ D :=
      (padicValNat_dvd_iff_le hDne (n := 3 * k - 1)).mpr (le_of_eq hvDeq.symm)
    exact Nat.mul_div_cancel' hdiv
  set D3 := D / 3 ^ (3 * k - 1)
  have h3Q : 3 ∣ Q := (padicValNat_dvd_iff_le hQne (n := 1)).mpr (le_of_eq hvQ.symm)
  have hQsplit : 3 * (Q / 3) = Q := Nat.mul_div_cancel' h3Q
  set Q3 := Q / 3
  have hβsplit : 3 ^ k * (β / 3 ^ k) = β := by
    have hdiv : 3 ^ k ∣ β :=
      (padicValNat_dvd_iff_le hβne (n := k)).mpr (le_of_eq rfl)
    exact Nat.mul_div_cancel' hdiv
  set β0 := β / 3 ^ k
  have hk : 0 < k := hkpos
  have hprod3 : D3 * Q3 = 2 * β0 ^ 3 := by
    have hmul :
        3 ^ (3 * k) * (D3 * Q3) = 3 ^ (3 * k) * (2 * β0 ^ 3) := by
      calc 3 ^ (3 * k) * (D3 * Q3)
          = (3 ^ (3 * k - 1) * 3) * (D3 * Q3) := by
              rw [three_pow_pred_mul_three hk]
        _ = (3 ^ (3 * k - 1) * D3) * (3 * Q3) := by
              simp [mul_assoc, mul_left_comm, mul_comm]
        _ = D * Q := by rw [hDsplit, hQsplit]
        _ = 2 * β ^ 3 := hfac
        _ = 2 * (3 ^ k * β0) ^ 3 := by rw [hβsplit]
        _ = 2 * (3 ^ (3 * k) * β0 ^ 3) := by
              rw [mul_pow]
              have : (3 ^ k) ^ 3 = 3 ^ (3 * k) := by
                rw [← pow_mul]; congr 1; ring
              rw [this]
        _ = 3 ^ (3 * k) * (2 * β0 ^ 3) := by
              simp [mul_left_comm]
    exact Nat.mul_left_cancel (pow_pos (by decide : 0 < 3) (3 * k)) hmul
  have hD3e : Even D3 := by
    have hDe : Even D :=
      (Nat.even_sub (Nat.le_of_lt hlt)).2
        (iff_of_false (Nat.not_even_iff_odd.2 hγo) (Nat.not_even_iff_odd.2 hαo))
    have : Even (3 ^ (3 * k - 1) * D3) := by rwa [hDsplit]
    have hodd : Odd (3 ^ (3 * k - 1)) := Odd.pow (by decide : Odd 3)
    exact (Nat.even_mul.mp this).resolve_left (Nat.not_even_iff_odd.2 hodd)
  obtain ⟨D3h, hD3h⟩ := even_iff_exists_two_mul.mp hD3e
  have hprod2 : D3h * Q3 = β0 ^ 3 := by
    have : 2 * (D3h * Q3) = 2 * β0 ^ 3 := by
      calc 2 * (D3h * Q3) = (2 * D3h) * Q3 := by ring
        _ = D3 * Q3 := by rw [hD3h]
        _ = 2 * β0 ^ 3 := hprod3
    exact Nat.mul_left_cancel (by decide : 0 < 2) this
  have hcop3 : Nat.Coprime D3 Q3 := by
    refine Nat.coprime_iff_gcd_eq_one.2 ?_
    set d := Nat.gcd D3 Q3
    have hdD : d ∣ D := by
      have : d ∣ D3 := Nat.gcd_dvd_left _ _
      have : d ∣ 3 ^ (3 * k - 1) * D3 := dvd_mul_of_dvd_right this _
      rwa [hDsplit] at this
    have hdQ : d ∣ Q := by
      have : d ∣ Q3 := Nat.gcd_dvd_right _ _
      have : d ∣ 3 * Q3 := dvd_mul_of_dvd_right this _
      rwa [hQsplit] at this
    have hd3 : d ∣ 3 := by
      have : d ∣ Nat.gcd D Q := Nat.dvd_gcd hdD hdQ
      rwa [hg3] at this
    rcases (Nat.dvd_prime Nat.prime_three).1 hd3 with h1 | h3d
    · exact h1
    · have h3D3 : 3 ∣ D3 := h3d ▸ Nat.gcd_dvd_left D3 Q3
      have : 3 ^ (3 * k) ∣ D := by
        have : 3 ^ ((3 * k - 1) + 1) ∣ 3 ^ (3 * k - 1) * D3 := by
          rw [pow_add, pow_one]
          exact mul_dvd_mul_left _ h3D3
        have hv1 : (3 * k - 1) + 1 = 3 * k := by omega
        rwa [hv1, hDsplit] at this
      have : 3 * k ≤ padicValNat 3 D :=
        (padicValNat_dvd_iff_le hDne (n := 3 * k)).mp this
      omega
  have hcop2 : Nat.Coprime D3h Q3 := by
    have hdiv : Nat.gcd D3h Q3 ∣ Nat.gcd D3 Q3 := by
      refine Nat.dvd_gcd ?_ (Nat.gcd_dvd_right _ _)
      have : Nat.gcd D3h Q3 ∣ D3h := Nat.gcd_dvd_left _ _
      have : Nat.gcd D3h Q3 ∣ 2 * D3h := dvd_mul_of_dvd_right this 2
      rwa [← hD3h] at this
    have : Nat.gcd D3h Q3 ∣ 1 := by
      rwa [Nat.coprime_iff_gcd_eq_one.mp hcop3] at hdiv
    exact Nat.coprime_iff_gcd_eq_one.2 (Nat.eq_one_of_dvd_one this)
  obtain ⟨t, ht⟩ := nat_eq_pow_of_mul_eq_pow_of_coprime hcop2 hprod2
  obtain ⟨s, hs⟩ := nat_eq_pow_of_mul_eq_pow_of_coprime_right hcop2 hprod2
  have ht0 : 0 < t := by
    have hD3h0 : 0 < D3h := by
      have hDpos : 0 < D := Nat.sub_pos_of_lt hlt
      have hD30 : 0 < D3 := by
        have : 0 < 3 ^ (3 * k - 1) := pow_pos (by decide : 0 < 3) _
        exact Nat.pos_of_mul_pos_left (hDsplit ▸ hDpos)
      have : 0 < 2 * D3h := by rwa [← hD3h]
      omega
    have ht0' : t ≠ 0 := by
      intro ht0
      subst ht0
      exact hD3h0.ne' (by simpa using ht)
    exact Nat.pos_iff_ne_zero.mpr ht0'
  have hs0 : 0 < s := by
    have hQ30 : 0 < Q3 := by
      have hQpos : 0 < Q := lt_of_lt_of_le (pow_pos hα0 2) (Nat.le_add_left _ _)
      exact Nat.pos_of_mul_pos_left (hQsplit ▸ hQpos)
    have hs0' : s ≠ 0 := by
      intro hs0
      subst hs0
      exact hQ30.ne' (by simpa using hs)
    exact Nat.pos_iff_ne_zero.mpr hs0'
  have hcopts : Nat.Coprime t s := by
    refine Nat.coprime_iff_gcd_eq_one.2 ?_
    set d := Nat.gcd t s
    have hdD : d ∣ D3h := by
      have : d ∣ t := Nat.gcd_dvd_left _ _
      have : d ∣ t ^ 3 := dvd_trans this (dvd_pow (dvd_refl t) (by decide : 3 ≠ 0))
      rwa [← ht] at this
    have hdQ : d ∣ Q3 := by
      have : d ∣ s := Nat.gcd_dvd_right _ _
      have : d ∣ s ^ 3 := dvd_trans this (dvd_pow (dvd_refl s) (by decide : 3 ≠ 0))
      rwa [← hs] at this
    have : d ∣ Nat.gcd D3h Q3 := Nat.dvd_gcd hdD hdQ
    have : d ∣ 1 := by rwa [Nat.coprime_iff_gcd_eq_one.mp hcop2] at this
    exact Nat.eq_one_of_dvd_one this
  have hsodd : Odd s := by
    have hQodd : Odd Q :=
      ((Odd.pow hγo).add_odd (hγo.mul hαo)).add_odd (Odd.pow hαo)
    have hQ3odd : Odd Q3 := by
      have : Odd (3 * Q3) := by simpa [hQsplit] using hQodd
      exact Nat.Odd.of_mul_right this
    have : Odd (s ^ 3) := by simpa [hs] using hQ3odd
    simpa [pow_three] using Nat.Odd.of_mul_right this
  have ht3 : ¬ 3 ∣ t := by
    intro ht3'
    have h3D3h : 3 ∣ D3h := by
      have : 3 ∣ t ^ 3 := dvd_trans ht3' (dvd_pow (dvd_refl t) (by decide : 3 ≠ 0))
      rwa [← ht] at this
    have h3D3 : 3 ∣ D3 := by
      rw [hD3h]
      exact dvd_mul_of_dvd_right h3D3h 2
    have : 3 ^ (3 * k) ∣ D := by
      have : 3 ^ ((3 * k - 1) + 1) ∣ 3 ^ (3 * k - 1) * D3 := by
        rw [pow_add, pow_one]
        exact mul_dvd_mul_left _ h3D3
      have hv1 : (3 * k - 1) + 1 = 3 * k := by omega
      rwa [hv1, hDsplit] at this
    have : 3 * k ≤ padicValNat 3 D :=
      (padicValNat_dvd_iff_le hDne (n := 3 * k)).mp this
    omega
  have hs3n : ¬ 3 ∣ s := by
    intro hs3'
    have h3Q3 : 3 ∣ Q3 := by
      have : 3 ∣ s ^ 3 := dvd_trans hs3' (dvd_pow (dvd_refl s) (by decide : 3 ≠ 0))
      rwa [← hs] at this
    have h9Q : 9 ∣ Q := by
      have : 3 * 3 ∣ 3 * Q3 := Nat.mul_dvd_mul_left 3 h3Q3
      simpa [show (9 : ℕ) = 3 * 3 by decide, hQsplit] using this
    have : 2 ≤ padicValNat 3 Q := (padicValNat_dvd_iff_le hQne (n := 2)).mp h9Q
    omega
  have hDform : D = 2 * (3 ^ (3 * k - 1) * t ^ 3) := by
    calc D = 3 ^ (3 * k - 1) * D3 := hDsplit.symm
      _ = 3 ^ (3 * k - 1) * (2 * D3h) := by rw [hD3h]
      _ = 2 * (3 ^ (3 * k - 1) * t ^ 3) := by rw [ht]; ring
  have hQform : Q = 3 * s ^ 3 := by rw [← hQsplit, hs]
  have hβform : β = 3 ^ k * t * s := by
    have hβ0 : β0 = t * s :=
      eq_of_nat_cube_eq (by
        calc β0 ^ 3 = D3h * Q3 := hprod2.symm
          _ = t ^ 3 * s ^ 3 := by rw [ht, hs]
          _ = (t * s) ^ 3 := (mul_pow t s 3).symm)
    calc β = 3 ^ k * β0 := hβsplit.symm
      _ = 3 ^ k * t * s := by rw [hβ0]; ring
  exact ⟨k, t, s, hk, ht0, hs0, hcopts, hsodd, ht3, hs3n, rfl, hDform, hQform, hβform⟩

/--
The gcd-`3` branch collapses to `s³ = τ² + (3^{2k−1} t²)³`.
-/
theorem exists_pos_cube_gcd_three_half_sum
    {α β γ : ℕ} (hα0 : 0 < α) (hβ0 : 0 < β) (hγ0 : 0 < γ)
    (hgcd : Nat.gcd α (Nat.gcd β γ) = 1)
    (heq : α ^ 3 + 2 * β ^ 3 = γ ^ 3)
    (hg3 : Nat.gcd (γ - α) (γ ^ 2 + γ * α + α ^ 2) = 3) :
    ∃ k t s τ : ℕ, 0 < k ∧ 0 < t ∧ 0 < s ∧
      3 ^ (3 * k - 1) * t ^ 3 < τ ∧
        Nat.Coprime t s ∧ Odd s ∧ ¬ 3 ∣ t ∧ ¬ 3 ∣ s ∧
          k = padicValNat 3 β ∧
            α = τ - 3 ^ (3 * k - 1) * t ^ 3 ∧
              γ = τ + 3 ^ (3 * k - 1) * t ^ 3 ∧
                β = 3 ^ k * t * s ∧
                  s ^ 3 = τ ^ 2 + (3 ^ (2 * k - 1) * t ^ 2) ^ 3 := by
  obtain ⟨k, t, s, hk, ht0, hs0, hcop, hsodd, ht3, hs3n, hkEq, hD, hQ, hβ⟩ :=
    exists_pos_cube_gcd_three_almost_cubes hα0 hβ0 hγ0 hgcd heq hg3
  obtain ⟨hlt, hαo, hγo, _, _, _, _⟩ :=
    pos_cube_diff_factor_package hα0 hβ0 hγ0 hgcd heq
  obtain ⟨τ, δ, hsum, hdiff, hγeq, hαeq, hδτ⟩ :=
    exists_half_sum_diff_of_odd hαo hγo (Nat.le_of_lt hlt)
  have hδ : δ = 3 ^ (3 * k - 1) * t ^ 3 :=
    Nat.mul_left_cancel (by decide : 0 < 2) (hdiff.symm.trans hD)
  subst hδ
  have hQτ : 3 * s ^ 3 = 3 * τ ^ 2 + (3 ^ (3 * k - 1) * t ^ 3) ^ 2 := by
    have := quad_factor_of_half_sum_diff (Nat.le_of_lt hlt) hsum hdiff
    rwa [hQ] at this
  have hs3 : s ^ 3 = τ ^ 2 + (3 ^ (2 * k - 1) * t ^ 2) ^ 3 := by
    have hmul :
        3 * s ^ 3 = 3 * (τ ^ 2 + (3 ^ (2 * k - 1) * t ^ 2) ^ 3) := by
      have hsq := sq_of_three_pow_mul_t_cube (t := t) hk
      have hcube := three_pow_t_sixth_eq_cube (t := t) hk
      have hpow := three_pow_sixth_pred_mul_three hk
      calc 3 * s ^ 3
          = 3 * τ ^ 2 + (3 ^ (3 * k - 1) * t ^ 3) ^ 2 := hQτ
        _ = 3 * τ ^ 2 + 3 ^ (6 * k - 2) * t ^ 6 := by rw [hsq]
        _ = 3 * τ ^ 2 + 3 ^ (6 * k - 3) * 3 * t ^ 6 := by rw [← hpow]
        _ = 3 * τ ^ 2 + 3 * (3 ^ (6 * k - 3) * t ^ 6) := by
              simp [mul_left_comm, mul_comm]
        _ = 3 * (τ ^ 2 + 3 ^ (6 * k - 3) * t ^ 6) := by
              simp [mul_add]
        _ = 3 * (τ ^ 2 + (3 ^ (2 * k - 1) * t ^ 2) ^ 3) := by rw [hcube]
    exact Nat.mul_left_cancel (by decide : 0 < 3) hmul
  have hτt : 3 ^ (3 * k - 1) * t ^ 3 < τ := by
    have : α = τ - 3 ^ (3 * k - 1) * t ^ 3 := hαeq
    omega
  exact ⟨k, t, s, τ, hk, ht0, hs0, hτt, hcop, hsodd, ht3, hs3n, hkEq,
    hαeq, hγeq, hβ, hs3⟩

/--
A primitive positive solution occupies exactly one of the two 3-descent
branches.
-/
theorem pos_cube_three_descent_dichotomy
    {α β γ : ℕ} (hα0 : 0 < α) (hβ0 : 0 < β) (hγ0 : 0 < γ)
    (hgcd : Nat.gcd α (Nat.gcd β γ) = 1)
    (heq : α ^ 3 + 2 * β ^ 3 = γ ^ 3) :
    (∃ t s τ : ℕ, 0 < t ∧ 0 < s ∧ t ^ 3 < τ ∧
        Nat.Coprime t s ∧ Odd s ∧ ¬ 3 ∣ t ∧ ¬ 3 ∣ s ∧ 3 ∣ τ ∧
          α = τ - t ^ 3 ∧ γ = τ + t ^ 3 ∧ β = t * s ∧
            s ^ 3 = t ^ 6 + 3 * τ ^ 2) ∨
      ∃ k t s τ : ℕ, 0 < k ∧ 0 < t ∧ 0 < s ∧
        3 ^ (3 * k - 1) * t ^ 3 < τ ∧
          Nat.Coprime t s ∧ Odd s ∧ ¬ 3 ∣ t ∧ ¬ 3 ∣ s ∧
            k = padicValNat 3 β ∧
              α = τ - 3 ^ (3 * k - 1) * t ^ 3 ∧
                γ = τ + 3 ^ (3 * k - 1) * t ^ 3 ∧
                  β = 3 ^ k * t * s ∧
                    s ^ 3 = τ ^ 2 + (3 ^ (2 * k - 1) * t ^ 2) ^ 3 := by
  obtain ⟨hlt, _, _, hcop, _, _, _⟩ :=
    pos_cube_diff_factor_package hα0 hβ0 hγ0 hgcd heq
  rcases gcd_cube_diff_eq_one_or_three hlt hcop with hg1 | hg3
  · exact Or.inl
      (exists_pos_cube_gcd_one_half_sum hα0 hβ0 hγ0 hgcd heq hg1)
  · exact Or.inr
      (exists_pos_cube_gcd_three_half_sum hα0 hβ0 hγ0 hgcd heq hg3)

/--
The gcd-`3` parametrisation reconstructs a positive solution of
`α³ + 2β³ = γ³`.
-/
theorem pos_cube_eq_of_gcd_three_params {k t s τ : ℕ}
    (hk : 0 < k) (h : 3 ^ (3 * k - 1) * t ^ 3 ≤ τ)
    (heq : s ^ 3 = τ ^ 2 + (3 ^ (2 * k - 1) * t ^ 2) ^ 3) :
    (τ - 3 ^ (3 * k - 1) * t ^ 3) ^ 3 + 2 * (3 ^ k * t * s) ^ 3 =
      (τ + 3 ^ (3 * k - 1) * t ^ 3) ^ 3 := by
  set δ := 3 ^ (3 * k - 1) * t ^ 3
  have hβ : (3 ^ k * t * s) ^ 3 = δ * (3 * τ ^ 2 + δ ^ 2) := by
    have hsq : δ ^ 2 = 3 ^ (6 * k - 2) * t ^ 6 := by
      simpa [δ] using sq_of_three_pow_mul_t_cube (k := k) (t := t) hk
    have hcube := three_pow_t_sixth_eq_cube (k := k) (t := t) hk
    have hpow3 := three_pow_pred_mul_three hk
    have hpow6 := three_pow_sixth_pred_mul_three hk
    have hδQ : δ * (3 * τ ^ 2 + δ ^ 2) =
        3 ^ (3 * k) * t ^ 3 * (τ ^ 2 + (3 ^ (2 * k - 1) * t ^ 2) ^ 3) := by
      calc δ * (3 * τ ^ 2 + δ ^ 2)
          = 3 ^ (3 * k - 1) * t ^ 3 *
              (3 * τ ^ 2 + 3 ^ (6 * k - 2) * t ^ 6) := by
                rw [hsq]
        _ = 3 ^ (3 * k - 1) * t ^ 3 *
              (3 * τ ^ 2 + 3 ^ (6 * k - 3) * 3 * t ^ 6) := by rw [← hpow6]
        _ = 3 ^ (3 * k - 1) * t ^ 3 *
              (3 * τ ^ 2 + 3 * (3 ^ (6 * k - 3) * t ^ 6)) := by
                simp [mul_left_comm, mul_comm]
        _ = (3 ^ (3 * k - 1) * 3) * t ^ 3 *
              (τ ^ 2 + 3 ^ (6 * k - 3) * t ^ 6) := by
                simp [mul_add, mul_assoc, mul_left_comm, mul_comm]
        _ = 3 ^ (3 * k) * t ^ 3 *
              (τ ^ 2 + 3 ^ (6 * k - 3) * t ^ 6) := by rw [hpow3]
        _ = 3 ^ (3 * k) * t ^ 3 *
              (τ ^ 2 + (3 ^ (2 * k - 1) * t ^ 2) ^ 3) := by rw [hcube]
    have hpow : (3 ^ k * t * s) ^ 3 = 3 ^ (3 * k) * t ^ 3 * s ^ 3 := by
      rw [mul_assoc (3 ^ k), mul_pow, mul_pow]
      have : (3 ^ k) ^ 3 = 3 ^ (3 * k) := by
        rw [← pow_mul]; congr 1; ring
      rw [this, mul_assoc]
    calc (3 ^ k * t * s) ^ 3
        = 3 ^ (3 * k) * t ^ 3 * s ^ 3 := hpow
      _ = 3 ^ (3 * k) * t ^ 3 *
          (τ ^ 2 + (3 ^ (2 * k - 1) * t ^ 2) ^ 3) := by rw [heq]
      _ = δ * (3 * τ ^ 2 + δ ^ 2) := hδQ.symm
  exact pos_cube_eq_of_half_sum_diff h hβ

/-! ### Phase 7o: Weierstrass model of `X³ + 2Y³ = 1` -/

/--
Forward map (for `X ≠ 1`):
`x = 24 Y / (1 - X)`, `y = 72 (1 + X) / (1 - X)`.
On solutions of `X³ + 2Y³ = 1` this lands on the Mordell curve
`y² = x³ - 1728` (equivalently `y² = x³ - 432 · 2²`).
-/
def affineCubeAddTwoToMordell (X Y : ℚ) : ℚ × ℚ :=
  (24 * Y / (1 - X), 72 * (1 + X) / (1 - X))

/--
Algebraic identity underlying the forward map: on `X³ + 2Y³ = 1`,
`8Y³ - (1-X)³ = 3(1-X)(1+X)²`.
-/
theorem eight_Y_cube_sub_one_sub_X_cube
    {X Y : ℚ} (heq : X ^ 3 + 2 * Y ^ 3 = 1) :
    8 * Y ^ 3 - (1 - X) ^ 3 = 3 * (1 - X) * (1 + X) ^ 2 := by
  have hY3 : 2 * Y ^ 3 = 1 - X ^ 3 := by linarith
  have h8 : 8 * Y ^ 3 = 4 * (1 - X ^ 3) := by linarith [hY3]
  rw [h8, show 1 - X ^ 3 = (1 - X) * (1 + X + X ^ 2) by ring]
  ring

/--
Identity: if `X³ + 2Y³ = 1` and `X ≠ 1`, then the forward image lies on
`y² = x³ - 1728`.
-/
theorem mordell_of_affine_cube_add_two
    {X Y : ℚ} (heq : X ^ 3 + 2 * Y ^ 3 = 1) (hX : X ≠ 1) :
    let p := affineCubeAddTwoToMordell X Y
    p.2 ^ 2 = p.1 ^ 3 - 1728 := by
  have hne : (1 - X : ℚ) ≠ 0 := sub_ne_zero.mpr (Ne.symm hX)
  have h8 := eight_Y_cube_sub_one_sub_X_cube heq
  -- Clear a common denominator `(1-X)³`.
  have hclear :
      ((72 * (1 + X) / (1 - X)) ^ 2 - ((24 * Y / (1 - X)) ^ 3 - 1728)) *
        (1 - X) ^ 3 = 0 := by
    field_simp [hne]
    -- Goal becomes a polynomial identity using h8.
    have := congrArg (· * (1 - X) ^ 3) h8
    ring_nf at this ⊢
    linarith
  have hden : (1 - X) ^ 3 ≠ 0 := pow_ne_zero 3 hne
  have : (72 * (1 + X) / (1 - X)) ^ 2 -
      ((24 * Y / (1 - X)) ^ 3 - 1728) = 0 :=
    (mul_eq_zero.mp hclear).resolve_right hden
  simpa [affineCubeAddTwoToMordell, sub_eq_zero] using this

/-- Forward map sends `(-1, 1)` to the 2-torsion point `(12, 0)`. -/
theorem affineCubeAddTwoToMordell_neg_one_one :
    affineCubeAddTwoToMordell (-1) 1 = (12, 0) := by
  simp [affineCubeAddTwoToMordell]; norm_num

/--
If the forward image is `(12, 0)`, the Affine point is `(-1, 1)`.
-/
theorem eq_neg_one_one_of_affine_to_mordell_twelve
    {X Y : ℚ} (hX : X ≠ 1)
    (hx : (affineCubeAddTwoToMordell X Y).1 = 12)
    (hy : (affineCubeAddTwoToMordell X Y).2 = 0) :
    X = -1 ∧ Y = 1 := by
  have hne : (1 - X : ℚ) ≠ 0 := sub_ne_zero.mpr (Ne.symm hX)
  have hy' : 72 * (1 + X) / (1 - X) = 0 := by
    simpa [affineCubeAddTwoToMordell] using hy
  have hX' : X = -1 := by
    have : 72 * (1 + X) = 0 := by
      field_simp [hne] at hy'
      simpa using hy'
    have : 1 + X = 0 := by linarith
    linarith
  refine ⟨hX', ?_⟩
  have hx' : 24 * Y / (1 - X) = 12 := by
    simpa [affineCubeAddTwoToMordell] using hx
  subst hX'
  field_simp at hx'
  linarith

/--
If `Y = 0` on `X³ + 2Y³ = 1`, then `X = 1` (only rational cube root of 1).
-/
theorem eq_one_of_affine_cube_add_two_Y_zero
    {X : ℚ} (heq : X ^ 3 + 2 * (0 : ℚ) ^ 3 = 1) : X = 1 := by
  have hX3 : X ^ 3 = 1 := by simpa using heq
  have hfac : (X - 1) * (X ^ 2 + X + 1) = 0 := by
    have : X ^ 3 - 1 = 0 := by linarith [hX3]
    have hId : X ^ 3 - 1 = (X - 1) * (X ^ 2 + X + 1) := by ring
    linarith [this, hId]
  rcases mul_eq_zero.mp hfac with h | h
  · linarith
  · have hdisc : ¬ ∃ r : ℚ, r ^ 2 + r + 1 = 0 := by
      intro ⟨r, hr⟩
      have h4 : (2 * r + 1) ^ 2 + 3 = 4 * (r ^ 2 + r + 1) := by ring
      have : (2 * r + 1) ^ 2 + 3 = 0 := by linarith [h4, hr]
      have hnn : (0 : ℚ) ≤ (2 * r + 1) ^ 2 := sq_nonneg _
      linarith
    exact False.elim (hdisc ⟨X, h⟩)

/--
**Affine residual** (phase 7m / 7u): the only rational points on
`X³ + 2Y³ = 1` are `(1, 0)` and `(-1, 1)`. Definitionally the Euler axiom.
-/
abbrev BealAffineCubeAddTwoResidual : Prop :=
  ∀ (X Y : ℚ), X ^ 3 + 2 * Y ^ 3 = 1 →
    (X = 1 ∧ Y = 0) ∨ (X = -1 ∧ Y = 1)

/--
**Diagnostic packaging** (phase 7o): only rational Weierstrass point on
`y² = x³ - 1728` is the 2-torsion `(12, 0)`. (Infinity corresponds to the
Affine point `(1, 0)`.) The cube leaf is closed by the Euler axiom on the
affine model, not by this packaging; mathlib has no rank for the curve.
-/
def BealMordellCubeAddTwoResidual : Prop :=
  ∀ (x y : ℚ), y ^ 2 = x ^ 3 - 1728 → x = 12 ∧ y = 0

/--
The Mordell residual implies the Affine residual via the birational map
`affineCubeAddTwoToMordell`.
-/
theorem BealAffineCubeAddTwoResidual_of_mordell
    (hMor : BealMordellCubeAddTwoResidual) :
    BealAffineCubeAddTwoResidual := by
  intro X Y heq
  by_cases hY : Y = 0
  · subst hY
    exact Or.inl ⟨eq_one_of_affine_cube_add_two_Y_zero heq, rfl⟩
  · by_cases hX : X = 1
    · subst hX
      have : 2 * Y ^ 3 = 0 := by simpa using heq
      have hY3 : Y ^ 3 = 0 := by linarith
      have : Y = 0 := (pow_eq_zero_iff (by decide : 3 ≠ 0)).1 hY3
      exact absurd this hY
    · have hlm := mordell_of_affine_cube_add_two heq hX
      obtain ⟨hx, hy⟩ := hMor _ _ hlm
      exact Or.inr (eq_neg_one_one_of_affine_to_mordell_twelve hX hx hy)

/--
The affine residual implies there are no positive integer solutions of
`α³ + 2β³ = γ³`.
-/
theorem BealPosCubeAddTwoCubeResidual_of_affine
    (hAff : BealAffineCubeAddTwoResidual) :
    BealPosCubeAddTwoCubeResidual := by
  intro α β γ hα0 hβ0 hγ0 heq
  have hγZ : (γ : ℚ) ≠ 0 := by exact_mod_cast (Nat.pos_iff_ne_zero.mp hγ0)
  have hrat : ((α : ℚ) / γ) ^ 3 + 2 * ((β : ℚ) / γ) ^ 3 = 1 := by
    field_simp [hγZ]
    exact_mod_cast heq
  rcases hAff (α / γ) (β / γ) hrat with ⟨_, hY⟩ | ⟨hX, _⟩
  · have : (β : ℚ) = 0 :=
      (div_eq_zero_iff.mp hY).resolve_right hγZ
    exact absurd (by exact_mod_cast this : β = 0) (Nat.pos_iff_ne_zero.mp hβ0)
  · have hneg : (α : ℚ) = -(γ : ℚ) := by
      field_simp [hγZ] at hX ⊢
      linarith [hX]
    have : (0 : ℚ) < α := by exact_mod_cast hα0
    have : (0 : ℚ) < γ := by exact_mod_cast hγ0
    linarith

/-- Mordell residual ⇒ positive-cube residual (via Affine). -/
theorem BealPosCubeAddTwoCubeResidual_of_mordell
    (hMor : BealMordellCubeAddTwoResidual) :
    BealPosCubeAddTwoCubeResidual :=
  BealPosCubeAddTwoCubeResidual_of_affine
    (BealAffineCubeAddTwoResidual_of_mordell hMor)

/-- Phase 7u: Euler axiom closes the positive-cube residual. -/
theorem BealPosCubeAddTwoCubeResidual_of_euler :
    BealPosCubeAddTwoCubeResidual :=
  BealPosCubeAddTwoCubeResidual_of_affine eulerAffineCubeAddTwo

/-- Phase 7u: no positive integers satisfy `α³ + 2β³ = γ³`. -/
theorem not_pos_cube_add_two_cube
    {α β γ : ℕ} (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ) :
    ¬ α ^ 3 + 2 * β ^ 3 = γ ^ 3 :=
  BealPosCubeAddTwoCubeResidual_of_euler α β γ hα hβ hγ

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

/-- Reducing `α³ + 2β³` modulo `n > 2` to the cube residues of `α` and `β`. -/
theorem cube_add_two_mod {n : ℕ} (hn : 2 < n) (α β : ℕ) :
    (α ^ 3 + 2 * β ^ 3) % n =
      (α ^ 3 % n + (2 * (β ^ 3 % n)) % n) % n := by
  have h2 : 2 % n = 2 := Nat.mod_eq_of_lt hn
  rw [Nat.add_mod, Nat.mul_mod, h2]

theorem nat_cube_mod_thirteen (v : ℕ) :
    v ^ 3 % 13 = 0 ∨ v ^ 3 % 13 = 1 ∨ v ^ 3 % 13 = 5 ∨
      v ^ 3 % 13 = 8 ∨ v ^ 3 % 13 = 12 := by
  have h : v % 13 = 0 ∨ v % 13 = 1 ∨ v % 13 = 2 ∨ v % 13 = 3 ∨
      v % 13 = 4 ∨ v % 13 = 5 ∨ v % 13 = 6 ∨ v % 13 = 7 ∨
      v % 13 = 8 ∨ v % 13 = 9 ∨ v % 13 = 10 ∨ v % 13 = 11 ∨
      v % 13 = 12 := by omega
  have hv : v ^ 3 % 13 = (v % 13) ^ 3 % 13 := by rw [← Nat.pow_mod]
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    <;> simp [hv, h]

theorem nat_cube_mod_nineteen (v : ℕ) :
    v ^ 3 % 19 = 0 ∨ v ^ 3 % 19 = 1 ∨ v ^ 3 % 19 = 7 ∨ v ^ 3 % 19 = 8 ∨
      v ^ 3 % 19 = 11 ∨ v ^ 3 % 19 = 12 ∨ v ^ 3 % 19 = 18 := by
  have h : v % 19 = 0 ∨ v % 19 = 1 ∨ v % 19 = 2 ∨ v % 19 = 3 ∨
      v % 19 = 4 ∨ v % 19 = 5 ∨ v % 19 = 6 ∨ v % 19 = 7 ∨
      v % 19 = 8 ∨ v % 19 = 9 ∨ v % 19 = 10 ∨ v % 19 = 11 ∨
      v % 19 = 12 ∨ v % 19 = 13 ∨ v % 19 = 14 ∨ v % 19 = 15 ∨
      v % 19 = 16 ∨ v % 19 = 17 ∨ v % 19 = 18 := by omega
  have hv : v ^ 3 % 19 = (v % 19) ^ 3 % 19 := by rw [← Nat.pow_mod]
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    <;> simp [hv, h]

/--
Cube residues of a positive solution modulo 7 occupy one of the five locally
admissible pairs. (The complementary pairs are cubes but the weighted sum is not.)
-/
theorem pos_cube_add_two_cube_mod_seven_classes
    {α β γ : ℕ} (heq : α ^ 3 + 2 * β ^ 3 = γ ^ 3) :
    α ^ 3 % 7 = 0 ∧ β ^ 3 % 7 = 0 ∨
      α ^ 3 % 7 = 1 ∧ β ^ 3 % 7 = 0 ∨
        α ^ 3 % 7 = 6 ∧ β ^ 3 % 7 = 0 ∨
          α ^ 3 % 7 = 6 ∧ β ^ 3 % 7 = 1 ∨
            α ^ 3 % 7 = 1 ∧ β ^ 3 % 7 = 6 := by
  have hα := nat_cube_mod_seven α
  have hβ := nat_cube_mod_seven β
  have hγ := nat_cube_mod_seven γ
  have hLHS : γ ^ 3 % 7 =
      (α ^ 3 % 7 + (2 * (β ^ 3 % 7)) % 7) % 7 := by
    rw [← heq, cube_add_two_mod (by decide)]
  rcases hα with hα | hα | hα
    <;> rcases hβ with hβ | hβ | hβ
    <;> simp [hα, hβ] at hLHS ⊢
    <;> omega

/-- Allowed cube-residue pairs modulo 9. -/
theorem pos_cube_add_two_cube_mod_nine_classes
    {α β γ : ℕ} (heq : α ^ 3 + 2 * β ^ 3 = γ ^ 3) :
    α ^ 3 % 9 = 0 ∧ β ^ 3 % 9 = 0 ∨
      α ^ 3 % 9 = 1 ∧ β ^ 3 % 9 = 0 ∨
        α ^ 3 % 9 = 8 ∧ β ^ 3 % 9 = 0 ∨
          α ^ 3 % 9 = 1 ∧ β ^ 3 % 9 = 8 ∨
            α ^ 3 % 9 = 8 ∧ β ^ 3 % 9 = 1 := by
  have hα := nat_cube_mod_nine α
  have hβ := nat_cube_mod_nine β
  have hγ := nat_cube_mod_nine γ
  have hLHS : γ ^ 3 % 9 =
      (α ^ 3 % 9 + (2 * (β ^ 3 % 9)) % 9) % 9 := by
    rw [← heq, cube_add_two_mod (by decide)]
  rcases hα with hα | hα | hα
    <;> rcases hβ with hβ | hβ | hβ
    <;> simp [hα, hβ] at hLHS ⊢
    <;> omega

/-- Allowed cube-residue pairs modulo 13. -/
theorem pos_cube_add_two_cube_mod_thirteen_classes
    {α β γ : ℕ} (heq : α ^ 3 + 2 * β ^ 3 = γ ^ 3) :
    α ^ 3 % 13 = 0 ∧ β ^ 3 % 13 = 0 ∨
      α ^ 3 % 13 = 1 ∧ β ^ 3 % 13 = 0 ∨
        α ^ 3 % 13 = 5 ∧ β ^ 3 % 13 = 0 ∨
          α ^ 3 % 13 = 8 ∧ β ^ 3 % 13 = 0 ∨
            α ^ 3 % 13 = 12 ∧ β ^ 3 % 13 = 0 ∨
              α ^ 3 % 13 = 12 ∧ β ^ 3 % 13 = 1 ∨
                α ^ 3 % 13 = 8 ∧ β ^ 3 % 13 = 5 ∨
                  α ^ 3 % 13 = 5 ∧ β ^ 3 % 13 = 8 ∨
                    α ^ 3 % 13 = 1 ∧ β ^ 3 % 13 = 12 := by
  have hα := nat_cube_mod_thirteen α
  have hβ := nat_cube_mod_thirteen β
  have hγ := nat_cube_mod_thirteen γ
  have hLHS : γ ^ 3 % 13 =
      (α ^ 3 % 13 + (2 * (β ^ 3 % 13)) % 13) % 13 := by
    rw [← heq, cube_add_two_mod (by decide)]
  rcases hα with hα | hα | hα | hα | hα
    <;> rcases hβ with hβ | hβ | hβ | hβ | hβ
    <;> simp [hα, hβ] at hLHS ⊢
    <;> omega

/-- Allowed cube-residue pairs modulo 19. -/
theorem pos_cube_add_two_cube_mod_nineteen_classes
    {α β γ : ℕ} (heq : α ^ 3 + 2 * β ^ 3 = γ ^ 3) :
    α ^ 3 % 19 = 0 ∧ β ^ 3 % 19 = 0 ∨
      α ^ 3 % 19 = 1 ∧ β ^ 3 % 19 = 0 ∨
        α ^ 3 % 19 = 7 ∧ β ^ 3 % 19 = 0 ∨
          α ^ 3 % 19 = 8 ∧ β ^ 3 % 19 = 0 ∨
            α ^ 3 % 19 = 11 ∧ β ^ 3 % 19 = 0 ∨
              α ^ 3 % 19 = 12 ∧ β ^ 3 % 19 = 0 ∨
                α ^ 3 % 19 = 18 ∧ β ^ 3 % 19 = 0 ∨
                  α ^ 3 % 19 = 18 ∧ β ^ 3 % 19 = 1 ∨
                    α ^ 3 % 19 = 12 ∧ β ^ 3 % 19 = 7 ∨
                      α ^ 3 % 19 = 11 ∧ β ^ 3 % 19 = 8 ∨
                        α ^ 3 % 19 = 8 ∧ β ^ 3 % 19 = 11 ∨
                          α ^ 3 % 19 = 7 ∧ β ^ 3 % 19 = 12 ∨
                            α ^ 3 % 19 = 1 ∧ β ^ 3 % 19 = 18 := by
  have hα := nat_cube_mod_nineteen α
  have hβ := nat_cube_mod_nineteen β
  have hγ := nat_cube_mod_nineteen γ
  have hLHS : γ ^ 3 % 19 =
      (α ^ 3 % 19 + (2 * (β ^ 3 % 19)) % 19) % 19 := by
    rw [← heq, cube_add_two_mod (by decide)]
  rcases hα with hα | hα | hα | hα | hα | hα | hα
    <;> rcases hβ with hβ | hβ | hβ | hβ | hβ | hβ | hβ
    <;> simp [hα, hβ] at hLHS ⊢
    <;> omega

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
**Residual** (phase 7m): equal-odd two-factor body for odd exponents `e ≥ 5`
with pure-power absolute value at least 3 (equivalently `1 < u`). The `|u| = 1`
branch is closed for all odd `e ≥ 3` by Mihăilescu.
-/
def BealEqualOddTwoFactorExpGeFiveResidual : Prop :=
  ∀ (m n : ℤ) (e : ℕ),
    5 ≤ e → Odd e →
    Int.gcd m n = 1 →
    ((Even m ∧ Odd n) ∨ (Odd m ∧ Even n)) →
    (∃ g : ℤ[i], Associated (g ^ e) (⟨m, n⟩ : ℤ[i])) →
    ((∃ u v : ℕ, 1 < u ∧ 0 < v ∧ n.natAbs = u ^ e ∧ 2 * m.natAbs = v ^ e) ∨
      (∃ u v : ℕ, 1 < u ∧ 0 < v ∧ m.natAbs = u ^ e ∧ 2 * n.natAbs = v ^ e)) →
    False

/-- Absolute value 1 on the pure-power slot is impossible for `e ≥ 3`. -/
theorem not_eq_odd_two_factor_abs_one_of_associated
    {m n : ℤ} {e v : ℕ}
    (he : 3 ≤ e) (hv0 : 0 < v)
    (hAssoc : ∃ g : ℤ[i], Associated (g ^ e) (⟨m, n⟩ : ℤ[i]))
    (hform :
      (n.natAbs = 1 ∧ 2 * m.natAbs = v ^ e) ∨
        (m.natAbs = 1 ∧ 2 * n.natAbs = v ^ e)) :
    False := by
  obtain ⟨g, hg⟩ := hAssoc
  have hIs := isGaussianHypotenusePower_of_associated_pow hg
  obtain ⟨c, heq⟩ := sum_sq_eq_natAbs_norm_pow_of_gaussian_hyp hIs
  rcases hform with ⟨hn1, hm⟩ | ⟨hm1, hn⟩
  · have hm0 : m ≠ 0 := by
      intro h; subst h
      have : v ^ e = 0 := by simpa using hm.symm
      exact Nat.pos_iff_ne_zero.mp hv0 (Nat.pow_eq_zero.mp this).1
    exact not_sum_sq_eq_pow_of_natAbs_one hm0 hn1 he heq
  · have hn0 : n ≠ 0 := by
      intro h; subst h
      have : v ^ e = 0 := by simpa using hn.symm
      exact Nat.pos_iff_ne_zero.mp hv0 (Nat.pow_eq_zero.mp this).1
    exact not_sum_sq_eq_pow_of_natAbs_one_left hn0 hm1 he heq

/--
Phase 7m assembly: positive-cube residual + narrowed `e ≥ 5` residual (with
`1 < u`) imply the full `BealEqualOddTwoFactorResidual`; `|u| = 1` is closed by
Mihăilescu for every odd `e ≥ 3`.
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
  · rcases hform with ⟨u, v, hu0, hv0, hn, hm⟩ | ⟨u, v, hu0, hv0, hm, hn⟩
    · by_cases hu1 : u = 1
      · subst hu1
        have hn1 : n.natAbs = 1 := by simpa using hn
        exact not_eq_odd_two_factor_abs_one_of_associated
          (Nat.le_trans (by decide : 3 ≤ 5) he5) hv0 hAssoc (Or.inl ⟨hn1, hm⟩)
      · have hu' : 1 < u := Nat.one_lt_iff_ne_zero_and_ne_one.2
          ⟨Nat.pos_iff_ne_zero.mp hu0, hu1⟩
        exact hGe5 m n e he5 hodd hcop hpar hAssoc
          (Or.inl ⟨u, v, hu', hv0, hn, hm⟩)
    · by_cases hu1 : u = 1
      · subst hu1
        have hm1 : m.natAbs = 1 := by simpa using hm
        exact not_eq_odd_two_factor_abs_one_of_associated
          (Nat.le_trans (by decide : 3 ≤ 5) he5) hv0 hAssoc (Or.inr ⟨hm1, hn⟩)
      · have hu' : 1 < u := Nat.one_lt_iff_ne_zero_and_ne_one.2
          ⟨Nat.pos_iff_ne_zero.mp hu0, hu1⟩
        exact hGe5 m n e he5 hodd hcop hpar hAssoc
          (Or.inr ⟨u, v, hu', hv0, hm, hn⟩)

/-- Phase 7u: equal-odd two-factor residual follows from the `e ≥ 5` leaf alone. -/
theorem BealEqualOddTwoFactorResidual_of_ge_five
    (hGe5 : BealEqualOddTwoFactorExpGeFiveResidual) :
    BealEqualOddTwoFactorResidual :=
  BealEqualOddTwoFactorResidual_of_pos_cube_and_ge_five
    BealPosCubeAddTwoCubeResidual_of_euler hGe5

end Theorems

end DstDiophantine
