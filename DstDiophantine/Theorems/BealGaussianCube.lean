import DstDiophantine.Theorems.BealGaussian
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
* mod-7 / mod-9 diagnostic slices for that equation;
* split assembly `e = 3` vs `e ≥ 5`;
* phase 7m: primitivity / parity / difference-factor / 2-adic packaging for
  `α³ + 2β³ = γ³`, and assembly from the affine residual `X³ + 2Y³ = 1`;
* phase 7o: birational packaging of that Affine curve onto the Mordell model
  `y² = x³ - 1728`, with assembly `BealMordellCubeAddTwoResidual → Affine`.

The positive cube equation `α³ + 2β³ = γ³` is the live residual for `e = 3`
(no new axiom; classical Beal is **not** claimed unconditionally). The naive
2-adic descent used for `x³ + 2y³ = 4z³` does **not** apply here (signed
solutions such as `(-1)³ + 2·1³ = 1³` exist). The Mordell rank is not in
mathlib; phase 7o does **not** close it.
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
**Residual** (phase 7l, unproved): no positive integers satisfy
`α³ + 2β³ = γ³`. (Signed solutions exist, e.g. `(-1)³ + 2·1³ = 1³`; the Beal
two-factor reduction only produces positive `α = u²`.)
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
  have heqN : γ ^ 2 + γ * α + α ^ 2 =
      (γ - α) * (γ + 2 * α) + 3 * α ^ 2 := by
    apply Int.ofNat_inj.mp
    have hγa : ((γ - α : ℕ) : ℤ) = (γ : ℤ) - α := Nat.cast_sub hle
    calc ((γ ^ 2 + γ * α + α ^ 2 : ℕ) : ℤ)
        = (γ : ℤ) ^ 2 + γ * α + α ^ 2 := by push_cast; ring
      _ = ((γ : ℤ) - α) * ((γ : ℤ) + 2 * α) + 3 * α ^ 2 := by ring
      _ = (((γ - α : ℕ) : ℤ) * ((γ + 2 * α : ℕ) : ℤ) + (3 * α ^ 2 : ℕ)) := by
            rw [hγa]; push_cast; ring
      _ = ((γ - α) * (γ + 2 * α) + 3 * α ^ 2 : ℕ) := by simp
  have hrew : Nat.gcd (γ - α) (γ ^ 2 + γ * α + α ^ 2) =
      Nat.gcd (γ - α) (3 * α ^ 2) := by
    rw [heqN, Nat.gcd_mul_left_add_right]
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
**Residual** (phase 7m, unproved): the only rational points on
`X³ + 2Y³ = 1` are `(1, 0)` and `(-1, 1)`.
-/
def BealAffineCubeAddTwoResidual : Prop :=
  ∀ (X Y : ℚ), X ^ 3 + 2 * Y ^ 3 = 1 →
    (X = 1 ∧ Y = 0) ∨ (X = -1 ∧ Y = 1)

/--
**Residual** (phase 7o, unproved): the only rational point on the Mordell curve
`y² = x³ - 1728` is the 2-torsion point `(12, 0)`.
(The point at infinity corresponds to the Affine point `(1, 0)` under the
birational map above; it is not an affine Weierstrass point.)
mathlib does not contain the rank of this curve; this is **not** a Lean proof
of Selmer's theorem.
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

end Theorems

end DstDiophantine
