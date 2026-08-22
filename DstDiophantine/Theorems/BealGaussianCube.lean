import DstDiophantine.Theorems.BealGaussian
import DstDiophantine.Theorems.Mihailescu
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Phase 7k: equal-odd two-factor cube slice (`e = 3`)

Infrastructure and closed branches for `BealEqualOddTwoFactorResidual` at
exponent 3:

* Gaussian cube expansion `(a+bi)³`;
* mod-8 obstruction when the factor `2` sits on an odd coordinate;
* Mihăilescu when the pure-cube coordinate has absolute value `1`.

The general `e = 3` residual body (odd cube coordinate `≥ 3`) remains open.
Classical Beal is **not** claimed unconditionally.
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

end Theorems

end DstDiophantine
