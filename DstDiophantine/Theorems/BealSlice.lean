import DstDiophantine.Theorems.Beal
import Mathlib.NumberTheory.FLT.Three
import Mathlib.NumberTheory.FLT.Four

/-!
# Phase 7g: unconditional Beal slices from mathlib FLT n = 3, 4

Isolated from `Beal.lean` so that the cyclotomic import for
`fermatLastTheoremThree` does not weigh down the diagnostic / CGA layer.

## What is closed here (no hypotheses)

* `3 ∣ bealExpGcd` or `4 ∣ bealExpGcd` — via `fermatLastTheoremThree` /
  `fermatLastTheoremFour` and `FermatLastTheoremFor.mono`;
* equal exponents `p = 3` and `p = 4`;
* `bealExpGcd = 2` with `4 ∣ x` and `4 ∣ y` — via `not_fermat_42`.

## What remains residual

* general `d ≥ 3` not divisible by 3 or 4 (needs full `FermatLastTheorem`);
* general `d = 2` Pythagorean powers beyond the biquadratic slice;
* `d = 1` mixed exponents (`BealMixedExpResidual`).

Classical Beal is **not** claimed unconditionally.
-/

namespace DstDiophantine

namespace Theorems

/-! ### FLT-for transfer along divisor of the exponent gcd -/

/--
If mathlib's `FermatLastTheoremFor n` holds with `n ≥ 3` and `n` divides the
Beal exponent gcd, there is no nonzero Beal solution.
-/
theorem not_beal_sol_of_expGcd_dvd_FLT_for
    {n : ℕ} (hnFLT : FermatLastTheoremFor n) (hn3 : 3 ≤ n)
    {A B C : ℤ} {x y z : ℕ}
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hdvd : n ∣ bealExpGcd x y z) :
    ¬ A ^ x + B ^ y = C ^ z := by
  intro hsol
  obtain ⟨k, hk⟩ := hdvd
  have hkpos : 0 < k := by
    refine Nat.pos_of_ne_zero fun hk0 => ?_
    have := (beal_eq_pow_mul_expGcd A B C x y z).mp hsol
    simp [hk, hk0] at this
  -- Hence `bealExpGcd = n * k ≥ n ≥ 3`.
  have _hge : 3 ≤ bealExpGcd x y z := by
    calc 3 ≤ n := hn3
      _ ≤ n * k := Nat.le_mul_of_pos_right n hkpos
      _ = bealExpGcd x y z := hk.symm
  obtain ⟨hα, hβ, hγ, hF⟩ := beal_fermat_of_expGcd_ge_three hA hB hC hsol
  have hFor : FermatLastTheoremFor (bealExpGcd x y z) :=
    FermatLastTheoremFor.mono ⟨k, hk⟩ hnFLT
  exact (fermatLastTheoremFor_iff_int).mp hFor _ _ _ hα hβ hγ hF

/-- Unconditional: no nonzero Beal solution when `3 ∣ bealExpGcd`. -/
theorem not_beal_sol_of_three_dvd_expGcd {A B C : ℤ} {x y z : ℕ}
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hdvd : 3 ∣ bealExpGcd x y z) :
    ¬ A ^ x + B ^ y = C ^ z :=
  not_beal_sol_of_expGcd_dvd_FLT_for fermatLastTheoremThree (by decide)
    hA hB hC hdvd

/-- Unconditional: no nonzero Beal solution when `4 ∣ bealExpGcd`. -/
theorem not_beal_sol_of_four_dvd_expGcd {A B C : ℤ} {x y z : ℕ}
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hdvd : 4 ∣ bealExpGcd x y z) :
    ¬ A ^ x + B ^ y = C ^ z :=
  not_beal_sol_of_expGcd_dvd_FLT_for fermatLastTheoremFour (by decide)
    hA hB hC hdvd

/-- Unconditional: no nonzero Beal solution when `3 ∣ d` or `4 ∣ d`. -/
theorem not_beal_sol_of_three_or_four_dvd_expGcd {A B C : ℤ} {x y z : ℕ}
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hdvd : 3 ∣ bealExpGcd x y z ∨ 4 ∣ bealExpGcd x y z) :
    ¬ A ^ x + B ^ y = C ^ z :=
  hdvd.elim (not_beal_sol_of_three_dvd_expGcd hA hB hC)
    (not_beal_sol_of_four_dvd_expGcd hA hB hC)

/-- Unconditional equal-exponent slice `p = 3`. -/
theorem not_beal_eq_exp_three {A B C : ℤ}
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0) :
    ¬ A ^ 3 + B ^ 3 = C ^ 3 :=
  not_beal_sol_of_three_dvd_expGcd hA hB hC (by simp [bealExpGcd_eq_of_eq_exp])

/-- Unconditional equal-exponent slice `p = 4`. -/
theorem not_beal_eq_exp_four {A B C : ℤ}
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0) :
    ¬ A ^ 4 + B ^ 4 = C ^ 4 :=
  not_beal_sol_of_four_dvd_expGcd hA hB hC (by simp [bealExpGcd_eq_of_eq_exp])

/-! ### Biquadratic Pythagorean slice (`d = 2`, `4 ∣ x`, `4 ∣ y`) -/

/--
When `bealExpGcd = 2` and both `x, y` are divisible by 4, a nonzero solution
would yield `a⁴ + b⁴ = c²`, forbidden by mathlib's `not_fermat_42`.
-/
theorem not_beal_sol_of_expGcd_eq_two_of_four_dvd_xy {A B C : ℤ} {x y z : ℕ}
    (hx : 3 ≤ x) (hy : 3 ≤ y) (hz : 3 ≤ z)
    (hA : A ≠ 0) (hB : B ≠ 0) (_hC : C ≠ 0)
    (hd : bealExpGcd x y z = 2)
    (hx4 : 4 ∣ x) (hy4 : 4 ∣ y) :
    ¬ A ^ x + B ^ y = C ^ z := by
  intro hsol
  obtain ⟨_, _, _, hsq⟩ :=
    beal_pythagorean_of_expGcd_eq_two hx hy hz hd hsol
  have hx_eq : x / 2 = 2 * (x / 4) := by omega
  have hy_eq : y / 2 = 2 * (y / 4) := by omega
  have hA4 : A ^ (x / 2) = (A ^ (x / 4)) ^ 2 := by
    rw [hx_eq, mul_comm, pow_mul]
  have hB4 : B ^ (y / 2) = (B ^ (y / 4)) ^ 2 := by
    rw [hy_eq, mul_comm, pow_mul]
  have hform : (A ^ (x / 4)) ^ 4 + (B ^ (y / 4)) ^ 4 = (C ^ (z / 2)) ^ 2 := by
    have hA' : (A ^ (x / 2)) ^ 2 = (A ^ (x / 4)) ^ 4 := by
      rw [hA4, ← pow_mul]
    have hB' : (B ^ (y / 2)) ^ 2 = (B ^ (y / 4)) ^ 4 := by
      rw [hB4, ← pow_mul]
    rw [← hA', ← hB', hsq]
  exact not_fermat_42 (pow_ne_zero _ hA) (pow_ne_zero _ hB) hform

end Theorems

end DstDiophantine
