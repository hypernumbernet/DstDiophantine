/-
Copyright (c) 2026 DstDiophantine contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DstDiophantine contributors
-/
import DstDiophantine.Algebra.Operations
import DstDiophantine.Algebra.PGA.Normed
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum

/-!
# Chiral / spinor projectors inside `G(3,1,1)`

The paper draft writes `P_L = (1 - i)/2` with the Cl(3,1) pseudoscalar `i`
satisfying `i² = -1`. That formula is **not** idempotent (proved below).
Working projectors use generators that square to `+1`:

* spatial `e₁` (`ι 1`) for a complementary pair `chiralityL` / `chiralityR`;
* hyperbolic `e₀e₁` for `spinorIdem`.

Irreducibility of the left ideal is deferred.
-/

namespace DstDiophantine

namespace Logic

open PGA Operations Generators CliffordAlgebra

noncomputable def half : PGA :=
  algebraMap ℝ PGA (1 / 2)

theorem half_mul_half : half * half = algebraMap ℝ PGA (1 / 4) := by
  unfold half; rw [← map_mul]; norm_num

theorem two_mul_half : algebraMap ℝ PGA 2 * half = 1 := by
  unfold half; rw [← map_mul, ← map_one (algebraMap ℝ PGA)]; norm_num

theorem two_mul_quarter : algebraMap ℝ PGA 2 * algebraMap ℝ PGA (1 / 4) = half := by
  unfold half; rw [← map_mul]; norm_num

theorem half_comm (x : PGA) : half * x = x * half :=
  Algebra.commutes (1 / 2 : ℝ) x

theorem map_two_comm (x : PGA) :
    algebraMap ℝ PGA 2 * x = x * algebraMap ℝ PGA 2 :=
  Algebra.commutes (2 : ℝ) x

theorem one_add_one_eq_map_two : (1 + 1 : PGA) = algebraMap ℝ PGA 2 := by
  calc (1 + 1 : PGA)
      = algebraMap ℝ PGA 1 + algebraMap ℝ PGA 1 := by simp [Algebra.algebraMap_eq_smul_one]
    _ = algebraMap ℝ PGA (1 + 1) := (map_add _ _ _).symm
    _ = algebraMap ℝ PGA 2 := by norm_num

theorem add_self_eq_map_two_mul (g : PGA) :
    g + g = algebraMap ℝ PGA 2 * g := by
  calc g + g = (1 + 1 : PGA) * g := by noncomm_ring
    _ = algebraMap ℝ PGA 2 * g := by rw [one_add_one_eq_map_two]

theorem mul_half_mul_half (a b : PGA) :
    a * half * (b * half) = a * b * (half * half) := by
  calc a * half * (b * half)
      = a * (half * b) * half := by noncomm_ring
    _ = a * (b * half) * half := by rw [half_comm]
    _ = a * b * (half * half) := by noncomm_ring

/-- If `a² = 2a`, then `(a/2)² = a/2`. -/
theorem idempotent_half {a : PGA}
    (ha : a * a = algebraMap ℝ PGA 2 * a) :
    a * half * (a * half) = a * half := by
  calc a * half * (a * half)
      = a * a * (half * half) := mul_half_mul_half _ _
    _ = (algebraMap ℝ PGA 2 * a) * algebraMap ℝ PGA (1 / 4) := by
        rw [ha, half_mul_half]
    _ = a * (algebraMap ℝ PGA 2 * algebraMap ℝ PGA (1 / 4)) := by
        rw [map_two_comm, mul_assoc]
    _ = a * half := by rw [two_mul_quarter]

theorem sq_one_expand_add {g : PGA} (hg : g * g = 1) :
    ((1 : PGA) + g) * ((1 : PGA) + g) = algebraMap ℝ PGA 2 * ((1 : PGA) + g) := by
  calc ((1 : PGA) + g) * ((1 : PGA) + g)
      = 1 + g + g + g * g := by noncomm_ring
    _ = 1 + g + g + 1 := by rw [hg]
    _ = (1 + 1) + (g + g) := by abel
    _ = algebraMap ℝ PGA 2 + algebraMap ℝ PGA 2 * g := by
        rw [one_add_one_eq_map_two, add_self_eq_map_two_mul]
    _ = algebraMap ℝ PGA 2 * ((1 : PGA) + g) := by noncomm_ring

theorem sq_one_expand_sub {g : PGA} (hg : g * g = 1) :
    ((1 : PGA) - g) * ((1 : PGA) - g) = algebraMap ℝ PGA 2 * ((1 : PGA) - g) := by
  calc ((1 : PGA) - g) * ((1 : PGA) - g)
      = 1 - g - g + g * g := by noncomm_ring
    _ = 1 - g - g + 1 := by rw [hg]
    _ = (1 + 1) - (g + g) := by abel
    _ = algebraMap ℝ PGA 2 - algebraMap ℝ PGA 2 * g := by
        rw [one_add_one_eq_map_two, add_self_eq_map_two_mul]
    _ = algebraMap ℝ PGA 2 * ((1 : PGA) - g) := by noncomm_ring

theorem idempotent_of_sq_one {g : PGA} (hg : g * g = 1) :
    ((1 : PGA) + g) * half * (((1 : PGA) + g) * half) = ((1 : PGA) + g) * half :=
  idempotent_half (sq_one_expand_add hg)

theorem idempotent_of_sq_one_sub {g : PGA} (hg : g * g = 1) :
    ((1 : PGA) - g) * half * (((1 : PGA) - g) * half) = ((1 : PGA) - g) * half :=
  idempotent_half (sq_one_expand_sub hg)

/-- Paper draft formula `(1 - i)/2`. -/
noncomputable def paperChiralityL : PGA :=
  ((1 : PGA) - pseudoscalar) * half

/-- Paper draft formula `(1 + i)/2`. -/
noncomputable def paperChiralityR : PGA :=
  ((1 : PGA) + pseudoscalar) * half

noncomputable def chiralityGen : PGA := ι 1

theorem chiralityGen_sq : chiralityGen * chiralityGen = 1 := e1_sq

noncomputable def chiralityL : PGA := ((1 : PGA) - chiralityGen) * half
noncomputable def chiralityR : PGA := ((1 : PGA) + chiralityGen) * half
noncomputable def spinorIdem : PGA := ((1 : PGA) + hyperbolic 0) * half

/-- With `i² = -1`, `((1 - i)/2)² = -i/2`. -/
theorem paperChiralityL_sq_eq :
    paperChiralityL * paperChiralityL = (-pseudoscalar) * half := by
  unfold paperChiralityL
  have hexp :
      ((1 : PGA) - pseudoscalar) * ((1 : PGA) - pseudoscalar) =
        -(algebraMap ℝ PGA 2 * pseudoscalar) := by
    calc ((1 : PGA) - pseudoscalar) * ((1 : PGA) - pseudoscalar)
        = 1 - pseudoscalar - pseudoscalar + (pseudoscalar * pseudoscalar) := by
          noncomm_ring
      _ = 1 - pseudoscalar - pseudoscalar + (-1 : PGA) := by rw [pseudoscalar_sq]
      _ = -(pseudoscalar + pseudoscalar) := by abel
      _ = -(algebraMap ℝ PGA 2 * pseudoscalar) := by rw [add_self_eq_map_two_mul]
  calc ((1 : PGA) - pseudoscalar) * half * (((1 : PGA) - pseudoscalar) * half)
      = ((1 : PGA) - pseudoscalar) * ((1 : PGA) - pseudoscalar) * (half * half) :=
        mul_half_mul_half _ _
    _ = (-(algebraMap ℝ PGA 2 * pseudoscalar)) * algebraMap ℝ PGA (1 / 4) := by
        rw [hexp, half_mul_half]
    _ = (-pseudoscalar) * (algebraMap ℝ PGA 2 * algebraMap ℝ PGA (1 / 4)) := by
        rw [map_two_comm pseudoscalar]; noncomm_ring
    _ = (-pseudoscalar) * half := by rw [two_mul_quarter]

private theorem half_ne_zero : half ≠ 0 := by
  intro h
  have : (1 / 2 : ℝ) = 0 :=
    (FaithfulSMul.algebraMap_eq_zero_iff (R := ℝ) (A := PGA)).mp h
  norm_num at this

theorem paperChiralityL_not_idempotent :
    paperChiralityL * paperChiralityL ≠ paperChiralityL := by
  intro h
  have hexp := paperChiralityL_sq_eq
  rw [h] at hexp
  have heq :
      ((1 : PGA) - pseudoscalar) * half = (-pseudoscalar) * half := by
    simpa [paperChiralityL] using hexp
  have hexpand :
      ((1 : PGA) - pseudoscalar) * half + pseudoscalar * half = half := by
    simp [sub_mul, one_mul]
  have : half = 0 := by
    calc half
        = ((1 : PGA) - pseudoscalar) * half + pseudoscalar * half := hexpand.symm
      _ = (-pseudoscalar) * half + pseudoscalar * half := by rw [heq]
      _ = (-pseudoscalar + pseudoscalar) * half := by rw [← add_mul]
      _ = 0 := by simp [neg_add_cancel, zero_mul]
  exact half_ne_zero this

theorem chiralityL_sq : chiralityL * chiralityL = chiralityL :=
  idempotent_of_sq_one_sub chiralityGen_sq

theorem chiralityR_sq : chiralityR * chiralityR = chiralityR :=
  idempotent_of_sq_one chiralityGen_sq

theorem chiralityL_add_chiralityR : chiralityL + chiralityR = 1 := by
  unfold chiralityL chiralityR
  have h :
      ((1 : PGA) - chiralityGen) * half + ((1 : PGA) + chiralityGen) * half =
        half + half := by
    simp [sub_mul, add_mul, one_mul]
  rw [h, add_self_eq_map_two_mul, two_mul_half]

theorem spinorIdem_sq : spinorIdem * spinorIdem = spinorIdem :=
  idempotent_of_sq_one (hyperbolic_sq 0)

end Logic

end DstDiophantine
