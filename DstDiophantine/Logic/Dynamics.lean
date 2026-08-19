/-
Copyright (c) 2026 DstDiophantine contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DstDiophantine contributors
-/
import DstDiophantine.Logic.Amplitude
import DstDiophantine.Algebra.Amplification
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# Amplification as a D4L dynamics

Pure-boost scaling multiplies `JNormalized` by `k²`. On labels this is a
partial map: `T` is fixed, `U` can be driven to `F` or out of the
admissible cone (`classify? = none`). The shared no-go is that reading —
no new arithmetic.

Does not import `Theorems`.
-/

namespace DstDiophantine

namespace Logic

open Admissible Amplification Invariant

theorem measure_scale (k : ℕ) (a : Amplitude)
    (h : IsAdmissibleContinuous (scaleTorsion (k : ℝ) a.params)) :
    Amplitude.measure ⟨scaleTorsion (k : ℝ) a.params, h⟩ =
      (k : ℝ) ^ 2 * a.measure := by
  simp [Amplitude.measure, JNormalized_scale]

/-- Synchrony is a fixed point of every admissible scaling. -/
theorem scale_T_stays_T {k : ℕ} {a : Amplitude} (ha : a.collapse = .T)
    (h : IsAdmissibleContinuous (scaleTorsion (k : ℝ) a.params)) :
    (⟨scaleTorsion (k : ℝ) a.params, h⟩ : Amplitude).collapse = .T := by
  have h0 : a.measure = 0 := a.measure_eq_zero_iff.mpr ha
  have hm := measure_scale k a h
  have : (⟨scaleTorsion (k : ℝ) a.params, h⟩ : Amplitude).measure = 0 := by
    simp [hm, h0]
  exact (Amplitude.measure_eq_zero_iff _).mp this

/-- A `U` seed whose `k`-fold image is the wall `F`. -/
noncomputable def seedU_to_F {k : ℕ} (hk : 2 ≤ k) : Amplitude :=
  ⟨pureHyperbolicRay (1 / (k : ℝ)), by
    have hk0 : 0 ≤ (1 : ℝ) / k := by positivity
    have hk1 : (1 : ℝ) / k ≤ 1 := by
      have : (1 : ℝ) ≤ k := Nat.one_le_cast.mpr (Nat.le_trans (by decide : 1 ≤ 2) hk)
      exact (div_le_one (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) this)).mpr this
    exact isAdmissibleContinuous_pureHyperbolicRay hk0 hk1⟩

theorem seedU_to_F_is_U {k : ℕ} (hk : 2 ≤ k) : (seedU_to_F hk).collapse = .U := by
  have hkpos : 0 < (k : ℝ) :=
    Nat.cast_pos.mpr (Nat.succ_le_iff.mp (Nat.le_trans (by decide : 1 ≤ 2) hk))
  have hJ : (seedU_to_F hk).measure = (1 / (k : ℝ)) ^ 2 := by
    simp [seedU_to_F, Amplitude.measure, JNormalized_pureHyperbolicRay]
  have h0 : 0 < (seedU_to_F hk).measure := by
    rw [hJ]; positivity
  have h1 : (seedU_to_F hk).measure < 1 := by
    rw [hJ]
    have hk2 : (2 : ℝ) ≤ k := Nat.cast_le.mpr hk
    have hle : (1 : ℝ) / k ≤ 1 / 2 :=
      one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hk2
    have hsq : ((1 : ℝ) / k) ^ 2 ≤ (1 / 2 : ℝ) ^ 2 :=
      pow_le_pow_left₀ (div_nonneg (by norm_num) hkpos.le) hle 2
    have h14 : (1 / 2 : ℝ) ^ 2 = 1 / 4 := by norm_num
    linarith
  exact (ofParams_eq_U_iff (seedU_to_F hk).admissible).mpr ⟨h0, h1⟩

theorem seedU_to_F_scale_admissible {k : ℕ} (hk : 2 ≤ k) :
    IsAdmissibleContinuous (scaleTorsion (k : ℝ) (seedU_to_F hk).params) := by
  intro a
  have hkpos : (k : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr
      (ne_of_gt (Nat.succ_le_iff.mp (Nat.le_trans (by decide : 1 ≤ 2) hk)))
  have hα :
      (scaleTorsion (k : ℝ) (seedU_to_F hk).params).alpha a = Real.pi / 2 := by
    simp [scaleTorsion, seedU_to_F, pureHyperbolicRay]
    field_simp [hkpos]
  have hβ : (scaleTorsion (k : ℝ) (seedU_to_F hk).params).beta a = 0 := by
    simp [scaleTorsion, seedU_to_F, pureHyperbolicRay]
  have hπ : (0 : ℝ) ≤ Real.pi / 2 := by positivity
  refine ⟨by simp [hα, hπ], by simp [hβ], ?_⟩
  simp [hα, hβ]

theorem seedU_to_F_scales_to_F {k : ℕ} (hk : 2 ≤ k) :
    (⟨scaleTorsion (k : ℝ) (seedU_to_F hk).params,
        seedU_to_F_scale_admissible hk⟩ : Amplitude).collapse = .F := by
  have hm := measure_scale k (seedU_to_F hk) (seedU_to_F_scale_admissible hk)
  have hJ : (seedU_to_F hk).measure = (1 / (k : ℝ)) ^ 2 := by
    simp [seedU_to_F, Amplitude.measure, JNormalized_pureHyperbolicRay]
  have : (⟨scaleTorsion (k : ℝ) (seedU_to_F hk).params,
      seedU_to_F_scale_admissible hk⟩ : Amplitude).measure = 1 := by
    have hkpos : (k : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (ne_of_gt (Nat.succ_le_iff.mp (Nat.le_trans (by decide : 1 ≤ 2) hk)))
    rw [hm, hJ]
    field_simp [hkpos]
  exact (Amplitude.measure_eq_one_iff _).mp this

/-- A `U` seed driven out of the admissible cone (`classify? = none`). -/
noncomputable def seedU_exits : Amplitude :=
  ⟨pureHyperbolicRay (Real.sqrt (1 / 2)), by
    refine isAdmissibleContinuous_pureHyperbolicRay (Real.sqrt_nonneg _) ?_
    exact (Real.sqrt_le_one).2 (by norm_num)⟩

theorem seedU_exits_is_U : seedU_exits.collapse = .U := by
  have hJ : JNormalized seedU_exits.params = 1 / 2 := by
    unfold seedU_exits
    rw [JNormalized_pureHyperbolicRay, Real.sq_sqrt (by norm_num)]
  exact (ofParams_eq_U_iff seedU_exits.admissible).mpr (by constructor <;> linarith [hJ])

theorem seedU_exits_not_admissible :
    ¬ IsAdmissibleContinuous (scaleTorsion (2 : ℝ) seedU_exits.params) := by
  intro h
  have hbound := torsion_bound_continuous _ h
  have hJ : JNormalized (scaleTorsion (2 : ℝ) seedU_exits.params) = 2 := by
    rw [JNormalized_scale]
    unfold seedU_exits
    rw [JNormalized_pureHyperbolicRay, Real.sq_sqrt (by norm_num)]
    norm_num
  rw [hJ] at hbound
  norm_num at hbound

theorem seedU_exits_unclassified :
    classify? (JNormalized (scaleTorsion (2 : ℝ) seedU_exits.params)) = none := by
  have hJ : JNormalized (scaleTorsion (2 : ℝ) seedU_exits.params) = 2 := by
    rw [JNormalized_scale]
    unfold seedU_exits
    rw [JNormalized_pureHyperbolicRay, Real.sq_sqrt (by norm_num)]
    norm_num
  simp [classify?, hJ]

end Logic

end DstDiophantine
