/-
Copyright (c) 2026 DstDiophantine contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DstDiophantine contributors
-/
import DstDiophantine.Algebra.Amplification
import DstDiophantine.Algebra.Admissible
import DstDiophantine.Algebra.Motor
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Dual-axis Fermat motor embedding

Separates the FLT multiplicative seed from the single-axis hyperbolic
`integerRotor` (axis 0 only). For a projective triple `[a:b:c]` with
`a, b, c ≠ 0`:

* boost rapidity `α = log(√(a²+b²)/|c|)` on hyperbolic axis 0;
* cyclic angle `β = arctan(|b|/|a|)` on cyclic axis 1.

Does **not** claim that mixed `R·T` equals `exp(Ω_biv)`. Unconditional FLT
is not claimed.
-/

namespace DstDiophantine

namespace Embedding

open Operations Amplification Admissible Motor Real

/-- Euclidean radius `√(a² + b²)` of the integer pair `(a, b)`. -/
noncomputable def fermatL2 (a b : ℤ) : ℝ :=
  Real.sqrt ((a.natAbs : ℝ) ^ 2 + (b.natAbs : ℝ) ^ 2)

/-- Radius boost: `α = log(√(a²+b²) / |c|)`. -/
noncomputable def fermatBoost (a b c : ℤ) (_hc : c ≠ 0) : ℝ :=
  Real.log (fermatL2 a b / (c.natAbs : ℝ))

/-- Direction angle: `β = arctan(|b|/|a|)` (requires `a ≠ 0`). -/
noncomputable def fermatAngle (a b : ℤ) (_ha : a ≠ 0) : ℝ :=
  Real.arctan ((b.natAbs : ℝ) / (a.natAbs : ℝ))

/--
Dual-axis torsion seed: hyperbolic on axis `0`, cyclic on axis `1`.
-/
noncomputable def fermatTorsion (a b c : ℤ) (ha : a ≠ 0) (hc : c ≠ 0) :
    TorsionParams where
  alpha := fun i => if i = 0 then fermatBoost a b c hc else 0
  beta := fun i => if i = 1 then fermatAngle a b ha else 0

/-- Dual-axis Fermat motor rotor `R = exp(Ω)` of the torsion seed. -/
noncomputable def fermatMotorRotor (a b c : ℤ) (ha : a ≠ 0) (hc : c ≠ 0) : PGA :=
  rotorTorsion (fermatTorsion a b c ha hc)

/-- Mixed seat: positive boost and interior cyclic angle. -/
def IsMixedFermatMotor (a b c : ℤ) (ha : a ≠ 0) (hc : c ≠ 0) : Prop :=
  0 < fermatBoost a b c hc ∧
    0 < fermatAngle a b ha ∧ fermatAngle a b ha < Real.pi / 2

/-- Pure cyclic seat: vanishing boost (Pythagorean radius). -/
def IsPureCyclicFermatMotor (a b c : ℤ) (hc : c ≠ 0) : Prop :=
  fermatBoost a b c hc = 0

theorem fermatL2_pos {a b : ℤ} (h : a ≠ 0 ∨ b ≠ 0) : 0 < fermatL2 a b := by
  unfold fermatL2
  refine Real.sqrt_pos.mpr ?_
  cases h with
  | inl ha =>
    have : 0 < (a.natAbs : ℝ) ^ 2 :=
      sq_pos_of_pos (Nat.cast_pos.mpr (Int.natAbs_pos.mpr ha))
    linarith [sq_nonneg (b.natAbs : ℝ)]
  | inr hb =>
    have : 0 < (b.natAbs : ℝ) ^ 2 :=
      sq_pos_of_pos (Nat.cast_pos.mpr (Int.natAbs_pos.mpr hb))
    linarith [sq_nonneg (a.natAbs : ℝ)]

theorem fermatL2_nonneg (a b : ℤ) : 0 ≤ fermatL2 a b :=
  Real.sqrt_nonneg _

theorem fermatAngle_nonneg (a b : ℤ) (ha : a ≠ 0) : 0 ≤ fermatAngle a b ha := by
  unfold fermatAngle
  exact Real.arctan_nonneg.mpr (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))

theorem fermatAngle_lt_half_pi (a b : ℤ) (ha : a ≠ 0) :
    fermatAngle a b ha < Real.pi / 2 := by
  unfold fermatAngle
  exact Real.arctan_lt_pi_div_two _

theorem fermatAngle_pos_of_b_ne {a b : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) :
    0 < fermatAngle a b ha := by
  unfold fermatAngle
  refine Real.arctan_pos.mpr ?_
  exact div_pos (Nat.cast_pos.mpr (Int.natAbs_pos.mpr hb))
    (Nat.cast_pos.mpr (Int.natAbs_pos.mpr ha))

theorem fermatBoost_eq_zero_iff {a b c : ℤ} (hc : c ≠ 0)
    (hab : a ≠ 0 ∨ b ≠ 0) :
    fermatBoost a b c hc = 0 ↔ fermatL2 a b = (c.natAbs : ℝ) := by
  unfold fermatBoost
  have hL : 0 < fermatL2 a b := fermatL2_pos hab
  have hc0 : (0 : ℝ) < c.natAbs :=
    Nat.cast_pos.mpr (Int.natAbs_pos.mpr hc)
  have harg : 0 < fermatL2 a b / (c.natAbs : ℝ) := div_pos hL hc0
  constructor
  · intro h
    have hexp : Real.exp (Real.log (fermatL2 a b / (c.natAbs : ℝ))) = Real.exp 0 := by
      rw [h]
    rw [Real.exp_log harg, Real.exp_zero] at hexp
    exact (div_eq_one_iff_eq (ne_of_gt hc0)).mp hexp
  · intro h
    rw [h, div_self (ne_of_gt hc0), Real.log_one]

theorem fermatBoost_eq_zero_iff_sq {a b c : ℤ} (hc : c ≠ 0)
    (hab : a ≠ 0 ∨ b ≠ 0) :
    fermatBoost a b c hc = 0 ↔
      (a.natAbs : ℝ) ^ 2 + (b.natAbs : ℝ) ^ 2 = (c.natAbs : ℝ) ^ 2 := by
  rw [fermatBoost_eq_zero_iff hc hab]
  unfold fermatL2
  constructor
  · intro h
    have hnn : 0 ≤ (a.natAbs : ℝ) ^ 2 + (b.natAbs : ℝ) ^ 2 :=
      add_nonneg (sq_nonneg _) (sq_nonneg _)
    have hsq := congrArg (fun x : ℝ => x ^ 2) h
    rwa [Real.sq_sqrt hnn] at hsq
  · intro h
    refine (Real.sqrt_eq_iff_eq_sq
      (add_nonneg (sq_nonneg _) (sq_nonneg _))
      (Nat.cast_nonneg _)).mpr ?_
    exact h

theorem isPureCyclic_iff_pythagorean {a b c : ℤ} (hc : c ≠ 0)
    (hab : a ≠ 0 ∨ b ≠ 0) :
    IsPureCyclicFermatMotor a b c hc ↔
      (a.natAbs : ℝ) ^ 2 + (b.natAbs : ℝ) ^ 2 = (c.natAbs : ℝ) ^ 2 :=
  fermatBoost_eq_zero_iff_sq hc hab

theorem fermatBoost_pos_iff {a b c : ℤ} (hc : c ≠ 0)
    (hab : a ≠ 0 ∨ b ≠ 0) :
    0 < fermatBoost a b c hc ↔ (c.natAbs : ℝ) < fermatL2 a b := by
  unfold fermatBoost
  have hL : 0 < fermatL2 a b := fermatL2_pos hab
  have hc0 : (0 : ℝ) < c.natAbs :=
    Nat.cast_pos.mpr (Int.natAbs_pos.mpr hc)
  have harg : 0 < fermatL2 a b / (c.natAbs : ℝ) := div_pos hL hc0
  rw [Real.log_pos_iff (le_of_lt harg), one_lt_div hc0]

/-- When boost and angle stay in the cone, the dual-axis seed is admissible. -/
theorem isAdmissibleContinuous_fermatTorsion {a b c : ℤ}
    (ha : a ≠ 0) (hc : c ≠ 0)
    (hα : 0 ≤ fermatBoost a b c hc) (hαπ : fermatBoost a b c hc ≤ Real.pi / 2)
    (hβ : 0 ≤ fermatAngle a b ha) (hβπ : fermatAngle a b ha ≤ Real.pi / 2) :
    IsAdmissibleContinuous (fermatTorsion a b c ha hc) := by
  intro i
  fin_cases i
  · refine ⟨hα, by simp [fermatTorsion], ?_⟩
    simpa [fermatTorsion] using hαπ
  · refine ⟨by simp [fermatTorsion], hβ, ?_⟩
    simpa [fermatTorsion] using hβπ
  · simp [fermatTorsion, Real.pi_div_two_pos.le]

end Embedding

end DstDiophantine
