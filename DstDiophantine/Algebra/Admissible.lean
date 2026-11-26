import DstDiophantine.Algebra.Operations
import Mathlib.Basic.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Admissible torsional configurations

`IsPrincipalBranch` alone does not bound `J`. Anti-synchronisation `R_dual = R_usual†` is not the
cone `α + β ≤ π/2`.
-/

namespace DstDiophantine

open Operations Real

namespace Admissible

def IsPrincipalBranch (p : TorsionParams) : Prop :=
  ∀ a : Fin 3, |p.alpha a + p.beta a| ≤ Real.pi / 2

/-- Legacy admissible cone (`α+β ≤ π/2`); strictly contained in `IsAdmissibleContinuous`. -/
def IsAdmissibleContinuousLegacy (p : TorsionParams) : Prop :=
  ∀ a : Fin 3, 0 ≤ p.alpha a ∧ 0 ≤ p.beta a ∧ p.alpha a + p.beta a ≤ Real.pi / 2

/-- Mismatch cone: rotation mismatch may reach `π` (primary overlap zero), boost nonnegative.
    Each axis satisfies `β ≤ π` and `α+β ≤ π`, so repulsion at `β=π` stays admissible. -/
def IsAdmissibleContinuous (p : TorsionParams) : Prop :=
  ∀ a : Fin 3, 0 ≤ p.alpha a ∧ 0 ≤ p.beta a ∧
    p.beta a ≤ Real.pi ∧ p.alpha a + p.beta a ≤ Real.pi

theorem legacy_admissible_implies_mismatch (p : TorsionParams)
    (h : IsAdmissibleContinuousLegacy p) : IsAdmissibleContinuous p := by
  intro a
  have hα := (h a).1
  have hβ := (h a).2.1
  have hsum := (h a).2.2
  refine ⟨hα, hβ, by linarith [hsum, hα, Real.pi_pos], ?_⟩
  exact le_trans hsum (by linarith [Real.pi_pos])

theorem admissibleContinuous_implies_principalBranch (p : TorsionParams)
    (h : IsAdmissibleContinuousLegacy p) : IsPrincipalBranch p := by
  intro a
  have hα := (h a).1
  have hβ := (h a).2.1
  have hsum := (h a).2.2
  rw [abs_of_nonneg (add_nonneg hα hβ)]
  exact hsum

theorem admissibleContinuous_alpha_nonneg (p : TorsionParams)
    (h : IsAdmissibleContinuous p) (a : Fin 3) : 0 ≤ p.alpha a :=
  (h a).1

theorem admissibleContinuous_beta_nonneg (p : TorsionParams)
    (h : IsAdmissibleContinuous p) (a : Fin 3) : 0 ≤ p.beta a :=
  (h a).2.1

theorem admissibleContinuous_beta_le_pi (p : TorsionParams)
    (h : IsAdmissibleContinuous p) (a : Fin 3) : p.beta a ≤ Real.pi :=
  (h a).2.2.1

theorem admissibleContinuous_sum_le (p : TorsionParams)
    (h : IsAdmissibleContinuous p) (a : Fin 3) :
    p.alpha a + p.beta a ≤ Real.pi :=
  (h a).2.2.2

theorem admissibleContinuous_legacy_sum_le_half_pi (p : TorsionParams)
    (h : IsAdmissibleContinuousLegacy p) (a : Fin 3) :
    p.alpha a + p.beta a ≤ Real.pi / 2 :=
  (h a).2.2

theorem admissibleContinuous_alpha_le_pi (p : TorsionParams)
    (h : IsAdmissibleContinuous p) (a : Fin 3) :
    p.alpha a ≤ Real.pi := by
  linarith [admissibleContinuous_beta_nonneg p h a, admissibleContinuous_sum_le p h a,
    Real.pi_pos]

theorem admissibleContinuous_legacy_alpha_nonneg (p : TorsionParams)
    (h : IsAdmissibleContinuousLegacy p) (a : Fin 3) : 0 ≤ p.alpha a :=
  (h a).1

theorem admissibleContinuous_legacy_beta_nonneg (p : TorsionParams)
    (h : IsAdmissibleContinuousLegacy p) (a : Fin 3) : 0 ≤ p.beta a :=
  (h a).2.1

theorem admissibleContinuous_legacy_alpha_le_half_pi (p : TorsionParams)
    (h : IsAdmissibleContinuousLegacy p) (a : Fin 3) :
    p.alpha a ≤ Real.pi / 2 := by
  linarith [admissibleContinuous_legacy_beta_nonneg p h a,
    admissibleContinuous_legacy_sum_le_half_pi p h a]

theorem admissibleContinuous_legacy_beta_le_half_pi (p : TorsionParams)
    (h : IsAdmissibleContinuousLegacy p) (a : Fin 3) :
    p.beta a ≤ Real.pi / 2 := by
  linarith [admissibleContinuous_legacy_alpha_nonneg p h a,
    admissibleContinuous_legacy_sum_le_half_pi p h a]

/-- Legacy cone bounds each half-angle by `π/2`. -/
theorem admissibleContinuous_alpha_le_half_pi (p : TorsionParams)
    (h : IsAdmissibleContinuousLegacy p) (a : Fin 3) :
    p.alpha a ≤ Real.pi / 2 :=
  admissibleContinuous_legacy_alpha_le_half_pi p h a

theorem admissibleContinuous_beta_le_half_pi (p : TorsionParams)
    (h : IsAdmissibleContinuousLegacy p) (a : Fin 3) :
    p.beta a ≤ Real.pi / 2 :=
  admissibleContinuous_legacy_beta_le_half_pi p h a

theorem admissible_mismatch_implies_beta_rotation_half_le_pi (p : TorsionParams)
    (h : IsAdmissibleContinuous p) (a : Fin 3) :
    p.beta a / 2 ≤ Real.pi / 2 :=
  div_le_div_of_nonneg_right (admissibleContinuous_beta_le_pi p h a) (by norm_num)

end Admissible

end DstDiophantine
