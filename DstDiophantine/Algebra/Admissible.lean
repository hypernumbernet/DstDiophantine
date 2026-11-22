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

def IsAdmissibleContinuous (p : TorsionParams) : Prop :=
  ∀ a : Fin 3, 0 ≤ p.alpha a ∧ 0 ≤ p.beta a ∧ p.alpha a + p.beta a ≤ Real.pi / 2

theorem admissibleContinuous_implies_principalBranch (p : TorsionParams)
    (h : IsAdmissibleContinuous p) : IsPrincipalBranch p := by
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

theorem admissibleContinuous_sum_le (p : TorsionParams)
    (h : IsAdmissibleContinuous p) (a : Fin 3) :
    p.alpha a + p.beta a ≤ Real.pi / 2 :=
  (h a).2.2

theorem admissibleContinuous_alpha_le_half_pi (p : TorsionParams)
    (h : IsAdmissibleContinuous p) (a : Fin 3) :
    p.alpha a ≤ Real.pi / 2 := by
  linarith [admissibleContinuous_beta_nonneg p h a, admissibleContinuous_sum_le p h a]

theorem admissibleContinuous_beta_le_half_pi (p : TorsionParams)
    (h : IsAdmissibleContinuous p) (a : Fin 3) :
    p.beta a ≤ Real.pi / 2 := by
  linarith [admissibleContinuous_alpha_nonneg p h a, admissibleContinuous_sum_le p h a]

end Admissible

end DstDiophantine
