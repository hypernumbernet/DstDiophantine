import DstDiophantine.Algebra.Operations
import Mathlib.Data.ZMod.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Discrete torsion torus `(ℤ/Nℤ)⁶`

Rapidities are discretised as in the DST paper:
`ω_a = 2π n_a / N`, `φ_a = 2π m_a / N` for `n_a, m_a ∈ ℤ/Nℤ`.
-/

namespace DstDiophantine

open Operations Real

namespace Discrete

variable {N : ℕ} [NeZero N]

/-- A point on the six-dimensional phase torus `(ℤ/Nℤ)⁶`. -/
structure DiscreteTorsion (N : ℕ) [NeZero N] where
  n : Fin 3 → ZMod N
  m : Fin 3 → ZMod N

def discreteEquiv : DiscreteTorsion N ≃ (Fin 3 → ZMod N) × (Fin 3 → ZMod N) where
  toFun t := (t.n, t.m)
  invFun p := { n := p.1, m := p.2 }
  left_inv t := by cases t; rfl
  right_inv _ := rfl

noncomputable instance : Fintype (DiscreteTorsion N) :=
  Fintype.ofEquiv _ discreteEquiv.symm

instance : Finite (DiscreteTorsion N) :=
  inferInstance

/-- Embed discrete rapidities into continuous torsion parameters. -/
noncomputable def toTorsionParams (t : DiscreteTorsion N) : TorsionParams where
  alpha := fun a => 2 * Real.pi * (t.n a).val / N
  beta := fun a => 2 * Real.pi * (t.m a).val / N

@[simp] theorem toTorsionParams_alpha (t : DiscreteTorsion N) (a : Fin 3) :
    (toTorsionParams t).alpha a = 2 * Real.pi * (t.n a).val / N := rfl

@[simp] theorem toTorsionParams_beta (t : DiscreteTorsion N) (a : Fin 3) :
    (toTorsionParams t).beta a = 2 * Real.pi * (t.m a).val / N := rfl

theorem toTorsionParams_alpha_nonneg (t : DiscreteTorsion N) (a : Fin 3) :
    0 ≤ (toTorsionParams t).alpha a := by
  simp only [toTorsionParams_alpha]
  have hπ : 0 ≤ Real.pi := Real.pi_pos.le
  have hN : 0 < (N : ℝ) := Nat.cast_pos.mpr (NeZero.pos N)
  exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hπ) (Nat.cast_nonneg _)) hN.le

theorem toTorsionParams_beta_nonneg (t : DiscreteTorsion N) (a : Fin 3) :
    0 ≤ (toTorsionParams t).beta a := by
  simp only [toTorsionParams_beta]
  have hπ : 0 ≤ Real.pi := Real.pi_pos.le
  have hN : 0 < (N : ℝ) := Nat.cast_pos.mpr (NeZero.pos N)
  exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hπ) (Nat.cast_nonneg _)) hN.le

/-- Principal-branch anti-synchronisation `|α_a + β_a| ≤ π/2`. -/
def IsPrincipalBranch (p : TorsionParams) : Prop :=
  ∀ a : Fin 3, |p.alpha a + p.beta a| ≤ Real.pi / 2

/-- Continuous admissible configuration: non-negative rapidities with anti-synchronisation. -/
def IsAdmissibleContinuous (p : TorsionParams) : Prop :=
  ∀ a : Fin 3, 0 ≤ p.alpha a ∧ 0 ≤ p.beta a ∧ p.alpha a + p.beta a ≤ Real.pi / 2

/-- Admissible discrete configuration: embedded parameters lie on the principal branch. -/
def IsAdmissible (t : DiscreteTorsion N) : Prop :=
  IsPrincipalBranch (toTorsionParams t)

theorem admissible_continuous_of_discrete (t : DiscreteTorsion N) (h : IsAdmissible t) :
    IsAdmissibleContinuous (toTorsionParams t) := by
  intro a
  have hα := toTorsionParams_alpha_nonneg t a
  have hβ := toTorsionParams_beta_nonneg t a
  have hsum := h a
  rw [abs_of_nonneg (add_nonneg hα hβ)] at hsum
  exact ⟨hα, hβ, hsum⟩

theorem admissible_sum_le (t : DiscreteTorsion N) (h : IsAdmissible t) (a : Fin 3) :
    (toTorsionParams t).alpha a + (toTorsionParams t).beta a ≤ Real.pi / 2 := by
  have hcont := admissible_continuous_of_discrete t h
  exact (hcont a).2.2

theorem admissible_alpha_le_half_pi (t : DiscreteTorsion N) (h : IsAdmissible t) (a : Fin 3) :
    (toTorsionParams t).alpha a ≤ Real.pi / 2 := by
  have hβ := toTorsionParams_beta_nonneg t a
  linarith [admissible_sum_le t h a]

theorem admissible_beta_le_half_pi (t : DiscreteTorsion N) (h : IsAdmissible t) (a : Fin 3) :
    (toTorsionParams t).beta a ≤ Real.pi / 2 := by
  have hα := toTorsionParams_alpha_nonneg t a
  linarith [admissible_sum_le t h a]

end Discrete

end DstDiophantine
