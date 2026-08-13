import DstDiophantine.Algebra.Admissible
import Mathlib.Data.ZMod.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Discrete torsion torus `(ℤ/Nℤ)⁶`

Rapidities are discretised as in the DST discrete companion:
`ω_a = 2π n_a / N`, `φ_a = 2π m_a / N` for `n_a, m_a ∈ ℤ/Nℤ`
(Lean: `alpha` / `beta` via `toTorsionParams`).

Admissibility predicates live in `Admissible`; this module only embeds the
torus and characterises discrete admissibility.
-/

namespace DstDiophantine

open Operations Real Admissible

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

/-- Backward-compatible aliases for continuous admissibility predicates. -/
abbrev IsPrincipalBranch := Admissible.IsPrincipalBranch
abbrev IsAdmissibleContinuous := Admissible.IsAdmissibleContinuous

/-- Admissible discrete configuration: embedded parameters are continuously admissible. -/
def IsAdmissible (t : DiscreteTorsion N) : Prop :=
  IsAdmissibleContinuous (toTorsionParams t)

/-- Discrete admissibility coincides with continuous admissibility of the embedding. -/
theorem isAdmissible_iff_admissibleContinuous (t : DiscreteTorsion N) :
    IsAdmissible t ↔ IsAdmissibleContinuous (toTorsionParams t) :=
  Iff.rfl

/-- Legacy name: discrete admissibility implies the principal-branch condition. -/
theorem admissible_continuous_of_discrete (t : DiscreteTorsion N) (h : IsAdmissible t) :
    IsAdmissibleContinuous (toTorsionParams t) :=
  h

theorem isAdmissible_iff_principalBranch (t : DiscreteTorsion N) :
    IsAdmissible t ↔ IsPrincipalBranch (toTorsionParams t) := by
  constructor
  · intro h
    exact admissibleContinuous_implies_principalBranch _ h
  · intro h a
    have hα := toTorsionParams_alpha_nonneg t a
    have hβ := toTorsionParams_beta_nonneg t a
    have hsum := h a
    rw [abs_of_nonneg (add_nonneg hα hβ)] at hsum
    exact ⟨hα, hβ, hsum⟩

theorem admissible_sum_le (t : DiscreteTorsion N) (h : IsAdmissible t) (a : Fin 3) :
    (toTorsionParams t).alpha a + (toTorsionParams t).beta a ≤ Real.pi / 2 :=
  admissibleContinuous_sum_le _ h a

theorem admissible_alpha_le_half_pi (t : DiscreteTorsion N) (h : IsAdmissible t) (a : Fin 3) :
    (toTorsionParams t).alpha a ≤ Real.pi / 2 :=
  admissibleContinuous_alpha_le_half_pi _ h a

theorem admissible_beta_le_half_pi (t : DiscreteTorsion N) (h : IsAdmissible t) (a : Fin 3) :
    (toTorsionParams t).beta a ≤ Real.pi / 2 :=
  admissibleContinuous_beta_le_half_pi _ h a

end Discrete

end DstDiophantine
