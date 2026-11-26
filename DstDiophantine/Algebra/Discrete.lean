import DstDiophantine.Algebra.Admissible
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Positivity

/-!
# Discrete torsion torus `(ℤ/Nℤ)⁶`

Rapidities are `2π k / N`. This module only embeds the torus; admissibility lives in `Admissible`.
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

theorem card_discreteTorsion : Fintype.card (DiscreteTorsion N) = N ^ 6 := by
  rw [Fintype.card_congr discreteEquiv, Fintype.card_prod]
  simp [Fintype.card_fin, ZMod.card]
  ring

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

theorem toTorsionParams_alpha_lt_two_pi (t : DiscreteTorsion N) (a : Fin 3) :
    (toTorsionParams t).alpha a < 2 * Real.pi := by
  simp only [toTorsionParams_alpha]
  have hN : 0 < (N : ℝ) := Nat.cast_pos.mpr (NeZero.pos N)
  have hval : ((t.n a).val : ℝ) < N := Nat.cast_lt.mpr (ZMod.val_lt _)
  have hmul : 2 * Real.pi * ((t.n a).val : ℝ) < 2 * Real.pi * N :=
    mul_lt_mul_of_pos_left hval (by positivity)
  rwa [div_lt_iff₀ hN]

theorem toTorsionParams_beta_lt_two_pi (t : DiscreteTorsion N) (a : Fin 3) :
    (toTorsionParams t).beta a < 2 * Real.pi := by
  simp only [toTorsionParams_beta]
  have hN : 0 < (N : ℝ) := Nat.cast_pos.mpr (NeZero.pos N)
  have hval : ((t.m a).val : ℝ) < N := Nat.cast_lt.mpr (ZMod.val_lt _)
  have hmul : 2 * Real.pi * ((t.m a).val : ℝ) < 2 * Real.pi * N :=
    mul_lt_mul_of_pos_left hval (by positivity)
  rwa [div_lt_iff₀ hN]

/-- Backward-compatible aliases for continuous admissibility predicates. -/
abbrev IsPrincipalBranch := Admissible.IsPrincipalBranch
abbrev IsAdmissibleContinuous := Admissible.IsAdmissibleContinuous

/-- Discrete cone: per axis `4(n+m) ≤ N` (legacy tight bound; implies mismatch admissibility). -/
def IsAdmissible (t : DiscreteTorsion N) : Prop :=
  ∀ a : Fin 3, 4 * ((t.n a).val + (t.m a).val) ≤ N

theorem isAdmissible_iff_four_coords (t : DiscreteTorsion N) :
    IsAdmissible t ↔ ∀ a : Fin 3, 4 * ((t.n a).val + (t.m a).val) ≤ N :=
  Iff.rfl

private theorem sum_le_half_pi_of_lattice (t : DiscreteTorsion N) (h : IsAdmissible t) (a : Fin 3) :
    (toTorsionParams t).alpha a + (toTorsionParams t).beta a ≤ Real.pi / 2 := by
  rw [toTorsionParams_alpha, toTorsionParams_beta]
  have hNpos : 0 < (N : ℝ) := Nat.cast_pos.mpr (NeZero.pos N)
  have hπ : 0 < Real.pi := Real.pi_pos
  have hineq : (4 * ((t.n a).val + (t.m a).val) : ℝ) ≤ N := by exact_mod_cast h a
  have hhalf : 2 * ((t.n a).val + (t.m a).val : ℝ) / N ≤ 1 / 2 := by
    have h1 : (4 * ((t.n a).val + (t.m a).val) : ℝ) / N ≤ 1 := (div_le_one hNpos).mpr hineq
    have : 2 * (2 * ((t.n a).val + (t.m a).val : ℝ) / N) ≤ 1 := by
      convert h1 using 1 <;> field_simp <;> ring
    linarith
  calc 2 * Real.pi * (t.n a).val / N + 2 * Real.pi * (t.m a).val / N
      = Real.pi * (2 * ((t.n a).val + (t.m a).val : ℝ) / N) := by ring
    _ ≤ Real.pi * (1 / 2) := mul_le_mul_of_nonneg_left hhalf hπ.le
    _ = Real.pi / 2 := by ring

theorem admissible_implies_continuous (t : DiscreteTorsion N) (h : IsAdmissible t) :
    IsAdmissibleContinuous (toTorsionParams t) := by
  intro a
  have hsum := sum_le_half_pi_of_lattice t h a
  have hα := toTorsionParams_alpha_nonneg t a
  refine ⟨hα, toTorsionParams_beta_nonneg t a, by linarith [hsum, hα, Real.pi_pos],
    le_trans hsum (by linarith [Real.pi_pos])⟩

theorem admissible_continuous_of_discrete (t : DiscreteTorsion N) (h : IsAdmissible t) :
    IsAdmissibleContinuous (toTorsionParams t) :=
  admissible_implies_continuous t h

theorem admissible_implies_legacy_continuous (t : DiscreteTorsion N) (h : IsAdmissible t) :
    IsAdmissibleContinuousLegacy (toTorsionParams t) := by
  intro a
  refine ⟨toTorsionParams_alpha_nonneg t a, toTorsionParams_beta_nonneg t a,
    sum_le_half_pi_of_lattice t h a⟩

theorem isAdmissible_iff_principalBranch (t : DiscreteTorsion N) :
    IsAdmissible t ↔ IsPrincipalBranch (toTorsionParams t) := by
  constructor
  · intro h a
    have hα := toTorsionParams_alpha_nonneg t a
    have hβ := toTorsionParams_beta_nonneg t a
    have hsum := sum_le_half_pi_of_lattice t h a
    rw [abs_of_nonneg (add_nonneg hα hβ)]
    exact hsum
  · intro h a
    have hα := toTorsionParams_alpha_nonneg t a
    have hβ := toTorsionParams_beta_nonneg t a
    have hsum := h a
    rw [abs_of_nonneg (add_nonneg hα hβ)] at hsum
    have hNpos : 0 < (N : ℝ) := Nat.cast_pos.mpr (NeZero.pos N)
    rw [toTorsionParams_alpha, toTorsionParams_beta] at hsum
    have hineq : (4 * ((t.n a).val + (t.m a).val) : ℝ) ≤ N := by
      have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
      field_simp [hNpos.ne', hπ] at hsum ⊢
      nlinarith [Real.pi_pos]
    exact_mod_cast hineq

theorem admissible_sum_le (t : DiscreteTorsion N) (h : IsAdmissible t) (a : Fin 3) :
    (toTorsionParams t).alpha a + (toTorsionParams t).beta a ≤ Real.pi :=
  admissibleContinuous_sum_le _ (admissible_implies_continuous t h) a

theorem admissible_sum_le_half_pi (t : DiscreteTorsion N) (h : IsAdmissible t) (a : Fin 3) :
    (toTorsionParams t).alpha a + (toTorsionParams t).beta a ≤ Real.pi / 2 :=
  sum_le_half_pi_of_lattice t h a

theorem admissible_alpha_le_half_pi (t : DiscreteTorsion N) (h : IsAdmissible t) (a : Fin 3) :
    (toTorsionParams t).alpha a ≤ Real.pi / 2 :=
  admissibleContinuous_alpha_le_half_pi _ (admissible_implies_legacy_continuous t h) a

theorem admissible_beta_le_half_pi (t : DiscreteTorsion N) (h : IsAdmissible t) (a : Fin 3) :
    (toTorsionParams t).beta a ≤ Real.pi / 2 :=
  admissibleContinuous_legacy_beta_le_half_pi _
    (admissible_implies_legacy_continuous t h) a

end Discrete

end DstDiophantine
