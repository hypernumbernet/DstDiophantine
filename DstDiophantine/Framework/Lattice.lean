import DstDiophantine.Embedding.Height
import DstDiophantine.Embedding.RotorClass
import DstDiophantine.Algebra.Discrete
import DstDiophantine.Algebra.Invariant
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# Admissible lattice and zero-height configurations

Diophantine search on the discrete torus is restricted to admissible points.
Zero torsional height is characterised by an integer lattice condition, which
is decidable without comparing transcendental reals.
-/

namespace DstDiophantine

namespace Framework

open Discrete Invariant Operations Real

variable {N : ℕ} [NeZero N]

/-- Normalised torsion height vanishes. -/
def IsZeroHeight (p : TorsionParams) : Prop :=
  Embedding.torsionHeight p = 0

theorem isZeroHeight_iff_JNormalized (p : TorsionParams) :
    IsZeroHeight p ↔ JNormalized p = 0 := by
  unfold IsZeroHeight Embedding.torsionHeight
  exact abs_eq_zero

theorem isZeroHeight_iff_J (p : TorsionParams) :
    IsZeroHeight p ↔ J p = 0 := by
  rw [isZeroHeight_iff_JNormalized]
  unfold JNormalized
  constructor
  · intro h
    have hpos : (8 / (3 * Real.pi ^ 2) : ℝ) ≠ 0 := by positivity
    exact (mul_eq_zero.mp h).resolve_left hpos
  · intro h
    simp [h]

/-- Integer quadratic mismatch of a discrete torus point. -/
def latticeMismatch (t : DiscreteTorsion N) : ℤ :=
  ∑ a : Fin 3, (((t.n a).val : ℤ) ^ 2 - ((t.m a).val : ℤ) ^ 2)

private theorem axis_sq_factor (n m N : ℕ) [NeZero N] :
    (2 * Real.pi * n / N) ^ 2 - (2 * Real.pi * m / N) ^ 2 =
      (2 * Real.pi / N) ^ 2 * ((n : ℝ) ^ 2 - (m : ℝ) ^ 2) := by
  field_simp

theorem J_toTorsionParams (t : DiscreteTorsion N) :
    J (toTorsionParams t) =
      (1 / 2) * (2 * Real.pi / N) ^ 2 * (latticeMismatch t : ℝ) := by
  rw [J_coef]
  simp only [toTorsionParams_alpha, toTorsionParams_beta, latticeMismatch]
  have hfac (a : Fin 3) :
      (2 * Real.pi * (t.n a).val / N) ^ 2 - (2 * Real.pi * (t.m a).val / N) ^ 2 =
        (2 * Real.pi / N) ^ 2 * (((t.n a).val : ℝ) ^ 2 - ((t.m a).val : ℝ) ^ 2) :=
    axis_sq_factor (t.n a).val (t.m a).val N
  simp_rw [hfac, ← Finset.mul_sum]
  push_cast
  ring_nf

theorem isZeroHeight_toTorsionParams_iff (t : DiscreteTorsion N) :
    IsZeroHeight (toTorsionParams t) ↔ latticeMismatch t = 0 := by
  rw [isZeroHeight_iff_J, J_toTorsionParams]
  have hcoef : (1 / 2 : ℝ) * (2 * Real.pi / N) ^ 2 ≠ 0 := by
    have : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
    positivity
  constructor
  · intro h
    have h' : (latticeMismatch t : ℝ) = 0 := (mul_eq_zero.mp h).resolve_left hcoef
    exact Int.cast_eq_zero.mp h'
  · intro h
    simp [h]

/-- Admissible discrete configurations as a subtype. -/
def AdmissibleClass (N : ℕ) [NeZero N] :=
  { t : DiscreteTorsion N // IsAdmissible t }

namespace AdmissibleClass

variable {N : ℕ} [NeZero N]

/-- Embed back to continuous torsion parameters. -/
noncomputable def toParams (t : AdmissibleClass N) : TorsionParams :=
  toTorsionParams t.val

/-- Zero-height predicate on admissible points. -/
def IsZero (t : AdmissibleClass N) : Prop :=
  IsZeroHeight (toParams t)

theorem isZero_iff_latticeMismatch (t : AdmissibleClass N) :
    IsZero t ↔ latticeMismatch t.val = 0 := by
  unfold IsZero toParams
  exact isZeroHeight_toTorsionParams_iff t.val

private theorem sum_le_half_pi_iff (n m N : ℕ) [NeZero N] :
    2 * Real.pi * n / N + 2 * Real.pi * m / N ≤ Real.pi / 2 ↔
      4 * (n + m) ≤ N := by
  have hNpos : 0 < (N : ℝ) := Nat.cast_pos.mpr (NeZero.pos N)
  have hπ : 0 < Real.pi := Real.pi_pos
  constructor
  · intro h
    have hcomb : 2 * Real.pi * (n + m : ℝ) / N ≤ Real.pi / 2 := by
      convert h using 1
      ring
    have hcleared : 4 * (n + m : ℝ) ≤ N := by
      have h1 := mul_le_mul_of_nonneg_left hcomb (by positivity : (0 : ℝ) ≤ 2 * N / Real.pi)
      have hL : 2 * N / Real.pi * (2 * Real.pi * (n + m : ℝ) / N) = 4 * (n + m : ℝ) := by
        field_simp; ring
      have hR : 2 * N / Real.pi * (Real.pi / 2) = (N : ℝ) := by
        field_simp
      rwa [hL, hR] at h1
    exact_mod_cast hcleared
  · intro h
    have hineqR : (4 * (n + m) : ℝ) ≤ N := by exact_mod_cast h
    have hhalf : 2 * (n + m : ℝ) / N ≤ 1 / 2 := by
      have h1 : (4 * (n + m : ℝ)) / N ≤ 1 := (div_le_one hNpos).mpr hineqR
      have : 2 * (2 * (n + m : ℝ) / N) ≤ 1 := by
        convert h1 using 1
        field_simp; ring
      linarith
    have hπbound : 2 * Real.pi * (n + m : ℝ) / N ≤ Real.pi / 2 := by
      calc 2 * Real.pi * (n + m : ℝ) / N
          = Real.pi * (2 * (n + m : ℝ) / N) := by ring
        _ ≤ Real.pi * (1 / 2) := mul_le_mul_of_nonneg_left hhalf hπ.le
        _ = Real.pi / 2 := by ring
    convert hπbound using 1
    ring

/--
Admissibility on the discrete torus is the integer inequality
`4 (n.val + m.val) ≤ N` on each axis (non-negative rapidities are automatic).
-/
theorem isAdmissible_iff_four_le (t : DiscreteTorsion N) :
    IsAdmissible t ↔ ∀ a : Fin 3, 4 * ((t.n a).val + (t.m a).val) ≤ N := by
  rw [isAdmissible_iff_principalBranch]
  unfold IsPrincipalBranch Admissible.IsPrincipalBranch
  constructor
  · intro h a
    have hα := toTorsionParams_alpha_nonneg t a
    have hβ := toTorsionParams_beta_nonneg t a
    have hsum := h a
    rw [abs_of_nonneg (add_nonneg hα hβ), toTorsionParams_alpha, toTorsionParams_beta] at hsum
    exact (sum_le_half_pi_iff (t.n a).val (t.m a).val N).mp hsum
  · intro h a
    have hα := toTorsionParams_alpha_nonneg t a
    have hβ := toTorsionParams_beta_nonneg t a
    rw [abs_of_nonneg (add_nonneg hα hβ), toTorsionParams_alpha, toTorsionParams_beta]
    exact (sum_le_half_pi_iff (t.n a).val (t.m a).val N).mpr (h a)

instance : DecidablePred (IsAdmissible (N := N)) := fun t =>
  decidable_of_iff _ (isAdmissible_iff_four_le t).symm

instance : DecidablePred (fun t : DiscreteTorsion N => latticeMismatch t = 0) :=
  fun _ => inferInstance

noncomputable instance : Fintype (AdmissibleClass N) :=
  Subtype.fintype _

theorem finite : Finite (AdmissibleClass N) :=
  inferInstance

end AdmissibleClass

/-- Existence of an admissible zero-height lattice point (discrete search problem). -/
def ExistsZeroHeight (N : ℕ) [NeZero N] : Prop :=
  ∃ t : AdmissibleClass N, AdmissibleClass.IsZero t

theorem existsZeroHeight_iff (N : ℕ) [NeZero N] :
    ExistsZeroHeight N ↔
      ∃ t : DiscreteTorsion N, IsAdmissible t ∧ latticeMismatch t = 0 := by
  constructor
  · rintro ⟨⟨t, ht⟩, hz⟩
    exact ⟨t, ht, (AdmissibleClass.isZero_iff_latticeMismatch ⟨t, ht⟩).mp hz⟩
  · rintro ⟨t, ht, hz⟩
    refine ⟨⟨t, ht⟩, (AdmissibleClass.isZero_iff_latticeMismatch ⟨t, ht⟩).mpr hz⟩

/-- Balanced axes (`n = m`) give zero height (sufficient but not necessary). -/
theorem zeroHeight_of_balanced (t : DiscreteTorsion N)
    (hbal : ∀ a, t.n a = t.m a) : IsZeroHeight (toTorsionParams t) := by
  rw [isZeroHeight_toTorsionParams_iff]
  unfold latticeMismatch
  apply Finset.sum_eq_zero
  intro a _
  simp [hbal a]

/-- The origin is an admissible zero-height point. -/
theorem zero_admissible_zeroHeight (N : ℕ) [NeZero N] :
    IsAdmissible (Embedding.zeroTorsion N) ∧
      IsZeroHeight (toTorsionParams (Embedding.zeroTorsion N)) := by
  constructor
  · rw [AdmissibleClass.isAdmissible_iff_four_le]
    intro a
    simp [Embedding.zeroTorsion]
  · exact zeroHeight_of_balanced _ (fun _ => rfl)

theorem existsZeroHeight_of_neZero (N : ℕ) [NeZero N] : ExistsZeroHeight N := by
  refine ⟨⟨Embedding.zeroTorsion N, (zero_admissible_zeroHeight N).1⟩, ?_⟩
  exact (AdmissibleClass.isZero_iff_latticeMismatch _).mpr <| by
    simp [latticeMismatch, Embedding.zeroTorsion]

end Framework

end DstDiophantine
