import DstDiophantine.Embedding.Height
import DstDiophantine.Embedding.RotorClass
import DstDiophantine.Algebra.Discrete
import DstDiophantine.Algebra.Invariant
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Order.Group.Abs

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

/-! ### Sharp discrete height bound via `⌊N/4⌋` -/

private theorem nat_sq_diff_le_sum_sq (n m : ℕ) :
    |(n : ℤ) ^ 2 - (m : ℤ) ^ 2| ≤ ((n + m : ℕ) : ℤ) ^ 2 := by
  have hfac : (n : ℤ) ^ 2 - (m : ℤ) ^ 2 =
      ((n : ℤ) - (m : ℤ)) * ((n : ℤ) + (m : ℤ)) := by ring
  rw [hfac, abs_mul]
  have hn : (0 : ℤ) ≤ n := Nat.cast_nonneg n
  have hm : (0 : ℤ) ≤ m := Nat.cast_nonneg m
  have hsum_nn : (0 : ℤ) ≤ (n : ℤ) + (m : ℤ) := add_nonneg hn hm
  have hsum : (n : ℤ) + (m : ℤ) = ((n + m : ℕ) : ℤ) := by push_cast; rfl
  rw [abs_of_nonneg hsum_nn, hsum]
  have hdiff : |(n : ℤ) - (m : ℤ)| ≤ ((n + m : ℕ) : ℤ) := by
    rw [← hsum]
    rcases le_total (n : ℤ) (m : ℤ) with hle | hle
    · rw [abs_of_nonpos (sub_nonpos.mpr hle)]; linarith
    · rw [abs_of_nonneg (sub_nonneg.mpr hle)]; linarith
  have hmul :
      |(n : ℤ) - (m : ℤ)| * ((n + m : ℕ) : ℤ) ≤
        ((n + m : ℕ) : ℤ) * ((n + m : ℕ) : ℤ) :=
    mul_le_mul_of_nonneg_right hdiff (Nat.cast_nonneg (n + m))
  simpa [pow_two] using hmul

private theorem axis_mismatch_le_floor
    {N : ℕ} [NeZero N] {n m : ℕ} (h : 4 * (n + m) ≤ N) :
    |(n : ℤ) ^ 2 - (m : ℤ) ^ 2| ≤ ((N / 4 : ℕ) : ℤ) ^ 2 := by
  have hsum : n + m ≤ N / 4 :=
    (Nat.le_div_iff_mul_le (by decide : 0 < (4 : ℕ))).2 (by
      have : 4 * (n + m) = (n + m) * 4 := by ring
      rwa [this] at h)
  exact (nat_sq_diff_le_sum_sq n m).trans <|
    pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hsum) 2

/-- On an admissible lattice point, `|latticeMismatch| ≤ 3 ⌊N/4⌋²`. -/
theorem abs_latticeMismatch_le_of_admissible {N : ℕ} [NeZero N]
    (t : DiscreteTorsion N) (h : IsAdmissible t) :
    |latticeMismatch t| ≤ 3 * ((N / 4 : ℕ) : ℤ) ^ 2 := by
  have hfour := (AdmissibleClass.isAdmissible_iff_four_le t).mp h
  unfold latticeMismatch
  simp only [Fin.sum_univ_three]
  have h0 := axis_mismatch_le_floor (hfour 0)
  have h1 := axis_mismatch_le_floor (hfour 1)
  have h2 := axis_mismatch_le_floor (hfour 2)
  have htri :
      |((t.n 0).val : ℤ) ^ 2 - ((t.m 0).val : ℤ) ^ 2 +
          (((t.n 1).val : ℤ) ^ 2 - ((t.m 1).val : ℤ) ^ 2) +
          (((t.n 2).val : ℤ) ^ 2 - ((t.m 2).val : ℤ) ^ 2)| ≤
        |((t.n 0).val : ℤ) ^ 2 - ((t.m 0).val : ℤ) ^ 2| +
          |((t.n 1).val : ℤ) ^ 2 - ((t.m 1).val : ℤ) ^ 2| +
          |((t.n 2).val : ℤ) ^ 2 - ((t.m 2).val : ℤ) ^ 2| := by
    refine (abs_add_le _ _).trans ?_
    gcongr
    exact abs_add_le _ _
  refine htri.trans ?_
  linarith [h0, h1, h2]

theorem JNormalized_eq_sixteen_lattice {N : ℕ} [NeZero N] (t : DiscreteTorsion N) :
    JNormalized (toTorsionParams t) =
      (16 : ℝ) / (3 * (N : ℝ) ^ 2) * (latticeMismatch t : ℝ) := by
  unfold JNormalized
  rw [J_toTorsionParams]
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp [hN, hπ]
  ring

/-- Sharp admissible discrete bound `|JNormalized| ≤ (4⌊N/4⌋/N)²`. -/
theorem torsion_bound_discrete_sharp {N : ℕ} [NeZero N]
    (t : DiscreteTorsion N) (h : IsAdmissible t) :
    |JNormalized (toTorsionParams t)| ≤ ((4 * (N / 4 : ℕ) : ℝ) / N) ^ 2 := by
  have hlm := abs_latticeMismatch_le_of_admissible t h
  have hcoef : 0 ≤ (16 : ℝ) / (3 * (N : ℝ) ^ 2) := by positivity
  rw [JNormalized_eq_sixteen_lattice, abs_mul, abs_of_nonneg hcoef]
  have hlmR : |(latticeMismatch t : ℝ)| ≤ 3 * ((N / 4 : ℕ) : ℝ) ^ 2 := by
    have h1 : ((|latticeMismatch t| : ℤ) : ℝ) ≤
        ((3 * ((N / 4 : ℕ) : ℤ) ^ 2 : ℤ) : ℝ) :=
      Int.cast_le.mpr hlm
    have hrhs : ((3 * ((N / 4 : ℕ) : ℤ) ^ 2 : ℤ) : ℝ) =
        3 * ((N / 4 : ℕ) : ℝ) ^ 2 := by norm_cast
    rwa [Int.cast_abs, hrhs] at h1
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  set k : ℝ := ((N / 4 : ℕ) : ℝ) with hk
  calc (16 : ℝ) / (3 * (N : ℝ) ^ 2) * |(latticeMismatch t : ℝ)|
      ≤ (16 : ℝ) / (3 * (N : ℝ) ^ 2) * (3 * k ^ 2) := by gcongr
    _ = (4 * k / N) ^ 2 := by
        field_simp [hN]
        ring
    _ = ((4 * (N / 4 : ℕ) : ℝ) / N) ^ 2 := by rw [hk]

theorem torsion_bound_discrete_sharp_le_one {N : ℕ} [NeZero N]
    (t : DiscreteTorsion N) (h : IsAdmissible t) :
    |JNormalized (toTorsionParams t)| ≤ 1 := by
  have hsharp := torsion_bound_discrete_sharp t h
  have hfloor : (4 * (N / 4 : ℕ) : ℝ) ≤ N := by
    exact_mod_cast Nat.mul_div_le N 4
  have hNpos : 0 < (N : ℝ) := Nat.cast_pos.mpr (NeZero.pos N)
  have hfrac : (4 * (N / 4 : ℕ) : ℝ) / N ≤ 1 := (div_le_one hNpos).mpr hfloor
  have hnn : 0 ≤ (4 * (N / 4 : ℕ) : ℝ) / N := div_nonneg (by positivity) hNpos.le
  have hsq : ((4 * (N / 4 : ℕ) : ℝ) / N) ^ 2 ≤ (1 : ℝ) ^ 2 :=
    pow_le_pow_left₀ hnn hfrac 2
  simpa using hsharp.trans hsq

/-- When `4 ∣ N`, the pure-hyperbolic lattice point (all axes `n = N/4`). -/
noncomputable def pureHyperbolicDiscrete (N : ℕ) [NeZero N] : DiscreteTorsion N where
  n := fun _ => (↑(N / 4) : ZMod N)
  m := fun _ => 0

/-- When `4 ∣ N`, the pure-elliptic lattice point (all axes `m = N/4`). -/
noncomputable def pureEllipticDiscrete (N : ℕ) [NeZero N] : DiscreteTorsion N where
  n := fun _ => 0
  m := fun _ => (↑(N / 4) : ZMod N)

theorem zmod_val_of_div_four {N : ℕ} [NeZero N] (_h4 : 4 ∣ N) :
    ((↑(N / 4) : ZMod N).val) = N / 4 := by
  have hlt : N / 4 < N := Nat.div_lt_self (NeZero.pos N) (by decide : 1 < 4)
  exact ZMod.val_natCast_of_lt hlt

theorem pureHyperbolicDiscrete_admissible {N : ℕ} [NeZero N] (h4 : 4 ∣ N) :
    IsAdmissible (pureHyperbolicDiscrete N) := by
  rw [AdmissibleClass.isAdmissible_iff_four_le]
  intro a
  simp only [pureHyperbolicDiscrete, ZMod.val_zero, add_zero]
  rw [zmod_val_of_div_four h4]
  exact le_of_eq (Nat.mul_div_cancel' h4)

theorem pureEllipticDiscrete_admissible {N : ℕ} [NeZero N] (h4 : 4 ∣ N) :
    IsAdmissible (pureEllipticDiscrete N) := by
  rw [AdmissibleClass.isAdmissible_iff_four_le]
  intro a
  simp only [pureEllipticDiscrete, ZMod.val_zero, zero_add]
  rw [zmod_val_of_div_four h4]
  exact le_of_eq (Nat.mul_div_cancel' h4)

theorem JNormalized_pureHyperbolicDiscrete {N : ℕ} [NeZero N] (h4 : 4 ∣ N) :
    JNormalized (toTorsionParams (pureHyperbolicDiscrete N)) = 1 := by
  have hval := zmod_val_of_div_four (N := N) h4
  have hmul : (4 * (N / 4) : ℕ) = N := Nat.mul_div_cancel' h4
  have hNne : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  rw [JNormalized_eq_sixteen_lattice]
  have hlm :
      latticeMismatch (pureHyperbolicDiscrete N) = 3 * ((N / 4 : ℕ) : ℤ) ^ 2 := by
    simp only [latticeMismatch, pureHyperbolicDiscrete, Fin.sum_univ_three,
      ZMod.val_zero, hval]
    ring
  have hN4 : ((N / 4 : ℕ) : ℝ) = (N : ℝ) / 4 := by
    have hcast : ((4 * (N / 4) : ℕ) : ℝ) = 4 * ((N / 4 : ℕ) : ℝ) := by norm_cast
    rw [hmul] at hcast
    have h4ne : (4 : ℝ) ≠ 0 := by norm_num
    field_simp [h4ne]
    linarith
  rw [hlm]
  have hcast : ((3 * ((N / 4 : ℕ) : ℤ) ^ 2 : ℤ) : ℝ) =
      3 * ((N / 4 : ℕ) : ℝ) ^ 2 := by norm_cast
  rw [hcast, hN4]
  field_simp [hNne]
  ring

theorem JNormalized_pureEllipticDiscrete {N : ℕ} [NeZero N] (h4 : 4 ∣ N) :
    JNormalized (toTorsionParams (pureEllipticDiscrete N)) = -1 := by
  have hval := zmod_val_of_div_four (N := N) h4
  have hmul : (4 * (N / 4) : ℕ) = N := Nat.mul_div_cancel' h4
  have hNne : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  rw [JNormalized_eq_sixteen_lattice]
  have hlm :
      latticeMismatch (pureEllipticDiscrete N) = -(3 * ((N / 4 : ℕ) : ℤ) ^ 2) := by
    simp only [latticeMismatch, pureEllipticDiscrete, Fin.sum_univ_three,
      ZMod.val_zero, hval]
    ring
  have hN4 : ((N / 4 : ℕ) : ℝ) = (N : ℝ) / 4 := by
    have hcast : ((4 * (N / 4) : ℕ) : ℝ) = 4 * ((N / 4 : ℕ) : ℝ) := by norm_cast
    rw [hmul] at hcast
    have h4ne : (4 : ℝ) ≠ 0 := by norm_num
    field_simp [h4ne]
    linarith
  rw [hlm]
  have hcast : ((-(3 * ((N / 4 : ℕ) : ℤ) ^ 2) : ℤ) : ℝ) =
      -(3 * ((N / 4 : ℕ) : ℝ) ^ 2) := by norm_cast
  rw [hcast, hN4]
  field_simp [hNne]
  ring

/-- If `4` does not divide `N`, every admissible point has `|JNormalized| < 1`. -/
theorem torsion_bound_discrete_strict {N : ℕ} [NeZero N]
    (h4 : ¬ 4 ∣ N) (t : DiscreteTorsion N) (h : IsAdmissible t) :
    |JNormalized (toTorsionParams t)| < 1 := by
  have hsharp := torsion_bound_discrete_sharp t h
  have hfloor : 4 * (N / 4) < N := by
    have hle := Nat.mul_div_le N 4
    refine lt_of_le_of_ne hle ?_
    intro heq
    exact h4 ⟨N / 4, heq.symm⟩
  have hNpos : 0 < (N : ℝ) := Nat.cast_pos.mpr (NeZero.pos N)
  have hfrac : (4 * (N / 4 : ℕ) : ℝ) / N < 1 :=
    (div_lt_one hNpos).mpr (by exact_mod_cast hfloor)
  have hnn : 0 ≤ (4 * (N / 4 : ℕ) : ℝ) / N := div_nonneg (by positivity) hNpos.le
  have hsq : ((4 * (N / 4 : ℕ) : ℝ) / N) ^ 2 < (1 : ℝ) ^ 2 := by
    nlinarith [hnn, hfrac]
  exact lt_of_le_of_lt hsharp (by simpa using hsq)

end Framework

end DstDiophantine
