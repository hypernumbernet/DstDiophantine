import DstDiophantine.Framework.Lattice
import DstDiophantine.Embedding.Height
import DstDiophantine.Algebra.Amplification
import DstDiophantine.Algebra.Invariant
import DstDiophantine.Algebra.Discrete
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# Shared amplification no-go core

Problem-independent continuous and discrete amplification contradictions.
Individual theorems (Fermat / Beal / abc) supply only the problem-specific
bridge that produces a seed or lattice witness; the contradiction itself lives
here.

## Layering

1. Integer equation ↔ null motor (additive, already in `Representation`).
2. Problem-specific bridge: solution ⇒ amplification witness.
3. Shared no-go: an admissible `k`-fold amplification cannot have seed taller
   than `1/k²` (continuous) or cannot sit on a coarse nonzero lattice
   (discrete).
-/

namespace DstDiophantine

namespace Framework

open Amplification Discrete Invariant
open _root_.DstDiophantine.Embedding

/-! ### Continuous pure-boost no-go -/

/--
If a `k`-fold pure boost remains continuously admissible, the seed height is at
most `1/k²`.
-/
theorem amplification_implies_seed_le (θ : ℝ) {k : ℕ} (hk : 1 ≤ k)
    (hadm : IsAdmissibleContinuous (pureBoost (k * θ))) :
    |JNormalized (pureBoost θ)| ≤ 1 / (k : ℝ) ^ 2 := by
  have hbound := torsion_bound_continuous _ hadm
  rw [JNormalized_pow_amplify] at hbound
  have hk2 : 0 < (k : ℝ) ^ 2 := by
    have : 0 < (k : ℝ) := Nat.cast_pos.mpr hk
    positivity
  have hmul : |(k : ℝ) ^ 2 * JNormalized (pureBoost θ)| ≤ 1 := hbound
  rw [abs_mul, abs_of_pos hk2] at hmul
  exact (le_div_iff₀ hk2).mpr (by linarith [hmul])

/-- Continuous amplification contradiction for an arbitrary pure-boost seed. -/
theorem continuous_amplification_contradiction (θ : ℝ) {k : ℕ} (hk : 1 ≤ k)
    (hadm : IsAdmissibleContinuous (pureBoost (k * θ)))
    (hbig : (1 : ℝ) / (k : ℝ) ^ 2 < |JNormalized (pureBoost θ)|) :
    False :=
  not_le_of_gt hbig (amplification_implies_seed_le θ hk hadm)

/-! ### Discrete lattice height -/

theorem abs_latticeMismatch_ge_one {N : ℕ} [NeZero N] (t : DiscreteTorsion N)
    (hne : latticeMismatch t ≠ 0) : 1 ≤ |latticeMismatch t| :=
  Int.one_le_abs hne

theorem JNormalized_toTorsionParams_abs_eq {N : ℕ} [NeZero N] (t : DiscreteTorsion N) :
    |JNormalized (toTorsionParams t)| =
      (8 / (3 * Real.pi ^ 2)) * ((1 / 2) * (2 * Real.pi / N) ^ 2) *
        |(latticeMismatch t : ℝ)| := by
  unfold JNormalized
  have hcoef1 : 0 ≤ 8 / (3 * Real.pi ^ 2) := by positivity
  have hcoef2 : 0 ≤ (1 / 2 : ℝ) * (2 * Real.pi / N) ^ 2 := by positivity
  rw [J_toTorsionParams, abs_mul, abs_mul, abs_of_nonneg hcoef1, abs_of_nonneg hcoef2]
  ring

/-- Universal nonzero lattice height lower bound `ε_N = 16/(3N²)`. -/
theorem discrete_nonzero_height_lb {N : ℕ} [NeZero N] (t : DiscreteTorsion N)
    (hne : latticeMismatch t ≠ 0) :
    (16 : ℝ) / (3 * N ^ 2) ≤ |JNormalized (toTorsionParams t)| := by
  rw [JNormalized_toTorsionParams_abs_eq]
  have hLM : (1 : ℝ) ≤ |(latticeMismatch t : ℝ)| := by
    have : (1 : ℤ) ≤ |latticeMismatch t| := abs_latticeMismatch_ge_one t hne
    exact_mod_cast this
  have hfac :
      (8 / (3 * Real.pi ^ 2)) * ((1 / 2) * (2 * Real.pi / N) ^ 2) =
        (16 : ℝ) / (3 * (N : ℝ) ^ 2) := by
    field_simp
    ring
  rw [hfac]
  calc (16 : ℝ) / (3 * (N : ℝ) ^ 2)
      = (16 : ℝ) / (3 * (N : ℝ) ^ 2) * 1 := by ring
    _ ≤ (16 : ℝ) / (3 * (N : ℝ) ^ 2) * |(latticeMismatch t : ℝ)| := by
        gcongr

/-- Discrete amplification contradiction for an arbitrary amplification factor. -/
theorem discrete_amplification_contradiction {N : ℕ} [NeZero N] {k : ℕ} (hk : 1 ≤ k)
    (t : AdmissibleClass N)
    (hlb : (1 : ℝ) / (k : ℝ) ^ 2 < torsionHeight (AdmissibleClass.toParams t))
    (hadm :
      IsAdmissibleContinuous
        (scaleTorsion (k : ℝ) (AdmissibleClass.toParams t))) :
    False := by
  have hbound := torsion_bound_continuous _ hadm
  rw [JNormalized_scale] at hbound
  unfold torsionHeight at hlb
  have hk2 : 0 < (k : ℝ) ^ 2 := by
    have : 0 < (k : ℝ) := Nat.cast_pos.mpr hk
    positivity
  have hmul : |(k : ℝ) ^ 2 * JNormalized (AdmissibleClass.toParams t)| ≤ 1 := hbound
  rw [abs_mul, abs_of_pos hk2] at hmul
  have hle : |JNormalized (AdmissibleClass.toParams t)| ≤ 1 / (k : ℝ) ^ 2 :=
    (le_div_iff₀ hk2).mpr (by linarith [hmul])
  exact not_le_of_gt hlb hle

/-! ### Coarse torus threshold -/

/--
Exact coarse-torus criterion: `3N² < 16k²` makes the universal nonzero lattice
height `16/(3N²)` strictly larger than the amplification threshold `1/k²`.
-/
theorem coarse_height_gap {N k : ℕ} [NeZero N] (hk : 1 ≤ k)
    (hcoarse : 3 * N ^ 2 < 16 * k ^ 2) :
    (1 : ℝ) / (k : ℝ) ^ 2 < (16 : ℝ) / (3 * (N : ℝ) ^ 2) := by
  have hk2 : 0 < (k : ℝ) ^ 2 := by
    have : 0 < (k : ℝ) := Nat.cast_pos.mpr hk
    positivity
  have hNden : 0 < (3 : ℝ) * (N : ℝ) ^ 2 := by
    have : 0 < (N : ℝ) := Nat.cast_pos.mpr (NeZero.pos N)
    positivity
  rw [div_lt_div_iff₀ hk2 hNden]
  simpa only [one_mul] using (by exact_mod_cast hcoarse :
    (3 : ℝ) * (N : ℝ) ^ 2 < 16 * (k : ℝ) ^ 2)

/-- The simple linear choice `N ≤ 2k` satisfies the exact coarse-size criterion. -/
theorem coarse_condition_of_le_two_mul {N k : ℕ} (hk : 1 ≤ k)
    (hN : N ≤ 2 * k) : 3 * N ^ 2 < 16 * k ^ 2 := by
  have hsquare : N ^ 2 ≤ (2 * k) ^ 2 := Nat.pow_le_pow_left hN 2
  have hk2 : 0 < k ^ 2 := pow_pos (Nat.zero_lt_of_lt hk) 2
  nlinarith

theorem coarse_height_gap_of_le_two_mul {N k : ℕ} [NeZero N] (hk : 1 ≤ k)
    (hN : N ≤ 2 * k) :
    (1 : ℝ) / (k : ℝ) ^ 2 < (16 : ℝ) / (3 * (N : ℝ) ^ 2) :=
  coarse_height_gap hk (coarse_condition_of_le_two_mul hk hN)

/--
No nonzero lattice mismatch on a coarse torus can remain admissible after
`k`-fold scaling.
-/
theorem coarse_discrete_contradiction {N k : ℕ} [NeZero N] (hk : 1 ≤ k)
    (hcoarse : 3 * N ^ 2 < 16 * k ^ 2) (t : AdmissibleClass N)
    (hne : latticeMismatch t.val ≠ 0)
    (hadm :
      IsAdmissibleContinuous
        (scaleTorsion (k : ℝ) (AdmissibleClass.toParams t))) :
    False := by
  have hgap := coarse_height_gap hk hcoarse
  have hlb := discrete_nonzero_height_lb t.val hne
  have hseed :
      (1 : ℝ) / (k : ℝ) ^ 2 < torsionHeight (AdmissibleClass.toParams t) :=
    hgap.trans_le hlb
  exact discrete_amplification_contradiction hk t hseed hadm

/-! ### Coarse amplification witness (bridge payload) -/

/--
A discrete amplification certificate: a nonzero admissible lattice point that
remains continuously admissible after `k`-fold scaling.  On a coarse torus this
is already contradictory; problem-specific bridges only need to *produce* such a
witness from an integer solution.
-/
structure CoarseAmplificationWitness (N k : ℕ) [NeZero N] where
  t : AdmissibleClass N
  nonzero : latticeMismatch t.val ≠ 0
  admissible_after :
    IsAdmissibleContinuous (scaleTorsion (k : ℝ) (AdmissibleClass.toParams t))

theorem CoarseAmplificationWitness.false {N k : ℕ} [NeZero N] (hk : 1 ≤ k)
    (hcoarse : 3 * N ^ 2 < 16 * k ^ 2)
    (w : CoarseAmplificationWitness N k) : False :=
  coarse_discrete_contradiction hk hcoarse w.t w.nonzero w.admissible_after

end Framework

end DstDiophantine
