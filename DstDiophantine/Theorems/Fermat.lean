import DstDiophantine.Framework.Representation
import DstDiophantine.Framework.Lattice
import DstDiophantine.Embedding.PowerMap
import DstDiophantine.Embedding.IntegerRotor
import DstDiophantine.Embedding.Height
import DstDiophantine.Algebra.Amplification
import DstDiophantine.Algebra.Invariant
import DstDiophantine.Algebra.Motor
import DstDiophantine.Algebra.Generators
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

/-!
# Phase 5: Fermat's Last Theorem (DST amplification core)

We formalise Chapter 5 of `dst-diophantine.tex` as an **amplification vs.
admissible bound** argument on the pure-boost mismatch model, together with the
faithful null-translator encoding of `a^p + b^p - c^p`.

## Paper gap (not closed)

Classical FLT (`¬∃ a b c p, 3 ≤ p ∧ a^p+b^p=c^p` for nonzero integers) is **not**
claimed unconditionally. The paper identifies continuous integer-rotor mismatch
with an admissible configuration after powering; that bridge is recorded as
`FermatAdmissibleBridge` and left unproved. On fine discrete tori the minimal
nonzero height is `O(1/N²)`, which need not exceed `1/p²`, so the paper's uniform
`ε > Jbound/p²` step also fails without an extra hypothesis.

Phase 6 treats this bridge only as a temporary diagnostic device.  In particular,
the balanced scale `θ = log 2 / p` is admissible after amplification but its seed
height is strictly below `1/p²`; see `fermat_balanced_seed_lt_threshold`.  The
target remains an unconditional classical FLT theorem obtained from a redesigned
quantisation argument, not by postulating this bridge.
-/

namespace DstDiophantine

namespace Theorems

open Amplification Discrete Invariant Motor Operations Generators
open CliffordAlgebra PGA Real NormedSpace
open _root_.DstDiophantine.Embedding
open _root_.DstDiophantine.Framework

/-! ### Additive sector -/

theorem fermat_solution_iff_motor (a b c : ℤ) (p : ℕ) :
    a ^ p + b ^ p = c ^ p ↔ powerSumMotor (fermatEquation a b c p) = 1 :=
  (fermatMotor_one_iff a b c p).symm

theorem fermat_pos_lt {a b c : ℤ} {p : ℕ} (_hp : 1 ≤ p)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hsol : a ^ p + b ^ p = c ^ p) : a < c := by
  have hbp : 0 < b ^ p := pow_pos hb p
  have hlt : a ^ p < c ^ p := by
    have : a ^ p < a ^ p + b ^ p := lt_add_of_pos_right _ hbp
    rwa [hsol] at this
  have _ := ha
  exact lt_of_pow_lt_pow_left₀ p (le_of_lt hc) hlt

theorem fermat_pos_natAbs_ne {a b c : ℤ} {p : ℕ} (hp : 1 ≤ p)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hsol : a ^ p + b ^ p = c ^ p) : Int.natAbs a ≠ Int.natAbs c := by
  have hlt := fermat_pos_lt hp ha hb hc hsol
  have ha0 : 0 ≤ a := ha.le
  have hc0 : 0 ≤ c := hc.le
  intro heq
  have : a = c := by
    have ha' : (a.natAbs : ℤ) = a := Int.natAbs_of_nonneg ha0
    have hc' : (c.natAbs : ℤ) = c := Int.natAbs_of_nonneg hc0
    calc a = (a.natAbs : ℤ) := ha'.symm
      _ = (c.natAbs : ℤ) := by rw [heq]
      _ = c := hc'
  exact (ne_of_lt hlt) this

/-! ### Mismatch rotor ↔ pure boost -/

private theorem reverse_smul_hyperbolic0 (r : ℝ) :
    reverse (r • hyperbolic 0) = -(r • hyperbolic 0) := by
  rw [map_smul, hyperbolic_reverse, smul_neg]

private theorem reverse_integerRotor (n : ℤ) (hn : n ≠ 0) :
    reverse (integerRotor n hn) =
      exp (-(Real.log (Int.natAbs n) • hyperbolic 0)) := by
  rw [integerRotor_eq_exp, reverse_exp_of_reverse_neg (reverse_smul_hyperbolic0 _)]

private theorem commute_smul_hyperbolic0 (x y : ℝ) :
    Commute (x • hyperbolic 0) (y • hyperbolic 0) :=
  Generators.hyperbolic_smul_mul x y

theorem pureBoost_scale_real (c θ : ℝ) :
    pureBoost (c * θ) = scaleTorsion c (pureBoost θ) := by
  dsimp [pureBoost, scaleTorsion]
  congr <;> funext a <;> fin_cases a <;> simp

theorem mismatchRotor_eq_rotorTorsion (a c : ℤ) (ha : a ≠ 0) (hc : c ≠ 0) :
    mismatchRotor a c ha hc =
      rotorTorsion
        (pureBoost (2 * (Real.log (Int.natAbs c) - Real.log (Int.natAbs a)))) := by
  set la : ℝ := Real.log (Int.natAbs a)
  set lc : ℝ := Real.log (Int.natAbs c)
  have hrev := reverse_integerRotor a ha
  have hcommNeg : Commute (-(la • hyperbolic 0)) (lc • hyperbolic 0) :=
    (commute_smul_hyperbolic0 la lc).neg_left
  have hadd :
      -(la • hyperbolic 0) + lc • hyperbolic 0 = (lc - la) • hyperbolic 0 := by
    simp only [sub_eq_add_neg, ← neg_smul, ← add_smul]
    rw [add_comm (-la) lc]
  have hθ :
      (lc - la) • hyperbolic 0 =
        ((2 * (lc - la) / 2) • hyperbolic 0) := by
    congr 1
    ring
  calc mismatchRotor a c ha hc
      = reverse (integerRotor a ha) * integerRotor c hc := rfl
    _ = exp (-(la • hyperbolic 0)) * exp (lc • hyperbolic 0) := by
        rw [hrev, integerRotor_eq_exp]
    _ = exp (-(la • hyperbolic 0) + lc • hyperbolic 0) :=
        (exp_add_of_commute hcommNeg).symm
    _ = exp ((lc - la) • hyperbolic 0) := by rw [hadd]
    _ = exp ((2 * (lc - la) / 2) • hyperbolic 0) := by rw [hθ]
    _ = rotorTorsion (pureBoost (2 * (lc - la))) :=
        (rotorTorsion_pureBoost (2 * (lc - la))).symm

/-- Relates `mismatchRotor` to the `logMismatch` seed (factor-of-two convention). -/
theorem mismatchRotor_eq_logMismatch_scale (a c : ℤ) (ha : a ≠ 0) (hc : c ≠ 0) :
    mismatchRotor a c ha hc =
      rotorTorsion (scaleTorsion 2 (logMismatch a c ha hc)) := by
  rw [mismatchRotor_eq_rotorTorsion, logMismatch, ← pureBoost_scale_real]

theorem poweredMismatch_eq_rotorTorsion (a c : ℤ) (ha : a ≠ 0) (hc : c ≠ 0) (p : ℕ) :
    poweredMismatch a c ha hc p =
      rotorTorsion
        (pureBoost (p * (2 * (Real.log (Int.natAbs c) - Real.log (Int.natAbs a))))) := by
  rw [poweredMismatch, mismatchRotor_eq_rotorTorsion, ← rotorTorsion_pureBoost_pow]

/-! ### Amplification vs admissible bound -/

private theorem log_two_nonneg : 0 ≤ Real.log 2 :=
  Real.log_nonneg (by norm_num)

private theorem log_two_lt_one : Real.log 2 < 1 := by
  have h := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) (by norm_num)
  norm_num at h ⊢
  exact h

/-- A one-axis pure boost is admissible exactly on the non-negative half principal branch. -/
theorem isAdmissibleContinuous_pureBoost_iff (θ : ℝ) :
    IsAdmissibleContinuous (pureBoost θ) ↔ 0 ≤ θ ∧ θ ≤ Real.pi / 2 := by
  constructor
  · intro h
    simpa [pureBoost] using h (0 : Fin 3)
  · rintro ⟨hθ0, hθπ⟩ a
    have hhalf_pi : (0 : ℝ) ≤ Real.pi / 2 := by positivity
    fin_cases a <;> simp [pureBoost, hθ0, hθπ, hhalf_pi]

/--
The dimensionless coefficient controlling the balanced seed is strictly below
one.  This is proved from `log 2 < 1` and `3 < π`, without decimal approximations.
-/
theorem fermat_balanced_seed_constant_lt_one :
    (4 / (3 * Real.pi ^ 2)) * Real.log 2 ^ 2 < (1 : ℝ) := by
  have hnum : 4 * Real.log 2 ^ 2 < 4 := by
    nlinarith [log_two_nonneg, log_two_lt_one]
  have hden : 4 < 3 * Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
  rw [div_mul_eq_mul_div, div_lt_one (by positivity)]
  exact hnum.trans hden

/-- Exact height of the balanced scale `θ = log 2 / p`. -/
theorem fermat_balanced_seed_height_eq (p : ℕ) :
    |JNormalized (pureBoost (Real.log 2 / (p : ℝ)))| =
      ((4 / (3 * Real.pi ^ 2)) * Real.log 2 ^ 2) / (p : ℝ) ^ 2 := by
  rw [abs_of_nonneg (JNormalized_pureBoost_nonneg _), JNormalized_pureBoost]
  ring

/--
At the balanced scale, the present pure-boost seed is too small for the
`1/p²` amplification contradiction.  This mechanically records the obstruction
that motivates the phase-6 model/quantisation redesign.
-/
theorem fermat_balanced_seed_lt_threshold {p : ℕ} (hp : 1 ≤ p) :
    |JNormalized (pureBoost (Real.log 2 / (p : ℝ)))| < (1 : ℝ) / (p : ℝ) ^ 2 := by
  rw [fermat_balanced_seed_height_eq]
  have hp2 : 0 < (p : ℝ) ^ 2 := by
    have : 0 < (p : ℝ) := Nat.cast_pos.mpr hp
    positivity
  exact (div_lt_div_iff_of_pos_right hp2).mpr fermat_balanced_seed_constant_lt_one

/--
The balanced seed remains admissible after `p`-fold amplification.  Thus the
balanced obstruction is the seed threshold, not principal-branch admissibility.
-/
theorem fermat_balanced_amplification_admissible {p : ℕ} (hp : 1 ≤ p) :
    IsAdmissibleContinuous (pureBoost (p * (Real.log 2 / (p : ℝ)))) := by
  have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt (Nat.zero_lt_of_lt hp))
  have hscale : (p : ℝ) * (Real.log 2 / (p : ℝ)) = Real.log 2 := by
    field_simp
  rw [hscale, isAdmissibleContinuous_pureBoost_iff]
  have hone_pi : (1 : ℝ) < Real.pi / 2 := by nlinarith [Real.pi_gt_three]
  exact ⟨log_two_nonneg, (log_two_lt_one.trans hone_pi).le⟩

theorem amplification_implies_seed_le (θ : ℝ) {p : ℕ} (hp : 1 ≤ p)
    (hadm : IsAdmissibleContinuous (pureBoost (p * θ))) :
    |JNormalized (pureBoost θ)| ≤ 1 / (p : ℝ) ^ 2 := by
  have hbound := torsion_bound_continuous _ hadm
  rw [JNormalized_pow_amplify] at hbound
  have hp2 : 0 < (p : ℝ) ^ 2 := by
    have : 0 < (p : ℝ) := Nat.cast_pos.mpr hp
    positivity
  have hmul : |(p : ℝ) ^ 2 * JNormalized (pureBoost θ)| ≤ 1 := hbound
  rw [abs_mul, abs_of_pos hp2] at hmul
  exact (le_div_iff₀ hp2).mpr (by linarith [hmul])

/-- Chapter 5 core: a seed taller than `1/p²` cannot amplify inside the admissible bound. -/
theorem fermat_amplification_contradiction
    {a c : ℤ} (ha : a ≠ 0) (hc : c ≠ 0) {p : ℕ} (hp : 1 ≤ p)
    (hadm :
      IsAdmissibleContinuous
        (pureBoost (p * (Real.log (Int.natAbs c) - Real.log (Int.natAbs a)))))
    (hbig :
      (1 : ℝ) / (p : ℝ) ^ 2 < |JNormalized (logMismatch a c ha hc)|) :
    False := by
  have hle := amplification_implies_seed_le
    (Real.log (Int.natAbs c) - Real.log (Int.natAbs a)) hp hadm
  change (1 : ℝ) / (p : ℝ) ^ 2 < |JNormalized (pureBoost _)| at hbig
  exact not_le_of_gt hbig hle

/-! ### Discrete minimal height -/

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

theorem discrete_amplification_contradiction {N : ℕ} [NeZero N] {p : ℕ} (hp : 1 ≤ p)
    (t : AdmissibleClass N)
    (hlb : (1 : ℝ) / (p : ℝ) ^ 2 < torsionHeight (AdmissibleClass.toParams t))
    (hadm :
      IsAdmissibleContinuous
        (scaleTorsion (p : ℝ) (AdmissibleClass.toParams t))) :
    False := by
  have hbound := torsion_bound_continuous _ hadm
  rw [JNormalized_scale] at hbound
  unfold torsionHeight at hlb
  have hp2 : 0 < (p : ℝ) ^ 2 := by
    have : 0 < (p : ℝ) := Nat.cast_pos.mpr hp
    positivity
  have hmul : |(p : ℝ) ^ 2 * JNormalized (AdmissibleClass.toParams t)| ≤ 1 := hbound
  rw [abs_mul, abs_of_pos hp2] at hmul
  have hle : |JNormalized (AdmissibleClass.toParams t)| ≤ 1 / (p : ℝ) ^ 2 :=
    (le_div_iff₀ hp2).mpr (by linarith [hmul])
  exact not_le_of_gt hlb hle

/--
Exact coarse-torus criterion: `3N² < 16p²` makes the universal nonzero lattice
height `16/(3N²)` strictly larger than the amplification threshold `1/p²`.
-/
theorem fermat_coarse_height_gap {N p : ℕ} [NeZero N] (hp : 1 ≤ p)
    (hcoarse : 3 * N ^ 2 < 16 * p ^ 2) :
    (1 : ℝ) / (p : ℝ) ^ 2 < (16 : ℝ) / (3 * (N : ℝ) ^ 2) := by
  have hp2 : 0 < (p : ℝ) ^ 2 := by
    have : 0 < (p : ℝ) := Nat.cast_pos.mpr hp
    positivity
  have hNden : 0 < (3 : ℝ) * (N : ℝ) ^ 2 := by
    have : 0 < (N : ℝ) := Nat.cast_pos.mpr (NeZero.pos N)
    positivity
  rw [div_lt_div_iff₀ hp2 hNden]
  simpa only [one_mul] using (by exact_mod_cast hcoarse :
    (3 : ℝ) * (N : ℝ) ^ 2 < 16 * (p : ℝ) ^ 2)

/-- The simple linear choice `N ≤ 2p` satisfies the exact coarse-size criterion. -/
theorem fermat_coarse_condition_of_le_two_mul {N p : ℕ} (hp : 1 ≤ p)
    (hN : N ≤ 2 * p) : 3 * N ^ 2 < 16 * p ^ 2 := by
  have hsquare : N ^ 2 ≤ (2 * p) ^ 2 := Nat.pow_le_pow_left hN 2
  have hp2 : 0 < p ^ 2 := pow_pos (Nat.zero_lt_of_lt hp) 2
  nlinarith

/-- Convenient `N = O(p)` form of `fermat_coarse_height_gap`. -/
theorem fermat_coarse_height_gap_of_le_two_mul {N p : ℕ} [NeZero N] (hp : 1 ≤ p)
    (hN : N ≤ 2 * p) :
    (1 : ℝ) / (p : ℝ) ^ 2 < (16 : ℝ) / (3 * (N : ℝ) ^ 2) :=
  fermat_coarse_height_gap hp (fermat_coarse_condition_of_le_two_mul hp hN)

/--
No nonzero lattice mismatch on a coarse torus can remain admissible after
`p`-fold scaling.  This is the reusable contradiction behind the phase-6 bridge.
-/
theorem fermat_coarse_discrete_contradiction {N p : ℕ} [NeZero N] (hp : 1 ≤ p)
    (hcoarse : 3 * N ^ 2 < 16 * p ^ 2) (t : AdmissibleClass N)
    (hne : latticeMismatch t.val ≠ 0)
    (hadm :
      IsAdmissibleContinuous
        (scaleTorsion (p : ℝ) (AdmissibleClass.toParams t))) :
    False := by
  have hgap := fermat_coarse_height_gap hp hcoarse
  have hlb := discrete_nonzero_height_lb t.val hne
  have hseed :
      (1 : ℝ) / (p : ℝ) ^ 2 < torsionHeight (AdmissibleClass.toParams t) :=
    hgap.trans_le hlb
  exact discrete_amplification_contradiction hp t hseed hadm

/--
Phase-6 coarse quantisation bridge.  Unlike `FermatAdmissibleBridge`, this asks
only for a nonzero admissible lattice mismatch on some torus satisfying the
explicit coarse-size inequality.  Constructing this witness from an integer
solution is the remaining quantisation problem; this proposition is not assumed
by any unconditional theorem.
-/
def FermatCoarseDiscreteBridge : Prop :=
  ∀ (a b c : ℤ) (p : ℕ) (_hp : 3 ≤ p) (_ha : a ≠ 0) (_hb : b ≠ 0) (_hc : c ≠ 0),
    a ^ p + b ^ p = c ^ p →
      ∃ (N : ℕ) (hN : N ≠ 0),
        letI : NeZero N := ⟨hN⟩
        3 * N ^ 2 < 16 * p ^ 2 ∧
          ∃ t : AdmissibleClass N,
            latticeMismatch t.val ≠ 0 ∧
              IsAdmissibleContinuous
                (scaleTorsion (p : ℝ) (AdmissibleClass.toParams t))

/--
The coarse bridge is sufficient for classical FLT.  The proof uses only the
integer lattice lower bound and the already verified amplification bound.
-/
theorem fermat_last_theorem_of_coarse_discrete_bridge
    (hbridge : FermatCoarseDiscreteBridge) :
    ∀ (a b c : ℤ) (p : ℕ), 3 ≤ p → a ≠ 0 → b ≠ 0 → c ≠ 0 →
      ¬ (a ^ p + b ^ p = c ^ p) := by
  intro a b c p hp ha hb hc hsol
  obtain ⟨N, hN, hcoarse, t, hne, hadm⟩ := hbridge a b c p hp ha hb hc hsol
  let _ : NeZero N := ⟨hN⟩
  have hp1 : 1 ≤ p := Nat.le_trans (by decide : 1 ≤ 3) hp
  exact fermat_coarse_discrete_contradiction hp1 hcoarse t hne hadm

/-! ### Classical FLT under an explicit bridge hypothesis -/

/--
Paper Chapter 5's missing bridge: a putative nonzero Fermat solution produces an
admissible powered pure-boost mismatch whose seed already exceeds `1/p²`.

This proposition is **not** proved in this development and is only a temporary
diagnostic device.  Its seed inequality fails for the balanced model scale
`θ = log 2 / p`, as `fermat_balanced_seed_lt_threshold` proves, even though the
powered scale `log 2` is admissible by
`fermat_balanced_amplification_admissible`.  Phase 6 therefore targets the
coarse discrete quantisation bridge above and ultimately an unconditional FLT
theorem; this continuous bridge must not be declared true by fiat.
-/
def FermatAdmissibleBridge : Prop :=
  ∀ (a b c : ℤ) (p : ℕ) (_hp : 3 ≤ p) (ha : a ≠ 0) (_hb : b ≠ 0) (hc : c ≠ 0),
    a ^ p + b ^ p = c ^ p →
      IsAdmissibleContinuous
          (pureBoost (p * (Real.log (Int.natAbs c) - Real.log (Int.natAbs a)))) ∧
        (1 : ℝ) / (p : ℝ) ^ 2 < |JNormalized (logMismatch a c ha hc)|

/-- Conditional DST recovery of Fermat's Last Theorem. -/
theorem fermat_last_theorem_of_bridge (hbridge : FermatAdmissibleBridge) :
    ∀ (a b c : ℤ) (p : ℕ), 3 ≤ p → a ≠ 0 → b ≠ 0 → c ≠ 0 →
      ¬ (a ^ p + b ^ p = c ^ p) := by
  intro a b c p hp ha hb hc hsol
  have ⟨hadm, hbig⟩ := hbridge a b c p hp ha hb hc hsol
  have hp1 : 1 ≤ p := Nat.le_trans (by decide : 1 ≤ 3) hp
  exact fermat_amplification_contradiction ha hc hp1 hadm hbig

end Theorems

end DstDiophantine
