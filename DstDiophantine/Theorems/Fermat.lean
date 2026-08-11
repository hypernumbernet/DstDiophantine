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

theorem JNormalized_pureBoost_nonneg (θ : ℝ) :
    0 ≤ JNormalized (pureBoost θ) := by
  unfold JNormalized
  have hJ : 0 ≤ J (pureBoost θ) := by
    rw [J_pureBoost]
    positivity
  positivity

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

/-! ### Classical FLT under an explicit bridge hypothesis -/

/--
Paper Chapter 5's missing bridge: a putative nonzero Fermat solution produces an
admissible powered pure-boost mismatch whose seed already exceeds `1/p²`.

This proposition is **not** proved in this development.
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
