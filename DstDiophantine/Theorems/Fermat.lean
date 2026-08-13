import DstDiophantine.Framework.Amplification
import DstDiophantine.Framework.Representation
import DstDiophantine.Framework.Lattice
import DstDiophantine.Embedding.PowerMap
import DstDiophantine.Embedding.IntegerRotor
import DstDiophantine.Embedding.RotorClass
import DstDiophantine.Embedding.Height
import DstDiophantine.Algebra.Amplification
import DstDiophantine.Algebra.ModularAmplification
import DstDiophantine.Algebra.Invariant
import DstDiophantine.Algebra.Motor
import DstDiophantine.Algebra.Generators
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.FLT.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

/-!
# Phase 5–7: Fermat's Last Theorem (problem-specific layer)

Additive null encoding and Fermat-specific bridges / balanced-seed diagnostics.
Shared amplification no-go theorems live in `Framework.Amplification`; pure-boost
algebra lives in `Algebra.Amplification`.

## Paper gap (not closed)

Classical FLT is **not** claimed unconditionally. Continuous
`FermatAdmissibleBridge` is only a diagnostic device (false on the balanced
scale). The legacy `FermatCoarseDiscreteBridge` uses a structurally empty
payload (`CoarseAmplificationWitness.empty_of_coarse`). The live programme is
`FermatModularBridge`: a **solution-dependent** modular witness on
`quantizeMismatch`, together with the residual conformal-gauge gap
`ConformalGaugeAdmissible`.
-/

namespace DstDiophantine

namespace Theorems

open Amplification Discrete Invariant Motor Operations Generators ModularAmplification
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

/-! ### Balanced-seed diagnostic (continuous bridge obstruction) -/

private theorem log_two_nonneg : 0 ≤ Real.log 2 :=
  Real.log_nonneg (by norm_num)

private theorem log_two_lt_one : Real.log 2 < 1 := by
  have h := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) (by norm_num)
  norm_num at h ⊢
  exact h

/--
The dimensionless coefficient controlling the balanced seed is strictly below
one.  Proved from `log 2 < 1` and `3 < π`, without decimal approximations.
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
`1/p²` amplification contradiction.
-/
theorem fermat_balanced_seed_lt_threshold {p : ℕ} (hp : 1 ≤ p) :
    |JNormalized (pureBoost (Real.log 2 / (p : ℝ)))| < (1 : ℝ) / (p : ℝ) ^ 2 := by
  rw [fermat_balanced_seed_height_eq]
  have hp2 : 0 < (p : ℝ) ^ 2 := by
    have : 0 < (p : ℝ) := Nat.cast_pos.mpr hp
    positivity
  exact (div_lt_div_iff_of_pos_right hp2).mpr fermat_balanced_seed_constant_lt_one

/-- The balanced seed remains admissible after `p`-fold amplification. -/
theorem fermat_balanced_amplification_admissible {p : ℕ} (hp : 1 ≤ p) :
    IsAdmissibleContinuous (pureBoost (p * (Real.log 2 / (p : ℝ)))) := by
  have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt (Nat.zero_lt_of_lt hp))
  have hscale : (p : ℝ) * (Real.log 2 / (p : ℝ)) = Real.log 2 := by
    field_simp
  rw [hscale, isAdmissibleContinuous_pureBoost_iff]
  have hone_pi : (1 : ℝ) < Real.pi / 2 := by nlinarith [Real.pi_gt_three]
  exact ⟨log_two_nonneg, (log_two_lt_one.trans hone_pi).le⟩

/-! ### Fermat wrappers around the shared no-go core -/

/-- Fermat continuous core: tall log-mismatch seed cannot amplify admissibly. -/
theorem fermat_amplification_contradiction
    {a c : ℤ} (ha : a ≠ 0) (hc : c ≠ 0) {p : ℕ} (hp : 1 ≤ p)
    (hadm :
      IsAdmissibleContinuous
        (pureBoost (p * (Real.log (Int.natAbs c) - Real.log (Int.natAbs a)))))
    (hbig :
      (1 : ℝ) / (p : ℝ) ^ 2 < |JNormalized (logMismatch a c ha hc)|) :
    False := by
  change (1 : ℝ) / (p : ℝ) ^ 2 < |JNormalized (pureBoost _)| at hbig
  exact continuous_amplification_contradiction _ hp hadm hbig

/-- Fermat specialisation of the coarse height gap. -/
theorem fermat_coarse_height_gap {N p : ℕ} [NeZero N] (hp : 1 ≤ p)
    (hcoarse : 3 * N ^ 2 < 16 * p ^ 2) :
    (1 : ℝ) / (p : ℝ) ^ 2 < (16 : ℝ) / (3 * (N : ℝ) ^ 2) :=
  coarse_height_gap hp hcoarse

theorem fermat_coarse_condition_of_le_two_mul {N p : ℕ} (hp : 1 ≤ p)
    (hN : N ≤ 2 * p) : 3 * N ^ 2 < 16 * p ^ 2 :=
  coarse_condition_of_le_two_mul hp hN

theorem fermat_coarse_height_gap_of_le_two_mul {N p : ℕ} [NeZero N] (hp : 1 ≤ p)
    (hN : N ≤ 2 * p) :
    (1 : ℝ) / (p : ℝ) ^ 2 < (16 : ℝ) / (3 * (N : ℝ) ^ 2) :=
  coarse_height_gap_of_le_two_mul hp hN

theorem fermat_coarse_discrete_contradiction {N p : ℕ} [NeZero N] (hp : 1 ≤ p)
    (hcoarse : 3 * N ^ 2 < 16 * p ^ 2) (t : AdmissibleClass N)
    (hne : latticeMismatch t.val ≠ 0)
    (hadm :
      IsAdmissibleContinuous
        (scaleTorsion (p : ℝ) (AdmissibleClass.toParams t))) :
    False :=
  coarse_discrete_contradiction hp hcoarse t hne hadm

/-! ### Legacy coarse discrete bridge (structurally vacuous) -/

/--
**Legacy / diagnostic** coarse bridge.

* **Payload:** `CoarseAmplificationWitness N p` under `3N² < 16p²`.
* **Proved independently of any equation:** that payload is uninhabited
  (`CoarseAmplificationWitness.empty_of_coarse`).  Real `p`-fold scaling plus
  coarseness force every lattice coordinate to vanish.
* **Conditional wrapper:** `fermat_last_theorem_of_coarse_discrete_bridge`
  remains valid as a vacuous implication, but is not a mid-term research
  target: the same real-scaling design stays empty if reused elsewhere.
  The live quantisation programme uses modular wrapping
  (`Algebra.ModularAmplification`).
* **Does not claim:** unconditional classical FLT.
-/
def FermatCoarseDiscreteBridge : Prop :=
  ∀ (a b c : ℤ) (p : ℕ) (_hp : 3 ≤ p) (_ha : a ≠ 0) (_hb : b ≠ 0) (_hc : c ≠ 0),
    a ^ p + b ^ p = c ^ p →
      ∃ (N : ℕ) (hN : N ≠ 0),
        letI : NeZero N := ⟨hN⟩
        3 * N ^ 2 < 16 * p ^ 2 ∧ Nonempty (CoarseAmplificationWitness N p)

/--
Vacuous conditional recovery of classical FLT via the legacy coarse witness.
Under the coarse threshold the witness is already empty
(`CoarseAmplificationWitness.empty_of_coarse`), so the implication holds but
does not encode a viable quantisation map.
-/
theorem fermat_last_theorem_of_coarse_discrete_bridge
    (hbridge : FermatCoarseDiscreteBridge) :
    ∀ (a b c : ℤ) (p : ℕ), 3 ≤ p → a ≠ 0 → b ≠ 0 → c ≠ 0 →
      ¬ (a ^ p + b ^ p = c ^ p) := by
  intro a b c p hp ha hb hc hsol
  obtain ⟨N, hN, hcoarse, ⟨w⟩⟩ := hbridge a b c p hp ha hb hc hsol
  let : NeZero N := ⟨hN⟩
  have hp1 : 1 ≤ p := Nat.le_trans (by decide : 1 ≤ 3) hp
  exact CoarseAmplificationWitness.empty_of_coarse hp1 hcoarse w

/-! ### Classical FLT under continuous bridge (diagnostic only) -/

/--
Continuous diagnostic bridge (balanced-seed obstruction).

* **Assumption (unproved):** an FLT solution yields an admissible powered
  pure-boost whose seed already exceeds `1/p²`.
* **Proved core:** `fermat_amplification_contradiction` /
  `continuous_amplification_contradiction`.
* **Does not claim:** unconditional classical FLT. The seed inequality fails on
  the balanced model scale `θ = log 2 / p` (`fermat_balanced_seed_lt_threshold`).
-/
def FermatAdmissibleBridge : Prop :=
  ∀ (a b c : ℤ) (p : ℕ) (_hp : 3 ≤ p) (ha : a ≠ 0) (_hb : b ≠ 0) (hc : c ≠ 0),
    a ^ p + b ^ p = c ^ p →
      IsAdmissibleContinuous
          (pureBoost (p * (Real.log (Int.natAbs c) - Real.log (Int.natAbs a)))) ∧
        (1 : ℝ) / (p : ℝ) ^ 2 < |JNormalized (logMismatch a c ha hc)|

/-- Conditional DST recovery of Fermat's Last Theorem (continuous bridge). -/
theorem fermat_last_theorem_of_bridge (hbridge : FermatAdmissibleBridge) :
    ∀ (a b c : ℤ) (p : ℕ), 3 ≤ p → a ≠ 0 → b ≠ 0 → c ≠ 0 →
      ¬ (a ^ p + b ^ p = c ^ p) := by
  intro a b c p hp ha hb hc hsol
  have ⟨hadm, hbig⟩ := hbridge a b c p hp ha hb hc hsol
  have hp1 : 1 ≤ p := Nat.le_trans (by decide : 1 ≤ 3) hp
  exact fermat_amplification_contradiction ha hc hp1 hadm hbig

/-! ### Live modular bridge (solution-dependent payload) -/

/--
**Live modular bridge** (unproved).

* **Payload (solution-dependent):** the quantised log-mismatch
  `t := quantizeMismatch N a c` is admissible, carries a
  `ModularAmplificationWitness N p` with `w.t.val = t`, and the powered
  real-scale configuration is `ConformalGaugeAdmissible`.
* **Unlike** `FermatCoarseDiscreteBridge`: the witness type is inhabited in
  general (`ModularAmplificationWitness.nonempty_example`), but the bridge
  demands that the *solution's* quantised mismatch be that witness — not a
  fixed unrelated seed.
* **Unlike** merely asserting `Nonempty (ModularAmplificationWitness 16 5)`:
  the seed is tied to `(a,c)` via `quantizeMismatch`.
* **Proved core used by the conditional wrapper:**
  `ModularAmplificationWitness.not_admissible_real_scale` — nonzero winding
  rules out `ConformalGaugeAdmissible` under the present identification of
  conformal gauge with the PGA real-scale cone.
* **Residual gap:** whether a conformal / CGA gauge can make the third
  conjunct hold without collapsing to that obstruction (see `Algebra.CGA`).
* **Does not claim:** unconditional classical FLT.
-/
def FermatModularBridge : Prop :=
  ∀ (a b c : ℤ) (p : ℕ) (_hp : 3 ≤ p) (ha : a ≠ 0) (_hb : b ≠ 0) (hc : c ≠ 0),
    a ^ p + b ^ p = c ^ p →
      ∃ (N : ℕ) (hN : N ≠ 0),
        letI : NeZero N := ⟨hN⟩
        let t := Embedding.quantizeMismatch N a c ha hc
        IsAdmissible t ∧
          (∃ w : ModularAmplificationWitness N p, w.t.val = t) ∧
            ModularAmplification.ConformalGaugeAdmissible
              (scaleTorsion (p : ℝ) (toTorsionParams t))

/--
Conditional FLT from the modular bridge: a solution-dependent winding witness
cannot be conformally / real-scale admissible.
-/
theorem fermat_last_theorem_of_modular_bridge
    (hbridge : FermatModularBridge) :
    ∀ (a b c : ℤ) (p : ℕ), 3 ≤ p → a ≠ 0 → b ≠ 0 → c ≠ 0 →
      ¬ (a ^ p + b ^ p = c ^ p) := by
  intro a b c p hp ha hb hc hsol
  obtain ⟨N, hN, _hadm, ⟨w, hw⟩, hconf⟩ := hbridge a b c p hp ha hb hc hsol
  let : NeZero N := ⟨hN⟩
  have hnot :=
    ModularAmplification.ModularAmplificationWitness.not_admissible_real_scale w
  rw [hw] at hnot
  exact hnot hconf

/-! ### Mathlib FLT hypothesis (for Beal exponent-gcd reduction) -/

/--
Modular bridge implies mathlib's `FermatLastTheorem` (phase 7f).

Not an `axiom`: Beal's exponent-gcd reduction takes `FermatLastTheorem` as an
assumption. Mathlib states FLT over `ℕ`; we transport via
`fermatLastTheoremFor_iff_int`.
-/
theorem FermatLastTheorem_of_modular_bridge
    (hbridge : FermatModularBridge) : FermatLastTheorem := by
  intro n hn
  rw [fermatLastTheoremFor_iff_int]
  intro a b c ha hb hc
  exact fermat_last_theorem_of_modular_bridge hbridge a b c n hn ha hb hc

end Theorems

end DstDiophantine
