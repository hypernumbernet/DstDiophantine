import DstDiophantine.Framework.Amplification
import DstDiophantine.Framework.Representation
import DstDiophantine.Framework.Lattice
import DstDiophantine.Embedding.PowerMap
import DstDiophantine.Embedding.Height
import DstDiophantine.Algebra.Amplification
import DstDiophantine.Algebra.Invariant
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic.Linarith

/-!
# Phase 5: Beal's conjecture (problem-specific layer)

Amplification vs. admissible bound with minimal exponent `m = min(x,y,z)`,
together with the faithful null-translator encoding of `A^x + B^y - C^z`.
Shared no-go theorems come from `Framework.Amplification` (not from Fermat).

## Paper gap (not closed)

Classical Beal is **not** claimed unconditionally. Fractional-power mismatch
rotors, the three-term BCH formula, and prime-rotor cancellation are left
informal. The bridge from a coprime integer solution to an admissible amplified
pure-boost is `BealAdmissibleBridge` (unproved).
-/

namespace DstDiophantine

namespace Theorems

open Amplification Discrete Invariant
open _root_.DstDiophantine.Embedding
open _root_.DstDiophantine.Framework

/-! ### Additive sector -/

theorem beal_solution_iff_motor (A B C : ℤ) (x y z : ℕ) :
    A ^ x + B ^ y = C ^ z ↔ powerSumMotor (bealEquation A B C x y z) = 1 :=
  (bealMotor_one_iff A B C x y z).symm

/-! ### Minimal exponent -/

/-- Amplification factor used in Chapter 6: `m = min(x,y,z)`. -/
def bealMinExp (x y z : ℕ) : ℕ :=
  min x (min y z)

theorem bealMinExp_le_left (x y z : ℕ) : bealMinExp x y z ≤ x :=
  min_le_left _ _

theorem bealMinExp_le_mid (x y z : ℕ) : bealMinExp x y z ≤ y :=
  le_trans (min_le_right _ _) (min_le_left _ _)

theorem bealMinExp_le_right (x y z : ℕ) : bealMinExp x y z ≤ z :=
  le_trans (min_le_right _ _) (min_le_right _ _)

theorem bealMinExp_ge_three {x y z : ℕ} (hx : 3 ≤ x) (hy : 3 ≤ y) (hz : 3 ≤ z) :
    3 ≤ bealMinExp x y z :=
  le_min hx (le_min hy hz)

theorem bealMinExp_ge_one {x y z : ℕ} (hx : 3 ≤ x) (hy : 3 ≤ y) (hz : 3 ≤ z) :
    1 ≤ bealMinExp x y z :=
  Nat.le_trans (by decide : 1 ≤ 3) (bealMinExp_ge_three hx hy hz)

/-- Three-way gcd on absolute values (classical Beal coprimality). -/
def bealGcd (A B C : ℤ) : ℕ :=
  Nat.gcd A.natAbs (Nat.gcd B.natAbs C.natAbs)

theorem bealGcd_pos {A B C : ℤ} (hA : A ≠ 0) : 0 < bealGcd A B C :=
  Nat.gcd_pos_of_pos_left _ (Int.natAbs_pos.mpr hA)

/-! ### Amplification vs admissible bound -/

/-- Chapter 6 core: a seed taller than `1/m²` cannot amplify inside the admissible bound. -/
theorem beal_amplification_contradiction
    {A C : ℤ} (hA : A ≠ 0) (hC : C ≠ 0) {x y z : ℕ}
    (hx : 3 ≤ x) (hy : 3 ≤ y) (hz : 3 ≤ z)
    (hadm :
      IsAdmissibleContinuous
        (pureBoost
          ((bealMinExp x y z : ℝ) *
            (Real.log (Int.natAbs C) - Real.log (Int.natAbs A)))))
    (hbig :
      (1 : ℝ) / (bealMinExp x y z : ℝ) ^ 2 <
        |JNormalized (logMismatch A C hA hC)|) :
    False := by
  have hm1 : 1 ≤ bealMinExp x y z := bealMinExp_ge_one hx hy hz
  change (1 : ℝ) / (_ : ℝ) ^ 2 < |JNormalized (pureBoost _)| at hbig
  exact continuous_amplification_contradiction _ hm1 hadm hbig

/-- Discrete torus form via the shared amplification core. -/
theorem beal_discrete_amplification_contradiction {N : ℕ} [NeZero N] {x y z : ℕ}
    (hx : 3 ≤ x) (hy : 3 ≤ y) (hz : 3 ≤ z)
    (t : AdmissibleClass N)
    (hlb :
      (1 : ℝ) / (bealMinExp x y z : ℝ) ^ 2 <
        torsionHeight (AdmissibleClass.toParams t))
    (hadm :
      IsAdmissibleContinuous
        (scaleTorsion (bealMinExp x y z : ℝ) (AdmissibleClass.toParams t))) :
    False := by
  have hm1 : 1 ≤ bealMinExp x y z := bealMinExp_ge_one hx hy hz
  exact discrete_amplification_contradiction hm1 t hlb hadm

/-! ### Classical Beal under an explicit bridge hypothesis -/

/--
Paper Chapter 6's missing bridge: a putative coprime Beal solution produces an
admissible powered pure-boost mismatch whose seed already exceeds `1/m²`.

**Assumption (unproved).** Shared no-go:
`beal_amplification_contradiction`. Does **not** yield unconditional Beal.
-/
def BealAdmissibleBridge : Prop :=
  ∀ (A B C : ℤ) (x y z : ℕ) (_hx : 3 ≤ x) (_hy : 3 ≤ y) (_hz : 3 ≤ z)
    (hA : A ≠ 0) (_hB : B ≠ 0) (hC : C ≠ 0),
    bealGcd A B C = 1 →
    A ^ x + B ^ y = C ^ z →
      IsAdmissibleContinuous
          (pureBoost
            ((bealMinExp x y z : ℝ) *
              (Real.log (Int.natAbs C) - Real.log (Int.natAbs A)))) ∧
        (1 : ℝ) / (bealMinExp x y z : ℝ) ^ 2 <
          |JNormalized (logMismatch A C hA hC)|

/-- Conditional DST recovery of Beal's conjecture (common prime factor). -/
theorem beal_conjecture_of_bridge (hbridge : BealAdmissibleBridge) :
    ∀ (A B C : ℤ) (x y z : ℕ),
      3 ≤ x → 3 ≤ y → 3 ≤ z →
      A ≠ 0 → B ≠ 0 → C ≠ 0 →
      A ^ x + B ^ y = C ^ z →
      1 < bealGcd A B C := by
  intro A B C x y z hx hy hz hA hB hC hsol
  by_contra hnot
  have hle : bealGcd A B C ≤ 1 := Nat.not_lt.mp hnot
  have hpos : 0 < bealGcd A B C := bealGcd_pos hA
  have hcoprime : bealGcd A B C = 1 := le_antisymm hle (Nat.succ_le_of_lt hpos)
  have ⟨hadm, hbig⟩ := hbridge A B C x y z hx hy hz hA hB hC hcoprime hsol
  exact beal_amplification_contradiction hA hC hx hy hz hadm hbig

/-! ### Equal-exponent recovery toward FLT -/

/-- Equal exponents specialise Beal's additive motor to Fermat's. -/
theorem beal_eq_exp_motor (A B C : ℤ) (p : ℕ) :
    powerSumMotor (bealEquation A B C p p p) =
      powerSumMotor (fermatEquation A B C p) := by
  rw [bealEquation_eq_fermat]

/--
Under the Beal bridge, an equal-exponent solution with `p ≥ 3` cannot be
primitive (`bealGcd = 1`). Combined with Chapter 5's descent (excluding all
nonzero solutions under `FermatAdmissibleBridge`), this recovers FLT as the
equal-exponent case — still conditional on the bridges.
-/
theorem beal_eq_exp_not_coprime_of_bridge (hbridge : BealAdmissibleBridge)
    (A B C : ℤ) (p : ℕ) (hp : 3 ≤ p)
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hsol : A ^ p + B ^ p = C ^ p) :
    1 < bealGcd A B C :=
  beal_conjecture_of_bridge hbridge A B C p p p hp hp hp hA hB hC hsol

end Theorems

end DstDiophantine
