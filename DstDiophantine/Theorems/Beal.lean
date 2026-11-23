import DstDiophantine.Framework.Amplification
import DstDiophantine.Framework.Representation
import DstDiophantine.Framework.Lattice
import DstDiophantine.Embedding.PowerMap
import DstDiophantine.Embedding.Height
import DstDiophantine.Embedding.RotorClass
import DstDiophantine.Algebra.Amplification
import DstDiophantine.Algebra.ModularAmplification
import DstDiophantine.Algebra.Invariant
import DstDiophantine.Algebra.Discrete
import DstDiophantine.Algebra.Motor
import DstDiophantine.Theorems.Fermat
import DstDiophantine.Theorems.FermatLast
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.NumberTheory.FLT.Basic
import Mathlib.NumberTheory.PythagoreanTriples

/-!
# Amplification versus the admissible bound

A seed taller than `1/m²` cannot amplify inside the admissible bound. Classical Beal is not claimed;
what remains are the named residuals.
-/

namespace DstDiophantine

namespace Theorems

open Amplification Discrete Invariant ModularAmplification Framework Motor
open _root_.DstDiophantine.Embedding

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

theorem bealMinExp_pos {x y z : ℕ} (hx : 3 ≤ x) (hy : 3 ≤ y) (hz : 3 ≤ z) :
    0 < bealMinExp x y z :=
  Nat.zero_lt_of_lt (bealMinExp_ge_one hx hy hz)

/-- `max(m, 4)`: a modular witness needs `4 ≤ k`, so `m = 3` lifts to `k = 4`. -/
def bealAmpExp (x y z : ℕ) : ℕ :=
  max (bealMinExp x y z) 4

theorem bealAmpExp_ge_four (x y z : ℕ) : 4 ≤ bealAmpExp x y z :=
  le_max_right _ _

theorem bealMinExp_le_bealAmpExp (x y z : ℕ) : bealMinExp x y z ≤ bealAmpExp x y z :=
  le_max_left _ _

theorem bealAmpExp_eq_of_four_le {x y z : ℕ} (hm : 4 ≤ bealMinExp x y z) :
    bealAmpExp x y z = bealMinExp x y z :=
  max_eq_left hm

theorem bealAmpExp_eq_four_of_minExp_eq_three {x y z : ℕ}
    (hm : bealMinExp x y z = 3) : bealAmpExp x y z = 4 := by
  simp [bealAmpExp, hm]

theorem bealAmpExp_pos (x y z : ℕ) : 0 < bealAmpExp x y z :=
  Nat.lt_of_lt_of_le (by decide : 0 < 4) (bealAmpExp_ge_four x y z)

/-- Three-way gcd on absolute values (classical Beal coprimality). -/
def bealGcd (A B C : ℤ) : ℕ :=
  Nat.gcd A.natAbs (Nat.gcd B.natAbs C.natAbs)

theorem bealGcd_pos {A B C : ℤ} (hA : A ≠ 0) : 0 < bealGcd A B C :=
  Nat.gcd_pos_of_pos_left _ (Int.natAbs_pos.mpr hA)

theorem bealGcd_dvd_left (A B C : ℤ) : bealGcd A B C ∣ A.natAbs :=
  Nat.gcd_dvd_left _ _

theorem bealGcd_dvd_mid (A B C : ℤ) : bealGcd A B C ∣ B.natAbs :=
  Nat.dvd_trans (Nat.gcd_dvd_right A.natAbs _) (Nat.gcd_dvd_left B.natAbs C.natAbs)

theorem bealGcd_dvd_right (A B C : ℤ) : bealGcd A B C ∣ C.natAbs :=
  Nat.dvd_trans (Nat.gcd_dvd_right A.natAbs _) (Nat.gcd_dvd_right B.natAbs C.natAbs)

theorem exists_common_prime_of_bealGcd_gt_one {A B C : ℤ}
    (h : 1 < bealGcd A B C) :
    ∃ p : ℕ, Nat.Prime p ∧ p ∣ A.natAbs ∧ p ∣ B.natAbs ∧ p ∣ C.natAbs := by
  obtain ⟨p, hp, hdiv⟩ := Nat.exists_prime_and_dvd (ne_of_gt h)
  refine ⟨p, hp, ?_, ?_, ?_⟩
  · exact Nat.dvd_trans hdiv (bealGcd_dvd_left A B C)
  · exact Nat.dvd_trans hdiv (bealGcd_dvd_mid A B C)
  · exact Nat.dvd_trans hdiv (bealGcd_dvd_right A B C)

/-! ### Pairwise coprimality from three-way gcd + the equation -/

private theorem beal_natAbs_dvd_of_int_pow_dvd {n : ℤ} {e p : ℕ}
    (hp : Nat.Prime p) (h : (p : ℤ) ∣ n ^ e) : p ∣ n.natAbs := by
  have hAbs : p ∣ (n ^ e).natAbs := Int.natCast_dvd.mp h
  rw [Int.natAbs_pow] at hAbs
  exact hp.dvd_of_dvd_pow hAbs

private theorem beal_prime_dvd_B_of_dvd_AC {A B C : ℤ} {x y z p : ℕ}
    (hp : Nat.Prime p) (hx : 0 < x) (_hy : 0 < y) (hz : 0 < z)
    (hsol : A ^ x + B ^ y = C ^ z)
    (hpA : p ∣ A.natAbs) (hpC : p ∣ C.natAbs) : p ∣ B.natAbs := by
  have hAℤ : (p : ℤ) ∣ A := Int.natCast_dvd.mpr hpA
  have hCℤ : (p : ℤ) ∣ C := Int.natCast_dvd.mpr hpC
  have hBy : (p : ℤ) ∣ B ^ y := by
    have hsub : (p : ℤ) ∣ C ^ z - A ^ x :=
      dvd_sub (dvd_pow hCℤ (ne_of_gt hz)) (dvd_pow hAℤ (ne_of_gt hx))
    have heq : C ^ z - A ^ x = B ^ y := by
      simpa [add_sub_cancel_left] using
        (congrArg (fun t => t - A ^ x) hsol).symm
    rwa [heq] at hsub
  exact beal_natAbs_dvd_of_int_pow_dvd hp hBy

private theorem beal_prime_dvd_C_of_dvd_AB {A B C : ℤ} {x y z p : ℕ}
    (hp : Nat.Prime p) (hx : 0 < x) (hy : 0 < y) (_hz : 0 < z)
    (hsol : A ^ x + B ^ y = C ^ z)
    (hpA : p ∣ A.natAbs) (hpB : p ∣ B.natAbs) : p ∣ C.natAbs := by
  have hCz : (p : ℤ) ∣ C ^ z := by
    have : (p : ℤ) ∣ A ^ x + B ^ y :=
      dvd_add (dvd_pow (Int.natCast_dvd.mpr hpA) (ne_of_gt hx))
        (dvd_pow (Int.natCast_dvd.mpr hpB) (ne_of_gt hy))
    rwa [hsol] at this
  exact beal_natAbs_dvd_of_int_pow_dvd hp hCz

private theorem beal_prime_dvd_A_of_dvd_BC {A B C : ℤ} {x y z p : ℕ}
    (hp : Nat.Prime p) (_hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hsol : A ^ x + B ^ y = C ^ z)
    (hpB : p ∣ B.natAbs) (hpC : p ∣ C.natAbs) : p ∣ A.natAbs := by
  have hAx : (p : ℤ) ∣ A ^ x := by
    have hsub : (p : ℤ) ∣ C ^ z - B ^ y :=
      dvd_sub (dvd_pow (Int.natCast_dvd.mpr hpC) (ne_of_gt hz))
        (dvd_pow (Int.natCast_dvd.mpr hpB) (ne_of_gt hy))
    have heq : C ^ z - B ^ y = A ^ x := by
      simpa [add_comm, add_sub_cancel_right] using
        (congrArg (fun t => t - B ^ y) hsol).symm
    rwa [heq] at hsub
  exact beal_natAbs_dvd_of_int_pow_dvd hp hAx

private theorem beal_pair_coprime_of
    {A B C : ℤ} {u v : ℕ}
    (hpos : 0 < Nat.gcd u v) (hgcd : bealGcd A B C = 1)
    (hthird : ∀ p : ℕ, Nat.Prime p → p ∣ u → p ∣ v →
      p ∣ A.natAbs ∧ p ∣ B.natAbs ∧ p ∣ C.natAbs) :
    Nat.Coprime u v := by
  rw [Nat.coprime_iff_gcd_eq_one]
  by_contra hne
  have hgt : 1 < Nat.gcd u v :=
    lt_of_le_of_ne (Nat.succ_le_of_lt hpos) (Ne.symm hne)
  obtain ⟨p, hp, hdiv⟩ := Nat.exists_prime_and_dvd (ne_of_gt hgt)
  obtain ⟨hpA, hpB, hpC⟩ :=
    hthird p hp (Nat.dvd_trans hdiv (Nat.gcd_dvd_left _ _))
      (Nat.dvd_trans hdiv (Nat.gcd_dvd_right _ _))
  have hpG : p ∣ bealGcd A B C := Nat.dvd_gcd hpA (Nat.dvd_gcd hpB hpC)
  rw [hgcd] at hpG
  exact Nat.Prime.not_dvd_one hp hpG

theorem beal_pairwise_coprime {A B C : ℤ} {x y z : ℕ}
    (hA : A ≠ 0) (hB : B ≠ 0) (_hC : C ≠ 0)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hgcd : bealGcd A B C = 1)
    (hsol : A ^ x + B ^ y = C ^ z) :
    Nat.Coprime A.natAbs B.natAbs ∧
      Nat.Coprime A.natAbs C.natAbs ∧
        Nat.Coprime B.natAbs C.natAbs := by
  refine ⟨?_, ?_, ?_⟩
  · exact beal_pair_coprime_of (Nat.gcd_pos_of_pos_left _ (Int.natAbs_pos.mpr hA))
      hgcd fun p hp hpA hpB =>
        ⟨hpA, hpB, beal_prime_dvd_C_of_dvd_AB hp hx hy hz hsol hpA hpB⟩
  · exact beal_pair_coprime_of (Nat.gcd_pos_of_pos_left _ (Int.natAbs_pos.mpr hA))
      hgcd fun p hp hpA hpC =>
        ⟨hpA, beal_prime_dvd_B_of_dvd_AC hp hx hy hz hsol hpA hpC, hpC⟩
  · exact beal_pair_coprime_of (Nat.gcd_pos_of_pos_left _ (Int.natAbs_pos.mpr hB))
      hgcd fun p hp hpB hpC =>
        ⟨beal_prime_dvd_A_of_dvd_BC hp hx hy hz hsol hpB hpC, hpB, hpC⟩

theorem beal_coprime_ac {A B C : ℤ} {x y z : ℕ}
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hgcd : bealGcd A B C = 1) (hsol : A ^ x + B ^ y = C ^ z) :
    Nat.Coprime A.natAbs C.natAbs :=
  (beal_pairwise_coprime hA hB hC hx hy hz hgcd hsol).2.1

theorem beal_coprime_ab {A B C : ℤ} {x y z : ℕ}
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hgcd : bealGcd A B C = 1) (hsol : A ^ x + B ^ y = C ^ z) :
    Nat.Coprime A.natAbs B.natAbs :=
  (beal_pairwise_coprime hA hB hC hx hy hz hgcd hsol).1

theorem beal_coprime_bc {A B C : ℤ} {x y z : ℕ}
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hgcd : bealGcd A B C = 1) (hsol : A ^ x + B ^ y = C ^ z) :
    Nat.Coprime B.natAbs C.natAbs :=
  (beal_pairwise_coprime hA hB hC hx hy hz hgcd hsol).2.2

theorem bealGcd_eq_one_of_not_gt {A B C : ℤ} (hA : A ≠ 0)
    (hnot : ¬ 1 < bealGcd A B C) : bealGcd A B C = 1 := by
  have hle : bealGcd A B C ≤ 1 := Nat.not_lt.mp hnot
  exact le_antisymm hle (Nat.succ_le_of_lt (bealGcd_pos hA))

/-! ### Amplification vs admissible bound -/

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

/-! ### Continuous bridge (diagnostic) -/

/-- Diagnostic, unproved: a coprime solution would already exceed `1/m²`. -/
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

/-! ### Balanced-seed diagnostic (continuous obstruction) -/

theorem beal_balanced_seed_lt_threshold {x y z : ℕ}
    (hx : 3 ≤ x) (hy : 3 ≤ y) (hz : 3 ≤ z) :
    |JNormalized (pureBoost (Real.log 2 / (bealMinExp x y z : ℝ)))| <
      (1 : ℝ) / (bealMinExp x y z : ℝ) ^ 2 :=
  fermat_balanced_seed_lt_threshold (bealMinExp_ge_one hx hy hz)

theorem beal_balanced_amplification_admissible {x y z : ℕ}
    (hx : 3 ≤ x) (hy : 3 ≤ y) (hz : 3 ≤ z) :
    IsAdmissibleContinuous
      (pureBoost
        ((bealMinExp x y z : ℝ) *
          (Real.log 2 / (bealMinExp x y z : ℝ)))) :=
  fermat_balanced_amplification_admissible (bealMinExp_ge_one hx hy hz)

/-! ### Equal-exponent recovery toward FLT -/

theorem beal_eq_exp_motor (A B C : ℤ) (p : ℕ) :
    powerSumMotor (bealEquation A B C p p p) =
      powerSumMotor (fermatEquation A B C p) := by
  rw [bealEquation_eq_fermat]

theorem beal_eq_exp_not_coprime_of_bridge (hbridge : BealAdmissibleBridge)
    (A B C : ℤ) (p : ℕ) (hp : 3 ≤ p)
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hsol : A ^ p + B ^ p = C ^ p) :
    1 < bealGcd A B C :=
  beal_conjecture_of_bridge hbridge A B C p p p hp hp hp hA hB hC hsol

/-! ### Phase 7f: exponent-gcd reduction -/

/-- Exponent gcd `d = gcd(x, gcd(y, z))` used for Fermat / Pythagorean reduction. -/
def bealExpGcd (x y z : ℕ) : ℕ :=
  Nat.gcd x (Nat.gcd y z)

theorem bealExpGcd_dvd_left (x y z : ℕ) : bealExpGcd x y z ∣ x :=
  Nat.gcd_dvd_left _ _

theorem bealExpGcd_dvd_mid (x y z : ℕ) : bealExpGcd x y z ∣ y :=
  Nat.dvd_trans (Nat.gcd_dvd_right x _) (Nat.gcd_dvd_left y z)

theorem bealExpGcd_dvd_right (x y z : ℕ) : bealExpGcd x y z ∣ z :=
  Nat.dvd_trans (Nat.gcd_dvd_right x _) (Nat.gcd_dvd_right y z)

theorem bealExpGcd_pos {x y z : ℕ} (hx : 3 ≤ x) :
    0 < bealExpGcd x y z :=
  Nat.gcd_pos_of_pos_left _ (Nat.lt_of_lt_of_le (by decide : 0 < 3) hx)

theorem bealExpGcd_eq_of_eq_exp (p : ℕ) :
    bealExpGcd p p p = p := by
  simp [bealExpGcd]

/-! ### Phase 7g: exponent-gcd trichotomy -/

theorem bealExpGcd_eq_one_or_eq_two_or_ge_three {x y z : ℕ} (hx : 3 ≤ x) :
    bealExpGcd x y z = 1 ∨ bealExpGcd x y z = 2 ∨ 3 ≤ bealExpGcd x y z := by
  have hpos : 0 < bealExpGcd x y z := bealExpGcd_pos hx
  omega

theorem bealExpGcd_eq_one_implies_not_all_eq {x y z : ℕ}
    (hx : 3 ≤ x) (hd : bealExpGcd x y z = 1) : ¬ (x = y ∧ y = z) := by
  intro ⟨hxy, hyz⟩
  subst hxy; subst hyz
  have : bealExpGcd x x x = x := bealExpGcd_eq_of_eq_exp x
  omega

theorem bealExpGcd_eq_two_dvd {x y z : ℕ} (hd : bealExpGcd x y z = 2) :
    2 ∣ x ∧ 2 ∣ y ∧ 2 ∣ z :=
  ⟨by have := bealExpGcd_dvd_left x y z; rwa [hd] at this,
    by have := bealExpGcd_dvd_mid x y z; rwa [hd] at this,
    by have := bealExpGcd_dvd_right x y z; rwa [hd] at this⟩

theorem bealExpGcd_div_two_eq_one {x y z : ℕ}
    (hd : bealExpGcd x y z = 2) :
    bealExpGcd (x / 2) (y / 2) (z / 2) = 1 := by
  obtain ⟨hxdiv, hydiv, hzdiv⟩ := bealExpGcd_eq_two_dvd hd
  have hmul :
      bealExpGcd x y z = 2 * bealExpGcd (x / 2) (y / 2) (z / 2) := by
    unfold bealExpGcd
    calc Nat.gcd x (Nat.gcd y z)
        = Nat.gcd (2 * (x / 2)) (Nat.gcd (2 * (y / 2)) (2 * (z / 2))) := by
          rw [Nat.mul_div_cancel' hxdiv, Nat.mul_div_cancel' hydiv,
            Nat.mul_div_cancel' hzdiv]
      _ = Nat.gcd (2 * (x / 2)) (2 * Nat.gcd (y / 2) (z / 2)) := by
          rw [Nat.gcd_mul_left]
      _ = 2 * Nat.gcd (x / 2) (Nat.gcd (y / 2) (z / 2)) :=
          Nat.gcd_mul_left _ _ _
  omega

theorem beal_eq_pow_mul_expGcd (A B C : ℤ) (x y z : ℕ) :
    let d := bealExpGcd x y z
    A ^ x + B ^ y = C ^ z ↔
      (A ^ (x / d)) ^ d + (B ^ (y / d)) ^ d = (C ^ (z / d)) ^ d := by
  intro d
  have hx : d ∣ x := bealExpGcd_dvd_left x y z
  have hy : d ∣ y := bealExpGcd_dvd_mid x y z
  have hz : d ∣ z := bealExpGcd_dvd_right x y z
  have hx' : (A ^ (x / d)) ^ d = A ^ x := by
    rw [← pow_mul, Nat.mul_comm, Nat.mul_div_cancel' hx]
  have hy' : (B ^ (y / d)) ^ d = B ^ y := by
    rw [← pow_mul, Nat.mul_comm, Nat.mul_div_cancel' hy]
  have hz' : (C ^ (z / d)) ^ d = C ^ z := by
    rw [← pow_mul, Nat.mul_comm, Nat.mul_div_cancel' hz]
  constructor
  · intro hsol
    rw [hx', hy', hz', hsol]
  · intro hsol
    rw [← hx', ← hy', ← hz', hsol]

theorem bealGcd_pow_eq_one {A B C : ℤ} {p q r : ℕ}
    (hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
    (hgcd : bealGcd A B C = 1) :
    bealGcd (A ^ p) (B ^ q) (C ^ r) = 1 := by
  by_contra hne
  have hAne : A ≠ 0 := by
    intro hA0
    have hg' : Nat.gcd B.natAbs C.natAbs = 1 := by
      simpa [bealGcd, hA0] using hgcd
    have hBpow : (B ^ q).natAbs = B.natAbs ^ q := Int.natAbs_pow B q
    have hCpow : (C ^ r).natAbs = C.natAbs ^ r := Int.natAbs_pow C r
    have hcop : Nat.Coprime (B.natAbs ^ q) (C.natAbs ^ r) := by
      rw [Nat.coprime_pow_left_iff hq, Nat.coprime_comm,
        Nat.coprime_pow_left_iff hr, Nat.coprime_comm]
      exact hg'
    have : bealGcd (A ^ p) (B ^ q) (C ^ r) = 1 := by
      simp [bealGcd, hA0, zero_pow (ne_of_gt hp), hBpow, hCpow,
        Nat.coprime_iff_gcd_eq_one.mp hcop]
    exact hne this
  have hpos : 0 < bealGcd (A ^ p) (B ^ q) (C ^ r) :=
    bealGcd_pos (pow_ne_zero p hAne)
  have hgt : 1 < bealGcd (A ^ p) (B ^ q) (C ^ r) :=
    lt_of_le_of_ne (Nat.succ_le_of_lt hpos) (Ne.symm hne)
  obtain ⟨prime, hpPrime, hpAp, hpBq, hpCr⟩ :=
    exists_common_prime_of_bealGcd_gt_one hgt
  have hpA : prime ∣ A.natAbs := by
    have : prime ∣ (A ^ p).natAbs := hpAp
    rw [Int.natAbs_pow] at this
    exact hpPrime.dvd_of_dvd_pow this
  have hpB : prime ∣ B.natAbs := by
    have : prime ∣ (B ^ q).natAbs := hpBq
    rw [Int.natAbs_pow] at this
    exact hpPrime.dvd_of_dvd_pow this
  have hpC : prime ∣ C.natAbs := by
    have : prime ∣ (C ^ r).natAbs := hpCr
    rw [Int.natAbs_pow] at this
    exact hpPrime.dvd_of_dvd_pow this
  have hpG : prime ∣ bealGcd A B C := Nat.dvd_gcd hpA (Nat.dvd_gcd hpB hpC)
  rw [hgcd] at hpG
  exact Nat.Prime.not_dvd_one hpPrime hpG

theorem beal_fermat_of_expGcd_ge_three {A B C : ℤ} {x y z : ℕ}
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hsol : A ^ x + B ^ y = C ^ z) :
    let d := bealExpGcd x y z
    let α := A ^ (x / d)
    let β := B ^ (y / d)
    let γ := C ^ (z / d)
    α ≠ 0 ∧ β ≠ 0 ∧ γ ≠ 0 ∧
      α ^ d + β ^ d = γ ^ d := by
  intro d α β γ
  exact ⟨pow_ne_zero _ hA, pow_ne_zero _ hB, pow_ne_zero _ hC,
    (beal_eq_pow_mul_expGcd A B C x y z).mp hsol⟩

theorem not_beal_sol_of_expGcd_ge_three_of_FLT
    (hFLT : FermatLastTheorem) {A B C : ℤ} {x y z : ℕ}
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hd : 3 ≤ bealExpGcd x y z) :
    ¬ A ^ x + B ^ y = C ^ z := by
  intro hsol
  obtain ⟨hα, hβ, hγ, hF⟩ := beal_fermat_of_expGcd_ge_three hA hB hC hsol
  have hInt : FermatLastTheoremWith ℤ (bealExpGcd x y z) :=
    (fermatLastTheoremFor_iff_int).mp (hFLT (bealExpGcd x y z) hd)
  exact hInt _ _ _ hα hβ hγ hF

/-- Uses `fermatLastTheorem`; not a Lean proof of Wiles. -/
theorem not_beal_sol_of_expGcd_ge_three {A B C : ℤ} {x y z : ℕ}
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hd : 3 ≤ bealExpGcd x y z) :
    ¬ A ^ x + B ^ y = C ^ z :=
  not_beal_sol_of_expGcd_ge_three_of_FLT fermatLastTheorem hA hB hC hd

/-- Vacuous: solutions with `bealExpGcd ≥ 3` are already forbidden. -/
theorem beal_conjecture_of_expGcd_ge_three_of_FLT
    (hFLT : FermatLastTheorem) {A B C : ℤ} {x y z : ℕ}
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hd : 3 ≤ bealExpGcd x y z)
    (hsol : A ^ x + B ^ y = C ^ z) :
    1 < bealGcd A B C :=
  False.elim (not_beal_sol_of_expGcd_ge_three_of_FLT hFLT hA hB hC hd hsol)

theorem beal_conjecture_of_expGcd_ge_three {A B C : ℤ} {x y z : ℕ}
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hd : 3 ≤ bealExpGcd x y z)
    (hsol : A ^ x + B ^ y = C ^ z) :
    1 < bealGcd A B C :=
  beal_conjecture_of_expGcd_ge_three_of_FLT fermatLastTheorem hA hB hC hd hsol

theorem beal_eq_exp_not_sol_of_FLT (hFLT : FermatLastTheorem)
    {A B C : ℤ} {p : ℕ} (hp : 3 ≤ p)
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0) :
    ¬ A ^ p + B ^ p = C ^ p := by
  have hd : 3 ≤ bealExpGcd p p p := by
    rw [bealExpGcd_eq_of_eq_exp]; exact hp
  exact not_beal_sol_of_expGcd_ge_three_of_FLT hFLT hA hB hC hd

theorem beal_eq_exp_not_sol {A B C : ℤ} {p : ℕ} (hp : 3 ≤ p)
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0) :
    ¬ A ^ p + B ^ p = C ^ p :=
  beal_eq_exp_not_sol_of_FLT fermatLastTheorem hp hA hB hC

theorem not_beal_sol_of_expGcd_ge_three_of_modular_bridge
    (hbridge : FermatModularBridge) {A B C : ℤ} {x y z : ℕ}
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hd : 3 ≤ bealExpGcd x y z) :
    ¬ A ^ x + B ^ y = C ^ z :=
  not_beal_sol_of_expGcd_ge_three_of_FLT
    (FermatLastTheorem_of_modular_bridge hbridge) hA hB hC hd

theorem beal_pythagorean_of_expGcd_eq_two {A B C : ℤ} {x y z : ℕ}
    (hx : 3 ≤ x) (hy : 3 ≤ y) (hz : 3 ≤ z)
    (hd : bealExpGcd x y z = 2)
    (hsol : A ^ x + B ^ y = C ^ z) :
    let x' := x / 2
    let y' := y / 2
    let z' := z / 2
    2 ≤ x' ∧ 2 ≤ y' ∧ 2 ≤ z' ∧
      (A ^ x') ^ 2 + (B ^ y') ^ 2 = (C ^ z') ^ 2 := by
  intro x' y' z'
  obtain ⟨hxdiv, hydiv, hzdiv⟩ := bealExpGcd_eq_two_dvd hd
  have hx2 : 2 ≤ x / 2 := by omega
  have hy2 : 2 ≤ y / 2 := by omega
  have hz2 : 2 ≤ z / 2 := by omega
  have hsol' := (beal_eq_pow_mul_expGcd A B C x y z).mp hsol
  simp only [hd] at hsol'
  exact ⟨hx2, hy2, hz2, hsol'⟩

theorem beal_pythagoreanTriple_of_expGcd_eq_two {A B C : ℤ} {x y z : ℕ}
    (hx : 3 ≤ x) (hy : 3 ≤ y) (hz : 3 ≤ z)
    (hd : bealExpGcd x y z = 2)
    (hsol : A ^ x + B ^ y = C ^ z) :
    PythagoreanTriple (A ^ (x / 2)) (B ^ (y / 2)) (C ^ (z / 2)) := by
  obtain ⟨_, _, _, hsq⟩ := beal_pythagorean_of_expGcd_eq_two hx hy hz hd hsol
  simpa [PythagoreanTriple, sq] using hsq

theorem beal_pythagorean_legs_coprime_of_expGcd_eq_two {A B C : ℤ} {x y z : ℕ}
    (hx : 3 ≤ x) (hy : 3 ≤ y) (hz : 3 ≤ z)
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hgcd : bealGcd A B C = 1)
    (hd : bealExpGcd x y z = 2)
    (hsol : A ^ x + B ^ y = C ^ z) :
    Int.gcd (A ^ (x / 2)) (B ^ (y / 2)) = 1 := by
  have hx0 : 0 < x := Nat.lt_of_lt_of_le (by decide : 0 < 3) hx
  have hy0 : 0 < y := Nat.lt_of_lt_of_le (by decide : 0 < 3) hy
  have hz0 : 0 < z := Nat.lt_of_lt_of_le (by decide : 0 < 3) hz
  have hab := beal_coprime_ab hA hB hC hx0 hy0 hz0 hgcd hsol
  obtain ⟨hx2, hy2, _, _⟩ := beal_pythagorean_of_expGcd_eq_two hx hy hz hd hsol
  have hx2pos : 0 < x / 2 := Nat.lt_of_lt_of_le (by decide : 0 < 2) hx2
  have hy2pos : 0 < y / 2 := Nat.lt_of_lt_of_le (by decide : 0 < 2) hy2
  have hpow : Nat.Coprime (A.natAbs ^ (x / 2)) (B.natAbs ^ (y / 2)) := by
    rw [Nat.coprime_pow_left_iff hx2pos, Nat.coprime_comm,
      Nat.coprime_pow_left_iff hy2pos, Nat.coprime_comm]
    exact hab
  simpa [Int.gcd, Int.natAbs_pow] using Nat.coprime_iff_gcd_eq_one.mp hpow

/-- Parametrisation only; descent of `m, n` is not closed here. -/
theorem beal_pythagorean_classification_of_expGcd_eq_two {A B C : ℤ} {x y z : ℕ}
    (hx : 3 ≤ x) (hy : 3 ≤ y) (hz : 3 ≤ z)
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hgcd : bealGcd A B C = 1)
    (hd : bealExpGcd x y z = 2)
    (hsol : A ^ x + B ^ y = C ^ z) :
    ∃ m n : ℤ,
      (A ^ (x / 2) = m ^ 2 - n ^ 2 ∧ B ^ (y / 2) = 2 * m * n ∨
        A ^ (x / 2) = 2 * m * n ∧ B ^ (y / 2) = m ^ 2 - n ^ 2) ∧
        (C ^ (z / 2) = m ^ 2 + n ^ 2 ∨ C ^ (z / 2) = -(m ^ 2 + n ^ 2)) ∧
          Int.gcd m n = 1 ∧
            (m % 2 = 0 ∧ n % 2 = 1 ∨ m % 2 = 1 ∧ n % 2 = 0) := by
  have htrip := beal_pythagoreanTriple_of_expGcd_eq_two hx hy hz hd hsol
  have hleg := beal_pythagorean_legs_coprime_of_expGcd_eq_two hx hy hz
    hA hB hC hgcd hd hsol
  exact (PythagoreanTriple.coprime_classification).mp ⟨htrip, hleg⟩

/-! ### Phase 7g/7h: mixed-exponent residual (type + case splits) -/

/-- Open residual: no three-way-coprime solution with `bealExpGcd = 1`. -/
def BealMixedExpResidual : Prop :=
  ∀ (A B C : ℤ) (x y z : ℕ) (_hx : 3 ≤ x) (_hy : 3 ≤ y) (_hz : 3 ≤ z)
    (_hA : A ≠ 0) (_hB : B ≠ 0) (_hC : C ≠ 0),
    bealGcd A B C = 1 →
    bealExpGcd x y z = 1 →
      ¬ A ^ x + B ^ y = C ^ z

theorem beal_two_equal_exp_of_expGcd_eq_one {x y z : ℕ}
    (hx : 3 ≤ x) (hxy : x = y) (hd : bealExpGcd x y z = 1) :
    Nat.gcd x z = 1 ∧ x ≠ z := by
  subst hxy
  have hgcdxz : Nat.gcd x z = 1 := by
    have : bealExpGcd x x z = Nat.gcd x z := by
      unfold bealExpGcd
      rw [← Nat.gcd_assoc, Nat.gcd_self]
    rwa [← this]
  refine ⟨hgcdxz, ?_⟩
  intro heq
  subst heq
  have : bealExpGcd x x x = x := bealExpGcd_eq_of_eq_exp x
  omega

theorem beal_eq_two_exp_form_of_expGcd_eq_one {A B C : ℤ} {x y z : ℕ}
    (hx : 3 ≤ x) (hxy : x = y) (hd : bealExpGcd x y z = 1)
    (hsol : A ^ x + B ^ y = C ^ z) :
    Nat.gcd x z = 1 ∧ x ≠ z ∧ A ^ x + B ^ x = C ^ z := by
  obtain ⟨hg, hne⟩ := beal_two_equal_exp_of_expGcd_eq_one hx hxy hd
  exact ⟨hg, hne, by simpa [hxy] using hsol⟩

theorem beal_two_equal_exp_yz_of_expGcd_eq_one {x y z : ℕ}
    (hy : 3 ≤ y) (hyz : y = z) (hd : bealExpGcd x y z = 1) :
    Nat.gcd x y = 1 ∧ x ≠ y := by
  have hd' : bealExpGcd x y y = 1 := by simpa [hyz] using hd
  have hgcdxy : Nat.gcd x y = 1 := by
    have : bealExpGcd x y y = Nat.gcd x y := by
      unfold bealExpGcd
      rw [Nat.gcd_comm y y, Nat.gcd_self, Nat.gcd_comm]
    rwa [← this]
  refine ⟨hgcdxy, ?_⟩
  intro heq
  have : bealExpGcd y y y = y := bealExpGcd_eq_of_eq_exp y
  have hd'' : bealExpGcd y y y = 1 := by simpa [heq] using hd'
  omega

theorem beal_eq_two_exp_yz_form_of_expGcd_eq_one {A B C : ℤ} {x y z : ℕ}
    (hy : 3 ≤ y) (hyz : y = z) (hd : bealExpGcd x y z = 1)
    (hsol : A ^ x + B ^ y = C ^ z) :
    Nat.gcd x y = 1 ∧ x ≠ y ∧ A ^ x + B ^ y = C ^ y := by
  obtain ⟨hg, hne⟩ := beal_two_equal_exp_yz_of_expGcd_eq_one hy hyz hd
  exact ⟨hg, hne, by simpa [hyz] using hsol⟩

theorem beal_two_equal_exp_xz_of_expGcd_eq_one {x y z : ℕ}
    (hx : 3 ≤ x) (hxz : x = z) (hd : bealExpGcd x y z = 1) :
    Nat.gcd x y = 1 ∧ x ≠ y := by
  have hd' : bealExpGcd x y x = 1 := by simpa [hxz] using hd
  have hgcdxy : Nat.gcd x y = 1 := by
    have : bealExpGcd x y x = Nat.gcd x y := by
      unfold bealExpGcd
      rw [Nat.gcd_comm y x, ← Nat.gcd_assoc, Nat.gcd_self]
    rwa [← this]
  refine ⟨hgcdxy, ?_⟩
  intro heq
  have : bealExpGcd x x x = x := bealExpGcd_eq_of_eq_exp x
  have hd'' : bealExpGcd x x x = 1 := by simpa [heq] using hd'
  omega

theorem beal_eq_two_exp_xz_form_of_expGcd_eq_one {A B C : ℤ} {x y z : ℕ}
    (hx : 3 ≤ x) (hxz : x = z) (hd : bealExpGcd x y z = 1)
    (hsol : A ^ x + B ^ y = C ^ z) :
    Nat.gcd x y = 1 ∧ x ≠ y ∧ A ^ x + B ^ y = C ^ x := by
  obtain ⟨hg, hne⟩ := beal_two_equal_exp_xz_of_expGcd_eq_one hx hxz hd
  exact ⟨hg, hne, by simpa [hxz] using hsol⟩

theorem beal_expGcd_eq_one_two_equal_or_all_distinct {x y z : ℕ}
    (_hd : bealExpGcd x y z = 1) :
    x = y ∨ y = z ∨ x = z ∨ (x ≠ y ∧ y ≠ z ∧ x ≠ z) := by
  by_cases hxy : x = y
  · exact Or.inl hxy
  · by_cases hyz : y = z
    · exact Or.inr (Or.inl hyz)
    · by_cases hxz : x = z
      · exact Or.inr (Or.inr (Or.inl hxz))
      · exact Or.inr (Or.inr (Or.inr ⟨hxy, hyz, hxz⟩))

theorem beal_all_distinct_exp_of_expGcd_eq_one {x y z : ℕ}
    (hd : bealExpGcd x y z = 1)
    (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) :
    bealExpGcd x y z = 1 ∧ x ≠ y ∧ y ≠ z ∧ x ≠ z :=
  ⟨hd, hxy, hyz, hxz⟩

end Theorems

end DstDiophantine
