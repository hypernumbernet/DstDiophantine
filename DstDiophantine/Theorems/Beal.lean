import DstDiophantine.Framework.Amplification
import DstDiophantine.Framework.Representation
import DstDiophantine.Framework.Lattice
import DstDiophantine.Embedding.PowerMap
import DstDiophantine.Embedding.Height
import DstDiophantine.Embedding.RotorClass
import DstDiophantine.Embedding.ConformalInteger
import DstDiophantine.Algebra.Amplification
import DstDiophantine.Algebra.ModularAmplification
import DstDiophantine.Algebra.Invariant
import DstDiophantine.Algebra.Discrete
import DstDiophantine.Algebra.Motor
import DstDiophantine.Theorems.Fermat
import DstDiophantine.Theorems.FermatLast
import DstDiophantine.Theorems.Mihailescu
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.NumberTheory.FLT.Basic
import Mathlib.NumberTheory.PythagoreanTriples
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Amplification versus the admissible bound

A seed taller than `1/m²` cannot amplify inside the admissible bound. Classical Beal is not claimed;
what remains are the named residuals.
-/

namespace DstDiophantine

namespace Theorems

open Amplification Discrete Invariant Real ModularAmplification Framework Motor
open _root_.DstDiophantine.Embedding
open _root_.DstDiophantine.CGA
open CliffordAlgebra

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

/-! ### Fractional-power log gap (magnitude layer; no BCH) -/

/-- Fractional log-gap `δ = (z/m) log|C| − (x/m) log|A|`. -/
noncomputable def bealFracLogGap (A C : ℤ) (x z m : ℕ) : ℝ :=
  (z : ℝ) / m * Real.log (Int.natAbs C) - (x : ℝ) / m * Real.log (Int.natAbs A)

theorem bealFracLogGap_mul (A C : ℤ) (x z m : ℕ) (hm : m ≠ 0) :
    (m : ℝ) * bealFracLogGap A C x z m =
      (z : ℝ) * Real.log (Int.natAbs C) - (x : ℝ) * Real.log (Int.natAbs A) := by
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm
  unfold bealFracLogGap
  field_simp [hm0]

theorem beal_pos_pow_lt {A B C : ℤ} {x y z : ℕ}
    (_hA : 0 < A) (hB : 0 < B) (_hC : 0 < C)
    (hsol : A ^ x + B ^ y = C ^ z) : A ^ x < C ^ z := by
  have hBy : 0 < B ^ y := pow_pos hB y
  have hlt : A ^ x < A ^ x + B ^ y := lt_add_of_pos_right _ hBy
  rwa [hsol] at hlt

theorem bealFracLogGap_eq_log_div (A C : ℤ) (x z m : ℕ) (hm : m ≠ 0)
    (hA : 0 < A) (hC : 0 < C) :
    bealFracLogGap A C x z m =
      (1 / (m : ℝ)) *
        Real.log ((C.natAbs : ℝ) ^ z / (A.natAbs : ℝ) ^ x) := by
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm
  have hAabs : (0 : ℝ) < (A.natAbs : ℝ) :=
    Nat.cast_pos.mpr (Int.natAbs_pos.mpr hA.ne')
  have hCabs : (0 : ℝ) < (C.natAbs : ℝ) :=
    Nat.cast_pos.mpr (Int.natAbs_pos.mpr hC.ne')
  have hApow : (0 : ℝ) < (A.natAbs : ℝ) ^ x := pow_pos hAabs _
  have hCpow : (0 : ℝ) < (C.natAbs : ℝ) ^ z := pow_pos hCabs _
  have hlog :
      Real.log ((C.natAbs : ℝ) ^ z / (A.natAbs : ℝ) ^ x) =
        (z : ℝ) * Real.log (C.natAbs : ℝ) - (x : ℝ) * Real.log (A.natAbs : ℝ) := by
    rw [Real.log_div (ne_of_gt hCpow) (ne_of_gt hApow), Real.log_pow, Real.log_pow]
  have hmul := bealFracLogGap_mul A C x z m hm
  have hmul' :
      (m : ℝ) * bealFracLogGap A C x z m =
        (z : ℝ) * Real.log (C.natAbs : ℝ) - (x : ℝ) * Real.log (A.natAbs : ℝ) := by
    simpa using hmul
  have hgap :
      bealFracLogGap A C x z m =
        (1 / (m : ℝ)) *
          ((z : ℝ) * Real.log (C.natAbs : ℝ) - (x : ℝ) * Real.log (A.natAbs : ℝ)) := by
    field_simp [hm0] at hmul' ⊢
    linarith [hmul']
  rw [hgap, hlog]

theorem bealFracLogGap_of_solution {A B C : ℤ} {x y z m : ℕ} (hm : m ≠ 0)
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (hsol : A ^ x + B ^ y = C ^ z) :
    (m : ℝ) * bealFracLogGap A C x z m =
      Real.log (1 + (B : ℝ) ^ y / (A : ℝ) ^ x) := by
  have hAposR : (0 : ℝ) < A := Int.cast_pos.mpr hA
  have hApow : (0 : ℝ) < (A : ℝ) ^ x := pow_pos hAposR _
  have hsolR : (A : ℝ) ^ x + (B : ℝ) ^ y = (C : ℝ) ^ z := by exact_mod_cast hsol
  have hAn : (A.natAbs : ℝ) = (A : ℝ) := by
    rw [← Int.cast_natCast A.natAbs, Int.natAbs_of_nonneg hA.le]
  have hCn : (C.natAbs : ℝ) = (C : ℝ) := by
    rw [← Int.cast_natCast C.natAbs, Int.natAbs_of_nonneg hC.le]
  have hratio : (C.natAbs : ℝ) ^ z / (A.natAbs : ℝ) ^ x =
      1 + (B : ℝ) ^ y / (A : ℝ) ^ x := by
    calc (C.natAbs : ℝ) ^ z / (A.natAbs : ℝ) ^ x
        = (C : ℝ) ^ z / (A : ℝ) ^ x := by rw [hAn, hCn]
      _ = ((A : ℝ) ^ x + (B : ℝ) ^ y) / (A : ℝ) ^ x := by rw [← hsolR]
      _ = 1 + (B : ℝ) ^ y / (A : ℝ) ^ x := by field_simp [ne_of_gt hApow]
  have hgap := bealFracLogGap_eq_log_div A C x z m hm hA hC
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm
  calc (m : ℝ) * bealFracLogGap A C x z m
      = (m : ℝ) * ((1 / (m : ℝ)) *
          Real.log ((C.natAbs : ℝ) ^ z / (A.natAbs : ℝ) ^ x)) := by rw [hgap]
    _ = Real.log ((C.natAbs : ℝ) ^ z / (A.natAbs : ℝ) ^ x) := by field_simp [hm0]
    _ = Real.log (1 + (B : ℝ) ^ y / (A : ℝ) ^ x) := by rw [hratio]

theorem bealFracLogGap_eq_exp (A C : ℤ) (p : ℕ) (hp : p ≠ 0) :
    bealFracLogGap A C p p p =
      Real.log (Int.natAbs C) - Real.log (Int.natAbs A) := by
  have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp
  unfold bealFracLogGap
  field_simp [hp0]

theorem bealFracLogGap_eq_log_one_add_div {A B C : ℤ} {x y z m : ℕ} (hm : m ≠ 0)
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (hsol : A ^ x + B ^ y = C ^ z) :
    bealFracLogGap A C x z m =
      Real.log (1 + (B : ℝ) ^ y / (A : ℝ) ^ x) / (m : ℝ) := by
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm
  have hmul := bealFracLogGap_of_solution hm hA hB hC hsol
  field_simp [hm0] at hmul ⊢
  linarith [hmul]

theorem bealFracLogGap_pos_of_solution {A B C : ℤ} {x y z m : ℕ} (hm : m ≠ 0)
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (hsol : A ^ x + B ^ y = C ^ z) :
    0 < bealFracLogGap A C x z m := by
  have hApow : (0 : ℝ) < (A : ℝ) ^ x := pow_pos (Int.cast_pos.mpr hA) _
  have hBpow : (0 : ℝ) < (B : ℝ) ^ y := pow_pos (Int.cast_pos.mpr hB) _
  have hlog :
      0 < Real.log (1 + (B : ℝ) ^ y / (A : ℝ) ^ x) :=
    Real.log_pos (lt_add_of_pos_right 1 (div_pos hBpow hApow))
  rw [bealFracLogGap_eq_log_one_add_div hm hA hB hC hsol]
  exact div_pos hlog (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm))

theorem beal_winding_threshold_gt_half_pi_of_minExp_eq_three
    {x y z : ℕ} (hm : bealMinExp x y z = 3) :
    Real.pi / 2 < 2 * Real.pi / (bealMinExp x y z : ℝ) := by
  rw [hm]; nlinarith [Real.pi_pos]

theorem beal_balanced_fracGap_lt_winding_threshold {m : ℕ} (hm : 0 < m) :
    Real.log 2 / (m : ℝ) < 2 * Real.pi / (m : ℝ) := by
  have hlog : Real.log 2 < 2 * Real.pi := by
    have h1 : Real.log 2 < 1 := by
      have h := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) (by norm_num)
      norm_num at h ⊢; exact h
    exact h1.trans (by nlinarith [Real.pi_gt_three])
  exact div_lt_div_of_pos_right hlog (Nat.cast_pos.mpr hm)

theorem beal_balanced_fracGap_lt_ampExp_threshold {x y z : ℕ}
    (hx : 3 ≤ x) (hy : 3 ≤ y) (hz : 3 ≤ z) :
    Real.log 2 / (bealMinExp x y z : ℝ) <
      2 * Real.pi / (bealAmpExp x y z : ℝ) := by
  have hmR : (0 : ℝ) < bealMinExp x y z := Nat.cast_pos.mpr (bealMinExp_pos hx hy hz)
  have hkR : (0 : ℝ) < bealAmpExp x y z := Nat.cast_pos.mpr (bealAmpExp_pos x y z)
  have hlog1 : Real.log 2 < 1 := by
    have h := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) (by norm_num)
    norm_num at h ⊢; exact h
  have : Real.log 2 * (bealAmpExp x y z : ℝ) <
      2 * Real.pi * (bealMinExp x y z : ℝ) := by
    by_cases h4 : 4 ≤ bealMinExp x y z
    · have hkEq : bealAmpExp x y z = bealMinExp x y z := bealAmpExp_eq_of_four_le h4
      rw [hkEq]
      nlinarith [hlog1, Real.pi_gt_three, hmR]
    · have hm3 : bealMinExp x y z = 3 := by
        have hge : 3 ≤ bealMinExp x y z := bealMinExp_ge_three hx hy hz
        have hlt : bealMinExp x y z < 4 := Nat.not_le.mp h4
        omega
      have hk4 : bealAmpExp x y z = 4 := bealAmpExp_eq_four_of_minExp_eq_three hm3
      rw [hm3, hk4]
      have hπ : (3 : ℝ) < Real.pi := Real.pi_gt_three
      have : (4 : ℝ) * Real.log 2 < 6 * Real.pi := by
        nlinarith [hlog1, hπ]
      convert this using 1 <;> ring
  exact (div_lt_div_iff₀ hmR hkR).mpr this

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

/-! ### Quantised fractional gap -/

/-- Quantise the Beal fractional log-gap to a pure-boost lattice seed. -/
noncomputable def quantizeBealMismatch (N : ℕ) [NeZero N] (A C : ℤ) (x z m : ℕ) :
    DiscreteTorsion N :=
  pureBoostSeedOfRapidity N (bealFracLogGap A C x z m)

theorem quantizeBealMismatch_pureBoost (N : ℕ) [NeZero N] (A C : ℤ) (x z m : ℕ) :
    IsPureBoostSeed (quantizeBealMismatch N A C x z m) :=
  pureBoostSeedOfRapidity_isPureBoost N _

/-! ### Diagnostic modular bridge (payload-incompatible) -/

/-- Diagnostic only: winding and `ConformalGaugeAdmissible` are incompatible. -/
def BealModularBridge : Prop :=
  ∀ (A B C : ℤ) (x y z : ℕ) (_hx : 3 ≤ x) (_hy : 3 ≤ y) (_hz : 3 ≤ z)
    (_hA : A ≠ 0) (_hB : B ≠ 0) (_hC : C ≠ 0),
    bealGcd A B C = 1 →
    A ^ x + B ^ y = C ^ z →
      ∃ (N : ℕ) (hN : N ≠ 0),
        letI : NeZero N := ⟨hN⟩
        let m := bealMinExp x y z
        let t := quantizeBealMismatch N A C x z m
        IsAdmissible t ∧
          (∃ w : ModularAmplificationWitness N m, w.t.val = t) ∧
            ConformalGaugeAdmissible
              (scaleTorsion (m : ℝ) (toTorsionParams t))

theorem beal_modular_payload_incompatible {N k : ℕ} [NeZero N]
    (w : ModularAmplificationWitness N k) :
    ¬ ConformalGaugeAdmissible
        (scaleTorsion (k : ℝ) (toTorsionParams w.t.val)) :=
  ModularAmplificationWitness.not_admissible_real_scale w

theorem beal_conjecture_of_modular_bridge (hbridge : BealModularBridge) :
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
  obtain ⟨N, hN, _hadm, ⟨w, hw⟩, hconf⟩ :=
    hbridge A B C x y z hx hy hz hA hB hC hcoprime hsol
  let : NeZero N := ⟨hN⟩
  have hnot' := beal_modular_payload_incompatible w
  rw [hw] at hnot'
  exact hnot' hconf

theorem beal_eq_exp_not_coprime_of_modular_bridge (hbridge : BealModularBridge)
    (A B C : ℤ) (p : ℕ) (hp : 3 ≤ p)
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hsol : A ^ p + B ^ p = C ^ p) :
    1 < bealGcd A B C :=
  beal_conjecture_of_modular_bridge hbridge A B C p p p hp hp hp hA hB hC hsol

/-! ### Partial winding on the principal interval -/

theorem beal_has_winding_of_fracGap_ge (N k m : ℕ) [NeZero N] (hk : 0 < k)
    (A C : ℤ) (x z : ℕ)
    (hle : 2 * Real.pi / k ≤ bealFracLogGap A C x z m)
    (hlt : bealFracLogGap A C x z m < 2 * Real.pi)
    (hdvd : k ∣ N) :
    windingTotal k (quantizeBealMismatch N A C x z m) ≠ 0 := by
  have hπk : 0 ≤ 2 * Real.pi / k :=
    div_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) Real.pi_pos.le) (Nat.cast_nonneg _)
  have h0 : 0 ≤ bealFracLogGap A C x z m := le_trans hπk hle
  simpa [quantizeBealMismatch] using
    windingTotal_ne_zero_of_rapidity_ge
      N k hk (bealFracLogGap A C x z m) h0 hle hlt hdvd

/-! ### Window-regime winding bridge (diagnostic for full solutions) -/

/-- Window-regime diagnostic, not a full-solution bridge. -/
def BealWindingBridge : Prop :=
  ∀ (A B C : ℤ) (x y z : ℕ) (_hx : 3 ≤ x) (_hy : 3 ≤ y) (_hz : 3 ≤ z)
    (_hA : A ≠ 0) (_hB : B ≠ 0) (_hC : C ≠ 0),
    bealGcd A B C = 1 →
    A ^ x + B ^ y = C ^ z →
      ∃ (N : ℕ) (hN : N ≠ 0),
        letI : NeZero N := ⟨hN⟩
        let m := bealMinExp x y z
        let k := bealAmpExp x y z
        let t := quantizeBealMismatch N A C x z m
        IsAdmissible t ∧ ∃ w : ModularAmplificationWitness N k, w.t.val = t

/-! ### CGA fractional-power magnitudes and triple Fermat form -/

/-- Fractional-power magnitude `|n|^{e/m}` used as a 1D CGA null-cone seed. -/
noncomputable def bealRootMag (n : ℤ) (e m : ℕ) : ℝ :=
  (n.natAbs : ℝ) ^ ((e : ℝ) / m)

theorem bealRootMag_pos {n : ℤ} (hn : n ≠ 0) (e m : ℕ) :
    0 < bealRootMag n e m := by
  unfold bealRootMag
  exact Real.rpow_pos_of_pos (Nat.cast_pos.mpr (Int.natAbs_pos.mpr hn)) _

theorem bealRootMag_pow (n : ℤ) (e m : ℕ) (hm : m ≠ 0) :
    bealRootMag n e m ^ m = (n.natAbs : ℝ) ^ e := by
  unfold bealRootMag
  have hnn : (0 : ℝ) ≤ (n.natAbs : ℝ) := Nat.cast_nonneg _
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm
  have hmul : ((e : ℝ) / m) * m = e := by field_simp [hm0]
  rw [← Real.rpow_natCast _ m, ← Real.rpow_mul hnn, hmul, Real.rpow_natCast]

theorem bealRootMag_eq_natAbs (n : ℤ) (p : ℕ) (hp : p ≠ 0) :
    bealRootMag n p p = (n.natAbs : ℝ) := by
  unfold bealRootMag
  have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp
  have : (p : ℝ) / p = 1 := by field_simp [hp0]
  rw [this, Real.rpow_one]

theorem bealFracLogGap_eq_log_rootMag (A C : ℤ) (x z m : ℕ)
    (hA : A ≠ 0) (hC : C ≠ 0) :
    bealFracLogGap A C x z m =
      Real.log (bealRootMag C z m) - Real.log (bealRootMag A x m) := by
  have hAabs : (0 : ℝ) < (A.natAbs : ℝ) :=
    Nat.cast_pos.mpr (Int.natAbs_pos.mpr hA)
  have hCabs : (0 : ℝ) < (C.natAbs : ℝ) :=
    Nat.cast_pos.mpr (Int.natAbs_pos.mpr hC)
  unfold bealFracLogGap bealRootMag
  rw [Real.log_rpow hCabs, Real.log_rpow hAabs]

theorem beal_rootMag_pow_sum_of_solution {A B C : ℤ} {x y z m : ℕ}
    (hm : m ≠ 0) (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (hsol : A ^ x + B ^ y = C ^ z) :
    bealRootMag A x m ^ m + bealRootMag B y m ^ m =
      bealRootMag C z m ^ m := by
  have hAn : (A.natAbs : ℝ) = (A : ℝ) := by
    rw [← Int.cast_natCast A.natAbs, Int.natAbs_of_nonneg hA.le]
  have hBn : (B.natAbs : ℝ) = (B : ℝ) := by
    rw [← Int.cast_natCast B.natAbs, Int.natAbs_of_nonneg hB.le]
  have hCn : (C.natAbs : ℝ) = (C : ℝ) := by
    rw [← Int.cast_natCast C.natAbs, Int.natAbs_of_nonneg hC.le]
  have hsolR : (A : ℝ) ^ x + (B : ℝ) ^ y = (C : ℝ) ^ z := by exact_mod_cast hsol
  rw [bealRootMag_pow A x m hm, bealRootMag_pow B y m hm, bealRootMag_pow C z m hm,
    hAn, hBn, hCn, hsolR]

theorem bealRootMag_isCGAPowerLatticePoint (A : ℤ) (x m : ℕ)
    (hA : A ≠ 0) (hm : m ≠ 0) :
    IsCGAPowerLatticePoint (bealRootMag A x m) m :=
  ⟨(A.natAbs : ℤ) ^ x,
    pow_ne_zero x (by exact_mod_cast ne_of_gt (Int.natAbs_pos.mpr hA)),
    by
      rw [bealRootMag_pow A x m hm]
      exact (Int.cast_pow (A.natAbs : ℤ) x).symm⟩

/-- Scale-invariant CGA mismatch of the A–C Beal dilation. -/
noncomputable def bealCGADilationMismatch (A C : ℤ) (x z m : ℕ) : ℝ :=
  cgaDilationMismatch (bealFracLogGap A C x z m)

theorem bealCGADilationMismatch_pos_of_solution {A B C : ℤ} {x y z m : ℕ}
    (hm : m ≠ 0) (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (hsol : A ^ x + B ^ y = C ^ z) :
    0 < bealCGADilationMismatch A C x z m := by
  unfold bealCGADilationMismatch
  exact CGA.CGA1.cgaDilationMismatch_pos_of_ne_zero
    (ne_of_gt (bealFracLogGap_pos_of_solution hm hA hB hC hsol))

/-! ### Diagnostic tautological CGA gauge (always true) -/

/-- Diagnostic: always-true null embedding. Not a live no-go. -/
def BealCGAGauge (A C : ℤ) (x z m : ℕ) : Prop :=
  conformalPoint (bealRootMag A x m) * conformalPoint (bealRootMag A x m) = 0 ∧
    conformalPoint (bealRootMag C z m) * conformalPoint (bealRootMag C z m) = 0

theorem BealCGAGauge_of_ne_zero (A C : ℤ) (x z m : ℕ) :
    BealCGAGauge A C x z m :=
  ⟨conformalPoint_sq _, conformalPoint_sq _⟩

theorem beal_cga_dilation_weights (A C : ℤ) (x z m : ℕ)
    (hA : A ≠ 0) (hC : C ≠ 0) :
    let δ := bealFracLogGap A C x z m
    let a := bealRootMag A x m
    conformalPoint (bealRootMag C z m) =
      CliffordAlgebra.ι Q21
        (CGA1.n0Vec + Real.exp δ • (a • CGA1.eLineVec)
          + (Real.exp δ) ^ 2 • ((1 / 2 * a ^ 2) • CGA1.nInfVec)) := by
  intro δ a
  have ha : 0 < a := bealRootMag_pos hA x m
  have hδ : δ = Real.log (bealRootMag C z m) - Real.log a :=
    bealFracLogGap_eq_log_rootMag A C x z m hA hC
  have hCpos : 0 < bealRootMag C z m := bealRootMag_pos hC z m
  have hexp : Real.exp δ * a = bealRootMag C z m := by
    rw [hδ, Real.exp_sub, Real.exp_log hCpos, Real.exp_log ha]
    field_simp [ne_of_gt ha]
  rw [← hexp, conformalPoint_smul]

theorem beal_cga_k_fold_dilation (A C : ℤ) (x z m k : ℕ) :
    let δ := bealFracLogGap A C x z m
    let a := bealRootMag A x m
    CGA1.pointVec (Real.exp ((k : ℝ) * δ) * a) =
      CGA1.pointVec (Real.exp δ ^ k * a) := by
  intro δ a
  exact CGA1.pointVec_exp_nat_mul a δ k

/-! ### Non-tautological DST integer null lattice gauge -/

/-- Integer null-lattice gauge. Not `IsAdmissibleContinuous`. -/
def BealCGALatticeGauge (A B C : ℤ) (x y z m : ℕ) : Prop :=
  IsCGAIntegerPoint (bealRootMag A x m) ∧
    IsCGAIntegerPoint (bealRootMag B y m) ∧
      IsCGAIntegerPoint (bealRootMag C z m)

theorem BealCGALatticeGauge_of_eq_exp (A B C : ℤ) (p : ℕ) (hp : p ≠ 0)
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0) :
    BealCGALatticeGauge A B C p p p p := by
  refine ⟨?_, ?_, ?_⟩
  · exact IsCGAIntegerPoint_of_eq (by exact_mod_cast ne_of_gt (Int.natAbs_pos.mpr hA))
      (bealRootMag_eq_natAbs A p hp)
  · exact IsCGAIntegerPoint_of_eq (by exact_mod_cast ne_of_gt (Int.natAbs_pos.mpr hB))
      (bealRootMag_eq_natAbs B p hp)
  · exact IsCGAIntegerPoint_of_eq (by exact_mod_cast ne_of_gt (Int.natAbs_pos.mpr hC))
      (bealRootMag_eq_natAbs C p hp)

theorem beal_eq_exp_lattice_fermat_form {A B C : ℤ} {p : ℕ} (hp : p ≠ 0)
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (hsol : A ^ p + B ^ p = C ^ p) :
    ∃ (α β γ : ℤ), α ≠ 0 ∧ β ≠ 0 ∧ γ ≠ 0 ∧
      α ^ p + β ^ p = γ ^ p ∧
        bealRootMag A p p = α ∧ bealRootMag B p p = β ∧
          bealRootMag C p p = γ := by
  refine ⟨(A.natAbs : ℤ), (B.natAbs : ℤ), (C.natAbs : ℤ),
    by exact_mod_cast ne_of_gt (Int.natAbs_pos.mpr hA.ne'),
    by exact_mod_cast ne_of_gt (Int.natAbs_pos.mpr hB.ne'),
    by exact_mod_cast ne_of_gt (Int.natAbs_pos.mpr hC.ne'), ?_,
    bealRootMag_eq_natAbs A p hp, bealRootMag_eq_natAbs B p hp,
    bealRootMag_eq_natAbs C p hp⟩
  have hpow := beal_rootMag_pow_sum_of_solution hp hA hB hC hsol
  have hA' := bealRootMag_eq_natAbs A p hp
  have hB' := bealRootMag_eq_natAbs B p hp
  have hC' := bealRootMag_eq_natAbs C p hp
  have : ((A.natAbs : ℤ) : ℝ) ^ p + ((B.natAbs : ℤ) : ℝ) ^ p =
      ((C.natAbs : ℤ) : ℝ) ^ p := by
    simpa [hA', hB', hC'] using hpow
  exact_mod_cast this

/-- Diagnostic: `2^{4/3}` misses the integer lattice. -/
theorem not_BealCGALatticeGauge_two_two_two_four_four_three :
    ¬ BealCGALatticeGauge 2 2 2 4 4 3 3 := by
  intro h
  have : IsCGAIntegerPoint (bealRootMag 2 4 3) := h.1
  unfold bealRootMag at this
  change IsCGAIntegerPoint ((2 : ℝ) ^ ((4 : ℝ) / 3)) at this
  exact not_isCGAIntegerPoint_two_rpow_four_thirds this

/-! ### Diagnostic / live CGA no-go predicates -/

/-- Diagnostic no-go on a tautological gauge. Ill-posed as a live bridge. -/
def BealCGANoGo : Prop :=
  ∀ (A B C : ℤ) (x y z : ℕ) (_hx : 3 ≤ x) (_hy : 3 ≤ y) (_hz : 3 ≤ z)
    (_hA : A ≠ 0) (_hB : B ≠ 0) (_hC : C ≠ 0),
    bealGcd A B C = 1 →
    A ^ x + B ^ y = C ^ z →
      BealCGAGauge A C x z (bealMinExp x y z) →
        ∀ (N : ℕ) (hN : N ≠ 0),
          letI : NeZero N := ⟨hN⟩
          let m := bealMinExp x y z
          let k := bealAmpExp x y z
          let t := quantizeBealMismatch N A C x z m
          ¬ (IsAdmissible t ∧ ∃ w : ModularAmplificationWitness N k, w.t.val = t)

/-- Unproved: a lattice solution carries no modular winding witness. -/
def BealCGADilationNoGo : Prop :=
  ∀ (A B C : ℤ) (x y z : ℕ) (_hx : 3 ≤ x) (_hy : 3 ≤ y) (_hz : 3 ≤ z)
    (_hA : A ≠ 0) (_hB : B ≠ 0) (_hC : C ≠ 0),
    bealGcd A B C = 1 →
    A ^ x + B ^ y = C ^ z →
      BealCGALatticeGauge A B C x y z (bealMinExp x y z) →
        ∀ (N : ℕ) (hN : N ≠ 0),
          letI : NeZero N := ⟨hN⟩
          let m := bealMinExp x y z
          let k := bealAmpExp x y z
          let t := quantizeBealMismatch N A C x z m
          ¬ (IsAdmissible t ∧ ∃ w : ModularAmplificationWitness N k, w.t.val = t)

theorem beal_conjecture_of_winding_and_cga_nogo
    (hwind : BealWindingBridge) (hnogo : BealCGANoGo) :
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
  obtain ⟨N, hN, hadm, hw⟩ :=
    hwind A B C x y z hx hy hz hA hB hC hcoprime hsol
  let : NeZero N := ⟨hN⟩
  exact hnogo A B C x y z hx hy hz hA hB hC hcoprime hsol
    (BealCGAGauge_of_ne_zero A C x z (bealMinExp x y z)) N hN ⟨hadm, hw⟩

theorem beal_conjecture_of_winding_and_cga_dilation_nogo
    (hwind : BealWindingBridge) (hnogo : BealCGADilationNoGo) :
    ∀ (A B C : ℤ) (x y z : ℕ),
      3 ≤ x → 3 ≤ y → 3 ≤ z →
      A ≠ 0 → B ≠ 0 → C ≠ 0 →
      BealCGALatticeGauge A B C x y z (bealMinExp x y z) →
      A ^ x + B ^ y = C ^ z →
      1 < bealGcd A B C := by
  intro A B C x y z hx hy hz hA hB hC hlat hsol
  by_contra hnot
  have hle : bealGcd A B C ≤ 1 := Nat.not_lt.mp hnot
  have hpos : 0 < bealGcd A B C := bealGcd_pos hA
  have hcoprime : bealGcd A B C = 1 := le_antisymm hle (Nat.succ_le_of_lt hpos)
  obtain ⟨N, hN, hadm, hw⟩ :=
    hwind A B C x y z hx hy hz hA hB hC hcoprime hsol
  let : NeZero N := ⟨hN⟩
  exact hnogo A B C x y z hx hy hz hA hB hC hcoprime hsol hlat N hN ⟨hadm, hw⟩

theorem beal_eq_exp_not_coprime_of_winding_and_cga_dilation_nogo
    (hwind : BealWindingBridge) (hnogo : BealCGADilationNoGo)
    (A B C : ℤ) (p : ℕ) (hp : 3 ≤ p)
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hsol : A ^ p + B ^ p = C ^ p) :
    1 < bealGcd A B C := by
  have hp0 : p ≠ 0 := ne_of_gt (Nat.lt_of_lt_of_le (by decide : 0 < 3) hp)
  have hlat : BealCGALatticeGauge A B C p p p (bealMinExp p p p) := by
    have hm : bealMinExp p p p = p := by simp [bealMinExp]
    rw [hm]
    exact BealCGALatticeGauge_of_eq_exp A B C p hp0 hA hB hC
  exact beal_conjecture_of_winding_and_cga_dilation_nogo hwind hnogo
    A B C p p p hp hp hp hA hB hC hlat hsol

/-! ### Phase 7d: k-fold CGA power-lattice descent -/

/-- `k`-fold CGA dilation of the A-root: `α · e^{kδ} = γ^k / α^{k−1}` when positive. -/
noncomputable def bealCGAKFoldMag (A C : ℤ) (x z m k : ℕ) : ℝ :=
  bealRootMag A x m * Real.exp ((k : ℝ) * bealFracLogGap A C x z m)

theorem bealCGAKFoldMag_eq_root_ratio (A C : ℤ) (x z m k : ℕ)
    (hA : A ≠ 0) (hC : C ≠ 0) (hk : 1 ≤ k) :
    bealCGAKFoldMag A C x z m k =
      bealRootMag C z m ^ k / bealRootMag A x m ^ (k - 1) := by
  unfold bealCGAKFoldMag
  set α := bealRootMag A x m
  set γ := bealRootMag C z m
  set δ := bealFracLogGap A C x z m
  have hα : 0 < α := bealRootMag_pos hA x m
  have hγ : 0 < γ := bealRootMag_pos hC z m
  have hδ : δ = Real.log γ - Real.log α :=
    bealFracLogGap_eq_log_rootMag A C x z m hA hC
  have hexp : Real.exp ((k : ℝ) * δ) = γ ^ k / α ^ k := by
    rw [hδ, mul_sub, Real.exp_sub, Real.exp_nat_mul, Real.exp_nat_mul,
      Real.exp_log hγ, Real.exp_log hα]
  have hsucc : k = (k - 1) + 1 := (Nat.sub_add_cancel hk).symm
  have hpow : α ^ k = α ^ ((k - 1) + 1) := by rw [← hsucc]
  calc α * Real.exp ((k : ℝ) * δ)
      = α * (γ ^ k / α ^ k) := by rw [hexp]
    _ = γ ^ k / α ^ (k - 1) := by
        rw [hpow, pow_succ]
        field_simp [ne_of_gt hα]

theorem bealCGAKFoldMag_pow (A C : ℤ) (x z m k : ℕ)
    (hm : m ≠ 0) (hA : A ≠ 0) (hC : C ≠ 0) (hk : 1 ≤ k) :
    bealCGAKFoldMag A C x z m k ^ m =
      (C.natAbs : ℝ) ^ (k * z) / (A.natAbs : ℝ) ^ (x * (k - 1)) := by
  have hapow := bealRootMag_pow A x m hm
  have hgpow := bealRootMag_pow C z m hm
  have hr := bealCGAKFoldMag_eq_root_ratio A C x z m k hA hC hk
  rw [hr, div_pow]
  have h1 : (bealRootMag C z m ^ k) ^ m = (C.natAbs : ℝ) ^ (k * z) := by
    rw [← pow_mul, mul_comm k m, pow_mul, hgpow, ← pow_mul, mul_comm z k]
  have h2 : (bealRootMag A x m ^ (k - 1)) ^ m =
      (A.natAbs : ℝ) ^ (x * (k - 1)) := by
    rw [← pow_mul, mul_comm (k - 1) m, pow_mul, hapow, ← pow_mul]
  rw [h1, h2]

theorem beal_kFold_powerLattice_dvd (A C : ℤ) (x z m k : ℕ)
    (hm : m ≠ 0) (hA : A ≠ 0) (hC : C ≠ 0) (hk : 1 ≤ k)
    (hlat : IsCGAPowerLatticePoint (bealCGAKFoldMag A C x z m k) m) :
    A.natAbs ^ (x * (k - 1)) ∣ C.natAbs ^ (k * z) := by
  obtain ⟨n, _hn, heq⟩ := hlat
  have hpow := bealCGAKFoldMag_pow A C x z m k hm hA hC hk
  have ha : 0 < (A.natAbs : ℝ) :=
    Nat.cast_pos.mpr (Int.natAbs_pos.mpr hA)
  have hden : (0 : ℝ) < (A.natAbs : ℝ) ^ (x * (k - 1)) :=
    pow_pos ha _
  have hnpos : 0 < (n : ℝ) := by
    have hmag : 0 < bealCGAKFoldMag A C x z m k := by
      unfold bealCGAKFoldMag
      exact mul_pos (bealRootMag_pos hA x m) (Real.exp_pos _)
    have : 0 < (bealCGAKFoldMag A C x z m k) ^ m := pow_pos hmag _
    rwa [heq] at this
  have hn0 : 0 < n := Int.cast_pos.mp hnpos
  have hdivR :
      (C.natAbs : ℝ) ^ (k * z) =
        (n : ℝ) * (A.natAbs : ℝ) ^ (x * (k - 1)) := by
    have : (C.natAbs : ℝ) ^ (k * z) / (A.natAbs : ℝ) ^ (x * (k - 1)) =
        (n : ℝ) := by
      rw [← hpow, heq]
    field_simp [ne_of_gt hden] at this ⊢
    linarith [this]
  refine ⟨n.toNat, ?_⟩
  apply_fun (fun t : ℕ => (t : ℝ)) using Nat.cast_injective
  simp only [Nat.cast_mul, Nat.cast_pow]
  have hnR : (n.toNat : ℝ) = (n : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hn0.le
  rw [hnR, hdivR, mul_comm]

theorem beal_natAbs_eq_one_of_ac_pow_dvd {A C : ℤ} {e f : ℕ}
    (he : 0 < e) (hac : Nat.Coprime A.natAbs C.natAbs)
    (hdvd : A.natAbs ^ e ∣ C.natAbs ^ f) : A.natAbs = 1 := by
  rw [Nat.eq_one_iff_not_exists_prime_dvd]
  intro p hp hpA
  have hpC : p ∣ C.natAbs := by
    have : p ∣ A.natAbs ^ e := dvd_pow hpA (ne_of_gt he)
    exact hp.dvd_of_dvd_pow (Nat.dvd_trans this hdvd)
  exact Nat.Prime.not_coprime_iff_dvd.mpr ⟨p, hp, hpA, hpC⟩ hac

theorem bealGcd_eq_one_of_not_gt {A B C : ℤ} (hA : A ≠ 0)
    (hnot : ¬ 1 < bealGcd A B C) : bealGcd A B C = 1 := by
  have hle : bealGcd A B C ≤ 1 := Nat.not_lt.mp hnot
  exact le_antisymm hle (Nat.succ_le_of_lt (bealGcd_pos hA))

theorem beal_natAbs_eq_one_of_kFold_powerLattice {A B C : ℤ} {x y z m k : ℕ}
    (hm : m ≠ 0) (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hk : 2 ≤ k)
    (hgcd : bealGcd A B C = 1)
    (hsol : A ^ x + B ^ y = C ^ z)
    (hlat : IsCGAPowerLatticePoint (bealCGAKFoldMag A C x z m k) m) :
    A.natAbs = 1 := by
  have hk1 : 1 ≤ k := Nat.le_trans (by decide : 1 ≤ 2) hk
  have hdvd := beal_kFold_powerLattice_dvd A C x z m k hm hA hC hk1 hlat
  have hac := beal_coprime_ac hA hB hC hx hy hz hgcd hsol
  have hpow : 0 < x * (k - 1) :=
    Nat.mul_pos hx (Nat.sub_pos_of_lt hk)
  exact beal_natAbs_eq_one_of_ac_pow_dvd hpow hac hdvd

theorem beal_kFold_powerLattice_of_natAbs_eq_one (A C : ℤ) (x z m k : ℕ)
    (hm : m ≠ 0) (hA : A ≠ 0) (hC : C ≠ 0) (hk : 1 ≤ k)
    (hA1 : A.natAbs = 1) :
    IsCGAPowerLatticePoint (bealCGAKFoldMag A C x z m k) m := by
  refine ⟨(C.natAbs : ℤ) ^ (k * z), ?_, ?_⟩
  · exact pow_ne_zero _ (by exact_mod_cast ne_of_gt (Int.natAbs_pos.mpr hC))
  · have hpow := bealCGAKFoldMag_pow A C x z m k hm hA hC hk
    rw [hpow, hA1]
    simp [one_pow]

theorem beal_kFold_powerLattice_iff_natAbs_eq_one {A B C : ℤ} {x y z m k : ℕ}
    (hm : m ≠ 0) (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hk : 2 ≤ k)
    (hgcd : bealGcd A B C = 1)
    (hsol : A ^ x + B ^ y = C ^ z) :
    IsCGAPowerLatticePoint (bealCGAKFoldMag A C x z m k) m ↔ A.natAbs = 1 := by
  constructor
  · exact beal_natAbs_eq_one_of_kFold_powerLattice hm hA hB hC hx hy hz hk
      hgcd hsol
  · intro hA1
    exact beal_kFold_powerLattice_of_natAbs_eq_one A C x z m k hm hA hC
      (Nat.le_trans (by decide : 1 ≤ 2) hk) hA1

theorem beal_balanced_gap_no_modularWitness (N : ℕ) [NeZero N] {x y z : ℕ}
    (hx : 3 ≤ x) (hy : 3 ≤ y) (hz : 3 ≤ z) :
    ¬ ∃ w : ModularAmplificationWitness N (bealAmpExp x y z),
      w.t.val = pureBoostSeedOfRapidity N
        (Real.log 2 / (bealMinExp x y z : ℝ)) := by
  intro hw
  exact not_exists_modularWitness_of_balanced_gap N (bealMinExp x y z)
    (bealAmpExp x y z) (bealAmpExp_pos x y z)
    (beal_balanced_fracGap_lt_ampExp_threshold hx hy hz) hw

/-! ### Bookkeeping discrete closure + unit-base residual (phase 7e) -/

/-- Bookkeeping: coprime power-lattice closure means `|A| = 1`. -/
def BealCGADiscreteClosed : Prop :=
  ∀ (A B C : ℤ) (x y z : ℕ) (_hx : 3 ≤ x) (_hy : 3 ≤ y) (_hz : 3 ≤ z)
    (_hA : A ≠ 0) (_hB : B ≠ 0) (_hC : C ≠ 0),
    bealGcd A B C = 1 →
    A ^ x + B ^ y = C ^ z →
      IsCGAPowerLatticePoint
        (bealCGAKFoldMag A C x z (bealMinExp x y z) (bealAmpExp x y z))
        (bealMinExp x y z)

/-- Residual: no coprime `|A| = 1`. Positive bases are closed by Mihăilescu. -/
def BealUnitBaseNoGo : Prop :=
  ∀ (A B C : ℤ) (x y z : ℕ) (_hx : 3 ≤ x) (_hy : 3 ≤ y) (_hz : 3 ≤ z)
    (_hA : A ≠ 0) (_hB : B ≠ 0) (_hC : C ≠ 0),
    bealGcd A B C = 1 →
    A.natAbs = 1 →
      ¬ A ^ x + B ^ y = C ^ z

theorem bealUnitBaseNoGo_pos {A B C : ℤ} {x y z : ℕ}
    (hx : 3 ≤ x) (hy : 3 ≤ y) (hz : 3 ≤ z)
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (hA1 : A.natAbs = 1) :
    ¬ A ^ x + B ^ y = C ^ z :=
  not_unitAbs_pow_add_pow_eq_pow_pos hA hB hC hA1 hx hy hz

theorem BealCGADiscreteClosed_iff_unitAbs :
    BealCGADiscreteClosed ↔
      ∀ (A B C : ℤ) (x y z : ℕ),
        3 ≤ x → 3 ≤ y → 3 ≤ z →
        A ≠ 0 → B ≠ 0 → C ≠ 0 →
        bealGcd A B C = 1 →
        A ^ x + B ^ y = C ^ z →
          A.natAbs = 1 := by
  constructor
  · intro hclosed A B C x y z hx hy hz hA hB hC hgcd hsol
    have hlat := hclosed A B C x y z hx hy hz hA hB hC hgcd hsol
    exact (beal_kFold_powerLattice_iff_natAbs_eq_one
      (ne_of_gt (bealMinExp_pos hx hy hz)) hA hB hC
      (Nat.lt_of_lt_of_le (by decide : 0 < 3) hx)
      (Nat.lt_of_lt_of_le (by decide : 0 < 3) hy)
      (Nat.lt_of_lt_of_le (by decide : 0 < 3) hz)
      (Nat.le_trans (by decide : 2 ≤ 4) (bealAmpExp_ge_four x y z))
      hgcd hsol).mp hlat
  · intro hunit A B C x y z hx hy hz hA hB hC hgcd hsol
    exact (beal_kFold_powerLattice_iff_natAbs_eq_one
      (ne_of_gt (bealMinExp_pos hx hy hz)) hA hB hC
      (Nat.lt_of_lt_of_le (by decide : 0 < 3) hx)
      (Nat.lt_of_lt_of_le (by decide : 0 < 3) hy)
      (Nat.lt_of_lt_of_le (by decide : 0 < 3) hz)
      (Nat.le_trans (by decide : 2 ≤ 4) (bealAmpExp_ge_four x y z))
      hgcd hsol).mpr (hunit A B C x y z hx hy hz hA hB hC hgcd hsol)

theorem beal_conjecture_of_discreteClosed_and_unitBaseNoGo
    (hclosed : BealCGADiscreteClosed) (hnogo : BealUnitBaseNoGo) :
    ∀ (A B C : ℤ) (x y z : ℕ),
      3 ≤ x → 3 ≤ y → 3 ≤ z →
      A ≠ 0 → B ≠ 0 → C ≠ 0 →
      A ^ x + B ^ y = C ^ z →
      1 < bealGcd A B C := by
  intro A B C x y z hx hy hz hA hB hC hsol
  by_contra hnot
  have hcoprime := bealGcd_eq_one_of_not_gt hA hnot
  have hA1 := BealCGADiscreteClosed_iff_unitAbs.mp hclosed
    A B C x y z hx hy hz hA hB hC hcoprime hsol
  exact hnogo A B C x y z hx hy hz hA hB hC hcoprime hA1 hsol

theorem beal_conjecture_pos_of_discreteClosed
    (hclosed : BealCGADiscreteClosed) :
    ∀ (A B C : ℤ) (x y z : ℕ),
      3 ≤ x → 3 ≤ y → 3 ≤ z →
      0 < A → 0 < B → 0 < C →
      A ^ x + B ^ y = C ^ z →
      1 < bealGcd A B C := by
  intro A B C x y z hx hy hz hA hB hC hsol
  by_contra hnot
  have hcoprime := bealGcd_eq_one_of_not_gt hA.ne' hnot
  have hA1 := BealCGADiscreteClosed_iff_unitAbs.mp hclosed
    A B C x y z hx hy hz hA.ne' hB.ne' hC.ne' hcoprime hsol
  exact bealUnitBaseNoGo_pos hx hy hz hA hB hC hA1 hsol

theorem not_one_add_pow_three_eq_pow_three {b c : ℤ}
    (hb : 0 < b) (hc : 0 < c) : ¬ ((1 : ℤ) + b ^ 3 = c ^ 3) := by
  intro hsol
  have hdiff : c ^ 3 - b ^ 3 = 1 := by linarith [hsol]
  have hfac : (c - b) * (c ^ 2 + c * b + b ^ 2) = 1 := by
    have : c ^ 3 - b ^ 3 = (c - b) * (c ^ 2 + c * b + b ^ 2) := by ring
    linarith [this, hdiff]
  have hcb_pos : 0 < c - b := by
    have hbc : b < c := by
      by_contra hle
      push Not at hle
      have : c ^ 3 ≤ b ^ 3 :=
        pow_le_pow_left₀ (le_of_lt hc) hle 3
      linarith [hdiff]
    linarith
  have hcb : c - b = 1 := by
    have h1' : c - b ∣ (1 : ℤ) := ⟨c ^ 2 + c * b + b ^ 2, hfac.symm⟩
    have hle : c - b ≤ 1 := Int.le_of_dvd (by decide : (0 : ℤ) < 1) h1'
    have hge : 1 ≤ c - b := Int.add_one_le_of_lt hcb_pos
    exact le_antisymm hle hge
  have hpoly : 3 * b ^ 2 + 3 * b = 0 := by
    have hc_eq : c = b + 1 := by linarith [hcb]
    rw [hc_eq] at hdiff
    ring_nf at hdiff
    linarith [hdiff]
  have : b * (b + 1) = 0 := by
    have h3 : (3 : ℤ) ≠ 0 := by decide
    have : (3 : ℤ) * (b * (b + 1)) = 0 := by linarith [hpoly]
    exact (mul_eq_zero.mp this).resolve_left h3
  exact (mul_eq_zero.mp this).elim (ne_of_gt hb) (by intro; linarith [hb])

/-! ### Phase 7e–7f: DST discrete config + CGA realisation (bookkeeping) -/

/-- PGA faithfulness together with an integer CGA dilation of the A–C root ratio. -/
def IsDSTBealDiscreteConfig (A B C : ℤ) (x y z : ℕ) : Prop :=
  powerSumMotor (bealEquation A B C x y z) = 1 ∧
    IsCGAIntegerDilation
      (bealRootMag C z (bealMinExp x y z) / bealRootMag A x (bealMinExp x y z))

theorem bealRootMag_div_eq_natAbs_div (A C : ℤ) (p : ℕ) (hp : p ≠ 0) :
    bealRootMag C p p / bealRootMag A p p =
      (C.natAbs : ℝ) / (A.natAbs : ℝ) := by
  rw [bealRootMag_eq_natAbs A p hp, bealRootMag_eq_natAbs C p hp]

theorem beal_integerDilation_iff_pow_eq (A C : ℤ) (x z m : ℕ)
    (hm : m ≠ 0) (hA : A ≠ 0) (hC : C ≠ 0) :
    IsCGAIntegerDilation (bealRootMag C z m / bealRootMag A x m) ↔
      ∃ k : ℕ, k ≠ 0 ∧ C.natAbs ^ z = k ^ m * A.natAbs ^ x := by
  have hα : 0 < bealRootMag A x m := bealRootMag_pos hA x m
  have hγ : 0 < bealRootMag C z m := bealRootMag_pos hC z m
  constructor
  · intro ⟨n, hn, heq⟩
    have hnpos : 0 < n :=
      Int.cast_pos.mp (heq ▸ div_pos hγ hα)
    have hscale : bealRootMag C z m = (n : ℝ) * bealRootMag A x m := by
      have := congrArg (fun t => t * bealRootMag A x m) heq
      field_simp [ne_of_gt hα] at this
      linarith [this]
    have hL := congrArg (fun t : ℝ => t ^ m) hscale
    rw [mul_pow, bealRootMag_pow A x m hm, bealRootMag_pow C z m hm] at hL
    refine ⟨n.toNat, ?_, ?_⟩
    · intro h0
      have : (n.toNat : ℤ) = n := Int.toNat_of_nonneg hnpos.le
      rw [h0, Nat.cast_zero] at this
      exact hn this.symm
    · apply_fun (fun t : ℕ => (t : ℝ)) using Nat.cast_injective
      simp only [Nat.cast_mul, Nat.cast_pow]
      have hnR : (n.toNat : ℝ) = (n : ℝ) := by
        exact_mod_cast Int.toNat_of_nonneg hnpos.le
      rw [hnR, hL, mul_comm]
  · intro ⟨k, hk, hpowN⟩
    refine ⟨(k : ℤ), by exact_mod_cast hk, ?_⟩
    have hαR : (bealRootMag A x m) ^ m = (A.natAbs : ℝ) ^ x :=
      bealRootMag_pow A x m hm
    have hγR : (bealRootMag C z m) ^ m = (C.natAbs : ℝ) ^ z :=
      bealRootMag_pow C z m hm
    have hpowR : (C.natAbs : ℝ) ^ z = (k : ℝ) ^ m * (A.natAbs : ℝ) ^ x := by
      exact_mod_cast hpowN
    have hscale : (bealRootMag C z m) ^ m =
        ((k : ℝ) * bealRootMag A x m) ^ m := by
      rw [mul_pow, hαR, hγR, hpowR]
    have hkpos : (0 : ℝ) < k := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hk)
    have hposR : 0 ≤ (k : ℝ) * bealRootMag A x m :=
      mul_nonneg hkpos.le hα.le
    have heqMag : bealRootMag C z m = (k : ℝ) * bealRootMag A x m :=
      (pow_left_inj₀ hγ.le hposR hm).mp hscale
    exact ((eq_div_iff (ne_of_gt hα)).mpr heqMag.symm).symm

theorem beal_natAbs_eq_one_of_dstDiscreteConfig {A B C : ℤ} {x y z : ℕ}
    (hx : 3 ≤ x) (hy : 3 ≤ y) (hz : 3 ≤ z)
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hgcd : bealGcd A B C = 1)
    (hcfg : IsDSTBealDiscreteConfig A B C x y z) :
    A.natAbs = 1 := by
  obtain ⟨hmotor, hdil⟩ := hcfg
  have hsol : A ^ x + B ^ y = C ^ z :=
    (beal_solution_iff_motor A B C x y z).mpr hmotor
  have hx0 : 0 < x := Nat.lt_of_lt_of_le (by decide : 0 < 3) hx
  have hy0 : 0 < y := Nat.lt_of_lt_of_le (by decide : 0 < 3) hy
  have hz0 : 0 < z := Nat.lt_of_lt_of_le (by decide : 0 < 3) hz
  have hac := beal_coprime_ac hA hB hC hx0 hy0 hz0 hgcd hsol
  set m := bealMinExp x y z
  have hm : m ≠ 0 := ne_of_gt (bealMinExp_pos hx hy hz)
  obtain ⟨k, _hk, hpow⟩ :=
    (beal_integerDilation_iff_pow_eq A C x z m hm hA hC).mp hdil
  exact beal_natAbs_eq_one_of_ac_pow_dvd hx0 hac ⟨k ^ m, by rw [hpow, mul_comm]⟩

theorem not_dstDiscreteConfig_coprime_pos {A B C : ℤ} {x y z : ℕ}
    (hx : 3 ≤ x) (hy : 3 ≤ y) (hz : 3 ≤ z)
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (hgcd : bealGcd A B C = 1)
    (hcfg : IsDSTBealDiscreteConfig A B C x y z) :
    False := by
  have hA1 := beal_natAbs_eq_one_of_dstDiscreteConfig hx hy hz
    hA.ne' hB.ne' hC.ne' hgcd hcfg
  exact bealUnitBaseNoGo_pos hx hy hz hA hB hC hA1
    ((beal_solution_iff_motor A B C x y z).mpr hcfg.1)

/-- Bookkeeping: coprime integer dilation forces `|A| = 1`. -/
def BealCGARealization : Prop :=
  ∀ (A B C : ℤ) (x y z : ℕ) (_hx : 3 ≤ x) (_hy : 3 ≤ y) (_hz : 3 ≤ z)
    (_hA : A ≠ 0) (_hB : B ≠ 0) (_hC : C ≠ 0),
    bealGcd A B C = 1 →
    A ^ x + B ^ y = C ^ z →
      IsCGAIntegerDilation
        (bealRootMag C z (bealMinExp x y z) / bealRootMag A x (bealMinExp x y z))

theorem IsDSTBealDiscreteConfig_of_realization
    (hreal : BealCGARealization) {A B C : ℤ} {x y z : ℕ}
    (hx : 3 ≤ x) (hy : 3 ≤ y) (hz : 3 ≤ z)
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hgcd : bealGcd A B C = 1)
    (hsol : A ^ x + B ^ y = C ^ z) :
    IsDSTBealDiscreteConfig A B C x y z :=
  ⟨(beal_solution_iff_motor A B C x y z).mp hsol,
    hreal A B C x y z hx hy hz hA hB hC hgcd hsol⟩

theorem beal_conjecture_pos_of_realization (hreal : BealCGARealization) :
    ∀ (A B C : ℤ) (x y z : ℕ),
      3 ≤ x → 3 ≤ y → 3 ≤ z →
      0 < A → 0 < B → 0 < C →
      A ^ x + B ^ y = C ^ z →
      1 < bealGcd A B C := by
  intro A B C x y z hx hy hz hA hB hC hsol
  by_contra hnot
  have hcoprime := bealGcd_eq_one_of_not_gt hA.ne' hnot
  exact not_dstDiscreteConfig_coprime_pos hx hy hz hA hB hC hcoprime
    (IsDSTBealDiscreteConfig_of_realization hreal hx hy hz
      hA.ne' hB.ne' hC.ne' hcoprime hsol)

theorem beal_eq_exp_mismatchRotor_scale (A C : ℤ) (p : ℕ) (hp : p ≠ 0)
    (hA : A ≠ 0) (hC : C ≠ 0) :
    mismatchRotor A C hA hC =
      rotorTorsion
        (pureBoost
          (2 * Real.log (bealRootMag C p p / bealRootMag A p p))) := by
  have hAabs : 0 < (A.natAbs : ℝ) :=
    Nat.cast_pos.mpr (Int.natAbs_pos.mpr hA)
  have hCabs : 0 < (C.natAbs : ℝ) :=
    Nat.cast_pos.mpr (Int.natAbs_pos.mpr hC)
  have hlog :
      Real.log (bealRootMag C p p / bealRootMag A p p) =
        Real.log (C.natAbs : ℝ) - Real.log (A.natAbs : ℝ) := by
    rw [bealRootMag_div_eq_natAbs_div A C p hp,
      Real.log_div (ne_of_gt hCabs) (ne_of_gt hAabs)]
  rw [mismatchRotor_eq_rotorTorsion A C hA hC, hlog]

theorem beal_eq_exp_integerDilation_iff (A C : ℤ) (p : ℕ) (hp : p ≠ 0)
    (hA : A ≠ 0) (hC : C ≠ 0) :
    IsCGAIntegerDilation (bealRootMag C p p / bealRootMag A p p) ↔
      A.natAbs ∣ C.natAbs := by
  rw [bealRootMag_div_eq_natAbs_div A C p hp]
  exact IsCGAIntegerDilation_div_iff hA hC

theorem beal_eq_exp_integerDilation_iff_natAbs_eq_one (A C : ℤ) (p : ℕ)
    (hp : p ≠ 0) (hA : A ≠ 0) (hC : C ≠ 0)
    (hac : Nat.Coprime A.natAbs C.natAbs) :
    IsCGAIntegerDilation (bealRootMag C p p / bealRootMag A p p) ↔
      A.natAbs = 1 := by
  rw [beal_eq_exp_integerDilation_iff A C p hp hA hC]
  exact ⟨fun hdvd => Nat.Coprime.eq_one_of_dvd hac hdvd, fun hA1 => by
    rw [hA1]; exact one_dvd _⟩

theorem beal_integerDilation_of_coprime_iff {A B C : ℤ} {x y z : ℕ}
    (hx : 3 ≤ x) (hy : 3 ≤ y) (hz : 3 ≤ z)
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hgcd : bealGcd A B C = 1)
    (hsol : A ^ x + B ^ y = C ^ z) :
    let m := bealMinExp x y z
    IsCGAIntegerDilation (bealRootMag C z m / bealRootMag A x m) ↔
      A.natAbs = 1 ∧ ∃ k : ℕ, k ≠ 0 ∧ C.natAbs ^ z = k ^ m := by
  intro m
  have hm : m ≠ 0 := ne_of_gt (bealMinExp_pos hx hy hz)
  constructor
  · intro hdil
    have hcfg : IsDSTBealDiscreteConfig A B C x y z :=
      ⟨(beal_solution_iff_motor A B C x y z).mp hsol, hdil⟩
    have hA1 := beal_natAbs_eq_one_of_dstDiscreteConfig hx hy hz
      hA hB hC hgcd hcfg
    obtain ⟨k, hk, hpow⟩ :=
      (beal_integerDilation_iff_pow_eq A C x z m hm hA hC).mp hdil
    refine ⟨hA1, ⟨k, hk, ?_⟩⟩
    simpa [hA1, one_pow, mul_one] using hpow
  · intro ⟨hA1, ⟨k, hk, hpowN⟩⟩
    refine (beal_integerDilation_iff_pow_eq A C x z m hm hA hC).mpr ?_
    refine ⟨k, hk, ?_⟩
    simpa [hA1, one_pow, mul_one] using hpowN

/-- `3² + 4² = 5²` misses integer dilation; exponents `2` lie outside Beal. -/
theorem not_beal_eq_exp_integerDilation_three_four_five :
    ¬ IsCGAIntegerDilation (bealRootMag (5 : ℤ) 2 2 / bealRootMag (3 : ℤ) 2 2) := by
  rw [bealRootMag_div_eq_natAbs_div 3 5 2 (by decide)]
  exact not_isCGAIntegerDilation_five_div_three

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

/-! ### Wide principal window (proved construction) -/

private theorem beal_wide_frac_bounds (k : ℕ) (hk : 0 < k) (δ : ℝ)
    (hle : 2 * Real.pi / k ≤ δ) (hlt : δ < 4 * Real.pi / k) :
    (1 : ℝ) ≤ δ * (k : ℝ) / (2 * Real.pi) ∧
      δ * (k : ℝ) / (2 * Real.pi) < (2 : ℝ) := by
  have hden : (0 : ℝ) < 2 * Real.pi := by positivity
  have hk0 : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hk)
  have hN : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have hNpos : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hlo : (2 * Real.pi / k) * (k : ℝ) / (2 * Real.pi) = (1 : ℝ) := by
    field_simp [hk0]
  have hhi : (4 * Real.pi / k) * (k : ℝ) / (2 * Real.pi) = (2 : ℝ) := by
    field_simp [hk0]; ring
  exact ⟨
    by
      have := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hle hN) hden.le
      rwa [hlo] at this,
    by
      have := div_lt_div_of_pos_right (mul_lt_mul_of_pos_right hlt hNpos) hden
      rwa [hhi] at this⟩

private theorem beal_wide_delta_lt_two_pi (k : ℕ) (hk4 : 4 ≤ k)
    (δ : ℝ) (hlt : δ < 4 * Real.pi / k) :
    δ < 2 * Real.pi := by
  have hkR : (4 : ℝ) ≤ k := Nat.cast_le.mpr hk4
  have hupper : 4 * Real.pi / k ≤ Real.pi := by
    have h : 4 * Real.pi / k ≤ 4 * Real.pi / 4 :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hkR
    convert h using 1; ring
  nlinarith [hlt, hupper, Real.pi_pos]

theorem pureBoostSeedOfRapidity_eq_principal (N : ℕ) [NeZero N] {θ : ℝ}
    (hθ : 0 ≤ θ) :
    pureBoostSeedOfRapidity N θ =
      pureBoostSeedOfRapidity N (principalRapidity θ) := by
  refine congr_arg₂ DiscreteTorsion.mk ?_ rfl
  funext i
  fin_cases i
  · change (quantizeRapidity N θ : ZMod N) =
        (quantizeRapidity N (principalRapidity θ) : ZMod N)
    exact quantizeRapidity_zmod_eq_principal N hθ
  · rfl
  · rfl

private theorem beal_wide_n0_val_eq_one (k : ℕ) [NeZero k] (hk4 : 4 ≤ k) {δ : ℝ}
    (hle : 2 * Real.pi / k ≤ δ) (hlt : δ < 4 * Real.pi / k) :
    ((pureBoostSeedOfRapidity k δ).n 0).val = 1 := by
  have hkpos : 0 < k := Nat.zero_lt_of_lt hk4
  have hδlt2π : δ < 2 * Real.pi := beal_wide_delta_lt_two_pi k hk4 δ hlt
  have hδ0 : 0 ≤ δ :=
    le_trans
      (div_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) (Nat.cast_nonneg _)) hle
  have hbounds := quantizeRapidity_of_lt_two_pi k δ hδ0 hδlt2π
  have hfrac := beal_wide_frac_bounds k hkpos δ hle hlt
  have hfloor : quantizeRapidity k δ = 1 := by
    have hleZ : (1 : ℤ) ≤ quantizeRapidity k δ := by
      have : ((1 : ℤ) : ℝ) ≤ δ * (k : ℝ) / (2 * Real.pi) := by
        simpa using hfrac.1
      exact Int.le_floor.mpr this
    have hltZ : quantizeRapidity k δ < (2 : ℤ) := by
      have : δ * (k : ℝ) / (2 * Real.pi) < ((2 : ℤ) : ℝ) := by
        simpa using hfrac.2
      exact Int.floor_lt.mpr this
    omega
  have hvalZ : (((pureBoostSeedOfRapidity k δ).n 0).val : ℤ) =
      quantizeRapidity k δ := hbounds.2.2
  rw [hfloor] at hvalZ
  exact_mod_cast hvalZ

private theorem beal_wide_smul_n0_eq_zero (k : ℕ) [NeZero k] (hk4 : 4 ≤ k) {δ : ℝ}
    (hle : 2 * Real.pi / k ≤ δ) (hlt : δ < 4 * Real.pi / k) :
    k • (pureBoostSeedOfRapidity k δ).n 0 = 0 := by
  set t := pureBoostSeedOfRapidity k δ
  have hval : (t.n 0).val = 1 := beal_wide_n0_val_eq_one k hk4 hle hlt
  have h1lt : 1 < k := Nat.lt_of_lt_of_le (by decide : 1 < 4) hk4
  have hn0 : t.n 0 = (1 : ZMod k) := by
    apply ZMod.val_injective
    have : Fact (1 < k) := ⟨h1lt⟩
    rw [hval, ZMod.val_one]
  rw [hn0, nsmul_eq_mul]
  change ((k : ℕ) : ZMod k) * (1 : ZMod k) = 0
  rw [mul_one, ZMod.natCast_self]

theorem beal_modularWitness_of_fracGap_window
    (A C : ℤ) (x z m k : ℕ) (hk4 : 4 ≤ k)
    (hle : 2 * Real.pi / k ≤ bealFracLogGap A C x z m)
    (hlt : bealFracLogGap A C x z m < 4 * Real.pi / k) :
    let N := k
    ∃ (hN : N ≠ 0),
      letI : NeZero N := ⟨hN⟩
      let t := quantizeBealMismatch N A C x z m
      IsAdmissible t ∧ ∃ w : ModularAmplificationWitness N k, w.t.val = t := by
  set N := k
  set δ := bealFracLogGap A C x z m
  have hkpos : 0 < k := Nat.zero_lt_of_lt hk4
  have hNne : N ≠ 0 := ne_of_gt hkpos
  refine ⟨hNne, ?_⟩
  let : NeZero N := ⟨hNne⟩
  set t := quantizeBealMismatch N A C x z m
  have hp : IsPureBoostSeed t := quantizeBealMismatch_pureBoost N A C x z m
  have hval : (t.n 0).val = 1 := by
    simpa [t, quantizeBealMismatch] using beal_wide_n0_val_eq_one k hk4 hle hlt
  have hadm : IsAdmissible t :=
    isAdmissible_of_pureBoost_n0_le t hp (by simpa [hval] using hk4)
  have hsmul : k • t.n 0 = 0 := by
    simp [t, quantizeBealMismatch]
  have hamp : IsAdmissible (amplifyDiscrete k t) :=
    isAdmissible_amplifyDiscrete_of_pureBoost_smul_n0 k t hp hsmul
  have hδlt2π : δ < 2 * Real.pi := beal_wide_delta_lt_two_pi k hk4 δ hlt
  have hwind : windingTotal k t ≠ 0 :=
    beal_has_winding_of_fracGap_ge N k m hkpos A C x z hle hδlt2π ⟨1, by ring⟩
  exact ⟨hadm, modularWitness_of_pureBoost_winding k t hp hadm hamp hwind, rfl⟩

theorem beal_modularWitness_of_fracGap_window_ampExp
    (A C : ℤ) (x y z : ℕ)
    (hle : 2 * Real.pi / bealAmpExp x y z ≤
      bealFracLogGap A C x z (bealMinExp x y z))
    (hlt : bealFracLogGap A C x z (bealMinExp x y z) <
      4 * Real.pi / bealAmpExp x y z) :
    let m := bealMinExp x y z
    let k := bealAmpExp x y z
    let N := k
    ∃ (hN : N ≠ 0),
      letI : NeZero N := ⟨hN⟩
      let t := quantizeBealMismatch N A C x z m
      IsAdmissible t ∧ ∃ w : ModularAmplificationWitness N k, w.t.val = t :=
  beal_modularWitness_of_fracGap_window A C x z (bealMinExp x y z)
    (bealAmpExp x y z) (bealAmpExp_ge_four x y z) hle hlt

theorem beal_modularWitness_of_principal_fracGap_window
    (A C : ℤ) (x z m k : ℕ) (hk4 : 4 ≤ k)
    (hδ0 : 0 ≤ bealFracLogGap A C x z m)
    (hle : 2 * Real.pi / k ≤ principalRapidity (bealFracLogGap A C x z m))
    (hlt : principalRapidity (bealFracLogGap A C x z m) < 4 * Real.pi / k) :
    let N := k
    ∃ (hN : N ≠ 0),
      letI : NeZero N := ⟨hN⟩
      let t := quantizeBealMismatch N A C x z m
      IsAdmissible t ∧ ∃ w : ModularAmplificationWitness N k, w.t.val = t := by
  set δ := bealFracLogGap A C x z m
  set δp := principalRapidity δ
  have hkpos : 0 < k := Nat.zero_lt_of_lt hk4
  have hNne : k ≠ 0 := ne_of_gt hkpos
  refine ⟨hNne, ?_⟩
  let : NeZero k := ⟨hNne⟩
  set t := quantizeBealMismatch k A C x z m
  have ht : t = pureBoostSeedOfRapidity k δp := by
    simp only [t, quantizeBealMismatch, δp]
    exact pureBoostSeedOfRapidity_eq_principal k hδ0
  have hp : IsPureBoostSeed t := quantizeBealMismatch_pureBoost k A C x z m
  have hval : (t.n 0).val = 1 := by
    have : ((pureBoostSeedOfRapidity k δp).n 0).val = 1 :=
      beal_wide_n0_val_eq_one k hk4 hle hlt
    simpa [ht] using this
  have hadm : IsAdmissible t :=
    isAdmissible_of_pureBoost_n0_le t hp (by simpa [hval] using hk4)
  have hsmul : k • t.n 0 = 0 := by
    have : k • (pureBoostSeedOfRapidity k δp).n 0 = 0 :=
      beal_wide_smul_n0_eq_zero k hk4 hle hlt
    simp [ht, this]
  have hamp : IsAdmissible (amplifyDiscrete k t) :=
    isAdmissible_amplifyDiscrete_of_pureBoost_smul_n0 k t hp hsmul
  have hδplt2π : δp < 2 * Real.pi := beal_wide_delta_lt_two_pi k hk4 δp hlt
  have hδp0 : 0 ≤ δp := principalRapidity_nonneg hδ0
  have hwind : windingTotal k t ≠ 0 := by
    have hw0 : windingTotal k (pureBoostSeedOfRapidity k δp) ≠ 0 :=
      windingTotal_ne_zero_of_rapidity_ge k k hkpos δp hδp0 hle hδplt2π ⟨1, by ring⟩
    simpa [ht] using hw0
  exact ⟨hadm, modularWitness_of_pureBoost_winding k t hp hadm hamp hwind, rfl⟩

/-! ### Window case of the winding bridge (proved) -/

theorem beal_winding_of_solution_window {A B C : ℤ} {x y z : ℕ}
    (_hA : 0 < A) (_hB : 0 < B) (_hC : 0 < C)
    (_hsol : A ^ x + B ^ y = C ^ z)
    (hle : 2 * Real.pi / bealAmpExp x y z ≤
      bealFracLogGap A C x z (bealMinExp x y z))
    (hlt : bealFracLogGap A C x z (bealMinExp x y z) <
      4 * Real.pi / bealAmpExp x y z) :
    let m := bealMinExp x y z
    let k := bealAmpExp x y z
    let N := k
    ∃ (hN : N ≠ 0),
      letI : NeZero N := ⟨hN⟩
      let t := quantizeBealMismatch N A C x z m
      IsAdmissible t ∧ ∃ w : ModularAmplificationWitness N k, w.t.val = t :=
  beal_modularWitness_of_fracGap_window_ampExp A C x y z hle hlt

theorem beal_winding_of_solution_principal_window {A B C : ℤ} {x y z : ℕ}
    (hx : 3 ≤ x) (hy : 3 ≤ y) (hz : 3 ≤ z)
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (hsol : A ^ x + B ^ y = C ^ z)
    (hle : 2 * Real.pi / bealAmpExp x y z ≤
      principalRapidity (bealFracLogGap A C x z (bealMinExp x y z)))
    (hlt : principalRapidity (bealFracLogGap A C x z (bealMinExp x y z)) <
      4 * Real.pi / bealAmpExp x y z) :
    let m := bealMinExp x y z
    let k := bealAmpExp x y z
    let N := k
    ∃ (hN : N ≠ 0),
      letI : NeZero N := ⟨hN⟩
      let t := quantizeBealMismatch N A C x z m
      IsAdmissible t ∧ ∃ w : ModularAmplificationWitness N k, w.t.val = t := by
  have hm : bealMinExp x y z ≠ 0 :=
    ne_of_gt (bealMinExp_pos hx hy hz)
  have hδ0 : 0 ≤ bealFracLogGap A C x z (bealMinExp x y z) :=
    (bealFracLogGap_pos_of_solution hm hA hB hC hsol).le
  exact beal_modularWitness_of_principal_fracGap_window A C x z
    (bealMinExp x y z) (bealAmpExp x y z) (bealAmpExp_ge_four x y z)
    hδ0 hle hlt

/-- Does not prove `BealCGANoGo`; the tautological gauge is too strong. -/
theorem beal_coprime_not_in_wide_window_of_cga_nogo
    (hnogo : BealCGANoGo) {A B C : ℤ} {x y z : ℕ}
    (hx : 3 ≤ x) (hy : 3 ≤ y) (hz : 3 ≤ z)
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (hcoprime : bealGcd A B C = 1)
    (hsol : A ^ x + B ^ y = C ^ z) :
    ¬ (2 * Real.pi / bealAmpExp x y z ≤
        bealFracLogGap A C x z (bealMinExp x y z) ∧
      bealFracLogGap A C x z (bealMinExp x y z) <
        4 * Real.pi / bealAmpExp x y z) := by
  rintro ⟨hle, hlt⟩
  obtain ⟨hN, hadm, hw⟩ :=
    beal_winding_of_solution_window hA hB hC hsol hle hlt
  let : NeZero (bealAmpExp x y z) := ⟨hN⟩
  exact hnogo A B C x y z hx hy hz hA.ne' hB.ne' hC.ne' hcoprime hsol
    (BealCGAGauge_of_ne_zero A C x z (bealMinExp x y z))
    (bealAmpExp x y z) hN ⟨hadm, hw⟩

end Theorems

end DstDiophantine
