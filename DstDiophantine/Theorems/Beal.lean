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
import DstDiophantine.Theorems.Fermat
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Phase 5–7d: Beal's conjecture (problem-specific layer)

Amplification vs. admissible bound with minimal exponent `m = min(x,y,z)`,
together with the faithful null-translator encoding of `A^x + B^y - C^z`.
Shared no-go theorems come from `Framework.Amplification` (not from Fermat).

## Paper gap (not closed)

Classical Beal is **not** claimed unconditionally. The live programme (phase 7d)
is power-lattice descent:

* `BealCGADiscreteClosed` — coprime solution ⇒ `k`-fold CGA seed stays on the
  `m`-power null lattice (unproved);
* `BealUnitBaseNoGo` — no coprime solution with `|A| = 1` (unproved residual;
  Mihăilescu / Fermat–Catalan scale);
* **Proved descent:** power-lattice closure of the `k`-fold seed + pairwise
  coprimality ⇒ `|A| = 1`;
* **Window winding (proved):** gap in `[2π/k, 4π/k)` ⇒ modular witness
  (`beal_winding_of_solution_window`);
* `BealWindingBridge` — **window-regime diagnostic** (not full-solution live):
  balanced gaps `log 2 / m < 2π/k` never yield a winding witness
  (`windingTotal_eq_zero_of_rapidity_lt`);
* Legacy integer-lattice `BealCGALatticeGauge` / `BealCGADilationNoGo` —
  equal-exponent slice only; mixed exponents miss the integer lattice;
* Diagnostic `BealCGAGauge` / `BealCGANoGo` — tautological / ill-posed.

The legacy `BealModularBridge` (witness + `ConformalGaugeAdmissible`) is
**diagnostic only**: those conjuncts are equation-independently incompatible
(`beal_modular_payload_incompatible`). Continuous `BealAdmissibleBridge` remains
diagnostic (balanced seeds sit below `1/m²`).

Amplification factor for modular witnesses is `k = bealAmpExp = max(m, 4)`.
Wide principal window: `2π/k ≤ {δ} < 4π/k` on `N = k` yields `n₀ = 1`.
-/

namespace DstDiophantine

namespace Theorems

open Amplification Discrete Invariant Real ModularAmplification Framework
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

/--
Modular amplification factor: `max(m, 4)`. The fractional gap still uses
`m = bealMinExp`, but `ModularAmplificationWitness` requires `4 ≤ k`
(`modularWitness_four_le`), so `m = 3` lifts to `k = 4`.
-/
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

/-- Classical Beal conclusion shape: a common prime factor of `|A|,|B|,|C|`. -/
theorem exists_common_prime_of_bealGcd_gt_one {A B C : ℤ}
    (h : 1 < bealGcd A B C) :
    ∃ p : ℕ, Nat.Prime p ∧ p ∣ A.natAbs ∧ p ∣ B.natAbs ∧ p ∣ C.natAbs := by
  obtain ⟨p, hp, hdiv⟩ := Nat.exists_prime_and_dvd (ne_of_gt h)
  refine ⟨p, hp, ?_, ?_, ?_⟩
  · exact Nat.dvd_trans hdiv (bealGcd_dvd_left A B C)
  · exact Nat.dvd_trans hdiv (bealGcd_dvd_mid A B C)
  · exact Nat.dvd_trans hdiv (bealGcd_dvd_right A B C)

/-! ### Pairwise coprimality from three-way gcd + the equation -/

private theorem beal_prime_dvd_B_of_dvd_AC {A B C : ℤ} {x y z p : ℕ}
    (hp : Nat.Prime p) (hx : 0 < x) (_hy : 0 < y) (hz : 0 < z)
    (hsol : A ^ x + B ^ y = C ^ z)
    (hpA : p ∣ A.natAbs) (hpC : p ∣ C.natAbs) : p ∣ B.natAbs := by
  have hAℤ : (p : ℤ) ∣ A := Int.natCast_dvd.mpr hpA
  have hCℤ : (p : ℤ) ∣ C := Int.natCast_dvd.mpr hpC
  have hAx : (p : ℤ) ∣ A ^ x := dvd_pow hAℤ (ne_of_gt hx)
  have hCz : (p : ℤ) ∣ C ^ z := dvd_pow hCℤ (ne_of_gt hz)
  have hBy : (p : ℤ) ∣ B ^ y := by
    have hsub : (p : ℤ) ∣ C ^ z - A ^ x := dvd_sub hCz hAx
    have heq : C ^ z - A ^ x = B ^ y := by
      have := congrArg (fun t => t - A ^ x) hsol
      simpa [add_sub_cancel_left] using this.symm
    rwa [heq] at hsub
  have hAbs : p ∣ (B ^ y).natAbs := Int.natCast_dvd.mp hBy
  rw [Int.natAbs_pow] at hAbs
  exact hp.dvd_of_dvd_pow hAbs

private theorem beal_prime_dvd_C_of_dvd_AB {A B C : ℤ} {x y z p : ℕ}
    (hp : Nat.Prime p) (hx : 0 < x) (hy : 0 < y) (_hz : 0 < z)
    (hsol : A ^ x + B ^ y = C ^ z)
    (hpA : p ∣ A.natAbs) (hpB : p ∣ B.natAbs) : p ∣ C.natAbs := by
  have hAℤ : (p : ℤ) ∣ A := Int.natCast_dvd.mpr hpA
  have hBℤ : (p : ℤ) ∣ B := Int.natCast_dvd.mpr hpB
  have hAx : (p : ℤ) ∣ A ^ x := dvd_pow hAℤ (ne_of_gt hx)
  have hBy : (p : ℤ) ∣ B ^ y := dvd_pow hBℤ (ne_of_gt hy)
  have hCz : (p : ℤ) ∣ C ^ z := by
    have : (p : ℤ) ∣ A ^ x + B ^ y := dvd_add hAx hBy
    rwa [hsol] at this
  have hAbs : p ∣ (C ^ z).natAbs := Int.natCast_dvd.mp hCz
  rw [Int.natAbs_pow] at hAbs
  exact hp.dvd_of_dvd_pow hAbs

private theorem beal_prime_dvd_A_of_dvd_BC {A B C : ℤ} {x y z p : ℕ}
    (hp : Nat.Prime p) (_hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hsol : A ^ x + B ^ y = C ^ z)
    (hpB : p ∣ B.natAbs) (hpC : p ∣ C.natAbs) : p ∣ A.natAbs := by
  have hBℤ : (p : ℤ) ∣ B := Int.natCast_dvd.mpr hpB
  have hCℤ : (p : ℤ) ∣ C := Int.natCast_dvd.mpr hpC
  have hBy : (p : ℤ) ∣ B ^ y := dvd_pow hBℤ (ne_of_gt hy)
  have hCz : (p : ℤ) ∣ C ^ z := dvd_pow hCℤ (ne_of_gt hz)
  have hAx : (p : ℤ) ∣ A ^ x := by
    have hsub : (p : ℤ) ∣ C ^ z - B ^ y := dvd_sub hCz hBy
    have heq : C ^ z - B ^ y = A ^ x := by
      have := congrArg (fun t => t - B ^ y) hsol
      simpa [add_comm, add_sub_cancel_right] using this.symm
    rwa [heq] at hsub
  have hAbs : p ∣ (A ^ x).natAbs := Int.natCast_dvd.mp hAx
  rw [Int.natAbs_pow] at hAbs
  exact hp.dvd_of_dvd_pow hAbs

/-- A three-way coprime Beal solution is pairwise coprime on absolute values. -/
theorem beal_pairwise_coprime {A B C : ℤ} {x y z : ℕ}
    (hA : A ≠ 0) (hB : B ≠ 0) (_hC : C ≠ 0)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hgcd : bealGcd A B C = 1)
    (hsol : A ^ x + B ^ y = C ^ z) :
    Nat.Coprime A.natAbs B.natAbs ∧
      Nat.Coprime A.natAbs C.natAbs ∧
        Nat.Coprime B.natAbs C.natAbs := by
  have hAC : Nat.Coprime A.natAbs C.natAbs := by
    rw [Nat.coprime_iff_gcd_eq_one]
    by_contra hne
    have hpos : 0 < Nat.gcd A.natAbs C.natAbs :=
      Nat.gcd_pos_of_pos_left _ (Int.natAbs_pos.mpr hA)
    have hgt : 1 < Nat.gcd A.natAbs C.natAbs :=
      lt_of_le_of_ne (Nat.succ_le_of_lt hpos) (Ne.symm hne)
    obtain ⟨p, hp, hdiv⟩ := Nat.exists_prime_and_dvd (ne_of_gt hgt)
    have hpA : p ∣ A.natAbs := Nat.dvd_trans hdiv (Nat.gcd_dvd_left _ _)
    have hpC : p ∣ C.natAbs := Nat.dvd_trans hdiv (Nat.gcd_dvd_right _ _)
    have hpB : p ∣ B.natAbs := beal_prime_dvd_B_of_dvd_AC hp hx hy hz hsol hpA hpC
    have hpG : p ∣ bealGcd A B C :=
      Nat.dvd_gcd hpA (Nat.dvd_gcd hpB hpC)
    exact Nat.Prime.not_dvd_one hp (by simpa [hgcd] using hpG)
  have hAB : Nat.Coprime A.natAbs B.natAbs := by
    rw [Nat.coprime_iff_gcd_eq_one]
    by_contra hne
    have hpos : 0 < Nat.gcd A.natAbs B.natAbs :=
      Nat.gcd_pos_of_pos_left _ (Int.natAbs_pos.mpr hA)
    have hgt : 1 < Nat.gcd A.natAbs B.natAbs :=
      lt_of_le_of_ne (Nat.succ_le_of_lt hpos) (Ne.symm hne)
    obtain ⟨p, hp, hdiv⟩ := Nat.exists_prime_and_dvd (ne_of_gt hgt)
    have hpA : p ∣ A.natAbs := Nat.dvd_trans hdiv (Nat.gcd_dvd_left _ _)
    have hpB : p ∣ B.natAbs := Nat.dvd_trans hdiv (Nat.gcd_dvd_right _ _)
    have hpC : p ∣ C.natAbs := beal_prime_dvd_C_of_dvd_AB hp hx hy hz hsol hpA hpB
    have hpG : p ∣ bealGcd A B C :=
      Nat.dvd_gcd hpA (Nat.dvd_gcd hpB hpC)
    exact Nat.Prime.not_dvd_one hp (by simpa [hgcd] using hpG)
  have hBC : Nat.Coprime B.natAbs C.natAbs := by
    rw [Nat.coprime_iff_gcd_eq_one]
    by_contra hne
    have hpos : 0 < Nat.gcd B.natAbs C.natAbs :=
      Nat.gcd_pos_of_pos_left _ (Int.natAbs_pos.mpr hB)
    have hgt : 1 < Nat.gcd B.natAbs C.natAbs :=
      lt_of_le_of_ne (Nat.succ_le_of_lt hpos) (Ne.symm hne)
    obtain ⟨p, hp, hdiv⟩ := Nat.exists_prime_and_dvd (ne_of_gt hgt)
    have hpB : p ∣ B.natAbs := Nat.dvd_trans hdiv (Nat.gcd_dvd_left _ _)
    have hpC : p ∣ C.natAbs := Nat.dvd_trans hdiv (Nat.gcd_dvd_right _ _)
    have hpA : p ∣ A.natAbs := beal_prime_dvd_A_of_dvd_BC hp hx hy hz hsol hpB hpC
    have hpG : p ∣ bealGcd A B C :=
      Nat.dvd_gcd hpA (Nat.dvd_gcd hpB hpC)
    exact Nat.Prime.not_dvd_one hp (by simpa [hgcd] using hpG)
  exact ⟨hAB, hAC, hBC⟩

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

/--
Fractional log-gap used as the Beal modular seed:
`δ = (z/m) log|C| − (x/m) log|A|`.
When `m = bealMinExp x y z` and `A^x + B^y = C^z` with positive terms,
`m · δ = log(1 + B^y / A^x)`.
-/
noncomputable def bealFracLogGap (A C : ℤ) (x z m : ℕ) : ℝ :=
  (z : ℝ) / m * Real.log (Int.natAbs C) - (x : ℝ) / m * Real.log (Int.natAbs A)

theorem bealFracLogGap_mul (A C : ℤ) (x z m : ℕ) (hm : m ≠ 0) :
    (m : ℝ) * bealFracLogGap A C x z m =
      (z : ℝ) * Real.log (Int.natAbs C) - (x : ℝ) * Real.log (Int.natAbs A) := by
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm
  unfold bealFracLogGap
  field_simp [hm0]

/-- Positive Beal solutions satisfy `A^x < C^z`. -/
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

/-- On a positive Beal solution, m · δ = log(1 + B^y / A^x). -/
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

/-- Equal exponents specialise the fractional gap to `log|C| − log|A|`. -/
theorem bealFracLogGap_eq_exp (A C : ℤ) (p : ℕ) (hp : p ≠ 0) :
    bealFracLogGap A C p p p =
      Real.log (Int.natAbs C) - Real.log (Int.natAbs A) := by
  have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp
  unfold bealFracLogGap
  field_simp [hp0]

/-- On a positive Beal solution, `δ = log(1 + B^y / A^x) / m`. -/
theorem bealFracLogGap_eq_log_one_add_div {A B C : ℤ} {x y z m : ℕ} (hm : m ≠ 0)
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (hsol : A ^ x + B ^ y = C ^ z) :
    bealFracLogGap A C x z m =
      Real.log (1 + (B : ℝ) ^ y / (A : ℝ) ^ x) / (m : ℝ) := by
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm
  have hmul := bealFracLogGap_of_solution hm hA hB hC hsol
  field_simp [hm0] at hmul ⊢
  linarith [hmul]

/-- Positive Beal solutions have strictly positive fractional log-gap. -/
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

/-- Winding threshold sits strictly above the continuous seed cone when `m = 3`. -/
theorem beal_winding_threshold_gt_half_pi_of_minExp_eq_three
    {x y z : ℕ} (hm : bealMinExp x y z = 3) :
    Real.pi / 2 < 2 * Real.pi / (bealMinExp x y z : ℝ) := by
  rw [hm]; nlinarith [Real.pi_pos]

/-- Balanced model gap `log 2 / m` misses the modular winding threshold `2π / m`. -/
theorem beal_balanced_fracGap_lt_winding_threshold {m : ℕ} (hm : 0 < m) :
    Real.log 2 / (m : ℝ) < 2 * Real.pi / (m : ℝ) := by
  have hlog : Real.log 2 < 2 * Real.pi := by
    have h1 : Real.log 2 < 1 := by
      have h := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) (by norm_num)
      norm_num at h ⊢; exact h
    exact h1.trans (by nlinarith [Real.pi_gt_three])
  exact div_lt_div_of_pos_right hlog (Nat.cast_pos.mpr hm)

/-- Balanced gap also misses the lifted threshold `2π / bealAmpExp`. -/
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
      -- `4 log 2 < 6π` from `log 2 < 1` and `π > 3`
      have hπ : (3 : ℝ) < Real.pi := Real.pi_gt_three
      have : (4 : ℝ) * Real.log 2 < 6 * Real.pi := by
        nlinarith [hlog1, hπ]
      convert this using 1 <;> ring
  exact (div_lt_div_iff₀ hmR hkR).mpr this

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

/-! ### Continuous bridge (diagnostic) -/

/--
Continuous Beal amplification bridge (**diagnostic**).

* **Assumption (unproved):** a coprime Beal solution yields an admissible powered
  pure-boost mismatch whose seed already exceeds `1/m²`.
* **Proved core:** `beal_amplification_contradiction` /
  `continuous_amplification_contradiction`.
* **Obstruction:** at the balanced scale `θ = log 2 / m` the seed is below
  `1/m²` (`beal_balanced_seed_lt_threshold`).
* **Live programme:** `BealModularBridge` (solution-dependent modular payload).
* **Does not claim:** unconditional classical Beal.
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

/-! ### Balanced-seed diagnostic (continuous obstruction) -/

/-- At `θ = log 2 / m`, the seed height is below the continuous Beal threshold. -/
theorem beal_balanced_seed_lt_threshold {x y z : ℕ}
    (hx : 3 ≤ x) (hy : 3 ≤ y) (hz : 3 ≤ z) :
    |JNormalized (pureBoost (Real.log 2 / (bealMinExp x y z : ℝ)))| <
      (1 : ℝ) / (bealMinExp x y z : ℝ) ^ 2 :=
  fermat_balanced_seed_lt_threshold (bealMinExp_ge_one hx hy hz)

/-- Balanced seed remains admissible after `m`-fold amplification. -/
theorem beal_balanced_amplification_admissible {x y z : ℕ}
    (hx : 3 ≤ x) (hy : 3 ≤ y) (hz : 3 ≤ z) :
    IsAdmissibleContinuous
      (pureBoost
        ((bealMinExp x y z : ℝ) *
          (Real.log 2 / (bealMinExp x y z : ℝ)))) :=
  fermat_balanced_amplification_admissible (bealMinExp_ge_one hx hy hz)

/-! ### Equal-exponent recovery toward FLT -/

/-- Equal exponents specialise Beal's additive motor to Fermat's. -/
theorem beal_eq_exp_motor (A B C : ℤ) (p : ℕ) :
    powerSumMotor (bealEquation A B C p p p) =
      powerSumMotor (fermatEquation A B C p) := by
  rw [bealEquation_eq_fermat]

/--
Under the continuous Beal bridge, an equal-exponent solution with `p ≥ 3` cannot
be primitive (`bealGcd = 1`). Still conditional on the bridge.
-/
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

/--
**Diagnostic** modular Beal bridge (do not treat as the live programme).

The three conjuncts are equation-independently incompatible: a
`ModularAmplificationWitness` with nonzero winding rules out
`ConformalGaugeAdmissible` under the present PGA real-scale identification
(`beal_modular_payload_incompatible`). Live programme (phase 7d):
`BealCGADiscreteClosed` + `BealUnitBaseNoGo`.
-/
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

/-- Winding witness and PGA-identified conformal gauge cannot hold together. -/
theorem beal_modular_payload_incompatible {N k : ℕ} [NeZero N]
    (w : ModularAmplificationWitness N k) :
    ¬ ConformalGaugeAdmissible
        (scaleTorsion (k : ℝ) (toTorsionParams w.t.val)) :=
  ModularAmplificationWitness.not_admissible_real_scale w

/-- Conditional classical Beal from the diagnostic modular bridge. -/
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

/-- Equal-exponent specialisation under the diagnostic modular Beal bridge. -/
theorem beal_eq_exp_not_coprime_of_modular_bridge (hbridge : BealModularBridge)
    (A B C : ℤ) (p : ℕ) (hp : 3 ≤ p)
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hsol : A ^ p + B ^ p = C ^ p) :
    1 < bealGcd A B C :=
  beal_conjecture_of_modular_bridge hbridge A B C p p p hp hp hp hA hB hC hsol

/-! ### Partial winding on the principal interval -/

/--
If `2π/k ≤ δ < 2π` and `k ∣ N`, the quantised Beal seed (gap still uses `m`)
has nonzero total winding under amplification factor `k`.
-/
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

/--
**Window-regime** Beal winding bridge (not the live full-solution programme).

Asserts that a coprime solution yields some lattice `N` carrying an admissible
modular winding witness with `k = bealAmpExp`. The **proved** half is the wide
window construction (`beal_winding_of_solution_window`). Balanced gaps
`δ ≈ log 2 / m < 2π/k` never wind (`windingTotal_eq_zero_of_rapidity_lt`), so
this cannot be the live bridge for all solutions. Live programme (phase 7d):
`BealCGADiscreteClosed` + `BealUnitBaseNoGo`.
-/
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

/-- Raising a fractional root magnitude to `m` recovers the integer power. -/
theorem bealRootMag_pow (n : ℤ) (e m : ℕ) (hm : m ≠ 0) :
    bealRootMag n e m ^ m = (n.natAbs : ℝ) ^ e := by
  unfold bealRootMag
  have hnn : (0 : ℝ) ≤ (n.natAbs : ℝ) := Nat.cast_nonneg _
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm
  have hmul : ((e : ℝ) / m) * m = e := by field_simp [hm0]
  rw [← Real.rpow_natCast _ m, ← Real.rpow_mul hnn, hmul, Real.rpow_natCast]

/-- Equal-exponent roots collapse to absolute values. -/
theorem bealRootMag_eq_natAbs (n : ℤ) (p : ℕ) (hp : p ≠ 0) :
    bealRootMag n p p = (n.natAbs : ℝ) := by
  unfold bealRootMag
  have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp
  have : (p : ℝ) / p = 1 := by field_simp [hp0]
  rw [this, Real.rpow_one]

/-- Fractional log-gap equals the log-ratio of fractional-power magnitudes. -/
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

/--
On a positive Beal solution the three root-magnitudes satisfy the Fermat-shaped
identity `α^m + β^m = γ^m`. PGA additive faithfulness and CGA dilation are thus
two faces of the same solution.
-/
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

/-- Beal root magnitudes always lie on the `m`-power null lattice. -/
theorem bealRootMag_isCGAPowerLatticePoint (A : ℤ) (x m : ℕ)
    (hA : A ≠ 0) (hm : m ≠ 0) :
    IsCGAPowerLatticePoint (bealRootMag A x m) m := by
  refine ⟨((A.natAbs : ℤ) ^ x), pow_ne_zero x
      (by exact_mod_cast ne_of_gt (Int.natAbs_pos.mpr hA)), ?_⟩
  have hpow := bealRootMag_pow A x m hm
  calc bealRootMag A x m ^ m
      = (A.natAbs : ℝ) ^ x := hpow
    _ = (((A.natAbs : ℤ) ^ x : ℤ) : ℝ) := by
        rw [Int.cast_pow]; rfl

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

/--
**Diagnostic** CGA gauge: A/C root-magnitudes embed as null points.
Always true (`BealCGAGauge_of_ne_zero`); do **not** use as a live no-go hypothesis.
Live gauge: `BealCGALatticeGauge`. The third root `B` is likewise null by
`conformalPoint_sq` (no separate triple predicate).
-/
def BealCGAGauge (A C : ℤ) (x z m : ℕ) : Prop :=
  conformalPoint (bealRootMag A x m) * conformalPoint (bealRootMag A x m) = 0 ∧
    conformalPoint (bealRootMag C z m) * conformalPoint (bealRootMag C z m) = 0

theorem BealCGAGauge_of_ne_zero (A C : ℤ) (x z m : ℕ) :
    BealCGAGauge A C x z m :=
  ⟨conformalPoint_sq _, conformalPoint_sq _⟩

/-- Dilation weights `(1, e^δ, e^{2δ})` relating the two Beal CGA seeds. -/
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

/-- Beal seed under `k`-fold CGA dilation (via `pointVec_exp_nat_mul`). -/
theorem beal_cga_k_fold_dilation (A C : ℤ) (x z m k : ℕ) :
    let δ := bealFracLogGap A C x z m
    let a := bealRootMag A x m
    CGA1.pointVec (Real.exp ((k : ℝ) * δ) * a) =
      CGA1.pointVec (Real.exp δ ^ k * a) := by
  intro δ a
  exact CGA1.pointVec_exp_nat_mul a δ k

/-! ### Non-tautological DST integer null lattice gauge -/

/--
**Live** CGA lattice gauge: all three root-magnitudes lie on the DST discrete
integer null lattice `X(n)`, `n ≠ 0`. **Not** identified with PGA
`IsAdmissibleContinuous`. Fails for typical mixed-exponent fractional powers.
-/
def BealCGALatticeGauge (A B C : ℤ) (x y z m : ℕ) : Prop :=
  IsCGAIntegerPoint (bealRootMag A x m) ∧
    IsCGAIntegerPoint (bealRootMag B y m) ∧
      IsCGAIntegerPoint (bealRootMag C z m)

/-- Equal exponents place all three roots on the integer null lattice. -/
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

/--
Equal-exponent positive solutions are integer Fermat equations on absolute
values (no unconditional FLT claimed). Lattice membership is immediate from
`BealCGALatticeGauge_of_eq_exp`.
-/
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

/-- Mixed-exponent seed `2^{4/3}` misses the integer lattice (diagnostic). -/
theorem not_BealCGALatticeGauge_two_two_two_four_four_three :
    ¬ BealCGALatticeGauge 2 2 2 4 4 3 3 := by
  intro h
  have : IsCGAIntegerPoint (bealRootMag 2 4 3) := h.1
  unfold bealRootMag at this
  change IsCGAIntegerPoint ((2 : ℝ) ^ ((4 : ℝ) / 3)) at this
  exact not_isCGAIntegerPoint_two_rpow_four_thirds this

/-! ### Diagnostic / live CGA no-go predicates -/

/--
**Diagnostic** geometric no-go (ill-posed as a live bridge).

Uses tautological `BealCGAGauge`, so together with the proved window construction
it would forbid coprime solutions from ever entering the wide gap window —
equation-independently over-strong. Kept for the logical relation lemma below.
Live programme: `BealCGADilationNoGo`.
-/
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

/--
**Live** CGA dilation / lattice no-go (unproved).

A coprime solution whose root-magnitudes lie on the DST integer null lattice
cannot carry a modular winding witness. Uses `BealCGALatticeGauge` (fails for
typical mixed exponents), not tautological `BealCGAGauge` / PGA real-scale.
-/
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

/-- Conditional classical Beal from winding + diagnostic CGA no-go. -/
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

/--
Conditional classical Beal from winding + live lattice/dilation no-go, for
solutions that satisfy the lattice gauge (includes equal exponents).
-/
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

/-- Equal-exponent specialisation of the live lattice conditional. -/
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

/--
`k`-fold CGA dilation of the A-root seed along the A–C fractional gap:
`α · e^{kδ}`. Equals `γ^k / α^{k-1}` when `α, γ > 0`.
-/
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
    try field_simp [ne_of_gt hα]
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

/--
If the `k`-fold seed lies on the `m`-power lattice, then
`|A|^{x(k-1)}` divides `|C|^{k z}` in `ℕ`.
-/
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

/--
Pairwise AC-coprimality + power-lattice closure of the `k`-fold seed
(`k ≥ 2`) forces `|A| = 1`. Unconditional descent lemma (no bridge).
-/
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
  have hpow : 0 < x * (k - 1) := by
    have : 0 < k - 1 := Nat.sub_pos_of_lt hk
    exact Nat.mul_pos hx this
  -- If a prime divides A, it divides C via the divisibility, contradicting hac.
  rw [Nat.eq_one_iff_not_exists_prime_dvd]
  intro p hp hpA
  have hpC : p ∣ C.natAbs := by
    have : p ∣ A.natAbs ^ (x * (k - 1)) :=
      dvd_pow hpA (ne_of_gt hpow)
    have : p ∣ C.natAbs ^ (k * z) := Nat.dvd_trans this hdvd
    exact hp.dvd_of_dvd_pow this
  exact Nat.Prime.not_coprime_iff_dvd.mpr ⟨p, hp, hpA, hpC⟩ hac

/-- Balanced model rapidity never yields a modular winding witness on any `N`. -/
theorem beal_balanced_gap_no_modularWitness (N : ℕ) [NeZero N] {x y z : ℕ}
    (hx : 3 ≤ x) (hy : 3 ≤ y) (hz : 3 ≤ z) :
    ¬ ∃ w : ModularAmplificationWitness N (bealAmpExp x y z),
      w.t.val = pureBoostSeedOfRapidity N
        (Real.log 2 / (bealMinExp x y z : ℝ)) := by
  intro hw
  exact not_exists_modularWitness_of_balanced_gap N (bealMinExp x y z)
    (bealAmpExp x y z) (bealMinExp_pos hx hy hz) (bealAmpExp_pos x y z)
    (beal_balanced_fracGap_lt_ampExp_threshold hx hy hz) hw

/-! ### Live bridges: discrete closure + unit-base residual -/

/--
**Live** geometric half (unproved): a coprime Beal solution has its `k`-fold
CGA seed on the `m`-power null lattice. Not the tautological statement that
root magnitudes themselves lie on that lattice (`bealRootMag_isCGAPowerLatticePoint`).
-/
def BealCGADiscreteClosed : Prop :=
  ∀ (A B C : ℤ) (x y z : ℕ) (_hx : 3 ≤ x) (_hy : 3 ≤ y) (_hz : 3 ≤ z)
    (_hA : A ≠ 0) (_hB : B ≠ 0) (_hC : C ≠ 0),
    bealGcd A B C = 1 →
    A ^ x + B ^ y = C ^ z →
      IsCGAPowerLatticePoint
        (bealCGAKFoldMag A C x z (bealMinExp x y z) (bealAmpExp x y z))
        (bealMinExp x y z)

/--
**Live** residual half (unproved): no coprime Beal solution has `|A| = 1`.
Elementary special cases (e.g. `1 + b³ = c³`) are available separately; the
general statement is Mihăilescu / Fermat–Catalan scale and is not claimed here.
-/
def BealUnitBaseNoGo : Prop :=
  ∀ (A B C : ℤ) (x y z : ℕ) (_hx : 3 ≤ x) (_hy : 3 ≤ y) (_hz : 3 ≤ z)
    (_hA : A ≠ 0) (_hB : B ≠ 0) (_hC : C ≠ 0),
    bealGcd A B C = 1 →
    A.natAbs = 1 →
      ¬ A ^ x + B ^ y = C ^ z

/-- Conditional classical Beal from discrete closure + unit-base no-go. -/
theorem beal_conjecture_of_discreteClosed_and_unitBaseNoGo
    (hclosed : BealCGADiscreteClosed) (hnogo : BealUnitBaseNoGo) :
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
  have hlat := hclosed A B C x y z hx hy hz hA hB hC hcoprime hsol
  have hm : bealMinExp x y z ≠ 0 := ne_of_gt (bealMinExp_pos hx hy hz)
  have hx0 : 0 < x := Nat.lt_of_lt_of_le (by decide : 0 < 3) hx
  have hy0 : 0 < y := Nat.lt_of_lt_of_le (by decide : 0 < 3) hy
  have hz0 : 0 < z := Nat.lt_of_lt_of_le (by decide : 0 < 3) hz
  have hk : 2 ≤ bealAmpExp x y z :=
    Nat.le_trans (by decide : 2 ≤ 4) (bealAmpExp_ge_four x y z)
  have hA1 : A.natAbs = 1 :=
    beal_natAbs_eq_one_of_kFold_powerLattice hm hA hB hC hx0 hy0 hz0 hk
      hcoprime hsol hlat
  exact hnogo A B C x y z hx hy hz hA hB hC hcoprime hA1 hsol

/-- Elementary unit-base fragment: `1 + b^3 = c^3` has no positive solutions. -/
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

/--
Wide principal window: if `4 ≤ k` and the gap lies in `[2π/k, 4π/k)`, the
quantised seed on `N = k` is a modular winding witness with `n₀ = 1`.

Depends only on the gap size (no solution hypothesis). Includes `m = 3` via
`k = bealAmpExp = 4` (window `[π/2, π)`).
-/
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

/-- Specialisation of the wide window to `k = bealAmpExp`. -/
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

/--
Torus fold: if the *principal* gap lies in the wide window, the quantised seed
(using the unreduced gap) still yields a modular winding witness, because
`quantizeRapidity` depends on `θ` only through its class mod `2π`.
-/
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

/--
Positive solution whose fractional gap lies in the wide principal window yields
a modular winding witness. Specialises the gap-only construction; no coprimality
hypothesis. Closes the window half of BealWindingBridge; the balanced regime
δ ≈ log 2 / m < 2π/k remains open.
-/
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

/-- Torus-folded window case for a positive Beal-range solution. -/
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

/--
Diagnostic relation: the ill-posed BealCGANoGo plus the window construction
implies that a coprime positive solution cannot lie in the wide gap window.
(Does not prove BealCGANoGo; records the over-strength of the tautological gauge.)
-/
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
