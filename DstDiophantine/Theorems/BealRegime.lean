/-
Copyright (c) 2026 DstDiophantine contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DstDiophantine contributors
-/
import DstDiophantine.Logic.Amplitude
import DstDiophantine.Logic.Example.BealRegime
import DstDiophantine.Theorems.BealResidualSearch

/-!
# Phase 7p: Beal regime witnesses (D4L ↔ Theorems)

Connects the abstract atlas in `Logic.Example.BealRegime` to the Bool open-
residual filter and the balanced-mass seat. **Not** re-exported from
`DstDiophantine.Basic` (keeps Logic off the Diophantine barrel).

Closed / diagnostic / bookkeeping facts already live under their own names
(`not_beal_sol_of_expGcd_ge_three`, `beal_modular_payload_incompatible`,
`BealCGADiscreteClosed_iff_unitAbs`, …); this module does not re-alias them.
Atlas entailment lemmas are in `Logic.Example.BealRegime`.

Unconditional classical Beal is **not** claimed.
-/

namespace DstDiophantine

namespace Theorems

open Logic

/-! ### Open-residual Bool ↔ regime label `U` -/

/--
Classify Beal exponents by residual status (D4L reading of the Bool filter).

* `U` — open residual (`isOpenResidualExponents`)
* `T` — Beal-range exponents not flagged open (closed slice under the filter)
* `F` — exponents outside Beal range (`min < 3`); unused by the search
-/
def classifyBealExponents (x y z : ℕ) : TruthValue :=
  if isOpenResidualExponents x y z then .U
  else if 3 ≤ x ∧ 3 ≤ y ∧ 3 ≤ z then .T
  else .F

theorem classifyBealExponents_eq_U_iff {x y z : ℕ} :
    classifyBealExponents x y z = .U ↔
      isOpenResidualExponents x y z = true := by
  unfold classifyBealExponents
  split_ifs <;> simp_all

/--
A finite open-residual hit would be a classical Beal counterexample candidate
(three-way gcd 1). Soundness only; no hit is claimed.
-/
theorem open_residual_hit_is_coprime_beal
    {A B x y z : ℕ}
    (h : isOpenResidualBealPerfectPower A B x y z = true) :
    ∃ C' : ℕ,
      3 ≤ x ∧ 3 ≤ y ∧ 3 ≤ z ∧
        0 < A ∧ 0 < B ∧ 0 < C' ∧
          A ^ x + B ^ y = C' ^ z ∧
            Nat.gcd A (Nat.gcd B C') = 1 ∧
              isOpenResidualExponents x y z = true ∧
                classifyBealExponents x y z = .U := by
  obtain ⟨hopen, ⟨C', hx, hy, hz, hA, hB, hC', hsol, hgcd⟩⟩ :=
    isOpenResidualBealPerfectPower_sound h
  exact ⟨C', hx, hy, hz, hA, hB, hC', hsol, hgcd, hopen,
    classifyBealExponents_eq_U_iff.mpr hopen⟩

/-! ### Balanced seed ↔ `IsBalancedMassive` (thin L3 link) -/

/--
Geometric seat of Beal balanced diagnostics: label `T` with positive mass,
not vacuum. Signed height alone conflates the two; the continuous obstruction
is `beal_balanced_seed_lt_threshold`.
-/
theorem beal_balanced_diagnostic_seat :
    balancedAmplitude.IsBalancedMassive ∧ ¬ balancedAmplitude.IsVacuum :=
  ⟨balancedAmplitude_isBalancedMassive,
    Amplitude.not_vacuum_of_balancedMassive balancedAmplitude_isBalancedMassive⟩

end Theorems

end DstDiophantine
