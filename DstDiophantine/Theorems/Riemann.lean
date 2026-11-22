import DstDiophantine.Embedding.IntegerRotor
import DstDiophantine.Embedding.Height
import DstDiophantine.Algebra.Amplification
import DstDiophantine.Algebra.Invariant
import DstDiophantine.Algebra.Discrete
import DstDiophantine.Algebra.Operations
import DstDiophantine.Algebra.PGA
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

set_option linter.style.native false

/-!
# Critical-line balance

An off-critical real part is a boost–rotation mismatch of positive height. Classical RH is not
claimed; `RiemannAdmissibleBridge` stays open.
-/

namespace DstDiophantine

namespace Theorems

open Amplification Discrete Invariant Operations Real
open CliffordAlgebra
open _root_.DstDiophantine.Embedding

/-! ### Prime rotors (finite ensemble; no Euler product) -/

/-- Canonical rotor for a prime: `R(p) = exp(log p · iI)`. -/
noncomputable def primeRotor (p : ℕ) (hp : Nat.Prime p) : PGA :=
  integerRotor (p : ℤ) (Int.natCast_ne_zero.mpr hp.ne_zero)

theorem primeRotor_eq_integerRotor (p : ℕ) (hp : Nat.Prime p) :
    primeRotor p hp = integerRotor (p : ℤ) (Int.natCast_ne_zero.mpr hp.ne_zero) :=
  rfl

theorem primeRotor_unitary (p : ℕ) (hp : Nat.Prime p) :
    primeRotor p hp * reverse (primeRotor p hp) = 1 :=
  integerRotor_unitary _ _

/-- Finite product of prime rotors (paper's ensemble fragment; not an Euler product). -/
noncomputable def finitePrimeEnsemble (ps : List ℕ) : PGA :=
  ps.foldl
    (fun acc p =>
      if h : Nat.Prime p then acc * primeRotor p h else acc)
    1

/-! ### Critical mismatch parameters -/

/-- Boost `θ · σ` and dual rotation `θ · (1 − σ)`, for a real part `σ`. -/
def criticalMismatchParams (θ σ : ℝ) : TorsionParams where
  alpha := fun a => match a with | 0 => θ * σ | _ => 0
  beta := fun a => match a with | 0 => θ * (1 - σ) | _ => 0

theorem criticalMismatchParams_alpha0 (θ σ : ℝ) :
    (criticalMismatchParams θ σ).alpha 0 = θ * σ := rfl

theorem criticalMismatchParams_beta0 (θ σ : ℝ) :
    (criticalMismatchParams θ σ).beta 0 = θ * (1 - σ) := rfl

theorem critical_J_eq (θ σ : ℝ) :
    J (criticalMismatchParams θ σ) = (1 / 2) * θ ^ 2 * (2 * σ - 1) := by
  rw [J_coef]
  simp only [criticalMismatchParams, Fin.sum_univ_three, pow_two, mul_zero, add_zero, sub_zero]
  ring

theorem critical_JNormalized_eq (θ σ : ℝ) :
    JNormalized (criticalMismatchParams θ σ) =
      (4 / (3 * Real.pi ^ 2)) * θ ^ 2 * (2 * σ - 1) := by
  unfold JNormalized
  rw [critical_J_eq]
  ring

/-- Normalised torsional height of the critical mismatch model. -/
noncomputable def criticalHeight (θ σ : ℝ) : ℝ :=
  |JNormalized (criticalMismatchParams θ σ)|

theorem criticalHeight_eq (θ σ : ℝ) :
    criticalHeight θ σ =
      |(4 / (3 * Real.pi ^ 2)) * θ ^ 2 * (2 * σ - 1)| := by
  unfold criticalHeight
  rw [critical_JNormalized_eq]

/-- Model zero-mismatch condition `J(ρ) = 0` (Chapter 8). -/
def IsCriticalZeroEnsemble (θ σ : ℝ) : Prop :=
  J (criticalMismatchParams θ σ) = 0

theorem isCriticalZeroEnsemble_iff_JNormalized (θ σ : ℝ) :
    IsCriticalZeroEnsemble θ σ ↔ JNormalized (criticalMismatchParams θ σ) = 0 := by
  unfold IsCriticalZeroEnsemble JNormalized
  constructor
  · intro h; simp [h]
  · intro h
    have hcoef : (8 / (3 * Real.pi ^ 2) : ℝ) ≠ 0 := by
      have : 0 < Real.pi := Real.pi_pos
      positivity
    exact (mul_eq_zero.mp h).resolve_left hcoef

theorem critical_zero_iff (θ σ : ℝ) (hθ : θ ≠ 0) :
    IsCriticalZeroEnsemble θ σ ↔ σ = 1 / 2 := by
  unfold IsCriticalZeroEnsemble
  rw [critical_J_eq]
  have hθ2 : θ ^ 2 ≠ 0 := pow_ne_zero 2 hθ
  constructor
  · intro h
    have h1 : θ ^ 2 * (2 * σ - 1) = 0 := by
      have h' : (1 / 2 : ℝ) * (θ ^ 2 * (2 * σ - 1)) = 0 := by
        convert h using 1; ring
      exact (mul_eq_zero.mp h').resolve_left (by norm_num)
    have h2 : 2 * σ - 1 = 0 := (mul_eq_zero.mp h1).resolve_left hθ2
    linarith
  · intro h
    rw [h]
    ring

theorem criticalHeight_eq_zero_iff (θ σ : ℝ) (hθ : θ ≠ 0) :
    criticalHeight θ σ = 0 ↔ σ = 1 / 2 := by
  unfold criticalHeight
  rw [abs_eq_zero, ← isCriticalZeroEnsemble_iff_JNormalized, critical_zero_iff θ σ hθ]

theorem critical_off_line_height_pos (θ σ : ℝ) (hθ : θ ≠ 0) (hne : σ ≠ 1 / 2) :
    0 < criticalHeight θ σ := by
  rw [← not_le]
  intro hle
  have h0 : criticalHeight θ σ = 0 := le_antisymm hle (abs_nonneg _)
  exact hne ((criticalHeight_eq_zero_iff θ σ hθ).mp h0)

theorem critical_off_line_contradiction (θ σ : ℝ) (hθ : θ ≠ 0) (hne : σ ≠ 1 / 2)
    (hzero : IsCriticalZeroEnsemble θ σ) : False :=
  hne ((critical_zero_iff θ σ hθ).mp hzero)

/-! ### Dagger / dual-sector symmetry (§8.4) -/

theorem critical_dagger (θ σ : ℝ) :
    daggerParams (criticalMismatchParams θ σ) = criticalMismatchParams θ (1 - σ) := by
  refine congr_arg₂ TorsionParams.mk ?_ ?_
  · funext a; fin_cases a <;> rfl
  · funext a; fin_cases a
    · change θ * σ = θ * (1 - (1 - σ))
      ring
    · rfl
    · rfl

theorem critical_dagger_involutive (θ σ : ℝ) :
    daggerParams (daggerParams (criticalMismatchParams θ σ)) =
      criticalMismatchParams θ σ := by
  rw [critical_dagger, critical_dagger]
  congr 1
  ring

theorem critical_J_dagger (θ σ : ℝ) :
    J (daggerParams (criticalMismatchParams θ σ)) = -J (criticalMismatchParams θ σ) := by
  rw [critical_dagger, critical_J_eq, critical_J_eq]
  ring

theorem criticalHeight_dagger (θ σ : ℝ) :
    criticalHeight θ (1 - σ) = criticalHeight θ σ := by
  unfold criticalHeight
  have hneg :
      JNormalized (daggerParams (criticalMismatchParams θ σ)) =
        -JNormalized (criticalMismatchParams θ σ) := by
    unfold JNormalized
    rw [critical_J_dagger]
    ring
  rw [← critical_dagger, hneg, abs_neg]

theorem critical_balanced_iff (θ σ : ℝ) (hθ : θ ≠ 0) :
    (criticalMismatchParams θ σ).alpha 0 = (criticalMismatchParams θ σ).beta 0 ↔
      σ = 1 / 2 := by
  simp only [criticalMismatchParams]
  constructor
  · intro h
    have : θ * σ = θ * (1 - σ) := h
    have : σ = 1 - σ := (mul_right_inj' hθ).mp this
    linarith
  · intro h
    rw [h]
    ring

/-! ### Discrete torsional layer scale (§8.2) -/

/-- Compactification length `ℓ_N = 2π / N`. -/
noncomputable def layerScale (N : ℕ) [NeZero N] : ℝ :=
  2 * Real.pi / N

theorem layerScale_pos (N : ℕ) [NeZero N] : 0 < layerScale N := by
  unfold layerScale
  have : 0 < (N : ℝ) := Nat.cast_pos.mpr (NeZero.pos N)
  positivity

theorem critical_zero_layer_invariant (θ σ : ℝ) (hθ : θ ≠ 0) (N : ℕ) [NeZero N] :
    IsCriticalZeroEnsemble θ σ ↔ σ = 1 / 2 :=
  critical_zero_iff θ σ hθ

/-! ### Finite rational-grid certificate -/

/-- Decidable check that the reduced fraction `num/den` equals `1/2`. -/
def criticalBalanceOk (num den : ℕ) : Bool :=
  decide (den ≠ 0 ∧ 2 * num = den)

theorem criticalBalanceOk_iff (num den : ℕ) :
    criticalBalanceOk num den = true ↔ den ≠ 0 ∧ 2 * num = den := by
  simp [criticalBalanceOk]

theorem criticalHeight_rat_eq_zero_iff (θ : ℝ) (hθ : θ ≠ 0) (num den : ℕ) (hden : den ≠ 0) :
    criticalHeight θ ((num : ℝ) / den) = 0 ↔ 2 * num = den := by
  rw [criticalHeight_eq_zero_iff θ _ hθ]
  have hdenR : (den : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hden
  constructor
  · intro h
    have : (2 : ℝ) * num = den := by
      field_simp [hdenR] at h
      linarith
    exact_mod_cast this
  · intro h
    have h2 : (2 : ℝ) * num = den := by exact_mod_cast h
    field_simp [hdenR]
    linarith

/-- Grid check: `criticalBalanceOk` agrees with `2·num = den` for `den ≤ D`. -/
def allCriticalBalanceUpTo (D : ℕ) : Bool :=
  (List.range (D + 1)).all fun den =>
    (List.range (den + 1)).all fun num =>
      (den == 0) || (criticalBalanceOk num den == (decide (2 * num = den)))

theorem allCriticalBalanceUpTo_sound {D num den : ℕ}
    (hall : allCriticalBalanceUpTo D = true) (hden : den ≠ 0) (hle : den ≤ D)
    (hnum : num ≤ den) :
    criticalBalanceOk num den = decide (2 * num = den) := by
  have hden_mem : den ∈ List.range (D + 1) := List.mem_range.mpr (Nat.lt_succ_of_le hle)
  have hall_den := (List.all_eq_true.mp hall) den hden_mem
  have hnum_mem : num ∈ List.range (den + 1) := List.mem_range.mpr (Nat.lt_succ_of_le hnum)
  have hall_num := (List.all_eq_true.mp hall_den) num hnum_mem
  have hne : (den == 0) = false := by
    simp [hden]
  simp only [hne, Bool.false_or] at hall_num
  exact (beq_iff_eq (a := criticalBalanceOk num den) (b := decide (2 * num = den))).mp hall_num

theorem critical_balance_of_le_twenty {num den : ℕ} (hden : den ≠ 0) (_hle : den ≤ 20)
    (_hnum : num ≤ den) {θ : ℝ} (hθ : θ ≠ 0) :
    criticalHeight θ ((num : ℝ) / den) = 0 ↔ 2 * num = den :=
  criticalHeight_rat_eq_zero_iff θ hθ num den hden

theorem critical_balance_ok_of_le_twenty {num den : ℕ} (hden : den ≠ 0) (hle : den ≤ 20)
    (hnum : num ≤ den) :
    criticalBalanceOk num den = true ↔ 2 * num = den := by
  have heq := allCriticalBalanceUpTo_sound
    (by native_decide : allCriticalBalanceUpTo 20 = true) hden hle hnum
  constructor
  · intro hok
    exact decide_eq_true_eq.mp (heq ▸ hok)
  · intro h
    exact heq.symm ▸ decide_eq_true_eq.mpr h

/-! ### Classical RH under an explicit bridge hypothesis -/

/-- Unproved bridge: an off-critical zero would force positive admissible height. -/
def RiemannAdmissibleBridge : Prop :=
  ∀ (ρ_re : ℝ), ρ_re ≠ 1 / 2 →
    ∃ θ : ℝ, 0 < θ ∧
      IsAdmissibleContinuous (criticalMismatchParams θ ρ_re) ∧
        0 < |JNormalized (criticalMismatchParams θ ρ_re)|

theorem riemann_hypothesis_of_bridge (hbridge : RiemannAdmissibleBridge) :
    ∀ (ρ_re : ℝ), ρ_re ≠ 1 / 2 →
      ∃ θ : ℝ, 0 < θ ∧
        IsAdmissibleContinuous (criticalMismatchParams θ ρ_re) ∧
          0 < criticalHeight θ ρ_re ∧
            ¬ IsCriticalZeroEnsemble θ ρ_re := by
  intro ρ_re hne
  obtain ⟨θ, hθ, hadm, hpos⟩ := hbridge ρ_re hne
  refine ⟨θ, hθ, hadm, ?_, ?_⟩
  · simpa [criticalHeight] using hpos
  · intro hzero
    exact critical_off_line_contradiction θ ρ_re (ne_of_gt hθ) hne hzero

theorem critical_line_of_zero_ensemble (θ σ : ℝ) (hθ : θ ≠ 0)
    (h : IsCriticalZeroEnsemble θ σ) : σ = 1 / 2 :=
  (critical_zero_iff θ σ hθ).mp h

end Theorems

end DstDiophantine
