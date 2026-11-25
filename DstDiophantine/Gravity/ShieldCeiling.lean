import DstDiophantine.Algebra.RelativeRotor
import DstDiophantine.Gravity.DualControl
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Mass ceiling of a shielded configuration

No electromagnetic coupling and no laboratory protocol is derived.
-/

namespace DstDiophantine

namespace Gravity

open scoped Real
open Operations Invariant Admissible

/-! ### Axis inequalities -/

private theorem axis_sum_sq_le {k α β : ℝ}
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hs : α + β ≤ k) :
    (α + β) ^ 2 ≤ k ^ 2 := by
  nlinarith

private theorem axis_diff_sq_le {k α β : ℝ}
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hs : α + β ≤ k) :
    (α - β) ^ 2 ≤ k ^ 2 := by
  nlinarith

theorem axis_trade_off {k α β : ℝ}
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hs : α + β ≤ k) :
    2 * k ^ 2 * (α ^ 2 + β ^ 2) ≤ k ^ 4 + (α ^ 2 - β ^ 2) ^ 2 := by
  have h1 : (0 : ℝ) ≤ k ^ 2 - (α + β) ^ 2 :=
    sub_nonneg.mpr (axis_sum_sq_le hα hβ hs)
  have h2 : (0 : ℝ) ≤ k ^ 2 - (α - β) ^ 2 :=
    sub_nonneg.mpr (axis_diff_sq_le hα hβ hs)
  nlinarith [mul_nonneg h1 h2]

theorem axis_abs_density_le {k α β : ℝ}
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hs : α + β ≤ k) :
    |α ^ 2 - β ^ 2| ≤ k ^ 2 := by
  have hk : 0 ≤ k := by linarith
  rw [abs_le]
  constructor <;> nlinarith

private theorem elementary_two_ge {K t₀ t₁ t₂ : ℝ}
    (h₀ : |t₀| ≤ K) (h₁ : |t₁| ≤ K) (h₂ : |t₂| ≤ K) :
    -(K ^ 2) ≤ t₀ * t₁ + t₀ * t₂ + t₁ * t₂ := by
  obtain ⟨h₀l, h₀u⟩ := abs_le.mp h₀
  obtain ⟨h₁l, h₁u⟩ := abs_le.mp h₁
  obtain ⟨h₂l, h₂u⟩ := abs_le.mp h₂
  rcases le_total 0 (t₀ + t₁) with hsum | hsum
  · nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ K - t₀)
      (by linarith : (0 : ℝ) ≤ K - t₁),
      mul_nonneg (by linarith : (0 : ℝ) ≤ t₂ + K) hsum]
  · nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ K + t₀)
      (by linarith : (0 : ℝ) ≤ K + t₁),
      mul_nonneg (by linarith : (0 : ℝ) ≤ K - t₂)
        (by linarith : (0 : ℝ) ≤ -(t₀ + t₁))]

private theorem three_axis_assembly {k t₀ t₁ t₂ u₀ u₁ u₂ : ℝ}
    (h₀ : 2 * k ^ 2 * u₀ ≤ k ^ 4 + t₀ ^ 2)
    (h₁ : 2 * k ^ 2 * u₁ ≤ k ^ 4 + t₁ ^ 2)
    (h₂ : 2 * k ^ 2 * u₂ ≤ k ^ 4 + t₂ ^ 2)
    (he : -(k ^ 4) ≤ t₀ * t₁ + t₀ * t₂ + t₁ * t₂) :
    2 * k ^ 2 * (u₀ + u₁ + u₂) ≤ 5 * k ^ 4 + (t₀ + t₁ + t₂) ^ 2 := by
  nlinarith [h₀, h₁, h₂, he]

/-! ### The trade-off between unsigned mass and mismatch -/

theorem pi_sq_mass_le_shield_ceiling_add_J_sq (p : TorsionParams)
    (h : IsAdmissibleContinuousLegacy p) :
    Real.pi ^ 2 * mass p ≤ 5 * Real.pi ^ 4 / 16 + 4 * J p ^ 2 := by
  have hax : ∀ a : Fin 3,
      2 * (Real.pi / 2) ^ 2 * (p.alpha a ^ 2 + p.beta a ^ 2)
        ≤ (Real.pi / 2) ^ 4 + (p.alpha a ^ 2 - p.beta a ^ 2) ^ 2 := fun a =>
    axis_trade_off (h a).1 (h a).2.1 (h a).2.2
  have habs : ∀ a : Fin 3,
      |p.alpha a ^ 2 - p.beta a ^ 2| ≤ (Real.pi / 2) ^ 2 := fun a =>
    axis_abs_density_le (h a).1 (h a).2.1 (h a).2.2
  have he : -((Real.pi / 2) ^ 4) ≤
      (p.alpha 0 ^ 2 - p.beta 0 ^ 2) * (p.alpha 1 ^ 2 - p.beta 1 ^ 2) +
        (p.alpha 0 ^ 2 - p.beta 0 ^ 2) * (p.alpha 2 ^ 2 - p.beta 2 ^ 2) +
        (p.alpha 1 ^ 2 - p.beta 1 ^ 2) * (p.alpha 2 ^ 2 - p.beta 2 ^ 2) := by
    have h3 := elementary_two_ge (habs 0) (habs 1) (habs 2)
    nlinarith [h3]
  have hcore := three_axis_assembly (hax 0) (hax 1) (hax 2) he
  rw [mass_coef, J_coef]
  simp only [Fin.sum_univ_three]
  nlinarith [hcore]

theorem pi_sq_mass_le_shield_ceiling_add_J_sq_of_continuous (p : TorsionParams)
    (h : IsAdmissibleContinuous p) :
    Real.pi ^ 2 * mass p ≤ 5 * Real.pi ^ 4 / 4 + 4 * J p ^ 2 := by
  have hax : ∀ a : Fin 3,
      2 * Real.pi ^ 2 * (p.alpha a ^ 2 + p.beta a ^ 2)
        ≤ Real.pi ^ 4 + (p.alpha a ^ 2 - p.beta a ^ 2) ^ 2 := fun a =>
    axis_trade_off (k := Real.pi) (h a).1 (h a).2.1 <|
      Admissible.admissibleContinuous_sum_le_pi p h a
  have habs : ∀ a : Fin 3,
      |p.alpha a ^ 2 - p.beta a ^ 2| ≤ Real.pi ^ 2 := fun a =>
    axis_abs_density_le (k := Real.pi) (h a).1 (h a).2.1 <|
      Admissible.admissibleContinuous_sum_le_pi p h a
  have he : -Real.pi ^ 4 ≤
      (p.alpha 0 ^ 2 - p.beta 0 ^ 2) * (p.alpha 1 ^ 2 - p.beta 1 ^ 2) +
        (p.alpha 0 ^ 2 - p.beta 0 ^ 2) * (p.alpha 2 ^ 2 - p.beta 2 ^ 2) +
        (p.alpha 1 ^ 2 - p.beta 1 ^ 2) * (p.alpha 2 ^ 2 - p.beta 2 ^ 2) := by
    have h3 := elementary_two_ge (habs 0) (habs 1) (habs 2)
    nlinarith [h3]
  have hcore := three_axis_assembly (hax 0) (hax 1) (hax 2) he
  rw [mass_coef, J_coef]
  simp only [Fin.sum_univ_three]
  nlinarith [hcore]

theorem massNormalized_le_shield_curve (p : TorsionParams)
    (h : IsAdmissibleContinuousLegacy p) :
    massNormalized p ≤ 5 / 6 + (3 / 2) * JNormalized p ^ 2 := by
  have hraw := pi_sq_mass_le_shield_ceiling_add_J_sq p h
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  have key : massNormalized p - (5 / 6 + (3 / 2) * JNormalized p ^ 2)
      = (8 / (3 * Real.pi ^ 4)) *
        (Real.pi ^ 2 * mass p - (5 * Real.pi ^ 4 / 16 + 4 * J p ^ 2)) := by
    unfold massNormalized JNormalized
    field_simp
    ring
  rw [← sub_nonpos, key]
  have hneg : Real.pi ^ 2 * mass p - (5 * Real.pi ^ 4 / 16 + 4 * J p ^ 2) ≤ 0 := by
    linarith
  have hcoef : (0 : ℝ) ≤ 8 / (3 * Real.pi ^ 4) := by positivity
  nlinarith [hneg, hcoef]

/-! ### The ceiling is attained -/

/-- Wall family attaining the trade-off: axis `0` purely usual, axis `1` purely dual, axis `2` on
the wall with free split `γ`. -/
noncomputable def ceilingWitness (γ : ℝ) : TorsionParams where
  alpha := fun a => if a.val = 0 then Real.pi / 2 else if a.val = 1 then 0 else γ
  beta := fun a =>
    if a.val = 0 then 0 else if a.val = 1 then Real.pi / 2 else Real.pi / 2 - γ

theorem J_ceilingWitness (γ : ℝ) :
    J (ceilingWitness γ) = (Real.pi / 2) * (γ - Real.pi / 4) := by
  rw [J_coef]
  simp only [ceilingWitness, Fin.sum_univ_three]
  norm_num
  ring

theorem mass_ceilingWitness (γ : ℝ) :
    mass (ceilingWitness γ) =
      5 * Real.pi ^ 2 / 16 + (γ - Real.pi / 4) ^ 2 := by
  rw [mass_coef]
  simp only [ceilingWitness, Fin.sum_univ_three]
  norm_num
  ring

theorem isAdmissibleContinuous_ceilingWitness {γ : ℝ}
    (h0 : 0 ≤ γ) (h1 : γ ≤ Real.pi / 2) :
    IsAdmissibleContinuous (ceilingWitness γ) := by
  have hπ : 0 < Real.pi := Real.pi_pos
  have hcase : ∀ b : Fin 3, b = 0 ∨ b = 1 ∨ b = 2 := by decide
  intro a
  rcases hcase a with rfl | rfl | rfl <;>
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [ceilingWitness] <;>
    norm_num <;>
    linarith [hπ]

theorem ceilingWitness_attains (γ : ℝ) :
    Real.pi ^ 2 * mass (ceilingWitness γ)
      = 5 * Real.pi ^ 4 / 16 + 4 * J (ceilingWitness γ) ^ 2 := by
  rw [mass_ceilingWitness, J_ceilingWitness]
  ring

/-- Heaviest admissible shield. -/
noncomputable def maximalShield : TorsionParams :=
  ceilingWitness (Real.pi / 4)

theorem J_maximalShield : J maximalShield = 0 := by
  rw [maximalShield, J_ceilingWitness, sub_self, mul_zero]

theorem mass_maximalShield : mass maximalShield = 5 * Real.pi ^ 2 / 16 := by
  rw [maximalShield, mass_ceilingWitness, sub_self]
  ring

theorem isAdmissibleContinuous_maximalShield :
    IsAdmissibleContinuous maximalShield := by
  have hπ : 0 < Real.pi := Real.pi_pos
  exact isAdmissibleContinuous_ceilingWitness (by linarith) (by linarith)

/-! ### Gravitational neutrality

Neutrality is neither the vacuum nor agreement of the two rotors.
-/

/-- Gravitational neutrality, equivalently shielding: the invariant torsional mismatch vanishes. -/
def IsGravNeutral (p : TorsionParams) : Prop := J p = 0

theorem isGravNeutral_iff_budgets_agree (p : TorsionParams) :
    IsGravNeutral p ↔
      ∑ a : Fin 3, p.alpha a ^ 2 = ∑ a : Fin 3, p.beta a ^ 2 :=
  J_eq_zero_iff p

theorem mass_eq_usual_budget_of_isGravNeutral {p : TorsionParams}
    (h : IsGravNeutral p) : mass p = ∑ a : Fin 3, p.alpha a ^ 2 :=
  mass_eq_sum_alpha_of_J_eq_zero h

/-- Neutrality is neither the vacuum nor coincidence of the two rotors. -/
theorem exists_isGravNeutral_massive_torsioned :
    ∃ p : TorsionParams, IsGravNeutral p ∧ 0 < mass p ∧
      RelativeRotor.relativeRotor p ≠ 1 :=
  RelativeRotor.J_zero_not_relativeRotor_one

/-! ### Consequences for shielding -/

theorem mass_le_shield_ceiling {p : TorsionParams}
    (h : IsAdmissibleContinuous p) (hJ : J p = 0) :
    mass p ≤ 5 * Real.pi ^ 2 / 4 := by
  have hraw := pi_sq_mass_le_shield_ceiling_add_J_sq_of_continuous p h
  rw [hJ] at hraw
  have hπ : 0 < Real.pi ^ 2 := by positivity
  nlinarith [hraw, hπ]

theorem mass_le_shield_ceiling_of_isGravNeutral {p : TorsionParams}
    (h : IsAdmissibleContinuous p) (hn : IsGravNeutral p) :
    mass p ≤ 5 * Real.pi ^ 2 / 4 :=
  mass_le_shield_ceiling h hn

theorem exists_admissible_shield_of_mass_eq_ceiling :
    ∃ p : TorsionParams, IsAdmissibleContinuous p ∧ J p = 0 ∧
      mass p = 5 * Real.pi ^ 2 / 16 :=
  ⟨maximalShield, isAdmissibleContinuous_maximalShield, J_maximalShield,
    mass_maximalShield⟩

/-- The ceiling is about neutrality, not about gravity: full repulsion carries no mass penalty. -/
theorem exists_admissible_max_mass_full_repulsion :
    ∃ p : TorsionParams, IsAdmissibleContinuous p ∧
      mass p = 3 * Real.pi ^ 2 / 8 ∧ J p = -(3 * Real.pi ^ 2 / 8) := by
  refine ⟨{ alpha := fun _ => 0, beta := fun _ => Real.pi / 2 },
    isAdmissibleContinuous_pureElliptic, ?_, ?_⟩
  · rw [mass_coef]
    simp only [Fin.sum_univ_three]
    ring
  · rw [J_coef]
    simp only [Fin.sum_univ_three]
    ring

private theorem mass_le_equalScale_ceiling_continuous_aux {p : TorsionParams}
    (h : IsAdmissibleContinuous p) (heq : p.beta = p.alpha) :
    mass p ≤ 3 * Real.pi ^ 2 / 4 := by
  have haxis : ∀ a : Fin 3, p.alpha a ^ 2 + p.beta a ^ 2 ≤ Real.pi ^ 2 / 2 := by
    intro a
    have hα := (h a).1
    have hsum := (h a).2.2.2
    have hβ : p.beta a = p.alpha a := congrFun heq a
    rw [hβ] at hsum ⊢
    nlinarith
  rw [mass_coef]
  simp only [Fin.sum_univ_three]
  linarith [haxis 0, haxis 1, haxis 2]

theorem mass_le_equalScale_ceiling_continuous {p : TorsionParams}
    (h : IsAdmissibleContinuous p) (heq : p.beta = p.alpha) :
    mass p ≤ 3 * Real.pi ^ 2 / 2 := by
  have hle : (3 : ℝ) * Real.pi ^ 2 / 4 ≤ 3 * Real.pi ^ 2 / 2 := by
    nlinarith [Real.pi_pos]
  exact le_trans (mass_le_equalScale_ceiling_continuous_aux h heq) hle

theorem mass_le_equalScale_ceiling {p : TorsionParams}
    (h : IsAdmissibleContinuousLegacy p) (heq : p.beta = p.alpha) :
    mass p ≤ 3 * Real.pi ^ 2 / 16 := by
  have hπ : 0 < Real.pi := Real.pi_pos
  have haxis : ∀ a : Fin 3, p.alpha a ^ 2 + p.beta a ^ 2 ≤ Real.pi ^ 2 / 8 := by
    intro a
    have hα := (h a).1
    have hsum := (h a).2.2
    have hβ : p.beta a = p.alpha a := congrFun heq a
    rw [hβ] at hsum ⊢
    nlinarith
  rw [mass_coef]
  simp only [Fin.sum_univ_three]
  linarith [haxis 0, haxis 1, haxis 2]

theorem pi_sq_div_eight_le_abs_J_of_mass_eq_max {p : TorsionParams}
    (h : IsAdmissibleContinuousLegacy p) (hM : mass p = 3 * Real.pi ^ 2 / 8) :
    Real.pi ^ 2 / 8 ≤ |J p| := by
  have hraw := pi_sq_mass_le_shield_ceiling_add_J_sq p h
  rw [hM] at hraw
  have hsq : (Real.pi ^ 2 / 8) ^ 2 ≤ J p ^ 2 := by nlinarith [hraw, Real.pi_pos]
  have habs : |Real.pi ^ 2 / 8| ≤ |J p| := by
    rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt hsq
  rwa [abs_of_nonneg (by positivity : (0 : ℝ) ≤ Real.pi ^ 2 / 8)] at habs

theorem not_isGravNeutral_of_mass_eq_max {p : TorsionParams}
    (h : IsAdmissibleContinuousLegacy p) (hM : mass p = 3 * Real.pi ^ 2 / 8) :
    ¬ IsGravNeutral p := by
  intro hn
  have hle := pi_sq_div_eight_le_abs_J_of_mass_eq_max h hM
  rw [IsGravNeutral] at hn
  rw [hn, abs_zero] at hle
  have : (0 : ℝ) < Real.pi ^ 2 / 8 := by positivity
  linarith

theorem axis_rigidity_of_mass_eq_max {p : TorsionParams}
    (h : IsAdmissibleContinuousLegacy p) (hM : mass p = 3 * Real.pi ^ 2 / 8)
    (a : Fin 3) :
    (p.alpha a = Real.pi / 2 ∧ p.beta a = 0) ∨
      (p.alpha a = 0 ∧ p.beta a = Real.pi / 2) := by
  have hπ : 0 < Real.pi := Real.pi_pos
  have haxle : ∀ b : Fin 3,
      p.alpha b ^ 2 + p.beta b ^ 2 ≤ Real.pi ^ 2 / 4 := fun b => by
    have hα := (h b).1
    have hβ := (h b).2.1
    have hsum := (h b).2.2
    nlinarith [sq_nonneg (p.alpha b - p.beta b), hsum, hα, hβ, Real.pi_pos]
  have hsum3 : p.alpha 0 ^ 2 + p.beta 0 ^ 2 + (p.alpha 1 ^ 2 + p.beta 1 ^ 2) +
      (p.alpha 2 ^ 2 + p.beta 2 ^ 2) = 3 * Real.pi ^ 2 / 4 := by
    have := hM
    rw [mass_coef] at this
    simp only [Fin.sum_univ_three] at this
    linarith
  have hcase : ∀ b : Fin 3, b = 0 ∨ b = 1 ∨ b = 2 := by decide
  have heq : p.alpha a ^ 2 + p.beta a ^ 2 = Real.pi ^ 2 / 4 := by
    rcases hcase a with rfl | rfl | rfl <;>
      nlinarith [haxle 0, haxle 1, haxle 2, hsum3,
        sq_nonneg (p.alpha 0 - p.beta 0), sq_nonneg (p.alpha 1 - p.beta 1),
        sq_nonneg (p.alpha 2 - p.beta 2)]
  have hα := (h a).1
  have hβ := (h a).2.1
  have hsum := (h a).2.2
  have hprod : p.alpha a * p.beta a = 0 := by nlinarith [hsum, Real.pi_pos]
  rcases mul_eq_zero.mp hprod with hz | hz
  · right
    refine ⟨hz, ?_⟩
    rw [hz] at heq
    nlinarith
  · left
    refine ⟨?_, hz⟩
    rw [hz] at heq
    nlinarith

/-! ### Link with dual-only control -/

theorem sum_alpha_sq_le_shield_ceiling_of_dual_only_shield
    {p q : TorsionParams} (hα : q.alpha = p.alpha)
    (hq : IsAdmissibleContinuous q) (hJ : J q = 0) :
    ∑ a : Fin 3, p.alpha a ^ 2 ≤ 5 * Real.pi ^ 2 / 4 := by
  rw [← mass_dual_only_of_J_eq_zero hα hJ]
  exact mass_le_shield_ceiling hq hJ

end Gravity

end DstDiophantine
