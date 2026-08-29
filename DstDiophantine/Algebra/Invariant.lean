import DstDiophantine.Algebra.Discrete
import DstDiophantine.Algebra.Motor
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Order.Group.Abs

/-!
# Torsional invariants `J`, `J⁽⁵⁾`, and unsigned mass `M`

The six-dimensional torsional scalar, its five-dimensional extension with the
Minkowski translation term, and the unsigned Euclidean mass that splits
label `T` into vacuum versus balanced massive.

## Boundedness note

The raw paper claim `|J| ≤ 1` under `IsPrincipalBranch` alone is false for
`J = (1/2) ∑ (α² - β²)`. On admissible configurations (`IsAdmissibleContinuous`:
non-negative rapidities with `α + β ≤ π/2`) we prove `|J| ≤ 3π²/8` and
`|JNormalized| ≤ 1` where `JNormalized = (8/(3π²)) J` matches the appendix extremals.

## Killing-form dictionary (main paper App. B)

Assume generator orthonormality `B(B⁺_a,B⁺_b)=8 δ_{ab}`, `B(B⁻_a,B⁻_b)=-8 δ_{ab}`
and expand `Ω = omegaTorsion p = ∑ (α_a/2) B⁺_a + (β_a/2) B⁻_a`. Then
`B(Ω,Ω) = 2 ∑(α²-β²)`, **not** the appendix claim `8 ∑(α²-β²)`.
The project's `J = ½∑(α²-β²)` is the discrete-companion conclusion formula;
it is **not** `(1/16) B(Ω,Ω)` under that expansion (which would be `⅛∑(α²-β²)`).
-/

namespace DstDiophantine

open Operations Motor Discrete Real

namespace Invariant

/-- Parameter-space pairing matching generator norms `B(B⁺,B⁺)=8`, `B(B⁻,B⁻)=-8`. -/
def killingForm (p q : TorsionParams) : ℝ :=
  8 * (∑ a : Fin 3, (p.alpha a * q.alpha a - p.beta a * q.beta a))

/--
Generator Killing form evaluated on the half-angle coefficients of `omegaTorsion`:
`∑_a 8 (α_a/2)² + (-8) (β_a/2)²`.
-/
noncomputable def omegaTorsionGeneratorKilling (p : TorsionParams) : ℝ :=
  ∑ a : Fin 3, (8 * (p.alpha a / 2) ^ 2 + (-8) * (p.beta a / 2) ^ 2)

theorem omegaTorsionGeneratorKilling_eq (p : TorsionParams) :
    omegaTorsionGeneratorKilling p =
      2 * ∑ a : Fin 3, (p.alpha a ^ 2 - p.beta a ^ 2) := by
  unfold omegaTorsionGeneratorKilling
  simp only [Fin.sum_univ_three]
  ring_nf

/-- Under generator orthonormality, `B(omegaTorsion p, omegaTorsion p)` equals
`omegaTorsionGeneratorKilling p = 2 ∑(α²-β²)`. -/
theorem omegaTorsion_killing_vs_param (p : TorsionParams) :
    omegaTorsionGeneratorKilling p = (1 / 4) * killingForm p p := by
  rw [omegaTorsionGeneratorKilling_eq]
  unfold killingForm
  simp only [Fin.sum_univ_three]
  ring_nf

/--
Appendix claim `B(Ω,Ω) = 8 ∑(α²-β²)` for `Ω = ∑(α/2)iΓ+(β/2)Γ` is false:
the generator expansion yields `2 ∑(α²-β²)` instead.
-/
theorem paper_appendix_killing_coeff_false :
    ∃ p : TorsionParams,
      omegaTorsionGeneratorKilling p ≠
        8 * ∑ a : Fin 3, (p.alpha a ^ 2 - p.beta a ^ 2) := by
  refine ⟨{ alpha := fun _ => 1, beta := fun _ => 0 }, ?_⟩
  rw [omegaTorsionGeneratorKilling_eq]
  simp only [Fin.sum_univ_three, one_pow, zero_pow (by norm_num : (2 : ℕ) ≠ 0), sub_zero]
  norm_num

/-- Discrete-companion / project conclusion formula for the torsional scalar. -/
noncomputable def J (p : TorsionParams) : ℝ :=
  (1 / 16) * killingForm p p

theorem J_coef (p : TorsionParams) :
    J p = (1 / 2) * ∑ a : Fin 3, (p.alpha a ^ 2 - p.beta a ^ 2) := by
  unfold J killingForm
  simp only [Fin.sum_univ_three]
  ring_nf

/-- `(1/16) B(Ω,Ω)` under the generator expansion is `⅛∑(α²-β²)`, not `J`. -/
theorem one_sixteenth_omegaKilling_eq (p : TorsionParams) :
    (1 / 16) * omegaTorsionGeneratorKilling p =
      (1 / 8) * ∑ a : Fin 3, (p.alpha a ^ 2 - p.beta a ^ 2) := by
  rw [omegaTorsionGeneratorKilling_eq]
  ring_nf

theorem J_eq_four_times_one_sixteenth_omegaKilling (p : TorsionParams) :
    J p = 4 * ((1 / 16) * omegaTorsionGeneratorKilling p) := by
  rw [J_coef, one_sixteenth_omegaKilling_eq]
  ring_nf

/-- Paper-normalized torsional scalar; equals `1` at appendix pure-boost extremals. -/
noncomputable def JNormalized (p : TorsionParams) : ℝ :=
  (8 / (3 * Real.pi ^ 2)) * J p

theorem JNormalized_coef (p : TorsionParams) :
    JNormalized p =
      (4 / (3 * Real.pi ^ 2)) * ∑ a : Fin 3, (p.alpha a ^ 2 - p.beta a ^ 2) := by
  unfold JNormalized
  rw [J_coef]
  ring_nf

/-- Euclidean pairing with the cyclic sign of `killingForm` flipped. -/
def euclideanForm (p q : TorsionParams) : ℝ :=
  8 * (∑ a : Fin 3, (p.alpha a * q.alpha a + p.beta a * q.beta a))

/--
Unsigned torsional mass `M = ½∑(α²+β²)`. Same normalisation coefficient as
`J`, so a pure-boost extremal has `massNormalized = 1 = JNormalized`.
This is a second observable, not a fifth D4L label.
-/
noncomputable def mass (p : TorsionParams) : ℝ :=
  (1 / 16) * euclideanForm p p

theorem mass_coef (p : TorsionParams) :
    mass p = (1 / 2) * ∑ a : Fin 3, (p.alpha a ^ 2 + p.beta a ^ 2) := by
  unfold mass euclideanForm
  simp only [Fin.sum_univ_three]
  ring_nf

theorem mass_nonneg (p : TorsionParams) : 0 ≤ mass p := by
  rw [mass_coef]
  exact mul_nonneg (by norm_num) <|
    Finset.sum_nonneg fun _ _ => add_nonneg (sq_nonneg _) (sq_nonneg _)

theorem mass_eq_zero_iff (p : TorsionParams) :
    mass p = 0 ↔ ∀ a : Fin 3, p.alpha a = 0 ∧ p.beta a = 0 := by
  have hnn : ∀ a ∈ (Finset.univ : Finset (Fin 3)),
      0 ≤ p.alpha a ^ 2 + p.beta a ^ 2 := fun _ _ =>
    add_nonneg (sq_nonneg _) (sq_nonneg _)
  constructor
  · intro hM
    have hsum : ∑ a : Fin 3, (p.alpha a ^ 2 + p.beta a ^ 2) = 0 := by
      have h2 := congrArg (fun t : ℝ => 2 * t) hM
      rw [mass_coef] at h2
      linarith
    intro a
    have ha : p.alpha a ^ 2 + p.beta a ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum a (Finset.mem_univ a)
    refine ⟨sq_eq_zero_iff.mp ?_, sq_eq_zero_iff.mp ?_⟩ <;>
      nlinarith [sq_nonneg (p.alpha a), sq_nonneg (p.beta a)]
  · intro h
    rw [mass_coef]
    have : ∑ a : Fin 3, (p.alpha a ^ 2 + p.beta a ^ 2) = 0 :=
      Finset.sum_eq_zero fun a _ => by simp [(h a).1, (h a).2]
    simp [this]

theorem J_eq_zero_of_mass_eq_zero {p : TorsionParams} (h : mass p = 0) :
    J p = 0 := by
  have hz := (mass_eq_zero_iff p).mp h
  rw [J_coef]
  simp [Fin.sum_univ_three, (hz 0).1, (hz 0).2, (hz 1).1, (hz 1).2, (hz 2).1, (hz 2).2]

/-- Usual–dual swap flips the sign of `J`. -/
theorem J_dagger (p : TorsionParams) : J (daggerParams p) = -J p := by
  rw [J_coef, J_coef]
  simp only [daggerParams, Fin.sum_univ_three]
  ring

/-- Usual–dual swap preserves unsigned mass. -/
theorem mass_dagger (p : TorsionParams) : mass (daggerParams p) = mass p := by
  rw [mass_coef, mass_coef]
  simp only [daggerParams, Fin.sum_univ_three]
  ring

theorem JNormalized_dagger (p : TorsionParams) :
    JNormalized (daggerParams p) = -JNormalized p := by
  unfold JNormalized
  rw [J_dagger]
  ring

/-- Paper-normalized mass; equals `1` at either appendix wall. -/
noncomputable def massNormalized (p : TorsionParams) : ℝ :=
  (8 / (3 * Real.pi ^ 2)) * mass p

theorem massNormalized_coef (p : TorsionParams) :
    massNormalized p =
      (4 / (3 * Real.pi ^ 2)) * ∑ a : Fin 3, (p.alpha a ^ 2 + p.beta a ^ 2) := by
  unfold massNormalized
  rw [mass_coef]
  ring_nf

theorem massNormalized_nonneg (p : TorsionParams) : 0 ≤ massNormalized p := by
  unfold massNormalized
  have := mass_nonneg p
  positivity

theorem massNormalized_eq_zero_iff (p : TorsionParams) :
    massNormalized p = 0 ↔ mass p = 0 := by
  have hcoef : (8 / (3 * Real.pi ^ 2) : ℝ) ≠ 0 := by positivity
  simp [massNormalized, mul_eq_zero, hcoef]

theorem JNormalized_eq_zero_of_massNormalized_eq_zero {p : TorsionParams}
    (h : massNormalized p = 0) : JNormalized p = 0 := by
  unfold JNormalized
  simp [J_eq_zero_of_mass_eq_zero ((massNormalized_eq_zero_iff p).mp h)]

/-- Axis-wise factorisation behind the Killing quadratic form. -/
theorem axis_sq_diff_eq (α β : ℝ) : α ^ 2 - β ^ 2 = (α - β) * (α + β) := by ring

/-- Pure hyperbolic dominance on every axis (appendix positive extremal). -/
def IsPureHyperbolic (p : TorsionParams) : Prop :=
  ∀ a : Fin 3, p.alpha a = Real.pi / 2 ∧ p.beta a = 0

/-- Pure elliptic dominance on every axis (appendix negative extremal). -/
def IsPureElliptic (p : TorsionParams) : Prop :=
  ∀ a : Fin 3, p.alpha a = 0 ∧ p.beta a = Real.pi / 2

/-- Axis-wise bound under non-negativity and anti-synchronisation. -/
theorem sq_diff_le_half_pi_sq {α β : ℝ}
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hsum : α + β ≤ Real.pi / 2) :
    |α ^ 2 - β ^ 2| ≤ (Real.pi / 2) ^ 2 := by
  have hαle : α ≤ Real.pi / 2 := by linarith [hβ]
  have hβle : β ≤ Real.pi / 2 := by linarith [hα]
  rcases le_total α β with hle | hle
  · have hnonpos : α ^ 2 - β ^ 2 ≤ 0 := by nlinarith
    rw [abs_of_nonpos hnonpos]
    nlinarith [sq_nonneg (β - α)]
  · have hnonneg : 0 ≤ α ^ 2 - β ^ 2 := by nlinarith
    rw [abs_of_nonneg hnonneg]
    nlinarith [sq_nonneg (α - β)]

/-- Unsigned axis mass is bounded by the same cone ceiling as the signed gap. -/
theorem sq_sum_le_half_pi_sq {α β : ℝ}
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hsum : α + β ≤ Real.pi / 2) :
    α ^ 2 + β ^ 2 ≤ (Real.pi / 2) ^ 2 := by
  nlinarith [sq_nonneg (α + β), mul_nonneg hα hβ]

/-- Equality in the unsigned axis bound is the same pair of extremes. -/
theorem sq_sum_eq_half_pi_sq_iff {α β : ℝ}
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hsum : α + β ≤ Real.pi / 2) :
    α ^ 2 + β ^ 2 = (Real.pi / 2) ^ 2 ↔
      (α = Real.pi / 2 ∧ β = 0) ∨ (α = 0 ∧ β = Real.pi / 2) := by
  constructor
  · intro heq
    have hπ : 0 < Real.pi / 2 := by positivity
    have hsum_sq_le : (α + β) ^ 2 ≤ (Real.pi / 2) ^ 2 := by nlinarith [hsum]
    have hsum_sq_ge : (Real.pi / 2) ^ 2 ≤ (α + β) ^ 2 := by
      nlinarith [mul_nonneg hα hβ]
    have hsum_sq_eq : (α + β) ^ 2 = (Real.pi / 2) ^ 2 :=
      le_antisymm hsum_sq_le hsum_sq_ge
    have hsum_eq : α + β = Real.pi / 2 :=
      (sq_eq_sq_iff_eq_or_eq_neg.mp hsum_sq_eq).resolve_right
        (by linarith [hα, hβ, hπ])
    have hαβ : α * β = 0 := by nlinarith [hsum_eq, heq]
    rcases mul_eq_zero.mp hαβ with hα0 | hβ0
    · exact Or.inr ⟨hα0, by linarith [hsum_eq]⟩
    · exact Or.inl ⟨by linarith [hsum_eq], hβ0⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> simp

/-- Equality in the axis-wise bound holds exactly at the two extremes. -/
theorem sq_diff_eq_half_pi_sq_iff {α β : ℝ}
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hsum : α + β ≤ Real.pi / 2) :
    |α ^ 2 - β ^ 2| = (Real.pi / 2) ^ 2 ↔
      (α = Real.pi / 2 ∧ β = 0) ∨ (α = 0 ∧ β = Real.pi / 2) := by
  constructor
  · intro heq
    have hαle : α ≤ Real.pi / 2 := by linarith [hβ]
    have hβle : β ≤ Real.pi / 2 := by linarith [hα]
    have hπ : 0 < Real.pi / 2 := by positivity
    rcases le_total α β with hle | hle
    · have hnonpos : α ^ 2 - β ^ 2 ≤ 0 := by nlinarith
      rw [abs_of_nonpos hnonpos] at heq
      -- β² - α² = (π/2)² and β - α ≤ β + α ≤ π/2, so both factors saturate
      have hfac : (β - α) * (α + β) = (Real.pi / 2) ^ 2 := by
        have : β ^ 2 - α ^ 2 = (β - α) * (α + β) := by ring
        linarith
      have hprod_le : (β - α) * (α + β) ≤ (α + β) * (α + β) := by
        nlinarith [sq_nonneg (β - α), hα]
      have hsum_sq : (α + β) ^ 2 ≤ (Real.pi / 2) ^ 2 := by nlinarith [hsum]
      have hsum_eq : α + β = Real.pi / 2 := by
        have : (α + β) ^ 2 = (Real.pi / 2) ^ 2 := by nlinarith [hfac, hprod_le, hsum_sq]
        exact (sq_eq_sq_iff_eq_or_eq_neg.mp this).resolve_right (by linarith [hα, hβ, hπ])
      have hdiff_eq : β - α = Real.pi / 2 := by
        have hsum_pos : 0 < α + β := by linarith [hπ, hsum_eq]
        have : (β - α) * (α + β) = (Real.pi / 2) * (α + β) := by
          rw [hfac, hsum_eq]; ring
        exact (mul_left_inj' hsum_pos.ne').mp this
      have hα0 : α = 0 := by linarith [hsum_eq, hdiff_eq]
      have hβπ : β = Real.pi / 2 := by linarith [hsum_eq, hα0]
      exact Or.inr ⟨hα0, hβπ⟩
    · have hnonneg : 0 ≤ α ^ 2 - β ^ 2 := by nlinarith
      rw [abs_of_nonneg hnonneg] at heq
      have hfac : (α - β) * (α + β) = (Real.pi / 2) ^ 2 := by
        have : α ^ 2 - β ^ 2 = (α - β) * (α + β) := by ring
        linarith
      have hprod_le : (α - β) * (α + β) ≤ (α + β) * (α + β) := by
        nlinarith [sq_nonneg (α - β), hβ]
      have hsum_sq : (α + β) ^ 2 ≤ (Real.pi / 2) ^ 2 := by nlinarith [hsum]
      have hsum_eq : α + β = Real.pi / 2 := by
        have : (α + β) ^ 2 = (Real.pi / 2) ^ 2 := by nlinarith [hfac, hprod_le, hsum_sq]
        exact (sq_eq_sq_iff_eq_or_eq_neg.mp this).resolve_right (by linarith [hα, hβ, hπ])
      have hdiff_eq : α - β = Real.pi / 2 := by
        have hsum_pos : 0 < α + β := by linarith [hπ, hsum_eq]
        have : (α - β) * (α + β) = (Real.pi / 2) * (α + β) := by
          rw [hfac, hsum_eq]; ring
        exact (mul_left_inj' hsum_pos.ne').mp this
      have hβ0 : β = 0 := by linarith [hsum_eq, hdiff_eq]
      have hαπ : α = Real.pi / 2 := by linarith [hsum_eq, hβ0]
      exact Or.inl ⟨hαπ, hβ0⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · simp only [zero_pow two_ne_zero, sub_zero, abs_of_nonneg (sq_nonneg (Real.pi / 2))]
    · simp only [zero_pow two_ne_zero, zero_sub, abs_neg,
        abs_of_nonneg (sq_nonneg (Real.pi / 2))]

theorem torsion_bound_raw_continuous (p : TorsionParams) (h : IsAdmissibleContinuous p) :
    |J p| ≤ 3 * (Real.pi / 2) ^ 2 / 2 := by
  rw [J_coef, abs_mul, abs_of_pos (show 0 < (1 / 2 : ℝ) by norm_num)]
  have hbound : ∀ a : Fin 3, |p.alpha a ^ 2 - p.beta a ^ 2| ≤ (Real.pi / 2) ^ 2 := fun a =>
    sq_diff_le_half_pi_sq (h a).1 (h a).2.1 (h a).2.2
  have hsum : ∑ a : Fin 3, |p.alpha a ^ 2 - p.beta a ^ 2| ≤ 3 * (Real.pi / 2) ^ 2 := by
    simp only [Fin.sum_univ_three]
    linarith [hbound 0, hbound 1, hbound 2]
  have habs : |∑ a : Fin 3, (p.alpha a ^ 2 - p.beta a ^ 2)| ≤
      ∑ a : Fin 3, |p.alpha a ^ 2 - p.beta a ^ 2| :=
    Finset.abs_sum_le_sum_abs (s := Finset.univ) (f := fun a => p.alpha a ^ 2 - p.beta a ^ 2)
  calc
    (1 / 2 : ℝ) * |∑ a : Fin 3, (p.alpha a ^ 2 - p.beta a ^ 2)|
        ≤ (1 / 2) * ∑ a : Fin 3, |p.alpha a ^ 2 - p.beta a ^ 2| :=
      mul_le_mul_of_nonneg_left habs (by norm_num)
    _ ≤ 3 * (Real.pi / 2) ^ 2 / 2 := by linarith [hsum]

/-- Explicit raw ceiling `|J| ≤ 3π²/8` on admissible continuous configurations. -/
theorem torsion_bound_raw_continuous_pi_sq (p : TorsionParams)
    (h : IsAdmissibleContinuous p) :
    |J p| ≤ 3 * Real.pi ^ 2 / 8 := by
  have hJ := torsion_bound_raw_continuous p h
  convert hJ using 1
  ring

/-- Raw bound `|J| ≤ 3π²/8` on admissible discrete configurations. -/
theorem torsion_bound_raw {N : ℕ} [NeZero N] (t : DiscreteTorsion N) (h : IsAdmissible t) :
    |J (toTorsionParams t)| ≤ 3 * (Real.pi / 2) ^ 2 / 2 :=
  torsion_bound_raw_continuous _ (admissible_continuous_of_discrete t h)

theorem torsion_bound_raw_pi_sq {N : ℕ} [NeZero N] (t : DiscreteTorsion N) (h : IsAdmissible t) :
    |J (toTorsionParams t)| ≤ 3 * Real.pi ^ 2 / 8 :=
  torsion_bound_raw_continuous_pi_sq _ (admissible_continuous_of_discrete t h)

/-- Normalized bound `|JNormalized| ≤ 1` on admissible continuous configurations. -/
theorem torsion_bound_continuous (p : TorsionParams) (h : IsAdmissibleContinuous p) :
    |JNormalized p| ≤ 1 := by
  unfold JNormalized
  have hJ := torsion_bound_raw_continuous p h
  have hcoef : 0 ≤ 8 / (3 * Real.pi ^ 2) := by positivity
  rw [abs_mul, abs_of_nonneg hcoef]
  calc
    (8 / (3 * Real.pi ^ 2)) * |J p|
        ≤ (8 / (3 * Real.pi ^ 2)) * (3 * (Real.pi / 2) ^ 2 / 2) := by gcongr
    _ = 1 := by field_simp; ring

/-- Normalized bound on admissible discrete configurations. -/
theorem torsion_bound {N : ℕ} [NeZero N] (t : DiscreteTorsion N) (h : IsAdmissible t) :
    |JNormalized (toTorsionParams t)| ≤ 1 :=
  torsion_bound_continuous _ (admissible_continuous_of_discrete t h)

/-- Raw mass ceiling `M ≤ 3π²/8` on the admissible cone. -/
theorem mass_bound_raw_continuous (p : TorsionParams) (h : IsAdmissibleContinuous p) :
    mass p ≤ 3 * Real.pi ^ 2 / 8 := by
  rw [mass_coef]
  have haxis : ∀ a : Fin 3, p.alpha a ^ 2 + p.beta a ^ 2 ≤ (Real.pi / 2) ^ 2 := fun a =>
    sq_sum_le_half_pi_sq (h a).1 (h a).2.1 (h a).2.2
  have hsum : ∑ a : Fin 3, (p.alpha a ^ 2 + p.beta a ^ 2) ≤ 3 * (Real.pi / 2) ^ 2 := by
    simp only [Fin.sum_univ_three]
    linarith [haxis 0, haxis 1, haxis 2]
  have : (1 / 2 : ℝ) * ∑ a : Fin 3, (p.alpha a ^ 2 + p.beta a ^ 2) ≤
      (1 / 2) * (3 * (Real.pi / 2) ^ 2) :=
    mul_le_mul_of_nonneg_left hsum (by norm_num)
  convert this using 1
  ring

/-- Normalized mass `0 ≤ M_norm ≤ 1` on the admissible cone. -/
theorem massNormalized_bound_continuous (p : TorsionParams)
    (h : IsAdmissibleContinuous p) :
    massNormalized p ≤ 1 := by
  unfold massNormalized
  have hM := mass_bound_raw_continuous p h
  have hcoef : 0 ≤ 8 / (3 * Real.pi ^ 2) := by positivity
  calc
    (8 / (3 * Real.pi ^ 2)) * mass p
        ≤ (8 / (3 * Real.pi ^ 2)) * (3 * Real.pi ^ 2 / 8) := by gcongr
    _ = 1 := by field_simp

/-- Appendix pure-boost extremal attains `JNormalized = 1`. -/
theorem JNormalized_extremal :
    JNormalized { alpha := fun _ => Real.pi / 2, beta := fun _ => 0 } = 1 := by
  unfold JNormalized J killingForm
  simp only [Fin.sum_univ_three, mul_zero, sub_zero]
  field_simp [Real.pi_ne_zero]
  ring_nf

/-- Appendix pure-elliptic extremal attains `JNormalized = -1`. -/
theorem JNormalized_extremal_neg :
    JNormalized { alpha := fun _ => 0, beta := fun _ => Real.pi / 2 } = -1 := by
  unfold JNormalized J killingForm
  simp only [Fin.sum_univ_three, zero_sub, mul_zero]
  field_simp [Real.pi_ne_zero]
  ring_nf

theorem isAdmissibleContinuous_pureHyperbolic :
    IsAdmissibleContinuous { alpha := fun _ => Real.pi / 2, beta := fun _ => 0 } := by
  intro a
  constructor
  · positivity
  constructor
  · exact le_refl 0
  · linarith [Real.pi_pos.le]

theorem isAdmissibleContinuous_pureElliptic :
    IsAdmissibleContinuous { alpha := fun _ => 0, beta := fun _ => Real.pi / 2 } := by
  intro a
  constructor
  · exact le_refl 0
  constructor
  · positivity
  · linarith [Real.pi_pos.le]

/-- Uniform scaling of all axes along the pure-boost ray. -/
noncomputable def pureHyperbolicRay (t : ℝ) : TorsionParams where
  alpha := fun _ => t * (Real.pi / 2)
  beta := fun _ => 0

/-- Uniform scaling of all axes along the pure-elliptic ray. -/
noncomputable def pureEllipticRay (t : ℝ) : TorsionParams where
  alpha := fun _ => 0
  beta := fun _ => t * (Real.pi / 2)

/--
Uniform equal usual–dual rapidity on every axis. Label `T` with positive
mass when `t ≠ 0`: the geometric seat of balanced Beal seeds.
-/
noncomputable def balancedRay (t : ℝ) : TorsionParams where
  alpha := fun _ => t * (Real.pi / 4)
  beta := fun _ => t * (Real.pi / 4)

theorem JNormalized_pureHyperbolicRay (t : ℝ) :
    JNormalized (pureHyperbolicRay t) = t ^ 2 := by
  rw [JNormalized_coef]
  simp only [pureHyperbolicRay, Fin.sum_univ_three]
  field_simp [Real.pi_ne_zero]
  ring

theorem JNormalized_pureEllipticRay (t : ℝ) :
    JNormalized (pureEllipticRay t) = -t ^ 2 := by
  rw [JNormalized_coef]
  simp only [pureEllipticRay, Fin.sum_univ_three]
  field_simp [Real.pi_ne_zero]
  ring

theorem isAdmissibleContinuous_pureHyperbolicRay {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    IsAdmissibleContinuous (pureHyperbolicRay t) := by
  intro a
  have hπ : 0 ≤ Real.pi / 2 := by positivity
  refine ⟨mul_nonneg ht0 hπ, le_rfl, ?_⟩
  change t * (Real.pi / 2) + 0 ≤ Real.pi / 2
  have : t * (Real.pi / 2) ≤ Real.pi / 2 := by
    calc t * (Real.pi / 2) ≤ 1 * (Real.pi / 2) := mul_le_mul_of_nonneg_right ht1 hπ
      _ = Real.pi / 2 := one_mul _
  linarith

theorem isAdmissibleContinuous_pureEllipticRay {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    IsAdmissibleContinuous (pureEllipticRay t) := by
  intro a
  have hπ : 0 ≤ Real.pi / 2 := by positivity
  refine ⟨le_rfl, mul_nonneg ht0 hπ, ?_⟩
  change 0 + t * (Real.pi / 2) ≤ Real.pi / 2
  have : t * (Real.pi / 2) ≤ Real.pi / 2 := by
    calc t * (Real.pi / 2) ≤ 1 * (Real.pi / 2) := mul_le_mul_of_nonneg_right ht1 hπ
      _ = Real.pi / 2 := one_mul _
  linarith

theorem JNormalized_balancedRay (t : ℝ) : JNormalized (balancedRay t) = 0 := by
  rw [JNormalized_coef]
  simp only [balancedRay, Fin.sum_univ_three]
  ring

theorem mass_balancedRay (t : ℝ) :
    mass (balancedRay t) = 3 * t ^ 2 * Real.pi ^ 2 / 16 := by
  rw [mass_coef]
  simp only [balancedRay, Fin.sum_univ_three]
  ring

theorem massNormalized_balancedRay (t : ℝ) :
    massNormalized (balancedRay t) = t ^ 2 / 2 := by
  unfold massNormalized
  rw [mass_balancedRay]
  field_simp [Real.pi_ne_zero]
  ring

theorem isAdmissibleContinuous_balancedRay {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    IsAdmissibleContinuous (balancedRay t) := by
  intro a
  have hπ4 : 0 ≤ Real.pi / 4 := by linarith [Real.pi_pos]
  have hα : 0 ≤ t * (Real.pi / 4) := mul_nonneg ht0 hπ4
  refine ⟨hα, hα, ?_⟩
  have hπ2 : 0 ≤ Real.pi / 2 := by positivity
  calc t * (Real.pi / 4) + t * (Real.pi / 4)
      = t * (Real.pi / 2) := by ring
    _ ≤ 1 * (Real.pi / 2) := mul_le_mul_of_nonneg_right ht1 hπ2
    _ = Real.pi / 2 := one_mul _

theorem mass_balancedRay_pos {t : ℝ} (ht : t ≠ 0) : 0 < mass (balancedRay t) := by
  rw [mass_balancedRay]
  have : 0 < t ^ 2 := sq_pos_of_ne_zero ht
  positivity

theorem not_admissible_balancedRay_of_one_lt {t : ℝ} (ht : 1 < t) :
    ¬ IsAdmissibleContinuous (balancedRay t) := by
  intro h
  have hsum := (h (0 : Fin 3)).2.2
  have hαβ :
      (balancedRay t).alpha 0 + (balancedRay t).beta 0 = t * (Real.pi / 2) := by
    simp [balancedRay]; ring
  have : t * (Real.pi / 2) ≤ Real.pi / 2 := by rwa [← hαβ]
  have hπ : 0 < Real.pi / 2 := by positivity
  nlinarith

/-- Paper Ch.6 step “`J = 0` ⇒ vacuum / trivial bases” is false. -/
theorem JNormalized_zero_not_implies_vacuum :
    ∃ p : TorsionParams,
      IsAdmissibleContinuous p ∧ JNormalized p = 0 ∧ 0 < mass p :=
  ⟨balancedRay 1, isAdmissibleContinuous_balancedRay (by norm_num) (by norm_num),
    JNormalized_balancedRay 1, mass_balancedRay_pos (by norm_num)⟩

/-- On the admissible cone, `JNormalized` attains every value in `[-1, 1]`. -/
theorem exists_admissible_JNormalized (y : ℝ) (hy : |y| ≤ 1) :
    ∃ p : TorsionParams, IsAdmissibleContinuous p ∧ JNormalized p = y := by
  rcases le_total 0 y with hy0 | hy0
  · refine ⟨pureHyperbolicRay (Real.sqrt y), ?_, ?_⟩
    · exact isAdmissibleContinuous_pureHyperbolicRay (Real.sqrt_nonneg _)
        ((Real.sqrt_le_one).2 (abs_le.mp hy).2)
    · rw [JNormalized_pureHyperbolicRay, Real.sq_sqrt hy0]
  · refine ⟨pureEllipticRay (Real.sqrt (-y)), ?_, ?_⟩
    · exact isAdmissibleContinuous_pureEllipticRay (Real.sqrt_nonneg _)
        ((Real.sqrt_le_one).2 (by linarith [(abs_le.mp hy).1]))
    · rw [JNormalized_pureEllipticRay, Real.sq_sqrt (neg_nonneg.mpr hy0), neg_neg]

private theorem axis_sq_diff_eq_half_pi_sq_of_abs
    {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (hsum : α + β ≤ Real.pi / 2)
    (heq : |α ^ 2 - β ^ 2| = (Real.pi / 2) ^ 2) :
    (α = Real.pi / 2 ∧ β = 0) ∨ (α = 0 ∧ β = Real.pi / 2) :=
  (sq_diff_eq_half_pi_sq_iff hα hβ hsum).mp heq

private theorem axis_diff_of_extreme {α β : ℝ}
    (h : (α = Real.pi / 2 ∧ β = 0) ∨ (α = 0 ∧ β = Real.pi / 2)) :
    α ^ 2 - β ^ 2 = (Real.pi / 2) ^ 2 ∨ α ^ 2 - β ^ 2 = -((Real.pi / 2) ^ 2) := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inl (by simp)
  · exact Or.inr (by simp)

private theorem signed_sum_of_extremes
    (d0 d1 d2 : ℝ) (c : ℝ)
    (h0 : d0 = c ∨ d0 = -c) (h1 : d1 = c ∨ d1 = -c) (h2 : d2 = c ∨ d2 = -c)
    (hc : 0 < c)
    (hsum : |d0 + d1 + d2| = 3 * c) :
    (d0 = c ∧ d1 = c ∧ d2 = c) ∨ (d0 = -c ∧ d1 = -c ∧ d2 = -c) := by
  have habs_neg : |-c| = c := by rw [abs_neg, abs_of_nonneg hc.le]
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact Or.inl ⟨h0, h1, h2⟩
  · rw [h0, h1, h2] at hsum
    have : |c + c + (-c)| = c := by ring_nf; exact abs_of_nonneg hc.le
    linarith [this]
  · rw [h0, h1, h2] at hsum
    have : |c + (-c) + c| = c := by ring_nf; exact abs_of_nonneg hc.le
    linarith [this]
  · rw [h0, h1, h2] at hsum
    have : |c + (-c) + (-c)| = c := by ring_nf; exact habs_neg
    linarith [this]
  · rw [h0, h1, h2] at hsum
    have : |(-c) + c + c| = c := by ring_nf; exact abs_of_nonneg hc.le
    linarith [this]
  · rw [h0, h1, h2] at hsum
    have : |(-c) + c + (-c)| = c := by ring_nf; exact habs_neg
    linarith [this]
  · rw [h0, h1, h2] at hsum
    have : |(-c) + (-c) + c| = c := by ring_nf; exact habs_neg
    linarith [this]
  · exact Or.inr ⟨h0, h1, h2⟩

private theorem abs_eq_of_sum_eq_three {x y z c : ℝ}
    (hx : |x| ≤ c) (hy : |y| ≤ c) (hz : |z| ≤ c)
    (hs : |x| + |y| + |z| = 3 * c) :
    |x| = c ∧ |y| = c ∧ |z| = c := by
  refine ⟨le_antisymm hx (by linarith), le_antisymm hy (by linarith),
    le_antisymm hz (by linarith)⟩

theorem JNormalized_of_pureHyperbolic (p : TorsionParams) (h : IsPureHyperbolic p) :
    JNormalized p = 1 := by
  rw [JNormalized_coef]
  simp only [Fin.sum_univ_three]
  have h0 := h 0; have h1 := h 1; have h2 := h 2
  simp [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2]
  field_simp [Real.pi_ne_zero]
  ring

theorem JNormalized_of_pureElliptic (p : TorsionParams) (h : IsPureElliptic p) :
    JNormalized p = -1 := by
  rw [JNormalized_coef]
  simp only [Fin.sum_univ_three]
  have h0 := h 0; have h1 := h 1; have h2 := h 2
  simp [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2]
  field_simp [Real.pi_ne_zero]
  ring

/-- `|JNormalized| = 1` on an admissible configuration iff pure hyperbolic or pure elliptic. -/
theorem abs_JNormalized_eq_one_iff (p : TorsionParams) (h : IsAdmissibleContinuous p) :
    |JNormalized p| = 1 ↔ IsPureHyperbolic p ∨ IsPureElliptic p := by
  constructor
  · intro heq
    have hJabs : |J p| = 3 * (Real.pi / 2) ^ 2 / 2 := by
      unfold JNormalized at heq
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 8 / (3 * Real.pi ^ 2))] at heq
      have hcoef_ne : (8 / (3 * Real.pi ^ 2) : ℝ) ≠ 0 := by positivity
      have hinv : |J p| = 3 * Real.pi ^ 2 / 8 := by
        apply mul_left_cancel₀ hcoef_ne
        rw [heq]
        field_simp
      rw [hinv]
      ring
    have haxis : ∀ a, |p.alpha a ^ 2 - p.beta a ^ 2| ≤ (Real.pi / 2) ^ 2 := fun a =>
      sq_diff_le_half_pi_sq (h a).1 (h a).2.1 (h a).2.2
    have habs_sum : |∑ a : Fin 3, (p.alpha a ^ 2 - p.beta a ^ 2)| ≤
        ∑ a : Fin 3, |p.alpha a ^ 2 - p.beta a ^ 2| :=
      Finset.abs_sum_le_sum_abs _ _
    have hJcoef : |J p| = (1 / 2) * |∑ a : Fin 3, (p.alpha a ^ 2 - p.beta a ^ 2)| := by
      rw [J_coef, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    have hsum_eq : |∑ a : Fin 3, (p.alpha a ^ 2 - p.beta a ^ 2)| = 3 * (Real.pi / 2) ^ 2 := by
      linarith [hJcoef, hJabs]
    have hsum_abs_le : ∑ a : Fin 3, |p.alpha a ^ 2 - p.beta a ^ 2| ≤ 3 * (Real.pi / 2) ^ 2 := by
      simp only [Fin.sum_univ_three]
      linarith [haxis 0, haxis 1, haxis 2]
    have hsum_sat : ∑ a : Fin 3, |p.alpha a ^ 2 - p.beta a ^ 2| = 3 * (Real.pi / 2) ^ 2 := by
      linarith [habs_sum, hsum_eq, hsum_abs_le]
    have hax_eq : ∀ a, |p.alpha a ^ 2 - p.beta a ^ 2| = (Real.pi / 2) ^ 2 := by
      have hs : |p.alpha 0 ^ 2 - p.beta 0 ^ 2| + |p.alpha 1 ^ 2 - p.beta 1 ^ 2| +
          |p.alpha 2 ^ 2 - p.beta 2 ^ 2| = 3 * (Real.pi / 2) ^ 2 := by
        simpa only [Fin.sum_univ_three] using hsum_sat
      have ⟨e0, e1, e2⟩ :=
        abs_eq_of_sum_eq_three (haxis 0) (haxis 1) (haxis 2) hs
      intro a; fin_cases a <;> assumption
    have hext : ∀ a, (p.alpha a = Real.pi / 2 ∧ p.beta a = 0) ∨
        (p.alpha a = 0 ∧ p.beta a = Real.pi / 2) := fun a =>
      axis_sq_diff_eq_half_pi_sq_of_abs (h a).1 (h a).2.1 (h a).2.2 (hax_eq a)
    set c := (Real.pi / 2) ^ 2 with hcdef
    have hc : 0 < c := by positivity
    have hd : ∀ a, p.alpha a ^ 2 - p.beta a ^ 2 = c ∨
        p.alpha a ^ 2 - p.beta a ^ 2 = -c := fun a =>
      axis_diff_of_extreme (hext a)
    have hsum3 : |(p.alpha 0 ^ 2 - p.beta 0 ^ 2) + (p.alpha 1 ^ 2 - p.beta 1 ^ 2) +
        (p.alpha 2 ^ 2 - p.beta 2 ^ 2)| = 3 * c := by
      simpa only [Fin.sum_univ_three, hcdef] using hsum_eq
    have hall := signed_sum_of_extremes _ _ _ c (hd 0) (hd 1) (hd 2) hc hsum3
    rcases hall with ⟨hd0, hd1, hd2⟩ | ⟨hd0, hd1, hd2⟩
    · refine Or.inl fun a => ?_
      have ha : p.alpha a ^ 2 - p.beta a ^ 2 = c := by
        fin_cases a <;> assumption
      rcases hext a with hex | hex
      · exact hex
      · have : p.alpha a ^ 2 - p.beta a ^ 2 = -c := by simp [hex.1, hex.2, c]
        linarith [ha, this, hc]
    · refine Or.inr fun a => ?_
      have ha : p.alpha a ^ 2 - p.beta a ^ 2 = -c := by
        fin_cases a <;> assumption
      rcases hext a with hex | hex
      · have : p.alpha a ^ 2 - p.beta a ^ 2 = c := by simp [hex.1, hex.2, c]
        linarith [ha, this, hc]
      · exact hex
  · rintro (hH | hE)
    · rw [JNormalized_of_pureHyperbolic p hH, abs_one]
    · rw [JNormalized_of_pureElliptic p hE, abs_neg, abs_one]

/-- Extended invariant with translation sector. -/
noncomputable def J5 (p : OmegaParams) : ℝ :=
  J p.torsion + (1 / 2) * minkowskiDot p.trans.lambda

theorem J5_eq (p : OmegaParams) :
    J5 p = J p.torsion + (1 / 2) * minkowskiDot p.trans.lambda := rfl

/-- Spatial translation: vanishing time component. -/
def IsSpatialTrans (p : TransParams) : Prop :=
  p.lambda 0 = 0

/-- Bounded spatial translation parameters. -/
def IsBoundedTrans (R : ℝ) (p : TransParams) : Prop :=
  IsSpatialTrans p ∧ ∑ μ : Fin 4, p.lambda μ ^ 2 ≤ R ^ 2

/-- Without translation constraints, `J⁽⁵⁾` is unbounded. -/
theorem J5_unbounded (M : ℝ) :
    ∃ p : OmegaParams, M < |J5 p| := by
  set L := Real.sqrt (2 * max (M + 1) 1)
  refine ⟨{
    torsion := { alpha := fun _ => 0, beta := fun _ => 0 }
    trans := { lambda := fun μ => if μ = (1 : Fin 4) then L else 0 }
  }, ?_⟩
  have hJ : J { alpha := fun _ => 0, beta := fun _ => 0 } = 0 := by
    rw [J_coef]
    simp
  have hdot : minkowskiDot (fun μ => if μ = (1 : Fin 4) then L else 0) = L ^ 2 := by
    simp only [minkowskiDot, pow_two]
    simp
  have hsq : L ^ 2 = 2 * max (M + 1) 1 := Real.sq_sqrt (by positivity)
  simp only [J5, hJ, zero_add]
  have hmain : M < (1 / 2 : ℝ) * (2 * max (M + 1) 1) := by
    rw [max_def]
    split_ifs with h
    · nlinarith
    · nlinarith
  have hnonneg : 0 ≤ (1 / 2 : ℝ) * (2 * max (M + 1) 1) := by positivity
  rw [hdot, hsq, abs_of_nonneg hnonneg]
  exact hmain

theorem minkowskiDot_le_sq (lam : Fin 4 → ℝ) (h0 : lam 0 = 0) :
    |minkowskiDot lam| ≤ ∑ μ : Fin 4, lam μ ^ 2 := by
  have hEq : minkowskiDot lam = lam 1 * lam 1 + lam 2 * lam 2 + lam 3 * lam 3 := by
    simp [minkowskiDot, h0]
  have hnn : 0 ≤ lam 1 * lam 1 + lam 2 * lam 2 + lam 3 * lam 3 :=
    add_nonneg (add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)) (mul_self_nonneg _)
  rw [hEq, abs_of_nonneg hnn]
  simp only [Fin.sum_univ_four, h0, pow_two]
  apply le_of_eq
  ring

/-- Counterexample showing `IsPrincipalBranch` alone does not bound `J`. -/
noncomputable def counterExampleParams : TorsionParams where
  alpha := fun a => match a with | 0 => 10 | 1 => 0 | 2 => 0
  beta := fun a => match a with | 0 => -10 + Real.pi / 4 | 1 => 0 | 2 => 0

/-- `IsPrincipalBranch` alone does not bound `J`; the paper's naive claim is false. -/
theorem torsion_bound_naive_false :
    ∃ p : TorsionParams, IsPrincipalBranch p ∧ 1 < |J p| := by
  refine ⟨counterExampleParams, ?_, ?_⟩
  · intro a
    fin_cases a
    · simp only [counterExampleParams]
      rw [show (10 : ℝ) + (-10 + Real.pi / 4) = Real.pi / 4 from by ring,
        abs_of_pos (by linarith [Real.pi_pos] : 0 < Real.pi / 4)]
      linarith [Real.pi_pos]
    · simp [counterExampleParams, abs_zero]
      linarith [Real.pi_pos.le]
    · simp [counterExampleParams, abs_zero]
      linarith [Real.pi_pos.le]
  · have hJ : J counterExampleParams = (1 / 2) * (5 * Real.pi - Real.pi ^ 2 / 16) := by
      rw [J_coef]
      simp [counterExampleParams, Fin.sum_univ_three]
      ring_nf
    rw [hJ]
    have hpos : 0 < (1 / 2) * (5 * Real.pi - Real.pi ^ 2 / 16) := by
      nlinarith [Real.pi_gt_three, Real.pi_pos, Real.pi_le_four]
    rw [abs_of_pos hpos]
    nlinarith [Real.pi_gt_three, Real.pi_pos, Real.pi_le_four]

/-- `J⁽⁵⁾` is bounded under admissible torsion and bounded spatial translation. -/
theorem J5_bound_spatial (R : ℝ) (p : OmegaParams)
    (ht : IsAdmissibleContinuous p.torsion) (hb : IsBoundedTrans R p.trans) :
    |J5 p| ≤ 3 * (Real.pi / 2) ^ 2 / 2 + R ^ 2 / 2 := by
  rw [J5_eq]
  have htors := torsion_bound_raw_continuous p.torsion ht
  have htrans : |minkowskiDot p.trans.lambda| ≤ R ^ 2 := by
    have h0 : p.trans.lambda 0 = 0 := hb.1
    calc |minkowskiDot p.trans.lambda|
        ≤ ∑ μ : Fin 4, p.trans.lambda μ ^ 2 := minkowskiDot_le_sq _ h0
      _ ≤ R ^ 2 := hb.2
  calc |J p.torsion + (1 / 2) * minkowskiDot p.trans.lambda|
      ≤ |J p.torsion| + |(1 / 2) * minkowskiDot p.trans.lambda| := abs_add_le _ _
    _ ≤ 3 * (Real.pi / 2) ^ 2 / 2 + |(1 / 2) * minkowskiDot p.trans.lambda| := by gcongr
    _ ≤ 3 * (Real.pi / 2) ^ 2 / 2 + (1 / 2) * R ^ 2 := by
      gcongr
      rw [abs_mul, abs_of_pos (show 0 < (1 / 2 : ℝ) by norm_num)]
      exact mul_le_mul_of_nonneg_left htrans (by norm_num)
    _ = 3 * (Real.pi / 2) ^ 2 / 2 + R ^ 2 / 2 := by ring

end Invariant

end DstDiophantine
