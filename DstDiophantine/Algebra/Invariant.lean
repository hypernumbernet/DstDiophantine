import DstDiophantine.Algebra.Discrete
import DstDiophantine.Algebra.Motor
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Order.Group.Abs

/-!
# Torsional invariants `J` and `J⁽⁵⁾

The six-dimensional torsional scalar and its five-dimensional extension with the
Minkowski translation term.

## Boundedness note

The raw paper claim `|J| ≤ 1` under `IsPrincipalBranch` alone is false for
`J = (1/2) ∑ (α² - β²)`. On admissible configurations (`IsAdmissibleContinuous`:
non-negative rapidities with `α + β ≤ π/2`) we prove `|J| ≤ 3π²/8` and
`|JNormalized| ≤ 1` where `JNormalized = (8/(3π²)) J` matches the appendix extremals.
-/

namespace DstDiophantine

open Operations Motor Discrete Real

namespace Invariant

/-- Normalised Killing form on the six-dimensional torsion sector. -/
def killingForm (p q : TorsionParams) : ℝ :=
  8 * (∑ a : Fin 3, (p.alpha a * q.alpha a - p.beta a * q.beta a))

/-- Original torsional scalar `J = (1/16) B_Killing(Ω, Ω)`. -/
noncomputable def J (p : TorsionParams) : ℝ :=
  (1 / 16) * killingForm p p

theorem J_coef (p : TorsionParams) :
    J p = (1 / 2) * ∑ a : Fin 3, (p.alpha a ^ 2 - p.beta a ^ 2) := by
  unfold J killingForm
  simp only [Fin.sum_univ_three]
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

/-- Axis-wise factorisation behind the Killing quadratic form. -/
theorem axis_sq_diff_eq (α β : ℝ) : α ^ 2 - β ^ 2 = (α - β) * (α + β) := by ring

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
    simp only [minkowskiDot, Fin.sum_univ_four, pow_two]
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
    simp [minkowskiDot, h0, Fin.sum_univ_four]
  have hnn : 0 ≤ lam 1 * lam 1 + lam 2 * lam 2 + lam 3 * lam 3 :=
    add_nonneg (add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)) (mul_self_nonneg _)
  rw [hEq, abs_of_nonneg hnn]
  simp only [Fin.sum_univ_four, h0, pow_two, sq]
  apply le_of_eq
  ring

private theorem sq_diff_le_half_pi_sq {α β : ℝ}
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

private theorem torsion_bound_raw_continuous (p : TorsionParams) (h : IsAdmissibleContinuous p) :
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

/-- Raw bound `|J| ≤ 3π²/8` on admissible discrete configurations. -/
theorem torsion_bound_raw {N : ℕ} [NeZero N] (t : DiscreteTorsion N) (h : IsAdmissible t) :
    |J (toTorsionParams t)| ≤ 3 * (Real.pi / 2) ^ 2 / 2 :=
  torsion_bound_raw_continuous _ (admissible_continuous_of_discrete t h)

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

/-- Appendix pure-boost extremal attains `JNormalized = 1`. -/
theorem JNormalized_extremal :
    JNormalized { alpha := fun _ => Real.pi / 2, beta := fun _ => 0 } = 1 := by
  unfold JNormalized J killingForm
  simp only [Fin.sum_univ_three, mul_zero, sub_zero]
  field_simp [Real.pi_ne_zero]
  ring_nf

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
