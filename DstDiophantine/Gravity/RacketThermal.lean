import DstDiophantine.Gravity.ChartRotation
import DstDiophantine.Gravity.RacketFlip
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Pi
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Order.Compact

/-!
# Mirror average and the canonical weight of the reversal

A partner and its mirror cancel. Over the `2ⁿ` assignments of a sign to each
of `n` moments, the uniform average of the signed sum is zero, and the
uniform average of its square is the sum of the squares of the moments. One
positive equal-distance moment therefore leaves a positive mean square.

On the torque-free rotor the gap `L² - 2 E I₂` drops the intermediate
component. The canonical weight is the product of three centered Gaussians of
variances `1/(β Iᵢ)`, which is the normalized factor `exp(-β E)`. Each
principal term has mean `1/(2β)`, and the mean gap is `(I₁ + I₃ - 2 I₂)/β`.
It vanishes if and only if `I₂` is the arithmetic mean of the other two. For
the six intercepts that condition is `2b² = a² + c²`, and both signs occur
among `0 < a < b < c`.

Every nonempty open set in the angular velocity has positive weight. In
particular both signs of the gap do, and so does the set of transverse
residuals about an intermediate spin that lie in `(0, 1/6)`. Every such
residual waits longer than the reversal takes to cross.

## Not claimed

* A frequency of reversals, or any count drawn from the weight.
* A floating-point many-body trajectory.
* A value of `a₀`, or an identification of a galaxy with this aggregate.
-/

namespace DstDiophantine.Gravity.RacketThermal

open ChartRotation MeasureTheory Metric ProbabilityTheory Real Set
open scoped NNReal ENNReal

/-! ### Mirror assignments -/

def signOf (b : Bool) : ℝ :=
  if b then 1 else -1

theorem sign_sq (b : Bool) : signOf b * signOf b = 1 := by
  cases b <;> simp [signOf]

def flipCoord {n : ℕ} (i : Fin n) (σ : Fin n → Bool) : Fin n → Bool :=
  Function.update σ i (!σ i)

theorem flipCoord_involutive {n : ℕ} (i : Fin n) : Function.Involutive (flipCoord i) := by
  intro σ
  funext j
  by_cases h : j = i
  · subst h
    simp [flipCoord, Function.update_self, Bool.not_not]
  · simp [flipCoord, Function.update_of_ne h]

def flipCoordEquiv {n : ℕ} (i : Fin n) : (Fin n → Bool) ≃ (Fin n → Bool) where
  toFun := flipCoord i
  invFun := flipCoord i
  left_inv := flipCoord_involutive i
  right_inv := flipCoord_involutive i

theorem flipCoord_sign {n : ℕ} (i : Fin n) (σ : Fin n → Bool) :
    signOf (flipCoord i σ i) = -signOf (σ i) := by
  cases h : σ i <;> simp [flipCoord, signOf, h, Function.update_self]

theorem flipCoord_ne {n : ℕ} {i j : Fin n} (hij : j ≠ i) (σ : Fin n → Bool) :
    flipCoord i σ j = σ j := by
  simp [flipCoord, Function.update_of_ne hij]

theorem card_mirror (n : ℕ) : Fintype.card (Fin n → Bool) = 2 ^ n := by
  rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]

theorem sum_sign_zero {n : ℕ} (i : Fin n) :
    ∑ σ : Fin n → Bool, signOf (σ i) = 0 := by
  let e : (Fin n → Bool) ≃ (Fin n → Bool) := flipCoordEquiv i
  have hcomp : ∑ σ : Fin n → Bool, signOf (e σ i) = ∑ σ : Fin n → Bool, signOf (σ i) :=
    Equiv.sum_comp e (fun σ => signOf (σ i))
  have hneg : ∑ σ : Fin n → Bool, signOf (e σ i) = ∑ σ : Fin n → Bool, -signOf (σ i) := by
    refine Finset.sum_congr rfl ?_
    intro σ _
    dsimp [e, flipCoordEquiv]
    exact flipCoord_sign i σ
  have hnegsum : ∑ σ : Fin n → Bool, -signOf (σ i) = -∑ σ : Fin n → Bool, signOf (σ i) := by
    simp
  linarith

theorem sum_sign_prod_zero {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    ∑ σ : Fin n → Bool, signOf (σ i) * signOf (σ j) = 0 := by
  have hcomp :=
    (flipCoord_involutive i).bijective.sum_comp (fun σ => signOf (σ i) * signOf (σ j))
  have hneg : ∑ σ : Fin n → Bool, signOf (flipCoord i σ i) * signOf (flipCoord i σ j) =
      ∑ σ : Fin n → Bool, -(signOf (σ i) * signOf (σ j)) := by
    refine Finset.sum_congr rfl ?_
    intro σ _
    rw [flipCoord_sign i σ, flipCoord_ne hij.symm]
    ring
  have hnegsum : ∑ σ : Fin n → Bool, -(signOf (σ i) * signOf (σ j)) =
      -∑ σ : Fin n → Bool, signOf (σ i) * signOf (σ j) := by
    simp
  linarith

def mirrorTorque {n : ℕ} (m : Fin n → ℝ) (σ : Fin n → Bool) : ℝ :=
  ∑ i, signOf (σ i) * m i

noncomputable def mirrorAverage {n : ℕ} (f : (Fin n → Bool) → ℝ) : ℝ :=
  (∑ σ, f σ) / (2 ^ n : ℝ)

theorem mirrorSum_sq {n : ℕ} (m : Fin n → ℝ) :
    ∑ σ : Fin n → Bool, mirrorTorque m σ ^ 2 = (2 : ℝ) ^ n * ∑ i, m i ^ 2 := by
  classical
  unfold mirrorTorque
  have hpow : ∀ σ : Fin n → Bool,
      (∑ i, signOf (σ i) * m i) ^ 2 =
        ∑ i, ∑ j, (signOf (σ i) * m i) * (signOf (σ j) * m j) := by
    intro σ
    rw [pow_two, Fintype.sum_mul_sum]
  simp_rw [hpow]
  have hswap :
      ∑ σ : Fin n → Bool, ∑ i, ∑ j, (signOf (σ i) * m i) * (signOf (σ j) * m j) =
        ∑ i, ∑ j, ∑ σ : Fin n → Bool, (signOf (σ i) * m i) * (signOf (σ j) * m j) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [Finset.sum_comm]
  rw [hswap]
  have hpull : ∀ i j,
      ∑ σ : Fin n → Bool, (signOf (σ i) * m i) * (signOf (σ j) * m j) =
        (∑ σ : Fin n → Bool, signOf (σ i) * signOf (σ j)) * (m i * m j) := by
    intro i j
    have :
        ∀ σ : Fin n → Bool, (signOf (σ i) * m i) * (signOf (σ j) * m j) =
          signOf (σ i) * signOf (σ j) * (m i * m j) := by
      intro σ
      ring
    simp_rw [this, Finset.sum_mul]
  simp_rw [hpull]
  have hsign : ∀ i j,
      ∑ σ : Fin n → Bool, signOf (σ i) * signOf (σ j) =
        if i = j then (2 : ℝ) ^ n else 0 := by
    intro i j
    by_cases hij : i = j
    · subst hij
      rw [ite_eq_left rfl]
      have hone : ∀ σ : Fin n → Bool, signOf (σ i) * signOf (σ i) = 1 :=
        fun σ => sign_sq (σ i)
      simp_rw [hone, Finset.sum_const, Finset.card_univ, card_mirror]
      simp
    · simp [hij, sum_sign_prod_zero hij]
  simp_rw [hsign]
  have hrow : ∀ i,
      ∑ j, (if i = j then (2 : ℝ) ^ n else 0) * (m i * m j) =
        (2 : ℝ) ^ n * m i ^ 2 := by
    intro i
    rw [Finset.sum_eq_single i]
    · simp [pow_two]
    · intro j _ hj
      rw [ite_eq_right (Ne.symm hj)]
      simp
    · intro hi
      exact (hi (Finset.mem_univ i)).elim
  simp_rw [hrow, ← Finset.mul_sum]

theorem mirrorAverage_zero {n : ℕ} (m : Fin n → ℝ) :
    mirrorAverage (fun σ => mirrorTorque m σ) = 0 := by
  unfold mirrorAverage mirrorTorque
  have hsum : ∑ σ : Fin n → Bool, ∑ i, signOf (σ i) * m i = 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero ?_
    intro i _
    rw [← Finset.sum_mul]
    simp [sum_sign_zero i]
  simp [hsum]

theorem mirrorAverage_sq {n : ℕ} (m : Fin n → ℝ) :
    mirrorAverage (fun σ => mirrorTorque m σ ^ 2) = ∑ i, m i ^ 2 := by
  unfold mirrorAverage
  rw [mirrorSum_sq]
  field_simp

theorem mirrorAverage_sq_pos {n : ℕ} {m : Fin n → ℝ} {i : Fin n} (hm : m i ≠ 0) :
    0 < mirrorAverage (fun σ => mirrorTorque m σ ^ 2) := by
  rw [mirrorAverage_sq]
  have hpos : 0 < m i ^ 2 := sq_pos_of_ne_zero hm
  have hrest : 0 ≤ ∑ j ∈ Finset.univ.erase i, m j ^ 2 :=
    Finset.sum_nonneg fun j _ => sq_nonneg (m j)
  calc
    0 < m i ^ 2 := hpos
    _ = m i ^ 2 + ∑ j ∈ Finset.univ.erase i, m j ^ 2 -
        ∑ j ∈ Finset.univ.erase i, m j ^ 2 := by ring
    _ ≤ m i ^ 2 + ∑ j ∈ Finset.univ.erase i, m j ^ 2 := by linarith
    _ = ∑ j, m j ^ 2 := by
      rw [← Finset.add_sum_erase Finset.univ (fun j => m j ^ 2) (Finset.mem_univ i)]

/-- One off-axis partner, copied across the assignments, leaves a positive mean square. -/
theorem mirror_defect_sq_pos {n : ℕ} (i : Fin n) {χ α : ℝ}
    (hχ : 0 < χ) (hχu : χ < Real.pi) (hα : 0 < α) (hαu : α < Real.pi) :
    0 < mirrorAverage (fun σ =>
      mirrorTorque (fun _ : Fin n => defectTorque χ α) σ ^ 2) := by
  refine mirrorAverage_sq_pos (i := i) ?_
  exact (defectTorque_pos hχ hχu hα hαu).ne'

/-! ### The gap `L² - 2 E I₂` -/

noncomputable def rotorEnergy (I1 I2 I3 ω1 ω2 ω3 : ℝ) : ℝ :=
  (1 / 2) * (I1 * ω1 ^ 2 + I2 * ω2 ^ 2 + I3 * ω3 ^ 2)

noncomputable def rotorLsq (I1 I2 I3 ω1 ω2 ω3 : ℝ) : ℝ :=
  I1 ^ 2 * ω1 ^ 2 + I2 ^ 2 * ω2 ^ 2 + I3 ^ 2 * ω3 ^ 2

noncomputable def separatrixGap (I1 I2 I3 ω1 ω2 ω3 : ℝ) : ℝ :=
  rotorLsq I1 I2 I3 ω1 ω2 ω3 - 2 * rotorEnergy I1 I2 I3 ω1 ω2 ω3 * I2

theorem separatrixGap_eq (I1 I2 I3 ω1 ω2 ω3 : ℝ) :
    separatrixGap I1 I2 I3 ω1 ω2 ω3 =
      I1 * (I1 - I2) * ω1 ^ 2 + I3 * (I3 - I2) * ω3 ^ 2 := by
  unfold separatrixGap rotorLsq rotorEnergy
  ring

theorem separatrixGap_intermediate (I1 I2 I3 ω2 : ℝ) :
    separatrixGap I1 I2 I3 0 ω2 0 = 0 := by
  simp [separatrixGap_eq]

theorem separatrixGap_small {I1 I2 I3 : ℝ} (h1 : 0 < I1) (h12 : I1 < I2) (_h23 : I2 < I3) :
    separatrixGap I1 I2 I3 1 0 0 < 0 := by
  rw [separatrixGap_eq]
  nlinarith

theorem separatrixGap_large {I1 I2 I3 : ℝ} (_h1 : 0 < I1) (_h12 : I1 < I2) (h23 : I2 < I3) :
    0 < separatrixGap I1 I2 I3 0 0 1 := by
  rw [separatrixGap_eq]
  nlinarith

theorem continuous_gap (I1 I2 I3 : ℝ) :
    Continuous fun p : ℝ × ℝ × ℝ => separatrixGap I1 I2 I3 p.1 p.2.1 p.2.2 := by
  have hform : (fun p : ℝ × ℝ × ℝ => separatrixGap I1 I2 I3 p.1 p.2.1 p.2.2) =
      fun p => I1 * (I1 - I2) * p.1 ^ 2 + I3 * (I3 - I2) * p.2.2 ^ 2 := by
    funext p
    exact separatrixGap_eq _ _ _ _ _ _
  rw [hform]
  fun_prop

/-! ### Canonical weight -/

noncomputable def axisVar (β I : ℝ) : ℝ≥0 :=
  Real.toNNReal (1 / (β * I))

theorem axisVar_coe {β I : ℝ} (hβ : 0 < β) (hI : 0 < I) :
    (axisVar β I : ℝ) = 1 / (β * I) := by
  unfold axisVar
  rw [Real.coe_toNNReal]
  positivity

theorem axisVar_ne_zero {β I : ℝ} (hβ : 0 < β) (hI : 0 < I) : axisVar β I ≠ 0 := by
  have : (axisVar β I : ℝ) ≠ 0 := by
    rw [axisVar_coe hβ hI]
    positivity
  exact NNReal.coe_ne_zero.mp this

noncomputable def boltzmannDensity (β I1 I2 I3 : ℝ) (p : ℝ × ℝ × ℝ) : ℝ :=
  gaussianPDFReal 0 (axisVar β I1) p.1 *
    gaussianPDFReal 0 (axisVar β I2) p.2.1 *
      gaussianPDFReal 0 (axisVar β I3) p.2.2

theorem boltzmannDensity_pos {β I1 I2 I3 : ℝ} (hβ : 0 < β) (h1 : 0 < I1) (h2 : 0 < I2)
    (h3 : 0 < I3) (p : ℝ × ℝ × ℝ) : 0 < boltzmannDensity β I1 I2 I3 p := by
  unfold boltzmannDensity
  exact mul_pos (mul_pos (gaussianPDFReal_pos _ _ _ (axisVar_ne_zero hβ h1))
    (gaussianPDFReal_pos _ _ _ (axisVar_ne_zero hβ h2)))
    (gaussianPDFReal_pos _ _ _ (axisVar_ne_zero hβ h3))

theorem continuous_boltzmannDensity (β I1 I2 I3 : ℝ) :
    Continuous (boltzmannDensity β I1 I2 I3) := by
  unfold boltzmannDensity gaussianPDFReal
  fun_prop

theorem axis_exponent {β I ω : ℝ} (hβ : 0 < β) (hI : 0 < I) :
    ω ^ 2 / (2 * (axisVar β I : ℝ)) = (β / 2) * I * ω ^ 2 := by
  rw [axisVar_coe hβ hI]
  field_simp [hβ.ne', hI.ne']

/-- The product of the three Gaussians is the normalized Boltzmann factor. -/
theorem boltzmannDensity_eq {β I1 I2 I3 : ℝ} (hβ : 0 < β) (h1 : 0 < I1) (h2 : 0 < I2)
    (h3 : 0 < I3) (p : ℝ × ℝ × ℝ) :
    boltzmannDensity β I1 I2 I3 p =
      Real.exp (-β * rotorEnergy I1 I2 I3 p.1 p.2.1 p.2.2) /
        Real.sqrt ((2 * Real.pi) ^ 3 *
          ((axisVar β I1 : ℝ) * (axisVar β I2 : ℝ) * (axisVar β I3 : ℝ))) := by
  unfold boltzmannDensity gaussianPDFReal rotorEnergy
  simp only [sub_zero]
  set v1 : ℝ := (axisVar β I1 : ℝ)
  set v2 : ℝ := (axisVar β I2 : ℝ)
  set v3 : ℝ := (axisVar β I3 : ℝ)
  have hv1 : 0 < v1 := by
    unfold v1
    rw [axisVar_coe hβ h1]
    positivity
  have hv2 : 0 < v2 := by
    unfold v2
    rw [axisVar_coe hβ h2]
    positivity
  have hv3 : 0 < v3 := by
    unfold v3
    rw [axisVar_coe hβ h3]
    positivity
  have hexp :
      Real.exp (-p.1 ^ 2 / (2 * v1)) * Real.exp (-p.2.1 ^ 2 / (2 * v2)) *
          Real.exp (-p.2.2 ^ 2 / (2 * v3)) =
        Real.exp (-β * ((1 / 2) * (I1 * p.1 ^ 2 + I2 * p.2.1 ^ 2 + I3 * p.2.2 ^ 2))) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    have e1 := axis_exponent (ω := p.1) hβ h1
    have e2 := axis_exponent (ω := p.2.1) hβ h2
    have e3 := axis_exponent (ω := p.2.2) hβ h3
    linear_combination -(e1 + e2 + e3)
  have hsqrt : Real.sqrt (2 * Real.pi * v1) * Real.sqrt (2 * Real.pi * v2) *
      Real.sqrt (2 * Real.pi * v3) =
      Real.sqrt ((2 * Real.pi) ^ 3 * (v1 * v2 * v3)) := by
    rw [← Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2 * Real.pi * v1),
      ← Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2 * Real.pi * v1 * (2 * Real.pi * v2))]
    congr 1
    ring
  calc
    (Real.sqrt (2 * Real.pi * v1))⁻¹ * Real.exp (-p.1 ^ 2 / (2 * v1)) *
          ((Real.sqrt (2 * Real.pi * v2))⁻¹ * Real.exp (-p.2.1 ^ 2 / (2 * v2))) *
        ((Real.sqrt (2 * Real.pi * v3))⁻¹ * Real.exp (-p.2.2 ^ 2 / (2 * v3))) =
      ((Real.sqrt (2 * Real.pi * v1))⁻¹ * (Real.sqrt (2 * Real.pi * v2))⁻¹ *
          (Real.sqrt (2 * Real.pi * v3))⁻¹) *
        (Real.exp (-p.1 ^ 2 / (2 * v1)) * Real.exp (-p.2.1 ^ 2 / (2 * v2)) *
          Real.exp (-p.2.2 ^ 2 / (2 * v3))) := by ring
    _ = (Real.sqrt ((2 * Real.pi) ^ 3 * (v1 * v2 * v3)))⁻¹ *
          Real.exp (-β * ((1 / 2) * (I1 * p.1 ^ 2 + I2 * p.2.1 ^ 2 + I3 * p.2.2 ^ 2))) := by
      rw [hexp, ← hsqrt, mul_inv, mul_inv]
    _ = Real.exp (-β * ((1 / 2) * (I1 * p.1 ^ 2 + I2 * p.2.1 ^ 2 + I3 * p.2.2 ^ 2))) /
          Real.sqrt ((2 * Real.pi) ^ 3 * (v1 * v2 * v3)) := by
      rw [div_eq_mul_inv]
      ring

noncomputable def rotorMeasure (β I1 I2 I3 : ℝ) : Measure (ℝ × ℝ × ℝ) :=
  (gaussianReal 0 (axisVar β I1)).prod
    ((gaussianReal 0 (axisVar β I2)).prod (gaussianReal 0 (axisVar β I3)))

theorem rotorMeasure_withDensity {β I1 I2 I3 : ℝ} (hβ : 0 < β) (h1 : 0 < I1) (h2 : 0 < I2)
    (h3 : 0 < I3) :
    rotorMeasure β I1 I2 I3 =
      volume.withDensity (fun z : ℝ × ℝ × ℝ =>
        gaussianPDF 0 (axisVar β I1) z.1 *
          gaussianPDF 0 (axisVar β I2) z.2.1 *
            gaussianPDF 0 (axisVar β I3) z.2.2) := by
  have hv1 := axisVar_ne_zero hβ h1
  have hv2 := axisVar_ne_zero hβ h2
  have hv3 := axisVar_ne_zero hβ h3
  unfold rotorMeasure
  rw [gaussianReal_of_var_ne_zero 0 hv1, gaussianReal_of_var_ne_zero 0 hv2,
    gaussianReal_of_var_ne_zero 0 hv3]
  have hinner :
      (volume.withDensity (gaussianPDF 0 (axisVar β I2))).prod
          (volume.withDensity (gaussianPDF 0 (axisVar β I3))) =
        (volume.prod volume).withDensity fun y : ℝ × ℝ =>
          gaussianPDF 0 (axisVar β I2) y.1 * gaussianPDF 0 (axisVar β I3) y.2 :=
    prod_withDensity (measurable_gaussianPDF _ _) (measurable_gaussianPDF _ _)
  rw [hinner]
  have hfun : Measurable fun y : ℝ × ℝ =>
      gaussianPDF 0 (axisVar β I2) y.1 * gaussianPDF 0 (axisVar β I3) y.2 := by
    fun_prop
  rw [prod_withDensity (μ := volume) (ν := volume.prod volume) (measurable_gaussianPDF _ _) hfun]
  have hbase : (volume.prod (volume.prod (volume : Measure ℝ)) : Measure (ℝ × ℝ × ℝ)) = volume := by
    rfl
  rw [hbase]
  refine withDensity_congr_ae ?_
  filter_upwards with z
  rw [mul_assoc]

private theorem gauss_sq_integrable {v : ℝ≥0} :
    Integrable (fun x : ℝ => x ^ 2) (gaussianReal 0 v) :=
  (memLp_id_gaussianReal (μ := 0) (v := v) 2).integrable_sq

theorem gaussian_second_moment {v : ℝ≥0} :
    ∫ x, x ^ 2 ∂gaussianReal 0 v = (v : ℝ) := by
  have hvar : Var[id; gaussianReal 0 v] = (v : ℝ) := variance_id_gaussianReal
  rw [variance_eq_integral (X := id) (μ := gaussianReal 0 v) aemeasurable_id] at hvar
  simpa [integral_id_gaussianReal, sub_zero, id_eq] using hvar

private theorem prob_inner {β I2 I3 : ℝ} :
    IsProbabilityMeasure
      ((gaussianReal 0 (axisVar β I2)).prod (gaussianReal 0 (axisVar β I3))) :=
  inferInstance

theorem integral_ω1_sq {β I1 I2 I3 : ℝ} :
    ∫ p : ℝ × ℝ × ℝ, p.1 ^ 2 ∂rotorMeasure β I1 I2 I3 = (axisVar β I1 : ℝ) := by
  have _ := prob_inner (β := β) (I2 := I2) (I3 := I3)
  unfold rotorMeasure
  rw [integral_fun_fst (μ := gaussianReal 0 (axisVar β I1))
    (ν := (gaussianReal 0 (axisVar β I2)).prod (gaussianReal 0 (axisVar β I3)))
    (fun x : ℝ => x ^ 2)]
  simp only [Measure.real, measure_univ, ENNReal.toReal_one, one_smul]
  exact gaussian_second_moment

theorem integral_ω2_sq {β I1 I2 I3 : ℝ} :
    ∫ p : ℝ × ℝ × ℝ, p.2.1 ^ 2 ∂rotorMeasure β I1 I2 I3 = (axisVar β I2 : ℝ) := by
  have _ := prob_inner (β := β) (I2 := I2) (I3 := I3)
  unfold rotorMeasure
  have houter :=
    integral_fun_snd (μ := gaussianReal 0 (axisVar β I1))
      (ν := (gaussianReal 0 (axisVar β I2)).prod (gaussianReal 0 (axisVar β I3)))
      (fun y : ℝ × ℝ => y.1 ^ 2)
  have hinner :=
    integral_fun_fst (μ := gaussianReal 0 (axisVar β I2))
      (ν := gaussianReal 0 (axisVar β I3)) (fun x : ℝ => x ^ 2)
  rw [houter]
  simp only [Measure.real, measure_univ, ENNReal.toReal_one, one_smul]
  rw [hinner]
  simp only [Measure.real, measure_univ, ENNReal.toReal_one, one_smul]
  exact gaussian_second_moment

theorem integral_ω3_sq {β I1 I2 I3 : ℝ} :
    ∫ p : ℝ × ℝ × ℝ, p.2.2 ^ 2 ∂rotorMeasure β I1 I2 I3 = (axisVar β I3 : ℝ) := by
  have _ := prob_inner (β := β) (I2 := I2) (I3 := I3)
  unfold rotorMeasure
  have houter :=
    integral_fun_snd (μ := gaussianReal 0 (axisVar β I1))
      (ν := (gaussianReal 0 (axisVar β I2)).prod (gaussianReal 0 (axisVar β I3)))
      (fun y : ℝ × ℝ => y.2 ^ 2)
  have hinner :=
    integral_fun_snd (μ := gaussianReal 0 (axisVar β I2))
      (ν := gaussianReal 0 (axisVar β I3)) (fun x : ℝ => x ^ 2)
  rw [houter]
  simp only [Measure.real, measure_univ, ENNReal.toReal_one, one_smul]
  rw [hinner]
  simp only [Measure.real, measure_univ, ENNReal.toReal_one, one_smul]
  exact gaussian_second_moment

private theorem integrable_comp_eq {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : α → ℝ} (h : Integrable f μ) (heq : f = g) : Integrable g μ :=
  heq ▸ h

private theorem integrable_ω1_sq {β I1 I2 I3 : ℝ} :
    Integrable (fun p : ℝ × ℝ × ℝ => p.1 ^ 2) (rotorMeasure β I1 I2 I3) := by
  have _ := prob_inner (β := β) (I2 := I2) (I3 := I3)
  let μ1 := gaussianReal 0 (axisVar β I1)
  let μ23 := (gaussianReal 0 (axisVar β I2)).prod (gaussianReal 0 (axisVar β I3))
  unfold rotorMeasure
  exact integrable_comp_eq
    ((measurePreserving_fst (μ := μ1) (ν := μ23)).integrable_comp_of_integrable
      (gauss_sq_integrable (v := axisVar β I1)))
    (by funext p; rfl)

private theorem integrable_ω2_sq {β I1 I2 I3 : ℝ} :
    Integrable (fun p : ℝ × ℝ × ℝ => p.2.1 ^ 2) (rotorMeasure β I1 I2 I3) := by
  have _ := prob_inner (β := β) (I2 := I2) (I3 := I3)
  have hinner : Integrable (fun y : ℝ × ℝ => y.1 ^ 2)
      ((gaussianReal 0 (axisVar β I2)).prod (gaussianReal 0 (axisVar β I3))) := by
    exact integrable_comp_eq
      ((measurePreserving_fst (μ := gaussianReal 0 (axisVar β I2))
        (ν := gaussianReal 0 (axisVar β I3))).integrable_comp_of_integrable
        (gauss_sq_integrable (v := axisVar β I2)))
      (by funext y; rfl)
  let μ1 := gaussianReal 0 (axisVar β I1)
  let μ23 := (gaussianReal 0 (axisVar β I2)).prod (gaussianReal 0 (axisVar β I3))
  unfold rotorMeasure
  exact integrable_comp_eq
    ((measurePreserving_snd (μ := μ1) (ν := μ23)).integrable_comp_of_integrable hinner)
    (by funext p; rfl)

private theorem integrable_ω3_sq {β I1 I2 I3 : ℝ} :
    Integrable (fun p : ℝ × ℝ × ℝ => p.2.2 ^ 2) (rotorMeasure β I1 I2 I3) := by
  have _ := prob_inner (β := β) (I2 := I2) (I3 := I3)
  have hinner : Integrable (fun y : ℝ × ℝ => y.2 ^ 2)
      ((gaussianReal 0 (axisVar β I2)).prod (gaussianReal 0 (axisVar β I3))) := by
    exact integrable_comp_eq
      ((measurePreserving_snd (μ := gaussianReal 0 (axisVar β I2))
        (ν := gaussianReal 0 (axisVar β I3))).integrable_comp_of_integrable
        (gauss_sq_integrable (v := axisVar β I3)))
      (by funext y; rfl)
  let μ1 := gaussianReal 0 (axisVar β I1)
  let μ23 := (gaussianReal 0 (axisVar β I2)).prod (gaussianReal 0 (axisVar β I3))
  unfold rotorMeasure
  exact integrable_comp_eq
    ((measurePreserving_snd (μ := μ1) (ν := μ23)).integrable_comp_of_integrable hinner)
    (by funext p; rfl)

theorem meanEnergy {β I1 I2 I3 : ℝ} (hβ : 0 < β) (h1 : 0 < I1) (h2 : 0 < I2) (h3 : 0 < I3) :
    ∫ p : ℝ × ℝ × ℝ, rotorEnergy I1 I2 I3 p.1 p.2.1 p.2.2 ∂rotorMeasure β I1 I2 I3 =
      3 / (2 * β) := by
  unfold rotorEnergy
  have h1i := integrable_ω1_sq (β := β) (I1 := I1) (I2 := I2) (I3 := I3)
  have h2i := integrable_ω2_sq (β := β) (I1 := I1) (I2 := I2) (I3 := I3)
  have h3i := integrable_ω3_sq (β := β) (I1 := I1) (I2 := I2) (I3 := I3)
  have hsum0 := (h1i.const_mul I1).add ((h2i.const_mul I2).add (h3i.const_mul I3))
  have hsum : Integrable (fun p : ℝ × ℝ × ℝ =>
      I1 * p.1 ^ 2 + I2 * p.2.1 ^ 2 + I3 * p.2.2 ^ 2) (rotorMeasure β I1 I2 I3) := by
    refine integrable_comp_eq hsum0 ?_
    funext p
    simp only [Pi.add_apply]
    ring
  rw [integral_const_mul (1 / 2)]
  have hflat : (fun p : ℝ × ℝ × ℝ => I1 * p.1 ^ 2 + I2 * p.2.1 ^ 2 + I3 * p.2.2 ^ 2) =
      fun a : ℝ × ℝ × ℝ =>
        (fun x : ℝ × ℝ × ℝ => I1 * x.1 ^ 2) a +
          ((fun x : ℝ × ℝ × ℝ => I2 * x.2.1 ^ 2) + fun x : ℝ × ℝ × ℝ => I3 * x.2.2 ^ 2) a := by
    funext a
    simp only [Pi.add_apply]
    ring
  have hinner : ((fun x : ℝ × ℝ × ℝ => I2 * x.2.1 ^ 2) + fun x : ℝ × ℝ × ℝ => I3 * x.2.2 ^ 2) =
      fun a : ℝ × ℝ × ℝ =>
        (fun x : ℝ × ℝ × ℝ => I2 * x.2.1 ^ 2) a + (fun x : ℝ × ℝ × ℝ => I3 * x.2.2 ^ 2) a := by
    funext a
    rfl
  have hsplit :
      ∫ p : ℝ × ℝ × ℝ, I1 * p.1 ^ 2 + I2 * p.2.1 ^ 2 + I3 * p.2.2 ^ 2 ∂rotorMeasure β I1 I2 I3 =
        I1 * (axisVar β I1 : ℝ) + I2 * (axisVar β I2 : ℝ) + I3 * (axisVar β I3 : ℝ) := by
    have hadd := integral_add (h1i.const_mul I1) ((h2i.const_mul I2).add (h3i.const_mul I3))
    have hadd2 := integral_add (h2i.const_mul I2) (h3i.const_mul I3)
    rw [hflat, hadd, hinner, hadd2,
      integral_const_mul I1 (fun p : ℝ × ℝ × ℝ => p.1 ^ 2),
      integral_const_mul I2 (fun p : ℝ × ℝ × ℝ => p.2.1 ^ 2),
      integral_const_mul I3 (fun p : ℝ × ℝ × ℝ => p.2.2 ^ 2),
      integral_ω1_sq, integral_ω2_sq, integral_ω3_sq]
    ring
  rw [hsplit, axisVar_coe hβ h1, axisVar_coe hβ h2, axisVar_coe hβ h3]
  field_simp [hβ.ne', h1.ne', h2.ne', h3.ne']
  norm_num

theorem meanGap {β I1 I2 I3 : ℝ} (hβ : 0 < β) (h1 : 0 < I1) (_h2 : 0 < I2) (h3 : 0 < I3) :
    ∫ p : ℝ × ℝ × ℝ, separatrixGap I1 I2 I3 p.1 p.2.1 p.2.2 ∂rotorMeasure β I1 I2 I3 =
      (I1 + I3 - 2 * I2) / β := by
  have hform : (fun p : ℝ × ℝ × ℝ => separatrixGap I1 I2 I3 p.1 p.2.1 p.2.2) =
      fun p => I1 * (I1 - I2) * p.1 ^ 2 + I3 * (I3 - I2) * p.2.2 ^ 2 := by
    funext p
    exact separatrixGap_eq _ _ _ _ _ _
  have hflat : (fun p : ℝ × ℝ × ℝ =>
      I1 * (I1 - I2) * p.1 ^ 2 + I3 * (I3 - I2) * p.2.2 ^ 2) =
      fun a : ℝ × ℝ × ℝ =>
        (fun x : ℝ × ℝ × ℝ => I1 * (I1 - I2) * x.1 ^ 2) a +
          (fun x : ℝ × ℝ × ℝ => I3 * (I3 - I2) * x.2.2 ^ 2) a := by
    funext a
    rfl
  rw [hform]
  have h1i := integrable_ω1_sq (β := β) (I1 := I1) (I2 := I2) (I3 := I3)
  have h3i := integrable_ω3_sq (β := β) (I1 := I1) (I2 := I2) (I3 := I3)
  have hadd := integral_add (h1i.const_mul (I1 * (I1 - I2))) (h3i.const_mul (I3 * (I3 - I2)))
  rw [hflat, hadd,
    integral_const_mul (I1 * (I1 - I2)) (fun p : ℝ × ℝ × ℝ => p.1 ^ 2),
    integral_const_mul (I3 * (I3 - I2)) (fun p : ℝ × ℝ × ℝ => p.2.2 ^ 2),
    integral_ω1_sq, integral_ω3_sq, axisVar_coe hβ h1, axisVar_coe hβ h3]
  field_simp [hβ.ne', h1.ne', h3.ne']
  ring

theorem meanGap_eq_zero_iff {β I1 I2 I3 : ℝ} (hβ : β ≠ 0) :
    (I1 + I3 - 2 * I2) / β = 0 ↔ I1 + I3 = 2 * I2 := by
  rw [div_eq_zero_iff]
  simp [hβ, sub_eq_zero, two_mul]

theorem interceptGap_eq (a b c : ℝ) :
    secondZ a b c + secondX a b c - 2 * secondY a b c =
      2 * (2 * b ^ 2 - a ^ 2 - c ^ 2) := by
  rw [secondZ_eq, secondX_eq, secondY_eq]
  ring

theorem interceptGap_both_signs :
    2 * ((2 : ℝ) ^ 2) - 1 ^ 2 - 3 ^ 2 < 0 ∧
      0 < 2 * ((2 : ℝ) ^ 2) - 1 ^ 2 - (5 / 2) ^ 2 := by
  norm_num

theorem boltzmann_closedBall_pos {β I1 I2 I3 : ℝ} {p : ℝ × ℝ × ℝ} {r : ℝ}
    (hβ : 0 < β) (h1 : 0 < I1) (h2 : 0 < I2) (h3 : 0 < I3) (hr : 0 < r) :
    0 < ∫ x in closedBall p r, boltzmannDensity β I1 I2 I3 x := by
  have hf := continuous_boltzmannDensity β I1 I2 I3
  have hs : IsCompact (closedBall p r) := isCompact_closedBall p r
  have hne : (closedBall p r).Nonempty := ⟨p, mem_closedBall_self hr.le⟩
  obtain ⟨x, _, hmin⟩ := hs.exists_isMinOn hne hf.continuousOn
  have hx0 : 0 < boltzmannDensity β I1 I2 I3 x := boltzmannDensity_pos hβ h1 h2 h3 x
  have hle : ∀ y ∈ closedBall p r, boltzmannDensity β I1 I2 I3 x ≤
      boltzmannDensity β I1 I2 I3 y :=
    (isMinOn_iff.mp hmin)
  have hmeas : MeasurableSet (closedBall p r) := measurableSet_closedBall
  have hfin : volume (closedBall p r) ≠ ∞ := hs.measure_ne_top
  have hint : IntegrableOn (boltzmannDensity β I1 I2 I3) (closedBall p r) :=
    hf.continuousOn.integrableOn_compact hs
  have hge := setIntegral_ge_of_const_le_real (f := boltzmannDensity β I1 I2 I3)
    (c := boltzmannDensity β I1 I2 I3 x) hmeas hfin hle hint
  have hvol : 0 < volume.real (closedBall p r) :=
    ENNReal.toReal_pos (measure_closedBall_pos volume p hr).ne' hfin
  exact lt_of_lt_of_le (mul_pos hx0 hvol) hge

theorem rotor_closedBall_pos {β I1 I2 I3 : ℝ} {p : ℝ × ℝ × ℝ} {r : ℝ}
    (hβ : 0 < β) (h1 : 0 < I1) (h2 : 0 < I2) (h3 : 0 < I3) (hr : 0 < r) :
    0 < rotorMeasure β I1 I2 I3 (closedBall p r) := by
  rw [rotorMeasure_withDensity hβ h1 h2 h3]
  have hmeas : MeasurableSet (closedBall p r) := measurableSet_closedBall
  rw [withDensity_apply _ hmeas]
  have hint : IntegrableOn (boltzmannDensity β I1 I2 I3) (closedBall p r) volume :=
    (continuous_boltzmannDensity β I1 I2 I3).continuousOn.integrableOn_compact
      (isCompact_closedBall p r)
  have hnn : 0 ≤ᵐ[volume.restrict (closedBall p r)] boltzmannDensity β I1 I2 I3 :=
    ae_of_all _ fun x => (boltzmannDensity_pos hβ h1 h2 h3 x).le
  have hlin :=
    ofReal_integral_eq_lintegral_ofReal (μ := volume.restrict (closedBall p r)) hint hnn
  have hden : ∀ x, gaussianPDF 0 (axisVar β I1) x.1 *
      gaussianPDF 0 (axisVar β I2) x.2.1 * gaussianPDF 0 (axisVar β I3) x.2.2 =
      ENNReal.ofReal (boltzmannDensity β I1 I2 I3 x) := by
    intro x
    unfold boltzmannDensity
    have hprod : 0 ≤ gaussianPDFReal 0 (axisVar β I1) x.1 *
        gaussianPDFReal 0 (axisVar β I2) x.2.1 :=
      mul_nonneg (gaussianPDFReal_nonneg _ _ _) (gaussianPDFReal_nonneg _ _ _)
    rw [gaussianPDF, gaussianPDF, gaussianPDF,
      ← ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _),
      ← ENNReal.ofReal_mul hprod]
  simp_rw [hden]
  rw [← hlin, ENNReal.ofReal_pos]
  simpa using boltzmann_closedBall_pos (p := p) (r := r) hβ h1 h2 h3 hr

theorem weight_of_open_pos {β I1 I2 I3 : ℝ} {s : Set (ℝ × ℝ × ℝ)} {p : ℝ × ℝ × ℝ}
    (hβ : 0 < β) (h1 : 0 < I1) (h2 : 0 < I2) (h3 : 0 < I3)
    (hs : IsOpen s) (hp : p ∈ s) :
    0 < rotorMeasure β I1 I2 I3 s := by
  obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp hs p hp
  have hhalf : 0 < r / 2 := by linarith
  have hclosed : closedBall p (r / 2) ⊆ s := by
    intro x hx
    apply hsub
    exact lt_of_le_of_lt (mem_closedBall.mp hx) (by linarith : r / 2 < r)
  exact lt_of_lt_of_le (rotor_closedBall_pos (p := p) (r := r / 2) hβ h1 h2 h3 hhalf)
    (measure_mono hclosed)

theorem gap_negative_weight {β I1 I2 I3 : ℝ} (hβ : 0 < β) (h1 : 0 < I1) (h12 : I1 < I2)
    (h23 : I2 < I3) :
    0 < rotorMeasure β I1 I2 I3 {p | separatrixGap I1 I2 I3 p.1 p.2.1 p.2.2 < 0} := by
  have h2 : 0 < I2 := lt_trans h1 h12
  have h3 : 0 < I3 := lt_trans h2 h23
  have hs : IsOpen {p : ℝ × ℝ × ℝ | separatrixGap I1 I2 I3 p.1 p.2.1 p.2.2 < 0} :=
    isOpen_lt (continuous_gap I1 I2 I3) continuous_const
  have hp : ((1, 0, 0) : ℝ × ℝ × ℝ) ∈
      {p | separatrixGap I1 I2 I3 p.1 p.2.1 p.2.2 < 0} := by
    simpa using separatrixGap_small h1 h12 h23
  exact weight_of_open_pos hβ h1 h2 h3 hs hp

theorem gap_positive_weight {β I1 I2 I3 : ℝ} (hβ : 0 < β) (h1 : 0 < I1) (h12 : I1 < I2)
    (h23 : I2 < I3) :
    0 < rotorMeasure β I1 I2 I3 {p | 0 < separatrixGap I1 I2 I3 p.1 p.2.1 p.2.2} := by
  have h2 : 0 < I2 := lt_trans h1 h12
  have h3 : 0 < I3 := lt_trans h2 h23
  have hs : IsOpen {p : ℝ × ℝ × ℝ | 0 < separatrixGap I1 I2 I3 p.1 p.2.1 p.2.2} :=
    isOpen_lt continuous_const (continuous_gap I1 I2 I3)
  have hp : ((0, 0, 1) : ℝ × ℝ × ℝ) ∈
      {p | 0 < separatrixGap I1 I2 I3 p.1 p.2.1 p.2.2} := by
    simpa using separatrixGap_large h1 h12 h23
  exact weight_of_open_pos hβ h1 h2 h3 hs hp

/-! ### Transverse residual about an intermediate spin -/

noncomputable def transverseResidual (I1 I2 I3 B ω1 ω3 : ℝ) : ℝ :=
  Real.sqrt ((I1 * ω1 ^ 2 + I3 * ω3 ^ 2) / (I2 * B ^ 2))

noncomputable def residualState (I1 I2 B : ℝ) : ℝ × ℝ × ℝ :=
  (B * Real.sqrt (I2 / I1) / 12, B, 0)

theorem residualState_eq {I1 I2 I3 B : ℝ} (h1 : 0 < I1) (h2 : 0 < I2) (hB : 0 < B) :
    transverseResidual I1 I2 I3 B (residualState I1 I2 B).1 (residualState I1 I2 B).2.2 =
      1 / 12 := by
  unfold transverseResidual residualState
  have harg : (I1 * (B * Real.sqrt (I2 / I1) / 12) ^ 2 + I3 * 0 ^ 2) / (I2 * B ^ 2) =
      1 / 144 := by
    have hsq : (Real.sqrt (I2 / I1)) ^ 2 = I2 / I1 :=
      Real.sq_sqrt (by positivity : (0 : ℝ) ≤ I2 / I1)
    calc
      (I1 * (B * Real.sqrt (I2 / I1) / 12) ^ 2 + I3 * 0 ^ 2) / (I2 * B ^ 2) =
          (I1 * (B ^ 2 * (Real.sqrt (I2 / I1)) ^ 2 / 144)) / (I2 * B ^ 2) := by ring
      _ = (I1 * (B ^ 2 * (I2 / I1) / 144)) / (I2 * B ^ 2) := by rw [hsq]
      _ = 1 / 144 := by field_simp [h1.ne', h2.ne', hB.ne']
  rw [harg]
  have hsq : (1 / 12 : ℝ) ^ 2 = 1 / 144 := by norm_num
  rw [← hsq, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1 / 12)]

theorem continuous_transverseResidual {I1 I2 I3 B : ℝ} (h2 : 0 < I2) (hB : 0 < B) :
    Continuous fun p : ℝ × ℝ × ℝ => transverseResidual I1 I2 I3 B p.1 p.2.2 := by
  unfold transverseResidual
  have hden : ∀ _p : ℝ × ℝ × ℝ, I2 * B ^ 2 ≠ 0 := fun _ => by positivity
  fun_prop (disch := assumption)

def residualSet (I1 I2 I3 B : ℝ) : Set (ℝ × ℝ × ℝ) :=
  {p | 0 < transverseResidual I1 I2 I3 B p.1 p.2.2 ∧
    transverseResidual I1 I2 I3 B p.1 p.2.2 < 1 / 6}

theorem isOpen_residualSet {I1 I2 I3 B : ℝ} (h2 : 0 < I2) (hB : 0 < B) :
    IsOpen (residualSet I1 I2 I3 B) := by
  have hcont := continuous_transverseResidual (I1 := I1) (I3 := I3) h2 hB
  have hpos : IsOpen {p : ℝ × ℝ × ℝ | 0 < transverseResidual I1 I2 I3 B p.1 p.2.2} :=
    isOpen_lt continuous_const hcont
  have hsmall : IsOpen {p : ℝ × ℝ × ℝ |
      transverseResidual I1 I2 I3 B p.1 p.2.2 < 1 / 6} :=
    isOpen_lt hcont continuous_const
  have : residualSet I1 I2 I3 B =
      {p | 0 < transverseResidual I1 I2 I3 B p.1 p.2.2} ∩
        {p | transverseResidual I1 I2 I3 B p.1 p.2.2 < 1 / 6} := by
    ext p
    simp [residualSet]
  simpa [this] using hpos.inter hsmall

theorem residualState_mem {I1 I2 I3 B : ℝ} (h1 : 0 < I1) (h2 : 0 < I2) (hB : 0 < B) :
    residualState I1 I2 B ∈ residualSet I1 I2 I3 B := by
  have h := residualState_eq (I3 := I3) h1 h2 hB
  constructor
  · rw [h]; norm_num
  · rw [h]; norm_num

/-- The canonical weight of the residuals that wait longer than the crossing is positive. -/
theorem residual_weight_pos {β I1 I2 I3 B : ℝ} (hβ : 0 < β) (h1 : 0 < I1) (h12 : I1 < I2)
    (h23 : I2 < I3) (hB : 0 < B) :
    0 < rotorMeasure β I1 I2 I3 (residualSet I1 I2 I3 B) := by
  have h2 : 0 < I2 := lt_trans h1 h12
  have h3 : 0 < I3 := lt_trans h2 h23
  exact weight_of_open_pos hβ h1 h2 h3 (isOpen_residualSet h2 hB)
    (residualState_mem h1 h2 hB)

end DstDiophantine.Gravity.RacketThermal
