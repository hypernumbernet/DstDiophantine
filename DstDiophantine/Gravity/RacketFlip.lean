import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Artanh
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The intermediate-axis reversal

A torque-free aggregate whose principal moments satisfy `0 < I1 < I2 < I3`
spins on the separatrix

`ω1 = A sech(k t)`, `ω2 = B tanh(k t)`, `ω3 = C sech(k t)`,

with `k`, `A`, and `C` fixed by `I1`, `I2`, `I3`, and `B > 0`. The profile
satisfies Euler's equations, keeps the energy `½ I2 B²`, and keeps
`L² = 2 E I2`. The intermediate component changes sign at `t = 0` and nowhere
else.

The transverse curvature is positive only about that intermediate axis. A
residual of relative size `ε < 1/6` takes longer to reach half amplitude than
the reversal itself takes to cross from half to half, and the wait exceeds
every bound as the residual shrinks. If two principal moments agree, the
curvature is zero.

## Not claimed

* A count of reversals. The canonical weight is `RacketThermal`.
-/

namespace DstDiophantine.Gravity.RacketFlip

open Real Filter

noncomputable def sech (t : ℝ) : ℝ :=
  (Real.cosh t)⁻¹

noncomputable def sepA (I1 I2 I3 B : ℝ) : ℝ :=
  B * Real.sqrt (I2 * (I3 - I2) / (I1 * (I3 - I1)))

noncomputable def sepC (I1 I2 I3 B : ℝ) : ℝ :=
  B * Real.sqrt (I2 * (I2 - I1) / (I3 * (I3 - I1)))

noncomputable def sepK (I1 I2 I3 B : ℝ) : ℝ :=
  B * Real.sqrt ((I2 - I1) * (I3 - I2) / (I1 * I3))

noncomputable def omega1 (I1 I2 I3 B t : ℝ) : ℝ :=
  sepA I1 I2 I3 B * sech (sepK I1 I2 I3 B * t)

noncomputable def omega2 (I1 I2 I3 B t : ℝ) : ℝ :=
  B * Real.tanh (sepK I1 I2 I3 B * t)

noncomputable def omega3 (I1 I2 I3 B t : ℝ) : ℝ :=
  sepC I1 I2 I3 B * sech (sepK I1 I2 I3 B * t)

noncomputable def racketEnergy (I1 I2 I3 B t : ℝ) : ℝ :=
  (1 / 2) * (I1 * omega1 I1 I2 I3 B t ^ 2 + I2 * omega2 I1 I2 I3 B t ^ 2 +
    I3 * omega3 I1 I2 I3 B t ^ 2)

noncomputable def racketLsq (I1 I2 I3 B t : ℝ) : ℝ :=
  I1 ^ 2 * omega1 I1 I2 I3 B t ^ 2 + I2 ^ 2 * omega2 I1 I2 I3 B t ^ 2 +
    I3 ^ 2 * omega3 I1 I2 I3 B t ^ 2

/-- Squared growth rate about the intermediate axis. -/
noncomputable def rateMid (I1 I2 I3 Ω : ℝ) : ℝ :=
  ((I3 - I2) * (I2 - I1) / (I1 * I3)) * Ω ^ 2

/-- Squared rate about the small axis. It is negative. -/
noncomputable def rateSmall (I1 I2 I3 Ω : ℝ) : ℝ :=
  -((I3 - I1) * (I2 - I1) / (I2 * I3)) * Ω ^ 2

/-- Squared rate about the large axis. It is negative. -/
noncomputable def rateLarge (I1 I2 I3 Ω : ℝ) : ℝ :=
  ((I2 - I3) * (I3 - I1) / (I1 * I2)) * Ω ^ 2

noncomputable def crossingTime (k : ℝ) : ℝ :=
  Real.log 3 / k

noncomputable def waitingTime (k ε : ℝ) : ℝ :=
  (1 / k) * Real.log (1 / (2 * ε))

variable {I1 I2 I3 B : ℝ}

private theorem gaps (h1 : 0 < I1) (h12 : I1 < I2) (h23 : I2 < I3) :
    0 < I2 ∧ 0 < I3 ∧ 0 < I2 - I1 ∧ 0 < I3 - I2 ∧ 0 < I3 - I1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> linarith

theorem sepA_sq (h1 : 0 < I1) (h12 : I1 < I2) (h23 : I2 < I3) (_hB : 0 < B) :
    sepA I1 I2 I3 B ^ 2 = B ^ 2 * (I2 * (I3 - I2) / (I1 * (I3 - I1))) := by
  unfold sepA
  have harg : 0 ≤ I2 * (I3 - I2) / (I1 * (I3 - I1)) := by
    rcases gaps h1 h12 h23 with ⟨hI2, _, _, h32, h31⟩
    exact div_nonneg (mul_nonneg hI2.le h32.le) (mul_pos h1 h31).le
  rw [mul_pow, Real.sq_sqrt harg]

theorem sepC_sq (h1 : 0 < I1) (h12 : I1 < I2) (h23 : I2 < I3) (_hB : 0 < B) :
    sepC I1 I2 I3 B ^ 2 = B ^ 2 * (I2 * (I2 - I1) / (I3 * (I3 - I1))) := by
  unfold sepC
  have harg : 0 ≤ I2 * (I2 - I1) / (I3 * (I3 - I1)) := by
    rcases gaps h1 h12 h23 with ⟨hI2, hI3, h21, _, h31⟩
    exact div_nonneg (mul_nonneg hI2.le h21.le) (mul_pos hI3 h31).le
  rw [mul_pow, Real.sq_sqrt harg]

theorem sepK_sq (h1 : 0 < I1) (h12 : I1 < I2) (h23 : I2 < I3) (_hB : 0 < B) :
    sepK I1 I2 I3 B ^ 2 = B ^ 2 * ((I2 - I1) * (I3 - I2) / (I1 * I3)) := by
  unfold sepK
  have harg : 0 ≤ (I2 - I1) * (I3 - I2) / (I1 * I3) := by
    rcases gaps h1 h12 h23 with ⟨_, hI3, h21, h32, _⟩
    exact div_nonneg (mul_nonneg h21.le h32.le) (mul_pos h1 hI3).le
  rw [mul_pow, Real.sq_sqrt harg]

theorem sepA_nonneg (_h1 : 0 < I1) (_h12 : I1 < I2) (_h23 : I2 < I3) (hB : 0 < B) :
    0 ≤ sepA I1 I2 I3 B := by
  unfold sepA
  exact mul_nonneg hB.le (Real.sqrt_nonneg _)

theorem sepC_nonneg (_h1 : 0 < I1) (_h12 : I1 < I2) (_h23 : I2 < I3) (hB : 0 < B) :
    0 ≤ sepC I1 I2 I3 B := by
  unfold sepC
  exact mul_nonneg hB.le (Real.sqrt_nonneg _)

theorem sepK_nonneg (_h1 : 0 < I1) (_h12 : I1 < I2) (_h23 : I2 < I3) (hB : 0 < B) :
    0 ≤ sepK I1 I2 I3 B := by
  unfold sepK
  exact mul_nonneg hB.le (Real.sqrt_nonneg _)

theorem sepK_pos (h1 : 0 < I1) (h12 : I1 < I2) (h23 : I2 < I3) (hB : 0 < B) :
    0 < sepK I1 I2 I3 B := by
  rcases gaps h1 h12 h23 with ⟨_, hI3, h21, h32, _⟩
  unfold sepK
  exact mul_pos hB (Real.sqrt_pos.mpr (div_pos (mul_pos h21 h32) (mul_pos h1 hI3)))

private theorem eq_of_sq_eq_nonneg {a b : ℝ} (hsq : a ^ 2 = b ^ 2) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a = b := by
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
  · exact h
  · linarith

theorem amp_energy (h1 : 0 < I1) (h12 : I1 < I2) (h23 : I2 < I3) (hB : 0 < B) :
    I1 * sepA I1 I2 I3 B ^ 2 + I3 * sepC I1 I2 I3 B ^ 2 = I2 * B ^ 2 := by
  rw [sepA_sq h1 h12 h23 hB, sepC_sq h1 h12 h23 hB]
  rcases gaps h1 h12 h23 with ⟨_, hI3, _, _, h31⟩
  have hI1 := h1.ne'
  have hD := h31.ne'
  have hI3n := hI3.ne'
  have t1 :
      I1 * (B ^ 2 * (I2 * (I3 - I2) / (I1 * (I3 - I1)))) =
        B ^ 2 * I2 * (I3 - I2) / (I3 - I1) := by field_simp [hI1, hD]
  have t3 :
      I3 * (B ^ 2 * (I2 * (I2 - I1) / (I3 * (I3 - I1)))) =
        B ^ 2 * I2 * (I2 - I1) / (I3 - I1) := by field_simp [hI3n, hD]
  rw [t1, t3]
  have tsum :
      B ^ 2 * I2 * (I3 - I2) / (I3 - I1) + B ^ 2 * I2 * (I2 - I1) / (I3 - I1) =
        B ^ 2 * I2 * ((I3 - I2) + (I2 - I1)) / (I3 - I1) := by field_simp [hD]
  rw [tsum, show (I3 - I2) + (I2 - I1) = I3 - I1 by ring]
  field_simp [hD]

theorem amp_momentum (h1 : 0 < I1) (h12 : I1 < I2) (h23 : I2 < I3) (hB : 0 < B) :
    I1 ^ 2 * sepA I1 I2 I3 B ^ 2 + I3 ^ 2 * sepC I1 I2 I3 B ^ 2 = I2 ^ 2 * B ^ 2 := by
  rw [sepA_sq h1 h12 h23 hB, sepC_sq h1 h12 h23 hB]
  rcases gaps h1 h12 h23 with ⟨_, hI3, _, _, h31⟩
  have hI1 := h1.ne'
  have hD := h31.ne'
  have hI3n := hI3.ne'
  have t1 :
      I1 ^ 2 * (B ^ 2 * (I2 * (I3 - I2) / (I1 * (I3 - I1)))) =
        I1 * B ^ 2 * I2 * (I3 - I2) / (I3 - I1) := by field_simp [hI1, hD]
  have t3 :
      I3 ^ 2 * (B ^ 2 * (I2 * (I2 - I1) / (I3 * (I3 - I1)))) =
        I3 * B ^ 2 * I2 * (I2 - I1) / (I3 - I1) := by field_simp [hI3n, hD]
  rw [t1, t3]
  have tsum :
      I1 * B ^ 2 * I2 * (I3 - I2) / (I3 - I1) + I3 * B ^ 2 * I2 * (I2 - I1) / (I3 - I1) =
        B ^ 2 * I2 * (I1 * (I3 - I2) + I3 * (I2 - I1)) / (I3 - I1) := by field_simp [hD]
  rw [tsum, show I1 * (I3 - I2) + I3 * (I2 - I1) = I2 * (I3 - I1) by ring]
  field_simp [hD]

theorem coeff_ak (h1 : 0 < I1) (h12 : I1 < I2) (h23 : I2 < I3) (hB : 0 < B) :
    sepA I1 I2 I3 B * sepK I1 I2 I3 B =
      ((I3 - I2) / I1) * B * sepC I1 I2 I3 B := by
  rcases gaps h1 h12 h23 with ⟨_, hI3, _, h32, h31⟩
  apply eq_of_sq_eq_nonneg
  · rw [mul_pow, sepA_sq h1 h12 h23 hB, sepK_sq h1 h12 h23 hB]
    have hr :
        (((I3 - I2) / I1) * B * sepC I1 I2 I3 B) ^ 2 =
          (I3 - I2) ^ 2 / I1 ^ 2 * B ^ 2 * sepC I1 I2 I3 B ^ 2 := by ring
    rw [hr, sepC_sq h1 h12 h23 hB]
    field_simp [h1.ne', hI3.ne', h31.ne']
  · exact mul_nonneg (sepA_nonneg h1 h12 h23 hB) (sepK_nonneg h1 h12 h23 hB)
  · exact mul_nonneg (mul_nonneg (div_nonneg h32.le h1.le) hB.le) (sepC_nonneg h1 h12 h23 hB)

theorem coeff_ck (h1 : 0 < I1) (h12 : I1 < I2) (h23 : I2 < I3) (hB : 0 < B) :
    sepC I1 I2 I3 B * sepK I1 I2 I3 B =
      ((I2 - I1) / I3) * sepA I1 I2 I3 B * B := by
  rcases gaps h1 h12 h23 with ⟨_, hI3, h21, _, h31⟩
  apply eq_of_sq_eq_nonneg
  · rw [mul_pow, sepC_sq h1 h12 h23 hB, sepK_sq h1 h12 h23 hB]
    have hr :
        (((I2 - I1) / I3) * sepA I1 I2 I3 B * B) ^ 2 =
          (I2 - I1) ^ 2 / I3 ^ 2 * sepA I1 I2 I3 B ^ 2 * B ^ 2 := by ring
    rw [hr, sepA_sq h1 h12 h23 hB]
    field_simp [h1.ne', hI3.ne', h31.ne']
  · exact mul_nonneg (sepC_nonneg h1 h12 h23 hB) (sepK_nonneg h1 h12 h23 hB)
  · exact mul_nonneg (mul_nonneg (div_nonneg h21.le hI3.le) (sepA_nonneg h1 h12 h23 hB)) hB.le

theorem coeff_bk (h1 : 0 < I1) (h12 : I1 < I2) (h23 : I2 < I3) (hB : 0 < B) :
    B * sepK I1 I2 I3 B = ((I3 - I1) / I2) * sepA I1 I2 I3 B * sepC I1 I2 I3 B := by
  rcases gaps h1 h12 h23 with ⟨hI2, hI3, _, _, h31⟩
  apply eq_of_sq_eq_nonneg
  · rw [mul_pow, sepK_sq h1 h12 h23 hB]
    have hr :
        (((I3 - I1) / I2) * sepA I1 I2 I3 B * sepC I1 I2 I3 B) ^ 2 =
          (I3 - I1) ^ 2 / I2 ^ 2 * sepA I1 I2 I3 B ^ 2 * sepC I1 I2 I3 B ^ 2 := by ring
    rw [hr, sepA_sq h1 h12 h23 hB, sepC_sq h1 h12 h23 hB]
    field_simp [h1.ne', hI2.ne', hI3.ne', h31.ne']
  · exact mul_nonneg hB.le (sepK_nonneg h1 h12 h23 hB)
  · exact mul_nonneg (mul_nonneg (div_nonneg h31.le hI2.le) (sepA_nonneg h1 h12 h23 hB))
      (sepC_nonneg h1 h12 h23 hB)

theorem tanh_sq_add_sech_sq (t : ℝ) : Real.tanh t ^ 2 + sech t ^ 2 = 1 := by
  rw [Real.tanh_eq_sinh_div_cosh, sech]
  field_simp [(Real.cosh_pos t).ne']
  linarith [Real.cosh_sq_sub_sinh_sq t]

theorem hasDerivAt_sech (t : ℝ) : HasDerivAt sech (-Real.tanh t * sech t) t := by
  have h := (Real.hasDerivAt_cosh t).inv (Real.cosh_pos t).ne'
  have hfun : sech =ᶠ[nhds t] Real.cosh⁻¹ :=
    Filter.Eventually.of_forall fun s => by simp [sech]
  refine (h.congr_deriv ?_).congr_of_eventuallyEq hfun
  rw [Real.tanh_eq_sinh_div_cosh, sech]
  field_simp [(Real.cosh_pos t).ne']

theorem hasDerivAt_tanh (t : ℝ) : HasDerivAt Real.tanh (sech t ^ 2) t := by
  have h := (Real.hasDerivAt_sinh t).div (Real.hasDerivAt_cosh t) (Real.cosh_pos t).ne'
  have hfun : Real.tanh =ᶠ[nhds t] (Real.sinh / Real.cosh) :=
    Filter.Eventually.of_forall fun s => by
      rw [Pi.div_apply, Real.tanh_eq_sinh_div_cosh]
  have hder :
      (Real.cosh t * Real.cosh t - Real.sinh t * Real.sinh t) / Real.cosh t ^ 2 = sech t ^ 2 := by
    have hnum : Real.cosh t * Real.cosh t - Real.sinh t * Real.sinh t = 1 := by
      linear_combination Real.cosh_sq_sub_sinh_sq t
    rw [hnum, sech]
    field_simp [(Real.cosh_pos t).ne']
  exact (h.congr_deriv hder).congr_of_eventuallyEq hfun

theorem hasDerivAt_sech_mul (k t : ℝ) :
    HasDerivAt (fun s => sech (k * s)) (-k * Real.tanh (k * t) * sech (k * t)) t := by
  have hinner : HasDerivAt (fun s => k * s) k t := by
    simpa using (hasDerivAt_id t).const_mul k
  have h := (hasDerivAt_sech (k * t)).comp t hinner
  have hderiv :
      -Real.tanh (k * t) * sech (k * t) * k = -k * Real.tanh (k * t) * sech (k * t) := by ring
  exact (h.congr_deriv hderiv).congr_of_eventuallyEq <| Filter.Eventually.of_forall fun s => by
    simp

theorem hasDerivAt_tanh_mul (k t : ℝ) :
    HasDerivAt (fun s => Real.tanh (k * s)) (k * sech (k * t) ^ 2) t := by
  have hinner : HasDerivAt (fun s => k * s) k t := by
    simpa using (hasDerivAt_id t).const_mul k
  have h := (hasDerivAt_tanh (k * t)).comp t hinner
  have hderiv : sech (k * t) ^ 2 * k = k * sech (k * t) ^ 2 := by ring
  exact (h.congr_deriv hderiv).congr_of_eventuallyEq <| Filter.Eventually.of_forall fun s => by
    simp

theorem hasDerivAt_omega1 (h1 : 0 < I1) (h12 : I1 < I2) (h23 : I2 < I3) (hB : 0 < B) (t : ℝ) :
    HasDerivAt (omega1 I1 I2 I3 B)
      (((I2 - I3) / I1) * omega2 I1 I2 I3 B t * omega3 I1 I2 I3 B t) t := by
  have hsech := hasDerivAt_sech_mul (sepK I1 I2 I3 B) t
  have hmul := hsech.const_mul (sepA I1 I2 I3 B)
  have hcoeff := coeff_ak h1 h12 h23 hB
  refine (hmul.congr_deriv ?_).congr_of_eventuallyEq ?_
  · simp only [omega2, omega3]
    have :
        sepA I1 I2 I3 B * (-sepK I1 I2 I3 B * Real.tanh (sepK I1 I2 I3 B * t) *
            sech (sepK I1 I2 I3 B * t)) =
          ((I2 - I3) / I1) * (B * Real.tanh (sepK I1 I2 I3 B * t)) *
            (sepC I1 I2 I3 B * sech (sepK I1 I2 I3 B * t)) := by
      have hneg : -sepA I1 I2 I3 B * sepK I1 I2 I3 B =
          ((I2 - I3) / I1) * B * sepC I1 I2 I3 B := by
        linear_combination -hcoeff
      linear_combination hneg * Real.tanh (sepK I1 I2 I3 B * t) *
        sech (sepK I1 I2 I3 B * t)
    simpa [mul_assoc, mul_left_comm, mul_comm] using this
  · refine Filter.Eventually.of_forall ?_
    intro s
    simp [omega1]

theorem hasDerivAt_omega2 (h1 : 0 < I1) (h12 : I1 < I2) (h23 : I2 < I3) (hB : 0 < B) (t : ℝ) :
    HasDerivAt (omega2 I1 I2 I3 B)
      (((I3 - I1) / I2) * omega3 I1 I2 I3 B t * omega1 I1 I2 I3 B t) t := by
  have htanh := hasDerivAt_tanh_mul (sepK I1 I2 I3 B) t
  have hmul := htanh.const_mul B
  have hcoeff := coeff_bk h1 h12 h23 hB
  refine (hmul.congr_deriv ?_).congr_of_eventuallyEq ?_
  · simp only [omega1, omega3]
    have :
        B * (sepK I1 I2 I3 B * sech (sepK I1 I2 I3 B * t) ^ 2) =
          ((I3 - I1) / I2) * (sepC I1 I2 I3 B * sech (sepK I1 I2 I3 B * t)) *
            (sepA I1 I2 I3 B * sech (sepK I1 I2 I3 B * t)) := by
      linear_combination hcoeff * sech (sepK I1 I2 I3 B * t) ^ 2
    simpa [mul_assoc, mul_left_comm, mul_comm, pow_two] using this
  · refine Filter.Eventually.of_forall ?_
    intro s
    simp [omega2]

theorem hasDerivAt_omega3 (h1 : 0 < I1) (h12 : I1 < I2) (h23 : I2 < I3) (hB : 0 < B) (t : ℝ) :
    HasDerivAt (omega3 I1 I2 I3 B)
      (((I1 - I2) / I3) * omega1 I1 I2 I3 B t * omega2 I1 I2 I3 B t) t := by
  have hsech := hasDerivAt_sech_mul (sepK I1 I2 I3 B) t
  have hmul := hsech.const_mul (sepC I1 I2 I3 B)
  have hcoeff := coeff_ck h1 h12 h23 hB
  refine (hmul.congr_deriv ?_).congr_of_eventuallyEq ?_
  · simp only [omega1, omega2]
    have :
        sepC I1 I2 I3 B * (-sepK I1 I2 I3 B * Real.tanh (sepK I1 I2 I3 B * t) *
            sech (sepK I1 I2 I3 B * t)) =
          ((I1 - I2) / I3) * (sepA I1 I2 I3 B * sech (sepK I1 I2 I3 B * t)) *
            (B * Real.tanh (sepK I1 I2 I3 B * t)) := by
      have hneg : -sepC I1 I2 I3 B * sepK I1 I2 I3 B =
          ((I1 - I2) / I3) * sepA I1 I2 I3 B * B := by
        linear_combination -hcoeff
      linear_combination hneg * sech (sepK I1 I2 I3 B * t) *
        Real.tanh (sepK I1 I2 I3 B * t)
    simpa [mul_assoc, mul_left_comm, mul_comm] using this
  · refine Filter.Eventually.of_forall ?_
    intro s
    simp [omega3]

theorem racketEnergy_const (h1 : 0 < I1) (h12 : I1 < I2) (h23 : I2 < I3) (hB : 0 < B) (t : ℝ) :
    racketEnergy I1 I2 I3 B t = (1 / 2) * I2 * B ^ 2 := by
  have hamp := amp_energy h1 h12 h23 hB
  have ht : Real.tanh (sepK I1 I2 I3 B * t) ^ 2 = 1 - sech (sepK I1 I2 I3 B * t) ^ 2 := by
    linarith [tanh_sq_add_sech_sq (sepK I1 I2 I3 B * t)]
  unfold racketEnergy omega1 omega2 omega3
  rw [show (B * Real.tanh (sepK I1 I2 I3 B * t)) ^ 2 =
      B ^ 2 * Real.tanh (sepK I1 I2 I3 B * t) ^ 2 by ring, ht]
  have hsum :
      I1 * (sepA I1 I2 I3 B * sech (sepK I1 I2 I3 B * t)) ^ 2 +
          I2 * (B ^ 2 * (1 - sech (sepK I1 I2 I3 B * t) ^ 2)) +
          I3 * (sepC I1 I2 I3 B * sech (sepK I1 I2 I3 B * t)) ^ 2 =
        I2 * B ^ 2 := by
    have :
        I1 * (sepA I1 I2 I3 B * sech (sepK I1 I2 I3 B * t)) ^ 2 +
            I2 * (B ^ 2 * (1 - sech (sepK I1 I2 I3 B * t) ^ 2)) +
            I3 * (sepC I1 I2 I3 B * sech (sepK I1 I2 I3 B * t)) ^ 2 =
          (I1 * sepA I1 I2 I3 B ^ 2 + I3 * sepC I1 I2 I3 B ^ 2) *
              sech (sepK I1 I2 I3 B * t) ^ 2 +
            I2 * B ^ 2 * (1 - sech (sepK I1 I2 I3 B * t) ^ 2) := by ring
    rw [this, hamp]
    ring
  rw [hsum]
  ring

theorem racketLsq_const (h1 : 0 < I1) (h12 : I1 < I2) (h23 : I2 < I3) (hB : 0 < B) (t : ℝ) :
    racketLsq I1 I2 I3 B t = I2 ^ 2 * B ^ 2 := by
  have hamp := amp_momentum h1 h12 h23 hB
  have ht : Real.tanh (sepK I1 I2 I3 B * t) ^ 2 = 1 - sech (sepK I1 I2 I3 B * t) ^ 2 := by
    linarith [tanh_sq_add_sech_sq (sepK I1 I2 I3 B * t)]
  unfold racketLsq omega1 omega2 omega3
  rw [show (B * Real.tanh (sepK I1 I2 I3 B * t)) ^ 2 =
      B ^ 2 * Real.tanh (sepK I1 I2 I3 B * t) ^ 2 by ring, ht]
  have hsum :
      I1 ^ 2 * (sepA I1 I2 I3 B * sech (sepK I1 I2 I3 B * t)) ^ 2 +
          I2 ^ 2 * (B ^ 2 * (1 - sech (sepK I1 I2 I3 B * t) ^ 2)) +
          I3 ^ 2 * (sepC I1 I2 I3 B * sech (sepK I1 I2 I3 B * t)) ^ 2 =
        I2 ^ 2 * B ^ 2 := by
    have :
        I1 ^ 2 * (sepA I1 I2 I3 B * sech (sepK I1 I2 I3 B * t)) ^ 2 +
            I2 ^ 2 * (B ^ 2 * (1 - sech (sepK I1 I2 I3 B * t) ^ 2)) +
            I3 ^ 2 * (sepC I1 I2 I3 B * sech (sepK I1 I2 I3 B * t)) ^ 2 =
          (I1 ^ 2 * sepA I1 I2 I3 B ^ 2 + I3 ^ 2 * sepC I1 I2 I3 B ^ 2) *
              sech (sepK I1 I2 I3 B * t) ^ 2 +
            I2 ^ 2 * B ^ 2 * (1 - sech (sepK I1 I2 I3 B * t) ^ 2) := by ring
    rw [this, hamp]
    ring
  exact hsum

theorem racket_critical (h1 : 0 < I1) (h12 : I1 < I2) (h23 : I2 < I3) (hB : 0 < B) (t : ℝ) :
    racketLsq I1 I2 I3 B t = 2 * racketEnergy I1 I2 I3 B t * I2 := by
  rw [racketLsq_const h1 h12 h23 hB t, racketEnergy_const h1 h12 h23 hB t]
  ring

theorem omega2_eq_zero_iff (h1 : 0 < I1) (h12 : I1 < I2) (h23 : I2 < I3) (hB : 0 < B) (t : ℝ) :
    omega2 I1 I2 I3 B t = 0 ↔ t = 0 := by
  have hk := sepK_pos h1 h12 h23 hB
  unfold omega2
  constructor
  · intro h
    have htan : Real.tanh (sepK I1 I2 I3 B * t) = 0 :=
      (mul_eq_zero.mp h).resolve_left hB.ne'
    have hkt : sepK I1 I2 I3 B * t = 0 :=
      Real.tanh_injective (by simpa [Real.tanh_zero] using htan)
    exact (mul_eq_zero.mp hkt).resolve_left hk.ne'
  · intro ht
    simp [ht, Real.tanh_zero]

private theorem tanh_pos_of_pos {x : ℝ} (hx : 0 < x) : 0 < Real.tanh x := by
  rw [Real.tanh_eq_sinh_div_cosh]
  exact div_pos (Real.sinh_pos_iff.mpr hx) (Real.cosh_pos x)

private theorem tanh_neg_of_neg {x : ℝ} (hx : x < 0) : Real.tanh x < 0 := by
  have h : 0 < Real.tanh (-x) := tanh_pos_of_pos (neg_pos.mpr hx)
  rw [Real.tanh_neg] at h
  linarith

theorem omega2_neg_of_neg (h1 : 0 < I1) (h12 : I1 < I2) (h23 : I2 < I3) (hB : 0 < B) {t : ℝ}
    (ht : t < 0) : omega2 I1 I2 I3 B t < 0 := by
  have hk := sepK_pos h1 h12 h23 hB
  unfold omega2
  have hkt : sepK I1 I2 I3 B * t < 0 := mul_neg_of_pos_of_neg hk ht
  exact mul_neg_of_pos_of_neg hB (tanh_neg_of_neg hkt)

theorem omega2_pos_of_pos (h1 : 0 < I1) (h12 : I1 < I2) (h23 : I2 < I3) (hB : 0 < B) {t : ℝ}
    (ht : 0 < t) : 0 < omega2 I1 I2 I3 B t := by
  have hk := sepK_pos h1 h12 h23 hB
  unfold omega2
  have hkt : 0 < sepK I1 I2 I3 B * t := mul_pos hk ht
  exact mul_pos hB (tanh_pos_of_pos hkt)

theorem rateMid_zero_of_left {I1 I2 I3 Ω : ℝ} (h : I1 = I2) : rateMid I1 I2 I3 Ω = 0 := by
  simp [rateMid, h, sub_self]

theorem rateMid_zero_of_right {I1 I2 I3 Ω : ℝ} (h : I2 = I3) : rateMid I1 I2 I3 Ω = 0 := by
  simp [rateMid, h, sub_self]

theorem rateMid_pos (h1 : 0 < I1) (h12 : I1 < I2) (h23 : I2 < I3) {Ω : ℝ} (hΩ : Ω ≠ 0) :
    0 < rateMid I1 I2 I3 Ω := by
  rcases gaps h1 h12 h23 with ⟨_, hI3, h21, h32, _⟩
  exact mul_pos (div_pos (mul_pos h32 h21) (mul_pos h1 hI3)) (sq_pos_of_ne_zero hΩ)

theorem rateSmall_neg (h1 : 0 < I1) (h12 : I1 < I2) (h23 : I2 < I3) {Ω : ℝ} (hΩ : Ω ≠ 0) :
    rateSmall I1 I2 I3 Ω < 0 := by
  rcases gaps h1 h12 h23 with ⟨hI2, hI3, h21, _, h31⟩
  have hpos : 0 < ((I3 - I1) * (I2 - I1) / (I2 * I3)) * Ω ^ 2 :=
    mul_pos (div_pos (mul_pos h31 h21) (mul_pos hI2 hI3)) (sq_pos_of_ne_zero hΩ)
  unfold rateSmall
  linarith

theorem rateLarge_neg (h1 : 0 < I1) (h12 : I1 < I2) (h23 : I2 < I3) {Ω : ℝ} (hΩ : Ω ≠ 0) :
    rateLarge I1 I2 I3 Ω < 0 := by
  rcases gaps h1 h12 h23 with ⟨hI2, _, _, _, h31⟩
  have hneg : I2 - I3 < 0 := by linarith
  have hnum : (I2 - I3) * (I3 - I1) < 0 := mul_neg_of_neg_of_pos hneg h31
  have hfrac : (I2 - I3) * (I3 - I1) / (I1 * I2) < 0 :=
    div_neg_of_neg_of_pos hnum (mul_pos h1 hI2)
  unfold rateLarge
  exact mul_neg_of_neg_of_pos hfrac (sq_pos_of_ne_zero hΩ)

theorem sepK_sq_eq_rateMid (h1 : 0 < I1) (h12 : I1 < I2) (h23 : I2 < I3) (hB : 0 < B) :
    sepK I1 I2 I3 B ^ 2 = rateMid I1 I2 I3 B := by
  rw [sepK_sq h1 h12 h23 hB, rateMid]
  ring

theorem mid_eigenvalue (h1 : 0 < I1) (h12 : I1 < I2) (h23 : I2 < I3) {Ω : ℝ} (hΩ : Ω ≠ 0) :
    0 < Real.sqrt (rateMid I1 I2 I3 Ω) ∧
      Real.sqrt (rateMid I1 I2 I3 Ω) ^ 2 = rateMid I1 I2 I3 Ω := by
  have h := rateMid_pos h1 h12 h23 hΩ
  exact ⟨Real.sqrt_pos.mpr h, Real.sq_sqrt h.le⟩

theorem small_no_positive_eigenvalue (h1 : 0 < I1) (h12 : I1 < I2) (h23 : I2 < I3) {Ω : ℝ}
    (hΩ : Ω ≠ 0) : ∀ lam : ℝ, 0 < lam → lam ^ 2 ≠ rateSmall I1 I2 I3 Ω := by
  intro lam hlam hEq
  have hneg := rateSmall_neg h1 h12 h23 hΩ
  have hpos : 0 < lam ^ 2 := sq_pos_of_pos hlam
  linarith

theorem large_no_positive_eigenvalue (h1 : 0 < I1) (h12 : I1 < I2) (h23 : I2 < I3) {Ω : ℝ}
    (hΩ : Ω ≠ 0) : ∀ lam : ℝ, 0 < lam → lam ^ 2 ≠ rateLarge I1 I2 I3 Ω := by
  intro lam hlam hEq
  have hneg := rateLarge_neg h1 h12 h23 hΩ
  have hpos : 0 < lam ^ 2 := sq_pos_of_pos hlam
  linarith

theorem tanh_half_log_three : Real.tanh (Real.log 3 / 2) = 1 / 2 := by
  have hs2 : Real.exp (Real.log 3 / 2) ^ 2 = 3 := by
    rw [pow_two, ← Real.exp_add, add_halves, Real.exp_log (by norm_num)]
  have hs : Real.exp (Real.log 3 / 2) = Real.sqrt 3 := by
    apply eq_of_sq_eq_nonneg
    · rw [hs2]
      exact (Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)).symm
    · exact (Real.exp_pos _).le
    · exact Real.sqrt_nonneg _
  rw [Real.tanh_eq, hs, Real.exp_neg, hs]
  have hsq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  field_simp [Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 3)]
  rw [hsq]
  norm_num

theorem waiting_gt_crossing {k ε : ℝ} (hk : 0 < k) (hε : 0 < ε) (hεu : ε < 1 / 6) :
    crossingTime k < waitingTime k ε := by
  unfold crossingTime waitingTime
  have hden : 0 < 2 * ε := by linarith
  have hcmp : (3 : ℝ) < 1 / (2 * ε) := by
    rw [lt_div_iff₀ hden]
    linarith
  have hlog := Real.log_lt_log (by norm_num : (0 : ℝ) < 3) hcmp
  have hk' : 0 < 1 / k := one_div_pos.mpr hk
  simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using mul_lt_mul_of_pos_left hlog hk'

/-- The wait exceeds every bound as the residual shrinks. -/
theorem waiting_unbounded {k : ℝ} (hk : 0 < k) (N : ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 / 6 ∧ N < waitingTime k ε := by
  by_cases hN : N < Real.log 6 / k
  · refine ⟨1 / 12, by norm_num, by norm_num, ?_⟩
    have hw : waitingTime k (1 / 12) = Real.log 6 / k := by
      unfold waitingTime
      have harg : (1 : ℝ) / (2 * (1 / 12)) = 6 := by norm_num
      rw [harg]
      field_simp [hk.ne']
    linarith
  · set ε : ℝ := 1 / (2 * Real.exp (k * (N + 1))) with hεdef
    have hexp : 0 < Real.exp (k * (N + 1)) := Real.exp_pos _
    have hε : 0 < ε := by
      rw [hεdef]
      exact one_div_pos.mpr (mul_pos (by norm_num) hexp)
    have hlow : Real.log 6 / k ≤ N := le_of_not_gt hN
    have hkN : Real.log 6 ≤ k * N := by
      calc
        Real.log 6 = k * (Real.log 6 / k) := by field_simp [hk.ne']
        _ ≤ k * N := mul_le_mul_of_nonneg_left hlow hk.le
    have hstep : Real.log 3 < k * (N + 1) := by
      have h36 : Real.log 3 < Real.log 6 := Real.log_lt_log (by norm_num) (by norm_num)
      linarith
    have hεu : ε < 1 / 6 := by
      rw [hεdef, div_lt_div_iff₀ (mul_pos (by norm_num) hexp) (by norm_num : (0 : ℝ) < 6)]
      have h3 : (3 : ℝ) < Real.exp (k * (N + 1)) := by
        rw [← Real.exp_log (by norm_num : (0 : ℝ) < 3)]
        exact (Real.exp_strictMono hstep)
      linarith
    have hw : waitingTime k ε = N + 1 := by
      unfold waitingTime
      rw [hεdef]
      have harg : (1 : ℝ) / (2 * (1 / (2 * Real.exp (k * (N + 1))))) =
          Real.exp (k * (N + 1)) := by field_simp [hexp.ne']
      rw [harg, Real.log_exp]
      field_simp [hk.ne']
    exact ⟨ε, hε, hεu, by linarith [hw]⟩

end DstDiophantine.Gravity.RacketFlip
