import DstDiophantine.Gravity.CliffordParallel
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Chart rotation of a three-sphere aggregate

Particles are points of the three-sphere. The force between two of them
follows the great circle, and the laboratory reads the sphere through the
azimuthal equidistant chart `logChart`. A pole-fixing rotation or reflection of
the sphere is the same rotation or reflection of that chart. A common left
translation leaves every relative rotor fixed, and its chart velocity at a
point on the second axis splits into a term along the generator and the cross
product of the generator with the chart point.

The chart torque of an aggregate is the sum of the pairwise `chordMoment`s.
On the axis intercepts `(±a,0,0)`, `(0,±b,0)`, `(0,0,±c)` each coordinate
plane is a mirror pair, so every component vanishes. The second moments on
those axes are `2(b²+c²)`, `2(a²+c²)`, and `2(a²+b²)`. For `0 < a < b < c`
they stand in that order, and two of them agree exactly when two of the
lengths agree. A body on the first axis, with a partner at the same chart
distance, has moment zero while the partner lies on the axis and a positive
moment once the partner is moved off the axis. The mirror partner cancels
that moment; removing the mirror leaves it.

## Not claimed

* A floating-point many-body trajectory.
* A Boltzmann weight on `L²`, or a frequency of reversals drawn from one.
* A value of `a₀`, or an identification of a galaxy with this aggregate.
-/

namespace DstDiophantine.Gravity.ChartRotation

open CliffordParallel Real RelationalPosition SlerpTorque

/-! ### Pole-fixing maps commute with the chart -/

/-- Reflection through the chart plane of the first two axes. -/
def reflectZ (n : V3) : V3
  | 0 => n 0
  | 1 => n 1
  | 2 => -n 2

/-- The same reflection on the ambient `ℝ × ℝ³`, fixing the real axis. -/
def reflectZ4 (p : V4) : V4
  | 0 => p 0
  | 1 => p 1
  | 2 => p 2
  | 3 => -p 3

/-- Rotation about the chart's third axis. -/
noncomputable def rotateZ (θ : ℝ) (n : V3) : V3
  | 0 => Real.cos θ * n 0 - Real.sin θ * n 1
  | 1 => Real.sin θ * n 0 + Real.cos θ * n 1
  | 2 => n 2

/-- The same rotation on the ambient space, fixing the real axis. -/
noncomputable def rotateZ4 (θ : ℝ) (p : V4) : V4
  | 0 => p 0
  | 1 => Real.cos θ * p 1 - Real.sin θ * p 2
  | 2 => Real.sin θ * p 1 + Real.cos θ * p 2
  | 3 => p 3

theorem reflectZ_unit {n : V3} (hn : dot3 n n = 1) : dot3 (reflectZ n) (reflectZ n) = 1 := by
  simp only [dot3, reflectZ]
  have hn' : n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2 = 1 := by
    simpa [dot3, pow_two] using hn
  linear_combination hn'

theorem rotateZ_unit {θ : ℝ} {n : V3} (hn : dot3 n n = 1) :
    dot3 (rotateZ θ n) (rotateZ θ n) = 1 := by
  simp only [dot3, rotateZ]
  have htrig := Real.sin_sq_add_cos_sq θ
  have hsq : n 0 * n 0 + n 1 * n 1 + n 2 * n 2 = 1 := by
    simpa [dot3, pow_two] using hn
  calc
      (Real.cos θ * n 0 - Real.sin θ * n 1) * (Real.cos θ * n 0 - Real.sin θ * n 1) +
          (Real.sin θ * n 0 + Real.cos θ * n 1) * (Real.sin θ * n 0 + Real.cos θ * n 1) +
          n 2 * n 2 =
        (Real.cos θ ^ 2 + Real.sin θ ^ 2) * (n 0 * n 0 + n 1 * n 1) + n 2 * n 2 := by ring
    _ = n 0 * n 0 + n 1 * n 1 + n 2 * n 2 := by
        rw [show Real.cos θ ^ 2 + Real.sin θ ^ 2 = 1 by rw [add_comm]; exact htrig]
        ring
    _ = 1 := hsq

theorem reflectZ4_fixes_real (p : V4) : reflectZ4 p 0 = p 0 := by
  simp [reflectZ4]

theorem rotateZ4_fixes_real (θ : ℝ) (p : V4) : rotateZ4 θ p 0 = p 0 := by
  simp [rotateZ4]

theorem reflectZ4_lift (χ : ℝ) (n : V3) : reflectZ4 (lift χ n) = lift χ (reflectZ n) := by
  funext i
  fin_cases i <;> simp [reflectZ4, reflectZ, lift]

theorem rotateZ4_lift (θ χ : ℝ) (n : V3) : rotateZ4 θ (lift χ n) = lift χ (rotateZ θ n) := by
  funext i
  fin_cases i <;> simp [rotateZ4, rotateZ, lift] <;> ring

theorem reflectZ4_preserves_norm (p : V4) : dot4 (reflectZ4 p) (reflectZ4 p) = dot4 p p := by
  simp only [dot4, reflectZ4]
  ring

theorem rotateZ4_preserves_norm (θ : ℝ) (p : V4) :
    dot4 (rotateZ4 θ p) (rotateZ4 θ p) = dot4 p p := by
  simp only [dot4, rotateZ4]
  have htrig := Real.sin_sq_add_cos_sq θ
  calc
      p 0 * p 0 + (Real.cos θ * p 1 - Real.sin θ * p 2) * (Real.cos θ * p 1 - Real.sin θ * p 2) +
          (Real.sin θ * p 1 + Real.cos θ * p 2) * (Real.sin θ * p 1 + Real.cos θ * p 2) +
          p 3 * p 3 =
        p 0 * p 0 + (Real.cos θ ^ 2 + Real.sin θ ^ 2) * (p 1 * p 1 + p 2 * p 2) + p 3 * p 3 := by
          ring
    _ = p 0 * p 0 + p 1 * p 1 + p 2 * p 2 + p 3 * p 3 := by
        rw [show Real.cos θ ^ 2 + Real.sin θ ^ 2 = 1 by rw [add_comm]; exact htrig]
        ring
    _ = dot4 p p := by simp [dot4]

theorem logChart_reflectZ {χ : ℝ} {n : V3} (hn : dot3 n n = 1) (hχ : 0 < χ) (hχu : χ < Real.pi) :
    logChart (lift χ (reflectZ n)) = reflectZ (logChart (lift χ n)) := by
  rw [logChart_lift hχ hχu (reflectZ_unit hn), logChart_lift hχ hχu hn]
  funext i
  fin_cases i <;> simp [reflectZ]

theorem logChart_rotateZ {θ χ : ℝ} {n : V3} (hn : dot3 n n = 1) (hχ : 0 < χ)
    (hχu : χ < Real.pi) :
    logChart (lift χ (rotateZ θ n)) = rotateZ θ (logChart (lift χ n)) := by
  rw [logChart_lift hχ hχu (rotateZ_unit hn), logChart_lift hχ hχu hn]
  funext i
  fin_cases i <;> simp [rotateZ] <;> ring

/-! ### Left translation: relative rotors fixed, chart velocity a cross product -/

/-- Unit direction of the second chart axis. -/
def axisJ : V3
  | 0 => 0
  | 1 => 1
  | 2 => 0

/-- Unit generator of the left translation, the first chart axis. -/
def generatorI : V3
  | 0 => 1
  | 1 => 0
  | 2 => 0

theorem axisJ_unit : dot3 axisJ axisJ = 1 := by
  simp [dot3, axisJ]

/-- Real part of `hopfI(t)` times the lift of `axisJ`. -/
noncomputable def movedRe (χ t : ℝ) : ℝ :=
  Real.cos t * Real.cos χ

noncomputable def movedI (χ t : ℝ) : ℝ :=
  Real.sin t * Real.cos χ

noncomputable def movedJ (χ t : ℝ) : ℝ :=
  Real.cos t * Real.sin χ

noncomputable def movedK (χ t : ℝ) : ℝ :=
  Real.sin t * Real.sin χ

theorem hopf_mul_axisJ (χ t : ℝ) :
    (hopfI t).val * liftQuat χ axisJ =
      ⟨movedRe χ t, movedI χ t, movedJ χ t, movedK χ t⟩ := by
  ext
  · simp [hopfI, liftQuat, axisJ, movedRe]
  · simp [hopfI, liftQuat, axisJ, movedI]
  · simp [hopfI, liftQuat, axisJ, movedJ]
  · simp [hopfI, liftQuat, axisJ, movedK]

theorem toChart_left (χ t : ℝ) :
    toChart ((hopfI t).val * liftQuat χ axisJ) = fun i =>
      match i with
      | 0 => movedRe χ t
      | 1 => movedI χ t
      | 2 => movedJ χ t
      | 3 => movedK χ t := by
  rw [hopf_mul_axisJ]
  funext i
  fin_cases i <;> simp [toChart_apply, movedRe, movedI, movedJ, movedK]

/-- Chart of the left translate of the point at distance `χ` along `axisJ`. -/
noncomputable def leftChart (χ t : ℝ) : V3 :=
  logChart (toChart ((hopfI t).val * liftQuat χ axisJ))

noncomputable def chartFactor (χ t : ℝ) : ℝ :=
  Real.arccos (movedRe χ t) / Real.sqrt (1 - movedRe χ t ^ 2)

noncomputable def chartCoord (χ t : ℝ) : V3
  | 0 => chartFactor χ t * movedI χ t
  | 1 => chartFactor χ t * movedJ χ t
  | 2 => chartFactor χ t * movedK χ t

theorem leftChart_eq_coord (χ t : ℝ) : leftChart χ t = chartCoord χ t := by
  funext i
  simp only [leftChart, logChart, chartCoord, chartFactor, toChart_left]
  fin_cases i <;> simp [chartIdx]

theorem common_left_preserves_relative (t : ℝ) (a b : S3) :
    relative (hopfI t * a) (hopfI t * b) = relative a b :=
  relative_left (hopfI t) a b

private theorem hasDerivAt_movedRe (χ t : ℝ) :
    HasDerivAt (movedRe χ) (-(Real.sin t) * Real.cos χ) t := by
  unfold movedRe
  simpa using ((Real.hasDerivAt_cos t).mul_const (Real.cos χ))

private theorem hasDerivAt_movedRe_zero (χ : ℝ) : HasDerivAt (movedRe χ) 0 0 := by
  simpa [Real.sin_zero] using hasDerivAt_movedRe χ 0

private theorem cos_ne_one_of_mem_Ioo {χ : ℝ} (hχ : 0 < χ) (hχu : χ < Real.pi) :
    Real.cos χ ≠ 1 := by
  intro h
  have := Real.arccos_cos hχ.le hχu.le
  rw [h, Real.arccos_one] at this
  exact hχ.ne this

private theorem cos_ne_neg_one_of_mem_Ioo {χ : ℝ} (hχ : 0 < χ) (hχu : χ < Real.pi) :
    Real.cos χ ≠ -1 := by
  intro h
  have := Real.arccos_cos hχ.le hχu.le
  rw [h, Real.arccos_neg_one] at this
  exact hχu.ne this.symm

private theorem one_sub_cos_sq (χ : ℝ) : 1 - Real.cos χ ^ 2 = Real.sin χ ^ 2 := by
  linarith [Real.sin_sq_add_cos_sq χ]

private theorem hasDerivAt_radius_zero {χ : ℝ} (hs : Real.sin χ ≠ 0) :
    HasDerivAt (fun t => Real.sqrt (1 - movedRe χ t ^ 2)) 0 0 := by
  have hu := hasDerivAt_movedRe_zero χ
  have hsqPow := hu.pow 2
  have hzero : (2 : ℝ) * movedRe χ 0 ^ (2 - 1) * 0 = 0 := by ring
  have hsq : HasDerivAt (fun t => movedRe χ t ^ 2) 0 0 :=
    (hsqPow.congr_deriv hzero).congr_of_eventuallyEq <| Filter.Eventually.of_forall fun t => by
      simp [Pi.pow_apply]
  have hsub := (hasDerivAt_const 0 (1 : ℝ)).sub hsq
  have hinside : HasDerivAt (fun t => 1 - movedRe χ t ^ 2) 0 0 := by
    refine (hsub.congr_deriv (sub_self (0 : ℝ))).congr_of_eventuallyEq ?_
    refine Filter.Eventually.of_forall ?_
    intro t
    change 1 - movedRe χ t ^ 2 = ((fun _ : ℝ => (1 : ℝ)) - fun s => movedRe χ s ^ 2) t
    rw [Pi.sub_apply]
  have hne : 1 - movedRe χ 0 ^ 2 ≠ 0 := by
    have hre : movedRe χ 0 = Real.cos χ := by simp [movedRe, Real.cos_zero]
    rw [hre, one_sub_cos_sq]
    exact pow_ne_zero 2 hs
  have hsqrt := hinside.sqrt hne
  have hderiv : 0 / (2 * Real.sqrt (1 - movedRe χ 0 ^ 2)) = 0 := by simp
  exact (hsqrt.congr_deriv hderiv).congr_of_eventuallyEq <| Filter.Eventually.of_forall fun _ => rfl

private theorem hasDerivAt_theta_zero {χ : ℝ} (hχ : 0 < χ) (hχu : χ < Real.pi) :
    HasDerivAt (fun t => Real.arccos (movedRe χ t)) 0 0 := by
  have hre : movedRe χ 0 = Real.cos χ := by simp [movedRe, Real.cos_zero]
  have harc : HasDerivAt Real.arccos (-(1 / Real.sqrt (1 - movedRe χ 0 ^ 2))) (movedRe χ 0) := by
    simpa [hre] using
      Real.hasDerivAt_arccos (cos_ne_neg_one_of_mem_Ioo hχ hχu) (cos_ne_one_of_mem_Ioo hχ hχu)
  have hcomp := harc.comp 0 (hasDerivAt_movedRe_zero χ)
  simpa [Function.comp_def] using hcomp

private theorem sqrt_one_sub_cos_sq {χ : ℝ} (hχ : 0 < χ) (hχu : χ < Real.pi) :
    Real.sqrt (1 - Real.cos χ ^ 2) = Real.sin χ := by
  rw [one_sub_cos_sq, Real.sqrt_sq (Real.sin_pos_of_pos_of_lt_pi hχ hχu).le]

private theorem chartFactor_zero {χ : ℝ} (hχ : 0 < χ) (hχu : χ < Real.pi) :
    chartFactor χ 0 = χ / Real.sin χ := by
  unfold chartFactor movedRe
  rw [Real.cos_zero, one_mul, one_sub_cos_sq, Real.sqrt_sq (Real.sin_pos_of_pos_of_lt_pi hχ hχu).le,
    Real.arccos_cos hχ.le hχu.le]

private theorem hasDerivAt_factor_zero {χ : ℝ} (hχ : 0 < χ) (hχu : χ < Real.pi) :
    HasDerivAt (chartFactor χ) 0 0 := by
  have hs : Real.sin χ ≠ 0 := (Real.sin_pos_of_pos_of_lt_pi hχ hχu).ne'
  have hθ := hasDerivAt_theta_zero hχ hχu
  have hr := hasDerivAt_radius_zero hs
  have hden : Real.sqrt (1 - movedRe χ 0 ^ 2) ≠ 0 := by
    rw [show movedRe χ 0 = Real.cos χ by simp [movedRe, Real.cos_zero],
      sqrt_one_sub_cos_sq hχ hχu]
    exact hs
  have hdiv := hθ.div hr hden
  unfold chartFactor
  convert hdiv using 2
  simp

private theorem hasDerivAt_movedI_zero (χ : ℝ) : HasDerivAt (movedI χ) (Real.cos χ) 0 := by
  unfold movedI
  simpa [Real.cos_zero] using ((Real.hasDerivAt_sin 0).mul_const (Real.cos χ))

private theorem hasDerivAt_movedJ_zero (χ : ℝ) : HasDerivAt (movedJ χ) 0 0 := by
  unfold movedJ
  simpa [Real.sin_zero] using ((Real.hasDerivAt_cos 0).mul_const (Real.sin χ))

private theorem hasDerivAt_movedK_zero (χ : ℝ) : HasDerivAt (movedK χ) (Real.sin χ) 0 := by
  unfold movedK
  simpa [Real.cos_zero] using ((Real.hasDerivAt_sin 0).mul_const (Real.sin χ))

/-- Chart velocity of the common left translation, at the identity instant. -/
noncomputable def leftVelocity (χ : ℝ) : V3
  | 0 => χ * Real.cos χ / Real.sin χ
  | 1 => 0
  | 2 => χ

theorem cross_generator (χ : ℝ) :
    cross3 generatorI (fun i => χ * axisJ i) = fun
      | 0 => 0
      | 1 => 0
      | 2 => χ := by
  funext i
  fin_cases i <;> simp [cross3, generatorI, axisJ]

theorem leftVelocity_split (χ : ℝ) :
    leftVelocity χ 0 = χ * Real.cos χ / Real.sin χ ∧
      leftVelocity χ 1 = cross3 generatorI (fun i => χ * axisJ i) 1 ∧
      leftVelocity χ 2 = cross3 generatorI (fun i => χ * axisJ i) 2 := by
  simp [leftVelocity, cross_generator]

theorem cross_component_ne_zero {χ : ℝ} (hχ : χ ≠ 0) :
    cross3 generatorI (fun i => χ * axisJ i) 2 ≠ 0 := by
  simpa [cross_generator] using hχ

theorem leftVelocity_equator :
    leftVelocity (Real.pi / 2) = cross3 generatorI (fun i => (Real.pi / 2) * axisJ i) := by
  funext i
  fin_cases i <;>
    simp [leftVelocity, cross_generator, Real.cos_pi_div_two, Real.sin_pi_div_two]

theorem hasDerivAt_leftChart_0 {χ : ℝ} (hχ : 0 < χ) (hχu : χ < Real.pi) :
    HasDerivAt (fun t => leftChart χ t 0) (leftVelocity χ 0) 0 := by
  have hmul := (hasDerivAt_factor_zero hχ hχu).mul (hasDerivAt_movedI_zero χ)
  have hpt : HasDerivAt (fun t => chartFactor χ t * movedI χ t) (leftVelocity χ 0) 0 := by
    convert hmul using 2
    simp [movedI, Real.sin_zero, chartFactor_zero hχ hχu, leftVelocity]
    field_simp [(Real.sin_pos_of_pos_of_lt_pi hχ hχu).ne']
  exact hpt.congr_of_eventuallyEq <| Filter.Eventually.of_forall fun t => by
    simp [leftChart_eq_coord, chartCoord]

theorem hasDerivAt_leftChart_1 {χ : ℝ} (hχ : 0 < χ) (hχu : χ < Real.pi) :
    HasDerivAt (fun t => leftChart χ t 1) (leftVelocity χ 1) 0 := by
  have hmul := (hasDerivAt_factor_zero hχ hχu).mul (hasDerivAt_movedJ_zero χ)
  have hpt : HasDerivAt (fun t => chartFactor χ t * movedJ χ t) (leftVelocity χ 1) 0 := by
    convert hmul using 2
    simp [leftVelocity]
  exact hpt.congr_of_eventuallyEq <| Filter.Eventually.of_forall fun t => by
    simp [leftChart_eq_coord, chartCoord]

theorem hasDerivAt_leftChart_2 {χ : ℝ} (hχ : 0 < χ) (hχu : χ < Real.pi) :
    HasDerivAt (fun t => leftChart χ t 2) (leftVelocity χ 2) 0 := by
  have hs : Real.sin χ ≠ 0 := (Real.sin_pos_of_pos_of_lt_pi hχ hχu).ne'
  have hmul := (hasDerivAt_factor_zero hχ hχu).mul (hasDerivAt_movedK_zero χ)
  have hpt : HasDerivAt (fun t => chartFactor χ t * movedK χ t) (leftVelocity χ 2) 0 := by
    convert hmul using 2
    simp [movedK, Real.sin_zero, chartFactor_zero hχ hχu, leftVelocity]
    field_simp [hs]
  exact hpt.congr_of_eventuallyEq <| Filter.Eventually.of_forall fun t => by
    simp [leftChart_eq_coord, chartCoord]

/-! ### The aggregate: inertia and cancelling torque -/

/-- The six axis intercepts. -/
def site (a b c : ℝ) : Fin 6 → V3
  | 0 => fun
    | 0 => a
    | 1 => 0
    | 2 => 0
  | 1 => fun
    | 0 => -a
    | 1 => 0
    | 2 => 0
  | 2 => fun
    | 0 => 0
    | 1 => b
    | 2 => 0
  | 3 => fun
    | 0 => 0
    | 1 => -b
    | 2 => 0
  | 4 => fun
    | 0 => 0
    | 1 => 0
    | 2 => c
  | 5 => fun
    | 0 => 0
    | 1 => 0
    | 2 => -c

def secondX (a b c : ℝ) : ℝ :=
  let s := site a b c
  (s 0 1 ^ 2 + s 0 2 ^ 2) + (s 1 1 ^ 2 + s 1 2 ^ 2) + (s 2 1 ^ 2 + s 2 2 ^ 2) +
    (s 3 1 ^ 2 + s 3 2 ^ 2) + (s 4 1 ^ 2 + s 4 2 ^ 2) + (s 5 1 ^ 2 + s 5 2 ^ 2)

def secondY (a b c : ℝ) : ℝ :=
  let s := site a b c
  (s 0 0 ^ 2 + s 0 2 ^ 2) + (s 1 0 ^ 2 + s 1 2 ^ 2) + (s 2 0 ^ 2 + s 2 2 ^ 2) +
    (s 3 0 ^ 2 + s 3 2 ^ 2) + (s 4 0 ^ 2 + s 4 2 ^ 2) + (s 5 0 ^ 2 + s 5 2 ^ 2)

def secondZ (a b c : ℝ) : ℝ :=
  let s := site a b c
  (s 0 0 ^ 2 + s 0 1 ^ 2) + (s 1 0 ^ 2 + s 1 1 ^ 2) + (s 2 0 ^ 2 + s 2 1 ^ 2) +
    (s 3 0 ^ 2 + s 3 1 ^ 2) + (s 4 0 ^ 2 + s 4 1 ^ 2) + (s 5 0 ^ 2 + s 5 1 ^ 2)

def productXY (a b c : ℝ) : ℝ :=
  let s := site a b c
  s 0 0 * s 0 1 + s 1 0 * s 1 1 + s 2 0 * s 2 1 + s 3 0 * s 3 1 + s 4 0 * s 4 1 +
    s 5 0 * s 5 1

def productXZ (a b c : ℝ) : ℝ :=
  let s := site a b c
  s 0 0 * s 0 2 + s 1 0 * s 1 2 + s 2 0 * s 2 2 + s 3 0 * s 3 2 + s 4 0 * s 4 2 +
    s 5 0 * s 5 2

def productYZ (a b c : ℝ) : ℝ :=
  let s := site a b c
  s 0 1 * s 0 2 + s 1 1 * s 1 2 + s 2 1 * s 2 2 + s 3 1 * s 3 2 + s 4 1 * s 4 2 +
    s 5 1 * s 5 2

theorem secondX_eq (a b c : ℝ) : secondX a b c = 2 * (b ^ 2 + c ^ 2) := by
  simp [secondX, site]
  ring

theorem secondY_eq (a b c : ℝ) : secondY a b c = 2 * (a ^ 2 + c ^ 2) := by
  simp [secondY, site]
  ring

theorem secondZ_eq (a b c : ℝ) : secondZ a b c = 2 * (a ^ 2 + b ^ 2) := by
  simp [secondZ, site]
  ring

theorem products_zero (a b c : ℝ) :
    productXY a b c = 0 ∧ productXZ a b c = 0 ∧ productYZ a b c = 0 := by
  simp [productXY, productXZ, productYZ, site]

theorem principal_ordered {a b c : ℝ} (ha : 0 < a) (hab : a < b) (hbc : b < c) :
    secondZ a b c < secondY a b c ∧ secondY a b c < secondX a b c := by
  rw [secondX_eq, secondY_eq, secondZ_eq]
  constructor <;> nlinarith

theorem secondX_eq_secondY_iff {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    secondX a b c = secondY a b c ↔ a = b := by
  rw [secondX_eq, secondY_eq]
  constructor
  · intro h
    have hsq : a ^ 2 = b ^ 2 := by linarith
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
    · exact h
    · have hb' : b = 0 := by nlinarith
      have ha' : a = 0 := by nlinarith
      linarith
  · intro h
    rw [h]

theorem secondY_eq_secondZ_iff {a b c : ℝ} (hb : 0 ≤ b) (hc : 0 ≤ c) :
    secondY a b c = secondZ a b c ↔ b = c := by
  rw [secondY_eq, secondZ_eq]
  constructor
  · intro h
    have hsq : b ^ 2 = c ^ 2 := by linarith
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
    · exact h
    · have hc' : c = 0 := by nlinarith
      have hb' : b = 0 := by nlinarith
      linarith
  · intro h
    rw [h]

theorem secondZ_eq_secondX_iff {a b c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) :
    secondZ a b c = secondX a b c ↔ a = c := by
  rw [secondZ_eq, secondX_eq]
  constructor
  · intro h
    have hsq : a ^ 2 = c ^ 2 := by linarith
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
    · exact h
    · have hc' : c = 0 := by nlinarith
      have ha' : a = 0 := by nlinarith
      linarith
  · intro h
    rw [h]
    ring

/-- Signed moments of the four cross pairs in one coordinate plane.
The two opposite arms each see both signs of the right angle. -/
noncomputable def axisPairTorque (χ ψ : ℝ) : ℝ :=
  chordMoment χ ψ (Real.pi / 2) + chordMoment χ ψ (-Real.pi / 2) +
    chordMoment χ ψ (-Real.pi / 2) + chordMoment χ ψ (Real.pi / 2)

theorem axisPairTorque_zero (χ ψ : ℝ) : axisPairTorque χ ψ = 0 := by
  unfold axisPairTorque
  have h := chordMoment_cancels χ ψ (Real.pi / 2)
  have hneg : -Real.pi / 2 = -(Real.pi / 2) := by ring
  rw [hneg]
  linarith

/-- The three components of the axis-intercept torque, one plane each. -/
theorem axisInterceptTorque_zero (a b c : ℝ) :
    axisPairTorque a b = 0 ∧ axisPairTorque b c = 0 ∧ axisPairTorque c a = 0 :=
  ⟨axisPairTorque_zero a b, axisPairTorque_zero b c, axisPairTorque_zero c a⟩

theorem aligned_moment_zero (χ : ℝ) (hs : Real.sin χ ≠ 0) : chordMoment χ χ 0 = 0 := by
  rw [chordMoment_equal χ 0 hs, Real.sin_zero]
  ring

/-- Moment of one off-axis partner at equal chart distance. -/
noncomputable def defectTorque (χ α : ℝ) : ℝ :=
  chordMoment χ χ α

theorem defectTorque_pos {χ α : ℝ} (hχ : 0 < χ) (hχu : χ < Real.pi) (hα : 0 < α)
    (hαu : α < Real.pi) : 0 < defectTorque χ α :=
  chordMoment_equal_pos hχ hχu hα hαu

/-- The mirror partner cancels the defect. -/
theorem mirrorTorque_zero (χ α : ℝ) : defectTorque χ α + chordMoment χ χ (-α) = 0 :=
  chordMoment_cancels χ χ α

/-- Moving the partner off the axis turns a vanishing moment into a positive one. -/
theorem displacement_seeds_torque {χ α : ℝ} (hχ : 0 < χ) (hχu : χ < Real.pi) (hα : 0 < α)
    (hαu : α < Real.pi) :
    chordMoment χ χ 0 = 0 ∧ 0 < defectTorque χ α := by
  refine ⟨?_, defectTorque_pos hχ hχu hα hαu⟩
  exact aligned_moment_zero χ (Real.sin_pos_of_pos_of_lt_pi hχ hχu).ne'

end DstDiophantine.Gravity.ChartRotation
