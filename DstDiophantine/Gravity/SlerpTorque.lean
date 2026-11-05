import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Order.Filter.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Torque from a spherical geodesic read in the flat chart

The pull follows a great circle of the three-sphere. The motion is read in the
flat three-space, through the azimuthal equidistant chart. Those two
directions are not the same, and the difference is a moment about the source.

The chart sends the point at geodesic distance `χ` in a unit direction `n` to
`χ n`. The great circle from the body to the source is the spherical
interpolation of their lifts. Its initial tangent pushes into the chart as
`pushedTangent`. About the source, that tangent has moment `pushedMoment`.
With the body at chart distance `χ`, the source at `ψ`, and angle `α` between
them,

`pushedMoment χ ψ α = chordMoment χ ψ α`.

The moment vanishes when `sin α = 0`, and when the source is the chart origin.
For equal chart distances it is `(1 - cos α) χ (χ - sin χ cos χ) sin α`,
which is positive for `χ, α ∈ (0, π)`. It is odd in the oriented angle, so the
moments at `α` and `-α` sum to zero, and on `(-π, 0)` the equal-distance
moment is negative. The cancellation is inside one chart. It is not an
exchange of the two parallel families.

## Not claimed

* A net spin of a ball whose source sits at the chart origin. That moment is
  zero: the great circle through the origin is a straight ray.
* A numerical angular momentum for the solar system or for a galaxy.
* A value of `a₀`, or a change to the circular-speed law.
-/

namespace DstDiophantine.Gravity.SlerpTorque

open Filter

abbrev V3 := Fin 3 → ℝ

abbrev V4 := Fin 4 → ℝ

def dot3 (u v : V3) : ℝ :=
  u 0 * v 0 + u 1 * v 1 + u 2 * v 2

def cross3 (u v : V3) : V3
  | 0 => u 1 * v 2 - u 2 * v 1
  | 1 => u 2 * v 0 - u 0 * v 2
  | 2 => u 0 * v 1 - u 1 * v 0

def dot4 (u v : V4) : ℝ :=
  u 0 * v 0 + u 1 * v 1 + u 2 * v 2 + u 3 * v 3

def smul4 (c : ℝ) (u : V4) : V4 :=
  fun i => c * u i

def add4 (u v : V4) : V4 :=
  fun i => u i + v i

def sub3 (u v : V3) : V3 :=
  fun i => u i - v i

/-- Lift of a chart point at distance `χ` in a unit direction. -/
noncomputable def lift (χ : ℝ) (n : V3) : V4
  | 0 => Real.cos χ
  | 1 => Real.sin χ * n 0
  | 2 => Real.sin χ * n 1
  | 3 => Real.sin χ * n 2

/-- Index of a chart coordinate inside the ambient `ℝ × ℝ³`. -/
def chartIdx : Fin 3 → Fin 4
  | 0 => 1
  | 1 => 2
  | 2 => 3

/-- Azimuthal equidistant projection, off the poles. -/
noncomputable def logChart (p : V4) : V3 :=
  let factor := Real.arccos (p 0) / Real.sqrt (1 - p 0 ^ 2)
  fun i => factor * p (chartIdx i)

theorem lift_on_sphere (χ : ℝ) (n : V3) (hn : dot3 n n = 1) :
    dot4 (lift χ n) (lift χ n) = 1 := by
  simp only [dot4, lift]
  have htrig := Real.sin_sq_add_cos_sq χ
  have hn' : n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2 = 1 := by
    simpa [dot3, pow_two] using hn
  have hmul :
      Real.cos χ * Real.cos χ + Real.sin χ * n 0 * (Real.sin χ * n 0) +
          Real.sin χ * n 1 * (Real.sin χ * n 1) + Real.sin χ * n 2 * (Real.sin χ * n 2) =
        Real.cos χ ^ 2 + Real.sin χ ^ 2 * (n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2) := by
    ring
  rw [hmul, hn']
  linear_combination htrig

theorem logChart_lift {χ : ℝ} {n : V3} (hχ : 0 < χ) (hχu : χ < Real.pi)
    (hn : dot3 n n = 1) :
    logChart (lift χ n) = fun i => χ * n i := by
  have hs : 0 < Real.sin χ := Real.sin_pos_of_pos_of_lt_pi hχ hχu
  have hsq : 1 - Real.cos χ ^ 2 = Real.sin χ ^ 2 := by
    have h := Real.sin_sq_add_cos_sq χ
    linarith
  have hsqrt : Real.sqrt (1 - Real.cos χ ^ 2) = Real.sin χ := by
    rw [hsq, Real.sqrt_sq hs.le]
  have _ := lift_on_sphere χ n hn
  funext i
  fin_cases i <;>
    simp [logChart, lift, chartIdx, Real.arccos_cos hχ.le hχu.le, hsqrt] <;>
    field_simp [hs.ne']

/-- Spherical interpolation from `P` to `Q` through angle `Ω`. -/
noncomputable def slerp (Ω : ℝ) (P Q : V4) (t : ℝ) : V4 :=
  fun i =>
    Real.sin ((1 - t) * Ω) / Real.sin Ω * P i +
      Real.sin (t * Ω) / Real.sin Ω * Q i

theorem slerp_zero (Ω : ℝ) (P Q : V4) (hΩ : Real.sin Ω ≠ 0) :
    slerp Ω P Q 0 = P := by
  funext i
  simp [slerp, hΩ]

theorem hasDerivAt_slerp_coord (Ω : ℝ) (P Q : V4) (i : Fin 4) (hΩ : Real.sin Ω ≠ 0) :
    HasDerivAt (fun t => slerp Ω P Q t i)
      (Ω / Real.sin Ω * (Q i - Real.cos Ω * P i)) 0 := by
  unfold slerp
  have hinner : HasDerivAt (fun t : ℝ => (1 - t) * Ω) (-Ω) 0 := by
    simpa using ((hasDerivAt_id 0).const_sub 1).mul_const Ω
  have h1 :=
    ((Real.hasDerivAt_sin ((1 - 0) * Ω)).comp 0 hinner).congr_of_eventuallyEq
      (Eventually.of_forall fun _ => rfl)
  have hinner2 : HasDerivAt (fun t : ℝ => t * Ω) Ω 0 := by
    simpa using (hasDerivAt_id 0).mul_const Ω
  have h2 :=
    ((Real.hasDerivAt_sin (0 * Ω)).comp 0 hinner2).congr_of_eventuallyEq
      (Eventually.of_forall fun _ => rfl)
  have hadd := (h1.div_const (Real.sin Ω)).mul_const (P i) |>.add
    ((h2.div_const (Real.sin Ω)).mul_const (Q i))
  refine hadd.congr_deriv ?_
  rw [show (1 - 0) * Ω = Ω by ring, show (0 : ℝ) * Ω = 0 by ring, Real.cos_zero]
  field_simp [hΩ]
  ring

/-- Initial tangent `Q - (P·Q) P` of the great circle, pushed by the
differential of the equidistant chart at chart radius `χ`. The body lies on
the first axis and the source in the first-second plane. -/
noncomputable def pushedTangent (χ ψ α : ℝ) : V3 :=
  let sχ := Real.sin χ
  let cχ := Real.cos χ
  let sψ := Real.sin ψ
  let cψ := Real.cos ψ
  let sα := Real.sin α
  let cα := Real.cos α
  let pq := cχ * cψ + sχ * sψ * cα
  let adot := cψ - pq * cχ
  let b1 := sψ * cα - pq * sχ
  let b2 := sψ * sα
  let dL1 := adot * (χ * cχ - sχ) / sχ ^ 2 + χ / sχ * b1
  let dL2 := χ / sχ * b2
  fun
    | 0 => dL1
    | 1 => dL2
    | 2 => 0

def bodyPoint (χ : ℝ) : V3
  | 0 => χ
  | 1 => 0
  | 2 => 0

noncomputable def sourcePoint (ψ α : ℝ) : V3
  | 0 => ψ * Real.cos α
  | 1 => ψ * Real.sin α
  | 2 => 0

/-- Moment about the source of the pushed tangent. Its third component is the
scalar `pushedMoment`; the first two vanish. -/
noncomputable def pushedMoment (χ ψ α : ℝ) : ℝ :=
  let sχ := Real.sin χ
  let cχ := Real.cos χ
  let sψ := Real.sin ψ
  let cψ := Real.cos ψ
  let sα := Real.sin α
  let cα := Real.cos α
  let pq := cχ * cψ + sχ * sψ * cα
  let adot := cψ - pq * cχ
  let b1 := sψ * cα - pq * sχ
  let b2 := sψ * sα
  let dL1 := adot * (χ * cχ - sχ) / sχ ^ 2 + χ / sχ * b1
  let dL2 := χ / sχ * b2
  let ux := ψ * cα - χ
  let uy := ψ * sα
  uy * dL1 - ux * dL2

/-- Closed moment, normal to the plane of the two chart radii. -/
noncomputable def chordMoment (χ ψ α : ℝ) : ℝ :=
  (χ ^ 2 * Real.sin ψ / Real.sin χ -
      χ * ψ * Real.sin ψ * Real.cos α / Real.sin χ -
      ψ * Real.sin χ * Real.cos ψ +
      ψ * Real.sin ψ * Real.cos α * Real.cos χ) *
    Real.sin α

theorem pushedMoment_eq (χ ψ α : ℝ) (hs : Real.sin χ ≠ 0) :
    pushedMoment χ ψ α = chordMoment χ ψ α := by
  simp only [pushedMoment, chordMoment]
  set sχ := Real.sin χ
  set cχ := Real.cos χ
  set sψ := Real.sin ψ
  set cψ := Real.cos ψ
  set sα := Real.sin α
  set cα := Real.cos α
  have hsχ : sχ ≠ 0 := by
    simpa [sχ] using hs
  have hχ : sχ ^ 2 + cχ ^ 2 - 1 = 0 := by
    unfold sχ cχ
    linear_combination Real.sin_sq_add_cos_sq χ
  have hpoly :
      sχ ^ 2 *
          ((ψ * sα) * ((cψ - (cχ * cψ + sχ * sψ * cα) * cχ) * (χ * cχ - sχ) / sχ ^ 2 +
              χ / sχ * (sψ * cα - (cχ * cψ + sχ * sψ * cα) * sχ)) -
            (ψ * cα - χ) * (χ / sχ * (sψ * sα)) -
            (χ ^ 2 * sψ / sχ - χ * ψ * sψ * cα / sχ - ψ * sχ * cψ +
                ψ * sψ * cα * cχ) * sα) =
        (sχ ^ 2 + cχ ^ 2 - 1) *
          (-cα * χ * ψ * sα * sχ * sψ - χ * cχ * cψ * ψ * sα + cψ * ψ * sα * sχ) := by
    field_simp [hsχ]
    ring
  have hzero :
      sχ ^ 2 *
          ((ψ * sα) * ((cψ - (cχ * cψ + sχ * sψ * cα) * cχ) * (χ * cχ - sχ) / sχ ^ 2 +
              χ / sχ * (sψ * cα - (cχ * cψ + sχ * sψ * cα) * sχ)) -
            (ψ * cα - χ) * (χ / sχ * (sψ * sα)) -
            (χ ^ 2 * sψ / sχ - χ * ψ * sψ * cα / sχ - ψ * sχ * cψ +
                ψ * sψ * cα * cχ) * sα) = 0 := by
    rw [hpoly, hχ, zero_mul]
  rw [mul_eq_zero] at hzero
  rcases hzero with hpow | hdiff
  · exact absurd hpow (pow_ne_zero 2 hsχ)
  · exact sub_eq_zero.mp hdiff

/-- On one ray from the chart origin the moment vanishes. -/
theorem pushedMoment_aligned (χ ψ α : ℝ) (hs : Real.sin χ ≠ 0) (hα : Real.sin α = 0) :
    pushedMoment χ ψ α = 0 := by
  rw [pushedMoment_eq χ ψ α hs, chordMoment, hα]
  ring

/-- A source at the chart origin exerts no moment. The great circle is a ray. -/
theorem pushedMoment_origin (χ α : ℝ) (hs : Real.sin χ ≠ 0) :
    pushedMoment χ 0 α = 0 := by
  rw [pushedMoment_eq χ 0 α hs]
  simp [chordMoment, Real.sin_zero, Real.cos_zero]

/-- Equal chart distances. -/
theorem chordMoment_equal (χ α : ℝ) (hs : Real.sin χ ≠ 0) :
    chordMoment χ χ α =
      (1 - Real.cos α) * χ * (χ - Real.sin χ * Real.cos χ) * Real.sin α := by
  unfold chordMoment
  field_simp [hs]
  ring

theorem chordMoment_equal_pos {χ α : ℝ} (hχ : 0 < χ) (hχu : χ < Real.pi)
    (hα : 0 < α) (hαu : α < Real.pi) :
    0 < chordMoment χ χ α := by
  have hs : Real.sin χ ≠ 0 := (Real.sin_pos_of_pos_of_lt_pi hχ hχu).ne'
  rw [chordMoment_equal χ α hs]
  have hsinα : 0 < Real.sin α := Real.sin_pos_of_pos_of_lt_pi hα hαu
  have hgap : Real.sin (2 * χ) < 2 * χ := by
    have h2 : 0 < 2 * χ := by linarith
    simpa using Real.sin_lt h2
  have hrad : 0 < χ - Real.sin χ * Real.cos χ := by
    have htwo : Real.sin (2 * χ) = 2 * Real.sin χ * Real.cos χ := Real.sin_two_mul χ
    have : χ - Real.sin χ * Real.cos χ = (2 * χ - Real.sin (2 * χ)) / 2 := by
      rw [htwo]
      ring
    rw [this]
    have : 0 < 2 * χ - Real.sin (2 * χ) := by linarith
    exact div_pos this two_pos
  have hcos : 0 < 1 - Real.cos α := by
    have hhalf_pos : 0 < α / 2 := by linarith
    have hhalf_lt : α / 2 < Real.pi / 2 := by linarith [Real.pi_pos]
    have hsin : 0 < Real.sin (α / 2) :=
      Real.sin_pos_of_pos_of_lt_pi hhalf_pos (by linarith [hhalf_lt, Real.pi_pos])
    have hform : Real.cos α = 1 - 2 * Real.sin (α / 2) ^ 2 := by
      have h := Real.cos_two_mul_eq_one_sub (α / 2)
      simpa [mul_div_cancel₀ α two_ne_zero] using h
    rw [hform]
    nlinarith [hsin]
  exact mul_pos (mul_pos (mul_pos hcos hχ) hrad) hsinα

/-- Reversing the oriented angle reverses the moment. -/
theorem chordMoment_neg_angle (χ ψ α : ℝ) :
    chordMoment χ ψ (-α) = -chordMoment χ ψ α := by
  simp only [chordMoment, Real.sin_neg, Real.cos_neg]
  ring

/-- A source and its reflection across the ray cancel. -/
theorem chordMoment_cancels (χ ψ α : ℝ) :
    chordMoment χ ψ α + chordMoment χ ψ (-α) = 0 := by
  rw [chordMoment_neg_angle]
  ring

/-- Equal chart distances give a negative moment on `(-π, 0)`. -/
theorem chordMoment_equal_neg {χ α : ℝ} (hχ : 0 < χ) (hχu : χ < Real.pi)
    (hα : -Real.pi < α) (hα0 : α < 0) :
    chordMoment χ χ α < 0 := by
  have hflip : chordMoment χ χ α = -chordMoment χ χ (-α) := by
    have h := chordMoment_neg_angle χ χ (-α)
    simpa using h
  rw [hflip]
  have hpos : 0 < chordMoment χ χ (-α) :=
    chordMoment_equal_pos hχ hχu (neg_pos.mpr hα0) (by linarith)
  linarith

theorem cross_pushedTangent (χ ψ α : ℝ) :
    cross3 (sub3 (bodyPoint χ) (sourcePoint ψ α)) (pushedTangent χ ψ α) =
      fun
        | 0 => 0
        | 1 => 0
        | 2 => pushedMoment χ ψ α := by
  funext i
  fin_cases i
  · simp [cross3, sub3, bodyPoint, sourcePoint, pushedTangent]
  · simp [cross3, sub3, bodyPoint, sourcePoint, pushedTangent]
  · simp [cross3, sub3, bodyPoint, sourcePoint, pushedTangent, pushedMoment]
    ring

end DstDiophantine.Gravity.SlerpTorque

