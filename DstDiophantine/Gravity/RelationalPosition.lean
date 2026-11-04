import Mathlib.Analysis.Quaternion
import DstDiophantine.Gravity.SlerpTorque

/-!
# Position as a relation of two elements

Each substance carries an element of the three-sphere, a unit quaternion. The
position of `b` relative to `a` is the rotor `ρ(a,b) = a⁻¹ b`. It is not the
mismatch `Ω = R_usual† R_dual` inside one particle, and it is not a coordinate
on a chart.

The description group is a pair of unit quaternions, acting by `p ↦ g p h`.
Left multiplication of both elements leaves `ρ` fixed. Right multiplication
replaces `ρ` by `h⁻¹ ρ h` and preserves the geodesic angle `arccos(Re ρ)`.

The equidistant coordinate of `p` about a pole is the logarithm of the relative
position. Moving the pole alone changes that coordinate and does not change
`ρ`. Left-multiplying the pole and the point together leaves the coordinate
fixed. About the pole `a`, the coordinate of `b` is the logarithm of `ρ`.

## Proved

* `ρ(a,b) = 1` if and only if `a = b`, and `Re ρ(a,b)` is the inner product.
* Left invariance of `ρ`, right conjugation, and invariance of the angle under
  both, hence under the pair.
* The equidistant coordinate of `p` about a pole `g` is the logarithm of
  `g⁻¹ p`. The formula returns the origin when `p` is the pole. About the pole
  `a`, the coordinate of `b` is the logarithm of `ρ`.
* A joint left rotation of body, source, and pole leaves the chart readings
  `bodyPoint` and `sourcePoint`. `chordMoment` is a function of those readings,
  so that reading is unchanged.
* One pair has positive `chordMoment` about the identity pole. After the right
  translation that puts the source at the pole and the body on the first
  coordinate axis, the source chart is the origin and `pushedMoment` is zero.
  The angle is the same.

## Not claimed

* A derivation of `a₀`, of circular speed, or of the chord-moment formula.
* That `chordMoment` is a function of the pair alone.
* An identification of `ρ` with the intra-particle mismatch `Ω`.
* A metric, a curvature tensor, or a diffeomorphism group of the three-sphere.
-/

noncomputable section

namespace DstDiophantine.Gravity.RelationalPosition

open Quaternion Real
open scoped Quaternion RealInnerProductSpace

/-- An element of a substance: a point of the three-sphere. -/
@[ext]
structure S3 where
  val : ℍ
  norm_one : normSq val = 1

/-- Unit quaternions multiply. -/
def mul (a b : S3) : S3 where
  val := a.val * b.val
  norm_one := by rw [map_mul, a.norm_one, b.norm_one, mul_one]

/-- Conjugation inverts a unit quaternion. -/
def invS (a : S3) : S3 where
  val := star a.val
  norm_one := by simp [normSq_star, a.norm_one]

/-- The identity element, the standard pole of the equidistant map. -/
def one : S3 where
  val := 1
  norm_one := by simp [normSq_def']

instance : Group S3 where
  mul := mul
  mul_assoc a b c := S3.ext (mul_assoc a.val b.val c.val)
  one := one
  one_mul a := S3.ext (one_mul a.val)
  mul_one a := S3.ext (mul_one a.val)
  inv := invS
  inv_mul_cancel a := S3.ext <| by
    change star a.val * a.val = (1 : ℍ)
    rw [star_mul_self, a.norm_one, coe_one]

@[simp] theorem mul_val (a b : S3) : (a * b).val = a.val * b.val := rfl

@[simp] theorem one_val : (1 : S3).val = 1 := rfl

@[simp] theorem inv_val (a : S3) : (a⁻¹).val = star a.val := rfl

/-- Position of `b` relative to `a`: the rotor `a⁻¹ * b`. -/
def relative (a b : S3) : S3 :=
  a⁻¹ * b

@[simp] theorem relative_val (a b : S3) :
    (relative a b).val = star a.val * b.val := by
  rw [relative, mul_val, inv_val]

/-- The real part of a product is symmetric. -/
theorem re_mul_comm (x y : ℍ) : (x * y).re = (y * x).re := by
  simp only [re_mul]
  ring

theorem re_star_mul (x y : ℍ) : (star x * y).re = (x * star y).re := by
  simp only [re_mul, re_star, imI_star, imJ_star, imK_star]
  ring

/-- `Re ρ(a,b)` is the Euclidean inner product of the two elements. -/
theorem re_relative_eq_inner (a b : S3) :
    (relative a b).val.re = ⟪a.val, b.val⟫ := by
  rw [relative_val, inner_def, re_star_mul]

theorem relative_eq_one_iff (a b : S3) : relative a b = 1 ↔ a = b := by
  rw [relative, inv_mul_eq_iff_eq_mul, mul_one, eq_comm]

/-- Left rotation of both elements leaves the position fixed. -/
theorem relative_left (g a b : S3) : relative (g * a) (g * b) = relative a b := by
  simp only [relative, mul_inv_rev]
  rw [mul_assoc, ← mul_assoc g⁻¹ g b, inv_mul_cancel, one_mul]

/-- Right rotation conjugates the position. -/
theorem relative_right (a b h : S3) :
    relative (a * h) (b * h) = h⁻¹ * relative a b * h := by
  simp only [relative, mul_inv_rev]
  rw [mul_assoc, ← mul_assoc a⁻¹ b h, ← mul_assoc]

/-- Conjugation by a unit quaternion preserves the real part. -/
theorem re_conj (h : S3) (q : ℍ) : (star h.val * q * h.val).re = q.re := by
  have hunit : h.val * star h.val = 1 := by rw [self_mul_star, h.norm_one, coe_one]
  have hcycle : ((star h.val * q) * h.val).re = (h.val * (star h.val * q)).re :=
    re_mul_comm (star h.val * q) h.val
  calc
    (star h.val * q * h.val).re = (h.val * (star h.val * q)).re := hcycle
    _ = ((h.val * star h.val) * q).re := by rw [← mul_assoc]
    _ = ((1 : ℍ) * q).re := by rw [hunit]
    _ = q.re := by simp

theorem re_relative_right (a b h : S3) :
    (relative (a * h) (b * h)).val.re = (relative a b).val.re := by
  rw [relative_right]
  simpa [mul_val, inv_val] using re_conj h (relative a b).val

/-- Geodesic angle between two elements. -/
def separation (a b : S3) : ℝ :=
  Real.arccos (relative a b).val.re

theorem abs_re_le_one (a : S3) : |a.val.re| ≤ 1 := by
  have hsq : a.val.re ^ 2 ≤ 1 := by
    have h := a.norm_one
    rw [normSq_def'] at h
    nlinarith [sq_nonneg a.val.imI, sq_nonneg a.val.imJ, sq_nonneg a.val.imK]
  rw [abs_le]
  constructor <;> nlinarith [hsq]

theorem cos_separation (a b : S3) :
    Real.cos (separation a b) = (relative a b).val.re := by
  have h := abs_re_le_one (relative a b)
  rw [separation, Real.cos_arccos (neg_le_of_abs_le h) (le_of_abs_le h)]

theorem separation_left (g a b : S3) :
    separation (g * a) (g * b) = separation a b := by
  rw [separation, separation, relative_left]

theorem separation_right (a b h : S3) :
    separation (a * h) (b * h) = separation a b := by
  rw [separation, separation, re_relative_right]

/-- A rotation of the three-sphere: left factor, then right factor. -/
@[ext]
structure Rotation where
  left : S3
  right : S3

namespace Rotation

/-- Pair product. The right factor is multiplied in the opposite order, so that
`(g, h) · p = g p h` is a left action. -/
def mul (x y : Rotation) : Rotation where
  left := x.left * y.left
  right := y.right * x.right

def one : Rotation where
  left := 1
  right := 1

def inv (x : Rotation) : Rotation where
  left := x.left⁻¹
  right := x.right⁻¹

instance : Group Rotation where
  mul := mul
  mul_assoc x y z := by
    apply Rotation.ext
    · exact mul_assoc x.left y.left z.left
    · exact (mul_assoc z.right y.right x.right).symm
  one := one
  one_mul x := by
    apply Rotation.ext
    · exact one_mul x.left
    · exact mul_one x.right
  mul_one x := by
    apply Rotation.ext
    · exact mul_one x.left
    · exact one_mul x.right
  inv := inv
  inv_mul_cancel x := by
    apply Rotation.ext
    · exact inv_mul_cancel x.left
    · exact mul_inv_cancel x.right

/-- `(g,h) · p = g p h`. -/
def act (r : Rotation) (p : S3) : S3 :=
  r.left * p * r.right

theorem act_mul (x y : Rotation) (p : S3) : (x * y).act p = x.act (y.act p) := by
  have hxy : x * y = mul x y := rfl
  rw [hxy]
  simp only [act, mul, mul_assoc]

end Rotation

/-- The whole rotation fixes the angle and the right factor alone moves `ρ`. -/
theorem relative_act (r : Rotation) (a b : S3) :
    relative (r.act a) (r.act b) = r.right⁻¹ * relative a b * r.right := by
  simp only [Rotation.act]
  rw [show r.left * a * r.right = r.left * (a * r.right) by rw [mul_assoc],
    show r.left * b * r.right = r.left * (b * r.right) by rw [mul_assoc],
    relative_left, relative_right]

theorem re_relative_act (r : Rotation) (a b : S3) :
    (relative (r.act a) (r.act b)).val.re = (relative a b).val.re := by
  rw [relative_act]
  simpa [mul_val, inv_val] using re_conj r.right (relative a b).val

theorem separation_act (r : Rotation) (a b : S3) :
    separation (r.act a) (r.act b) = separation a b := by
  rw [separation, separation, re_relative_act]

/-! ### Equidistant readings -/

/-- Components of a quaternion, in the order used by `SlerpTorque.lift`. -/
def toChart (q : ℍ) : SlerpTorque.V4 :=
  Quaternion.equivTuple ℝ q

theorem toChart_apply (q : ℍ) :
    toChart q = ![q.re, q.imI, q.imJ, q.imK] :=
  Quaternion.equivTuple_apply ℝ q

/-- Unit quaternion at geodesic distance `χ` in a unit direction. -/
def liftQuat (χ : ℝ) (n : SlerpTorque.V3) : ℍ :=
  ⟨Real.cos χ, Real.sin χ * n 0, Real.sin χ * n 1, Real.sin χ * n 2⟩

theorem toChart_liftQuat (χ : ℝ) (n : SlerpTorque.V3) :
    toChart (liftQuat χ n) = SlerpTorque.lift χ n := by
  funext i
  fin_cases i <;>
    simp [toChart_apply, liftQuat, SlerpTorque.lift]

theorem liftQuat_normSq {χ : ℝ} {n : SlerpTorque.V3} (hn : SlerpTorque.dot3 n n = 1) :
    normSq (liftQuat χ n) = 1 := by
  simp only [normSq_def', liftQuat]
  have hn' : n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2 = 1 := by
    simpa [SlerpTorque.dot3, pow_two] using hn
  have hsum :
      Real.cos χ ^ 2 + (Real.sin χ * n 0) ^ 2 + (Real.sin χ * n 1) ^ 2 +
          (Real.sin χ * n 2) ^ 2 =
        Real.cos χ ^ 2 + Real.sin χ ^ 2 * (n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2) := by
    ring
  rw [hsum, hn', mul_one]
  linear_combination Real.sin_sq_add_cos_sq χ

def elem (χ : ℝ) (n : SlerpTorque.V3) (hn : SlerpTorque.dot3 n n = 1) : S3 where
  val := liftQuat χ n
  norm_one := liftQuat_normSq hn

/-- Coordinate of `p` in the equidistant map whose pole is `pole`. -/
def chartAt (pole p : S3) : SlerpTorque.V3 :=
  SlerpTorque.logChart (toChart (relative pole p).val)

/-- About the pole `a`, the coordinate of `b` is the logarithm of the position. -/
theorem chartAt_eq_log_position (a b : S3) :
    chartAt a b = SlerpTorque.logChart (toChart (relative a b).val) :=
  rfl

/-- At the pole the formula returns the origin. Off the pole, `logChart` is the
equidistant projection. At the identity the written factor is `0 / 0`, and Lean
division gives `0`, the value of the continuous extension. -/
theorem chartAt_self (a : S3) : chartAt a a = fun _ => 0 := by
  rw [chartAt, (relative_eq_one_iff a a).2 rfl, one_val]
  funext i
  simp only [SlerpTorque.logChart, toChart_apply, SlerpTorque.chartIdx]
  fin_cases i <;> simp

/-- Left-multiplying the pole and the point together leaves the coordinate. -/
theorem chartAt_left (g pole p : S3) :
    chartAt (g * pole) (g * p) = chartAt pole p := by
  rw [chartAt, chartAt, relative_left]

theorem chartAt_elem {χ : ℝ} {n : SlerpTorque.V3} (hn : SlerpTorque.dot3 n n = 1)
    (hχ : 0 < χ) (hχu : χ < Real.pi) :
    chartAt 1 (elem χ n hn) = fun i => χ * n i := by
  have hrel : relative 1 (elem χ n hn) = elem χ n hn := by
    apply S3.ext
    simp [relative_val, one_val, elem, star_one, one_mul]
  rw [chartAt, hrel]
  have hval : (elem χ n hn).val = liftQuat χ n := rfl
  rw [hval, toChart_liftQuat]
  exact SlerpTorque.logChart_lift hχ hχu hn

def axis0 : SlerpTorque.V3
  | 0 => 1
  | 1 => 0
  | 2 => 0

def axisAngle (α : ℝ) : SlerpTorque.V3
  | 0 => Real.cos α
  | 1 => Real.sin α
  | 2 => 0

theorem axis0_unit : SlerpTorque.dot3 axis0 axis0 = 1 := by
  simp [SlerpTorque.dot3, axis0]

theorem axisAngle_unit (α : ℝ) : SlerpTorque.dot3 (axisAngle α) (axisAngle α) = 1 := by
  simp only [SlerpTorque.dot3, axisAngle]
  linear_combination Real.sin_sq_add_cos_sq α

def bodyElem (χ : ℝ) : S3 :=
  elem χ axis0 axis0_unit

def sourceElem (ψ α : ℝ) : S3 :=
  elem ψ (axisAngle α) (axisAngle_unit α)

theorem chartAt_body {χ : ℝ} (hχ : 0 < χ) (hχu : χ < Real.pi) :
    chartAt 1 (bodyElem χ) = SlerpTorque.bodyPoint χ := by
  unfold bodyElem
  rw [chartAt_elem axis0_unit hχ hχu]
  funext i
  fin_cases i <;> simp [axis0, SlerpTorque.bodyPoint]

theorem chartAt_source {ψ α : ℝ} (hψ : 0 < ψ) (hψu : ψ < Real.pi) :
    chartAt 1 (sourceElem ψ α) = SlerpTorque.sourcePoint ψ α := by
  unfold sourceElem
  rw [chartAt_elem (axisAngle_unit α) hψ hψu]
  funext i
  fin_cases i <;> simp [axisAngle, SlerpTorque.sourcePoint]

/-- Body, source, and pole, rotated together, keep the chart readings.
`chordMoment` is a function of those readings, so it is unchanged. -/
theorem charts_joint_left (g : S3) {χ ψ α : ℝ}
    (hχ : 0 < χ) (hχu : χ < Real.pi) (hψ : 0 < ψ) (hψu : ψ < Real.pi) :
    chartAt g (g * bodyElem χ) = SlerpTorque.bodyPoint χ ∧
      chartAt g (g * sourceElem ψ α) = SlerpTorque.sourcePoint ψ α := by
  refine ⟨?_, ?_⟩
  · calc
      chartAt g (g * bodyElem χ) = chartAt (g * 1) (g * bodyElem χ) := by rw [mul_one]
      _ = chartAt 1 (bodyElem χ) := chartAt_left g 1 (bodyElem χ)
      _ = SlerpTorque.bodyPoint χ := chartAt_body hχ hχu
  · calc
      chartAt g (g * sourceElem ψ α) = chartAt (g * 1) (g * sourceElem ψ α) := by
        rw [mul_one]
      _ = chartAt 1 (sourceElem ψ α) := chartAt_left g 1 (sourceElem ψ α)
      _ = SlerpTorque.sourcePoint ψ α := chartAt_source hψ hψu

/-! ### One pair, two poles -/

def sampleχ : ℝ :=
  Real.pi / 2

def sampleBody : S3 :=
  bodyElem sampleχ

def sampleSource : S3 :=
  sourceElem sampleχ sampleχ

/-- Right translation that lays the sample body on the first chart axis.
`relative_right` conjugates by `h⁻¹`, and that conjugate is the quaternion
`logChart` sends to `bodyPoint (-sampleχ)`. -/
def axisTurn : S3 where
  val := ⟨Real.sqrt 2 / 2, 0, Real.sqrt 2 / 2, 0⟩
  norm_one := by
    rw [normSq_def']
    have hsq : (Real.sqrt 2 / 2) ^ 2 = 1 / 2 := by
      rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    rw [hsq]
    norm_num

private theorem sampleχ_mem_Ioo : 0 < sampleχ ∧ sampleχ < Real.pi := by
  unfold sampleχ
  constructor
  · exact div_pos Real.pi_pos two_pos
  · linarith [Real.pi_pos]

private theorem sample_relative_val :
    (relative sampleSource sampleBody).val = ⟨0, 0, 0, 1⟩ := by
  ext <;>
    simp [relative_val, sampleSource, sampleBody, sourceElem, bodyElem, elem, liftQuat, axis0,
      axisAngle, sampleχ, Real.cos_pi_div_two, Real.sin_pi_div_two]

private theorem axisTurn_conj_sample :
    star axisTurn.val * (relative sampleSource sampleBody).val * axisTurn.val =
      ⟨0, -1, 0, 0⟩ := by
  rw [sample_relative_val]
  set c : ℝ := Real.sqrt 2 / 2
  have hc : c * c = 1 / 2 := by
    rw [show c = Real.sqrt 2 / 2 from rfl, ← sq, div_pow,
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hstar : star axisTurn.val = ⟨c, 0, -c, 0⟩ := by
    simp [axisTurn, c]
  rw [hstar]
  have hturn : axisTurn.val = ⟨c, 0, c, 0⟩ := by simp [axisTurn, c]
  rw [hturn]
  ext <;> simp; linarith [hc]

private theorem relative_sample_turned_val :
    (relative (sampleSource * axisTurn) (sampleBody * axisTurn)).val =
      ⟨0, -1, 0, 0⟩ := by
  rw [relative_right]
  simpa [mul_val, inv_val] using axisTurn_conj_sample

private theorem logChart_neg_i :
    SlerpTorque.logChart (toChart (⟨0, -1, 0, 0⟩ : ℍ)) =
      SlerpTorque.bodyPoint (-sampleχ) := by
  let n : SlerpTorque.V3 := fun i => -axis0 i
  have hn : SlerpTorque.dot3 n n = 1 := by
    simp [SlerpTorque.dot3, n, axis0]
  have hlift : (⟨0, -1, 0, 0⟩ : ℍ) = liftQuat sampleχ n := by
    simp [liftQuat, n, axis0, sampleχ, Real.cos_pi_div_two, Real.sin_pi_div_two]
  rw [hlift, toChart_liftQuat]
  have hlog := SlerpTorque.logChart_lift sampleχ_mem_Ioo.1 sampleχ_mem_Ioo.2 hn
  funext i
  rw [hlog]
  fin_cases i <;> simp [n, axis0, SlerpTorque.bodyPoint, sampleχ]

private theorem chartAt_sample_body_turned :
    chartAt (sampleSource * axisTurn) (sampleBody * axisTurn) =
      SlerpTorque.bodyPoint (-sampleχ) := by
  rw [chartAt, relative_sample_turned_val]
  exact logChart_neg_i

/-- The same two elements, read from two poles.

About the identity pole the chart figure is the equal-distance pair, and
`chordMoment` is positive. The right translation `axisTurn` puts the source at
the pole of the new chart and lays the body on the first coordinate axis, where
`pushedMoment` is the origin value `0`. The angle is unchanged.
-/
theorem pole_shift_changes_moment :
    one ≠ sampleSource ∧
      chartAt 1 sampleBody = SlerpTorque.bodyPoint sampleχ ∧
      chartAt 1 sampleSource = SlerpTorque.sourcePoint sampleχ sampleχ ∧
      0 < SlerpTorque.chordMoment sampleχ sampleχ sampleχ ∧
      chartAt (sampleSource * axisTurn) (sampleBody * axisTurn) =
        SlerpTorque.bodyPoint (-sampleχ) ∧
      (chartAt (sampleSource * axisTurn) (sampleSource * axisTurn) = fun _ => 0) ∧
      SlerpTorque.pushedMoment (-sampleχ) 0 0 = 0 ∧
      SlerpTorque.chordMoment sampleχ sampleχ sampleχ ≠
        SlerpTorque.pushedMoment (-sampleχ) 0 0 ∧
      separation (sampleSource * axisTurn) (sampleBody * axisTurn) =
        separation sampleSource sampleBody := by
  have hmem := sampleχ_mem_Ioo
  have hpos : 0 < SlerpTorque.chordMoment sampleχ sampleχ sampleχ :=
    SlerpTorque.chordMoment_equal_pos hmem.1 hmem.2 hmem.1 hmem.2
  have hzero : SlerpTorque.pushedMoment (-sampleχ) 0 0 = 0 := by
    apply SlerpTorque.pushedMoment_origin
    simp [sampleχ, Real.sin_neg, Real.sin_pi_div_two]
  refine ⟨?_, chartAt_body hmem.1 hmem.2, chartAt_source hmem.1 hmem.2, hpos,
    chartAt_sample_body_turned, chartAt_self _, hzero, ?_,
    separation_right sampleSource sampleBody axisTurn⟩
  · intro h
    have hre := congrArg (fun a : S3 => a.val.re) h
    simp only [sampleSource, sourceElem, elem, liftQuat, axisAngle, sampleχ,
      Real.cos_pi_div_two] at hre
    exact one_ne_zero hre
  · exact ne_of_gt (by simpa [hzero] using hpos)

end DstDiophantine.Gravity.RelationalPosition
