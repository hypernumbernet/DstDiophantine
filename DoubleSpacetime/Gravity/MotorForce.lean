import DoubleSpacetime.Gravity.KillingTransport
import DoubleSpacetime.Gravity.DualRotorDynamics
import DoubleSpacetime.Gravity.DualRotorFlow
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Force along a fixed motor, as time advances

Position and movement of one motor against the group unit are the motor path `motorPath`: a torsion
rotor times the truncated null translator `1 + t Ω_trans`. The unit is the reference of that
factorization. It is not a massive particle. The translator coefficient reads the motor against the
unit, and it is not a position held by one particle. Space between two particles is the relative
motor of `RelationalMotor`. The translator coefficient of this path is linear in the flow
parameter, so its second derivative vanishes. The body velocity is `M̃ Ṁ`. Its derivative, the
commutator `[Ω_torsion, Ω_trans]`, is the acceleration of that body velocity. It is not the
particle's torsional mismatch.

That commutator does not depend on the flow parameter. What grows linearly is the body-frame
translational velocity. The Minkowski square of that velocity is quadratic in the parameter, and
the derivative of the square is not the commutator. The written lag force `-m δ(t)` is linear in
the same parameter because the written mismatch accelerates by zero. Reading `killingRate` off the
translator clock applies the field law a second time. Neither reading is this commutator.

The field law still selects the generator from the separation. Once the generator is fixed, the
motor clock does not multiply the force.
-/

namespace DoubleSpacetime.Gravity.MotorForce

open CliffordAlgebra NormedSpace
open PGA Generators Operations Motor Amplification
open KillingAxis (lorentzAct killingRate)
open KillingTransport (commutator_omegaTorsion_omegaTrans)

/-! ### The force is the commutator -/

/-- Body-frame force of a fixed generator: `[Ω_torsion, Ω_trans]`. -/
noncomputable def motorForceBivector (p : OmegaParams) : PGA :=
  commutator (omegaTorsion p.torsion) (omegaTrans p.trans)

/-- Coefficient of that force. `lorentzAct` is already the action of `Ω_torsion`. -/
def motorForceCoefficient (p : OmegaParams) : Vec4 :=
  lorentzAct p.torsion p.trans.lambda

/-- Minkowski square of the force coefficient. It has no flow parameter. -/
noncomputable def motorForceMagnitudeSq (p : OmegaParams) : ℝ :=
  Q31 (motorForceCoefficient p)

theorem motorForceBivector_eq (p : OmegaParams) :
    motorForceBivector p = omegaTrans ⟨motorForceCoefficient p⟩ :=
  commutator_omegaTorsion_omegaTrans p.torsion p.trans

/-- Body velocity `Ω + t [Ω_torsion, Ω_trans]`. -/
noncomputable def motorBodyVelocity (p : OmegaParams) (t : ℝ) : PGA :=
  omegaBiv p + t • motorForceBivector p

/-- Translational coefficient of the body velocity: `λ + t ωλ`. -/
def bodyTransCoefficient (p : OmegaParams) (t : ℝ) : Vec4 :=
  fun μ => p.trans.lambda μ + t * motorForceCoefficient p μ

/-- Translator coefficient of the right factor, relative to the identity witness. -/
def translatorCoefficient (p : OmegaParams) (t : ℝ) : Vec4 :=
  fun μ => t * p.trans.lambda μ

theorem motorBodyVelocity_zero (p : OmegaParams) :
    motorBodyVelocity p 0 = omegaBiv p := by
  simp [motorBodyVelocity]

theorem motorBodyVelocity_increment (p : OmegaParams) (t : ℝ) :
    motorBodyVelocity p t = motorBodyVelocity p 0 + t • motorForceBivector p := by
  simp [motorBodyVelocity]

theorem omegaTrans_smul_lambda (c : ℝ) (v : Vec4) :
    c • omegaTrans ⟨v⟩ = omegaTrans ⟨fun μ => c * v μ⟩ := by
  simp only [omegaTrans, Finset.smul_sum]
  congr 1
  ext μ
  simp only [smul_smul]
  congr 1
  ring

theorem motorBodyVelocity_split (p : OmegaParams) (t : ℝ) :
    motorBodyVelocity p t =
      omegaTorsion p.torsion + omegaTrans ⟨bodyTransCoefficient p t⟩ := by
  rw [motorBodyVelocity, omegaBiv, motorForceBivector_eq, omegaTrans_smul_lambda, add_assoc,
    omegaTrans_add]
  rfl

/-! ### The translator factor cancels, and the path is unitary -/

theorem motorPath_factor (p : OmegaParams) (t : ℝ) :
    motorPath p t =
      exp (t • omegaTorsion p.torsion) * (1 + t • omegaTrans p.trans) := by
  rw [motorPath, exp_smul_omegaTrans]

theorem exp_smul_mul_exp_neg (x : PGA) (t : ℝ) :
    exp (t • x) * exp ((-t) • x) = 1 := by
  have hc : Commute (t • x) ((-t) • x) :=
    ((Commute.refl x).smul_left t).smul_right (-t)
  rw [← exp_add_of_commute hc, ← add_smul, add_neg_cancel, zero_smul, exp_zero]

theorem reverse_translator (p : TransParams) (t : ℝ) :
    reverse (1 + t • omegaTrans p) = 1 - t • omegaTrans p := by
  have hrev : reverse (omegaTrans p) = -omegaTrans p := by
    simp only [omegaTrans, map_sum, map_smul, null_reverse]
    rw [← Finset.sum_neg_distrib]
    congr 1
    ext μ
    rw [smul_neg]
  rw [CliffordAlgebra.reverse.map_add, CliffordAlgebra.reverse.map_one, map_smul, hrev,
    smul_neg, sub_eq_add_neg]

theorem reverse_exp_torsion (p : TorsionParams) (t : ℝ) :
    reverse (exp (t • omegaTorsion p)) = exp (-(t • omegaTorsion p)) := by
  have h : reverse (t • omegaTorsion p) = -(t • omegaTorsion p) := by
    rw [map_smul, omegaTorsion_reverse, smul_neg]
  exact reverse_exp_of_reverse_neg h

private theorem translator_square_cancel (B : PGA) (hB : B * B = 0) (t : ℝ) :
    (1 + t • B) * (1 - t • B) = 1 := by
  have hsq : (t • B) * (t • B) = 0 := by
    rw [smul_mul_assoc, mul_smul_comm, hB, smul_zero, smul_zero]
  calc
    (1 + t • B) * (1 - t • B)
        = 1 + t • B - (t • B + (t • B) * (t • B)) := by
          rw [mul_sub, mul_one, add_mul, one_mul]
      _ = 1 + t • B - (t • B + 0) := by rw [hsq]
      _ = 1 + t • B - t • B := by rw [add_zero]
      _ = 1 := by abel

theorem motorPath_unitary (p : OmegaParams) (t : ℝ) :
    motorPath p t * reverse (motorPath p t) = 1 := by
  rw [motorPath_factor, CliffordAlgebra.reverse.map_mul, reverse_translator, reverse_exp_torsion]
  have hcancel := translator_square_cancel (omegaTrans p.trans) (omegaTrans_sq p.trans) t
  calc
    exp (t • omegaTorsion p.torsion) * (1 + t • omegaTrans p.trans) *
          ((1 - t • omegaTrans p.trans) * exp (-(t • omegaTorsion p.torsion)))
        = exp (t • omegaTorsion p.torsion) *
            ((1 + t • omegaTrans p.trans) *
              ((1 - t • omegaTrans p.trans) * exp (-(t • omegaTorsion p.torsion)))) := by
          rw [mul_assoc]
      _ = exp (t • omegaTorsion p.torsion) *
            (((1 + t • omegaTrans p.trans) * (1 - t • omegaTrans p.trans)) *
              exp (-(t • omegaTorsion p.torsion))) := by
          rw [← mul_assoc (1 + t • omegaTrans p.trans) (1 - t • omegaTrans p.trans)]
      _ = exp (t • omegaTorsion p.torsion) *
            (1 * exp (-(t • omegaTorsion p.torsion))) := by rw [hcancel]
      _ = exp (t • omegaTorsion p.torsion) * exp (-(t • omegaTorsion p.torsion)) := by
          rw [one_mul]
      _ = exp (t • omegaTorsion p.torsion) * exp ((-t) • omegaTorsion p.torsion) := by
          rw [neg_smul]
      _ = 1 := exp_smul_mul_exp_neg _ _

/-! ### Right translation turns the commutator into a constant force -/

theorem translator_mul_body (p : OmegaParams) (t : ℝ) :
    (1 + t • omegaTrans p.trans) * motorBodyVelocity p t =
      omegaTorsion p.torsion * (1 + t • omegaTrans p.trans) + omegaTrans p.trans := by
  set A := omegaTorsion p.torsion
  set B := omegaTrans p.trans
  set C := motorForceBivector p
  have hC : C = A * B - B * A := rfl
  have hB2 : B * B = 0 := omegaTrans_sq p.trans
  have hBAB : B * A * B = 0 := omegaTrans_mul_mul p.trans A
  have hBC : B * C = 0 := by
    calc
      B * C = B * (A * B) - B * (B * A) := by rw [hC, mul_sub]
      _ = B * A * B - B * B * A := by rw [← mul_assoc, ← mul_assoc]
      _ = 0 - 0 * A := by rw [hBAB, hB2]
      _ = 0 := by simp
  have hBB : (t • B) * B = 0 := by
    rw [smul_mul_assoc, hB2, smul_zero]
  have htC : (t • B) * (t • C) = 0 := by
    rw [smul_mul_assoc, mul_smul_comm, hBC, smul_zero, smul_zero]
  have htA : (t • B) * A = t • (B * A) := smul_mul_assoc t B A
  calc
    (1 + t • B) * (A + B + t • C)
        = A + B + t • C + (t • B) * (A + B + t • C) := by rw [add_mul, one_mul]
      _ = A + B + t • C + ((t • B) * A + (t • B) * B + (t • B) * (t • C)) := by
          rw [mul_add, mul_add]
      _ = A + B + t • C + (t • B) * A := by rw [hBB, htC, add_zero, add_zero]
      _ = A + B + (t • (A * B) - t • (B * A)) + t • (B * A) := by
          rw [htA, hC, smul_sub]
      _ = A + B + t • (A * B) := by abel
      _ = A * (1 + t • B) + B := by
          rw [mul_add, mul_one, mul_smul_comm]
          abel

theorem hasDerivAt_motorPath_body (p : OmegaParams) (t : ℝ) :
    HasDerivAt (motorPath p) (motorPath p t * motorBodyVelocity p t) t := by
  have hL := hasDerivAt_exp_smul_const (omegaTorsion p.torsion) t
  have hR : HasDerivAt (fun u => (1 : PGA) + u • omegaTrans p.trans) (omegaTrans p.trans) t := by
    have hlin : HasDerivAt (fun u : ℝ => u • omegaTrans p.trans) (omegaTrans p.trans) t := by
      simpa using (hasDerivAt_id t).smul_const (omegaTrans p.trans)
    exact hlin.const_add (1 : PGA)
  have hfun : motorPath p =
      (fun u => exp (u • omegaTorsion p.torsion)) *
        fun u => (1 : PGA) + u • omegaTrans p.trans := by
    ext u
    exact motorPath_factor p u
  rw [hfun]
  refine ((hL.mul hR).congr_deriv ?_)
  set A := omegaTorsion p.torsion
  set B := omegaTrans p.trans
  calc
    (exp (t • A) * A) * (1 + t • B) + exp (t • A) * B
        = exp (t • A) * (A * (1 + t • B)) + exp (t • A) * B := by rw [mul_assoc]
      _ = exp (t • A) * (A * (1 + t • B) + B) := by rw [← mul_add]
      _ = exp (t • A) * ((1 + t • B) * motorBodyVelocity p t) := by
          rw [translator_mul_body]
      _ = (exp (t • A) * (1 + t • B)) * motorBodyVelocity p t := by rw [← mul_assoc]

theorem deriv_motorPath_body (p : OmegaParams) (t : ℝ) :
    deriv (motorPath p) t = motorPath p t * motorBodyVelocity p t :=
  (hasDerivAt_motorPath_body p t).deriv

/-- Pull the derivative back to the body. This is the velocity bivector. -/
theorem motorBodyVelocity_eq_pull (p : OmegaParams) (t : ℝ) :
    reverse (motorPath p t) * deriv (motorPath p) t = motorBodyVelocity p t := by
  rw [deriv_motorPath_body, ← mul_assoc, reverse_mul_of_mul_reverse (motorPath_unitary p t),
    one_mul]

theorem hasDerivAt_motorBodyVelocity (p : OmegaParams) (t : ℝ) :
    HasDerivAt (motorBodyVelocity p) (motorForceBivector p) t := by
  have hconst : HasDerivAt (fun _ : ℝ => omegaBiv p) 0 t := hasDerivAt_const t _
  have hlin : HasDerivAt (fun s : ℝ => s • motorForceBivector p) (motorForceBivector p) t := by
    simpa using (hasDerivAt_id t).smul_const (motorForceBivector p)
  refine ((hconst.add hlin).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun s => ?_)).congr_deriv (by simp)
  simp [motorBodyVelocity]

/-- The force along a fixed generator does not depend on the flow parameter. -/
theorem deriv_motorBodyVelocity (p : OmegaParams) :
    deriv (motorBodyVelocity p) = fun _ => motorForceBivector p := by
  ext t
  exact (hasDerivAt_motorBodyVelocity p t).deriv

theorem motorForce_independent (p : OmegaParams) (t s : ℝ) :
    deriv (motorBodyVelocity p) t = deriv (motorBodyVelocity p) s := by
  simp [deriv_motorBodyVelocity]

/-! ### The witness coefficient does not accelerate -/

theorem hasDerivAt_translatorCoefficient (p : OmegaParams) (μ : Fin 4) (t : ℝ) :
    HasDerivAt (fun s => translatorCoefficient p s μ) (p.trans.lambda μ) t := by
  simpa [translatorCoefficient] using (hasDerivAt_id t).mul_const (p.trans.lambda μ)

theorem deriv_translatorCoefficient (p : OmegaParams) (μ : Fin 4) :
    deriv (fun s => translatorCoefficient p s μ) = fun _ => p.trans.lambda μ := by
  ext t
  exact (hasDerivAt_translatorCoefficient p μ t).deriv

theorem translatorCoefficient_accel (p : OmegaParams) (μ : Fin 4) (t : ℝ) :
    deriv (deriv (fun s => translatorCoefficient p s μ)) t = 0 := by
  rw [deriv_translatorCoefficient]
  simp

/-! ### A unit boost on a unit spatial shift -/

/-- Unit boost on axis 0, unit shift along `e₁`. The commutator is a unit time translation. -/
def boostShift : OmegaParams :=
  ⟨pureBoost 1, ⟨![0, 1, 0, 0]⟩⟩

theorem boostShift_forceCoefficient :
    motorForceCoefficient boostShift = ![1, 0, 0, 0] := by
  ext μ
  fin_cases μ <;> simp [motorForceCoefficient, boostShift, lorentzAct, pureBoost]

theorem boostShift_forceMagnitude :
    motorForceMagnitudeSq boostShift = -1 := by
  rw [motorForceMagnitudeSq, boostShift_forceCoefficient, Q31_eq_minkowskiDot, minkowskiDot]
  simp

theorem boostShift_bodyCoefficient (t : ℝ) :
    bodyTransCoefficient boostShift t = ![t, 1, 0, 0] := by
  ext μ
  rw [bodyTransCoefficient, boostShift_forceCoefficient]
  fin_cases μ <;> simp [boostShift]

theorem boostShift_velocity_square (t : ℝ) :
    Q31 (bodyTransCoefficient boostShift t) = 1 - t ^ 2 := by
  rw [boostShift_bodyCoefficient, Q31_eq_minkowskiDot, minkowskiDot]
  simp
  ring

theorem boostShift_velocity_square_changes :
    Q31 (bodyTransCoefficient boostShift 0) ≠ Q31 (bodyTransCoefficient boostShift 1) := by
  rw [boostShift_velocity_square, boostShift_velocity_square]
  norm_num

theorem hasDerivAt_boostShift_velocity_square (t : ℝ) :
    HasDerivAt (fun s => Q31 (bodyTransCoefficient boostShift s)) (-(2 * t)) t := by
  have hfun : (fun s => Q31 (bodyTransCoefficient boostShift s)) = fun s => 1 - s ^ 2 := by
    ext s
    exact boostShift_velocity_square s
  rw [hfun]
  have hpow : HasDerivAt (fun s : ℝ => s ^ 2) (2 * t) t := by
    simpa using hasDerivAt_pow 2 t
  exact (hpow.const_sub 1).congr_deriv (by ring)

/-- The derivative of the velocity square is not the force. -/
theorem velocity_square_rate_ne_force :
    deriv (fun t => Q31 (bodyTransCoefficient boostShift t)) 0 = 0 ∧
      motorForceMagnitudeSq boostShift = -1 ∧
        deriv (fun t => Q31 (bodyTransCoefficient boostShift t)) 0 ≠
          motorForceMagnitudeSq boostShift := by
  have hderiv := (hasDerivAt_boostShift_velocity_square 0).deriv
  refine ⟨?_, boostShift_forceMagnitude, ?_⟩
  · rw [hderiv]
    norm_num
  · rw [hderiv, boostShift_forceMagnitude]
    norm_num

theorem boostShift_force_ne_zero : motorForceBivector boostShift ≠ 0 := by
  rw [motorForceBivector_eq, boostShift_forceCoefficient]
  intro h
  have hsum : (1 / 2 : ℝ) • null 0 = 0 := by
    have hzero : omegaTrans ⟨![1, 0, 0, 0]⟩ = (1 / 2 : ℝ) • null 0 := by
      simp only [omegaTrans, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.cons_val_three]
      simp
    rw [← hzero]
    exact h
  exact (smul_ne_zero (by norm_num) (null_ne_zero 0)) hsum

/-- The positional parameter has zero acceleration while the force does not vanish. -/
theorem position_accel_zero_force_not (μ : Fin 4) (t : ℝ) :
    deriv (deriv (fun s => translatorCoefficient boostShift s μ)) t = 0 ∧
      motorForceBivector boostShift ≠ 0 :=
  ⟨translatorCoefficient_accel boostShift μ t, boostShift_force_ne_zero⟩

theorem boostShift_translator_spatial (t : ℝ) :
    translatorCoefficient boostShift t 1 = t := by
  simp [translatorCoefficient, boostShift]

/-- The exterior rate, read on the translator clock, changes. The motor force does not. -/
theorem killingRate_of_clock_changes {rs : ℝ} (hrs : rs ≠ 0) :
    killingRate rs (translatorCoefficient boostShift 1 1) ≠
      killingRate rs (translatorCoefficient boostShift 2 1) := by
  rw [boostShift_translator_spatial, boostShift_translator_spatial]
  intro h
  rw [killingRate, killingRate] at h
  have hpow : (1 : ℝ) ^ 2 = 1 ∧ (2 : ℝ) ^ 2 = 4 := by constructor <;> norm_num
  rw [hpow.1, hpow.2] at h
  field_simp at h
  linarith

/-! ### The written lag force is the linear piece, not this commutator -/

theorem lagForce_along_affine (t : ℝ) :
    paperForcePhi 1 (affineMismatch 0 1 t) 0 = -t := by
  simp [paperForcePhi, affineMismatch]

theorem lagForce_changes :
    paperForcePhi 1 (affineMismatch 0 1 0) 0 ≠ paperForcePhi 1 (affineMismatch 0 1 1) 0 := by
  rw [lagForce_along_affine, lagForce_along_affine]
  norm_num

/-- A lag force that changes with the flow parameter is not the motor force. -/
theorem lagForce_not_motorForce :
    paperForcePhi 1 (affineMismatch 0 1 0) 0 ≠ paperForcePhi 1 (affineMismatch 0 1 1) 0 ∧
      deriv (motorBodyVelocity boostShift) 0 = deriv (motorBodyVelocity boostShift) 1 :=
  ⟨lagForce_changes, motorForce_independent boostShift 0 1⟩

end DoubleSpacetime.Gravity.MotorForce
