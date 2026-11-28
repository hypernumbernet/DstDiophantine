import DoubleSpacetime.Algebra.Sandwich
import DoubleSpacetime.Gravity.MotorForce

/-!
# Space only between two particles

Position and movement stay a torsion rotor times a truncated translator. `motorPath` is the case
whose translator vanishes at the flow origin, so every such path starts on the identity witness.
That witness is a second particle. The translator coefficient is the relation to it, and one such
coefficient is not a position.

A particle placed off the witness is the same factorization with an initial translator. Space
between two particles is the motor `reverse(M_a) M_b`. It is the identity when the particles
coincide. A common left motor cancels, so a shared displacement is not space.

On a shared torsion rotor the rotors cancel. The translator that remains is the difference of the
initial coefficients plus the flow parameter times the difference of the velocity coefficients.
Particles that share a velocity keep that difference fixed, while each witness coefficient keeps
moving. The commutator force of the joining translator is zero. The two witness forces need not
be, and their difference is not the force in the space between the particles.

Joining two parameters of one `motorPath` conjugates the earlier translator by the relative rotor.
The difference of the witness coefficients is not that translator. No metric and no position
operator is introduced.
-/

noncomputable section

namespace DoubleSpacetime.Gravity.RelationalMotor

open CliffordAlgebra NormedSpace
open PGA Generators Operations Motor Amplification Sandwich
open MotorForce (boostShift motorBodyVelocity motorForceBivector motorForceCoefficient
  motorPath_factor translatorCoefficient omegaTrans_smul_lambda exp_smul_mul_exp_neg
  reverse_exp_torsion)
open KillingAxis (killingRate lorentzAct)

/-! ### A translator may carry an initial coefficient -/

/-- Translator present at the flow origin. -/
def placedOffset (p : OmegaParams) (x : TransParams) (t : ℝ) : PGA :=
  omegaTrans x + t • omegaTrans p.trans

/-- Right factor `1 + Ω_x + t Ω_v`. At `x = 0` this is the factor of `motorPath`. -/
def placedRight (p : OmegaParams) (x : TransParams) (t : ℝ) : PGA :=
  1 + placedOffset p x t

/-- Torsion rotor times that translator. -/
def placedPath (p : OmegaParams) (x : TransParams) (t : ℝ) : PGA :=
  exp (t • omegaTorsion p.torsion) * placedRight p x t

/-- Coefficient from `a` to `b`: initial difference plus the parameter times the velocity
difference. -/
def separationCoefficient (xa xb va vb : TransParams) (t : ℝ) : Vec4 :=
  fun μ => xb.lambda μ - xa.lambda μ + t * (vb.lambda μ - va.lambda μ)

/-- The motor from `a` to `b`. -/
def between (a b : PGA) : PGA :=
  reverse a * b

def zeroTrans : TransParams where
  lambda := fun _ => 0

/-- Unit coefficient along `e₁`, scaled by `c`. -/
def along1 (c : ℝ) : TransParams where
  lambda := ![0, c, 0, 0]

theorem omegaTrans_zero : omegaTrans zeroTrans = 0 := by
  simp [omegaTrans, zeroTrans]

theorem omegaTrans_neg (p : TransParams) :
    omegaTrans ⟨fun μ => -p.lambda μ⟩ = -omegaTrans p := by
  simp only [omegaTrans]
  rw [← Finset.sum_neg_distrib]
  congr 1
  ext μ
  rw [neg_div, neg_smul]

theorem omegaTrans_sub (p q : TransParams) :
    omegaTrans q - omegaTrans p = omegaTrans ⟨fun μ => q.lambda μ - p.lambda μ⟩ := by
  rw [sub_eq_add_neg, ← omegaTrans_neg, omegaTrans_add]
  rfl

theorem omegaTrans_eq_of_lambda {v w : Vec4} (h : ∀ μ, v μ = w μ) :
    omegaTrans ⟨v⟩ = omegaTrans ⟨w⟩ := by
  rw [show v = w from funext h]

theorem reverse_omegaTrans (p : TransParams) : reverse (omegaTrans p) = -omegaTrans p := by
  simp only [omegaTrans, map_sum, map_smul, null_reverse]
  rw [← Finset.sum_neg_distrib]
  congr 1
  ext μ
  rw [smul_neg]

theorem reverse_placedOffset (p : OmegaParams) (x : TransParams) (t : ℝ) :
    reverse (placedOffset p x t) = -placedOffset p x t := by
  simp only [placedOffset, map_add, map_smul, reverse_omegaTrans, smul_neg, neg_add]

theorem reverse_placedRight (p : OmegaParams) (x : TransParams) (t : ℝ) :
    reverse (placedRight p x t) = 1 - placedOffset p x t := by
  rw [placedRight, CliffordAlgebra.reverse.map_add, CliffordAlgebra.reverse.map_one,
    reverse_placedOffset, sub_eq_add_neg]

theorem placedOffset_null (p : OmegaParams) (x : TransParams) (t : ℝ) :
    placedOffset p x t ∈ nullSpan :=
  add_mem (omegaTrans_mem_nullSpan x)
    (smul_mem_nullSpan t (omegaTrans_mem_nullSpan p.trans))

theorem placedOffset_sq (p : OmegaParams) (x : TransParams) (t : ℝ) :
    placedOffset p x t * placedOffset p x t = 0 :=
  nullSpan_mul (placedOffset_null p x t) (placedOffset_null p x t)

theorem placedOffset_mul_trans (p : OmegaParams) (x : TransParams) (t : ℝ) :
    placedOffset p x t * omegaTrans p.trans = 0 :=
  nullSpan_mul (placedOffset_null p x t) (omegaTrans_mem_nullSpan p.trans)

theorem trans_mul_placedOffset (p : OmegaParams) (x : TransParams) (t : ℝ) :
    omegaTrans p.trans * placedOffset p x t = 0 :=
  nullSpan_mul (omegaTrans_mem_nullSpan p.trans) (placedOffset_null p x t)

theorem placedOffset_mul_mul (p : OmegaParams) (x : TransParams) (t : ℝ) (z : PGA) :
    placedOffset p x t * z * placedOffset p x t = 0 :=
  nullSpan_mul_mul (placedOffset_null p x t) (placedOffset_null p x t) z

theorem placedPath_zero (p : OmegaParams) (t : ℝ) :
    placedPath p zeroTrans t = motorPath p t := by
  simp [placedPath, placedRight, placedOffset, omegaTrans_zero, motorPath_factor]

/-! ### The relation to the witness is not space -/

theorem between_one (m : PGA) : between 1 m = m := by
  simp [between]

theorem between_self {m : PGA} (h : m * reverse m = 1) : between m m = 1 := by
  rw [between, reverse_mul_of_mul_reverse h]

theorem between_left {g a b : PGA} (hg : g * reverse g = 1) :
    between (g * a) (g * b) = between a b := by
  rw [between, between, CliffordAlgebra.reverse.map_mul]
  calc
    reverse a * reverse g * (g * b) = reverse a * (reverse g * (g * b)) := by rw [mul_assoc]
    _ = reverse a * (reverse g * g * b) := by rw [← mul_assoc (reverse g) g b]
    _ = reverse a * (1 * b) := by rw [reverse_mul_of_mul_reverse hg]
    _ = reverse a * b := by rw [one_mul]

theorem placedPath_unitary (p : OmegaParams) (x : TransParams) (t : ℝ) :
    placedPath p x t * reverse (placedPath p x t) = 1 := by
  rw [placedPath, CliffordAlgebra.reverse.map_mul, reverse_placedRight, reverse_exp_torsion]
  calc
    exp (t • omegaTorsion p.torsion) * (1 + placedOffset p x t) *
          ((1 - placedOffset p x t) * exp (-(t • omegaTorsion p.torsion)))
        = exp (t • omegaTorsion p.torsion) *
            ((1 + placedOffset p x t) * (1 - placedOffset p x t) *
              exp (-(t • omegaTorsion p.torsion))) := by
          rw [mul_assoc, mul_assoc]
      _ = exp (t • omegaTorsion p.torsion) *
            (1 * exp (-(t • omegaTorsion p.torsion))) := by
          rw [show (1 + placedOffset p x t) * (1 - placedOffset p x t) = 1 by
            have hsq := placedOffset_sq p x t
            calc
              (1 + placedOffset p x t) * (1 - placedOffset p x t)
                  = 1 + placedOffset p x t -
                      (placedOffset p x t + placedOffset p x t * placedOffset p x t) := by
                    rw [mul_sub, mul_one, add_mul, one_mul]
                _ = 1 + placedOffset p x t - (placedOffset p x t + 0) := by rw [hsq]
                _ = 1 + placedOffset p x t - placedOffset p x t := by rw [add_zero]
                _ = 1 := by abel]
      _ = exp (t • omegaTorsion p.torsion) * exp ((-t) • omegaTorsion p.torsion) := by
          rw [one_mul, neg_smul]
      _ = 1 := exp_smul_mul_exp_neg _ _

theorem between_placed_self (p : OmegaParams) (x : TransParams) (t : ℝ) :
    between (placedPath p x t) (placedPath p x t) = 1 :=
  between_self (placedPath_unitary p x t)

/-- On one torsion, the rotors cancel and the translator is the separation coefficient. -/
theorem between_shared (tor : TorsionParams) (xa xb va vb : TransParams) (t : ℝ) :
    between (placedPath ⟨tor, va⟩ xa t) (placedPath ⟨tor, vb⟩ xb t) =
      1 + omegaTrans ⟨separationCoefficient xa xb va vb t⟩ := by
  set A := omegaTorsion tor
  have hpath (v x : TransParams) :
      placedPath ⟨tor, v⟩ x t = exp (t • A) * (1 + placedOffset ⟨tor, v⟩ x t) := by
    simp [placedPath, placedRight, A]
  have hcancel : exp (-(t • A)) * exp (t • A) = 1 := by
    simpa [neg_smul] using exp_smul_mul_exp_neg A (-t)
  have hrevOff (v x : TransParams) :
      reverse (1 + placedOffset ⟨tor, v⟩ x t) = 1 - placedOffset ⟨tor, v⟩ x t := by
    simpa [placedRight] using reverse_placedRight ⟨tor, v⟩ x t
  rw [hpath va xa, hpath vb xb, between, CliffordAlgebra.reverse.map_mul, hrevOff va xa,
    reverse_exp_torsion]
  have hDa : placedOffset ⟨tor, va⟩ xa t = omegaTrans xa + t • omegaTrans va := rfl
  have hDb : placedOffset ⟨tor, vb⟩ xb t = omegaTrans xb + t • omegaTrans vb := rfl
  have hmul : placedOffset ⟨tor, va⟩ xa t * placedOffset ⟨tor, vb⟩ xb t = 0 :=
    nullSpan_mul (placedOffset_null _ _ _) (placedOffset_null _ _ _)
  have hprod :
      (1 - placedOffset ⟨tor, va⟩ xa t) * (1 + placedOffset ⟨tor, vb⟩ xb t) =
        1 + placedOffset ⟨tor, vb⟩ xb t - placedOffset ⟨tor, va⟩ xa t := by
    calc
      (1 - placedOffset ⟨tor, va⟩ xa t) * (1 + placedOffset ⟨tor, vb⟩ xb t)
          = 1 + placedOffset ⟨tor, vb⟩ xb t -
              (placedOffset ⟨tor, va⟩ xa t +
                placedOffset ⟨tor, va⟩ xa t * placedOffset ⟨tor, vb⟩ xb t) := by
            rw [sub_mul, one_mul, mul_add, mul_one]
        _ = 1 + placedOffset ⟨tor, vb⟩ xb t - placedOffset ⟨tor, va⟩ xa t := by
            rw [hmul, add_zero]
  calc
    (1 - placedOffset ⟨tor, va⟩ xa t) * exp (-(t • A)) *
          (exp (t • A) * (1 + placedOffset ⟨tor, vb⟩ xb t))
        = (1 - placedOffset ⟨tor, va⟩ xa t) *
            (exp (-(t • A)) * exp (t • A) * (1 + placedOffset ⟨tor, vb⟩ xb t)) := by
          rw [mul_assoc, ← mul_assoc (exp (-(t • A))) (exp (t • A))]
      _ = (1 - placedOffset ⟨tor, va⟩ xa t) * (1 + placedOffset ⟨tor, vb⟩ xb t) := by
          rw [hcancel, one_mul]
      _ = 1 + placedOffset ⟨tor, vb⟩ xb t - placedOffset ⟨tor, va⟩ xa t := hprod
      _ = 1 + (omegaTrans xb - omegaTrans xa) +
            (t • omegaTrans vb - t • omegaTrans va) := by
          rw [hDa, hDb]
          abel
      _ = 1 + omegaTrans ⟨fun μ => xb.lambda μ - xa.lambda μ⟩ +
            t • omegaTrans ⟨fun μ => vb.lambda μ - va.lambda μ⟩ := by
          rw [omegaTrans_sub, ← smul_sub, omegaTrans_sub]
      _ = 1 + omegaTrans ⟨separationCoefficient xa xb va vb t⟩ := by
          have hcomb : omegaTrans ⟨fun μ => xb.lambda μ - xa.lambda μ⟩ +
              t • omegaTrans ⟨fun μ => vb.lambda μ - va.lambda μ⟩ =
              omegaTrans ⟨separationCoefficient xa xb va vb t⟩ := by
            rw [omegaTrans_smul_lambda, omegaTrans_add]
            exact omegaTrans_eq_of_lambda fun μ => by simp [separationCoefficient]
          rw [add_assoc, hcomb]

/-! ### Movement of the separation, and the witness coefficient -/

theorem hasDerivAt_separationCoefficient (xa xb va vb : TransParams) (μ : Fin 4) (t : ℝ) :
    HasDerivAt (fun s => separationCoefficient xa xb va vb s μ) (vb.lambda μ - va.lambda μ) t := by
  have hfun : (fun s => separationCoefficient xa xb va vb s μ) =
      fun s => (xb.lambda μ - xa.lambda μ) + s * (vb.lambda μ - va.lambda μ) := by
    ext s
    simp [separationCoefficient]
  rw [hfun]
  exact (((hasDerivAt_id t).mul_const (vb.lambda μ - va.lambda μ)).const_add
    (xb.lambda μ - xa.lambda μ)).congr_deriv (one_mul _)

theorem separationCoefficient_accel (xa xb va vb : TransParams) (μ : Fin 4) (t : ℝ) :
    deriv (deriv (fun s => separationCoefficient xa xb va vb s μ)) t = 0 := by
  have hderiv : deriv (fun s => separationCoefficient xa xb va vb s μ) =
      fun _ => vb.lambda μ - va.lambda μ := by
    ext s
    exact (hasDerivAt_separationCoefficient xa xb va vb μ s).deriv
  rw [hderiv]
  exact (hasDerivAt_const t _).deriv

theorem separation_fixed_of_shared_velocity (xa xb v : TransParams) (t : ℝ) :
    separationCoefficient xa xb v v t = fun μ => xb.lambda μ - xa.lambda μ := by
  ext μ
  simp [separationCoefficient]

/-! ### The joining translator carries no commutator force -/

def pureTranslator (x : TransParams) : OmegaParams where
  torsion := ⟨fun _ => 0, fun _ => 0⟩
  trans := x

theorem pureTranslator_force (x : TransParams) :
    motorForceCoefficient (pureTranslator x) = fun _ => 0 := by
  ext μ
  fin_cases μ <;> simp [motorForceCoefficient, pureTranslator, lorentzAct]

theorem boostVelocity_force (c : ℝ) :
    motorForceCoefficient ⟨pureBoost 1, along1 c⟩ = ![c, 0, 0, 0] := by
  ext μ
  fin_cases μ <;> simp [motorForceCoefficient, lorentzAct, pureBoost, along1]

/-- Two boosts of speeds `1` and `3` along `e₁`. The space between them at parameter `1` has
coefficient `2`. Each witness coefficient is the other number. The witness forces differ from
each other and from the force of the joining translator, which is zero. -/
theorem pair_space_not_witness :
    between (placedPath ⟨pureBoost 1, along1 1⟩ zeroTrans 1)
        (placedPath ⟨pureBoost 1, along1 3⟩ zeroTrans 1) =
      1 + omegaTrans (along1 2) ∧
    (translatorCoefficient ⟨pureBoost 1, along1 1⟩ 1 = (along1 1).lambda) ∧
      (translatorCoefficient ⟨pureBoost 1, along1 3⟩ 1 = (along1 3).lambda) ∧
        (separationCoefficient zeroTrans zeroTrans (along1 1) (along1 3) 1 = (along1 2).lambda) ∧
          ((along1 1).lambda ≠ (along1 2).lambda) ∧
            ((along1 3).lambda ≠ (along1 2).lambda) ∧
              (motorForceCoefficient ⟨pureBoost 1, along1 1⟩ = ![1, 0, 0, 0]) ∧
                (motorForceCoefficient ⟨pureBoost 1, along1 3⟩ = ![3, 0, 0, 0]) ∧
                  (motorForceCoefficient (pureTranslator (along1 2)) = fun _ => (0 : ℝ)) ∧
                    motorForceCoefficient ⟨pureBoost 1, along1 1⟩ ≠
                      motorForceCoefficient (pureTranslator (along1 2)) := by
  have hbetween := between_shared (pureBoost 1) zeroTrans zeroTrans (along1 1) (along1 3) 1
  have hsep : separationCoefficient zeroTrans zeroTrans (along1 1) (along1 3) 1 =
      (along1 2).lambda := by
    ext μ
    fin_cases μ
    · simp [separationCoefficient, zeroTrans, along1]
    · norm_num [separationCoefficient, zeroTrans, along1]
    · simp [separationCoefficient, zeroTrans, along1]
    · simp [separationCoefficient, zeroTrans, along1]
  have htrans : omegaTrans ⟨separationCoefficient zeroTrans zeroTrans (along1 1) (along1 3) 1⟩ =
      omegaTrans (along1 2) := by
    rw [hsep]
  refine ⟨?_, ?_, ?_, hsep, ?_, ?_, boostVelocity_force 1, boostVelocity_force 3,
    pureTranslator_force (along1 2), ?_⟩
  · rw [hbetween, htrans]
  · ext μ
    fin_cases μ <;> simp [translatorCoefficient, along1]
  · ext μ
    fin_cases μ <;> simp [translatorCoefficient, along1]
  · intro h
    have := congrFun h 1
    simp [along1] at this
  · intro h
    have := congrFun h 1
    simp [along1] at this
  · rw [boostVelocity_force, pureTranslator_force]
    intro h
    have := congrFun h 0
    simp at this

/-- Shared velocity: the separation stays the initial difference, while the witness coefficient
of the first particle moves. -/
theorem comoving_space_fixed (t : ℝ) :
    separationCoefficient (along1 1) (along1 3) (along1 1) (along1 1) t = (along1 2).lambda ∧
      deriv (fun s => separationCoefficient (along1 1) (along1 3) (along1 1) (along1 1) s 1) t =
        0 ∧
        deriv (fun s => translatorCoefficient ⟨pureBoost 1, along1 1⟩ s 1) t = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [separation_fixed_of_shared_velocity]
    ext μ
    fin_cases μ
    · simp [along1]
    · norm_num [along1]
    · simp [along1]
    · simp [along1]
  · rw [(hasDerivAt_separationCoefficient (along1 1) (along1 3) (along1 1) (along1 1) 1 t).deriv]
    simp [along1]
  · rw [MotorForce.deriv_translatorCoefficient]
    simp [along1]

theorem field_reads_the_pair {rs : ℝ} (hrs : rs ≠ 0) :
    killingRate rs 1 ≠ killingRate rs 2 ∧ killingRate rs 3 ≠ killingRate rs 2 := by
  constructor
  · intro h
    rw [killingRate, killingRate] at h
    have hpow : (1 : ℝ) ^ 2 = 1 ∧ (2 : ℝ) ^ 2 = 4 := by constructor <;> norm_num
    rw [hpow.1, hpow.2] at h
    field_simp at h
    linarith
  · intro h
    rw [killingRate, killingRate] at h
    have hpow : (3 : ℝ) ^ 2 = 9 ∧ (2 : ℝ) ^ 2 = 4 := by constructor <;> norm_num
    rw [hpow.1, hpow.2] at h
    field_simp at h
    linarith

/-! ### Body velocity of a placed motor -/

/-- Body velocity `Ω + [Ω_torsion, Ω_x] + t [Ω_torsion, Ω_v]`. The offset shifts the velocity and
does not enter the force. -/
def placedBodyVelocity (p : OmegaParams) (x : TransParams) (t : ℝ) : PGA :=
  omegaBiv p + commutator (omegaTorsion p.torsion) (omegaTrans x) + t • motorForceBivector p

theorem placedBodyVelocity_zero (p : OmegaParams) (t : ℝ) :
    placedBodyVelocity p zeroTrans t = motorBodyVelocity p t := by
  simp [placedBodyVelocity, motorBodyVelocity, omegaTrans_zero, Generators.commutator]

theorem placedBodyVelocity_split (p : OmegaParams) (x : TransParams) (t : ℝ) :
    placedBodyVelocity p x t =
      omegaTorsion p.torsion + omegaTrans p.trans +
        commutator (omegaTorsion p.torsion) (placedOffset p x t) := by
  rw [placedBodyVelocity, placedOffset, commutator_add_right, commutator_smul_right, omegaBiv,
    motorForceBivector]
  abel

theorem right_mul_body (p : OmegaParams) (x : TransParams) (t : ℝ) :
    placedRight p x t * placedBodyVelocity p x t =
      omegaTorsion p.torsion * placedRight p x t + omegaTrans p.trans := by
  set A := omegaTorsion p.torsion
  set B := omegaTrans p.trans
  set D := placedOffset p x t
  have hV : placedBodyVelocity p x t = A + B + commutator A D := by
    simpa [A, B, D] using placedBodyVelocity_split p x t
  have hDD : D * D = 0 := placedOffset_sq p x t
  have hDB : D * B = 0 := placedOffset_mul_trans p x t
  have hDAD : D * A * D = 0 := placedOffset_mul_mul p x t A
  rw [placedRight, hV]
  have hcomm : commutator A D = A * D - D * A := rfl
  rw [hcomm]
  have hDA : D * (A * D) = 0 := by simpa [mul_assoc] using hDAD
  have hDDA : D * (D * A) = 0 := by rw [← mul_assoc, hDD, zero_mul]
  calc
    (1 + D) * (A + B + (A * D - D * A))
        = A + B + (A * D - D * A) + D * (A + B + (A * D - D * A)) := by
          rw [add_mul, one_mul]
      _ = A + B + A * D - D * A + (D * A + D * B + D * (A * D) - D * (D * A)) := by
          have hsub : A + B + (A * D - D * A) = A + B + A * D - D * A := by abel
          rw [hsub, mul_sub, mul_add, mul_add]
      _ = A + B + A * D - D * A + (D * A + 0 + 0 - 0) := by rw [hDB, hDA, hDDA]
      _ = A + B + A * D := by abel
      _ = A * (1 + D) + B := by
          rw [mul_add, mul_one]
          abel

theorem hasDerivAt_placedPath (p : OmegaParams) (x : TransParams) (t : ℝ) :
    HasDerivAt (placedPath p x)
      (exp (t • omegaTorsion p.torsion) *
        (omegaTorsion p.torsion * placedRight p x t + omegaTrans p.trans)) t := by
  have hL := hasDerivAt_exp_smul_const (omegaTorsion p.torsion) t
  have hR : HasDerivAt (placedRight p x) (omegaTrans p.trans) t := by
    have hlin : HasDerivAt (fun u : ℝ => u • omegaTrans p.trans) (omegaTrans p.trans) t := by
      simpa using (hasDerivAt_id t).smul_const (omegaTrans p.trans)
    have hfun : placedRight p x =
        (fun _ : ℝ => (1 : PGA) + omegaTrans x) + fun u => u • omegaTrans p.trans := by
      ext u
      simp [placedRight, placedOffset, add_assoc]
    rw [hfun]
    exact (hlin.const_add ((1 : PGA) + omegaTrans x))
  have hfun : placedPath p x =
      (fun u => exp (u • omegaTorsion p.torsion)) * placedRight p x := by
    ext u
    rfl
  rw [hfun]
  refine ((hL.mul hR).congr_deriv ?_)
  set A := omegaTorsion p.torsion
  set B := omegaTrans p.trans
  calc
    (exp (t • A) * A) * placedRight p x t + exp (t • A) * B
        = exp (t • A) * (A * placedRight p x t + B) := by rw [mul_assoc, ← mul_add]

theorem deriv_placedPath_body (p : OmegaParams) (x : TransParams) (t : ℝ) :
    deriv (placedPath p x) t = placedPath p x t * placedBodyVelocity p x t := by
  rw [(hasDerivAt_placedPath p x t).deriv, placedPath, ← right_mul_body, ← mul_assoc]

theorem placedBodyVelocity_eq_pull (p : OmegaParams) (x : TransParams) (t : ℝ) :
    reverse (placedPath p x t) * deriv (placedPath p x) t = placedBodyVelocity p x t := by
  rw [deriv_placedPath_body, ← mul_assoc,
    reverse_mul_of_mul_reverse (placedPath_unitary p x t), one_mul]

theorem hasDerivAt_placedBodyVelocity (p : OmegaParams) (x : TransParams) (t : ℝ) :
    HasDerivAt (placedBodyVelocity p x) (motorForceBivector p) t := by
  have hconst : HasDerivAt
      (fun _ : ℝ => omegaBiv p + commutator (omegaTorsion p.torsion) (omegaTrans x)) 0 t :=
    hasDerivAt_const t _
  have hlin : HasDerivAt (fun s : ℝ => s • motorForceBivector p) (motorForceBivector p) t := by
    simpa using (hasDerivAt_id t).smul_const (motorForceBivector p)
  refine ((hconst.add hlin).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun s => ?_)).congr_deriv (by simp)
  simp [placedBodyVelocity, add_assoc]

/-- The force along a placed motor is the commutator of the torsion with the velocity translator.
The initial translator does not enter. -/
theorem deriv_placedBodyVelocity (p : OmegaParams) (x : TransParams) :
    deriv (placedBodyVelocity p x) = fun _ => motorForceBivector p := by
  ext t
  exact (hasDerivAt_placedBodyVelocity p x t).deriv

theorem placed_force_ignores_offset (p : OmegaParams) (x : TransParams) (t : ℝ) :
    deriv (placedBodyVelocity p x) t = deriv (motorBodyVelocity p) t := by
  rw [deriv_placedBodyVelocity, MotorForce.deriv_motorBodyVelocity]

/-! ### Two parameters of one path are not two positions -/

/-- Translator of the motor that joins parameter `s` to parameter `t` on `boostShift`. -/
def joiningLambda (s t : ℝ) : Vec4 :=
  ![s * Real.sinh (t - s), t - s * Real.cosh (t - s), 0, 0]

theorem boostShift_omegaTrans :
    omegaTrans boostShift.trans = (1 / 2 : ℝ) • null 1 := by
  simp only [omegaTrans, boostShift, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three]
  simp

theorem exp_boostShift_gap (s t : ℝ) :
    exp ((t - s) • omegaTorsion boostShift.torsion) = rotorTorsion (pureBoost (t - s)) := by
  have hA : omegaTorsion boostShift.torsion = (1 / 2 : ℝ) • hyperbolic 0 := by
    simpa [boostShift] using omegaTorsion_pureBoost 1
  rw [hA, smul_smul, rotorTorsion_pureBoost]
  congr 1
  ring_nf

theorem sandwich_gap_shift (s t : ℝ) :
    sandwich (rotorTorsion (pureBoost (s - t))) (omegaTrans boostShift.trans) =
      omegaTrans ⟨![Real.sinh (s - t), Real.cosh (s - t), 0, 0]⟩ := by
  rw [boostShift_omegaTrans, sandwich_smul, sandwich_pureBoost_null1]
  have hhalf : (1 / 2 : ℝ) • (Real.sinh (s - t) • null 0 + Real.cosh (s - t) • null 1) =
      (Real.sinh (s - t) / 2) • null 0 + (Real.cosh (s - t) / 2) • null 1 := by
    rw [smul_add, smul_smul, smul_smul]
    ring_nf
  rw [hhalf]
  simp only [omegaTrans, Fin.sum_univ_four]
  simp [div_eq_mul_inv]

theorem between_boostShift (s t : ℝ) :
    between (motorPath boostShift s) (motorPath boostShift t) =
      rotorTorsion (pureBoost (t - s)) * (1 + omegaTrans ⟨joiningLambda s t⟩) := by
  set A := omegaTorsion boostShift.torsion
  set B := omegaTrans boostShift.trans
  have hs : motorPath boostShift s = exp (s • A) * (1 + s • B) := by
    simpa [A, B] using motorPath_factor boostShift s
  have ht : motorPath boostShift t = exp (t • A) * (1 + t • B) := by
    simpa [A, B] using motorPath_factor boostShift t
  have hc : Commute ((-s) • A) (t • A) := ((Commute.refl A).smul_left (-s)).smul_right t
  have hgap : exp ((-s) • A) * exp (t • A) = exp ((t - s) • A) := by
    rw [← exp_add_of_commute hc]
    congr 1
    rw [← add_smul]
    ring_nf
  have hrot : exp ((t - s) • A) = rotorTorsion (pureBoost (t - s)) := by
    simpa [A] using exp_boostShift_gap s t
  have hrev : reverse (exp (s • A)) = exp ((-s) • A) := by
    simpa [A, neg_smul] using reverse_exp_torsion boostShift.torsion s
  have hrevB : reverse (1 + s • B) = 1 - s • B := by
    have hB : reverse B = -B := by simpa [B] using reverse_omegaTrans boostShift.trans
    rw [CliffordAlgebra.reverse.map_add, CliffordAlgebra.reverse.map_one, map_smul, hB, smul_neg,
      sub_eq_add_neg]
  have hBRB : B * exp ((t - s) • A) * B = 0 := by
    simpa [B] using omegaTrans_mul_mul boostShift.trans (exp ((t - s) • A))
  have hunit : exp ((t - s) • A) * reverse (exp ((t - s) • A)) = 1 := by
    rw [hrot]
    exact rotor_unitary (pureBoost (t - s))
  have hsandwich : reverse (exp ((t - s) • A)) * B * exp ((t - s) • A) =
      sandwich (reverse (exp ((t - s) • A))) B := by
    rw [sandwich, reverse_reverse]
  rw [hs, ht, between, CliffordAlgebra.reverse.map_mul, hrev, hrevB]
  have hslide : B * exp ((t - s) • A) =
      exp ((t - s) • A) * (reverse (exp ((t - s) • A)) * B * exp ((t - s) • A)) := by
    calc
      B * exp ((t - s) • A)
          = 1 * (B * exp ((t - s) • A)) := by
            conv_lhs => rw [← one_mul (B * exp ((t - s) • A))]
        _ = (exp ((t - s) • A) * reverse (exp ((t - s) • A))) * (B * exp ((t - s) • A)) := by
            conv_lhs => rw [← hunit]
        _ = exp ((t - s) • A) * (reverse (exp ((t - s) • A)) * (B * exp ((t - s) • A))) := by
            rw [mul_assoc]
        _ = exp ((t - s) • A) * (reverse (exp ((t - s) • A)) * B * exp ((t - s) • A)) := by
            rw [← mul_assoc (reverse (exp ((t - s) • A))) B]
  have hpull : (s • B) * exp ((t - s) • A) =
      exp ((t - s) • A) * (s • (reverse (exp ((t - s) • A)) * B * exp ((t - s) • A))) := by
    calc
      (s • B) * exp ((t - s) • A) = s • (B * exp ((t - s) • A)) := by rw [smul_mul_assoc]
      _ = s • (exp ((t - s) • A) * (reverse (exp ((t - s) • A)) * B * exp ((t - s) • A))) := by
          rw [hslide]
      _ = exp ((t - s) • A) * (s • (reverse (exp ((t - s) • A)) * B * exp ((t - s) • A))) := by
          rw [← mul_smul_comm]
  -- Rebuild the product once the rotor has been slid left.
  calc
    (1 - s • B) * exp ((-s) • A) * (exp (t • A) * (1 + t • B))
        = (1 - s • B) * (exp ((-s) • A) * exp (t • A) * (1 + t • B)) := by
          rw [mul_assoc, ← mul_assoc (exp ((-s) • A)) (exp (t • A))]
      _ = (1 - s • B) * (exp ((t - s) • A) * (1 + t • B)) := by rw [hgap]
      _ = (1 - s • B) * (exp ((t - s) • A) + t • (exp ((t - s) • A) * B)) := by
          rw [mul_add, mul_one, mul_smul_comm]
      _ = exp ((t - s) • A) + t • (exp ((t - s) • A) * B) -
            ((s • B) * exp ((t - s) • A) + (s • B) * (t • (exp ((t - s) • A) * B))) := by
          rw [sub_mul, one_mul, mul_add]
      _ = exp ((t - s) • A) + t • (exp ((t - s) • A) * B) - (s • B) * exp ((t - s) • A) := by
          have hkill : (s • B) * (t • (exp ((t - s) • A) * B)) = 0 := by
            rw [smul_mul_assoc, mul_smul_comm, smul_smul, ← mul_assoc, hBRB, smul_zero]
          rw [hkill, add_zero]
      _ = exp ((t - s) • A) * (1 + t • B) -
            exp ((t - s) • A) *
              (s • (reverse (exp ((t - s) • A)) * B * exp ((t - s) • A))) := by
          rw [hpull]
          congr 1
          rw [mul_add, mul_one, mul_smul_comm]
      _ = exp ((t - s) • A) *
            (1 + t • B - s • (reverse (exp ((t - s) • A)) * B * exp ((t - s) • A))) := by
          rw [← mul_sub]
      _ = rotorTorsion (pureBoost (t - s)) *
            (1 + t • B - s • sandwich (reverse (rotorTorsion (pureBoost (t - s)))) B) := by
          rw [hsandwich, hrot]
      _ = rotorTorsion (pureBoost (t - s)) *
            (1 + omegaTrans ⟨joiningLambda s t⟩) := by
          have hrevR : reverse (rotorTorsion (pureBoost (t - s))) =
              rotorTorsion (pureBoost (s - t)) := by
            rw [← hrot]
            have hneg : reverse (exp ((t - s) • A)) = exp (-((t - s) • A)) := by
              simpa [A, neg_smul] using reverse_exp_torsion boostShift.torsion (t - s)
            rw [hneg]
            have hsmul : -((t - s) • A) = (s - t) • A := by
              rw [← neg_smul, neg_sub]
            rw [hsmul]
            simpa [A] using exp_boostShift_gap t s
          rw [hrevR]
          have hsandwichB := sandwich_gap_shift s t
          have hsub : t • B - s • sandwich (rotorTorsion (pureBoost (s - t))) B =
              omegaTrans ⟨joiningLambda s t⟩ := by
            rw [hsandwichB]
            have htB : t • B = omegaTrans ⟨![0, t, 0, 0]⟩ := by
              rw [show B = omegaTrans boostShift.trans from rfl, omegaTrans_smul_lambda]
              exact omegaTrans_eq_of_lambda fun μ => by fin_cases μ <;> simp [boostShift]
            have hsB : s • omegaTrans ⟨![Real.sinh (s - t), Real.cosh (s - t), 0, 0]⟩ =
                omegaTrans ⟨![s * Real.sinh (s - t), s * Real.cosh (s - t), 0, 0]⟩ := by
              rw [omegaTrans_smul_lambda]
              exact omegaTrans_eq_of_lambda fun μ => by fin_cases μ <;> simp
            rw [htB, hsB, omegaTrans_sub]
            exact omegaTrans_eq_of_lambda fun μ => by
              fin_cases μ
              · simp only [joiningLambda, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, zero_sub]
                rw [← neg_sub t s, Real.sinh_neg]
                ring
              · rw [joiningLambda]
                change t - s * Real.cosh (s - t) = t - s * Real.cosh (t - s)
                rw [show Real.cosh (s - t) = Real.cosh (t - s) by
                  rw [show s - t = -(t - s) by ring, Real.cosh_neg]]
              · simp [joiningLambda]
              · simp [joiningLambda]
          rw [show (1 : PGA) + t • B -
                s • sandwich (rotorTorsion (pureBoost (s - t))) B =
                1 + (t • B - s • sandwich (rotorTorsion (pureBoost (s - t))) B) by abel,
            hsub]

/-- The witness coefficients at parameters `1` and `2` differ by a pure spatial step. The
translator that joins those events has a nonzero time coefficient. -/
theorem witness_difference_ne_joining :
    (fun μ => translatorCoefficient boostShift 2 μ - translatorCoefficient boostShift 1 μ) ≠
      joiningLambda 1 2 := by
  intro h
  have h0 := congrFun h 0
  have hsinh : Real.sinh 1 ≠ 0 := by
    intro hz
    exact one_ne_zero (Real.sinh_eq_zero.mp hz)
  have hcoeff :
      translatorCoefficient boostShift 2 0 - translatorCoefficient boostShift 1 0 = 0 := by
    simp [translatorCoefficient, boostShift]
  have hjoin : joiningLambda 1 2 0 = Real.sinh (2 - 1) := by
    simp [joiningLambda]
  rw [hcoeff, hjoin] at h0
  rw [show (2 : ℝ) - 1 = 1 by norm_num] at h0
  exact hsinh h0.symm

end DoubleSpacetime.Gravity.RelationalMotor
