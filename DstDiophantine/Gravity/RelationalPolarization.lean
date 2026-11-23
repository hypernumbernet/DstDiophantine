import DstDiophantine.Gravity.RelationalPosition
import DstDiophantine.Gravity.RestMass
import DstDiophantine.Gravity.TorsionalLayer
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Polarization along the relative rotor

Two charges are labels on one axis. Their interaction is the cross term of the
written stiffness, evaluated at the geodesic angle of the relative rotor
`ρ(a,b) = a⁻¹b`. That angle is not a chart coordinate, not an eigenvalue of a
position operator, and not the intra-particle mismatch. The dual spinor space
does not carry the canonical pair, a plane wave is not a position eigenfield,
and the singlet, whose total spin squared vanishes, is not this pair of
elements.

Holding the usual rapidity at zero remains a constraint. The derivative of the
polarization in the geodesic angle is not an Euler–Lagrange force. For like
charges the polarization grows with the angle. No length `ℓ` enters, no Coulomb
law is claimed, and no binding energy is assigned.

On the equal-scale locus `J` vanishes while `γ_s` changes sign, so the shells
whose denominator is `γ_s` are not this polarization. On a diameter the
electron–electron angle is twice the nuclear angle, the coefficient is `4 - Z`,
and the angle derivative vanishes throughout `(0, π/2)` exactly when `Z = 4`.
-/

namespace DstDiophantine

namespace Gravity

open Quaternion Real RelationalPosition RelativeRotor Invariant

noncomputable section

/-! ### The equal-scale clock is not the mismatch -/

/-- On one axis the equal-scale mismatch vanishes. -/
theorem equalScale_J_zero (t : ℝ) : J (axisParams t t) = 0 :=
  J_axisParams_balanced t

/-- `γ_s` changes sign between two equal-scale states that share `J = 0`. -/
theorem equalScale_clock_not_mismatch :
    J (axisParams (2 * π) (2 * π)) = 0 ∧ gammaSEqual π < 0 ∧
      J (axisParams 0 0) = 0 ∧ gammaSEqual 0 = 1 := by
  refine ⟨equalScale_J_zero _, ?_, equalScale_J_zero _, gammaSEqual_zero⟩
  have h := gammaSEqual_nat_mul_pi 1
  simp only [Nat.cast_one, one_mul, pow_one] at h
  rw [h]
  linarith [cosh_pos π]

/-! ### Charge-sourced dual rapidity -/

/-- Dual rapidity `q φ` on one axis, with the usual rapidity held at rest. -/
def dualSourced (q φ : ℝ) : Operations.TorsionParams :=
  axisParams 0 (q * φ)

/-- Pure dual stiffness is `-m J`. -/
theorem stiffness_eq_neg_mul_J_of_usual_zero (m β : ℝ) :
    stiffnessPotential m (axisParams 0 β) = -m * J (axisParams 0 β) := by
  rw [stiffness_axis, J_axisParams]
  ring

/-- Stiffness of the summed charges, minus the two separate stiffnesses. -/
noncomputable def interactionStiffness (m q1 q2 φ : ℝ) : ℝ :=
  stiffnessPotential m (dualSourced (q1 + q2) φ) -
    stiffnessPotential m (dualSourced q1 φ) -
    stiffnessPotential m (dualSourced q2 φ)

theorem interactionStiffness_eq (m q1 q2 φ : ℝ) :
    interactionStiffness m q1 q2 φ = m * q1 * q2 * φ ^ 2 := by
  unfold interactionStiffness dualSourced
  rw [stiffness_axis, stiffness_axis, stiffness_axis]
  ring

/-- Polarization `J(p + q) - J(p) - J(q)` of two pure dual charges. -/
noncomputable def interactionJ (q1 q2 φ : ℝ) : ℝ :=
  J (dualSourced (q1 + q2) φ) - J (dualSourced q1 φ) - J (dualSourced q2 φ)

theorem interactionJ_eq (q1 q2 φ : ℝ) :
    interactionJ q1 q2 φ = -(q1 * q2 * φ ^ 2) := by
  unfold interactionJ dualSourced
  rw [J_axisParams, J_axisParams, J_axisParams]
  ring

theorem interactionStiffness_eq_neg_mul_interactionJ (m q1 q2 φ : ℝ) :
    interactionStiffness m q1 q2 φ = -m * interactionJ q1 q2 φ := by
  rw [interactionStiffness_eq, interactionJ_eq]
  ring

/-! ### Unsigned mass of the sourced state does not carry `m` -/

theorem mass_dualSourced (q φ : ℝ) :
    mass (dualSourced q φ) = (1 / 2) * (q * φ) ^ 2 := by
  unfold dualSourced
  rw [mass_axisParams]
  ring

/-- Polarization of the unsigned mass of two pure dual charges. -/
noncomputable def interactionMass (q1 q2 φ : ℝ) : ℝ :=
  mass (dualSourced (q1 + q2) φ) - mass (dualSourced q1 φ) - mass (dualSourced q2 φ)

theorem interactionMass_eq (q1 q2 φ : ℝ) :
    interactionMass q1 q2 φ = q1 * q2 * φ ^ 2 := by
  unfold interactionMass
  rw [mass_dualSourced, mass_dualSourced, mass_dualSourced]
  ring

theorem interactionStiffness_eq_mul_interactionMass (m q1 q2 φ : ℝ) :
    interactionStiffness m q1 q2 φ = m * interactionMass q1 q2 φ := by
  rw [interactionStiffness_eq, interactionMass_eq]
  ring

/-! ### A frozen usual rapidity is a constraint -/

/-- Vanishing velocities give vanishing momenta, and the Jacobi integral equals the stiffness. -/
theorem dualSourced_rest_reads (m q φ : ℝ) :
    paperMomentumSigma 0 0 = 0 ∧ paperMomentumDelta 0 0 = 0 ∧
      paperEnergy m 0 (q * φ) 0 0 = stiffnessPotential m (dualSourced q φ) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [paperMomentumSigma]
  · simp [paperMomentumDelta]
  · rw [paperEnergy, dualSourced, stiffness_axis]
    ring

/-- Nonzero stiffness and a nonzero dual rapidity are not a free solution at usual rapidity zero. -/
theorem dualSourced_not_actualEL {m q φ : ℝ} (hm : m ≠ 0) (hβ : q * φ ≠ 0) :
    ¬ PaperActualEL m 0 (q * φ) 0 0 := by
  intro h
  have hφ := ((paperActualEL_eq m 0 (q * φ) 0 0).mp h).1
  have hzero : m * (q * φ) = 0 := by
    have : -m * (0 - q * φ) = m * (q * φ) := by ring
    linarith
  exact hβ ((mul_eq_zero.mp hzero).resolve_left hm)

/-- Both-channel forces `v = u = -m q φ` cancel both accelerations. -/
theorem dualSourced_both_constrained (m q φ : ℝ) :
    PaperBothSourcedEL m 0 (q * φ) 0 0 (-m * (q * φ)) (-m * (q * φ)) := by
  constructor <;> ring

/-- At vanishing velocities the constraint does no work. -/
theorem dualSourced_constraint_powerless (m q φ : ℝ) :
    paperEnergyDot m 0 (q * φ) 0 0 0 0 = 0 := by
  have h :=
    paperEnergyDot_rest_usual (θdot := 0) (dualSourced_both_constrained m q φ) rfl
  simpa using h

/-! ### The geodesic angle is the argument of the polarization -/

/-- Stiffness cross term at the geodesic angle of `ρ(a,b)`. -/
noncomputable def relationalPolarization (m q1 q2 : ℝ) (a b : S3) : ℝ :=
  interactionStiffness m q1 q2 (separation a b)

theorem relationalPolarization_eq (m q1 q2 : ℝ) (a b : S3) :
    relationalPolarization m q1 q2 a b = m * q1 * q2 * (separation a b) ^ 2 := by
  unfold relationalPolarization
  rw [interactionStiffness_eq]

theorem relationalPolarization_left (m q1 q2 : ℝ) (g a b : S3) :
    relationalPolarization m q1 q2 (g * a) (g * b) = relationalPolarization m q1 q2 a b := by
  unfold relationalPolarization
  rw [separation_left]

theorem relationalPolarization_right (m q1 q2 : ℝ) (a b h : S3) :
    relationalPolarization m q1 q2 (a * h) (b * h) = relationalPolarization m q1 q2 a b := by
  unfold relationalPolarization
  rw [separation_right]

/-- Derivative of the polarization in the geodesic angle. Not an Euler–Lagrange force. -/
def polarizationAngleDeriv (m q1 q2 θ : ℝ) : ℝ :=
  2 * m * q1 * q2 * θ

theorem hasDerivAt_interactionStiffness (m q1 q2 θ : ℝ) :
    HasDerivAt (fun t : ℝ => interactionStiffness m q1 q2 t)
      (polarizationAngleDeriv m q1 q2 θ) θ := by
  have hpow : HasDerivAt (fun t : ℝ => t ^ 2) (2 * θ) θ := by
    simpa [pow_one] using hasDerivAt_pow 2 θ
  have h := hpow.const_mul (m * q1 * q2)
  have hfun : (fun t : ℝ => (m * q1 * q2) * t ^ 2) = fun t => interactionStiffness m q1 q2 t := by
    ext t
    rw [interactionStiffness_eq]
  have hder : (m * q1 * q2) * (2 * θ) = polarizationAngleDeriv m q1 q2 θ := by
    unfold polarizationAngleDeriv
    ring
  rw [← hfun]
  exact h.congr_deriv hder

/-- For like charges the polarization grows with the angle. -/
theorem polarizationAngleDeriv_pos_of_like {m q1 q2 θ : ℝ}
    (hm : 0 < m) (hq : 0 < q1 * q2) (hθ : 0 < θ) :
    0 < polarizationAngleDeriv m q1 q2 θ := by
  have hpos : 0 < 2 * m * θ := by positivity
  have hfac : polarizationAngleDeriv m q1 q2 θ = (2 * m * θ) * (q1 * q2) := by
    unfold polarizationAngleDeriv
    ring
  rw [hfac]
  exact mul_pos hpos hq

/-- At unit data the usual-channel constraint is `-1` and the angle derivative is `2`. -/
theorem unit_usualConstraint_ne_angleDeriv :
    -((1 : ℝ) * (1 * 1)) ≠ polarizationAngleDeriv 1 1 1 1 := by
  unfold polarizationAngleDeriv
  norm_num

/-! ### Diameter: opposite elements on one axis -/

/-- Direction opposite `axis0`. -/
def oppositeAxis : SlerpTorque.V3 :=
  fun i => -axis0 i

theorem oppositeAxis_unit : SlerpTorque.dot3 oppositeAxis oppositeAxis = 1 := by
  simp [SlerpTorque.dot3, oppositeAxis, axis0]

/-- Electron opposite `bodyElem χ` through the identity. -/
def oppositeElem (χ : ℝ) : S3 :=
  elem χ oppositeAxis oppositeAxis_unit

theorem bodyElem_re (χ : ℝ) : (bodyElem χ).val.re = Real.cos χ := by
  simp [bodyElem, elem, liftQuat, axis0]

theorem oppositeElem_re (χ : ℝ) : (oppositeElem χ).val.re = Real.cos χ := by
  simp [oppositeElem, elem, liftQuat, oppositeAxis, axis0]

theorem separation_nucleus_body {χ : ℝ} (hχ : 0 ≤ χ) (hχu : χ ≤ π / 2) :
    separation 1 (bodyElem χ) = χ := by
  have hpi : χ ≤ π := by linarith [pi_pos]
  have hrel : relative 1 (bodyElem χ) = bodyElem χ := by
    apply S3.ext
    simp [relative_val, one_val, bodyElem, elem, star_one, one_mul]
  rw [separation, hrel, bodyElem_re, arccos_cos hχ hpi]

theorem separation_nucleus_opposite {χ : ℝ} (hχ : 0 ≤ χ) (hχu : χ ≤ π / 2) :
    separation 1 (oppositeElem χ) = χ := by
  have hpi : χ ≤ π := by linarith [pi_pos]
  have hrel : relative 1 (oppositeElem χ) = oppositeElem χ := by
    apply S3.ext
    simp [relative_val, one_val, oppositeElem, elem, star_one, one_mul]
  rw [separation, hrel, oppositeElem_re, arccos_cos hχ hpi]

theorem opposite_pair_re (χ : ℝ) :
    (relative (bodyElem χ) (oppositeElem χ)).val.re = Real.cos (2 * χ) := by
  rw [relative_val]
  simp only [bodyElem, oppositeElem, elem, liftQuat, axis0, oppositeAxis, re_mul, re_star,
    imI_star, imJ_star, imK_star, mul_one, mul_zero, neg_zero]
  rw [cos_two_mul]
  have hsq := sin_sq_add_cos_sq χ
  linarith

theorem separation_opposite {χ : ℝ} (hχ : 0 ≤ χ) (hχu : χ ≤ π / 2) :
    separation (bodyElem χ) (oppositeElem χ) = 2 * χ := by
  have h0 : 0 ≤ 2 * χ := by linarith
  have hpi : 2 * χ ≤ π := by linarith
  rw [separation, opposite_pair_re, arccos_cos h0 hpi]

/-- Polarization of a nucleus of charge `Z` and two opposite electrons, in the geodesic angle. -/
noncomputable def diameterPolarization (m Z χ : ℝ) : ℝ :=
  interactionStiffness m (-1) Z χ + interactionStiffness m (-1) (-1) (2 * χ)

theorem diameterPolarization_eq (m Z χ : ℝ) :
    diameterPolarization m Z χ = m * χ ^ 2 * (4 - Z) := by
  unfold diameterPolarization
  rw [interactionStiffness_eq, interactionStiffness_eq]
  ring

theorem diameterPolarization_of_elements {m Z χ : ℝ} (hχ : 0 ≤ χ) (hχu : χ ≤ π / 2) :
    diameterPolarization m Z χ =
      relationalPolarization m (-1) Z 1 (bodyElem χ) +
        relationalPolarization m (-1) (-1) (bodyElem χ) (oppositeElem χ) := by
  unfold relationalPolarization diameterPolarization
  rw [separation_nucleus_body hχ hχu, separation_opposite hχ hχu]

/-- Derivative of `diameterPolarization` in the nuclear angle. -/
def diameterAngleDeriv (m Z χ : ℝ) : ℝ :=
  2 * m * (4 - Z) * χ

theorem hasDerivAt_diameterPolarization (m Z χ : ℝ) :
    HasDerivAt (fun t : ℝ => diameterPolarization m Z t) (diameterAngleDeriv m Z χ) χ := by
  have hpow : HasDerivAt (fun t : ℝ => t ^ 2) (2 * χ) χ := by
    simpa [pow_one] using hasDerivAt_pow 2 χ
  have h := hpow.const_mul (m * (4 - Z))
  have hfun : (fun t : ℝ => (m * (4 - Z)) * t ^ 2) = fun t => diameterPolarization m Z t := by
    ext t
    rw [diameterPolarization_eq]
    ring
  have hder : (m * (4 - Z)) * (2 * χ) = diameterAngleDeriv m Z χ := by
    unfold diameterAngleDeriv
    ring
  rw [← hfun]
  exact h.congr_deriv hder

theorem diameterAngleDeriv_eq_zero_iff {m Z χ : ℝ} (hm : m ≠ 0) (hχ : χ ≠ 0) :
    diameterAngleDeriv m Z χ = 0 ↔ Z = 4 := by
  unfold diameterAngleDeriv
  have hassoc : 2 * m * (4 - Z) * χ = (2 * χ * m) * (4 - Z) := by ring
  rw [hassoc, mul_eq_zero]
  constructor
  · intro h
    rcases h with hprod | hZ
    · have h2χ : 2 * χ ≠ 0 := mul_ne_zero (by norm_num) hχ
      exact absurd hprod (mul_ne_zero h2χ hm)
    · linarith
  · intro hZ
    exact Or.inr (by linarith)

theorem diameterAngleDeriv_zero_of_four (m χ : ℝ) : diameterAngleDeriv m 4 χ = 0 := by
  unfold diameterAngleDeriv
  ring

theorem diameterAngleDeriv_ne_zero_of_one {m χ : ℝ} (hm : m ≠ 0) (hχ : χ ≠ 0) :
    diameterAngleDeriv m 1 χ ≠ 0 := by
  intro h0
  have hZ : (1 : ℝ) = 4 := (diameterAngleDeriv_eq_zero_iff hm hχ).1 h0
  norm_num at hZ

/-- A root in `(0, π/2)` exists exactly when `Z = 4`, and then every such angle is a root. -/
theorem diameter_one_root_iff {m Z : ℝ} (hm : m ≠ 0) :
    (∃ χ : ℝ, 0 < χ ∧ χ < π / 2 ∧ diameterAngleDeriv m Z χ = 0) ↔ Z = 4 := by
  constructor
  · rintro ⟨χ, hχ, _, h0⟩
    exact (diameterAngleDeriv_eq_zero_iff hm hχ.ne').1 h0
  · intro hZ
    refine ⟨π / 4, div_pos pi_pos (by norm_num), ?_, ?_⟩
    · linarith [pi_pos]
    · exact (diameterAngleDeriv_eq_zero_iff hm (div_pos pi_pos (by norm_num)).ne').2 hZ

theorem diameter_all_angles_iff {m Z : ℝ} (hm : m ≠ 0) :
    (∀ χ : ℝ, 0 < χ → χ < π / 2 → diameterAngleDeriv m Z χ = 0) ↔ Z = 4 := by
  constructor
  · intro h
    exact (diameter_one_root_iff hm).1
      ⟨π / 4, div_pos pi_pos (by norm_num), by linarith [pi_pos],
        h (π / 4) (div_pos pi_pos (by norm_num)) (by linarith [pi_pos])⟩
  · intro hZ χ hχ _
    exact (diameterAngleDeriv_eq_zero_iff hm hχ.ne').2 hZ

end

end Gravity

end DstDiophantine
