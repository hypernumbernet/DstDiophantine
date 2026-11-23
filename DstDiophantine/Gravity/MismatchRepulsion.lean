import DstDiophantine.Gravity.RestMass
import DstDiophantine.Gravity.TorsionalLayer
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Repulsion from the torsional mismatch

A charge held at usual rapidity zero sources a dual rapidity `q φ` on the
joining axis. Both charges are labels on that one axis, so the configuration
has one pair of conjugate momenta. The hold is a constraint: with `m ≠ 0` and
`q φ ≠ 0` it is not a free solution of the written Euler–Lagrange equations.
The interaction is the cross term of the written stiffness, equivalently the
polarization of `J`. Its separation-increasing derivative is the force. The
profile `φ(s) = ℓ/s` is an input, and `ℓ` is not derived.

The coefficient `m` is the stiffness of this one configuration. The conjugate
momenta are half the mismatch rate and half the common rate, and the unsigned
mass of the sourced state is a function of the dual rapidity alone. The radial
force is the derivative of the stiffness cross term in the separation. The
usual-channel constraint that cancels the usual acceleration is a different
function of the same data.

On the equal-scale locus the mismatch vanishes while `γ_s` changes sign, so the
shells whose denominator is `γ_s` are the time-delay calculation and are not
this force. The force scales as `1/s³` and is not Coulomb's law. No binding
energy is assigned, and `J` is not read as a dimensionful coupling.
-/

namespace DstDiophantine

namespace Gravity

open Real RelativeRotor Invariant

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

/-! ### Profile `ℓ/s` and the separation-increasing force -/

/-- Input profile. The length `ℓ` is not derived. -/
noncomputable def mismatchProfile (ℓ s : ℝ) : ℝ :=
  ℓ / s

/-- Interaction stiffness at separation `s`. -/
noncomputable def mismatchPotential (m q1 q2 ℓ s : ℝ) : ℝ :=
  interactionStiffness m q1 q2 (mismatchProfile ℓ s)

theorem mismatchPotential_eq (m q1 q2 ℓ s : ℝ) :
    mismatchPotential m q1 q2 ℓ s = m * q1 * q2 * ℓ ^ 2 / s ^ 2 := by
  unfold mismatchPotential mismatchProfile
  rw [interactionStiffness_eq, div_pow, mul_div_assoc]

/-- Separation-increasing force, minus the radial derivative of `mismatchPotential`. -/
noncomputable def mismatchForce (m q1 q2 ℓ s : ℝ) : ℝ :=
  2 * m * q1 * q2 * ℓ ^ 2 / s ^ 3

theorem mismatchForce_mul_cube (m q1 q2 ℓ s : ℝ) (hs : s ≠ 0) :
    mismatchForce m q1 q2 ℓ s * s ^ 3 = 2 * m * q1 * q2 * ℓ ^ 2 := by
  unfold mismatchForce
  field_simp [hs]

theorem hasDerivAt_mismatchPotential {m q1 q2 ℓ s : ℝ} (hs : s ≠ 0) :
    HasDerivAt (fun t : ℝ => mismatchPotential m q1 q2 ℓ t) (-mismatchForce m q1 q2 ℓ s) s := by
  set c : ℝ := m * q1 * q2 * ℓ ^ 2
  have hpow : HasDerivAt (fun t : ℝ => t ^ 2) (2 * s) s := by
    simpa [pow_one] using hasDerivAt_pow 2 s
  have hinv := hpow.inv (pow_ne_zero 2 hs)
  have hconst := hinv.const_mul c
  have hfun : (fun t : ℝ => c * (t ^ 2)⁻¹) = fun t => mismatchPotential m q1 q2 ℓ t := by
    ext t
    rw [mismatchPotential_eq, div_eq_mul_inv]
  have hder : c * (-(2 * s) / (s ^ 2) ^ 2) = -mismatchForce m q1 q2 ℓ s := by
    unfold mismatchForce
    have hs2 : s ^ 2 ≠ 0 := pow_ne_zero 2 hs
    field_simp [hs, hs2]
    ring
  rw [← hfun]
  exact hconst.congr_deriv hder

theorem mismatchForce_ne_zero {m q1 q2 ℓ s : ℝ}
    (hm : m ≠ 0) (hq : q1 * q2 ≠ 0) (hℓ : ℓ ≠ 0) (hs : s ≠ 0) :
    mismatchForce m q1 q2 ℓ s ≠ 0 := by
  intro h
  have hcube := mismatchForce_mul_cube m q1 q2 ℓ s hs
  rw [h, zero_mul] at hcube
  have hzero : 2 * (m * (q1 * (q2 * ℓ ^ 2))) = 0 := by
    have hprod : 2 * m * q1 * q2 * ℓ ^ 2 = 0 := by linarith
    convert hprod using 1
    ring
  have h2 : (2 : ℝ) ≠ 0 := by norm_num
  rcases mul_eq_zero.mp hzero with htwo | hrest
  · exact absurd htwo h2
  rcases mul_eq_zero.mp hrest with hm0 | hrest
  · exact hm hm0
  rcases mul_eq_zero.mp hrest with hq1 | hrest
  · exact hq (mul_eq_zero.mpr (Or.inl hq1))
  rcases mul_eq_zero.mp hrest with hq2 | hℓ2
  · exact hq (mul_eq_zero.mpr (Or.inr hq2))
  · exact hℓ (sq_eq_zero_iff.mp hℓ2)

theorem mismatchForce_pos_of_like {m q1 q2 ℓ s : ℝ}
    (hm : 0 < m) (hq : 0 < q1 * q2) (hℓ : ℓ ≠ 0) (hs : 0 < s) :
    0 < mismatchForce m q1 q2 ℓ s := by
  have hpos : 0 < 2 * m * ℓ ^ 2 / s ^ 3 := by positivity
  have hfac : mismatchForce m q1 q2 ℓ s = (2 * m * ℓ ^ 2 / s ^ 3) * (q1 * q2) := by
    unfold mismatchForce
    ring
  rw [hfac]
  exact mul_pos hpos hq

theorem mismatchForce_neg_of_unlike {m q1 q2 ℓ s : ℝ}
    (hm : 0 < m) (hq : q1 * q2 < 0) (hℓ : ℓ ≠ 0) (hs : 0 < s) :
    mismatchForce m q1 q2 ℓ s < 0 := by
  have hpos : 0 < 2 * m * ℓ ^ 2 / s ^ 3 := by positivity
  have hfac : mismatchForce m q1 q2 ℓ s = (2 * m * ℓ ^ 2 / s ^ 3) * (q1 * q2) := by
    unfold mismatchForce
    ring
  rw [hfac]
  exact mul_neg_of_pos_of_neg hpos hq

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

/-- At unit data the usual-channel constraint is `-1` and the radial force is `2`. -/
theorem unit_usualConstraint_ne_mismatchForce :
    -((1 : ℝ) * (1 * mismatchProfile 1 1)) ≠ mismatchForce 1 1 1 1 1 := by
  unfold mismatchProfile mismatchForce
  norm_num

/-! ### Diameter: the homothetic coefficient never vanishes for `Z ≥ 1` -/

/-- Geometric weight of the diameter: the electron chord contributes `1/4`, the nucleus `-Z`. -/
noncomputable def mismatchDiameterCoeff (Z : ℝ) : ℝ :=
  1 / 4 - Z

/-- Potential of one electron: the nucleus at radius `r`, the other electron at chord `2r`. -/
noncomputable def mismatchDiameterPotential (m ℓ Z r : ℝ) : ℝ :=
  mismatchPotential m (-1) Z ℓ r + mismatchPotential m (-1) (-1) ℓ (2 * r)

theorem mismatchDiameterPotential_eq {m ℓ Z r : ℝ} (hr : r ≠ 0) :
    mismatchDiameterPotential m ℓ Z r = m * ℓ ^ 2 / r ^ 2 * mismatchDiameterCoeff Z := by
  unfold mismatchDiameterPotential mismatchDiameterCoeff
  rw [mismatchPotential_eq, mismatchPotential_eq]
  have hr2 : (2 * r) ^ 2 ≠ 0 := pow_ne_zero 2 (mul_ne_zero (by norm_num) hr)
  have hr1 : r ^ 2 ≠ 0 := pow_ne_zero 2 hr
  field_simp [hr1, hr2]
  ring

/-- Radial force conjugate to the homothetic radius. -/
noncomputable def mismatchDiameterForce (m ℓ Z r : ℝ) : ℝ :=
  2 * m * ℓ ^ 2 * mismatchDiameterCoeff Z / r ^ 3

theorem mismatchDiameterCoeff_neg_of_one {Z : ℝ} (hZ : 1 ≤ Z) : mismatchDiameterCoeff Z < 0 := by
  unfold mismatchDiameterCoeff
  linarith

theorem mismatchDiameterForce_eq_zero_iff {m ℓ Z r : ℝ} (hr : r ≠ 0) :
    mismatchDiameterForce m ℓ Z r = 0 ↔ m = 0 ∨ ℓ = 0 ∨ mismatchDiameterCoeff Z = 0 := by
  unfold mismatchDiameterForce
  have hr3 : r ^ 3 ≠ 0 := pow_ne_zero 3 hr
  rw [div_eq_zero_iff, or_iff_left hr3]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with hleft | hZ
    · rcases mul_eq_zero.mp hleft with h2m | hℓ
      · rcases mul_eq_zero.mp h2m with htwo | hm
        · exact absurd htwo (by norm_num)
        · exact Or.inl hm
      · exact Or.inr (Or.inl (sq_eq_zero_iff.mp hℓ))
    · exact Or.inr (Or.inr hZ)
  · rintro (hm | hℓ | hZ)
    · simp [hm]
    · simp [hℓ]
    · simp [hZ]

theorem hasDerivAt_mismatchDiameterPotential {m ℓ Z r : ℝ} (hr : r ≠ 0) :
    HasDerivAt (fun t : ℝ => mismatchDiameterPotential m ℓ Z t)
      (-mismatchDiameterForce m ℓ Z r) r := by
  have hr2 : 2 * r ≠ 0 := mul_ne_zero (by norm_num) hr
  have h1 := hasDerivAt_mismatchPotential (m := m) (q1 := -1) (q2 := Z) (ℓ := ℓ) hr
  have hpair := hasDerivAt_mismatchPotential (m := m) (q1 := -1) (q2 := -1) (ℓ := ℓ) hr2
  have hlin : HasDerivAt (fun t : ℝ => 2 * t) 2 r := by
    simpa using (hasDerivAt_id r).const_mul 2
  have h2 := hpair.comp r hlin
  have hsum := h1.add h2
  have hder :
      -mismatchForce m (-1) Z ℓ r + -mismatchForce m (-1) (-1) ℓ (2 * r) * 2 =
        -mismatchDiameterForce m ℓ Z r := by
    unfold mismatchForce mismatchDiameterForce mismatchDiameterCoeff
    have hr3 : r ^ 3 ≠ 0 := pow_ne_zero 3 hr
    have h8 : (2 * r) ^ 3 ≠ 0 := pow_ne_zero 3 hr2
    field_simp [hr3, h8]
    ring
  exact hsum.congr_deriv hder

/-- A root at one positive radius is a root at every positive radius. -/
theorem diameter_root_iff_coeff {m ℓ Z : ℝ} (hm : m ≠ 0) (hℓ : ℓ ≠ 0) :
    (∃ r : ℝ, 0 < r ∧ mismatchDiameterForce m ℓ Z r = 0) ↔ mismatchDiameterCoeff Z = 0 := by
  constructor
  · rintro ⟨r, hr, h0⟩
    rcases (mismatchDiameterForce_eq_zero_iff hr.ne').1 h0 with hm0 | hℓ0 | hZ
    · exact absurd hm0 hm
    · exact absurd hℓ0 hℓ
    · exact hZ
  · intro hZ
    refine ⟨1, by norm_num, ?_⟩
    exact (mismatchDiameterForce_eq_zero_iff (by norm_num)).2 (Or.inr (Or.inr hZ))

theorem diameter_force_all_radii_iff {m ℓ Z : ℝ} (hm : m ≠ 0) (hℓ : ℓ ≠ 0) :
    (∀ r : ℝ, 0 < r → mismatchDiameterForce m ℓ Z r = 0) ↔ mismatchDiameterCoeff Z = 0 := by
  constructor
  · intro h
    exact (diameter_root_iff_coeff hm hℓ).1 ⟨1, by norm_num, h 1 (by norm_num)⟩
  · intro hZ r hr
    exact (mismatchDiameterForce_eq_zero_iff hr.ne').2 (Or.inr (Or.inr hZ))

theorem no_diameter_root {m ℓ Z r : ℝ} (hm : m ≠ 0) (hℓ : ℓ ≠ 0) (hZ : 1 ≤ Z)
    (hr : 0 < r) : mismatchDiameterForce m ℓ Z r ≠ 0 := by
  intro h0
  have hcoeff : mismatchDiameterCoeff Z = 0 :=
    (diameter_root_iff_coeff hm hℓ).1 ⟨r, hr, h0⟩
  linarith [mismatchDiameterCoeff_neg_of_one hZ, hcoeff]

end Gravity

end DstDiophantine
