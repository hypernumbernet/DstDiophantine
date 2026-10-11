import DstDiophantine.Gravity.ElectronForce
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# One electron about a nucleus of charge `Z`

The nuclear charge, counted in units of the proton charge, is the proton
number. No centrifugal term is added. The length `ℓ` is not derived.

## Paper boundary (do **not** claim)

The restoring radius is not `a₀`, and it is not `a₀/Z`. The circular energy
is not a laboratory ionization energy. No decimal for the root or the energy
is claimed. The plunge toward the first node stays unbounded below.

## What is proved

* Counted with attraction positive, one electron about charge `Z` feels
  `Z` times the one-proton force `4x²/γ_s(x)`.
* On the outer well the logarithmic derivative does not depend on `Z > 0`.
  The circular path is radially restoring at the same phases as the
  one-proton path.
* The centripetal kinetic term and the outer-well potential each scale with
  `Z`, so the circular energy is `Z` times the one-proton energy.
* For every `Z > 0` that energy is strictly least at the one-proton root,
  and the value is negative. A larger charge makes the value lower.
-/

namespace DstDiophantine

namespace Gravity

open Set

/-- Attraction-positive force of one electron about nuclear charge `Z`,
in units of `k e²/ℓ²`. -/
noncomputable def ionAttraction (Z x : ℝ) : ℝ :=
  Z * pairAttraction x

/-- Kinetic term of the centripetal identity, in units of `k e²/ℓ`.
`v² = Z k e²/(m γ_s r)` and `r = ℓ/(2x)` give `Z x/γ_s`. -/
noncomputable def ionCircKinetic (Z x : ℝ) : ℝ :=
  Z * x / gammaSEqual x

/-- Outer-well potential of charge `Z`, vanishing at infinity,
in units of `k e²/ℓ`. -/
noncomputable def ionCircPotential (Z x : ℝ) : ℝ :=
  -(2 * Z * layerAccum x)

/-- Circular-path energy of one electron about charge `Z`,
in units of `k e²/ℓ`. -/
noncomputable def ionCircEnergy (Z x : ℝ) : ℝ :=
  Z * circEnergy x

theorem ionCircEnergy_eq_parts {Z x : ℝ} :
    ionCircEnergy Z x = ionCircKinetic Z x + ionCircPotential Z x := by
  unfold ionCircEnergy ionCircKinetic ionCircPotential circEnergy
  have hkin : Z * (x / gammaSEqual x) = Z * x / gammaSEqual x := by
    rw [mul_div_assoc]
  have hpot : Z * (2 * layerAccum x) = 2 * Z * layerAccum x := by ring
  rw [mul_sub, hkin, hpot]
  ring

private theorem deriv_ionAttraction {Z x : ℝ} (hγ : gammaSEqual x ≠ 0) :
    deriv (ionAttraction Z) x = Z * deriv pairAttraction x := by
  unfold ionAttraction
  rw [deriv_pairAttraction hγ]
  exact ((hasDerivAt_pairAttraction hγ).const_mul Z).deriv

private theorem ionAttraction_logDeriv_eq {Z x : ℝ} (hZ : Z ≠ 0)
    (hx : x ∈ Ioo (0 : ℝ) resonanceRoot1) :
    x * deriv (ionAttraction Z) x / ionAttraction Z x =
      x * deriv pairAttraction x / pairAttraction x := by
  have hγ : gammaSEqual x ≠ 0 := (gammaSEqual_pos_left_of_first_node hx).ne'
  rw [deriv_ionAttraction hγ]
  unfold ionAttraction
  have hY : pairAttraction x ≠ 0 := (pairAttraction_pos_outer hx).ne'
  field_simp [hZ, hY]

/-- The restoring comparison is the one-proton comparison, for every `Z > 0`. -/
theorem ionAttraction_logDeriv_lt_three_outer_iff {Z x : ℝ} (hZ : 0 < Z)
    (hx : x ∈ Ioo (0 : ℝ) resonanceRoot1) :
    x * deriv (ionAttraction Z) x / ionAttraction Z x < 3 ↔ 0 < circStable x := by
  rw [ionAttraction_logDeriv_eq hZ.ne' hx]
  exact pairAttraction_logDeriv_lt_three_outer_iff hx

private theorem ionCircEnergy_lt_of_lt_charge_of_neg {Z W x : ℝ}
    (hZW : Z < W) (hE : circEnergy x < 0) :
    ionCircEnergy W x < ionCircEnergy Z x := by
  unfold ionCircEnergy
  exact mul_lt_mul_of_neg_right hZW hE

/-- For every `Z > 0` the circular energy is strictly least at the
one-proton root, and the value is negative. -/
theorem ionCircEnergy_least_outer {Z x y : ℝ} (hZ : 0 < Z)
    (hx : x ∈ Ioo (0 : ℝ) resonanceRoot1)
    (hy : y ∈ Ioo (1 / 2) (3 / 5)) (h0 : circStable y = 0) :
    ionCircEnergy Z y < 0 ∧ ionCircEnergy Z y ≤ ionCircEnergy Z x ∧
      (ionCircEnergy Z x = ionCircEnergy Z y ↔ x = y) := by
  have h := circEnergy_least_outer hx hy h0
  unfold ionCircEnergy
  refine ⟨mul_neg_of_pos_of_neg hZ h.1, mul_le_mul_of_nonneg_left h.2.1 hZ.le, ?_⟩
  constructor
  · intro hEq
    exact h.2.2.mp (mul_left_cancel₀ hZ.ne' hEq)
  · intro hxy
    rw [hxy]

/-- At that common root a larger charge makes the circular energy lower. -/
theorem ionCircEnergy_lt_of_lt_charge {Z W y : ℝ} (hZW : Z < W)
    (hy : y ∈ Ioo (1 / 2) (3 / 5)) (h0 : circStable y = 0) :
    ionCircEnergy W y < ionCircEnergy Z y :=
  ionCircEnergy_lt_of_lt_charge_of_neg hZW (circEnergy_neg_at_root hy h0)

end Gravity

end DstDiophantine
