import DstDiophantine.Algebra.Sandwich
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# One revolution of the dual rotor, and the scalar phase on it

## Paper boundary (do **not** claim)

`pr = nℏ` is not the return of the dual rotor to `1`, and it is not the
return of the orbital point. Both of those happen at an angle fixed by the
rotor, with no momentum in them. Setting the dual angle equal to the
accumulated phase `2π pr/ℏ` still leaves the rotor at `-1` when `pr = ℏ`,
where the plane-wave factor has already returned to `1`. The identity of
that rotor asks for an even multiple.

## What is proved

* One revolution, angle `2π`, sends the dual rotor to `-1` and restores
  every point of the orbital plane.
* Two revolutions, angle `4π`, restore the rotor to `1`.
* On one revolution the plane-wave factor equals `1` exactly when
  `pr = nℏ` for some `n : ℤ`.
* The same revolution can restore the point while the plane-wave factor
  equals `-1` (`pr = ℏ/2`).
* With the centripetal identity, the return of the plane-wave factor places
  the radius at `n² ℏ² γ / (m k e²)`.
-/

namespace DstDiophantine

namespace Gravity

open CliffordAlgebra PGA Generators Motor Amplification Operations
open Sandwich

/-- One revolution sends the dual rotor to `-1`. -/
theorem dualRotor_one_revolution :
    rotorTorsion (pureRotation1 (2 * Real.pi)) = -1 := by
  rw [rotorTorsion_pureRotation1_closed]
  have hhalf : (2 * Real.pi) / 2 = Real.pi := by ring
  rw [hhalf, Real.cos_pi, Real.sin_pi]
  simp

/-- Two revolutions restore the dual rotor to the identity. -/
theorem dualRotor_two_revolutions :
    rotorTorsion (pureRotation1 (4 * Real.pi)) = 1 := by
  rw [rotorTorsion_pureRotation1_closed]
  have hhalf : (4 * Real.pi) / 2 = 2 * Real.pi := by ring
  rw [hhalf, Real.cos_two_pi, Real.sin_two_pi]
  simp

private theorem sandwich_one_revolution_ι1 :
    sandwich (rotorTorsion (pureRotation1 (2 * Real.pi))) (ι 1) = ι 1 := by
  have h := sandwich_pureRotation1_ι1 (2 * Real.pi)
  simpa [Real.cos_two_pi, Real.sin_two_pi] using h

private theorem sandwich_one_revolution_ι3 :
    sandwich (rotorTorsion (pureRotation1 (2 * Real.pi))) (ι 3) = ι 3 := by
  have h := sandwich_pureRotation1_ι3 (2 * Real.pi)
  simpa [Real.cos_two_pi, Real.sin_two_pi] using h

/-- One revolution restores every point of the orbital plane. -/
theorem orbitPoint_one_revolution (a b : ℝ) :
    sandwich (rotorTorsion (pureRotation1 (2 * Real.pi))) (a • ι 1 + b • ι 3) =
      a • ι 1 + b • ι 3 := by
  rw [sandwich_add, sandwich_smul, sandwich_smul, sandwich_one_revolution_ι1,
    sandwich_one_revolution_ι3]

/-- Plane-wave factor on one revolution: `exp(i 2π pr/ℏ) = 1` iff `pr = nℏ`. -/
theorem planeWave_revolution_iff {p r ℏ : ℝ} (hℏ : ℏ ≠ 0) :
    Complex.exp (Complex.I * ((p * r * (2 * Real.pi) / ℏ : ℝ) : ℂ)) = 1 ↔
      ∃ n : ℤ, p * r = (n : ℝ) * ℏ := by
  set θ : ℝ := p * r * (2 * Real.pi) / ℏ
  constructor
  · intro h
    rw [Complex.exp_eq_one_iff] at h
    obtain ⟨n, hn⟩ := h
    have hI : (Complex.I : ℂ) ≠ 0 := Complex.I_ne_zero
    have hθ : (θ : ℂ) = (n : ℂ) * (2 * (Real.pi : ℂ)) := by
      have hre : Complex.I * (θ : ℂ) =
          Complex.I * ((n : ℂ) * (2 * (Real.pi : ℂ))) := by
        calc Complex.I * (θ : ℂ)
            = (n : ℂ) * ((2 * Real.pi : ℂ) * Complex.I) := hn
          _ = (n : ℂ) * (Complex.I * (2 * (Real.pi : ℂ))) := by
              congr 1
              ring
          _ = Complex.I * ((n : ℂ) * (2 * (Real.pi : ℂ))) := by ring
      exact mul_left_cancel₀ hI hre
    have hθR : θ = (n : ℝ) * (2 * Real.pi) :=
      Complex.ofReal_inj.mp (by simpa using hθ)
    have h2 : (2 : ℝ) * Real.pi ≠ 0 := mul_ne_zero two_ne_zero Real.pi_ne_zero
    refine ⟨n, ?_⟩
    calc p * r
        = θ * ℏ / (2 * Real.pi) := by
            unfold θ
            field_simp [hℏ, h2]
      _ = ((n : ℝ) * (2 * Real.pi)) * ℏ / (2 * Real.pi) := by rw [hθR]
      _ = (n : ℝ) * ℏ := by field_simp [h2]
  · rintro ⟨n, hn⟩
    have hθ : θ = (n : ℝ) * (2 * Real.pi) := by
      unfold θ
      rw [hn]
      field_simp [hℏ]
    apply Complex.exp_eq_one_iff.mpr
    refine ⟨n, ?_⟩
    rw [hθ]
    push_cast
    ring

/-- The revolution that restores the point can leave the plane-wave factor at `-1`. -/
theorem revolution_with_open_phase :
    rotorTorsion (pureRotation1 (2 * Real.pi)) = -1 ∧
      sandwich (rotorTorsion (pureRotation1 (2 * Real.pi))) (ι 1) = ι 1 ∧
        Complex.exp (Complex.I * (((1 / 2) * (2 * Real.pi) : ℝ) : ℂ)) = -1 := by
  refine ⟨dualRotor_one_revolution, sandwich_one_revolution_ι1, ?_⟩
  have harg : Complex.I * (((1 / 2) * (2 * Real.pi) : ℝ) : ℂ) =
      Real.pi * Complex.I := by
    push_cast
    ring
  rw [harg, Complex.exp_pi_mul_I]

/-- Phase-aligned dual angle `2π` is the case `pr = ℏ`: the rotor is `-1`
while the plane-wave factor equals `1`. -/
theorem phaseAligned_one_quantum :
    rotorTorsion (pureRotation1 (2 * Real.pi)) = -1 ∧
      Complex.exp (Complex.I * ((2 * Real.pi : ℝ) : ℂ)) = 1 := by
  refine ⟨dualRotor_one_revolution, ?_⟩
  have harg : Complex.I * ((2 * Real.pi : ℝ) : ℂ) =
      (1 : ℤ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [harg]
  exact Complex.exp_eq_one_iff.mpr ⟨1, rfl⟩

/-- The same alignment restores the rotor only at an even multiple, `pr = 2ℏ`. -/
theorem phaseAligned_rotor_identity :
    rotorTorsion (pureRotation1 (4 * Real.pi)) = 1 ∧
      Complex.exp (Complex.I * ((2 * (2 * Real.pi) : ℝ) : ℂ)) = 1 := by
  refine ⟨dualRotor_two_revolutions, ?_⟩
  have harg : Complex.I * ((2 * (2 * Real.pi) : ℝ) : ℂ) =
      (2 : ℤ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [harg]
  exact Complex.exp_eq_one_iff.mpr ⟨2, rfl⟩

/-- `pr = nℏ` and `p²/m = ke²/(γ r)` give `r = n² ℏ² γ / (m k e²)`. -/
theorem closure_radius_of_winding {n : ℤ} {ℏ m k e γ r p : ℝ}
    (_hn : n ≠ 0) (hm : m ≠ 0) (hr : r ≠ 0) (hγ : γ ≠ 0) (hk : k ≠ 0) (he : e ≠ 0)
    (hphase : p * r = (n : ℝ) * ℏ)
    (hcent : p ^ 2 / m = k * e ^ 2 / (γ * r)) :
    r = (n : ℝ) ^ 2 * ℏ ^ 2 * γ / (m * k * e ^ 2) := by
  have hp : p = (n : ℝ) * ℏ / r := by
    field_simp [hr] at hphase ⊢
    linarith
  rw [hp] at hcent
  have hke : m * k * e ^ 2 ≠ 0 :=
    mul_ne_zero (mul_ne_zero hm hk) (pow_ne_zero 2 he)
  field_simp [hm, hr, hγ, hke] at hcent ⊢
  nlinarith

/-- The return of the plane-wave factor, with the centripetal identity,
places the radius. -/
theorem closure_radius_of_planeWave {ℏ m k e γ r p : ℝ}
    (hℏ : ℏ ≠ 0) (hm : m ≠ 0) (hr : r ≠ 0) (hγ : γ ≠ 0) (hk : k ≠ 0) (he : e ≠ 0)
    (hwave : Complex.exp (Complex.I * ((p * r * (2 * Real.pi) / ℏ : ℝ) : ℂ)) = 1)
    (hcent : p ^ 2 / m = k * e ^ 2 / (γ * r)) :
    ∃ n : ℤ, n ≠ 0 ∧ r = (n : ℝ) ^ 2 * ℏ ^ 2 * γ / (m * k * e ^ 2) := by
  obtain ⟨n, hn⟩ := (planeWave_revolution_iff hℏ).1 hwave
  have hn0 : n ≠ 0 := by
    intro h0
    subst h0
    have hpr : p * r = 0 := by simpa using hn
    have hp : p = 0 := (mul_eq_zero.mp hpr).resolve_right hr
    rw [hp, zero_pow (by norm_num : 2 ≠ 0), zero_div] at hcent
    have hden : γ * r ≠ 0 := mul_ne_zero hγ hr
    have hrhs : k * e ^ 2 / (γ * r) ≠ 0 :=
      div_ne_zero (mul_ne_zero hk (pow_ne_zero 2 he)) hden
    exact hrhs hcent.symm
  exact ⟨n, hn0, closure_radius_of_winding hn0 hm hr hγ hk he hn hcent⟩

end Gravity

end DstDiophantine
