import DstDiophantine.Algebra.Sandwich
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# One revolution of the dual rotor, and the scalar phase on it

`pr = nℏ` is not the rotor's return to `1` or the orbital return, and it is not used to place a radius or to close a matter-wave phase on a nuclear circumference.
-/

namespace DstDiophantine

namespace Gravity

open CliffordAlgebra PGA Generators Motor Amplification Operations
open Sandwich

theorem dualRotor_one_revolution :
    rotorTorsion (pureRotation1 (2 * Real.pi)) = -1 := by
  rw [rotorTorsion_pureRotation1_closed]
  have hhalf : (2 * Real.pi) / 2 = Real.pi := by ring
  rw [hhalf, Real.cos_pi, Real.sin_pi]
  simp

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

theorem orbitPoint_one_revolution (a b : ℝ) :
    sandwich (rotorTorsion (pureRotation1 (2 * Real.pi))) (a • ι 1 + b • ι 3) =
      a • ι 1 + b • ι 3 := by
  rw [sandwich_add, sandwich_smul, sandwich_smul, sandwich_one_revolution_ι1,
    sandwich_one_revolution_ι3]

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

/-- Phase alignment at angle `2π` is the case `pr = ℏ`. -/
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

end Gravity

end DstDiophantine
