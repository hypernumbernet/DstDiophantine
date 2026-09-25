import DstDiophantine.Algebra.RelativeRotor
import DstDiophantine.Gravity.DualRotorFlow
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The critical lag is not the vacuum

On one axis the Killing scalar and the unsigned mass, written in the
common rapidity `σ = φ + θ` and the mismatch `δ = φ - θ`, are
`J = δ σ / 2` and `M = (σ² + δ²) / 4`.

The harmonic stiffness is critical only at alignment `δ = 0`. Along the
written flow that alignment persists when the lag rate vanishes, and then
`σ` coasts. `J` stays zero while `M = σ(t)² / 4`. That mass is constant
in time if and only if the common rate vanishes. A nonzero common rate
crosses `M = 0` once; away from that instant the two
rotors still disagree, so the state is not free fall.

A frozen quartic well `δ = v` is a different line. There
`J = v σ / 2` and `M = (σ² + v²) / 4`. Coasting `σ` carries both scalars.
At rest, with `σ = 0` and `v ≠ 0`, the well is balanced and massive,
`J = 0` and `M = v² / 4`, and the rotors do not coincide.

An affine lag of nonzero rate meets every critical value once and does
not stop there. No electroweak vacuum is claimed.
-/

namespace DstDiophantine

namespace Gravity

open RelativeRotor Invariant

/-! ### One-axis scalars in `(σ, δ)` -/

theorem axis_J_sum_diff (σ δ : ℝ) :
    J (axisParams ((σ + δ) / 2) ((σ - δ) / 2)) = δ * σ / 2 := by
  rw [J_axisParams]
  ring

theorem axis_mass_sum_diff (σ δ : ℝ) :
    mass (axisParams ((σ + δ) / 2) ((σ - δ) / 2)) = (σ ^ 2 + δ ^ 2) / 4 := by
  rw [mass_axisParams]
  ring

/-! ### Written alignment: `J = 0`, mass coasts -/

theorem written_aligned_angles (σ₀ σd₀ m t : ℝ) :
    writtenDelta 0 0 t = 0 ∧
      writtenSigma σ₀ σd₀ m 0 0 t = σ₀ + σd₀ * t ∧
        writtenUsual σ₀ σd₀ m 0 0 t = (σ₀ + σd₀ * t) / 2 ∧
          writtenDual σ₀ σd₀ m 0 0 t = (σ₀ + σd₀ * t) / 2 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [writtenDelta, affineMismatch]
  · simp [writtenSigma, cubicRapidity]
  · simp [writtenUsual, usualFrom, writtenSigma, writtenDelta, affineMismatch, cubicRapidity]
  · simp [writtenDual, dualFrom, writtenSigma, writtenDelta, affineMismatch, cubicRapidity]

theorem written_aligned_J (σ₀ σd₀ m t : ℝ) :
    J (axisParams (writtenUsual σ₀ σd₀ m 0 0 t) (writtenDual σ₀ σd₀ m 0 0 t)) = 0 := by
  have h := written_aligned_angles σ₀ σd₀ m t
  rw [h.2.2.1, h.2.2.2, J_axisParams]
  ring

theorem written_aligned_mass (σ₀ σd₀ m t : ℝ) :
    mass (axisParams (writtenUsual σ₀ σd₀ m 0 0 t) (writtenDual σ₀ σd₀ m 0 0 t)) =
      (σ₀ + σd₀ * t) ^ 2 / 4 := by
  have h := written_aligned_angles σ₀ σd₀ m t
  rw [h.2.2.1, h.2.2.2, mass_axisParams]
  ring

/-- Coasting alignment has stationary mass iff the common rate vanishes. -/
theorem written_aligned_mass_const_iff {σ₀ σd₀ m : ℝ} :
    (∀ t, mass (axisParams (writtenUsual σ₀ σd₀ m 0 0 t) (writtenDual σ₀ σd₀ m 0 0 t)) =
        mass (axisParams (writtenUsual σ₀ σd₀ m 0 0 0) (writtenDual σ₀ σd₀ m 0 0 0))) ↔
      σd₀ = 0 := by
  constructor
  · intro h
    have h1 := h 1
    have h2 := h 2
    rw [written_aligned_mass, written_aligned_mass] at h1 h2
    have h1' : (σ₀ + σd₀) ^ 2 = σ₀ ^ 2 := by
      have := congrArg (fun x : ℝ => x * 4) h1
      ring_nf at this
      linarith
    have h2' : (σ₀ + σd₀ * 2) ^ 2 = σ₀ ^ 2 := by
      have := congrArg (fun x : ℝ => x * 4) h2
      ring_nf at this
      linarith
    have hlin1 : 2 * σ₀ * σd₀ + σd₀ ^ 2 = 0 := by
      nlinarith [sq_nonneg σ₀, sq_nonneg (σ₀ + σd₀)]
    have hlin2 : 4 * σ₀ * σd₀ + 4 * σd₀ ^ 2 = 0 := by
      nlinarith [sq_nonneg σ₀, sq_nonneg (σ₀ + σd₀ * 2)]
    nlinarith
  · intro hσ t
    rw [written_aligned_mass, written_aligned_mass, hσ]
    ring

/-- A nonzero common rate meets the empty state once. -/
theorem written_aligned_crosses_empty {σ₀ σd₀ m : ℝ} (hσ : σd₀ ≠ 0) :
    ∃! t, mass (axisParams (writtenUsual σ₀ σd₀ m 0 0 t)
      (writtenDual σ₀ σd₀ m 0 0 t)) = 0 := by
  refine ExistsUnique.intro (-σ₀ / σd₀) ?_ ?_
  · rw [written_aligned_mass]
    have : σ₀ + σd₀ * (-σ₀ / σd₀) = 0 := by
      field_simp [hσ]
      ring
    rw [this]
    ring
  · intro t ht
    rw [written_aligned_mass] at ht
    have hsq : (σ₀ + σd₀ * t) ^ 2 = 0 := by nlinarith
    have hlin : σ₀ + σd₀ * t = 0 := sq_eq_zero_iff.mp hsq
    have : σd₀ * t = -σ₀ := by linarith
    have : t * σd₀ = -σ₀ := by linarith
    calc
      t = (t * σd₀) / σd₀ := by field_simp [hσ]
      _ = -σ₀ / σd₀ := by rw [this]

/-- Away from the empty instant, coasting alignment is not free fall. -/
theorem written_aligned_not_freefall {σ₀ σd₀ m t : ℝ}
    (hs : Real.sinh ((σ₀ + σd₀ * t) / 4) ≠ 0) :
    relativeRotor (axisParams (writtenUsual σ₀ σd₀ m 0 0 t)
      (writtenDual σ₀ σd₀ m 0 0 t)) ≠ 1 := by
  intro hΩ
  have hrot := (relativeRotor_eq_one_iff _).mp hΩ
  have hang := written_aligned_angles σ₀ σd₀ m t
  rw [hang.2.2.1, hang.2.2.2] at hrot
  have hs' : Real.sinh (((σ₀ + σd₀ * t) / 2) / 2) ≠ 0 := by
    simpa [div_div] using hs
  exact _root_.DstDiophantine.RelativeRotor.axis_rotors_ne_of_bivector (Or.inl hs') hrot

/-! ### A frozen quartic well is a massive line -/

theorem frozen_well_J (v σ : ℝ) :
    J (axisParams ((σ + v) / 2) ((σ - v) / 2)) = v * σ / 2 :=
  axis_J_sum_diff σ v

theorem frozen_well_mass (v σ : ℝ) :
    mass (axisParams ((σ + v) / 2) ((σ - v) / 2)) = (σ ^ 2 + v ^ 2) / 4 :=
  axis_mass_sum_diff σ v

/-- At rest the well is balanced and massive, and the rotors disagree. -/
theorem frozen_well_at_rest_not_empty {v : ℝ} (hv : v ≠ 0)
    (hs : Real.sinh (v / 4) ≠ 0 ∨ Real.sin (-v / 4) ≠ 0) :
    J (axisParams (v / 2) (-v / 2)) = 0 ∧
      mass (axisParams (v / 2) (-v / 2)) = v ^ 2 / 4 ∧
        0 < mass (axisParams (v / 2) (-v / 2)) ∧
          relativeRotor (axisParams (v / 2) (-v / 2)) ≠ 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [J_axisParams]; ring
  · rw [mass_axisParams]; ring
  · rw [mass_axisParams]
    have : 0 < v ^ 2 := sq_pos_of_ne_zero hv
    nlinarith
  · intro hΩ
    have hrot := (relativeRotor_eq_one_iff _).mp hΩ
    have hs' : Real.sinh ((v / 2) / 2) ≠ 0 ∨ Real.sin ((-v / 2) / 2) ≠ 0 := by
      rcases hs with hsinh | hsin
      · refine Or.inl ?_
        have : (v / 2) / 2 = v / 4 := by ring
        simpa [this] using hsinh
      · refine Or.inr ?_
        have : (-v / 2) / 2 = -v / 4 := by ring
        simpa [this] using hsin
    exact _root_.DstDiophantine.RelativeRotor.axis_rotors_ne_of_bivector hs' hrot

/-- Coasting through a frozen well carries `J` unless the common rate vanishes. -/
theorem frozen_well_J_const_iff {v σ₀ σd₀ : ℝ} (hv : v ≠ 0) :
    (∀ t, J (axisParams ((σ₀ + σd₀ * t + v) / 2) ((σ₀ + σd₀ * t - v) / 2)) =
        J (axisParams ((σ₀ + v) / 2) ((σ₀ - v) / 2))) ↔
      σd₀ = 0 := by
  constructor
  · intro h
    have h1 := h 1
    rw [frozen_well_J, frozen_well_J] at h1
    have h1' : v * (σ₀ + σd₀ * 1) / 2 = v * σ₀ / 2 := h1
    have hv' : v * σd₀ = 0 := by nlinarith
    exact (mul_eq_zero.mp hv').resolve_left hv
  · intro hσ t
    rw [frozen_well_J, frozen_well_J, hσ]
    ring

/-! ### An affine lag crosses every critical value -/

theorem affine_hits {δ₀ ν δc : ℝ} (hν : ν ≠ 0) :
    affineMismatch δ₀ ν ((δc - δ₀) / ν) = δc := by
  unfold affineMismatch
  have : ν * ((δc - δ₀) / ν) = δc - δ₀ := by field_simp [hν]
  linarith

theorem affine_hits_with_rate (δ₀ ν δc : ℝ) :
    deriv (affineMismatch δ₀ ν) ((δc - δ₀) / ν) = ν := by
  rw [deriv_affineMismatch]

theorem affine_crosses_once {δ₀ ν δc : ℝ} (hν : ν ≠ 0) :
    ∃! t, affineMismatch δ₀ ν t = δc := by
  refine ExistsUnique.intro ((δc - δ₀) / ν) (affine_hits hν) ?_
  intro t ht
  unfold affineMismatch at ht
  have : ν * t = δc - δ₀ := by linarith
  have : t * ν = δc - δ₀ := by linarith
  calc
    t = (t * ν) / ν := by field_simp [hν]
    _ = (δc - δ₀) / ν := by rw [this]

end Gravity

end DstDiophantine
