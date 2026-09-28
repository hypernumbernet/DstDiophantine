import DstDiophantine.Algebra.RelativeRotor
import DstDiophantine.Gravity.DualControl
import DstDiophantine.Gravity.DualRotorVacuum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Rest mass, unsigned mass, and free fall

Three quantities are distinct.

* The stiffness potential \(V=(m/2)\sum_a(\alpha_a-\beta_a)^2\) is the
  potential of the written particle action. The coefficient \(m\) is not
  derived from the algebra.
* The unsigned mass is \(M=\tfrac12\sum_a(\alpha_a^2+\beta_a^2)\).
* Free fall is \(\Omega=1\), the coincidence of the two rotors.

On one axis, with \(\sigma=\alpha+\beta\) and \(\delta=\alpha-\beta\),
\(V=2m(M-\sigma^2/4)\) and \(J=\delta\sigma/2\). For \(m\neq 0\),
\(V=mJ\) if and only if the lag vanishes or the dual angle vanishes.
The two sides can both be nonzero only on the pure-usual ray.

A cross-axis shield has \(J=0\), positive unsigned mass, and positive
\(V\). On one axis with nonnegative rapidities, \(J=0\) is alignment, and
then \(V=0\) while \(M\) may not vanish. Anti-alignment \(\theta=-\phi\neq 0\)
has \(J=0\) and \(V>0\), and is not free fall.

Vanishing stiffness makes both angular accelerations of the written action
zero for every angle, and still admits a pure boost with \(J\neq 0\),
\(M\neq 0\), and \(\Omega\neq 1\).

A frozen lag on the written flow keeps \(V\) constant. If \(m\delta\neq 0\),
both \(J\) and \(M\) move with the common rapidity. The same-sign kinetic
model is the one that restores the lag, and it is not the written action.

No identification with \(F=ma\), and no acceleration ceiling, is claimed.
-/

namespace DstDiophantine

namespace Gravity

open Operations RelativeRotor Invariant

/-! ### Stiffness potential -/

/-- Sum of squared lags, \(\sum(\alpha_a-\beta_a)^2\). -/
def lagSq (p : TorsionParams) : ℝ :=
  ∑ a : Fin 3, (p.alpha a - p.beta a) ^ 2

/-- Potential of the written action, \((m/2)\) times `lagSq`. -/
noncomputable def stiffnessPotential (m : ℝ) (p : TorsionParams) : ℝ :=
  (m / 2) * lagSq p

theorem stiffnessPotential_eq_lag (m : ℝ) (p : TorsionParams) :
    stiffnessPotential m p = (m / 2) * lagSq p := by
  rfl

theorem stiffness_axis (m α β : ℝ) :
    stiffnessPotential m (axisParams α β) = (m / 2) * (α - β) ^ 2 := by
  unfold stiffnessPotential lagSq
  rw [Fin.sum_univ_three]
  simp [axisParams]

/-- On one axis, \(V=2m(M-\sigma^2/4)\) with \(\sigma=\alpha+\beta\). -/
theorem stiffness_axis_massShift (m α β : ℝ) :
    stiffnessPotential m (axisParams α β) =
      2 * m * (mass (axisParams α β) - (α + β) ^ 2 / 4) := by
  rw [stiffness_axis, mass_axisParams]
  ring

/-- On the pure-usual ray, \(V=mJ\). -/
theorem stiffness_eq_mul_J_of_dual_zero (m α : ℝ) :
    stiffnessPotential m (axisParams α 0) = m * J (axisParams α 0) := by
  rw [stiffness_axis, J_axisParams]
  ring

/-- For nonzero stiffness, \(V=mJ\) iff the lag vanishes or the dual angle does. -/
theorem stiffness_eq_mul_J_iff {m α β : ℝ} (hm : m ≠ 0) :
    stiffnessPotential m (axisParams α β) = m * J (axisParams α β) ↔
      α = β ∨ β = 0 := by
  rw [stiffness_axis, J_axisParams]
  constructor
  · intro h
    have hdiff : (α - β) ^ 2 - (α ^ 2 - β ^ 2) = -2 * β * (α - β) := by ring
    have hzero : (α - β) ^ 2 - (α ^ 2 - β ^ 2) = 0 := by
      have h2 : m * ((α - β) ^ 2 - (α ^ 2 - β ^ 2)) = 0 := by linarith
      exact (mul_eq_zero.mp h2).resolve_left hm
    have hz : β * (α - β) = 0 := by linarith
    rcases mul_eq_zero.mp hz with hβ | hδ
    · exact Or.inr hβ
    · exact Or.inl (sub_eq_zero.mp hδ)
  · rintro (hα | hβ)
    · subst hα
      ring
    · subst hβ
      ring

/-! ### Neutrality does not extinguish the potential -/

theorem lagSq_crossAxisDual (α : ℝ) :
    lagSq (crossAxisDual α) = 2 * α ^ 2 := by
  rw [lagSq, Fin.sum_univ_three]
  simp [crossAxisDual, finCoord]
  ring

private theorem mass_crossAxisDual (α : ℝ) :
    mass (crossAxisDual α) = α ^ 2 := by
  rw [mass_coef, Fin.sum_univ_three]
  simp [crossAxisDual, finCoord]
  ring

/-- A cross-axis shield is neutral, massive, and stiff. -/
theorem crossAxis_neutral_stiff {m α : ℝ} (hm : 0 < m) (hα : α ≠ 0) :
    J (crossAxisDual α) = 0 ∧
      0 < mass (crossAxisDual α) ∧
        0 < stiffnessPotential m (crossAxisDual α) := by
  refine ⟨J_crossAxisDual α, ?_, ?_⟩
  · rw [mass_crossAxisDual]
    exact sq_pos_of_ne_zero hα
  · rw [stiffnessPotential_eq_lag, lagSq_crossAxisDual]
    nlinarith [sq_pos_of_ne_zero hα, hm]

/-- Nonnegative one-axis rapidities: \(J=0\) iff the two angles agree. -/
theorem J_axis_eq_zero_iff_aligned {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) :
    J (axisParams α β) = 0 ↔ α = β := by
  rw [J_axisParams]
  constructor
  · intro h
    have hsq : α ^ 2 = β ^ 2 := by linarith
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with heq | hneg
    · exact heq
    · have hα0 : α = 0 := by nlinarith [hα, hβ, hneg]
      have hβ0 : β = 0 := by nlinarith [hα, hβ, hneg]
      linarith
  · intro h
    rw [h]
    ring

theorem stiffness_aligned (m α : ℝ) :
    stiffnessPotential m (axisParams α α) = 0 := by
  rw [stiffness_axis]
  ring

/-- Anti-alignment keeps \(J=0\) and makes the potential positive. -/
theorem antialigned_potential {m φ : ℝ} (hm : 0 < m) (hφ : φ ≠ 0) :
    J (axisParams φ (-φ)) = 0 ∧
      0 < mass (axisParams φ (-φ)) ∧
        0 < stiffnessPotential m (axisParams φ (-φ)) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [J_axisParams]
    ring
  · rw [mass_axisParams]
    nlinarith [sq_pos_of_ne_zero hφ]
  · rw [stiffness_axis]
    nlinarith [sq_pos_of_ne_zero hφ, hm]

theorem antialigned_not_freefall {φ : ℝ} (hφ : φ ≠ 0) :
    relativeRotor (axisParams φ (-φ)) ≠ 1 := by
  intro hΩ
  have hrot := (relativeRotor_eq_one_iff _).mp hΩ
  have hs : Real.sinh (φ / 2) ≠ 0 := by
    intro hs0
    have hhalf : φ / 2 = 0 := Real.sinh_eq_zero.mp hs0
    exact hφ (by linarith)
  exact axis_rotors_ne_of_bivector (Or.inl hs) hrot

/-! ### Vanishing stiffness is not resonance -/

theorem written_zero_stiffness (φ θ : ℝ) :
    PaperActualEL 0 φ θ 0 0 :=
  (paperActualEL_eq 0 φ θ 0 0).mpr ⟨by ring, by ring⟩

/-- A pure boost satisfies the massless jet and is not free fall. -/
theorem zero_stiffness_pureBoost :
    PaperActualEL 0 1 0 0 0 ∧
      J (axisParams 1 0) ≠ 0 ∧
        0 < mass (axisParams 1 0) ∧
          relativeRotor (axisParams 1 0) ≠ 1 := by
  refine ⟨written_zero_stiffness 1 0, ?_, ?_, ?_⟩
  · rw [J_axisParams]
    norm_num
  · rw [mass_axisParams]
    norm_num
  · intro hΩ
    have hrot := (relativeRotor_eq_one_iff _).mp hΩ
    have hs : Real.sinh ((1 : ℝ) / 2) ≠ 0 :=
      (Real.sinh_pos_iff.mpr (by norm_num : (0 : ℝ) < (1 : ℝ) / 2)).ne'
    exact axis_rotors_ne_of_bivector (Or.inl hs) hrot

/-! ### Frozen lag: the potential stands still -/

theorem written_frozen_delta (δ₀ t : ℝ) :
    writtenDelta δ₀ 0 t = δ₀ := by
  simp [writtenDelta, affineMismatch]

theorem written_frozen_sigma (σ₀ σd₀ m δ₀ t : ℝ) :
    writtenSigma σ₀ σd₀ m δ₀ 0 t = σ₀ + σd₀ * t - m * δ₀ * t ^ 2 := by
  simp [writtenSigma, cubicRapidity]

theorem written_frozen_J (σ₀ σd₀ m δ₀ t : ℝ) :
    J (axisParams (writtenUsual σ₀ σd₀ m δ₀ 0 t) (writtenDual σ₀ σd₀ m δ₀ 0 t)) =
      δ₀ * (σ₀ + σd₀ * t - m * δ₀ * t ^ 2) / 2 := by
  have h := axis_J_sum_diff (writtenSigma σ₀ σd₀ m δ₀ 0 t) (writtenDelta δ₀ 0 t)
  simpa [writtenUsual, writtenDual, usualFrom, dualFrom, written_frozen_sigma,
    written_frozen_delta] using h

theorem written_frozen_mass (σ₀ σd₀ m δ₀ t : ℝ) :
    mass (axisParams (writtenUsual σ₀ σd₀ m δ₀ 0 t)
        (writtenDual σ₀ σd₀ m δ₀ 0 t)) =
      ((σ₀ + σd₀ * t - m * δ₀ * t ^ 2) ^ 2 + δ₀ ^ 2) / 4 := by
  have h := axis_mass_sum_diff (writtenSigma σ₀ σd₀ m δ₀ 0 t) (writtenDelta δ₀ 0 t)
  simpa [writtenUsual, writtenDual, usualFrom, dualFrom, written_frozen_sigma,
    written_frozen_delta] using h

theorem written_frozen_potential (m σ₀ σd₀ δ₀ t : ℝ) :
    stiffnessPotential m (axisParams (writtenUsual σ₀ σd₀ m δ₀ 0 t)
        (writtenDual σ₀ σd₀ m δ₀ 0 t)) =
      (m / 2) * δ₀ ^ 2 := by
  rw [stiffness_axis, writtenUsual, writtenDual]
  rw [usualFrom_sub_dualFrom, written_frozen_delta]

/-- A frozen lag does not move \(J\) for every initial rate. -/
theorem written_frozen_J_moves {σ₀ σd₀ m δ₀ : ℝ} (h : m * δ₀ ≠ 0) :
    ¬ ∀ t,
      J (axisParams (writtenUsual σ₀ σd₀ m δ₀ 0 t)
          (writtenDual σ₀ σd₀ m δ₀ 0 t)) =
        J (axisParams (writtenUsual σ₀ σd₀ m δ₀ 0 0)
            (writtenDual σ₀ σd₀ m δ₀ 0 0)) := by
  intro hconst
  have hδ : δ₀ ≠ 0 := by
    intro hδ
    exact h (by simp [hδ])
  have h1 := hconst 1
  have h2 := hconst 2
  rw [written_frozen_J, written_frozen_J] at h1 h2
  have h1' : δ₀ * (σd₀ - m * δ₀) = 0 := by
    have := congrArg (fun x : ℝ => x * 2) h1
    ring_nf at this
    linarith
  have h2' : δ₀ * (2 * σd₀ - 4 * m * δ₀) = 0 := by
    have := congrArg (fun x : ℝ => x * 2) h2
    ring_nf at this
    linarith
  have hσ : σd₀ = m * δ₀ := by
    apply mul_left_cancel₀ hδ
    linarith
  rw [hσ] at h2'
  have : δ₀ * (2 * (m * δ₀) - 4 * m * δ₀) = 0 := h2'
  have : δ₀ * (-2 * m * δ₀) = 0 := by ring_nf at this; linarith
  have : m * δ₀ = 0 := by
    have hmul : δ₀ * (m * δ₀) = 0 := by linarith
    exact mul_left_cancel₀ hδ (by linarith)
  exact h this

private theorem sqSigma_fourthDiff (σ₀ σd₀ a : ℝ) :
    (σ₀ + σd₀ * 0 - a * 0 ^ 2) ^ 2 -
        4 * (σ₀ + σd₀ * 1 - a * 1 ^ 2) ^ 2 +
        6 * (σ₀ + σd₀ * 2 - a * 2 ^ 2) ^ 2 -
        4 * (σ₀ + σd₀ * 3 - a * 3 ^ 2) ^ 2 +
        (σ₀ + σd₀ * 4 - a * 4 ^ 2) ^ 2 =
      24 * a ^ 2 := by
  ring

theorem written_frozen_mass_moves {σ₀ σd₀ m δ₀ : ℝ} (h : m * δ₀ ≠ 0) :
    ¬ ∀ t,
      mass (axisParams (writtenUsual σ₀ σd₀ m δ₀ 0 t)
          (writtenDual σ₀ σd₀ m δ₀ 0 t)) =
        mass (axisParams (writtenUsual σ₀ σd₀ m δ₀ 0 0)
            (writtenDual σ₀ σd₀ m δ₀ 0 0)) := by
  intro hconst
  let a : ℝ := m * δ₀
  have ha : a ≠ 0 := h
  have hs (t : ℝ) :
      mass (axisParams (writtenUsual σ₀ σd₀ m δ₀ 0 t)
          (writtenDual σ₀ σd₀ m δ₀ 0 t)) =
        ((σ₀ + σd₀ * t - a * t ^ 2) ^ 2 + δ₀ ^ 2) / 4 := by
    simpa [a] using written_frozen_mass σ₀ σd₀ m δ₀ t
  have hsq (t : ℝ) :
      (σ₀ + σd₀ * t - a * t ^ 2) ^ 2 = (σ₀) ^ 2 := by
    have ht := hconst t
    rw [hs t, hs 0] at ht
    have h4 := congrArg (fun x : ℝ => x * 4) ht
    ring_nf at h4
    linarith
  have hdiff := sqSigma_fourthDiff σ₀ σd₀ a
  have hflat :
      (σ₀ + σd₀ * 0 - a * 0 ^ 2) ^ 2 -
          4 * (σ₀ + σd₀ * 1 - a * 1 ^ 2) ^ 2 +
          6 * (σ₀ + σd₀ * 2 - a * 2 ^ 2) ^ 2 -
          4 * (σ₀ + σd₀ * 3 - a * 3 ^ 2) ^ 2 +
          (σ₀ + σd₀ * 4 - a * 4 ^ 2) ^ 2 =
        0 := by
    rw [hsq 0, hsq 1, hsq 2, hsq 3, hsq 4]
    ring
  have : (24 : ℝ) * a ^ 2 = 0 := by linarith
  exact ha (by nlinarith)

/-! ### Only the same-sign model restores the lag -/

theorem sameSign_restores {m φ θ φddot θddot : ℝ}
    (h : OscillatorEL m φ θ φddot θddot) :
    φddot - θddot = -2 * m * (φ - θ) ∧ φddot + θddot = 0 := by
  refine ⟨?_, oscillatorEL_free_common h⟩
  have hδ := oscillatorEL_harmonic h
  linarith

theorem sameSign_not_written {m φ θ φddot θddot : ℝ}
    (h : OscillatorEL m φ θ φddot θddot) (hδ : m * (φ - θ) ≠ 0) :
    ¬ PaperActualEL m φ θ φddot θddot := by
  intro hw
  have hrest := (sameSign_restores h).1
  have hfree := paperActualEL_free_mismatch hw
  apply hδ
  linarith

end Gravity

end DstDiophantine
